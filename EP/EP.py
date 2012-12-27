## Copyright 2012 Google Inc. All Rights Reserved.
##
## Licensed under the Apache License, Version 2.0 (the "License")
## you may not use this file except in compliance with the License.
## You may obtain a copy of the License at
##
##     http://www.apache.org/licenses/LICENSE-2.0
##
## Unless required by applicable law or agreed to in writing, software
## distributed under the License is distributed on an AS IS BASIS,
## WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
## See the License for the specific language governing permissions and
## limitations under the License.
##
## Author: yonidonner@gmail.com (Yoni Donner)

## Expectation Propagation: building an infrastructure to use EP on virtually any model.

class Logger(object):
    log_text = []

    @classmethod
    def log(cls, txt):
        cls.log_text.append(txt)

    @classmethod
    def get_log(cls):
        return "".join(cls.log_text)

    @classmethod
    def reset(cls):
        cls.log_text = []

class EPVariable(object):
    index = 0

    def __init__(self, name = None):
        if name is None:
            self.name = "Variable %d"%(self.index)
            self.index += 1
        else:
            self.name = name

    def set(self, other_var):
        raise NotImplementedError

    def divide(self, other_var):
        raise NotImplementedError

    def clone(self):
        new_ep_variable = self.__class__(name = self.name)
        return new_ep_variable

    def __repr__(self):
        return self.name

    def integrate(self):
        return 0.0

    def is_invalid(self):
        return False

class EPTerm(object):
    index = 0

    def __init__(self, ep_variables, name = None):
        self.full_posterior_variables = ep_variables
        self.term_variables = [x.clone() for x in ep_variables]
        if name is None:
            self.name = "Term %d over %s"%(self.index,
                                           ', '.join([v.name for v in self.term_variables]))
            EPTerm.index += 1
        else:
            self.name = name
        self.reset()

    def reset(self):
        self.updated = False

    def __repr__(self):
        return "%s: "%(self.name)+"\n".join(["%s"%(repr(v)) for v in self.term_variables])

    def compute_old_posterior(self, full_posterior):
        return [posterior_variable.divide(term_variable) for (posterior_variable, term_variable)
                in zip(full_posterior, self.term_variables)]

    def proj(self, old_posterior):
        raise NotImplementedError

    def term_information(self):
        return self.name

    def update(self, full_posterior):
        Logger.log("Doing update on: ")
        Logger.log(self.term_information()+"\n")
        if self.updated:
            Logger.log("Dividing by the following term variables:\n")
            Logger.log(repr(self.term_variables)+"\n")
            old_posterior_variables = self.compute_old_posterior(full_posterior)
            for opv in old_posterior_variables:
                if opv.is_invalid():
                    Logger.log("Skipping update because %s has invalid old posterior: %s\n"%\
                                   (opv.name,  opv))
                    return full_posterior
        else:
            old_posterior_variables = full_posterior
        Logger.log("Old posterior:\n")
        Logger.log(repr(old_posterior_variables) + "\n")
        new_posterior = self.proj(old_posterior_variables)
        Logger.log("New posterior:\n")
        Logger.log(repr(new_posterior)+"\n")
        Logger.log("New term variables:\n")
        for (posterior_variable, old_posterior_variable, term_variable) in
        zip(new_posterior, old_posterior_variables, self.term_variables):
            updated_variable = posterior_variable.divide(old_posterior_variable)
            Logger.log(repr(updated_variable)+"\n")
            term_variable.set(updated_variable)
        self.updated = True
        return new_posterior

class EPModel(object):
    def __init__(self, variables = None, terms = None, min_mll_improvement = 1e-4,
                 random_schedule = False):
        self.min_mll_improvement = min_mll_improvement
        self.random_schedule = random_schedule
        if variables is not None:
            self.set_variables(variables)
            if terms is not None:
                self.set_terms(terms)

    def set_variables(self, variables):
        self.variables = []
        self.variable_by_name = {}
        for v in variables:
            self.add_variable(v)

    def add_variable(self, v):
        self.variable_by_name[v.name] = len(self.variables)
        self.variables.append(v)

    def set_terms(self, terms):
        self.terms = []
        self.term_by_name = {}
        for term in terms:
            self.add_term(term)

    def add_term(self, term):
        self.term_by_name[term.name] = len(self.terms)
        self.terms.append(term)

    def schedule(self):
        inds = range(len(self.terms))
        if self.random_schedule:
            random.shuffle(inds)
        return inds

    def recompute_marginal_log_likelihood(self):
        self.mll = sum([x.integrate() for x in self.variables])
        return self.mll

    def run_iteration(self):
        for term_index in self.schedule():
            Logger.log("Updating term: %s...\n"%self.terms[term_index].name)
            term_variables = self.terms[term_index].full_posterior_variables
            Logger.log("The full posterior variables are:\n")
            Logger.log(repr(term_variables)+"\n")
            new_posterior = self.terms[term_index].update(term_variables)
            for (ep_var, new_posterior_var) in zip(term_variables, new_posterior):
                ep_var.set(new_posterior_var)
            Logger.log("Done updating: %s.\n\n"%self.terms[term_index].name)
        # The schedule does not have to be a permutation,
        # so don't sum likelihoods within the above loop
        return self.recompute_marginal_log_likelihood()

    def is_converged(self, prv_variables):
        for (cur_var, prv_var) in zip(self.variables, prv_variables):
            if not cur_var.is_converged(prv_var):
                Logger.log("%s is not converged (%s,%s)\n"%\
                               (cur_var.name, repr(cur_var), repr(prv_var)))
                return False
        return True

    def run_to_convergence(self, verbose = False):
        prv_mll = None
        while True:
            prv_variables = [x.clone() for x in self.variables]
            new_mll = self.run_iteration()
            if verbose:
                print "Finished EP iteration with log-likelihood %.4f"%new_mll
            if self.is_converged(prv_variables):
                break
            else:
                continue
        return new_mll

    def initialize(self):
        pass
