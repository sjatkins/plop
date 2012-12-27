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

from numpy import *

class EPDiscreteVariable(EPVariable):
    def __init__(self, T = None, name = None):
        super(EPDiscreteVariable, self).__init__(name)
        if isscalar(T):
            T = -log(T)*ones([T])
        self.T = T

    def clone(self):
        if self.T is None:
            new_T = None
        else:
            new_T = array(self.T)
        return EPDiscreteVariable(new_T, name = self.name)

    def is_converged(self, other_var, threshold = 1e-6):
        if other_var.T is None:
            return False
        if self.T is None:
            return False
        kld = self.KL_divergence(other_var)
        if kld is None:
            return False
        if kld > threshold:
            return False
        return True

    def interpolate(self, other, stepsize):
        if self.T is None:
            self_T = zeros(other.T.shape)
        else:
            self_T = self.T
        if other.T is None:
            other_T = zeros(self.T.shape)
        else:
            other_T = other.T
        return EPDiscreteVariable((1.0 - stepsize) * self_T + stepsize * other_T, name = self.name)

    def set(self, other_var, return_changed = False):
        if return_changed:
            changed = False
            if self.T is None:
                changed = True
            else:
                kld = self.KL_divergence(other_var)
                if (kld is None) or (kld > 1e-6):
                    changed = True
        if other_var.T is None:
            self.T = None
        else:
            self.T = array(other_var.T)
        if return_changed:
            return changed
        return self

    def divide(self, other):
        if other.T is None:
            result = EPDiscreteVariable(self.T, name = self.name)
        else:
            result = EPDiscreteVariable(self.T - other.T, name = self.name)
        return result

    def product(self, other):
        if self.T is None:
            result = EPDiscreteVariable(other.T, name = self.name)
        elif other.T is None:
            result = EPDiscreteVariable(self.T, name = self.name)
        else:
            result = EPDiscreteVariable(self.T + other.T, name = self.name)
        return result

    def probabilities(self):
        w = exp(self.T - max(self.T))
        w = w / sum(w)
        return w

    def integrate(self):
        return sum_logs(self.T)

    def __repr__(self):
        if self.T is None:
            return "%s is uninitialized"%self.name
        return "%s: [%s]"%(self.name, ", ".join(["%f"%x for x in self.T]))

    def KL_divergence(self, other):
        if other.T is None:
            return None
        if self.T is None:
            return None
        my_probabilities = self.probabilities()
        other_probabilities = other.probabilities()
        return sum(where(my_probabilities == 0, 0.0, my_probabilities * (log(my_probabilities) - log(other_probabilities))))

class EPDiscreteTerm(EPTerm):
    def __init__(self, C, T, name = None):
        super(EPDiscreteTerm, self).__init__([C], name = name)
        self.T = EPDiscreteVariable(T)

    def update(self, full_posterior, stepsize = 0.1):
        if self.updated:
            return full_posterior
        return full_posterior[0].product(self.T)

    def proj(self, old_posterior, point = False):
        if point:
            return self.T.T[old_posterior[0]]
        return old_posterior[0].product(self.T)
