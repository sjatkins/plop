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

class EPMVGVariable(EPVariable):
    def __init__(self, G = None, name = None):
        super(EPMVGVariable, self).__init__(name)
        self.G = G

    def set(self, other_var):
        self.G = other_var.G.clone()
        return self

    def divide(self, other):
        result = EPMVGVariable(name = self.name)
        if (other.G is None):
            return (result.set(self), 0.0)
        result.G, mll = self.G.divide(other.G)
        return result, mll

    def __repr__(self):
        if self.G is None:
            return self.name
        return "%s ~ %s"%(self.name, self.G)

class EPScaledMVGVariable(EPVariable):
    def __init__(self, G = None, name = None):
        super(EPScaledMVGVariable, self).__init__(name)
        self.G = G

    def is_converged(self, other_var):
        if other_var.G is None:
            return False
        if self.G is None:
            return False
        kld = self.G.KL_divergence(other_var.G)
        if kld is None:
            return False
        if kld > 1e-4:
            return False
        return True

    def is_invalid(self):
        if self.G is not None:
            if sum(self.G.get_eig()[0] < 0.0) > 0:
                return True
        return False

    def interpolate(self, other, stepsize):
        if other.G is None:
            other_G = ScaledMVG(iSigma = zeros(self.G.get_iSigma().shape),
                                iSigma_mu = zeros(self.G.get_iSigma_mu().shape),
                                mu_iSigma_mu = 0.0,
                                scale = 0.0)
        else:
            other_G = other.G
        if self.G is None:
            self_G = ScaledMVG(iSigma = zeros(other.G.get_iSigma().shape),
                               iSigma_mu = zeros(other.G.get_iSigma_mu().shape),
                               mu_iSigma_mu = 0.0,
                               scale = 0.0)
        else:
            self_G = self.G
        result = EPScaledMVGVariable(name = self.name)
        result.G = self_G.interpolate(other_G, stepsize)
        return result

    def set(self, other_var, return_changed = False):
        if return_changed:
            changed = False
            if self.G is None:
                changed = True
            else:
                kld = self.G.KL_divergence(other_var.G)
                if (kld is None) or (kld > 1e-6):
                    print "%s (%s to %s) is still changing (KL: %s)"%(self.name, repr(self.G), repr(other_var.G), repr(kld))
                    changed = True
        self.G = other_var.G.clone()
        if return_changed:
            return changed
        return self

    def divide(self, other):
        result = EPScaledMVGVariable(name = self.name)
        if (other.G is None):
            return result.set(self)
        result.G = self.G.divide(other.G)
        return result

    def product(self, other):
        result = EPScaledMVGVariable(name = self.name)
        if (self.G is None):
            return result.set(other)
        if (other.G is None):
            return result.set(self)
        result.G = self.G.product(other.G)
        return result

    def clone(self):
        new_G = None
        if self.G is not None:
            new_G = self.G.clone()
        return EPScaledMVGVariable(new_G, name = self.name)

    def integrate(self):
        return self.G.integrate()

    def __repr__(self):
        if self.G is None:
            return "%s is uninitialized"%self.name
        return "%s ~ %s"%(self.name, self.G)

class EPGaussianTerm(EPTerm):
    def __init__(self, X, mu, Sigma, name = None):
        super(EPGaussianTerm, self).__init__([X], name = name)
        self.G = EPScaledMVGVariable(ScaledMVG(mu = mu, Sigma = Sigma))

    def update(self, full_posterior, stepsize = 0.1):
        if self.updated:
            return full_posterior
        res_X = full_posterior[0].product(self.G)
        self.updated = True
        return [res_X]

    def proj(self, old_posterior, point = False):
        if not point:
            return [EPScaledMVGVariable(old_posterior[0].product(self.G))]
        return self.G.G.log_pdf(old_posterior[0])
