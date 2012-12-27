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

class MVG:
    def __init__(self, mu, Sigma = None, logdet_iSigma = None, scale = None):
        if scale is not None:
            self.scale = scale
            self.iSigma_mu = mu
            self.iSigma = Sigma
            self.mu_iSigma_mu = logdet_iSigma
            self.mu = None
            self.Sigma = None
            self.rank = None
            self.logdet = None
            self.w = None
            self.U = None
            return
        if (Sigma is not None) and (isscalar(mu)) and (isscalar(Sigma)):
            Sigma = ones([1,1]) * Sigma
            mu = ones([1]) * mu
        if isscalar(mu):
            self.d = mu
            self.mu = zeros([self.d])
        else:
            self.mu = array(mu)
            self.d = len(self.mu)
        if Sigma is None:
            self.Sigma = eye(self.d)
        else:
            self.Sigma = Sigma
        if logdet_iSigma is None:
            self.compute_inverse()
        else:
            self.rank, self.logdet, self.iSigma, self.iSigma_mu, self.mu_iSigma_mu,
            self.w, self.U = logdet_iSigma
        self.scale = None

    def __repr__(self):
        if self.scale is not None:
            return "sN(%f, %s, %s)"%(self.scale, repr(self.iSigma_mu), repr(self.iSigma))
        if self.d == 1:
            return "N(%f, %f)"%(self.mu[0], self.Sigma[0,0])
        return "N(%s, %s)"%(repr(self.mu), repr(self.Sigma))

    def clone(self):
        if self.scale is not None:
            return MVG(self.iSigma_mu, self.iSigma, self.mu_iSigma_mu, self.scale)
        return MVG(self.mu, self.Sigma,
                   (self.rank, self.logdet, self.iSigma,
                    self.iSigma_mu, self.mu_iSigma_mu, self.w, self.U))

    def compute_inverse(self):
        if self.d == 1:
            self.logdet = log(self.Sigma[0,0])
            self.iSigma = 1.0 / self.Sigma
            self.iSigma_mu = self.iSigma * self.mu
            self.rank = 1
            self.w = self.Sigma
            self.U = ones([1,1])
        else:
            self.w, self.U = self.stable_eig(self.Sigma)
            self.rank = len(self.w)
            self.logdet = sum(log(self.w))
            self.iw = 1.0 / self.w
            self.iSigma = dot(self.U, self.iw[:,newaxis]*transpose(self.U))
            self.iSigma_mu = dot(self.iSigma, self.mu)
            self.mu_iSigma_mu = sum(self.mu * self.iSigma_mu)

    def dot(self, M):
        if self.d == 1 and isscalar(M):
            new_mu = M * self.mu
            new_Sigma = M**2 * self.Sigma
            return MVG(new_mu, new_Sigma)
        new_mu = dot(M, self.mu)
        new_Sigma = dot(M, dot(self.Sigma, transpose(M)))
        return MVG(new_mu, new_Sigma)

    def addvec(self, b):
        new_iSigma_mu = self.iSigma_mu + dot(self.iSigma, b)
        new_mu_iSigma_mu = sum(new_iSigma_mu * (self.mu + b))
        return MVG(self.mu + b, self.Sigma,
                   (self.rank, self.logdet, self.iSigma, new_iSigma_mu,
                    new_mu_iSigma_mu, self.w, self.U))

    def log_pdf(self, x):
        if self.d == 1:
            if not isscalar(x):
                x = x[0]
            x0 = x - self.mu[0]
            return -0.5*(log(2*pi)+self.logdet+x0**2/self.Sigma[0,0])
        x0 = x - self.mu
        v = dot(x0, self.U)
        return -0.5*(self.rank*log(2*pi)+self.logdet+sum(v**2 / self.w))

    def log_pdf0(self):
        return self.log_pdf(zeros([self.d]))

    def stable_eig(self, M):
        w, U = linalg.eigh(M)
        inds = nonzero(abs(w) > 1e-6)[0]
        w = w[inds]
        U = U[:,inds]
        return w, U

    def multi_product(self, others):
        if self.scale is None:
            new_scale = 0.0
        else:
            new_scale = self.scale
        new_iSigma = self.iSigma
        new_iSigma_mu = self.iSigma_mu
        for other in others:
            new_scale = new_scale + other.scale
            new_iSigma = new_iSigma + other.iSigma
            new_iSigma_mu = new_iSigma_mu + other.iSigma_mu
            new_scale = new_scale - 0.5*(other.rank*log(2*pi)+other.logdet+
                                         other.mu_iSigma_mu)
        w, U = self.stable_eig(new_iSigma)
        new_rank = len(w)
        new_logdet = -sum(log(w))
        iw = 1.0 / w
        new_Sigma = dot(U, iw[:,newaxis]*transpose(U))
        new_mu = dot(new_Sigma, new_iSigma_mu)
        new_mu_iSigma_mu = sum(new_iSigma_mu * new_mu)
        res = MVG(new_mu, new_Sigma,
                  (new_rank, new_logdet, new_iSigma, new_iSigma_mu,
                   new_mu_iSigma_mu, iw, U))
        Z = new_scale+0.5*(new_rank*log(2*pi)+new_logdet)
        return res, Z

    def product(self, other):
        if other.scale is not None:
            new_iSigma = self.iSigma + other.iSigma
            new_iSigma_mu = self.iSigma_mu + other.iSigma_mu
        if self.d == 1:
            new_iSigma = 1.0 / self.Sigma[0,0] + 1.0 / other.Sigma[0,0]
            new_Sigma = 1.0 / new_iSigma
            new_logdet = log(new_Sigma)
            new_mu = new_Sigma * (self.mu[0] / self.Sigma[0,0] + other.mu[0] / other.Sigma[0,0])
            Z = -0.5*(log(2*pi)+self.logdet+other.logdet-new_logdet+
                      self.mu[0]**2/self.Sigma[0,0]+
                      other.mu[0]**2/other.Sigma[0,0]-new_mu**2/new_Sigma)
            return MVG(ones([1])*new_mu, ones([1,1])*new_Sigma,
                       (1, new_logdet, ones([1,1])*new_iSigma,
                        ones([1])*new_iSigma*new_mu, None, new_Sigma, ones([1,1]))), Z
        new_iSigma = self.iSigma + other.iSigma
        w, U = self.stable_eig(new_iSigma)
        new_rank = len(w)
        new_logdet = -sum(log(w))
        iw = 1.0 / w
        new_Sigma = dot(U, iw[:,newaxis]*transpose(U))
        v1 = dot(self.iSigma, self.mu)
        v2 = dot(other.iSigma, other.mu)
        new_mu = dot(new_Sigma, v1 + v2)
        Z = -0.5*((self.rank+other.rank-new_rank)*log(2*pi)+self.logdet+
                  other.logdet-new_logdet+sum(self.mu*v1)+sum(other.mu*v2)-
                  sum(new_mu*(v1+v2)))
        return MVG(new_mu, new_Sigma,
                   (new_rank, new_logdet, new_iSigma,
                    dot(new_iSigma, new_mu), None, iw, U)), Z

    def divide(self, other):
        if self.scale is None and other.scale is None:
            v1 = dot(self.iSigma, self.mu)
            v2 = dot(other.iSigma, other.mu)
            new_iSigma = self.iSigma - other.iSigma
            w, U = self.stable_eig(new_iSigma)
            v = dot(transpose(U), v1-v2)
            mu_iSigma_mu = sum(v**2/w)
            new_iSigma_mu = self.iSigma_mu - other.iSigma_mu
            new_scale = 0.5*(other.logdet-self.logdet+mu_iSigma_mu+
                             sum(other.mu*v2)-sum(self.mu*v1))
            res = MVG(new_iSigma_mu, new_iSigma, mu_iSigma_mu, new_scale)
            return res, 0.0
        if self.d == 1:
            new_iSigma = 1.0 / self.Sigma[0,0] - 1.0 / other.Sigma[0,0]
            new_Sigma = 1.0 / new_iSigma
            new_logdet = log(new_Sigma)
            new_mu = new_Sigma * (self.mu[0] / self.Sigma[0,0] -
                                  other.mu[0] / other.Sigma[0,0])
            Z = -0.5*(-log(2*pi)+self.logdet-other.logdet-new_logdet+
                       self.mu[0]**2/self.Sigma[0,0]-
                       other.mu[0]**2/other.Sigma[0,0]-new_mu**2/new_Sigma)
            return MVG(ones([1])*new_mu, ones([1,1])*new_Sigma,
                       (1, new_logdet, ones([1,1])*new_iSigma,
                        ones([1]) * new_iSigma * new_mu, new_iSigma * new_mu,
                        new_Sigma, ones([1,1]))), Z
        new_iSigma = self.iSigma - other.iSigma
        w, U = self.stable_eig(new_iSigma)
        new_logdet = -sum(log(w))
        iw = 1.0 / w
        new_Sigma = dot(U, iw[:,newaxis]*transpose(U))
        v1 = self.iSigma_mu
        v2 = other.iSigma_mu
        new_mu = dot(new_Sigma, v1 - v2)
        new_iSigma_mu = dot(new_iSigma, new_mu)
        new_rank = len(w)
        Z = 0.5*(other.logdet-self.logdet+sum(new_mu*(v1-v2))+sum(other.mu*v2)-
                 sum(self.mu*v1))
        return MVG(new_mu, new_Sigma,
                   (new_rank, new_logdet, new_iSigma,
                    new_iSigma_mu, sum(new_iSigma_mu * new_mu), iw, U)), Z

    def w_slogdet(self, w):
        logdet = 0.0
        sign = 1
        for w_i_0 in w:
            if w_i_0 < 0:
                w_i = -w_i_0
                sign = sign * -1
            else:
                w_i = w_i_0
            logdet += log(w_i)
        return (logdet, sign)

class ScaledMVG:
    """A potentially-unnormalized Gaussian-like object, representing
the function (in logspace):
    f(x) = scale - 0.5*(x-mu)^T*Sigma^{-1}*(x-mu).

    A fully precomputed ScaledMVG stores the following:

    mu
    Sigma
    scale
    iSigma = Sigma^{-1}
    iSigma_mu = Sigma^{-1} * mu
    mu_iSigma_mu = mu^T * Sigma^{-1} * mu
    logdet = log(|Sigma|)
    rank, U, w such that Sigma = U * diag(w) * U^T and rank = len(w)

    Any subset of those may be None, and everything is computed lazily when needed.
    For some applications, it is never needed to explicitly represent mu and Sigma,
    just iSigma and iSigma_mu.
    To access any element of the representation, getters are used, which, if it not
    already computed, compute it
    from the minimal subset of other elements that are already stored.

    These are:
    get_mu()
    get_Sigma()
    get_scale()
    get_iSigma()
    get_iSigma_mu()
    get_mu_iSigma_mu()
    get_logdet()
    get_eig() for U and w
    get_rank()
"""

    def __init__(self, mu = None, Sigma = None, iSigma = None, iSigma_mu = None,
                 logdet = None, rank = None, scale = None, mu_iSigma_mu = None,
                 w = None, U = None):
        self.mu = mu
        self.Sigma = Sigma
        self.iSigma = iSigma
        self.iSigma_mu = iSigma_mu
        self.logdet = logdet
        self.rank = rank
        self.scale = scale
        self.mu_iSigma_mu = mu_iSigma_mu
        self.w = w
        self.U = U

    def __repr__(self):
        mu = self.get_mu()
        if mu is None:
            return "uninitialized"
        Sigma = self.get_Sigma()
        if self.scale is None:
            return "N(%s, %s)"%(repr(mu), repr(Sigma))
        return "sN(%s, %s, %f)"%(repr(mu), repr(Sigma), self.scale)

    def clone(self):
        return self.__class__(mu = self.mu, Sigma = self.Sigma, iSigma = self.iSigma,
                              iSigma_mu = self.iSigma_mu, logdet = self.logdet,
                              rank = self.rank, scale = self.scale,
                              mu_iSigma_mu = self.mu_iSigma_mu, w = self.w, U = self.U)

    def dot(self, A):
        if self.mu is None:
            mu = None
        else:
            mu = dot(A, self.mu)
        if self.Sigma is None:
            Sigma = None
        else:
            Sigma = dot(A, dot(self.Sigma, transpose(A)))
        res = ScaledMVG(mu = mu, Sigma = Sigma)
        if self.scale is not None:
            res.scale = res.normalized_scale() + self.scale - self.normalized_scale()
        return res

    def addvec(self, b):
        mu = self.get_mu() + b
        return ScaledMVG(mu = mu, Sigma = self.Sigma, iSigma = self.iSigma,
                         logdet = self.logdet, rank = self.rank, scale = self.scale,
                         w = self.w, U = self.U)

    def log_pdf(self, X):
        "Returns the logarithm of the PDF of X by this Gaussian."
        X_minus_mu = X - self.get_mu()
        return -0.5*(self.get_rank()*log(2*pi)+self.get_logdet()+
                     sum(X_minus_mu * dot(self.get_iSigma(), X_minus_mu)))

    def stable_eig(self, M):
        w, U = linalg.eigh(M)
        inds = nonzero(abs(w) > 1e-6)[0]
        w = w[inds]
        U = U[:,inds]
        return w, U

    def get_eig(self):
        if self.w is None:
            if self.Sigma is not None:
                self.w, self.U = self.stable_eig(self.Sigma)
            elif self.iSigma is not None:
                w, self.U = self.stable_eig(self.iSigma)
                self.w = 1.0 / w
        return (self.w, self.U)

    def get_Sigma(self):
        if self.Sigma is None:
            w, U = self.get_eig()
            self.Sigma = dot(U, w[:,newaxis] * transpose(U))
        return self.Sigma

    def get_iSigma(self):
        if self.iSigma is None:
            w, U = self.get_eig()
            self.iSigma = dot(U, (1.0/w)[:,newaxis] * transpose(U))
        return self.iSigma

    def get_logdet(self):
        if self.logdet is None:
            w, U = self.get_eig()
            self.logdet = sum(log(w))
        return self.logdet

    def get_iSigma_mu(self):
        if self.iSigma_mu is None:
            if self.mu is not None:
                iSigma = self.get_iSigma()
                self.iSigma_mu = dot(self.iSigma, self.mu)
        return self.iSigma_mu

    def get_mu_iSigma_mu(self):
        if self.mu_iSigma_mu is None:
            iSigma_mu = self.get_iSigma_mu()
            if self.mu is not None:
                self.mu_iSigma_mu = sum(iSigma_mu * self.mu)
            else:
                w, U = self.get_eig()
                # Sigma = U * w * U^T
                # mu^T * iSigma * mu = iSigma_mu^T * Sigma * iSigma_mu
                # = v^T v where v = Sigma**0.5 * iSigma_mu =
                # = U * w**0.5 * U^T * iSigma_mu
                v = dot(transpose(U), iSigma_mu)
                self.mu_iSigma_mu = sum(v**2*w)
        return self.mu_iSigma_mu

    def get_mu(self):
        if self.mu is None:
            # Compute mu from iSigma_mu and Sigma or iSigma
            self.mu = dot(self.get_Sigma(), self.get_iSigma_mu())
        return self.mu

    def get_rank(self):
        if self.rank is None:
            w, U = self.get_eig()
            self.rank = len(w)
        return self.rank

    def get_scale(self):
        if self.scale is None:
            self.scale = self.normalized_scale()
        return self.scale

    def product(self, other):
        # Sigma^{-1} = Sigma_1^{-1} + Sigma_2^{-1}
        # mu = Sigma * (Sigma_1^{-1} mu_1 + Sigma_2^{-1} mu_2)
        # (x-mu_1)^T*Sigma_1^{-1}*(x-mu_1)+(x-mu_2)^T*Sigma_2^{-1}*(x-mu_2)
        # = x^T Sigma^{-1} x - 2 x^T Sigma^{-1} mu + mu_1^T Sigma_1^{-1} mu_1 +
        # + mu_2^T Sigma_2^{-1} mu_2
        # = (x-mu)^T Sigma^{-1} (x-mu) + mu_1^T Sigma_1^{-1} mu_1 +
        # + mu_2^T Sigma_2^{-1} mu_2 - mu^T Sigma^{-1} mu
        iSigma = self.get_iSigma() + other.get_iSigma()
        iSigma_mu = self.get_iSigma_mu() + other.get_iSigma_mu()
        result = ScaledMVG(iSigma = iSigma, iSigma_mu = iSigma_mu)
        result.scale = self.get_scale() + other.get_scale() -
        0.5*(self.get_mu_iSigma_mu() + other.get_mu_iSigma_mu() -
             result.get_mu_iSigma_mu())
        return result

    def divide(self, other):
        # Sigma^{-1} = Sigma_1^{-1} - Sigma_2^{-1}
        # mu = Sigma * (Sigma_1^{-1} mu_1 - Sigma_2^{-1} mu_2)
        # (x-mu_1)^T*Sigma_1^{-1}*(x-mu_1)-(x-mu_2)^T*Sigma_2^{-1}*(x-mu_2)
        # = x^T Sigma^{-1} x - 2 x^T Sigma^{-1} mu + mu_1^T Sigma_1^{-1} mu_1 -
        # - mu_2^T Sigma_2^{-1} mu_2
        # = (x-mu)^T Sigma^{-1} (x-mu) + mu_1^T Sigma_1^{-1} mu_1 -
        # - mu_2^T Sigma_2^{-1} mu_2 - mu^T Sigma^{-1} mu
        iSigma = self.get_iSigma() - other.get_iSigma()
        iSigma_mu = self.get_iSigma_mu() - other.get_iSigma_mu()
        result = ScaledMVG(iSigma = iSigma, iSigma_mu = iSigma_mu)
        result.scale = self.get_scale() - other.get_scale() -
        0.5*(self.get_mu_iSigma_mu() - other.get_mu_iSigma_mu() -
             result.get_mu_iSigma_mu())
        return result

    def normalized_scale(self):
        "Returns the the normalizing constant that transforms the function into a
        normalized Gaussian."
        return -0.5*(self.get_rank() * log(2*pi) + self.get_logdet())

    def integrate(self):
        "Returns the logarithm of the integral over x of f(x)."
        return self.get_scale() - self.normalized_scale()
