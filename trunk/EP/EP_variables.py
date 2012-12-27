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

def mvtrunc(mu, Sigma, a, b):
    U = linalg.cholesky(Sigma)
    p1 = dot(a, U)
    b1 = b - sum(a*mu)
    M1 = eye(len(p1))
    M1[:,0] = p1
    Q,R = linalg.qr(M1)
    if R[0,0] < 0:
        Q *= -1
        R *= -1
    b2 = b1 / R[0,0]
    m,v = trunc1d(b2)
    mf = zeros(len(a))
    mf[0] = m
    mv = ones(len(a))
    mv[0] = v
    UQ = dot(U, Q)
    Zm = dot(UQ, mf) + mu
    Zv = dot(UQ, mv[:,newaxis] * transpose(UQ))
    return Zm, Zv

def log_N(mu, iSigma, logdetSigma, x):
    d = len(mu)
    xmu = x - mu
    return -0.5*(log(2*pi)*d+logdetSigma + sum(xmu * dot(iSigma, xmu)))

class EPTruncatedGaussianTerm(EPTerm):
    def __init__(self, variable, a, b, probit = False, name = None):
        super(EPTruncatedGaussianTerm, self).__init__([variable], name)
        self.a = a
        self.b = b
        self.probit = probit

    def proj(self, old_posterior):
        m = old_posterior[0].get_mu()
        V = old_posterior[0].get_Sigma()
        if old_posterior[0].is_univariate:
            m = m * ones([1])
            a = self.a * ones([1])
            V = V * ones([1,1])
        d = len(m)
        if self.probit:
            m = concatenate([m, 0])
            V = concatenate([concatenate([V, zeros([d, 1])], 1), zeros([1, d+1])], 0)
            V[d, d] = 1
            a = concatenate([a, 1])
        new_m, new_V = mvtrunc(m, V, a, self.b)
        if self.probit:
            new_m = new_m[:d]
            new_V = new_V[:d,:d]
        res = [EPScaledMVGVariable(ScaledMVG(new_m, new_V), name = old_posterior[0].name)]
        return res

class EPMVGTerm(EPTerm):
    def __init__(self, variable, G, name = None):
        super(EPMVGTerm, self).__init__([variable], name = name)
        self.G = G
        self.term_variables = [EPMVGVariable(variable.name)]

    def proj(self, old_posterior):
        new_G, mll = old_posterior[0].G.product(self.G)
        self.full_posterior_variables[0].G = new_G
        return [EPScaledMVGVariable(new_G, name = old_posterior[0].name)]

class EPSphericalGaussianVariable(EPVariable):
    def __init__(self, name = None):
        super(EPSphericalGaussianVariable, self).__init__(name)
        self.m = None
        self.v = None

    def __repr__(self):
        if self.m is None:
            return "None"
        return "m=[%s], v=%.4f"%(", ".join(["%.4f"%x for x in self.m]), self.v)

    def set(self, other_var):
        self.m = other_var.m
        self.v = other_var.v
        return self

    def divide(self, other):
        result = EPSphericalGaussianVariable(name = self.name)
        if (other.v is None):
            return result.set(self)
        iv = (1.0 / self.v - 1.0 / other.v)
        if iv == 0:
            result.m = None
            result.v = None
            return result
        result.v = 1.0 / iv
        result.m = result.v * (self.m / self.v - other.m / other.v)
        return result

    def log_N(self, x):
        return log_N(self.m, eye(len(self.m)) / self.v, len(self.m) * log(self.v), x)

    def N(self, x):
        return exp(self.log_N(x))

class EPMinkaClutterTerm(EPTerm):
    def __init__(self, variable, w, y, name = None):
        super(EPMinkaClutterTerm, self).__init__([variable], name = name)
        self.w = w
        self.y = y

    def proj(self, old_posterior):
        old_var = old_posterior[0]
        m = old_var.m
        v = old_var.v
        d = len(m)
        lZ0 = log(1 - self.w) + log_N(m, eye(d) / (v + 1.0), d * log(v+1), self.y)
        lZ1 = log(self.w) + log_N(zeros([d]), 0.1 * eye(d), d * log(10), self.y)
        mx = max(lZ0, lZ1)
        lZ = log(exp(lZ0 - mx) + exp(lZ1 - mx)) + mx
        r = exp(lZ0 - lZ)
        res = [EPSphericalGaussianVariable(old_posterior[0].name)]
        res[0].m = m + v * r * (self.y - m) / (v + 1.0)
        res[0].v = v - r * v**2 / (v + 1.0) + r * (1 - r) * (v**2 * sum((self.y - m)**2) / (d * (1.0 + v)**2))
        return res
