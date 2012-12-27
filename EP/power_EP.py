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

def probit_proj(m, v, b, y):
    if y == 0:
        m = -m
        b = -b
    btag = (b - m) / sqrt(v + 1.0)
    mll = norm_logsf(btag)
    logm0 = -0.5*(log(2*pi)+btag**2) - mll
    m0 = exp(logm0)
    new_m = v / sqrt(v + 1.0) * m0 + m
    new_v = v / (v + 1.0) * (v * (1+btag*m0-m0**2) + 1.0)
    if y == 0:
        new_m = -new_m
    return (new_m, new_v, mll)

def powerEP_probit(mu, sigmasqr, bnk, max_iterations = 100):
    """
    To update t_i(x)^n:
    Delete t~_i(x) to get the old posterior. PROJ to get the new full posterior.
    Divide by the old posterior to get t0_i(x) with iv0, ivm0.
    Interpolate to get t1_i(x)=t0_i(x)^gamma*t~_i(x)^{1-gamma}.
    Since t0_i=new/old and t~_i=full/old this is
    t~_i^{1-gamma}*(t~_i*new/full)^gamma = t~_i*(new/full)^gamma.
    Update: full*(t1_i/t~_i)^n = full*(new/full)^{gamma*n}."""
    terms = []
    m = mu
    v = sigmasqr
    total_mll = 0.0
    iv = 1.0 / sigmasqr
    for iter_i in xrange(max_iterations):
        prv_m = m
        prv_v = v
        prv_iv = iv
        for bnk_i in xrange(len(bnk)):
            (b,n,k) = bnk[bnk_i]
            for y in [0,1]:
                term_i = 2*bnk_i+y
                n_a = (n-k,k)[y]
                if (n_a == 0):
                    if len(terms) <= term_i:
                        terms.append(None)
                    continue
                if (len(terms) > term_i) and (terms[term_i] is not None):
                    (term_iv, term_ivm, term_mll) = terms[term_i]
                    old_iv = iv - term_iv
                    if old_iv < 0:
                        continue
                    old_v = 1.0 / old_iv
                    old_m = old_v * (m*iv - term_ivm)
                    old_mll = total_mll - term_mll
                else:
                    term_iv = 0.0
                    term_ivm = 0.0
                    term_mll = 0.0
                    old_iv = iv
                    old_v = v
                    old_m = m
                    old_mll = total_mll
                (new_m, new_v, mll) = probit_proj(old_m, old_v, b, y)
                new_iv = 1.0 / new_v
                delta_iv = new_iv - iv
                delta_ivm = new_iv * new_m - iv * m
                delta_mll = old_mll + mll - total_mll
                gamma = 1.0 / n_a
                new_term_iv = term_iv + delta_iv * gamma
                new_term_ivm = term_ivm + delta_ivm * gamma
                new_term_mll = term_mll + delta_mll * gamma
                updated_iv = iv + n_a * gamma * delta_iv
                updated_ivm = iv * m + n_a * gamma * delta_ivm
                updated_mll = total_mll + n_a * gamma * delta_mll
                if (updated_iv > 0):
                    v = 1.0 / updated_iv
                    iv = updated_iv
                    m = v * updated_ivm
                    total_mll = updated_mll
                    updated_term = (new_term_iv,new_term_ivm,new_term_mll)
                else:
                    updated_term = None
                if len(terms) > term_i:
                    terms[term_i] = updated_term
                else:
                    terms.append(updated_term)
        m_diff = m - prv_m
        v_diff = v - prv_v
        if (m_diff**2+v_diff**2)<1e-8:
            break
    return (m,v,total_mll)

def test_powerEP_probit(N = 20, M = 50):
    mu = random.normal()
    sigmasqr = var(random.normal(size=[10]))
    X = random.normal() * sqrt(sigmasqr) + mu
    b = random.normal(size=[N])
    p = stats.norm.cdf(X - b)
    k = random.binomial(M, p)
    bnk = zip(b,ones([N],dtype='int32')*M,k)
    (m,v,mll) = powerEP_probit(mu, sigmasqr, bnk, max_iterations = 1000)
    return (mu, sigmasqr, X), (m, v, mll)
