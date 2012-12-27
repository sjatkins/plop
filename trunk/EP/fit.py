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

def backtracking_line_search(fx, x, d, alpha = 0.5, t_threshold = 1e-8, min_change = 1e-6):
    t = 1.0
    f0 = fx(x)
    while t > t_threshold:
        x_new = x + d*t
        f1 = fx(x_new)
        if (f0 - f1) > min_change:
            return t
        t *= alpha
    return None

def basic_newton(fgh, x0, lambdasqr_threshold = 1e-8, backtracking_alpha = 0.5, t_threshold = 1e-8, min_change = 1e-6):
    x = array(x0)
    while True:
        fx, gx, hx = fgh(x)
        d = linalg.solve(hx, -gx)
        lambdasqr = -sum(gx*d)
        if (lambdasqr < lambdasqr_threshold):
            break
        only_f = lambda x1: fgh(x1, only_f = True)
        t = backtracking_line_search(only_f, x, d, alpha = backtracking_alpha, t_threshold = t_threshold, min_change = min_change)
        if t is None:
            break
        x = x + d*t
    return x

def test_fg(f, g, x, delta = 1e-4):
    d = len(x)
    my_g = zeros([d])
    x_plus = x[:,newaxis] + eye(d)*delta
    x_minus = x[:,newaxis] - eye(d)*delta
    for i in xrange(len(my_g)):
        my_x1 = x_plus[:,i]
        my_x2 = x_minus[:,i]
        my_g[i] = (f(my_x1) - f(my_x2)) / (2.0*delta)
    return g(x), my_g

def test_fgh(f, g, h, x, delta = 1e-4, threshold = 1e-8):
    real_g, fd_g = test_fg(f, g, x, delta)
    if sum((real_g-fd_g)**2) > threshold:
        return False
    for i in xrange(len(x)):
        h1 = lambda xtag: h(xtag)[i,:]
        g1 = lambda xtag: g(xtag)[i]
        real_hi, fd_hi = test_fg(g1, h1, x, delta)
        if sum((real_hi-fd_hi)**2) > threshold:
            return False
    return True

def gauss_proj_fgh(mu_X, Sigma_X, C, b, x):
    """
    Computes the function, gradient and hessian for P(a^T*[X,C]-b=x),
    where X ~ N(mu_X, Sigma_X) and C is a fixed known vector.
    U = a^T*X+c^T*C
    mu_U = a^T*mu_X+c^T*C
    sigma_U^2 = a^T*Sigma_X*a
    Equivalently, compute the function, gradient and hessian for:
    f(a) = P(U = x) = 1/sqrt(2*pi*sigma_U^2)*exp(-0.5*(x-mu_U)^2/sigma_U^2)=f1(a)*f2(a)
    f1(a) = 1/sqrt(2*pi*sigma_U^2)
    f2(a) = exp(f3(a))
    f3(a) = -0.5*f4(a)*f5(a)
    f4(a) = (x-mu_U)^2
    f5(a) = 1/sigma_U^2
    gmu(a) = [mu_X, C]
    gsigmasqr(a) = Sigma_X*a
    g(a) = g1(a)*f2(a)+g2(a)*f1(a)
    g1(a) = -0.5*(2*pi*sigma_U^2)^(-3/2)*2*pi*Sigma_X*a
    g2(a) = exp(f3(a))*g3(a)
    g3(a) = -0.5*(g4(a)*f5(a)+f4(a)*g5(a))
    g4(a) = -2*(x-mu_U)*mu_X
    g5(a) = -1/sigma_U^4*Sigma_X*a
    hmu(a) = 0
    hsigmasqr(a) = Sigma_X
    h(a) = h1(a)*f2(a)+g1(a)*g2(a)^T+g2(a)*g1(a)^T+h2(a)*f1(a)
    etc..
    """
    D = len(mu_X)
    K = len(C)
    fmu = lambda ac: sum(ac[:D]*mu_X)+sum(ac[D:]*C)-b
    fsigmasqr = lambda ac: sum(ac[:D]*dot(Sigma_X, ac[:D]))
    gmu = lambda ac: concatenate([mu_X, C])
    gsigmasqr = lambda ac: concatenate([2*dot(Sigma_X, ac[:D]), zeros([K])])
    hmu = lambda ac: zeros([D+K,D+K])
    def hsigmasqr(ac):
        res = zeros([D+K,D+K])
        res[:D,:D] = 2*Sigma_X
        return res
    f4 = lambda ac: (x-fmu(ac))**2
    g4 = lambda ac: concatenate([-2.0*(x-fmu(ac))*mu_X, zeros([K])])
    def h4(ac):
        gmuac = gmu(ac)
        return 2.0*outer(gmuac, gmuac)
    f5 = lambda ac: 1.0/fsigmasqr(ac)
    g5 = lambda ac: -1.0/fsigmasqr(ac)**2*gsigmasqr(ac)
    def h5(ac):
        fssa = fsigmasqr(ac)
        gssa = gsigmasqr(ac)
        return 2.0/fssa**3*outer(gssa,gssa)-1.0/fssa**2*hsigmasqr(ac)
    f3 = lambda ac: -0.5*f4(ac)*f5(ac)
    g3 = lambda ac: -0.5*(g4(ac)*f5(ac)+f4(ac)*g5(ac))
    def h3(ac):
        g4a = g4(ac)
        g5a = g5(ac)
        return -0.5*(f5(ac)*h4(ac)+f4(ac)*h5(ac)+outer(g4a,g5a)+outer(g5a,g4a))
    f2 = lambda ac: exp(f3(ac))
    g2 = lambda ac: f2(ac)*g3(ac)
    h2 = lambda ac: f2(ac)*h3(ac)+outer(g2(ac),g3(ac))
    f11 = lambda ac: 2*pi*fsigmasqr(ac)
    g11 = lambda ac: 2*pi*gsigmasqr(ac)
    h11 = lambda ac: 2*pi*hsigmasqr(ac)
    f1 = lambda ac: f11(ac)**(-0.5)
    g1 = lambda ac: -0.5*f11(ac)**(-1.5)*g11(ac)
    h1 = lambda ac: 0.5*1.5*f11(ac)**(-2.5)*outer(g11(ac), g11(ac))-0.5*f11(ac)**(-1.5)*h11(ac)
    f = lambda ac: f1(ac)*f2(ac)
    g = lambda ac: f1(ac)*g2(ac)+g1(ac)*f2(ac)
    def h(ac):
        g1a = g1(ac)
        g2a = g2(ac)
        return f1(ac)*h2(ac)+h1(ac)*f2(ac)+outer(g1a,g2a)+outer(g2a,g1a)
    return f,g,h

def gauss_proj_fgh2(mu_X, Sigma_X, C, a, c, b, X, F, Q, only_f = False):
    """
    E[l(a)] = int_x P(X=x)*log(P(D|a,x))*dx = int_u P(a^T*X=u)*log(P(D|u))*du =
            = E_U[log(P(D|u))] ~~ 1/Z * sum_j P(U=v_j) / Q(v_j) * log(P(D|v_j)) =
            = (sum_j w_j*f_j) / sum_j w_j
    fmu(ac) = a^T*mu_X+c^T*C+b
    fss(ac) = a^T*Sigma_X*a
    gmu(ac) = [mu_X, C]
    gss(ac) = [2*Sigma_X*a, 0]
    hmu(ac) = 0
    hss(ac) = [[2*Sigma_X, 0],[0,0]]
    f(a) = f1(a) * f2(a)
    g(a) = f1(a) * g2(a) + g1(a) * f2(a)
    h(a) = f1(a) * h2(a) + g1(a)*g2(a)^T + g2(a)*g1(a)^T + h1(a) * f2(a)
    f1(a) = sum_j w_j(a)*f_j = sum_j f3_j(a)*f_j
    g1(a) = sum_j g3_j(a)*f_j
    h1(a) = sum_j h3_j(a)*f_j
    f2(a) = 1/sum_j[w_j] = 1/sum_j[f3_j(a)]
    g2(a) = -sum_j[g3_j(a)]/f2(a)^2
    h2(a) = 2*f2(a)^{-3}*outer(sum_j[g3_j(a)],sum_j[g3_j(a)])-sum_j[h3_j(a)]/f2(a)^2
    f3_j(a) = P(U=v_j)/Q(v_j) = f4_j(a)/Q(v_j)
    g3_j(a) = g4_j(a)/Q(v_j)
    h3_j(a) = h4_j(a)/Q(v_j)
    f4_j(a) = f5(a)*f6_j(a)
    g4_j(a) = f5(a)*g6_j(a)+g5(a)*f6_j(a)
    h4_j(a) = f5(a)*h6_j(a)+h5(a)*f6_j(a)+g5(a)*g6_j(a)^T+g6_j(a)*g5(a)^T
    f5(a) = (2*pi*fss(a))^{-0.5}
    g5(a) = -0.5*(2*pi*fss(a))^{-1.5}*2*pi*gss(a)
    h5(a) = 0.5*1.5*(2*pi*fss(a))^{-2.5}*(2*pi)^2*outer(gss(a),gss(a))-0.5*(2*pi*fss(a))^{-1.5}*2*pi*hss(a)
    f6_j(a) = exp(f7_j(a))
    g6_j(a) = f6_j(a) * g7_j(a)
    h6_j(a) = f6_j(a) * h7_j(a) + f6_j(a)*outer(g7_j(a),g7_j(a))
    f7(a) = -0.5*(v_j-fmu(a))^2/fss(a) = -0.5*f8_j(a)*f9(a)
    g7(a) = -0.5*(g8_j(a)*f9(a)+f8_j(a)*g9(a))
    h7(a) = -0.5*(h8_j(a)*f9(a)+g8_j(a)*g9(a)^T+g9(a)*g8_j(a)^T+f8_j(a)*h9(a))
    f8_j(a) = (v_j-fmu(a))^2
    g8_j(a) = 2*(v_j-fmu(a))*gmu(a)
    h8_j(a) = 2*(v_j-fmu(a))*hmu(a)-2*gmu(a)*gmu(a)^T
    f9(a) = 1/fss(a)
    g9(a) = -gss(a)/fss(a)^2
    h9(a) = -hss(a)/fss(a)^2+2*fss(a)^{-3}*gss(a)*gss(a)^T
    """
    D = len(mu_X)
    K = len(C)
    fmu = sum(a * mu_X) + sum(c * C) + b
    fss = sum(a * dot(Sigma_X, a))
    f9 = 1.0/fss
    X_minus_fmu = X-fmu
    f8 = X_minus_fmu**2
    f7 = -0.5*f8*f9
    f6 = exp(f7)
    twopifss = 2*pi*fss
    f5 = twopifss**(-0.5)
    f4 = f5 * f6
    f3 = f4/Q
    f2 = 1/sum(f3)
    f1 = sum(f3*F)
    f = f1*f2
    if only_f:
        return f
    gmu = concatenate([mu_X, C])
    hmu = zeros([D+K,D+K])
    gss = concatenate([2*dot(Sigma_X, a), zeros([K])])
    hss = zeros([D+K,D+K])
    hss[:D,:D] = 2*Sigma_X
    g9 = -gss/(fss**2)
    h9 = 2*outer(gss,gss)/(fss**3)-hss/(fss**2)
    g8 = -2*X_minus_fmu[:,newaxis]*gmu[newaxis,:]
    h8 = 2*outer(gmu,gmu)[newaxis,:,:]-2*X_minus_fmu[:,newaxis,newaxis]*hmu[newaxis,:,:]
    g7 = -0.5*(g8*f9+f8[:,newaxis]*g9[newaxis,:])
    h7 = -0.5*(h8*f9+g8[:,:,newaxis]*g9[newaxis,newaxis,:]+g9[newaxis,:,newaxis]*g8[:,newaxis,:]+f8[:,newaxis,newaxis]*h9[newaxis,:,:])
    g6 = f6[:,newaxis]*g7
    h6 = f6[:,newaxis,newaxis]*(h7+g7[:,newaxis,:]*g7[:,:,newaxis])
    g5 = -pi*twopifss**(-1.5)*gss
    h5 = 3*pi**2*twopifss**(-2.5)*outer(gss,gss)-pi*twopifss**(-1.5)*hss
    g4 = f5*g6+g5[newaxis,:]*f6[:,newaxis]
    h4 = f5*h6+h5[newaxis,:,:]*f6[:,newaxis,newaxis]+g5[newaxis,:,newaxis]*g6[:,newaxis,:]+g6[:,:,newaxis]*g5[newaxis,newaxis,:]
    g3 = g4/Q[:,newaxis]
    h3 = h4/Q[:,newaxis,newaxis]
    sumg3 = sum(g3,0)
    g2 = -sumg3*f2**2
    h2 = 2*f2**3*outer(sumg3,sumg3)-sum(h3,0)*f2**2
    g1 = sum(g3*F[:,newaxis],0)
    h1 = sum(h3*F[:,newaxis,newaxis],0)
    g = f1*g2+g1*f2
    h = f1*h2+h1*f2+outer(g1,g2)+outer(g2,g1)
    return f,g,h

def test_gauss_proj_fgh2():
    D = 5
    K = 3
    M = 50
    mu_X = random.normal(size=[D])
    Sigma_X = cov(random.normal(size=[D,10]))
    C = random.normal(size=[K])
    X = random.normal(size=[M])
    F = random.normal(size=[M])
    Q = random.random(size=[M])
    a = random.normal(size=[D])
    c = random.normal(size=[K])
    b = random.normal()
    fgh = gauss_proj_fgh2(mu_X, Sigma_X, C, a, c, b, X, F, Q, only_f = False)
    # direct computation
    mu_U = sum(mu_X*a)+sum(C*c)+b
    sigmasqr_U = sum(a*dot(Sigma_X,a))
    logP = -0.5*(log(2*pi*sigmasqr_U)+(X-mu_U)**2/sigmasqr_U)
    P = exp(logP)
    W = P / Q
    f_direct = sum(W * F) / sum(W)
    # test gradient
    just_f = lambda ac: gauss_proj_fgh2(mu_X, Sigma_X, C, ac[:D], ac[D:], b, X, F, Q)[0]
    just_g = lambda ac: gauss_proj_fgh2(mu_X, Sigma_X, C, ac[:D], ac[D:], b, X, F, Q)[1]
    just_h = lambda ac: gauss_proj_fgh2(mu_X, Sigma_X, C, ac[:D], ac[D:], b, X, F, Q)[2]
    return test_fgh(just_f, just_g, just_h, concatenate([a,c]))

def norm_logcdf(x):
    return where(x < -35, -2.9501008622617708+0.058637475892812145*x-0.49956953912089291*x**2, stats.norm.logcdf(x))
    if x < -35:
        return -2.9501008622617708+0.058637475892812145*x-0.49956953912089291*x**2
    return stats.norm.logcdf(x)

def norm_logsf(x):
    return where(x > 35, -2.9501008622617708-0.058637475892812145*x-0.49956953912089291*x**2, stats.norm.logsf(x))

def simple_probit_fgh(a, X, n, k, sigmasqr_a = None, only_f = False):
    aTX = dot(a, X)
    logP = norm_logcdf(aTX)
    logQ = norm_logsf(aTX)
    d = len(a)
    if sigmasqr_a is None:
        lambda_a = 0.0
        log_sigmasqr_a = 0.0
    else:
        lambda_a = 1.0 / sigmasqr_a
        log_sigmasqr_a = log(sigmasqr_a)
    fa = -0.5*(d*(log(2*pi)+log_sigmasqr_a)+lambda_a*sum(a**2)) + sum(k*logP) + sum((n-k)*logQ)
    if only_f:
        return -fa
    P = exp(logP)
    R = stats.norm.pdf(aTX)
    T1 = k - n*P
    RT1 = R * T1
    T2 = exp(-logP-logQ)
    ga = -lambda_a*a + dot(X, RT1 * T2)
    WH = R*(aTX*T1*T2 + R*n*T2 + T1*T2**2*R*(1.0-2*P))
    ha = -lambda_a*eye(d) - dot(X, WH[:,newaxis] * transpose(X))
    return (-fa,-ga,-ha)

def test_simple_probit_fgh():
    D = 5
    N = 100
    M = 50
    X = random.normal(size=[D,N])
    a = random.normal(size=[D])
    p = stats.norm.cdf(dot(a, X))
    n = random.poisson(M, size=[N])
    k = random.binomial(n, p)
    sigmasqr_a = 100.0
    f = lambda a1: simple_probit_fgh(a1, X, n, k, sigmasqr_a, only_f = True)
    g = lambda a1: simple_probit_fgh(a1, X, n, k, sigmasqr_a)[1]
    h = lambda a1: simple_probit_fgh(a1, X, n, k, sigmasqr_a)[2]
    return test_fgh(f, g, h, a)

def simple_probit_fit(X, n, k, sigmasqr_a = None):
    """Tests the Newton method using probit regression:
    P(Y_i = 1 | X_i) = Phi(a^T*X_i)
    The data Y has n_i observations, out of which k_i have Y_i=1 and n_i-k_i have Y_i=0.
    The prior is P(a) = N(a ; 0, sigmasqr_a*I)
    f(a) = log(P(a)) + log(P(D|a)) = -0.5*(d*log(2*pi*sigmasqr_a)+|a|^2/sigmasqr_a) +
         + sum_i [k_i*log(Phi(a^T*X_i))+(n_i-k_i)*log(1-Phi(a^T*X_i))]
    g(a) = -a/sigmasqr_a + sum_i k_i*X_i*phi(a^T*X_i)/Phi(a^T*X_i)+(n_i-k_i)*(-X_i*phi(a^T*X_i)/(1-Phi(a^T*X_i))) =
         = -a/sigmasqr_a + sum_i X_i*phi(a^T*X_i)*(k_i/Phi(a^T*X_i)-(n_i-k_i)/(1-Phi(a^T*X_i))) =
         = -a/sigmasqr_a + sum_i X_i*phi(a^T*X_i)*(k_i-k_i*Phi(...)-n_i*Phi(...)+k_i*Phi(...))/(Phi(...)*(1-Phi(...))) =
         = -a/sigmasqr_a + sum_i X_i*phi(a^T*X_i)*(k_i-n_i*p_i)/(p_i*(1-p_i)) =
         = -a/sigmasqr_a + sum_i X_i*r_i*(k_i-n_i*p_i)/(p_i*(1-p_i))
    where p_i = Phi(a^T*X_i), r_i = phi(a^T*X_i) = 1/sqrt(2*pi)*exp(-0.5*(a^T*X_i)^2)
    dp_i/da = X_i*r_i
    dr_i/da = -X_i*r_i*a^T*X_i
    For the hessian we need a few more symbols:
    t1_i = k_i-n_i*p_i
    t2_i = 1/(p_i*(1-p_i))
    g(a) = -a/sigmasqr_a + sum_i X_i*r_i*t1_i*t2_i
    dt2_i / da = -t2_i^2*X_i*(r_i*(1-p_i)-p_i*r_i)=-t2_i^2*X_i*r_i*(1-2*p_i)
    h(a) = -1/sigmasqr_a + sum_i X_i*X_i^T*(-r_i*a^T*X_i*t1_i*t2_i - r_i^2*n_i*t2_i - r_i*t1_i*t2_i^2*r_i*(1-2*p_i)) =
         = -1/sigmasqr_a - sum_i X_i*X_i^T*r_i*(a^T*X_i*t1_i*t2_i + r_i*n_i*t2_i + t1_i*t2_i^2*r_i*(1-2*p_i))
    """
    fgh = lambda a, only_f = False: simple_probit_fgh(a, X, n, k, sigmasqr_a, only_f)
    a = basic_newton(fgh, zeros([X.shape[0]]))
    return a

def test_simple_probit_fit():
    D = 5
    N = 1000
    M = 50
    X = random.normal(size=[D,N])
    a = random.normal(size=[D])
    p = stats.norm.cdf(dot(a, X))
    n = random.poisson(M, size=[N])
    k = random.binomial(n, p)
    sigmasqr_a = 100.0
    a1 = simple_probit_fit(X, n, k, sigmasqr_a = sigmasqr_a, add_intercept = False)
    return a,a1

def test_probit_fit3():
    D = 5
    K = 3
    N = 1000
    m = 50
    mu_Z = random.normal(size=[N,D])
    M = random.normal(size=[N,D,D])
    Sigma_Z = array([0.1*(eye(D)+dot(M[i,:,:],transpose(M[i,:,:]))) for i in xrange(N)])
    Z = [random.multivariate_normal(mu_Z[i,:], Sigma_Z[i,:,:]) for i in xrange(N)]
    a = random.normal(size=[D])
    c = random.normal(size=[K])
    X = random.normal(size=[N,K])
    b = random.normal(size=[N])
    w = random.random(size=[N])
    U = dot(Z, a) + dot(X, c) - b
    p = stats.norm.cdf(U)
    k = random.binomial(m, p)
    n = ones([N]) * m
    data = (mu_Z, Sigma_Z, X, b, n, k, w)
    sigmasqr_a = 1e4
    fit_a, fit_c = probit_fit3(data, random.normal(size=[D]), random.normal(size=[K]), sigmasqr_a = sigmasqr_a, n_reso=100)
    return a,c,fit_a,fit_c

def probit_fit3(data, a, c, sigmasqr_a = None, n_reso = 100, **kwargs):
    """Let Y_1,...,Y_N be sets of binary data with n_i observations and k_i successes,
    (X_1,...,X_N) observed covariates and (Z_1,...,Z_N) hidden variables.
    P(Y_ij = 1 | X_i, Z_i) = Phi(c^T*X_i+a^T*Z_i-b_i).
    We want to estimate a and c given some initial values. We also have the distributions
    of Z_i: Z_i ~ N(mu_i, Sigma_i). Let U_i = c^T*X_i+a^T*Z_i.
    The data is:
    mu_Z: (N,D)
    Sigma_Z: (N,D,D)
    X: (N,K)
    b: (N,)
    n: (N,)
    k: (N,)
    w: (N,)
    """
    (mu_Z, Sigma_Z, X, b, n, k, w) = data
    (N,K) = X.shape
    D = mu_Z.shape[1]
    XtYs = concatenate([mu_Z, X], 1)
    XtXs = XtYs[:,:,newaxis] * XtYs[:,newaxis,:]
    XtXs[:,:D,:D] += Sigma_Z
    terms = [[(0.0, 0.0, 0.0) for j in xrange(3)] for i in xrange(N)]
    m_U = zeros([N])
    v_U = zeros([N])
    iv_U = zeros([N])
    ivm_U = zeros([N])
    iter_i = 0
    while True:
        iter_i += 1
        if iter_i > 100:
            break
        mu_U = dot(mu_Z, a) + dot(X, c)
        sigmasqr_U = dot(sum(Sigma_Z * a[newaxis,:,newaxis], 1), a)
        prior_iv = 1.0 / sigmasqr_U
        prior_ivm = mu_U * prior_iv
        prior_terms = zip(prior_iv, prior_ivm, zeros([N]))
        for i in xrange(N):
            term_iv, term_ivm, term_scale = terms[i][2]
            iv_U[i] -= term_iv
            ivm_U[i] -= term_ivm
            new_term = prior_terms[i]
            new_term_iv, new_term_ivm, new_term_mll = new_term
            iv_U[i] += new_term_iv
            ivm_U[i] += new_term_ivm
            terms[i][2] = new_term

            if n[i] == 0:
                continue

            while True:
                prv_iv = iv_U[i]
                prv_ivm = ivm_U[i]
                for y in [0,1]:
                    n_a = (n[i]-k[i],k[i])[y]
                    if (n_a == 0):
                        continue
                    data_term = terms[i][y]
                    (term_iv, term_ivm, term_mll) = data_term
                    old_iv = iv_U[i] - term_iv
                    if old_iv <= 0:
                        continue
                    old_ivm = ivm_U[i] - term_ivm
                    old_v = 1.0 / old_iv
                    old_m = old_v * old_ivm
                    (new_m, new_v, mll) = probit_proj(old_m, old_v, b[i], y)
                    new_iv = 1.0 / new_v
                    new_ivm = new_m * 1.0 / new_v
                    delta_iv = new_iv - iv_U[i]
                    delta_ivm = new_ivm - ivm_U[i]
                    gamma = 1.0 / n[i]
                    new_term_iv = term_iv + delta_iv * gamma
                    new_term_ivm = term_ivm + delta_ivm * gamma
                    updated_iv = iv_U[i] + n_a * gamma * delta_iv
                    updated_ivm = ivm_U[i] + n_a * gamma * delta_ivm
                    if (updated_iv > 0):
                        iv_U[i] = updated_iv
                        ivm_U[i] = updated_ivm
                        terms[i][y] = (new_term_iv,new_term_ivm,0.0)
                v_ratio = iv_U[i]/prv_iv
                kld = -0.5*(v_ratio - log(v_ratio) + iv_U[i] * (ivm_U[i] / iv_U[i] - prv_ivm / prv_iv)**2 - 1.0)
                if (kld < 1e-16):
                    break
            v_U[i] = 1.0 / iv_U[i]
            m_U[i] = v_U[i] * ivm_U[i]
        iZ = concatenate([log((arange(n_reso)+0.5)/n_reso),-log((arange(n_reso)+0.5)/n_reso)])
        V = iZ[newaxis,:] * sqrt(v_U)[:,newaxis] + m_U[:,newaxis]
        logR = log(0.5)-0.5*log(v_U)[:,newaxis]-abs(iZ)[newaxis,:]
        R = exp(logR)
        F = k[:,newaxis] * norm_logcdf(V - b[:,newaxis]) + (n-k)[:,newaxis] * norm_logsf(V - b[:,newaxis])
        a, c = probit_fit3_newton(mu_Z, Sigma_Z, X, a, c, b, V, R, F, **kwargs)
    return a,c

def probit_fit3_newton(mu_Z, Sigma_Z, X, a, c, b, V, R, F, **kwargs):
    """
    The input is:
    mu_Z: (N, D)
    Sigma_Z: (N, D, D)
    X: (N, K)
    a: (D,)
    c: (K,)
    b: (N,)
    V: (N, M)
    R: (N, M)
    F: (N, M)
    """
    (N, D) = mu_Z.shape
    K = X.shape[1]
    M = V.shape[1]
    def fgh(ac, only_f = False):
        res = [gauss_proj_fgh2(mu_Z[i,:], Sigma_Z[i,:,:], X[i,:], ac[:D], ac[D:], -b[i], V[i,:], F[i,:], R[i,:], only_f = only_f) for i in xrange(N)]
        if only_f:
            return -sum(res)
        f = sum([x[0] for x in res])
        g = sum(array([x[1] for x in res]), 0)
        h = sum(array([x[2] for x in res]), 0)
        return -f,-g,-h
    ac = basic_newton(fgh, concatenate([a,c]), **kwargs)
    return (ac[:D], ac[D:])
