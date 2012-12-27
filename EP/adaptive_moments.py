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

from scipy import stats
from numpy import *

## Adaptive computation of moments.

def sum_logs(*logs):
    if len(logs) == 1:
        logs = logs[0]
    logs = array(logs)
    mx = max(logs)
    return log(sum(exp(logs - mx))) + mx

def adaptive_moments(mu, sigmasqr, llf, block_size = 100, n_blocks = 100):
    sum_ll = None
    sample_Ex = mu
    sample_Ex2 = sigmasqr + mu**2
    base_points = stats.norm.ppf((arange(block_size)+0.5)/block_size)
    base_correction = -0.5*base_points**2
    for block_i in xrange(n_blocks):
        sample_mu = sample_Ex
        sample_sigmasqr = sample_Ex2 - sample_Ex**2
        samples = base_points * sqrt(sample_sigmasqr) + sample_mu
        if block_size == 1:
            samples = samples[0]
        lls = llf(samples)
        correction = -0.5*(log(sigmasqr)+(samples-mu)**2/sigmasqr)-base_correction
        lls = lls + correction
        block_Z = sum_logs(lls)
        block_w = exp(lls - block_Z)
        block_Ex = sum(block_w * samples)
        block_Ex2 = sum(block_w * samples**2)
        if sum_ll is None:
            sample_Ex = block_Ex
            sample_Ex2 = block_Ex2
            sum_ll = block_Z
        else:
            new_sum_ll = sum_logs(sum_ll, block_Z)
            w_new = exp(block_Z - new_sum_ll)
            sample_Ex = (1-w_new) * sample_Ex + w_new * block_Ex
            sample_Ex2 = (1-w_new) * sample_Ex2 + w_new * block_Ex2
            sum_ll = new_sum_ll
    Z = sum_ll - log(block_size) - log(n_blocks)
    return (Z, sample_Ex, sample_Ex2 - sample_Ex**2)
