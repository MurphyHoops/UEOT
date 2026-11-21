"""Prospective numerical design. Example counts are feasibility arithmetic only."""
import json
import math
from pathlib import Path
from scipy.stats import beta, binom

HERE = Path(__file__).resolve().parent
def main():
    peer = json.loads((HERE.parent/"local/result.json").read_text())
    lower = float(peer["cases"]["chapter71_local"]["+"]["fixed_lab_axis"]["delta_p_e"][0])
    delta = .0055212
    assert lower >= delta
    n, m = 262144, 3200000
    gain, differential, loss = .99, .001, .00030
    acal, afail, atest, beta_test = .01, .01, .03, .05
    # 2 periods x 2 arms x 2 known truths, two one-sided bounds in each.
    def envelope(pos, missing):
        lo = beta.ppf(acal/16,pos,n-pos+1) if pos else 0.
        k = pos+missing
        hi = beta.isf(acal/16,k+1,n-k) if k<n else 1.
        return [lo,hi]
    ref_g = envelope(262,26)
    ref_e = envelope(n-524-26,26)
    assert ref_e[0]-ref_g[1] >= gain
    assert max(ref_e[1]-ref_e[0],ref_g[1]-ref_g[0])<=.00085

    def t(m,a):
        return math.sqrt(2*math.log(1/a)/m)
    margin = gain*delta-2*differential-2*loss
    minimal = math.ceil(2*(math.sqrt(math.log(1/atest))+math.sqrt(math.log(1/beta_test)))**2/
                        margin**2)
    assert t(minimal-1,atest)+t(minimal-1,beta_test)>margin>=t(minimal,atest)+t(minimal,beta_test)
    assert m>=minimal
    # Largest number of erasures per arm meeting the one-sided CP upper bound.
    cap = int(binom.ppf(afail/2,m,loss))
    while binom.cdf(cap,m,loss)>afail/2:
        cap -= 1
    assert binom.cdf(cap,m,loss)<=afail/2 < binom.cdf(cap+1,m,loss)
    power_failure = math.exp(-m*(margin-t(m,atest))**2/2)
    # Optional operating point with margin below the admission cap.
    veto_prob = 2*binom.sf(cap,m,.00015)
    print(json.dumps(dict(status="prospective_design_only",published_lower=lower,
        frozen_delta=delta,cal_starts=8*n,per_arm=m,all_starts=8*n+2*m,
        illustrative_reference_g=ref_g,illustrative_reference_e=ref_e,
        minimal_m_by_bound=minimal,design_margin=margin,noise_null_upper=differential,
        critical_observed_difference=differential+t(m,atest),
        critical_integer_difference=math.floor(m*(differential+t(m,atest)))+1,
        least_alt_mean_X=gain*delta-differential-2*loss,
        max_erased_per_arm=cap,alt_nonreject_prob_bound=power_failure,
        loss_veto_prob_bound_at_00015=veto_prob),indent=2))

if __name__=="__main__":
    main()
