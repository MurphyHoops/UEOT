"""Same normal source, complete local Gaussian records, and posterior risk."""
import sympy as sp
from common import *
def result():
    v,w=sp.symbols("v w",positive=True)
    p1,p2,z1,z2,Cs,mu=sp.symbols("p1 p2 z1 z2 C mu",real=True)
    postvar=v*w/(v+w)
    m1=(w*p1+v*z1)/(v+w);m2=(w*p2+v*z2)/(v+w)
    # Completing the square for each actual latent Gaussian block.
    P=sp.symbols("P",real=True)
    for p,z,m in [(p1,z1,m1),(p2,z2,m2)]:
        lhs=(P-p)**2/v+(z-P)**2/w
        rhs=(P-m)**2/postvar+(z-p)**2/(v+w)
        assert sp.cancel(lhs-rhs)==0
    e1,e2=sp.symbols("e1 e2",real=True)
    err=(2*p1*e1+2*p2*e2+e1**2+e2**2-2*w)/Cs
    def gaussian_expect(expr):
        pol=sp.Poly(sp.expand(expr),e1,e2);out=0
        moments={0:1,1:0,2:w,3:0,4:3*w*w}
        for powers,coef in pol.terms():out+=coef*moments[powers[0]]*moments[powers[1]]
        return sp.factor(out)
    assert gaussian_expect(err)==0
    assert sp.simplify(gaussian_expect(err**2)-(4*w*(p1*p1+p2*p2)+4*w*w)/Cs**2)==0
    assert above(VOLUME) and below(NTHERMAL,"0.019")
    assert above(LOCAL_MSE_UPPER)
    return {
      "actual_source_nonselective_spectral_law_preserved":True,
      "record_domain":"all z in R^2; no tail, failure, or stop records discarded",
      "local_record_model":"z=P+N(0,w I2), w=(Vhigh(f)+vm)/beta_f^2",
      "posterior_latent_weights":"prior(dp)*exp(-|z-p|^2/[2(v+w)]), normalized",
      "posterior_mean_P_given_z_p":"(w*p+v*z)/(v+w)",
      "posterior_covariance_P_given_z_p":"v*w/(v+w) I2",
      "posterior_mu":"[E_{p|z}|(w*p+v*z)/(v+w)|^2 + 2*v*w/(v+w)]/C",
      "posterior_mu_strict_lower":"2*v*w/[C*(v+w)] > 0",
      "posterior_mu_unbounded_at_large_record":True,
      "posterior_mean_tower_law":"E_z mu_z = original mu",
      "Bayes_risk_upper":"E Var(S0|z) <= 4*w*mu/C + 4*w^2/C^2",
      "complete_record_MSE_upper_using_all_modes":outward(LOCAL_MSE_UPPER),
      "global_scalar_source_posterior_and_local_vector_posterior_distinct":True,
      "policy_calibrated_to_fixed_original_prior":True,
      "arbitrary_unknown_input_universal_mean_feedback_proved":False,
      "measured_high_state_and_zero_high_correlations_can_be_reset_freely":False,
      "proof":"RECORDS.md"}
if __name__=="__main__":finish("records.py",result(),["RECORDS.md"])
