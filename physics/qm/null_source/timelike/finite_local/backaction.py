"""Exact Gaussian displacement stress/noise accounting and switching Ward identity."""
import sympy as sp
from common import finish
def result():
    xi,s,T,U,L,M,C,D=sp.symbols("xi s T U L M C D",real=True)
    expr=sp.expand((T+xi*L+xi**2*C)*(U+xi*M+xi**2*D))
    moments={0:1,1:0,2:s,3:0,4:3*s*s}
    avg=sum(co*moments[pow[0]] for pow,co in sp.Poly(expr,xi).terms())
    assert sp.expand(avg-(T+s*C)*(U+s*D)-s*L*M-2*s*s*C*D)==0
    alpha,g,varPi,Csrc=sp.symbols("alpha g varPi Csrc",real=True)
    assert sp.simplify(g*g*varPi*alpha*alpha/Csrc-alpha*alpha/(4*Csrc)*(4*g*g*varPi))==0
    # Two free stress divergences plus interaction stress; the controller term remains.
    coupling,chi,phi,psi,dphi,dpsi,dchi=sp.symbols("coupling chi phi psi dphi dpsi dchi")
    div_free=coupling*chi*(psi*dphi+phi*dpsi)
    div_interaction=-coupling*(dchi*phi*psi+chi*dphi*psi+chi*phi*dpsi)
    assert sp.expand(div_free+div_interaction+coupling*phi*psi*dchi)==0
    return {
      "u":"E_ret f in and after the coupling; E f agrees only in the common out region",
      "nonselective_displacement_variance":"s=1/(4vm)",
      "Hadamard_two_point_difference":"s*u tensor u, smooth",
      "mean_RSET_change":"s*T[u]",
      "complete_symmetric_noise_change":"s*<sym L L> + 2*s^2*T[u] tensor T[u]",
      "L":"T[phi+u]-T[phi]-T[u], linear in phi",
      "uncentered_L_second_moment_required":True,
      "zero_source_backaction":"Delta<S0>=alpha_f^2/(4*C*vm)",
      "shift_invariant_test_alpha_f_zero_preserves_source":True,
      "ordinary_bilinear_switching_Ward_remainder":"-coupling*phi*psi*d(chi)",
      "controller_source_required":"opposite of the displayed switching remainder",
      "exact_local_CPTP_algebra_is_total_gravity_device":False,
      "proof":"BACKACTION.md"}
if __name__=="__main__":finish("backaction.py",result(),["BACKACTION.md"])
