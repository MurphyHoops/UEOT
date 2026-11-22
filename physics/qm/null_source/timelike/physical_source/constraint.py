"""A fixed-state FLRW linear stochastic constraint obstruction, with controls."""
import sympy as sp
from common import *
def result():
    e,a,m,u,h,cs,xi,b,v=sp.symbols("e A M U H Cstate xi b v",real=True)
    rho_geom=sp.Rational(3,2)*(h*h+1/(a*(1+e))**2)
    dgeom=sp.diff(rho_geom,e).subs({e:0,h:0})
    dind=-3/a**2
    assert sp.simplify(dgeom-dind)==0
    assert sp.diff(rho_geom,h).subs(h,0)==0
    # Keeping the state-energy integration constant explicitly avoids hiding a contract.
    residual=sp.simplify(2*dgeom*e-2*(dind*e+cs)-2*xi)
    assert residual==-2*(cs+xi)
    # Both exact static mean equations, with the radius equation substituted.
    bb,ee,d0,ll=sp.symbols("B E D L",real=True)
    k=ll*m/(2*a**6)
    UU=1/a**2-(2*bb/3-d0)/a**4
    substitution={ll*m:a**4-2*a*a*(4*bb/3+d0)}
    rho_total=2*bb/a**4+k+UU
    p_total=2*(bb/3+d0)/a**4+k-UU
    assert sp.simplify((rho_total-3/(2*a*a)).subs(substitution))==0
    assert sp.simplify((p_total+1/(2*a*a)).subs(substitution))==0
    # A genuine squeezed Hadamard finite-rank control permits short-time NEC<0.
    n,mc=sp.Rational(1,8),sp.Rational(3,8)
    assert mc*mc==n*(n+1)
    assert (4*n-2*mc)/3==-sp.Rational(1,12)
    assert 4*n/3==sp.Rational(1,6)
    # Classical diagnostic only: this is not a new quantum solution.
    dm,da=sp.symbols("dm da",real=True)
    expansion=sp.series((1+dm)/(1+da)**6+2-3/(1+da)**2,da,0,3).removeO()
    assert sp.expand(expansion-(dm-6*dm*da+(12+21*dm)*da**2))==0
    samples={}
    for name,budget,vr in [("minimum_equal_law",D/2,iv.mpf(3)/16),
                           ("zero_radial_noise",D,iv.mpf(0))]:
        x=root_box(budget)
        statevar=M*M*vr/(4*x**6)+M*(1+budget)/(4*iv.pi**2*x**5)+1/(16*iv.pi**4*x**4)
        assert above(statevar)
        samples[name]=outward(statevar)
    return {"complete_static_mean_equations_symbolically_verified":True,
        "normal_projected_geometric_density_variation":"-3*epsilon/A^2",
        "fixed_retarded_state_density_variation":"-3*epsilon/A^2",
        "with_extra_state_constant_constraint":"C_state+xi_rho=0",
        "fixed_state_contract":"C_state=0",
        "actual_total_energy_noise_variance":"M2^2*VarR/(4*A^12)+M2*(1+b)/(4*pi^2*A^10)+1/(16*pi^4*A^8)",
        "strict_positive_variance_intervals":samples,
        "fixed_state_homogeneous_linear_stochastic_completion_excluded":True,
        "lapse_or_linear_initial_H_resolves_obstruction":False,
        "general_gravity_completion_excluded":False,
        "squeezed_control":{"n":"1/8","m":"3/8","instant_NEC_in_Omega_over_V":"-1/12",
            "long_time_NEC_in_Omega_over_V":"1/6","positive_energy_in_Omega":"1/8"},
        "classical_only_constraint_diagnostic":"3*(A*H)^2=dm+12*da^2-6*dm*da+21*dm*da^2+O(da^3)",
        "normal_zero_mode_exact_energy_eigenstate_available":False,
        "next_gate":"lawful constraint-compatible joint state/geometry initial data and propagation",
        "quantum_second_order_contacts_and_joint_initial_family_certified":False}
if __name__=="__main__":finish("constraint.py",result())
