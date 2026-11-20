"""A concrete new controller counterterm and its joint stress/force Ward check."""
import sympy as sp
from common import *
def result():
    g,ch,Abox,Bgrad,R=sp.symbols("g chi A B R",real=True)
    vp=g*Abox/(2*(1+g*ch))-g*g*Bgrad/(4*(1+g*ch)**2)
    vm=-g*Abox/(2*(1-g*ch))-g*g*Bgrad/(4*(1-g*ch)**2)
    square=sp.series((vp*vp+vm*vm)/2,g,0,4).removeO()
    total=sp.series(vp+vm,g,0,4).removeO()
    assert sp.expand(square-g*g*Abox*Abox/4)==0
    assert sp.expand(total+g*g*(ch*Abox+Bgrad/2))==0
    a4_local=sp.series((vp*vp+vm*vm)/2-R*(vp+vm)/6,g,0,4).removeO()
    assert sp.expand(a4_local-g*g*(Abox*Abox/4+R*(ch*Abox+Bgrad/2)/6))==0
    t=sp.symbols("t");f=sp.Function("chi")(t)
    rho=sp.diff(f,t,2)**2-2*sp.diff(f,t,3)*sp.diff(f,t)
    pressure=-sp.diff(f,t,2)**2-2*sp.diff(f,t,3)*sp.diff(f,t)
    force=2*sp.diff(f,t,4)
    assert sp.simplify(-sp.diff(rho,t)-force*sp.diff(f,t))==0
    assert sp.simplify(rho+pressure+4*sp.diff(f,t,3)*sp.diff(f,t))==0
    return {
      "one_pair_flat_a4_chi_density_over_(4pi)^-2":"g_c^2*(Box chi)^2/4 + O(g_c^4)",
      "two_pair_flat_a4_chi_density_over_(4pi)^-2":"g_c^2*(Box chi)^2/2 + O(g_c^4)",
      "zeta_pole_one_pair":"-g_c^2/[8*s*(4*pi)^2] * integral (Box chi)^2",
      "finite_controller_counterterm_coefficient_fixed_by_free_AE_scheme":False,
      "new_counterterm":"c_chi*g_c^2*integral sqrt(-g)*(Box chi)^2",
      "controller_Euler_term":"2*c_chi*g_c^2*Box^2 chi",
      "counterterm_stress_and_force_Ward_verified":True,
      "target_and_probe_shift_symmetries_preserved":True,
      "Lorentzian_global_analytic_Wick_rotation_assumed":False,
      "Euclidean_a4_claimed_to_supply_retarded_or_noise_kernel":False,
      "renormalization_impossible_claimed":False,
      "finite_renormalized_controller_parameters_supplied":False,
      "proof":"RENORMALIZATION.md"}
if __name__=="__main__":finish("renormalization.py",result(),["RENORMALIZATION.md","kinetic_probe.json"])
