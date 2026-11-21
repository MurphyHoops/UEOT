"""Certified smooth auxiliary past and finite-jet bounds, without an ODE integration."""
import sympy as sp
from common import *
def result():
    cosh=lambda t:(iv.exp(t)+iv.exp(-t))/2
    sinh=lambda t:(iv.exp(t)-iv.exp(-t))/2
    x=sp.symbols("x")
    density=2772*x**5*(1-x)**5
    assert sp.integrate(density,(x,0,1))==1
    assert sp.expand(density.subs(x,1-x)-density)==0
    derivative_caps=[4,23,316,3939,61850]
    critical_data=[]
    def polyeval(poly,xx):
        value=iv.mpf(0)
        for c in sp.Poly(poly,x).all_coeffs():
            value=value*xx+exact(int(c.p))/int(c.q)
        return value
    for j,cap in enumerate(derivative_caps,1):
        p=sp.diff(density,x,j-1)/sp.Rational(7,10)**j
        intervals=sp.polys.polytools.intervals(sp.diff(p,x),eps=sp.Rational(1,10**24))
        candidates=[(sp.Rational(0),sp.Rational(0)),(sp.Rational(1),sp.Rational(1))]
        candidates += [(lo,hi) for ((lo,hi),multiplicity) in intervals if lo>=0 and hi<=1]
        maximum=exact(0)
        for lo,hi in candidates:
            xx=iv.mpf([(exact(int(lo.p))/int(lo.q)).a,(exact(int(hi.p))/int(hi.q)).b])
            vv=abs(polyeval(p,xx))
            assert below(vv,cap)
            maximum=iv.mpf([0,max(maximum.b,vv.b)])
        critical_data.append({"derivative":j,"strict_cap":cap,
                              "maximum_absolute_enclosure":outward(maximum),
                              "critical_intervals":[[str(lo),str(hi)] for lo,hi in candidates]})
    zmin=cosh(exact("1.2"))-iv.sqrt(exact(23)/20)*sinh(exact("1.2"))
    assert above(zmin,(exact(4)/7)**3)
    assert below(cosh(exact("0.4")),exact(13)/12)
    assert below(iv.exp(iv.sqrt(exact(23)/20)/10),exact(9)/8)
    bmin=exact(4)/7;bmax=exact(9)/8
    v2max=max((bmin**2+exact(3)/20/bmin**4).b,
             (bmax**2+exact(3)/20/bmax**4).b)
    assert bool(v2max<(exact(4)/3)**2)
    b,v,z=sp.symbols("b v z");cs=sp.symbols("c0:6")
    vv=sp.expand(cs[0]**2*(v*v+b*b-2*z/b**4)+b*v*cs[1])
    def D(f):
        return sp.expand(b*(sp.diff(f,b)*cs[0]*v+
          sp.diff(f,v)*cs[0]*(b-2*z/b**5)+
          sum(sp.diff(f,cs[j])*cs[j+1] for j in range(5))))
    values={b:iv.mpf([bmin.a,bmax.b]),v:iv.mpf([(-exact(4)/3).a,(exact(4)/3).b]),
      z:iv.mpf([0,(exact(3)/20).b]),cs[0]:iv.mpf([0,1]),cs[1]:iv.mpf([0,4]),
      cs[2]:iv.mpf([-23,23]),cs[3]:iv.mpf([-316,316]),
      cs[4]:iv.mpf([-3939,3939]),cs[5]:iv.mpf([-61850,61850])}
    def evaluate(e):
        if e.is_Integer:return exact(int(e))
        if e.is_Rational:return exact(int(e.p))/int(e.q)
        if e.is_Symbol:return values[e]
        if e.is_Add:return sum((evaluate(t) for t in e.args),exact(0))
        if e.is_Mul:
            ans=exact(1)
            for t in e.args:ans*=evaluate(t)
            return ans
        if e.is_Pow:return evaluate(e.base)**int(e.exp)
        raise ValueError(e)
    caps=[10,95,1615,32568,811690]
    jets=[]
    for j,cap in enumerate(caps):
        bound=evaluate(vv);assert below(abs(bound),cap)
        jets.append({"order":j,"strict_cap":cap,"direct_interval":outward(bound),
                     "expanded_terms":len(sp.Add.make_args(vv))})
        if j<4:vv=D(vv)
    cir=exact(13)**2/12**2*(exact(7)/4)**6
    assert below(cir,34)
    return {
      "chi":"Beta(6,6) CDF on [-3/4,-1/20] convolved with fixed even smooth probability bump on [-1/20,1/20]",
      "actual_profile_is_C_infinity":True,
      "only_derivative_bound_uses_finite_smoothness_base":True,
      "chi_transition":[-0.8,0.0],"integral_chi_over_transition":"2/5",
      "chi_derivative_certificates":critical_data,
      "auxiliary_time_map":"s(tau)=integral_0^tau chi; constant -2/5 before -4/5; s=tau for tau>=0",
      "past_static_radius_ratio":["4/7","13/12"],
      "whole_auxiliary_and_future_radius_ratio":["4/7","9/8"],
      "future_tau_window":[0.0,0.1],
      "dimensionless_classical_velocity_absolute_upper":"4/3",
      "scaled_conformal_length_upper":"63/40",
      "scaled_h_absolute_upper":"4/3",
      "potential_jet_bounds":jets,
      "low_mode_proper_energy_constant_strict_upper":34,
      "low_mode_constant_rational_upper":outward(cir),
      "auxiliary_past_solves_physical_Einstein_equation":False,
      "auxiliary_profile_is_only_coordinate_change":False,
      "proof":"PROFILE.md"}
if __name__=="__main__":finish("profile.py",result(),["PROFILE.md"])
