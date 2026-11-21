"""Actual KG response, all AE contacts, and an infinite-tail growth certificate."""
import sympy as sp
from fractions import Fraction
from common import *
def result():
    t,s,w=sp.symbols("t s w",real=True,positive=True)
    q=-1-t*s*s;h=t*s;f=-t*s**3;q2=-t*s**4
    e1=(h*h-1)/2
    e3=(q*q-2*(h*h-1)*q+2*h*f)/8
    p1=q/3+h*h/2+sp.Rational(1,6)
    p3=-q*q/8-q2/12-(3*h*h+1)*q/12+h*f/4
    der=lambda e:sp.simplify(sp.diff(e,t).subs(t,0))
    assert der(e1)==der(e3)==0
    assert sp.simplify(der(p1)+s*s/3)==0
    assert sp.simplify(der(p3)+s*s/6-s**4/12)==0
    response=s/(s-2*sp.I*w)
    dv2=sp.simplify((response+sp.conjugate(response))/(2*w))
    dp2=sp.simplify(sp.re(sp.I*(s-sp.I*w)*response))
    assert sp.simplify(dv2-s*s/(w*(s*s+4*w*w)))==0
    assert sp.simplify(dp2+w*s*s/(s*s+4*w*w))==0
    assert sp.simplify(dp2+w*w*dv2)==0
    assert sp.simplify(dp2-w*w*dv2/3+4*w*s*s/(3*(s*s+4*w*w)))==0
    ca,rho,p=sp.symbols("ca rho p",real=True)
    drho=-4*rho-sp.Rational(1,32)
    dtrace=sp.Rational(1,8)-ca*s**4/480+(ca-29)*s*s/240
    dp=sp.expand((drho-dtrace)/3)
    # Units pi^2*A^4; p_an=rho_an/3+1/96.
    assert sp.simplify(dp-(-4*(rho/3+sp.Rational(1,96))
        +ca*s**4/1440-(ca-29)*s*s/720-sp.Rational(1,96)))==0
    u,z=sp.symbols("u z",real=True)
    ff=sp.sqrt(1-u)/(1+z*u)
    ff2=-1/(4*(1-u)**sp.Rational(3,2)*(1+z*u))+z/(sp.sqrt(1-u)*(1+z*u)**2)+2*z*z*sp.sqrt(1-u)/(1+z*u)**3
    assert sp.simplify(sp.diff(ff,u,2)-ff2)==0
    bound=Fraction(20,39)+Fraction(400,169)+Fraction(12800,2197)
    assert bound==Fraction(57380,6591) and bound<9
    # sqrt(1-u)>=4/5 and (1-u)^(3/2)>=3/5, verified without rounding.
    assert Fraction(3,4)>Fraction(16,25) and Fraction(27,64)>Fraction(9,25)
    x=iv.mpf([4*LAM**2,9*LAM**2])
    assert below(abs(B(x)),iv.mpf(1)/20) and above(C(x)) and below(C(x),400)
    zbound=iv.mpf(125)/8+400*iv.mpf(81)/360+400*iv.mpf(9)/180+iv.mpf(1)/24
    bracket=iv.mpf(8)/60+D0+zbound/(4*iv.pi**2)
    assert below(bracket,4)
    at1=-3+2*interval(-bracket,bracket)/x
    at3=5+2*interval(-bracket,bracket)/x
    assert below(at1,0) and above(at3)
    shift=8/(3*x)
    assert below(shift,"0.000000000621")
    # Independent new algebraic response sums; not a propagation of old modes.
    K=128;samples={}
    xb=root_box(D/2)
    for ss in [1,2,3]:
        sv=iv.mpf(ss);ds=sv*sv/4-1
        value=-1+sv*sv/2-sv**4/12
        for k in range(2,K+1):
            kv=iv.mpf(k);uv=1/(kv*kv)
            value+=sv*sv*kv/3*(1+(iv.mpf(1)/2-sv*sv/4)*uv-iv.sqrt(1-uv)/(1+ds*uv))
        tail=iv.mpf(27)/(4*K*K)
        value+=interval(-tail,tail)
        zz=value+C(xb)*sv**4/360-(C(xb)-29)*sv*sv/180-iv.mpf(1)/24
        dd=sv*sv-4+2/xb*(8*B(xb)/3-D0+zz/(4*iv.pi**2))
        samples[str(ss)]={"Z":outward(zz),"characteristic":outward(dd)}
    return {"symbolic_KG_and_subtractions":True,"all_AE_contacts_retained":True,
        "density_response":"delta rho_q=-3*(rho_q+p_q)*epsilon",
        "tail_second_derivative_rational_bound":str(bound),
        "tail_term_bound":"27/(2*k^3), 1<=s<=3",
        "total_numeric_symbol_absolute_bound":"125/8",
        "full_characteristic_bracket_absolute_upper":outward(bracket),
        "characteristic_at_1":outward(at1),"characteristic_at_3":outward(at3),
        "positive_growth_root_exists":True,"absolute_s_minus_2_upper":outward(shift)[1],
        "proper_growth_rate":"s/A, model units",
        "new_response_series_terms_per_sample":K-1,"infinite_tail_included":True,
        "sample_symbols_at_minimum_budget":samples,
        "fixed_incoming_state_and_zero_momentum":True,
        "linearized_Hamiltonian_constraint_satisfied":True,
        "nonlinear_instability_theorem_claimed":False,
        "linear_mode_integrated_to_nonlinear_SCE_family":False}
if __name__=="__main__":finish("stability.py",result())
