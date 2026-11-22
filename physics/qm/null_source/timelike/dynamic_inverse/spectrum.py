"""Exact pole/divided-difference identities supporting the complete spectrum proof."""
import sympy as sp
from common import *
def result():
    y,k=sp.symbols("y k",real=True)
    omega=sp.sqrt(k*k-1); d=y/4-1
    term=-4*k*k*omega*y/(3*(y+4*(k*k-1)))+y*k/3+(y/6-y*y/12)/k
    ak=k**3-k/2-k*k*omega
    rearranged=-y*(d+sp.Rational(1,2))*d/(3*k*(k*k+d))+y*ak/(3*(k*k+d))
    assert sp.simplify(term-rearranged)==0
    assert sp.simplify(sp.diff(term,y,3)+32*k*k*omega**3/(y+4*omega**2)**4)==0
    pole=-4*(k*k-1)
    assert sp.simplify(sp.limit((y-pole)*term,y,pole)-16*k*k*omega**3/3)==0
    assert sp.simplify(ak*(k**3-k/2+k*k*omega)-k*k/4)==0
    x,ca,jn=sp.symbols("x CA Jn",positive=True)
    N,HN=sp.symbols("N HN",real=True)
    lead=(-sp.Rational(1,12)-(HN-1)/12+ca/360)/(2*sp.pi**2*x)
    assert sp.simplify(lead-(ca/30-HN)/(24*sp.pi**2*x))==0
    thermal=4*jn*(y+24)/(3*x*(y+12))
    assert sp.simplify(sp.limit((y+12)*thermal,y,-12)-16*jn/x)==0
    b,r1,r2,W=sp.symbols("b r1 r2 W",positive=True)
    def divided_difference(expr):
        a=expr.subs(y,r1);c=expr.subs(y,r2)
        line=a+(y-r1)*(c-a)/(r2-r1)
        return sp.factor((expr-line)/((y-r1)*(y-r2)))
    assert sp.simplify(divided_difference(W/(y+b))-W/((b+r1)*(b+r2)*(b+y)))==0
    aa,bb,cc=sp.symbols("aa bb cc",real=True)
    assert sp.simplify(divided_difference(aa*y*y+bb*y+cc)-aa)==0
    yr,yi=sp.symbols("yr yi",real=True)
    f=W/((b+r1)*(b+r2)*(b+yr+sp.I*yi))
    assert sp.simplify(sp.im(f)+yi*W/((b+r1)*(b+r2)*((b+yr)**2+yi**2)))==0
    assert sp.simplify(sp.diff(W/((b+r1)*(b+r2)*(b+y)),y)+
                       W/((b+r1)*(b+r2)*(b+y)**2))==0
    # Exact correlated form used by the fast root certificate.
    C,L,H,R,c0=sp.symbols("C L H R c0",real=True)
    p=1+C*(sp.Rational(1,2)-(ca-29)/180)
    expr=c0/y+p+C*y*(ca/30-1-H)/12+C*H/6+C*R/3
    target=c0/y+1+C*y*L/12+C*(sp.Rational(89,180)-L/6+R/3)
    assert sp.simplify(expr.subs(H,ca/30-1-L)-target)==0
    # Independent third-derivative/origin and finite-N sufficient threshold checks.
    assert below(CA(X),400) and above(CA(X),0)
    assert below(characteristic_zero(),-3) and above(characteristic_zero(),-5)
    origin_lower=1-CA(X)/(360*iv.pi**2*X)-JN/(9*X)
    assert above(origin_lower,0)
    assert above(20*iv.log(2),iv.mpf(40)/3)
    assert above(5-8/X,0)
    return {
      "summand_rearrangement_exact":True,
      "positive_vacuum_pole_residue":"W_k=8*k^2*(k^2-1)^(3/2)/(3*pi^2*x)",
      "positive_thermal_residue_at_minus_12":"16*Jn/x",
      "divided_difference_identity_exact":True,
      "F_definition":"D(y)/((y-r1)*(y-r2)), r1 and r2 the two certified positive zeros",
      "imaginary_part":"Im F(y)=-Im y * sum W_k/((b_k+r1)*(b_k+r2)*abs(b_k+y)^2)",
      "real_derivative":"F'(y)=-sum W_k/((b_k+r1)*(b_k+r2)*(b_k+y)^2)",
      "series_convergence_scope":"Original response, imaginary part and differentiated F converge locally uniformly off poles; do not split the divergent real F constant and sum.",
      "characteristic_at_zero":outward(characteristic_zero()),
      "origin_y_derivative_strict_lower":outward(origin_lower),
      "CA":outward(CA(X)),
      "alternative_finite_truncation_quadratic":"a2_N=(CA/30-H_N)/(24*pi^2*x)",
      "alternative_finite_truncation_sufficient_N":2**20,
      "large_truncation_executed":False,
      "third_derivative":"D'''(y)=-16/(pi^2*x)*sum k^2*omega_k^3/(y+4*omega_k^2)^4-96*Jn/(x*(y+12)^4)",
      "analytic_proof":"SPECTRUM.md; identities here support but do not machine-formalize the infinite-dimensional theorem",
      "complete_spectrum_claim_conditional_inputs":"The inherited slow-root existence and new fast_root.json signs; see review.json",
      "right_half_s_plane_roots":2,
      "negative_y_interlacing":"One simple root in (-12,0) and between every consecutive negative pole",
      "nonreal_y_zeros":0,
      "full_nonlinear_uniqueness_proved":False
    }
if __name__=="__main__":finish("spectrum.py",result())
