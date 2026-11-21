"""Fresh exact KG, normal derivative, subtractions and full fixed-AE second jet."""
import sympy as sp
from common import finish
R=sp.Rational
def result():
    z,s,w,b,c=sp.symbols("z s w b c",real=True)
    def T(e):
        e=sp.expand(e)
        return sum(e.coeff(z,j)*z**j for j in range(3))
    def D(e):return T(s*z*sp.diff(e,z))
    def coef(e,j):return sp.simplify(sp.expand(e).coeff(z,j))
    def eq(a,b=0):assert sp.simplify(a-b)==0,sp.simplify(a-b)
    def expu(n):return 1+n*z+(n*b+R(n*n,2))*z*z
    h=s*z+2*s*b*z*z
    a2=T(D(h)+h*h)
    a3=T(D(a2)+h*a2)
    a4=T(D(a3)+h*a3)
    c1=s/(s-2*sp.I*w)
    c2=c1/2+b*s/(s-sp.I*w)
    v=1+c1*z+c2*z*z
    eq(coef(D(D(v))-2*sp.I*w*D(v)-a2*v,1))
    eq(coef(D(D(v))-2*sp.I*w*D(v)-a2*v,2))
    vp=T(D(v)-sp.I*w*v)
    normal=T(vp-h*v)
    wr=T(v*sp.conjugate(vp)-sp.conjugate(v)*vp)/(2*w)
    for j in range(3):eq(coef(wr,j),sp.I if j==0 else 0)
    e=T(normal*sp.conjugate(normal)+w*w*v*sp.conjugate(v))/(2*w)
    p=T(normal*sp.conjugate(normal)-w*w*v*sp.conjugate(v)/3)/(2*w)
    r=s*s/(s*s+4*w*w)
    eq(coef(e,0),w);eq(coef(e,1));eq(coef(e,2),2*w*r)
    eq(coef(p,0),w/3);eq(coef(p,1),-4*w*r/3)
    eq(coef(p,2),2*w*r/3-4*b*w*s*s/(3*(s*s+w*w)))
    # AE numerical subtractions use q=-1-a''/a, f=q', q2=q''.
    q=-1-a2;f=D(q);q2=D(f)
    e1=T((h*h-1)/2)
    e3=T((q*q-2*(h*h-1)*q+2*h*f)/8)
    p1=T(q/3+h*h/2+R(1,6))
    p3=T(-q*q/8-q2/12-(3*h*h+1)*q/12+h*f/4)
    for expr in [p1,p3]:eq(coef(expr.subs(b,0),2),-coef(expr,1)/2)
    eq(coef(e1.subs(b,0),2),-3*coef(p1,1)/2)
    eq(coef(e3.subs(b,0),2),-3*coef(p3,1)/2)
    # All local tensors, in units a^-4; trace convention rho-3p.
    H1=T(-36*a3*h+72*a2*h*h+18*a2*a2+36*h*h-18)
    T1=T(-36*a4+144*a3*h-216*a2*h*h+108*a2*a2+72*a2-72*h*h)
    H3=T(3*h**4+6*h*h+3)
    T3=T(12*a2*h*h-12*h**4+12*a2-12*h*h)
    ell=(c-19)/15+2*(z+b*z*z)
    rn=T((-H1/6+H3)/2880-H1/1728+
        (H1*(2+ell)/32-R(9,4)*(h*h*a2+h*h))/36)
    tn=T((-T1/6+T3)/2880-T1/1728+
        (T1*(2+ell)/32-R(9,8)*(4*a3*h-10*a2*h*h+
            3*a2*a2+4*a2-6*h*h+1))/36)
    pn=T((rn-tn)/3)
    ra=T(expu(-4)*rn).subs(b,0)
    pa=T(expu(-4)*pn).subs(b,0)
    dn,nr,np=sp.symbols("Dnum Nr0 Np0",real=True)
    # k=1 regular zero: bare numerator (1/2)*exp(-2u).
    # Its +1/2 correction is retained when summing the second pressure jet.
    rn_total=T(expu(-4).subs(b,0)*(nr-z+(-3*dn/2-R(1,2))*z*z)+4*ra)
    pn_total=T(expu(-4).subs(b,0)*(np+dn*z+(-dn/2+R(1,2))*z*z)+4*pa)
    zz=dn+c*s**4/360-(c-29)*s*s/180-R(1,24)
    eq(coef(rn_total,1),-4*coef(rn_total,0)-R(9,8))
    eq(coef(pn_total,1),-4*coef(pn_total,0)+zz)
    eq(coef(rn_total,2),8*coef(rn_total,0)-3*zz/2+R(63,16))
    eq(coef(pn_total,2),8*coef(pn_total,0)-9*zz/2+
        R(23,48)-s*s/4+3*s**4/8)
    # Independent recombination of both fields, actual zero and thermal shell.
    x,bb,d0,j,zzs=sp.symbols("x B D0 Jn Z",real=True)
    rq=bb/x**2;pq=(bb/3+d0)/x**2
    rzstd=1/(8*sp.pi**2*x**2);rt=j/x**2
    rz=(1/x-2*(rq+pq)+4*rzstd-4*rt/3)/2
    pq1=-4*pq+zzs/(4*sp.pi**2*x**2)
    pq2=8*pq+(-9*zzs/2+R(23,48)-s*s/4+3*s**4/8)/(4*sp.pi**2*x**2)
    rr=s*s/(s*s+12)
    pt1=2*pq1+12*rzstd-6*rz-R(4,3)*rt*(1+rr)
    pt2=2*pq2-36*rzstd+18*rz+(R(8,3)+6*rr)*rt
    char=s*s-1+x*pt1
    expected=s*s-4+2/x*(8*bb/3-d0+zzs/(4*sp.pi**2))+4*j/(3*x)*(s*s+24)/(s*s+12)
    eq(char,expected)
    forcing=s*s/2-1+2*x*pt1+x*pt2
    expected_q=s*s/2+2+(-8*bb-6*d0+j*(-4+R(10,3)*rr)+
        (-5*zzs/2+R(23,48)-s*s/4+3*s**4/8)/(2*sp.pi**2))/x
    eq(forcing,expected_q)
    return {
        "fixed_incoming_KG_coefficients":"c1=s/(s-2iw); c2=c1/2+beta*s/(s-iw)",
        "normal_derivative_used":"(v'-h*v)/a^2; canonical momentum a*(v'-h*v)",
        "second_order_KG_and_Wronskian_coefficients_exact":True,
        "truncated_mode_is_full_state":False,
        "all_fixed_AE_local_terms_and_log_derivatives_retained":True,
        "AE_trace_convention":"rho-3p",
        "reference_pressure_second_coefficient":"8*pq0+(-9*Z/2+23/48-s^2/4+3*s^4/8)/(4*pi^2*x^2)",
        "reference_density_second_coefficient":"8*rhoq0+(-3*Z/2+63/16)/(4*pi^2*x^2)",
        "standard_zero_removed_and_actual_fixed_P_zero_added":True,
        "thermal_pressure_second_coefficient":"(8/3+6*s^2/(s^2+12))*rho_th",
        "spatial_equation":"S=u''+(h^2+1)/2+a^2*p",
        "first_coefficient":"D_new(s)",
        "second_coefficient":"beta*D_new(2*s)+Q2(s)",
        "Q2":"s^2/2+2+[-8B-6D0+Jn*(-4+10*s^2/(3*(s^2+12)))+(-5Z/2+23/48-s^2/4+3*s^4/8)/(2*pi^2)]/x",
        "all_source_strengths_and_U0_fixed":True,
        "finite_positive_window_numerical_remainder_certified":False,
        "nonlinear_SCE_existence_claimed":False}
if __name__=="__main__":finish("jet.py",result())
