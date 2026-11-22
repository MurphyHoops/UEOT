"""Fresh exact covariance, renormalized kernels, and fixed-AE conversion identities."""
import sympy as sp
from common import finish
R=sp.Rational
def result():
    w,V,V1,V2,h=sp.symbols("omega V V1 V2 h",real=True)
    f,g,f1,g1=sp.symbols("f g f1 g1")
    def eq(a,b=0):assert sp.cancel(a-b)==0,sp.factor(a-b)
    f2=(V-w*w)*f;g2=(V-w*w)*g
    f3=V1*f+(V-w*w)*f1;g3=V1*g+(V-w*w)*g1
    W=f*g;W1=f1*g+f*g1
    W2=f2*g+2*f1*g1+f*g2
    W3=f3*g+3*f2*g1+3*f1*g2+f*g3
    eq(W3+4*(w*w-V)*W1-2*V1*W)
    hp=V-h*h
    bare_p=f1*g1-h*W1+(h*h-w*w/3)*W
    bare_e=f1*g1-h*W1+(h*h+w*w)*W
    eq(bare_p,W2/2-hp*W-h*W1+2*w*w*W/3)
    eq(bare_e,W2/2-hp*W-h*W1+2*w*w*W)

    # Bare mode Ward identity for the new product representation.
    wd,wd1,wd2=sp.symbols("W W1 W2")
    hpp=V1-2*h*hp
    wd3=4*(V-w*w)*wd1+2*V1*wd
    ee=wd2/(4*w)-(hp*wd+h*wd1)/(2*w)+w*wd
    pp=wd2/(4*w)-(hp*wd+h*wd1)/(2*w)+w*wd/3
    eprime=wd3/(4*w)-(hpp*wd+2*hp*wd1+h*wd2)/(2*w)+w*wd1
    eq(eprime,h*(ee-3*pp))

    a,b,t=sp.symbols("a b t",positive=True)
    lam=a+b; beta=(a+2*b)/lam
    D=lambda z:z*z+4*w*w
    L=lambda z:-4*w/(3*D(z))
    Q=beta*(lam*lam+4*w*w/3)/(w*D(lam)*D(b))
    Qe=beta/(w*D(b))
    C=-lam/(w*D(b))
    Lren=-t**4/(12*w**3*D(t))
    Qren=beta/w*(2*lam*lam/(3*D(lam)*D(b))-b*b/(12*w*w*D(b)))
    Qeren=-beta*b*b/(4*w**3*D(b))
    Cren=lam*b*b/(4*w**3*D(b))
    eq(L(t)+1/(3*w)-t*t/(12*w**3),Lren)
    eq(Q-beta/(12*w**3),Qren)
    eq(Qe-beta/(4*w**3),Qeren)
    eq(C+lam/(4*w**3),Cren)
    eq(beta+(b+2*a)/lam,3)
    eq(sp.diff(t*t/D(t),t),8*t*w*w/D(t)**2)

    q=-1-V;q1=-V1;q2=-V2
    E1=(h*h-1)/2
    E3=(q*q-2*(h*h-1)*q+2*h*q1)/8
    P1=q/3+h*h/2+R(1,6)
    P3=-q*q/8-q2/12-(3*h*h+1)*q/12+h*q1/4
    Ae=h*h/2;Ap=h*h/2-V/3
    Ce=V*V/8+h*h*V/4-h*V1/4
    Cp=-V*V/8+h*h*V/4-h*V1/4+V2/12
    eq(Cp,V2/12+V*V/8-((V-h*h)*V+h*V1)/4)
    eq(Ce,3*V*V/8-((V-h*h)*V+h*V1)/4)
    eq(E1,Ae-R(1,2));eq(E3,Ce+Ae/2-R(1,8))
    eq(P1,Ap-R(1,6));eq(P3,Cp+Ap/2-R(1,24))

    # A fresh second-order witness is derived only from the new exact kernels.
    s=sp.symbols("s",positive=True)
    qp=Q.subs({a:s,b:s})
    cp=C.subs({a:s,b:s})
    p_second=s*s/(2*w)+L(2*s)*s*s+qp*s**4+cp*s**3
    eq(p_second,2*w*s*s/(3*(s*s+4*w*w)))
    e_second=s*s/(2*w)+Qe.subs({a:s,b:s})*s**4+cp*s**3
    eq(e_second,2*w*s*s/(s*s+4*w*w))
    # Full linear symbol: low modes, k=1 subtraction, all AE local tensors,
    # actual zero and thermal occupations, not merely a few evaluated roots.
    z,ca,dnum,bb,d0,jn,xx=sp.symbols("z CA Dnum B D0 Jn x",real=True)
    hh=t*z;v=t*t*z;a3=t**3*z;a4=t**4*z
    ell=(ca-19)/15+2*z
    H1=-36*a3*hh+72*v*hh*hh+18*v*v+36*hh*hh-18
    T1=-36*a4+144*a3*hh-216*v*hh*hh+108*v*v+72*v-72*hh*hh
    H3=3*hh**4+6*hh*hh+3
    T3=12*v*hh*hh-12*hh**4+12*v-12*hh*hh
    rn=(-H1/6+H3)/2880-H1/1728+(H1*(2+ell)/32-R(9,4)*(hh*hh*v+hh*hh))/36
    tn=(-T1/6+T3)/2880-T1/1728+(T1*(2+ell)/32-
        R(9,8)*(4*a3*hh-10*v*hh*hh+3*v*v+4*v-6*hh*hh+1))/36
    pn=(rn-tn)/3
    zchar=dnum+ca*t**4/360-(ca-29)*t*t/180-R(1,24)
    klinear=dnum+1+4*sp.diff(pn,z).subs(z,0)
    eq(klinear,zchar+1)
    R0=4*sp.pi**2*bb-R(1,2)
    K0=4*sp.pi**2*bb/3+4*sp.pi**2*d0-R(1,2)
    j=(1-(R0+K0)/(2*sp.pi**2*xx)-4*jn/(3*xx))/2
    uu=R(1,2)+j+K0/(2*sp.pi**2*xx)+jn/(3*xx)
    linear=t*t-4*j-2*uu+(klinear-2*K0)/(2*sp.pi**2*xx)+jn/xx*(-R(4,3)*t*t/(t*t+12)-R(2,3))
    frozen=t*t-4+2/xx*(8*bb/3-d0+zchar/(4*sp.pi**2))+4*jn/(3*xx)*(t*t+24)/(t*t+12)
    eq(linear,frozen)
    return {
      "exact_product_equation":"Theta(Theta^2+4*omega^2)W=4V*Theta(W)+2*Theta(V)*W",
      "constant_normalization":1,
      "exact_mode_Ward_identity":"Theta(e)=h*(e-3*p)",
      "positive_frequency_B_kernel":"beta(a,b)=(a+2b)/(a+b), 1<=beta<=2",
      "B_V_V_exact":"3*V^2/2",
      "pressure_Lren":"-t^4/[12*omega^3*(t^2+4*omega^2)]",
      "pressure_Qren":"beta/omega*[2*Lambda^2/(3*D(Lambda)*D(b))-b^2/(12*omega^2*D(b))]",
      "energy_Qren":"-beta*b^2/[4*omega^3*D(b)]",
      "Cren":"Lambda*b^2/[4*omega^3*D(b)]",
      "complete_high_Born_remainder_includes_h_W2":True,
      "omega_to_fixed_AE_k_conversion":"b*K0+A*K1+C*K3",
      "full_linear_DS_equals_frozen_response_for_every_positive_frequency":True,
      "zero_excluded_vacuum_linear_numerator":"K1=Z+1",
      "fixed_AE_coefficients":"T1=A-b/2, T3=C+A/2-b/8",
      "independent_second_order_pressure_witness":"2*omega*s^2/[3*(s^2+4*omega^2)]",
      "independent_second_order_energy_witness":"2*omega*s^2/(s^2+4*omega^2)",
      "exact_Jost_product_not_a_truncated_state":True,
      "symbolic_checks_are_full_formal_proof":False,
      "all_order_proof":"KERNELS.md"}
if __name__=="__main__":finish("kernels.py",result())
