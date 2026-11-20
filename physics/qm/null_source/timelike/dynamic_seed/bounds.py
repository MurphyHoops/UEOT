"""New infinite-tail characteristic, uniqueness and nonresonant second-jet bounds."""
from fractions import Fraction as F
from common import *
K=256
def dnum(s,large=False):
    d=s*s/4-1
    value=-1+s*s/2-s**4/12
    for k in range(2,K+1):
        kk=iv.mpf(k);u=1/(kk*kk)
        value+=s*s*kk/3*(1+(iv.mpf(1)/2-s*s/4)*u-iv.sqrt(1-u)/(1+d*u))
    tail=iv.mpf(525 if large else 27)/(4*K*K)
    return value+interval(-tail,tail)
def Z(s,large=False):
    return dnum(s,large)+CA(X)*s**4/360-(CA(X)-29)*s*s/180-iv.mpf(1)/24
def H(s,large=False):
    return 2*(8*B(X)/3-D0+Z(s,large)/(4*iv.pi**2))+4*JN/3*(s*s+24)/(s*s+12)
def character(s,large=False):return s*s-4+H(s,large)/X
def Q2(s):
    r=s*s/(s*s+12)
    return s*s/2+2+(-8*B(X)-6*D0+JN*(-4+iv.mpf(10)*r/3)+
        (-iv.mpf(5)*Z(s)/2+iv.mpf(23)/48-s*s/4+3*s**4/8)/(2*iv.pi**2))/X
def result():
    # Rational derivative/Taylor bounds on sqrt(1-u)/(1+d*u).
    small=F(20,39)+F(400,169)+F(12800,2197)
    large=F(5,12)+F(105,16)+F(441,8)
    assert small<9 and large<63
    assert F(160,169)+F(10240,2197)<6
    assert F(3,4)>F(16,25) and F(27,64)>F(9,25)
    # Sum k^-3, k>=2, is <=1/8+integral_2^infty t^-3 dt=1/4.
    nsmall=1+F(9,2)+F(81,12)+F(27,8)
    nlarge=1+F(25,2)+F(625,12)+F(525,8)
    assert nsmall==F(125,8) and nlarge==F(3149,24)
    zsmall=nsmall+F(400*81,360)+F(400*9,180)+F(1,24)
    zlarge=nlarge+F(400*625,360)+F(400*25,180)+F(1,24)
    assert zsmall==F(377,3) and zlarge==F(3525,4)
    pi2lower=F(49,5)
    hsmall=F(16,60)+F(3,16)/pi2lower+zsmall/(2*pi2lower)+F(1,25)*F(25,13)
    hlarge=F(16,60)+F(3,16)/pi2lower+zlarge/(2*pi2lower)+F(1,25)*F(33,21)
    assert hsmall<8 and hlarge<47
    forcing_bound=F(8,20)+F(18,32)/pi2lower+F(12,100)+(
        F(5,2)*zsmall+F(23,48)+F(9,4)+F(243,8))/(2*pi2lower)
    assert forcing_bound<20
    zprime=21+120+40
    hprime=F(zprime,2)/pi2lower+F(1,25)*F(72,169)
    assert hprime<10
    assert F(47)+F(160,3)<101 and F(101+72,33)<6
    assert above(X,10**9) and below(abs(B(X)),iv.mpf(1)/20)
    assert above(CA(X)) and below(CA(X),400)
    assert above(JN) and below(JN,iv.mpf(3)/100)
    assert above(iv.pi**2,iv.mpf(49)/5)
    at1=-3+interval(-8,8)/X;at3=5+interval(-8,8)/X
    assert below(at1,0) and above(at3)
    derivative_lower=2-10/X
    assert above(derivative_lower)
    shift=8/(3*X)
    s=interval(2-shift,2+shift)
    for _ in range(5):
        candidate=iv.sqrt(4-H(s)/X)
        lo=max(s.a,candidate.a);hi=min(s.b,candidate.b)
        assert lo<hi
        s=interval(lo,hi)
    ds2=character(2*s,True)
    forcing=Q2(s)
    beta=-forcing/ds2
    beta_error=6/X
    assert above(ds2,11)
    assert below(abs(ds2-12),101/X)
    assert below(abs(forcing-4),24/X)
    assert below(abs(beta+iv.mpf(1)/3),beta_error)
    return {
        "base_history":"joint_history/history.json: cases.unfiltered",
        "x":outward(X),"thermal_Jn":outward(JN),
        "same_M2_U0_and_incoming_zero_spectrum":True,
        "numeric_response_terms_per_sum":K-1,
        "infinite_tail_included":True,
        "small_s_range":[1,3],"large_s_range":[3,5],
        "small_tail_term":"27/(2*k^3)","large_tail_term":"525/(2*k^3)",
        "tail_after_K_small":outward(iv.mpf(27)/(4*K*K)),
        "tail_after_K_large":outward(iv.mpf(525)/(4*K*K)),
        "derivative_tail_after_K":"18/K^2, 1<=s<=3",
        "coarse_H_abs_small":str(hsmall),"coarse_H_abs_large":str(hlarge),
        "coarse_H_derivative_abs":str(hprime),
        "characteristic_at_1":outward(at1),"characteristic_at_3":outward(at3),
        "characteristic_derivative_lower":outward(derivative_lower),
        "positive_root_unique_in_1_3":True,
        "positive_root_s":outward(s),
        "absolute_s_minus_2_upper":outward(shift)[1],
        "D_at_twice_root":outward(ds2),"Q2_at_root":outward(forcing),
        "beta":outward(beta),"absolute_beta_plus_one_third_upper":outward(beta_error)[1],
        "proper_growth_rate_model_units":outward(s/A),
        "proper_time_volume_quadratic":outward(3*beta+iv.mpf(3)/2),
        "certified_scope":"Infinite-sum renormalized second jet; no numerical finite-z remainder.",
        "chosen_finite_z_window":None,
        "nonlinear_SCE_existence_claimed":False,
        "complete_stochastic_source_constraint_solved":False}
if __name__=="__main__":finish("bounds.py",result())
