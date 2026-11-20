"""Uniform complex-parameter UV bounds and an actual positive-time residual window.

Cauchy's delta disk is applied only to the finite WKB5 local expression.
Exact Jost modes are compared to WKB at real frequencies by Volterra estimates.
"""
from fractions import Fraction as F
import sympy as sp
from common import *
RZ=F(1,16)
RDELTA=F(1,4)
K=8
def I(q):
    q=F(q)
    return iv.mpf(q.numerator)/q.denominator
def result():
    # Generic Riccati identities, independently reconstructed.
    vv=sp.symbols("V0:7",real=True)
    def Dt(e):return sp.expand(sum(sp.diff(e,vv[j])*vv[j+1] for j in range(6)))
    rr={1:-vv[0]}
    for n in range(1,6):
        rr[n+1]=sp.expand(Dt(rr[n])+sum(rr[j]*rr[n-j] for j in range(1,n)))
    expected=[
        -vv[0],-vv[1],-vv[2]+vv[0]**2,
        -vv[3]+4*vv[0]*vv[1],
        -vv[4]+5*vv[1]**2+6*vv[0]*vv[2]-2*vv[0]**3,
        -vv[5]+18*vv[1]*vv[2]+8*vv[0]*vv[3]-16*vv[0]**2*vv[1]]
    assert all(sp.expand(rr[j+1]-v)==0 for j,v in enumerate(expected))
    # Fresh local WKB5 expansion through delta^2, not an expansion of exact modes.
    d,h=sp.symbols("delta h",real=True)
    def tr(e):
        e=sp.expand(e)
        return sum(e.coeff(d,j)*d**j for j in range(3))
    TT=vv[0]*d/2+(vv[0]/2+(2*vv[0]**2-vv[2])/8)*d*d
    AA=vv[1]*d/4+(vv[1]/4+rr[4]/16)*d*d
    JJ=vv[0]*d/2+(vv[0]/2+rr[3]/8)*d*d
    expT=tr(1+TT+TT*TT/2)
    invsqrt=1+d/2+sp.Rational(3,8)*d*d
    fe=tr(expT*(d*(AA-h)**2+(1-d)*((1-JJ)**2+1))*invsqrt/2)
    fp=tr(expT*(d*(AA-h)**2+(1-d)*((1-JJ)**2-sp.Rational(1,3)))*invsqrt/2)
    q=-1-vv[0];f=-vv[1];q2=-vv[2]
    ed=[1,(h*h-1)/2,(q*q-2*(h*h-1)*q+2*h*f)/8]
    pd=[sp.Rational(1,3),q/3+h*h/2+sp.Rational(1,6),
        -q*q/8-q2/12-(3*h*h+1)*q/12+h*f/4]
    for j in range(3):
        assert sp.simplify(fe.coeff(d,j)-ed[j])==0
        assert sp.simplify(fp.coeff(d,j)-pd[j])==0
    # Uniform polynomial norms for complex |z|<=1/16, real 1<=s<=3, |beta|<=1.
    coefficients={1:F(1),2:F(5),3:F(4),4:F(4)}
    v_actual=[3**(j+2)*sum(c*m**j*RZ**m for m,c in coefficients.items()) for j in range(6)]
    vb=[F(3,4),F(3),F(13),F(61),F(343),F(2160)]
    assert all(v_actual[j]<vb[j] for j in range(6))
    v_integral=3*sum(c*RZ**m/m for m,c in coefficients.items())
    assert v_integral<F(7,32)
    assert 3*(RZ+2*RZ**2)<F(1,4)
    rb=[F(3,4),F(3),F(14),F(70),F(448)]
    assert vb[2]+vb[0]**2<rb[2]
    assert vb[3]+4*vb[0]*vb[1]<=rb[3]
    assert vb[4]+5*vb[1]**2+6*vb[0]*vb[2]+2*vb[0]**3<rb[4]
    r6=vb[5]+18*vb[1]*vb[2]+8*vb[0]*vb[3]+16*vb[0]**2*vb[1]
    assert r6<3300
    dc=[F(3300)]+[sum(rb[j-1]*rb[m-j-1] for j in range(1,6)
                     if 1<=m-j<=5) for m in range(6,11)]
    assert dc==list(map(F,[3300,1288,4648,17444,62720,200704]))
    # All defect polynomials have positive z degree; L1 <= disk norm for s>=1.
    rbound=sum(rb[j-1]/14**j for j in range(1,6))
    defect=sum(dc[m-5]/(2**m*7**(m-5)) for m in range(5,11))
    assert rbound<F(2,25) and defect<108
    mode_error=108*iv.exp(I(F(2,25)+F(1,32)))
    derivative_error=108*iv.exp(I(F(2,25)))*(1+I(F(1,32))*iv.exp(I(F(1,32))))
    assert below(mode_error,130) and below(derivative_error,124)
    W=iv.exp(I(F(2,25)))
    normal_error=124+I(F(1,4))*130/7
    normal_approx=W*(1+(I(F(2,25))+I(F(1,4)))/7)
    e_error=normal_approx*normal_error+W*130+(normal_error**2+130**2)/(2*7**6)
    p_error=normal_approx*normal_error+W*130/3+(normal_error**2+iv.mpf(130**2)/3)/(2*7**6)
    assert below(e_error,450) and below(p_error,360)
    assert F(64,63)**5<F(16,9)  # (k/omega)^5 < 4/3 for k>=8.
    # Local WKB disk bounds. The exact Jost family is NOT delta-analytic at zero.
    tb=F(3,4)/6+(2*F(3,4)**2+13)/72
    ab=F(3)/12+F(70)/144
    jb=F(3,4)/6+F(14)/72+F(448)/864
    assert tb==F(185,576)<F(1,3)
    assert ab==F(53,72)<F(3,4)
    assert jb==F(181,216)<F(7,8)
    e_disk=iv.exp(I(F(1,3)))/(2*iv.sqrt(I(F(3,4))))*(
        I(F(5,4))*((1+I(F(7,8)))**2+1)+I(F(1,4)))
    p_disk=iv.exp(I(F(1,3)))/(2*iv.sqrt(I(F(3,4))))*(
        I(F(5,4))*((1+I(F(7,8)))**2+I(F(1,3)))+I(F(1,4)))
    assert below(e_disk,6) and below(p_disk,5)
    assert F(6)*64/(1-F(1,16))<410
    assert F(5)*64/(1-F(1,16))<342
    assert 600+410<1100 and 600+342<1100
    # Exact two-field pressure: zero is explicit, k=1 subtraction remains.
    H=I(F(1,4));V,V1,V2=map(I,vb[:3])
    qm=1+V
    p1=qm/3+H**2/2+I(F(1,6))
    p3=qm**2/8+V2/12+(3*H**2+1)*qm/12+H*V1/4
    finite=iv.mpf(0);thermal_bare=None
    for k in range(2,K+1):
        omega=iv.sqrt(k*k-1)
        amp=iv.exp(I(F(7,32))/omega)
        norm=omega+(I(F(7,32))+H)*amp
        bare=(norm**2+omega**2*amp**2)/(2*omega)
        finite+=k*k*(bare+iv.mpf(k)/3+p1/k+p3/k**3)
        if k==2:thermal_bare=bare
    tail=I(F(550,K*K))
    a3=V1+H*V
    a4=V2+V**2+2*H*V1
    H1=36*a3*H+72*V*H**2+18*V**2+36*H**2+18
    T1=36*a4+144*a3*H+216*V*H**2+108*V**2+72*V+72*H**2
    H3=3*H**4+6*H**2+3
    T3=12*V*H**2+12*H**4+12*V+12*H**2
    gamma=I(RZ+RZ**2)
    assert below((CA(X)-19)/15+2+2*gamma,28)
    assert above((CA(X)-19)/15+2-2*gamma)
    ra=(H1/6+H3)/2880+H1/1728+(H1*28/32+I(F(9,4))*(H**2*V+H**2))/36
    ta=(T1/6+T3)/2880+T1/1728+(T1*28/32+I(F(9,8))*(
        4*a3*H+10*V*H**2+3*V**2+4*V+6*H**2+1))/36
    pa=(ra+ta)/3
    bracket=I(F(1,3))+p1+p3+finite+tail+4*pa
    # These are bounds of the fixed actual source, not new adjustable parameters.
    x_rhoz=box(HISTORY["fixed_M2"])*box(CASE["mu"])/(2*X**2)
    x_U=box(HISTORY["fixed_U0"])*X
    assert below(x_rhoz,iv.mpf(3)/5) and below(x_U,iv.mpf(101)/100)
    disc_bound=9*I(RZ+4*RZ**2)+H**2/2+I(F(1,2))+iv.mpf(3)/5*iv.exp(4*gamma)+iv.mpf(101)/100*iv.exp(2*gamma)
    disc_bound+=iv.exp(2*gamma)*bracket/(2*iv.pi**2*X)
    disc_bound+=4*N*thermal_bare*iv.exp(2*gamma)/(iv.pi**2*X)
    assert below(disc_bound,4)
    # Cauchy in z is justified by the exact-mode analyticity and uniform UV sum.
    radius=F(1,10000);ratio=radius/RZ;M=iv.mpf(4)
    spatial=M*I(ratio)**3/(1-I(ratio))
    gr=I(radius+radius**2)
    constraint=iv.exp(2*gr)*(1+2*I(radius))*M*I(radius)**4/(2*I(RZ)**3*(1-I(ratio)))
    normal_defect=3*iv.exp(2*gr)*constraint
    pressure_defect=2*iv.exp(2*gr)*spatial
    assert below(spatial,"0.00000001642")
    assert below(pressure_defect,"0.00000003284")
    assert below(normal_defect,"0.000000000002465")
    spatial_eta=3*M*I(ratio)**3*(3-2*I(ratio))/(1-I(ratio))**2
    h_real=3*I(radius)*(1+2*I(radius))
    pressure_normal=2*(spatial_eta+2*h_real*spatial)
    density_normal=h_real*(6*spatial+9*constraint)
    assert below(pressure_normal,"0.000000300") and below(density_normal,"0.0000000000300")
    jets=json.loads((HERE/"jet.json").read_text())
    bounds=json.loads((HERE/"bounds.json").read_text())
    assert jets["status"]==bounds["status"]=="PASS"
    assert bounds["positive_root_unique_in_1_3"]
    assert max(abs(v) for v in bounds["beta"])<1
    ss=box(bounds["positive_root_s"])
    epsilon=I(radius)*iv.exp(-ss)
    return {
        "disk_radius_z":str(RZ),"disk_radius_delta_for_local_WKB_only":str(RDELTA),
        "exact_Jost_modes_assumed_delta_analytic":False,
        "analytic_stress_uses_F_plus_times_F_minus":True,
        "complex_disk_full_state_is_physical":False,
        "real_parameter_exact_state_positive_CCR_Hadamard":True,
        "polynomial_derivative_bounds":[str(v) for v in v_actual],
        "V_L1_bound":str(v_integral),"Riccati_5_defect_coeff_bounds":[str(v) for v in dc],
        "Riccati_5_L1_and_sup_upper":str(rbound),"defect_omega5_L1_upper":str(defect),
        "real_frequency_Volterra_amplitude_error_coefficient":outward(mode_error),
        "real_frequency_Volterra_derivative_error_coefficient":outward(derivative_error),
        "WKB5_bare_AE_coefficients_match_exactly":True,
        "exact_bare_minus_AE_uniform_bound":"1100/k^5, k>=8, |z|<=1/16",
        "subtracted_stress_sum_tail_after_K":outward(tail),"K":K,
        "exact_spatial_residual_disk_bound":outward(disc_bound),
        "chosen_Cauchy_majorant":4,
        "real_window_z_radius":str(radius),
        "conformal_time_window":[0,1],
        "fixed_epsilon_definition":"epsilon=(1/10000)*exp(-s)",
        "fixed_epsilon_interval":outward(epsilon),
        "spatial_S_absolute_upper":outward(spatial)[1],
        "Hamiltonian_E_absolute_upper":outward(constraint)[1],
        "spatial_conformal_time_derivative_upper":outward(spatial_eta)[1],
        "a_cubed_times_normal_density_defect_derivative_upper":outward(density_normal)[1],
        "a_cubed_times_normal_pressure_defect_derivative_upper":outward(pressure_normal)[1],
        "x_times_orthonormal_density_defect_upper":outward(normal_defect)[1],
        "x_times_orthonormal_pressure_defect_upper":outward(pressure_defect)[1],
        "proper_time_duration_model_units":outward(interval(A*iv.exp(-gr),A*iv.exp(gr))),
        "same_actual_state_and_fixed_source_through_window":True,
        "timewise_parameter_reselection":False,
        "finite_positive_window_numerical_remainder_certified":True,
        "off_shell_approximate_mean_history_only":True,
        "exact_nonlinear_SCE_solution_constructed":False,
        "random_source_constraint_or_gravity_instrument_constructed":False,
        "proof_notes":"DYNAMICS.md: real-frequency Volterra, finite local delta Cauchy, then exact RSET z Cauchy and Ward."
    }
if __name__=="__main__":finish("window.py",result(),["jet.py","jet.json","bounds.py","bounds.json"])
