"""Fixed-mean gap identity and exact infinite thermal-shell resource curve."""
import math
import sympy as s
from common import *
h,b,z,c=s.symbols("h b z c",real=True)
# A=C+h-b, TC=C+h. Pointwise difference after zero-mean linear term.
expr=s.expand((c+h-b+z)**2-(c+h)**2-2*c*(z-b)-((z-b)**2+2*h*z))
assert expr==-2*b*h # h*b=0
q=s.symbols("q",positive=True)
def prob(j):return s.binomial(j+7,7)*(1-q)**8*q**j
def tail(r,k):
    if k<=0:return s.Integer(1)
    return q**k*sum(s.binomial(k+j-1,j)*(1-q)**j for j in range(r))
nth=q/(1-q)
rows=[];fixed=[]
for k in [0,1,2,4]:
    em=8*nth+sum((k-j)*prob(j) for j in range(k))
    sm=8*nth+72*nth**2+sum((k*k-j*j)*prob(j) for j in range(k))
    # Raw NB moment E N^2 = 8*n + 72*n^2.
    if k==0:
        exc=8*nth;exc2=8*nth+72*nth**2
    else:
        t0=tail(8,k+1);t1=8*nth*tail(9,k)
        t2=72*nth**2*tail(10,k-1)+t1
        exc=t1-k*t0;exc2=t2-2*k*t1+k*k*t0
    assert s.simplify(em-(k+exc))==0
    assert s.simplify(sm-(k*k+2*k*exc+exc2))==0
    # Evaluate the stable excess-moment expression with intervals.
    fun=s.lambdify(q,[exc,exc2],modules=[{"sqrt":iv.sqrt}])
    ei,e2i=fun(Q)
    vi=e2i-ei**2
    mean=k+ei
    assert above(vi)
    rows.append({"threshold_quanta":k,"apparatus_levels":k+1,
      "mean_total_quanta":outward(mean),"mean_apparatus_quanta":([0,0] if k==0 else outward(mean-8*N)),
      "minimum_variance_quanta_squared":outward(vi),
      "minimum_proper_energy_variance":outward(OMEGA**2*vi)})
    if k:
        less=1-tail(8,k)
        threshold=k-exc/less
        vv=exc2+exc**2/less
        checkmean=8*nth+sum((threshold-j)*prob(j) for j in range(k))
        checkvar=8*nth+72*nth**2+sum((threshold**2-j*j)*prob(j) for j in range(k))-k*k
        assert s.simplify(checkmean-k)==0 and s.simplify(checkvar-vv)==0
        fl=s.lambdify(q,[threshold,vv],modules=[{"sqrt":iv.sqrt}])
        ci,vi2=fl(Q)
        assert above(ci,k-1) and below(ci,k) and above(vi2)
        fixed.append({"total_mean_quanta":k,"apparatus_levels":k+1,
          "threshold_quanta":outward(ci),"apparatus_mean_quanta":outward(k-8*N),
          "minimum_variance_quanta_squared":outward(vi2)})
# Exact two-level pure-state counterexample: rho=|+><+|, A=diag(0,2), C=1.
rho=s.Matrix([[s.Rational(1,2)]*2]*2);bc=s.diag(1,0)
comm=rho*bc-bc*rho
assert comm.adjoint()*comm==s.eye(2)/4
# trace norm(comm)=1, Vclip=1/4, gap lower=1/4, true product minimum=1.
finish("compensation.py",{
 "exact_gap":"Var(A+B)-Vclip=< (B-bC)^2 >+2< (A-C)_+ B >",
 "quantum_gap":"Var(A+B)>=Vclip+norm1([rho,bC])^2/4",
 "full_marginal_attainability_iff":"[rho,bC]=0 with designed apparatus spectrum and normality",
 "unbounded_tail_zero_variance_at_finite_budget":False,
 "NOON_energy_degenerate_coherence_preserved":True,"thermal_resource_curve":rows,
 "fixed_total_mean_resource_curve":fixed,
 "finite_prefix_and_independent_infinite_tail_formulas_agree":True,
 "pure_counterexample":{"Vclip":"1/4","quantum_gap_lower":"1/4","actual_minimum":"1"},
 "physical_apparatus_stress_or_local_gate_constructed":False})
