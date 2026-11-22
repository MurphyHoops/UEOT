"""Exact ensemble/flag witnesses and calibrated proper-time coefficients."""
import sympy as sp
from common import finish
R=sp.Rational
def result():
    z0=sp.diag(1,0);z1=sp.diag(0,1)
    xp=sp.Matrix([[1,1],[1,1]])/2
    xm=sp.Matrix([[1,-1],[-1,1]])/2
    A=sp.diag(2,0)
    assert (z0+z1)/2==(xp+xm)/2==sp.eye(2)/2
    means=[sp.trace(A*r) for r in [z0,z1,xp,xm]]
    assert means==[2,0,1,1]
    Pz=[R(1,2),0,R(1,2)];Px=[0,1,0];outcomes=[0,1,2]
    assert sum(abs(a-b) for a,b in zip(Pz,Px))/2==1
    assert sum(a*g for a,g in zip(Pz,outcomes))==sum(a*g for a,g in zip(Px,outcomes))==1
    assert sum(a*g*g for a,g in zip(Pz,outcomes))==2
    assert sum(a*g*g for a,g in zip(Px,outcomes))==1
    assert sum(a*(g-1)**2 for a,g in zip(Pz,outcomes))==1
    assert sum(a*(g-1)**2 for a,g in zip(Px,outcomes))==0
    # A single CPTP flag-reading channel is possible on distinct flagged inputs.
    oz=sp.diag(z0/2,z1/2,sp.zeros(2),sp.zeros(2))
    ox=sp.diag(sp.zeros(2),sp.zeros(2),xp/2,xm/2)
    kraus=[]
    for flag,g in enumerate(means):
        for j in range(2):
            k=sp.zeros(3,8);k[g,2*flag+j]=1;kraus.append(k)
    assert sum((k.T*k for k in kraus),sp.zeros(8))==sp.eye(8)
    phi=lambda state:sum((k*state*k.T for k in kraus),sp.zeros(3))
    assert phi(oz)==sp.diag(*Pz) and phi(ox)==sp.diag(*Px)
    # A nontrivial adaptive covariant three-record witness, not a proof for all channels.
    ra=sp.diag(R(1,3),R(2,3),0);rb=sp.eye(3)/3
    def twirl(r):return sp.diag(r[0,0],(r[1,1]+r[2,2])/2,(r[1,1]+r[2,2])/2)
    assert twirl(ra)==twirl(rb)
    k0=sp.diag(R(1,2),R(2,3),R(2,3))
    k1=sp.diag(sp.sqrt(3)/2,sp.sqrt(5)/3,sp.sqrt(5)/3)
    l0=sp.diag(R(1,3),R(3,4),R(3,4))
    l1=sp.diag(2*sp.sqrt(2)/3,sp.sqrt(7)/4,sp.sqrt(7)/4)
    assert k0.T*k0+k1.T*k1==sp.eye(3)
    assert l0.T*l0+l1.T*l1==sp.eye(3)
    words={"stop":k0,"failure/success":l0*k1,"failure/failure":l1*k1}
    probs={}
    for name,k in words.items():
        aa=k*ra*k.T;bb=k*rb*k.T
        p=sp.simplify(sp.trace(aa))
        assert p==sp.simplify(sp.trace(bb))
        assert twirl(aa/p)==twirl(bb/p)
        probs[name]=str(p)
    assert sum(sp.Rational(v) for v in probs.values())==1
    # Proper time, with actual initial-volume normalization.
    e,w,b,r=sp.symbols("epsilon w beta r",real=True)
    tr=lambda expr:sp.series(expr,e,0,3).removeO().expand()
    z=e*r+e*e*(r-r*r)
    u=tr(z+b*z*z)
    u0=e+b*e*e
    logvol=tr(3*(u-u0))
    expected=3*e*(r-1)+3*e*e*((b-1)*(r*r-1)+(r-1))
    assert sp.simplify(logvol-expected)==0
    vol=tr(1+3*(u-u0)+R(9,2)*(u-u0)**2)
    expected_vol=1+3*e*(r-1)+e*e*((3*b+R(3,2))*r*r-6*r+R(9,2)-3*b)
    assert sp.simplify(vol-expected_vol)==0
    assert sp.simplify(vol.subs(r,1))==1
    past_u=(w-w*w)+b*w*w
    past_vol=sp.series(sp.exp(3*past_u),w,0,3).removeO().expand()
    assert sp.simplify(past_vol-(1+3*w+(3*b+R(3,2))*w*w))==0
    return {
        "unflagged_same_density_matrix":"I/2",
        "deterministic_pure_state_record_values":[2,0,1,1],
        "Z_record_distribution":["1/2","0","1/2"],
        "X_record_distribution":["0","1","0"],
        "total_variation_distance":1,"common_mean":1,"second_moments":[2,1],
        "bounded_effect_expectations":[1,0],
        "contradiction_scope":"No common affine channel on the same unflagged density input can realize both branchwise deterministic record laws.",
        "same_four_flag_CPTP_map_constructed_for_distinct_joint_inputs":True,
        "adaptive_covariant_finite_witness_probabilities":probs,
        "general_O2_dynamic_record_theorem":"Analytical proof in RECORDS.md, conditional on full joint twirl equality and a common causal constraint-preserving covariant instrument.",
        "finite_witness_substitutes_for_general_proof":False,
        "physical_gravity_channel_constructed":False,
        "all_nonlinear_gravity_excluded":False,
        "past_clock_volume_quadratic_coefficient":"3*beta+3/2",
        "initial_calibrated_volume_ratio":"1+3*epsilon*(r-1)+epsilon^2*((3*beta+3/2)*r^2-6*r+9/2-3*beta)",
        "clock_or_probe_instrument_constructed":False}
if __name__=="__main__":finish("records.py",result())
