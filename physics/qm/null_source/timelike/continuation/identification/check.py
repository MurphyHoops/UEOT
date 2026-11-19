"""Finite-data stress-noise inference. Proof and scope: README.md.
Exact moment identities, general-contract controls and a local-pointer
conditional design. All generated data are synthetic.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import math
import numpy as np
from scipy.special import ndtr

HERE=Path(__file__).resolve().parent
TIMELIKE=HERE.parents[1]
ARCHIVE=TIMELIKE/"instrument/result.json"


def moment(law, k):
    return sum(p*x**k for x,p in law.items())


def alternative(delta, far):
    # Radial laws; positive radius means symmetric +/- atoms.
    v,b=F(3,4),F(3,2)
    base={F(0):1-v/b**2,b:v/b**2}
    law={F(0):base[F(0)]+delta/b**2-delta/far**2,
         b:base[b]-delta/b**2,far:delta/far**2}
    assert 0<delta<v and far>b and min(law.values())>0
    assert sum(law.values())==1 and moment(law,2)==moment(base,2)==v
    tv=sum(abs(law.get(x,0)-base.get(x,0)) for x in set(law)|set(base))/2
    assert tv==delta/b**2
    assert moment(law,4)-moment(base,4)==delta*(far**2-b**2)
    return base,law,tv


def finite_budget():
    n,eps=1_000_000,F(1,1000)
    delta=eps*F(9,4)/n
    rows=[]
    for far in map(F,(1000,1000000,1000000000)):
        base,law,tv=alternative(delta,far)
        rows.append(dict(far_amplitude=int(far),tail_probability_exact=str(law[far]),
            single_preparation_tv_exact=str(tv),all_output_tv_upper=float(n*tv),
            m4=float(moment(law,4)),m4_increase=float(moment(law,4)-moment(base,4))))
    assert rows[-1]["m4"]>1e9
    return dict(max_independent_preparations=n,total_tv_budget=float(eps),
        base_m4=float(moment(base,4)),alternatives=rows,
        confidence_consequence="uniform coverage 1-alpha implies P_base(U=infinity)>=1-alpha")


def quantum_contraction():
    # Independent finite-dimensional numerical control, not the proof.
    base,law,tv=alternative(F(1,20),F(13))
    def pure(x):
        z=np.array([1.,np.exp(.37j*float(x)),np.exp(.113j*float(x))])
        z/=np.linalg.norm(z)
        return np.outer(z,z.conj())
    def mix(radial):
        return sum(float(p)*(pure(x)+pure(-x))/2 for x,p in radial.items())
    a,b=mix(base),mix(law)
    one=float(np.abs(np.linalg.eigvalsh(a-b)).sum()/2)
    two=float(np.abs(np.linalg.eigvalsh(np.kron(a,a)-np.kron(b,b))).sum()/2)
    assert one<=float(tv)+1e-14 and two<=2*float(tv)+1e-14
    rng=np.random.default_rng(2026111901)
    q,_=np.linalg.qr(rng.normal(size=(6,6))+1j*rng.normal(size=(6,6)))
    anc=np.array([[.6,.1],[.1,.4]])
    pa=np.diag(q@np.kron(a,anc)@q.conj().T).real
    pb=np.diag(q@np.kron(b,anc)@q.conj().T).real
    measured=float(np.abs(pa-pb).sum()/2)
    assert measured<=one+1e-14
    return dict(source_tv=float(tv),quantum_one_copy=one,quantum_two_copies=two,
                ancilla_and_POVM_tv=measured)


def restoration():
    # These grids falsify implementation errors; the global inequality is proved in text.
    u=np.r_[np.linspace(0,3,10001),np.geomspace(3,1e5,2000)]
    for eta in (.5,1.,2.):
        assert np.max(1-np.sinc(u/np.pi)**4-(2/3)**(eta/2)*u**eta)<1e-13
    rng=np.random.default_rng(2026111902)
    for _ in range(100):
        xs=rng.uniform(-3,3,8); p=rng.dirichlet(np.ones(8)); t=rng.uniform(.05,2.)
        m4=float(p@xs**4); d=float(p@(16*np.sin(t*xs/2)**4/t**4))
        for eta in (.5,1.,2.):
            upper=d+(t*t/6)**(eta/2)*float(p@np.abs(xs)**(4+eta))
            assert d<=m4+1e-12 and m4<=upper+1e-12
    _,law,_=alternative(F(1,10**8),F(10**6))
    t=.4
    d=sum(float(p)*16*math.sin(t*float(x)/2)**4/t**4 for x,p in law.items())
    assert d<10 and float(moment(law,4))>9000 and max(law)>F(3,2)
    return dict(random_law_checks=300,
        unbounded_tail_negative_control=dict(bounded_readout_D=d,
            actual_m4=float(moment(law,4)),false_support_bound=1.6875,
            known_counterexample_violates_assumed_support=True),
        restoration="D_t<=m4<=D_t+(t^2/6)^(eta/2)*K_(4+eta), 0<eta<=2")


def h4(z,nu):
    return z**4-6*nu*z**2+3*nu**2


def h4_second_cap(B,v,nu,e):
    # Exact Hermite expansion around true noise nu+d, |d|<=e.
    m4,m6,m8=v*B**2,v*B**4,v*B**6
    plus=nu+e
    return (m8+12*e*m6+42*e**2*m4+36*e**3*v+9*e**4
            +plus*(16*m6+96*e*m4+144*e**2*v)
            +72*plus**2*(m4+2*e*v+e**2)+96*plus**3*v+24*plus**4)


def tail_bias(B,nu,e,R):
    plus=nu+e
    a=(R-B)/math.sqrt(plus)
    density=math.exp(-a*a/2)/math.sqrt(2*math.pi)
    i0=2*float(ndtr(-a))
    i2=2*(a*density+float(ndtr(-a)))
    i4=2*((a**3+3*a)*density+3*float(ndtr(-a)))
    error=((8*B**4+12*nu*B**2+3*nu**2+abs(h4(R,nu)))*i0
            +8*plus**2*i4+12*nu*plus*i2)
    return error,i0


def pointer():
    archive=json.loads(ARCHIVE.read_text()); s=archive["smooth"]
    m=float(s["means"][1]); g=float(archive["g"])
    W=float(s["covariance"][1][1])/g**2
    # lambda=1, finite minimum-uncertainty pointer, known shear compensated.
    var_q,var_p=W,1/(4*W)
    nu=(W+var_q)/m**2
    B,v,e=1.5,.75,.002
    second=h4_second_cap(B,v,nu,e)
    R=B+9*math.sqrt(nu+e)
    tail,tail_prob=tail_bias(B,nu,e,R)
    half_step=R/(2**40-1)
    decode_round=64*np.finfo(float).eps*max(1.,R)
    quant=(4*R**3+12*nu*R)*(half_step+decode_round)
    var_bias=6*e*v+3*e**2
    bias=tail+quant+var_bias
    gap=1.125; alpha=.025
    prospective=math.ceil(second/(alpha*(gap/2-bias)**2))+1
    assert R>math.sqrt((3+math.sqrt(6))*nu)
    # Check the uncertain-variance second-moment bound at both endpoints.
    for actual in (nu-e,nu,nu+e):
        for xs,ps in ((np.array([-math.sqrt(.75),math.sqrt(.75)]),np.array([.5,.5])),
                      (np.array([0.,-1.5,1.5]),np.array([2/3,1/6,1/6]))):
            d=actual-nu
            exact=float(ps@((xs**4+6*d*xs**2+3*d*d)**2
                +actual*(4*xs**3+12*d*xs)**2
                +2*actual**2*(6*xs**2+6*d)**2
                +96*actual**3*xs**2+24*actual**4))
            assert exact<=second*(1+1e-14)
    rng=np.random.default_rng(2026111903)
    n=200000; rows=[]; step=2*half_step
    for name in ("A","B"):
        if name=="A":
            x=rng.choice((-math.sqrt(.75),math.sqrt(.75)),size=n); truth=.5625
        else:
            x=rng.choice((0.,-1.5,1.5),size=n,p=(2/3,1/6,1/6)); truth=1.6875
        raw=x+rng.normal(0.,math.sqrt(nu),size=n)
        overflow=int(np.count_nonzero(np.abs(raw)>R))
        clipped=np.clip(raw,-R,R)
        indices=np.clip(np.round((clipped+R)/step),0,2**40-1)
        z=np.clip(-R+indices*step,-R,R)
        assert np.max(np.abs(z))<=R
        assert np.max(np.abs(z-clipped))<=half_step+decode_round
        estimate=float(np.mean(h4(z,nu)))
        standard=float(np.mean(z**4)-6*nu*np.mean(z**2)+3*nu**2)
        assert abs(estimate-standard)<1e-9
        width=math.sqrt(second/(n*alpha))+bias
        assert estimate-width<=truth<=estimate+width
        assert estimate-width<.5625 and estimate+width>1.6875
        rows.append(dict(candidate=name,synthetic_starts=n,kept_starts=n,
            overflow_flags=overflow,m4_truth=truth,hermite_estimate=estimate,
            ordinary_deconvolution_estimate=standard,
            interval_95_family=[max(v*v,estimate-width),min(v*B*B,estimate+width)],
            sum_z2=float(np.sum(z**2)),sum_z4=float(np.sum(z**4))))
    energy=s["energy_by_gate"][1]; field_scale=var_p/g**2
    missed=var_p/m**2; wrong=6*missed*v+3*missed**2
    assert wrong>gap
    return dict(reference_contract="instrument.state_scale: eta -1/8 to -1/16, same minimal field",
        archived_mode_values_are_numerical_not_UV_certificate=True,
        mean_m2=m,field_covariance_W22=W,effective_gaussian_variance=nu,
        pointer_var_Q=var_q,pointer_var_P=var_p,pointer_lambda=1.,
        shear_compensation_required=True,prior_source_support_B=B,known_source_m2=v,
        E_H4_squared_upper=second,
        finite_readout=dict(radius=R,bits=40,overflow_prob_upper=tail_prob,
            tail_bias_upper=tail,digitization_bias_upper=quant,decoder_roundoff_allowance=decode_round,
            effective_variance_calibration_radius_required=e,
            variance_bias_upper=var_bias,total_bias_upper=bias),
        prospective_starts_per_named_candidate_Chebyshev=prospective,
        prospective_starts_both_named_candidates=2*prospective,
        independent_calibration_starts_not_included=True,
        field_only_per_start={k:field_scale*energy[v] for k,v in
            (("delta_energy","E"),("switch_work","switch_work"),("metric_work","metric_work"))},
        synthetic_rows=rows,standard_baseline_uses_same_records_and_budget=True,
        ignored_pointer_shear_negative_control=dict(beta=1.,missed_variance=missed,m4_bias=wrong),
        status="CONDITIONAL_DESIGN_AND_SYNTHETIC_CHECK; NO_DEVICE_CERTIFICATION")


def main():
    return dict(baseline="a3ae75078ae903163bf0759fbd302e836aeeea84",
        input_sha256={str(ARCHIVE.relative_to(TIMELIKE)):hashlib.sha256(ARCHIVE.read_bytes()).hexdigest()},
        finite_budget=finite_budget(),quantum_contraction=quantum_contraction(),
        restoration=restoration(),local_pointer=pointer(),empirical_status="SYNTHETIC_ONLY")


def compare(expected, observed, path="root"):
    """Exact contracts/counts/hashes; tolerant floating diagnostics across BLAS platforms."""
    if isinstance(expected, dict):
        if not isinstance(observed, dict) or set(expected)!=set(observed):
            raise AssertionError(path+": object keys differ")
        for key in expected: compare(expected[key],observed[key],path+"."+key)
    elif isinstance(expected, list):
        if not isinstance(observed,list) or len(expected)!=len(observed):
            raise AssertionError(path+": list length differs")
        for i,(e,o) in enumerate(zip(expected,observed)): compare(e,o,path+f"[{i}]")
    elif isinstance(expected,float):
        if not isinstance(observed,float) or not math.isclose(expected,observed,rel_tol=1e-10,abs_tol=2e-8):
            raise AssertionError(path+f": float mismatch {expected} != {observed}")
    elif type(expected) is not type(observed) or expected!=observed:
        raise AssertionError(path+f": exact field differs {expected} != {observed}")


if __name__=="__main__":
    if not __debug__: raise RuntimeError("enable assertions")
    parser=argparse.ArgumentParser(); parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    rendered=json.dumps(main(),indent=2,sort_keys=True)+"\n"
    if args.check:
        compare(json.loads((HERE/"result.json").read_text()),json.loads(rendered))
        print("identification: exact alternatives, tail restoration, pointer accounting, 400000 synthetic starts PASS")
    else: print(rendered,end="")
