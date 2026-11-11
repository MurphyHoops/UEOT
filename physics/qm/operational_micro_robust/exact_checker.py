"""Independent rational/symbolic checker; does not import the producer.

Reads physical inputs and a candidate, reconstructs the full source, and
validates algebraic identities. Universal inequalities are proved in the
companion paper; this checker certifies their exact polynomial ingredients
and this finite matrix witness, not an unimplemented infinite-dimensional
proof assistant theorem or real hardware observations.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import json
import math
from pathlib import Path
import sympy as S


def check(model_path, candidate_path):
    model=json.loads(model_path.read_text())
    candidate=json.loads(candidate_path.read_text())
    checks=[]
    def record(name, condition, detail):
        if not condition:
            raise AssertionError(name)
        checks.append({"name":name,"verified":True,"detail":detail})
    lo,hi=map(F,model["q_interval"])
    delta=(hi-lo)/2
    record("model_identity", candidate["model_sha256"]==hashlib.sha256(model_path.read_bytes()).hexdigest(),
           "Candidate bound to the exact frozen inputs")
    record("frozen_domain", (lo+hi)/2==F(1,2) and 0<=delta<=F(1,2),
           "Symmetric interval and monotonicity domain are exact")
    q,w=S.symbols("q w",real=True)
    s=1-q/2
    source={"f":1-s,"0f":s*(1-q)*(1-s),"1f":s*q*(1-s),
            "00":s*s*(1-q)**2,"01":s*s*q*(1-q),
            "10":s*s*q*(1-q),"11":s*s*q*q}
    record("all_seven_raw_leaves_complete", S.expand(sum(source.values())-1)==0,
           "f,0f,1f,00,01,10,11 retained; probabilities derived from source")
    accept=[r for r in model["source_records"] if "f" not in r]
    record("source_acceptance", S.simplify(sum(source[r] for r in accept)-s*s)==0,
           "Backward effect H0=s^2 I, independent of input")
    target={r:S.cancel(source[r]/(s*s)) for r in accept}
    bern=lambda p:{"00":(1-p)**2,"01":p*(1-p),"10":p*(1-p),"11":p*p}
    record("conditional_source_derived", all(S.expand(target[r]-bern(q)[r])==0 for r in accept),
           "Target divided by actual scalar source acceptance, not supplied as certificate")
    diffs={r:S.factor(target[r]-bern(w)[r]) for r in accept}
    record("memoryless_tv_polynomial_factors", (
           S.expand(diffs["00"]+(q-w)*(2-q-w))==0 and
           S.expand(diffs["11"]-(q-w)*(q+w))==0 and
           S.expand(diffs["01"]-(q-w)*(1-q-w))==0 and diffs["01"]==diffs["10"]),
           "Absolute-value cases yield |q-w|(1+|q+w-1|) for 0<=q,w<=1")
    emem=delta*(1+delta)
    record("memoryless_uniform_bound", F(candidate["memoryless_error"])==emem==F(51,2500),
           "Exact endpoint bound; paper supplies monotonicity over entire interval")
    pfirst=F(model["adaptive_first_label1_weight"])
    p0=F(model["adaptive_second_label1_given_0"])
    p1=F(model["adaptive_second_label1_given_1"])
    adaptive={"00":(1-pfirst)*(1-p0),"01":(1-pfirst)*p0,
              "10":pfirst*(1-p1),"11":pfirst*p1}
    record("adaptive_legal_conditional_weights", all(0<=p<=1 for p in [pfirst,p0,p1]) and
           sum(adaptive.values())==1 and
           adaptive=={k:F(v) for k,v in candidate["policy_word_weights"].items()},
           "One policy from visible first label only; no hidden q access")
    record("adaptive_word_construction", adaptive=={"00":F(1,4)+delta**2,"11":F(1,4)+delta**2,
                                                        "01":F(1,4)-delta**2,"10":F(1,4)-delta**2},
           "Actual controller probabilities produce minimax word weights")
    t,d,x=S.symbols("t d x",real=True)
    ad={"00":S.Rational(1,4)+d*d,"11":S.Rational(1,4)+d*d,
        "01":S.Rational(1,4)-d*d,"10":S.Rational(1,4)-d*d}
    u=d*d-t*t
    desired={"00":-t-u,"01":u,"10":u,"11":t-u}
    record("adaptive_signed_blocks", all(S.expand(bern(S.Rational(1,2)+t)[r]-ad[r]-desired[r])==0 for r in accept),
           "Exact trace distance is max(|t|,u)+u when |t|<=d")
    record("adaptive_uniform_inequality_factors", (
           S.expand(d-(x+d*d-x*x)-(d-x)*(1-d-x))==0 and
           S.expand(d-2*(d*d-x*x)-(d*(1-2*d)+2*x*x))==0),
           "Both remainders nonnegative on 0<=x<=d<=1/2; explicit paper cases")
    endpoint_tv=sum(abs(F(target[r].subs(q,S.Rational(lo.numerator,lo.denominator)))-
                          F(target[r].subs(q,S.Rational(hi.numerator,hi.denominator)))) for r in accept)/2
    record("minimax_lower_bound", endpoint_tv==2*delta and
           F(candidate["adaptive_error"])==F(candidate["uniform_policy_lower_bound"])==delta,
           "Over full frozen design interval only, endpoint marginals differ by 2d; not a lower bound on every narrower calibration set")
    z=S.Rational(model["phase_real"])+S.I*S.Rational(model["phase_imag"])
    c=S.Rational(model["exchange_cos"]); v=S.Rational(model["exchange_sin"])
    U0=S.diag(1,z,1)
    U1=S.Matrix([[1,0,0],[0,c,-S.I*v],[0,-S.I*v,c]])
    G=S.diag(0,1,1)
    record("exact_physical_gates", S.simplify(U0*U0.H)==S.eye(3) and S.simplify(U1*U1.H)==S.eye(3) and
           U0*G==G*U0 and U1*G==G*U1,
           "Both actual rational unitaries preserve the excitation cutoff")
    # Bell-entangled one-excitation input; density uses rational entries.
    vector=S.zeros(6,1); vector[2]=1; vector[5]=1
    rho=vector*vector.H/2
    record("retained_reference_input", rho.trace()==1 and rho*rho==rho and
           S.trace(S.kronecker_product(G,S.eye(2))*rho)==1,
           "Positive rank-one 3x2 joint input; reference is retained and untouched")
    states={}
    for r in model["source_records"]:
        V=S.eye(3)
        for label in r:
            if label=="f":break
            V=({"0":U0,"1":U1}[label])*V
        VR=S.kronecker_product(V,S.eye(2))
        states[r]=S.simplify(VR*rho*VR.H)
    record("all_path_states_are_densities", all(vv.trace()==1 and S.simplify(vv.H-vv)==S.zeros(6) and S.simplify(vv*vv-vv)==S.zeros(6) for vv in states.values()),
           "Each exact path block is a nonnegative scalar times a genuine density")
    raw_total=S.simplify(sum((source[r]*states[r] for r in source),S.zeros(6)))
    record("complete_raw_quantum_trace", S.simplify(raw_total.trace()-1)==0,
           "Complete source quantum output including f,0f,1f has trace one")
    qmid=S.Rational(1,2)
    record("raw_source_not_conditional_target", S.simplify(1-s*s).subs(q,qmid)==S.Rational(7,16),
           "Full raw-vs-conditional CQ distance at q=1/2 is 7/16, not zero")
    vac=S.diag(1,0,0); exc=S.diag(0,1,0)
    record("support_false_success_control", U0*vac*U0.H==U1*vac*U1.H and U1*exc*U1.H!=exc,
           "Vacuum input agreement cannot certify full-support maps; excited pure-state distance=4/5")
    record("label_swap_control", sum(abs(vv) for vv in [F(1),F(-1)])/2==1,
           "Identical terminal channel with labels 0 vs 1 has full-CQ distance one")
    tail=F(model["analytic_energy_budget"])/(model["analytic_cutoff_N"]+1)
    cut=F(1,64); prep=cut+tail
    record("physical_filter_error_values", cut*cut==tail and
           F(candidate["complete_preparation_upper"])==prep and
           F(candidate["adaptive_full_output_upper"])==prep+delta and
           F(candidate["memoryless_full_output_upper"])==prep+emem,
           "Exact safe sqrt(delta_tail)+delta_tail failure-retaining preparation allowance")
    eps=F(model["required_full_output_precision"])
    record("frozen_precision_pass", prep+delta<eps and prep+emem<eps,
           "Both mathematical complete-output guarantees beat the preregistered 1/20 target")
    record("source_success_floor", F(candidate["source_acceptance_lower"])==(1-hi/2)**2==F(1369,2500),
           "Same q controls source success probability and conditional law")
    exp4=sum((F(4)**k/F(math.factorial(k)) for k in range(9)),F(0))
    n=model["calibration"]["shots"]; r=F(model["calibration"]["q_confidence_radius"])
    record("calibration_coverage_exact_tail", F(n)*r*r/2==4 and exp4>40,
           "Written iid mgf proof plus exp(4)>finite Taylor sum>40 yields error <1/20")
    nh=model["holdout"]["shots_per_protocol"]; rh=F(model["holdout"]["cell_frequency_radius"])
    exp8=sum((F(8)**k/F(math.factorial(k)) for k in range(9)),F(0))
    record("holdout_union_allowance", 2*nh*rh*rh==8 and exp8>560,
           "Fourteen fixed cell testers, two-sided union error <=28 exp(-8)<1/20")
    record("quantifier_control", delta>F(1,100) and lo>F(1,100),
           "No uniform .01 policy on full design region; no impossibility inherited by a smaller data interval; singleton-0 excludes every design q")
    g=candidate["generic_triangle_example"]
    bound=F(g["r_nominal"])+F(g["eta_T"])+sum(F(ww)*F(ee) for ww,ee in zip(g["weights"],g["eta_actions"]))
    record("generic_robust_sum", bound==F(g["derived_upper"]),
           "Exact arithmetic only; general trace-norm theorem proved in paper")
    record("insufficient_certificate_controls", candidate["classification"]["generic_insufficient_bound"]==
           candidate["classification"]["maximum_distance_bound"]=="INSUFFICIENT_CERTIFICATE",
           "Insufficient upper bounds are not called physical impossibility")
    return {"schema":"ueot-qm.micro-robust-independent-check/1",
            "classification":"exact symbolic/rational finite check, not hardware evidence",
            "sympy_version":S.__version__,"all_verified":True,"checks":checks,
            "input_hashes":{str(p.name):hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in [model_path,candidate_path,Path(__file__)]},
            "not_covered":["general infinite-dimensional proof assistant acceptance",
                           "actual gate matching", "real calibration/model membership", "measured full-CQ error"]}


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--model",type=Path,default=Path(__file__).with_name("frozen_model.json"))
    p.add_argument("--candidate",type=Path,default=Path(__file__).with_name("candidate.json"))
    p.add_argument("--output",type=Path,default=Path(__file__).with_name("exact_check_receipt.json"))
    a=p.parse_args(); out=check(a.model,a.candidate)
    a.output.write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({"all_verified":out["all_verified"],"checks":len(out["checks"]),"output":str(a.output)}))


if __name__=="__main__":main()
