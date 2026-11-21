"""Offline equal-budget replay. Working files live beside this module."""
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
QM = HERE.parents[1]
BASE = QM / "cross_domain/field"
CASES = ["chapter71_local", "chapter71_antipodal", "strict_timelike", "strict_spacelike"]
ALLOC = [32768, 8192, 16384, 8192, 32768]  # per sign, after calibration
ALPHA = .05
TRANSFER = .005


def sha(data):
    return hashlib.sha256(data).hexdigest()


def sources(setting):
    # Fourier series of four independently convolved boxes and two displaced satellites.
    a,b,gap = (float(Fraction(setting[k])) for k in ("a","b","gap"))
    j = np.arange(641)
    ratio = (3/5)*np.sqrt(.75)/np.sinc(1/80)**4
    mix = 2*(1-ratio)
    f = np.sinc(j/80)**4*(1-mix+mix*np.cos(np.pi*j/3))
    w = np.sqrt(1+1.25*j*j)
    g = np.sqrt(2/w)*f
    g[0] = 1.
    A = -.3*g*np.expm1(1j*w*a)/w
    loc = (-1.)**j if setting["antipodal"] else np.ones_like(w)
    B = -.3*g*loc*np.exp(1j*w*(a+gap))*np.expm1(1j*w*b)/w
    return w,g,A,B


def chi(beta):
    # Gaussian characteristic function, n=.5, c=.25.
    return np.exp(-.5*np.vdot(beta,beta).real
                  -.5*np.vdot(beta[:2],beta[:2]).real
                  -.5*(beta[0].conjugate()*beta[1]).real)


def standard_path(history):
    # Ordered product D(v1)...D(vk) under one final joint field trace.
    total = np.zeros_like(history[0])
    phase = 0.
    for v in history:
        phase += np.vdot(v,total).imag
        total += v
    return np.exp(1j*phase)*chi(total)


def predict():
    settings = json.loads((BASE/"design.json").read_text())["experiments"]
    archived = json.loads((BASE/"result.json").read_text())["results"]
    results = {}
    for name,setting in zip(CASES,settings,strict=True):
        assert name == setting["id"]
        w,g,A,B = sources(setting)
        phase = 4*np.vdot(A,B).imag
        Q = 2*np.vdot(B,B).real+2*np.vdot(B[:2],B[:2]).real+2*(B[0].conjugate()*B[1]).real
        signed = np.exp(-Q)*np.sin(phase)
        direct = [standard_path([-s*A,B,B,s*A]) for s in (1,-1)]
        probs = [(1-z.imag)/2 for z in direct]
        np.testing.assert_allclose(probs[1]-probs[0], signed, atol=5e-15)
        lo,hi = map(lambda x: float(Fraction(x)),archived[name]["p_plusY"])
        if not lo-4e-15 <= probs[0] <= hi+4e-15:
            raise AssertionError(f"{name}: standard p={probs[0]} outside [{lo},{hi}]")
        short = standard_path([-A[:2],B[:2],B[:2],A[:2]])
        # Uniform delay derivative, including the omitted vacuum shells.
        tail_E = 2*(80/np.pi)**8/(9*(5/4)*640**9)
        derivative = (4*np.sum(w*abs(A*B)) + 16*.3**2*tail_E
                      + 2*(w[1]-w[0])*abs(B[0]*B[1]))/2
        results[name] = dict(delay_slope_p_upper=derivative,phase=phase,Q=Q,delta=signed,plus_minus_p=probs,
                             two_mode_delta=short.imag, reset_delta=0.,
                             original_field_energy=np.sum(w*(abs(A)**2+abs(B)**2)))
    return results


def radii(n):
    # One-sided Hoeffding union over <=64 registered endpoints.
    return math.sqrt(math.log(64/ALPHA)/(2*n))


def bracket(y):
    eps = radii(len(y))
    plus = np.mean(y==1)
    unknown = np.mean(y==2)
    return [max(0.,plus-eps),min(1.,plus+unknown+eps)]


def calibrate(tags,sign,records):
    result = {}
    eligible = True
    for s in (0,1):
        cells = []
        for truth in (0,1):
            halves = [records[(tags==2*period+truth)&(sign==s)] for period in (0,1)]
            assert all(len(h)==8192 for h in halves)
            l1,u1 = bracket(halves[0])
            l2,u2 = bracket(halves[1])
            detected_drift = max(0.,l1-u2,l2-u1)
            if detected_drift > .05:
                eligible = False
            pooled = bracket(np.concatenate(halves))
            cells.append(dict(p_plus=pooled,pre_post_gap_lower=detected_drift))
        if cells[1]["p_plus"][0] <= cells[0]["p_plus"][1]:
            eligible = False
        result[str(s)] = cells
    return result,eligible


def invert_readout(y,ref):
    # Forward q=(1-p)a+p b plus transferable probability error of either sign.
    a,b = (c["p_plus"] for c in ref)
    q = bracket(y)
    lo = (q[0]-TRANSFER-a[1])/(b[1]-a[1])
    hi = (q[1]+TRANSFER-a[0])/(b[0]-a[0])
    feasible = [max(0.,lo),min(1.,hi)]
    if feasible[0] > feasible[1]:
        return None, {"reason":"observed_probability_outside_calibrated_dynamic_range",
                      "observed_probability_interval":q,
                      "calibrated_dynamic_range":[max(0.,a[0]-TRANSFER),min(1.,b[1]+TRANSFER)]}
    return feasible, None


def score(records, pred):
    tags,sign,bits,det = unpack(records)
    ref,eligible = calibrate(tags,sign,bits)
    out = {}
    for k,name in enumerate(CASES):
        arms = []
        conflicts = {}
        point = []
        counts = []
        for s in (0,1):  # 0 => A=+, 1 => A=-
            ys = bits[(tags==4+k)&(sign==s)]
            if len(ys) != ALLOC[k]:
                raise ValueError(f"{name}: bad number of starts")
            counts.append(np.bincount(ys,minlength=3).tolist())
            point.append(np.mean(ys==1))
            if eligible:
                arm,error = invert_readout(ys,ref[str(s)])
                if error is None:
                    arms.append(arm)
                else:
                    conflicts[("A+","A-")[s]] = error
        ci = [arms[1][0]-arms[0][1],arms[1][1]-arms[0][0]] if len(arms)==2 else None
        out[name] = dict(counts_minus_plus_loss_by_sign=counts,
                         observed_plus_per_start_contrast=point[1]-point[0],latent_delta_CI=ci)
        if conflicts:
            out[name].update(status="reject_setting_calibration_transfer",conflicts_by_arm=conflicts)
        if ci is not None:
            out[name].update({key:bool(ci[0]<=pred[name][key]<=ci[1])
                              for key in ("delta","reset_delta","two_mode_delta")})
    return dict(calibration_by_sign=ref,eligible=eligible,cases=out)


def pack(tags,sign,bits,det):
    return (tags | (sign<<4) | (bits<<5) | (det<<7)).astype("uint16")


def unpack(raw):
    return raw&15,(raw>>4)&1,(raw>>5)&3,(raw>>7)&3


def generate(pred,gate,control=None):
    schedule = np.random.Generator(np.random.PCG64(94054103))
    cal_rng = np.random.Generator(np.random.PCG64(94054101))
    hold_rng = np.random.Generator(np.random.PCG64(94054102))

    def block(groups):
        pairs = np.concatenate([np.tile([t,s],(n,1)) for t,s,n in groups])
        schedule.shuffle(pairs,axis=0)
        return pairs

    def calibration(period):
        rows = block([(2*period+b,s,8192) for b in (0,1) for s in (0,1)])
        tags,sign = rows.T
        truth = tags%2
        readout = np.where(truth==0,.015,.975)
        if control=="drift" and period==1:
            readout = np.where((truth==0)&(sign==0),readout+.18,readout)
        y = (cal_rng.random(len(rows))<readout).astype(int)
        y[cal_rng.random(len(rows))<.002] = 2
        return pack(tags,sign,y,np.full(len(rows),3))

    pre = calibration(0)
    rows = block([(4+k,s,n) for k,n in enumerate(ALLOC) for s in (0,1)])
    tags,sign = rows.T
    u = hold_rng.random(len(rows))
    probs = np.array([pred[name]["plus_minus_p"] for name in CASES])
    if control in ("reset","selection","hidden_offset"):
        probs = np.full_like(probs,.5)
    physics = np.zeros(len(rows),dtype=int)
    detector = np.full(len(rows),3,dtype=int)
    original = tags < 8
    physics[original] = u[original] < probs[tags[original]-4,sign[original]]
    for s in (0,1):
        mask = (tags==8)&(sign==s)
        # Gate table in (B=0,D=0),(0,1),(1,0),(1,1) order.
        idx = np.searchsorted(np.cumsum(gate[s]),u[mask])
        physics[mask],detector[mask] = idx//2,idx%2
    readout = np.where(physics==0,.015,.975)
    if control=="hidden_offset":
        delta = pred[CASES[0]]["delta"]
        readout = np.where(tags==4, .495 + (2*sign-1)*.96*delta/2,readout)
    y = (hold_rng.random(len(rows))<readout).astype(int)
    failure = hold_rng.random(len(rows))<.002
    if control=="selection":
        # A+ (s=0) should lose positives; A- should lose negatives.
        reject = (tags==4)&(y!=sign)
        failure |= reject & (hold_rng.random(len(rows))<.30)
    y[failure] = 2
    active = detector != 3
    # The added detector is an ideal synthetic readout with an explicit erasure channel.
    detector[active & (hold_rng.random(len(rows))<.002)] = 2
    post = calibration(1)
    return np.concatenate([pre,pack(tags,sign,y,detector),post]).astype("<u2")


def local_gate(k=-.1,last=640):
    setting = json.loads((BASE/"design.json").read_text())["experiments"][0]
    w,g,A,B = (v[:last+1] for v in sources(setting))
    C = -k*g*np.exp(1j*w*(65/12))*np.expm1(1j*w*.4)/w
    rho0 = np.kron(np.ones((2,2))*.5,[[.8,.32+.24j],[.32-.24j,.2]])
    y = np.array([[0.,-1j],[1j,0.]])
    x = np.array([[0.,1.],[1.,0.]])
    eye = np.eye(2)
    proj_y = [(eye-y)/2,(eye+y)/2]
    proj_e = [(eye+x)/2,(eye-x)/2]
    labels = [(u,v) for u in (1,-1) for v in (1,-1)]
    out = []
    for s in (1,-1):
        rho = np.zeros_like(rho0)
        energy_before = energy_after = 0.
        for i,(u,v) in enumerate(labels):
            prior = s*A+u*B
            energy_before += rho0[i,i].real*np.sum(w*abs(prior)**2)
            energy_after += rho0[i,i].real*np.sum(w*abs(prior+v*C)**2)
            for j,(a,b) in enumerate(labels):
                trace = standard_path([-s*A,-a*B,-b*C,v*C,u*B,s*A])
                rho[i,j] = rho0[i,j]*trace
        if np.linalg.eigvalsh(rho).min() < -1e-13:
            raise AssertionError("negative joint state")
        np.testing.assert_allclose(rho,rho.conj().T,atol=2e-13)
        joint = np.array([[np.trace(rho@np.kron(pb,pc)).real for pc in proj_e] for pb in proj_y])
        assert joint.min()>=0 and abs(joint.sum()-1)<1e-13
        p_b,p_c = joint.sum(axis=1)[1],joint.sum(axis=0)[1]
        e_c = .5*(p_c-.18)
        e_f = energy_after-energy_before
        np.testing.assert_allclose(e_f,np.sum(w*(abs(C)**2+1.2*s*(A.conj()*C).real)),
                                   atol=2e-14)
        # Edge work from the actual lab force at both switches.
        onset = 65/12
        edge_on = 2*k*np.sum(g*(s*.6*A*np.exp(-1j*w*onset)).real)
        edge_off = -2*k*np.sum(g*((s*.6*A+C)*np.exp(-1j*w*(onset+.4))).real)
        np.testing.assert_allclose(edge_on+edge_off,e_f,atol=3e-14)
        bits = -np.sum(joint*np.log2(joint))
        out.append(dict(joint_B_C=joint.tolist(),B_p_plus=p_b,C_p_excited=p_c,
                        covariance_B_C=joint[1,1]-p_b*p_c,
                        field_increase=e_f,C_increase=e_c,net_gate_work=e_f+e_c,
                        turn_on_work=edge_on, turn_off_work=edge_off,axis_work=e_c,
                        local_field_energy_after_AB=energy_before,
                        field_energy_after_ABC=energy_after,record_bits=bits,
                        degenerate_memory_reset_lower_bound=.25*bits*np.log(2),
                        conditional_C_reprepare_work=-e_c,
                        source_preps_per_C_excitation=1/p_c))
    return out


def assess_gate(data,gate):
    tags,sign,bits,det = unpack(data)
    out = []
    for s in (0,1):
        active = (tags==8)&(sign==s)
        b,c = bits[active],det[active]
        both = np.bincount((3*b+c).astype(int),minlength=9).reshape(3,3)
        lo,hi = bracket(c)
        ci = [max(0.,lo-TRANSFER),min(1.,hi+TRANSFER)]
        out.append(dict(counts_3x3=both.tolist(),C_p_interval=ci,
                        standard_in_interval=bool(ci[0]<=gate[s]["C_p_excited"]<=ci[1]),
                        gate_off_in_interval=bool(ci[0]<=.18<=ci[1])))
    return out


def entropy(probabilities):
    p = np.asarray(probabilities)
    return -np.sum(p[p>0]*np.log2(p[p>0]))


def resources(data,pred,gate):
    # Columns are true states; rows recorded (-,+,erasure) outcomes.
    b_map = np.array([[.985,.025],[.015,.975]])*.998
    b_map = np.vstack([b_map,[.002,.002]])
    c_map = np.array([[.998,0.],[0.,.998],[.002,.002]])
    tables = np.array([q["joint_B_C"] for q in gate])
    logged = np.array([b_map@q@c_map.T for q in tables])
    np.testing.assert_allclose(logged.sum(axis=(1,2)),[1.,1.])
    ideal_conditional = np.mean([entropy(q) for q in tables])
    ideal_mixed = entropy(tables.mean(axis=0))
    log_conditional = np.mean([entropy(q) for q in logged])
    log_mixed = entropy(logged.mean(axis=0))
    total_bits = 32768*(entropy(b_map[:,0])+entropy(b_map[:,1]))
    for name,n in zip(CASES,ALLOC[:4],strict=True):
        for p in pred[name]["plus_minus_p"]:
            total_bits += n*entropy(b_map@np.array([1-p,p]))
    total_bits += 2*ALLOC[-1]*log_conditional
    tags,sign,b,c = unpack(data)
    if (len(data)!=262144 or np.any(data>>9) or np.any(tags[:32768]>1)
        or np.any((tags[-32768:]<2)|(tags[-32768:]>3))
        or np.any((tags[32768:-32768]<4)|(tags[32768:-32768]>8))):
        raise ValueError("incomplete or invalid ordered attempt stream")
    for j,n in enumerate(ALLOC):
        if any(np.count_nonzero((tags==j+4)&(sign==s))!=n for s in (0,1)):
            raise ValueError(f"unbalanced attempt allocation in setting {j}")
    if np.any(tags>8) or np.any(b>2) or np.any(c[tags==8]>2) or np.any(c[tags<8]!=3):
        raise ValueError("impossible raw record")
    return dict(field_preparations=len(data),source_A_gates=len(data),source_B_gates=len(data),
                calibration_reference_injections=65536,C_gates=int(sum(tags==8)),
                B_readouts=len(b),C_readouts=int(sum(c!=3)),B_loss=int(sum(b==2)),
                C_loss=int(sum(c==2)),B_or_C_loss=int(sum((b==2)|(c==2))),
                raw_bytes=data.nbytes,all_record_entropy_bits_given_schedule=total_bits,
                all_record_isothermal_reset_work_lower_bound=.25*np.log(2)*total_bits,
                gate_ideal_bits_sign_known=ideal_conditional,gate_ideal_bits_sign_unknown=ideal_mixed,
                gate_logged_bits_sign_known=log_conditional,gate_logged_bits_sign_unknown=log_mixed,
                same_carrier_extra_reset_work_unknown_sign=.25*np.log(2)*(log_mixed-log_conditional))


def design_power(delta):
    # Analytic lower bound under the registered, stationary synthetic alternative.
    t=.015
    rc,rh = radii(16384)+t, radii(32768)+t
    def envelopes(q,r):
        return max(0.,.998*q-r),min(1.,.998*q+.002+r)
    alo,ahi=envelopes(.015,rc)
    blo,bhi=envelopes(.975,rc)
    qminus=.015+.96*(1+delta)/2
    qplus=.015+.96*(1-delta)/2
    lo=(envelopes(qminus,rh)[0]-TRANSFER-ahi)/(bhi-ahi)
    hi=(envelopes(qplus,rh)[1]+TRANSFER-alo)/(blo-alo)
    # 8 one-sided pooled-reference endpoints, 4 held endpoints, 16 pre/post endpoints.
    fail = 8*np.exp(-2*16384*t*t)+4*np.exp(-2*32768*t*t)+16*ALPHA/64
    if lo<=hi or blo<=ahi:
        raise AssertionError("reference noise leaves no guaranteed separation")
    return dict(primary_delta_lower_on_good_event=lo-hi,power_lower=1-fail,
                assumptions="registered noise, independent stationary starts, fixed allocation")


def peer_check(gate):
    peer = json.loads((HERE.parent/"local/result.json").read_text())["cases"][CASES[0]]
    keys = {"C_p_excited":"p_C_e","B_p_plus":"p_B_plusY",
            "field_increase":"delta_E_F","axis_work":"axis_pump","turn_on_work":"switch_on",
            "turn_off_work":"switch_off","net_gate_work":"net_drive_C_stage",
            "covariance_B_C":"p_Yplus_e_minus_product"}
    count = 0
    for sig,q in zip(("+","-"),gate,strict=True):
        intervals = [(q[key],peer[sig][name],name) for key,name in keys.items()]
        for j,branch in enumerate(("Y-,g","Y-,e","Y+,g","Y+,e")):
            intervals.append((np.ravel(q["joint_B_C"])[j],peer[sig]["branches"][branch]["p"],branch))
        for value,iv,name in intervals:
            lo,hi = map(float,iv)
            if not lo <= value <= hi:
                raise AssertionError(f"peer {sig} {name}: {value} outside [{lo},{hi}]")
            count += 1
    return count


def range_control(data,pred):
    # Deterministic, no new starts. Stable references, one arm just above their span.
    tags,sign,b,det = unpack(data)
    for tag in range(4):
        for s in (0,1):
            idx = np.flatnonzero((tags==tag)&(sign==s))
            b[idx] = 0
            b[idx[:round(len(idx)*(.65 if tag%2 else .20))]] = 1
    idx = np.flatnonzero((tags==4)&(sign==0))
    b[idx] = 0
    b[idx[:round(.72*len(idx))]] = 1
    scored = score(pack(tags,sign,b,det),pred)
    assert scored["eligible"]  # both reference epochs pass
    case = scored["cases"][CASES[0]]
    assert case["status"]=="reject_setting_calibration_transfer"
    assert list(case["conflicts_by_arm"])==["A+"]
    assert case["latent_delta_CI"] is None and "delta" not in case
    error = case["conflicts_by_arm"]["A+"]
    assert error["observed_probability_interval"][0] > error["calibrated_dynamic_range"][1]
    assert scored["cases"][CASES[1]]["latent_delta_CI"] is not None
    return case


def analyze():
    pred = predict()
    gate = local_gate()
    off = local_gate(k=0.)
    for s in range(2):
        np.testing.assert_allclose(gate[s]["B_p_plus"],pred[CASES[0]]["plus_minus_p"][s],atol=2e-14)
        np.testing.assert_allclose([off[s]["C_p_excited"],off[s]["net_gate_work"]],[.18,0.],atol=2e-14)
    joint = [np.ravel(d["joint_B_C"]) for d in gate]
    data = generate(pred,joint)
    assert len(data)==262144
    nominal = score(data,pred)
    assert nominal["eligible"]
    for c in nominal["cases"].values():
        assert c["delta"]
    assert not nominal["cases"][CASES[0]]["reset_delta"]
    assert nominal["cases"][CASES[2]]["reset_delta"]
    negative = {}
    for name in ("reset","selection","hidden_offset","drift"):
        alt = generate(pred,joint,name)
        alt_score = score(alt,pred)
        case = alt_score["cases"][CASES[0]]
        counts = np.array(case["counts_minus_plus_loss_by_sign"])
        rate = counts[:,1]/counts[:,:2].sum(axis=1)
        negative[name] = dict(eligible=alt_score["eligible"],
                              local=case,success_only_contrast=rate[1]-rate[0],
                              starts_per_survivor=(counts.sum(axis=1)/counts[:,:2].sum(axis=1)).tolist())
    assert negative["reset"]["local"]["reset_delta"] and not negative["reset"]["local"]["delta"]
    assert negative["selection"]["local"]["reset_delta"] and negative["selection"]["success_only_contrast"]>.1
    assert not negative["drift"]["eligible"] and negative["hidden_offset"]["local"]["delta"]
    gate_obs = assess_gate(data,gate)
    assert all(run["standard_in_interval"] for run in gate_obs)
    weak = pred[CASES[2]]["delta"]
    tol = weak/2-2*.000045086952653
    m_ideal = math.ceil(math.log(2/.05)/tol**2)
    beta = np.sqrt(5)/2
    H = 2*(80/np.pi)**8/(10*beta**3*640**10)
    E = 2*(80/np.pi)**8/(9*beta**2*640**9)
    return data,dict(
        contract_sha256=sha((HERE/"CONTRACT.md").read_bytes()),
        local_contract_parameters="same-center: a=2/3,b=3/4,T=65/12,h=2/5,k=-.1,Omega=.5",
        baseline="940541cd464d8bccb9f7c553dbd3ebfefde596b7",
        planned_starts=262144,nominal_primary_design_power=design_power(pred[CASES[0]]["delta"]),raw_sha256=sha(data.tobytes()),
        predictions=pred,local_gate=gate,local_gate_k0=off,measured=nominal,
        peer_enclosures_checked=peer_check(gate),dynamic_range_negative_control=range_control(data,pred),gate_measurement=gate_obs,resources=resources(data,pred,gate),counterfactual_replays=negative,
        strict_timelike_ideal_m_per_sign=m_ideal,tail_640_H=H,
        joint_event_series_tail_upper=16*(2.8**2)*H,field_total_energy_series_tail_upper=4*.7**2*E)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--predict-only",action="store_true")
    modes.add_argument("--check",action="store_true",help="default: check raw records and receipt")
    modes.add_argument("--score-raw",action="store_true",help="score archived starts without a generator")
    modes.add_argument("--write",action="store_true",help="write the synthetic receipt and raw stream")
    args = parser.parse_args()
    if args.predict_only:
        print(json.dumps(dict(original=predict(),local=local_gate()),indent=2))
        return
    if args.score_raw:
        data = np.frombuffer((HERE/"starts.u16le").read_bytes(),dtype="<u2")
        pred,gate = predict(),local_gate()
        report = dict(original=score(data,pred),gate=assess_gate(data,gate),
                      ledger=resources(data,pred,gate))
        print(json.dumps(report,indent=2))
        return
    data,result = analyze()
    raw_path = HERE/"starts.u16le"
    receipt = HERE/"result.json"
    if args.write:
        raw_path.write_bytes(data.tobytes())
        receipt.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n")
    else:
        raw=raw_path.read_bytes()
        if sha(raw)!=result["raw_sha256"]:
            raise AssertionError("raw records disagree with fixed starts/seed")
        archived=json.loads(receipt.read_text())
        def compare(a,b,path):
            if isinstance(b,dict):
                assert set(a)==set(b),path
                for key in b:
                    compare(a[key],b[key],f"{path}.{key}")
            elif isinstance(b,list):
                assert len(a)==len(b),path
                for i,value in enumerate(b):
                    compare(a[i],value,f"{path}[{i}]")
            elif isinstance(b,float):
                np.testing.assert_allclose(a,b,atol=2e-12,rtol=1e-11,err_msg=path)
            else:
                assert a==b,path
        compare(result,archived,"receipt")
        assert score(np.frombuffer(raw,dtype="<u2"),result["predictions"]) == result["measured"]
    print("PASS: 262144 starts, four signed settings, independent joint gate and controls.")


if __name__=="__main__":
    main()
