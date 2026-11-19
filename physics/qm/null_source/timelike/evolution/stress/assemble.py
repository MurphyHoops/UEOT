"""Assemble the same-reference finite modes, AE additions and certified UV tail."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import sys
from mpmath import iv
import tail

HERE=Path(__file__).resolve().parent
EVO=HERE.parent
I,box=tail.I,tail.box

def source_identity():
    paths={"stress/assemble.py":HERE/"assemble.py",
           "stress/tail.py":HERE/"tail.py"}
    return {name:hashlib.sha256(path.read_bytes()).hexdigest() for name,path in paths.items()}

LOADED_SOURCE_SHA256=source_identity()

def check_source_receipt(receipt,base,expected):
    hashes=receipt["source_sha256"]
    assert set(hashes)==set(expected),"incomplete or unexpected source identity"
    paths=[]
    for name,digest in hashes.items():
        path=base/name
        assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,("source hash mismatch",name)
        paths.append(path)
    return paths

def ib(x):return box(Q(x[0]),Q(x[1]))
def boundary(x):return tail.pair(x)
def cut_stress(eta,modes):
    t=Q(eta);c=iv.cos(2*I(t));h=-iv.tan(2*I(t));q=1/(c*c)
    a=iv.sqrt(3*c)
    E1=(h*h-1)/2
    E3=3*q*(1-3*h*h)/8
    P1=q/3+h*h/2+I(1)/6
    P3=-q*(7+27*h*h)/8
    # k=1 exact Gaussian kinetic mode, including exactly one UV subtraction.
    e0=I(1)/(2*c)
    er=e0-1-E1-E3
    pr=e0-I(1)/3-P1-P3
    ks=[]
    for row in modes:
        k=row["k"];ks.append(k)
        er+=k*k*(ib(row["e"])-k-E1/k-E3/k**3)
        pr+=k*k*(ib(row["s"])-I(k)/3-P1/k-P3/k**3)
    assert ks==list(range(2,max(ks)+1)), "incomplete or duplicated finite modes"
    pref=1/(4*iv.pi**2*a**4)
    ra,pa=tail.analytic(t)
    return {"eta":eta,"K":max(ks),"rho_cutoff":boundary(pref*er+ra),
            "pressure_cutoff":boundary(pref*pr+pa),"rho_analytic":boundary(ra),
            "pressure_analytic":boundary(pa),"zero_raw_e":boundary(e0)}

def lower_splice(finite,anchor):
    """Eta0: instantaneous energy positivity for K<k<=J, W2 only beyond J."""
    assert finite["eta"]==anchor["eta"]=="0"
    K=finite["K"]
    D5=tail.read_pair(anchor["integration_D5"])
    Hv=tail.read_pair(anchor["integration_Hvariation"])
    N11=tail.read_pair(anchor["integration_N11"])
    records=[]
    for J in (512,1024,2048,3072,4096,8192,16384):
        if J<max(K,anchor["K"]):continue
        far=tail.local_tail(Q(0),J,D5,Hv,N11,anchor["ibp_phase_positive"])
        # All exact modes satisfy e_k>=sqrt(k^2-1) from their Wronskian.
        # k^2(omega-d_k)=r_static(k)-1/(2k).
        middle=(iv.log(I(J)/K)/2
                +I(1)/(32*K*K*(1-I(1)/(K+1)**2)))
        pref=1/(36*iv.pi**2)
        middle_lower=-tail.topI(pref*middle)
        far_lower=tail.read_pair(far["rho_UV_tail_lower_bound"])
        full=tail.botI(ib(finite["rho_cutoff"]))+middle_lower+far_lower
        records.append({"J":J,"middle_energy_lower_bound":boundary(middle_lower),
             "far_UV_lower_bound":boundary(far_lower),
             "rho_full_lower_bound":boundary(tail.botI(full)),
             "anchor_K":anchor["K"]})
    best=max(records,key=lambda r:Q(r["rho_full_lower_bound"][0]))
    assert Q(best["rho_full_lower_bound"][0])>Q(1,2)
    return {"method":"finite_modes_plus_instantaneous_ground_bound_plus_W2_UV",
        "finite_K":K,"candidates":records,"selected":best,
        "rho_classical_on_given_initial_geometry":"1/2",
        "Hamiltonian_required_total_density":"1/2",
        "quantum_alone_exceeds_required_total":True,
        "scope":"fixed_archived_geometry_reference_and_mu1_no_extra_finite_curvature_terms"}

def assemble():
    if not __debug__:raise RuntimeError("Assertions required; do not use -O.")
    assert source_identity()==LOADED_SOURCE_SHA256,"assembler source changed after import"
    prop_path=EVO/"propagation/result.json"
    tail64_path=HERE/"tail_K64_M1024.json"
    anchor_path=HERE/"tail_K256_M1024.json"
    receipt_digests={}
    def load_receipt(path):
        raw=path.read_bytes()
        receipt_digests[path]=hashlib.sha256(raw).hexdigest()
        return json.loads(raw)
    prop=load_receipt(prop_path)
    uv64=load_receipt(tail64_path)
    anchor=load_receipt(anchor_path)
    assert prop["last_nonzero_mode"]==uv64["K"]==64
    background=EVO/"propagation/background.py"
    bg_hash=hashlib.sha256(background.read_bytes()).hexdigest()
    assert uv64["background_sha256"]==anchor["background_sha256"]==bg_hash
    assert prop["source_sha256"]["background.py"]==bg_hash
    inputs=[prop_path,tail64_path,anchor_path,background,HERE/"tail.py",HERE/"assemble.py"]
    inputs+=check_source_receipt(prop,EVO/"propagation",["background.py","finite_modes.py"])
    for receipt in [uv64,anchor]:
        assert receipt["interval_encoding"]=="exact_binary_endpoints_as_rational_strings"
        inputs+=check_source_receipt(receipt,HERE,["tail.py","../propagation/background.py"])
    rows=[]
    for u in uv64["targets"]:
        eta=u["eta"];finite=cut_stress(eta,prop["targets"][eta]["modes"])
        rho=ib(finite["rho_cutoff"])+box(
            Q(u["rho_UV_tail_lower_bound"][0]),
            Q(u["rho_UV_tail_absolute_bound"][1]))
        pbound=Q(u["pressure_UV_tail_absolute_bound"][1])
        pressure=ib(finite["pressure_cutoff"])+box(-pbound,pbound)
        rows.append({"finite":finite,"rho_full_interval":boundary(rho),
                     "pressure_full_interval":boundary(pressure),
                     "enclosure_usefulness":"finite_but_not_precise"})
    zero=rows[0]["finite"]
    azero=next(x for x in anchor["targets"] if x["eta"]=="0")
    splices=[lower_splice(zero,azero)]
    extra_path=EVO/"propagation/extra_eta0_256.json"
    if extra_path.exists():
        extra=load_receipt(extra_path)
        # The extra receipt must use the same background; its nominal source may
        # additionally bind the original interval propagator.
        assert extra["source_sha256"]["background.py"]==bg_hash
        assert extra["first_nonzero_mode"]==65 and extra["last_nonzero_mode"]==256
        inputs+=check_source_receipt(extra,EVO/"propagation",
                                     ["background.py","finite_modes.py","extra_eta0.py"])
        modes=prop["targets"]["0"]["modes"]+extra["targets"]["0"]["modes"]
        ext=cut_stress("0",modes)
        assert ext["K"]==256
        ext_uv=azero
        ext["rho_full_interval_direct_UV"]=boundary(ib(ext["rho_cutoff"])+box(
            Q(ext_uv["rho_UV_tail_lower_bound"][0]),
            Q(ext_uv["rho_UV_tail_absolute_bound"][1])))
        ext["pressure_full_interval_direct_UV"]=boundary(ib(ext["pressure_cutoff"])+box(
            -Q(ext_uv["pressure_UV_tail_absolute_bound"][1]),
            Q(ext_uv["pressure_UV_tail_absolute_bound"][1])))
        splices.append(lower_splice(ext,azero))
        inputs.append(extra_path)
    else:ext=None
    for path,digest in receipt_digests.items():
        assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,("input receipt changed",str(path))
    inputs=sorted(set(p.resolve() for p in inputs))
    assert source_identity()==LOADED_SOURCE_SHA256,"assembler source changed during computation"
    # Recheck every source receipt after using the inputs, so a concurrent edit
    # cannot silently bind old numerical data to a new implementation.
    check_source_receipt(prop,EVO/"propagation",["background.py","finite_modes.py"])
    for receipt in [uv64,anchor]:
        check_source_receipt(receipt,HERE,["tail.py","../propagation/background.py"])
    if extra_path.exists():
        check_source_receipt(extra,EVO/"propagation",["background.py","finite_modes.py","extra_eta0.py"])
    return {"status":"DYNAMIC_ABSOLUTE_POINT_ENCLOSURES_AND_INITIAL_CONSTRAINT_REJECTION",
        "source_sha256":dict(LOADED_SOURCE_SHA256),
        "base":"987dd4ccc58d0086cc1305e99b5cdb67f8127fde",
        "scheme":"Anderson_Eaker_mu1_no_additional_finite_curvature_terms",
        "points":rows,"extra_eta0_finite":ext,"initial_energy_certificates":splices,
        "input_sha256":{str(p.relative_to(EVO)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
        "claims_not_made":["new_self_consistent_geometry","renormalization_independent_no_go",
                          "precise_dynamic_pressure","window_average_baseline",
                          "real_device_validation"]}

if __name__=="__main__":
    if not __debug__:raise SystemExit("Assertions required; do not use -O.")
    p=argparse.ArgumentParser();p.add_argument("--write",action="store_true")
    p.add_argument("--check",action="store_true");args=p.parse_args()
    result=assemble();rendered=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.write:(HERE/"result.json").write_text(rendered)
    if args.check:assert rendered==(HERE/"result.json").read_text(),"receipt mismatch"
    for c in result["initial_energy_certificates"]:
        s=c["selected"]
        print("certified initial rho lower",float(Q(s["rho_full_lower_bound"][0])),
              "finite K",c["finite_K"],"splice J",s["J"])
    print("PASS: fixed-scheme dynamic enclosures and initial Hamiltonian constraint verdict.")
