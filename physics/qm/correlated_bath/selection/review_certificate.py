"""Root replay and independent full-record Choi, cell geometry, and curvature checks."""
import hashlib
import itertools
import json
import os
import subprocess
import sys
import tempfile
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import sympy as sy

from review_dynamics import blocks, deployment, distance, eye, fail_sq, kicks, pass_sq, rotations, spec
from review_dynamics import pin, pinned_blob, repo, spec_bytes

here = Path(__file__).resolve().parent
cert, inf = here.parent / "certificate", here.parent / "inference"
# The archived fit binds its calibration bytes and its pre-sampling freeze.
FIT_SHA256 = "2567d937b789568cc366a21ef8afc0be414fc36f6417c282380546407f6e5d4b"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def point(v):
    return np.array([float(F(x)) for x in v])


def cells(fit):
    planes = []
    def bracket(row, low, high):
        row = np.array(row, float)
        return [(row, high), (-row, -low)]

    planes += bracket((0, 0, 1), *point(fit["simultaneous_outer"]["w"]))
    planes += [(np.array(v), 0.) for v in ((-1, 2, 1), (-1, -2, 1), (1, 0, -2.2))]
    elo, ehi = point(fit["ramsey_mean_outer"]["eta"])
    for t, name in ((.75, "m_short"), (1.5, "m_long")):
        a, b = kicks((1,), (t,), 1)[0]
        true = np.array([2*(abs(a)**2+abs(b)**2), 8*(a.conjugate()*b).real, 0.])
        row = np.round(true, 10)
        pad = np.abs(true-row).sum()
        ml, mh = point(fit["ramsey_mean_outer"][name])
        planes += bracket(row, np.log(elo/mh)-pad, np.log(ehi/ml)+pad)

    def vertices(poly):
        rows = np.array([row for row, _ in poly])
        rhs = np.array([bound for _, bound in poly])
        pts = []
        for idx in itertools.combinations(range(len(rhs)), 3):
            mat = rows[list(idx)]
            if abs(np.linalg.det(mat)) < 1e-12:
                continue
            v = np.linalg.solve(mat, rhs[list(idx)])
            if (rows @ v <= rhs+1e-12).all() and not any(np.linalg.norm(v-p)<1e-12 for p in pts):
                pts.append(v)
        return np.array(pts)

    outer = vertices(planes)
    parts = [planes]
    for k in (0, 2):
        axis = np.eye(3)[k]
        mid = (outer[:, k].min()+outer[:, k].max())/2
        parts = [p + [constraint] for p in parts for constraint in ((axis, mid), (-axis, -mid))]
    return outer, [p for poly in parts if len(p := vertices(poly))]


def histories(times):
    for record in spec["records"]:
        op, displacements = [], []
        for h in itertools.product((1, -1), repeat=len(record)):
            a = eye
            for j, (label, sign) in enumerate(zip(record, h)):
                m = (np.diag(np.sqrt(fail_sq)) if label == "f" else
                     rotations[j] @ np.diag(np.sqrt(pass_sq)))
                v = eye[(1-sign)//2]
                a = m @ np.outer(v, v) @ a
            op.append(a.flatten()/np.sqrt(2))
            displacements.append(kicks(h, times[:len(h)], 1.))
        coefficients, matrices = [], []
        for i, left in enumerate(displacements):
            for j, right in enumerate(displacements):
                word = np.concatenate((-right, left[::-1]))
                phase = sum(np.vdot(v, u).imag for k, u in enumerate(word) for v in word[k+1:])
                diff = word.sum(axis=0)
                coefficients.append([-.5*np.vdot(diff,diff).real,
                                     -2*(diff[0].conjugate()*diff[1]).real, 1j*phase])
                matrices.append(np.outer(op[i],op[j].conj()).flatten())
        yield np.array(coefficients), np.array(matrices)


def interpolate(times, nom, cell_list):
    vertex_error = [np.zeros(len(cell)) for cell in cell_list]
    remainder = np.zeros(len(cell_list))
    center_resid = np.zeros(len(cell_list))
    for coeff, mat in histories(times):
        baseline = np.exp(nom @ coeff.T) @ mat
        for i, vs in enumerate(cell_list):
            z = vs @ coeff.T
            assert z.real.max() < 1e-12
            at_vertices = np.exp(z) @ mat
            vertex_error[i] += 2*np.linalg.norm(at_vertices-baseline, axis=1)
            var_bound = (np.ptp(z.real, axis=0)**2 + np.ptp(z.imag, axis=0)**2)/4
            remainder[i] += np.linalg.norm(mat, axis=1) @ var_bound
            interp = at_vertices.mean(axis=0)
            actual = np.exp(z.mean(axis=0)) @ mat
            center_resid[i] += 2*np.linalg.norm(actual-interp)
    assert np.all(center_resid <= remainder+1e-13) and center_resid.max() > 1e-6
    return max(v.max()+r for v,r in zip(vertex_error,remainder)), max(center_resid)


def check_choi(encoded, nom, times, budget):
    marginal = sy.zeros(2)
    js = {}
    for label, pairs in encoded.items():
        j = sy.Matrix([[sy.Rational(a)+sy.I*sy.Rational(b) for a,b in row] for row in pairs])
        assert j == j.H
        for size in range(1,5):
            for indices in itertools.combinations(range(4),size):
                assert j.extract(indices,indices).det() >= 0
        marginal += j[:2,:2]+j[2:,2:]
        js[label] = np.array(j, complex).reshape(2,2,2,2)
    assert marginal == sy.eye(2)/2
    psi = np.array([1., 1j, 0., -1j, 2., 1.])
    rho = np.outer(psi,psi.conj())/np.vdot(psi,psi)
    u,v,w = nom
    ref = blocks(rho, times, np.sqrt(w), (u/w-1)/2, v/w)
    predicted = {r:2*np.einsum("aibj,irjs->arbs",j,rho.reshape(2,3,2,3)).reshape(6,6)
                 for r,j in js.items()}
    err = distance(ref,predicted)
    half_trace = sum(b.trace().real for b in predicted.values())/2
    assert err < budget and abs(half_trace-.5)<1e-12
    return err, half_trace


def main():
    fit = read(inf/"calibration_fit.json")
    proto = read(inf/"protocol.json")
    frozen = read(inf/"freeze.json")
    assert digest(inf/"calibration_fit.json")==FIT_SHA256
    assert frozen["upstream_commit"]==pin
    assert digest(inf/"protocol.json")==frozen["files"]["protocol.json"]
    assert digest(inf/"freeze.json")==fit["freeze_hash"]
    assert digest(inf/"calibration.npz")==fit["calibration_hash"]
    print("reviewed files", {p.name:digest(p) for p in (
        cert/"complete.py", cert/"joint.py", cert/"first-output.json",cert/"joint-result.json")})
    original_joint = read(cert/"joint-result.json")
    inputs = [inf/"calibration_fit.json", inf/"freeze.json", inf/"protocol.json",
              inf/"calibration.npz", cert/"first-output.json"]
    hashes = {p.name:digest(p) for p in inputs}
    assert original_joint["dependencies"] == hashes
    blobs = {"SHARED_MODEL.json":hashlib.sha256(spec_bytes).hexdigest()}
    for name in ("dynamics.py", "interval_certificate.py"):
        blobs[name] = hashlib.sha256(pinned_blob(name)).hexdigest()
    assert blobs["dynamics.py"] == frozen["upstream_git_blob_sha256"]["dynamics"]
    print("pinned Git source", pin, "repo", repo, "blob SHA256", blobs)
    print("actual certificate input SHA256", hashes)
    with tempfile.TemporaryDirectory(dir=here) as runtime:
        tmp = Path(runtime)
        env = dict(os.environ, TMPDIR=str(tmp), PYTHONDONTWRITEBYTECODE="1")
        def run(filename, *args):
            p = subprocess.run([sys.executable,"-B",str(cert/filename),*map(str,args),
                                "--repo",repo], cwd=tmp, env=env, check=True,
                               capture_output=True, text=True)
            return p.stdout.strip()
        run("complete.py",cert/"first-input.json",tmp/"point.json")
        saved = read(cert/"first-output.json")
        assert digest(tmp/"point.json")==hashes["first-output.json"]
        # Keep basename identical because joint.py binds dependency names.
        (tmp/"point.json").rename(tmp/"first-output.json")
        print(run("joint.py",inf/"calibration_fit.json",inf/"protocol.json",
                  tmp/"first-output.json",tmp/"joint.json"))
        assert digest(tmp/"joint.json")==digest(cert/"joint-result.json")
        print("replay: both JSON results exactly equal (byte-for-byte)")
        nom = point([fit["nominal"][k] for k in ("u","v","w")])
        outer, cell_list = cells(fit)
        ref_outer = [point(row) for row in original_joint["physical_outer_vertices"]]
        assert len(outer)==len(ref_outer)==8 and len(cell_list)==4
        assert all(min(np.max(abs(v-r)) for r in ref_outer)<1e-12 for v in outer)
        b_fock = read(here.parent/"dynamics"/"observed.json")["rational_choi"]
        for i, times in enumerate((deployment,deployment[[1,0,2]])):
            row = original_joint["results"][i]
            interp, residual = interpolate(times,nom,cell_list)
            assert abs(interp-float(F(row["joint_parameter_upper"])))<2e-12
            matrix = saved["results"][i]["physical_repair"]["choi_blocks_exact_fraction_pairs"]
            err, wrong_trace = check_choi(matrix,nom,times,1e-8)
            b_row = b_fock[("deployment", "changed_intervals")[i]+"_K16"]
            b_nom = [.18, .0225, .09]
            b_err, _ = check_choi(b_row["choi_real_imag_pairs"],b_nom,times,
                                  float(b_row["point_budget_upper"]["total"]))
            event = 4*F(str(proto["bias_event"]))
            grid = F(4,2**proto["grid_bits"])
            pre = F(row["complete_upper"])+F(row["terminal_visibility_upper"])+event
            assert F(row["eight_cell_bias_upper"])==event and F(row["sampler_tv_allowance"])==grid
            assert grid==F(4,2**40) and F(row["terminal_upper"])==pre
            digitized = F(row["terminal_digitized_upper"])
            assert digitized == F(-(-(pre+grid)*10**12//1),10**12)
            assert digitized < F(row["target"])==F(1,20) and row["verdict"]=="CERTIFIED_SYNTHETIC"
            print(f"timing {i+1}, independent parameter={interp:.12g}, "
                  f"actual center interpolation residual={residual:.9g}, arbitrary SR error={err:.3g}, "
                  f"without normalized-Choi factor input gives trace={wrong_trace:.3g}")
            print(f"Bell analog TV={float(pre):.12f}, outward digitized TV={float(digitized):.12f}")
            print(f"B K=16 repaired Choi at B's own point, general SR discrepancy {b_err:.9g}")
        # Retain f labels. Modify only the ZZ-plus terminal effect on f by +|01><01|/2.
        e01 = np.diag([0.,1.,0.,0.])
        zz = np.diag([1.,-1.,-1.,1.])
        effect = (np.eye(4)+.96*zz+e01)/2
        assert np.linalg.eigvalsh(effect).min()>=0 and np.linalg.eigvalsh(effect).max()<=1
        bell = np.array([1.,0.,0.,1.])
        gaps = []
        for rho in (np.outer(bell,bell)/2,e01):
            fail = blocks(rho,deployment,.3,.5,.25)["f"]
            gaps.append(np.trace(e01 @ fail).real/2)
        assert abs(gaps[0])<1e-14 and abs(gaps[1]-1/16)<1e-14
        print("record-conditioned detector residual, Bell vs |01> TV:", *gaps)
        # Proof failure: both endpoint phase channels equal the identity, midpoint flips |+>.
        plus, minus = np.array([1.,1.])/np.sqrt(2), np.array([1.,-1.])/np.sqrt(2)
        gap = np.linalg.svd(np.outer(plus,plus)-np.outer(minus,minus),compute_uv=False).sum()/2
        assert abs(gap-1)<1e-14
        print("endpoints U(0)=U(2pi)=I, midpoint U(pi)=Z: trace distance on |+> =",round(gap,12))
        bias = F(str(proto["bias_event"]))
        scale = 2**proto["grid_bits"]
        ideal = [F(1,8)]*8
        biased = [p+(-1)**i*bias for i,p in enumerate(ideal)]
        cuts = [0] + [round(scale*s) for s in itertools.accumulate(biased)]
        tv = sum(abs(F(b-a,scale)-p) for a,b,p in zip(cuts,cuts[1:],ideal))/2
        assert 4*bias < tv <= 4*(bias+F(1,scale))
        print("digitized tight alternating-bias example: TV excess over 4b =",tv-4*bias)
        def require_binding_rejection(fit_path, protocol_path, label):
            output = tmp/(label + "-result.json")
            try:
                run("joint.py",fit_path,protocol_path,tmp/"first-output.json",output)
            except subprocess.CalledProcessError as e:
                reason = e.stderr.strip().splitlines()[-1]
                assert reason == "ValueError: calibration freeze binding mismatch", e.stderr
                assert not output.exists()
                print(f"{label}: rejected before output, exit {e.returncode}, {reason}")
            else:
                raise AssertionError(f"joint.py accepted {label}")

        alternate = tmp/"protocol.json"
        alternate.write_text(json.dumps(dict(proto, bias_event=0)))
        assert digest(alternate)!=hashes["protocol.json"]
        require_binding_rejection(inf/"calibration_fit.json",alternate,"substituted protocol")

        for name in ("freeze.json","calibration_fit.json"):
            (tmp/name).write_bytes((inf/name).read_bytes())
        (tmp/"calibration.npz").write_bytes((inf/"calibration.npz").read_bytes()+b"\x00")
        assert digest(tmp/"calibration.npz")!=fit["calibration_hash"]
        require_binding_rejection(tmp/"calibration_fit.json",inf/"protocol.json","substituted raw calibration")

        # Loosening a valid point-map error bound leaves the physical data and map intact.
        # At the analog threshold the small digitizer charge must change the verdict.
        first = original_joint["results"][0]
        repair = saved["results"][0]["physical_repair"]
        repair["certified_half_diamond_rational_upper"] = str(
            F(repair["certified_half_diamond_rational_upper"])+F(first["target"])-F(first["terminal_upper"]))
        stress = tmp/"looser-point-bound.json"
        stress.write_text(json.dumps(saved))
        run("joint.py",inf/"calibration_fit.json",inf/"protocol.json",stress,tmp/"stress.json")
        boundary = read(tmp/"stress.json")["results"][0]
        assert F(boundary["terminal_upper"])==F(boundary["target"])==F(1,20)
        assert F(boundary["terminal_digitized_upper"])>F(1,20) and boundary["verdict"]=="NOT_CERTIFIED"
        print("threshold control: analog",boundary["terminal_upper"],"digitized",
              boundary["terminal_digitized_upper"],"verdict",boundary["verdict"])


if __name__=="__main__":
    main()
