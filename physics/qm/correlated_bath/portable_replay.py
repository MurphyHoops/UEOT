"""Replay the published A/C experiment offline (Python 3.10+, numpy, scipy, mpmath, sympy).

CI: check out the archive and the full upstream commit, install the scientific
dependencies in the runner interpreter, then execute this file with --repo
"$GITHUB_WORKSPACE" --receipt "$RUNNER_TEMP/portable-replay.json". Upload that
receipt as a workflow artifact. The receipt path must be new. Without --receipt
the same JSON is printed on stdout. The historical freeze is an input.
"""

import argparse
import ast
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from time import monotonic
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parent
PIN = "44b6cd200cd01eccf15d4dc817311388d317a1af"
PREFIX = PIN + ":physics/qm/persistent_bath/"
PINNED = {
    "freeze.json": "1ed04d9b4dc22cbff70017614ff653b65c58f26435b068c7a2c7fe44be9668be",
    "calibration.npz": "2e1fd32698d82455ca879bc062863f5acb86b2c1d9147fa529b9de7e8fb2c2b9",
    "holdout.npz": "a1c4a7aa613f5e3eb58b8ec664c100bf8c05236f76932aa5909d9ef2cb152190",
    "calibration_fit.json": "2567d937b789568cc366a21ef8afc0be414fc36f6417c282380546407f6e5d4b",
    "predictions.json": "b99b9542009b7604098560aa643dae088ce99277a56a14899617e6fed7874672",
    "holdout_results.json": "e1dd6ae86ed4e8902a67b6f2bffa1503ab0f8c2ea3d28fc2d40082704c467f73",
}
BLOBS = ("common_c.py", "interval_source.py", "dynamics.py", "interval_certificate.py", "SHARED_MODEL.json")


def require(condition, description):
    if not condition:
        raise ValueError(description)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def incoming(folder, name):
    path = ROOT / folder / name
    require(path.is_file() and path.resolve() == path, f"expected regular archive file: {folder}/{name}")
    return path


def copy_into(target, folder, names):
    dest = target / folder
    dest.mkdir(exist_ok=True)
    for name in names:
        shutil.copyfile(incoming(folder, name), dest / name)


def compare(got, expected, field, tolerance=None):
    """Report the first differing scientific field, including its list index."""
    if isinstance(expected, dict) and isinstance(got, dict):
        require(got.keys() == expected.keys(), f"{field}: differing keys {sorted(got.keys() ^ expected.keys())}")
        for key in expected:
            compare(got[key], expected[key], f"{field}.{key}", tolerance)
    elif isinstance(expected, list) and isinstance(got, list):
        require(len(got)==len(expected), f"{field}: expected {len(expected)} items, got {len(got)}")
        for i,(a,b) in enumerate(zip(got,expected)):
            compare(a,b,f"{field}[{i}]",tolerance)
    elif got != expected:
        if tolerance is None or abs(Fraction(got)-Fraction(expected)) > tolerance:
            raise ValueError(f"{field}: expected {expected!r}, observed {got!r}")


def connect_git(repo, tmp, env, frozen):
    real = shutil.which("git", path=env["PATH"])
    require(real is not None, "Git executable missing")
    def git(*args):
        proc = subprocess.run([real,"-C",str(repo),"--no-replace-objects",*args], env=env,
                              capture_output=True)
        require(proc.returncode == 0, f"upstream {' '.join(args)}: Git exited {proc.returncode}")
        return proc.stdout

    git("cat-file","-e",PIN+"^{commit}")
    hashes = {n:hashlib.sha256(git("cat-file","blob",PREFIX+n)).hexdigest() for n in BLOBS}
    for n,h in frozen["upstream_git_blob_sha256"].items():
        compare(hashes[n+".py"],h,"upstream."+n)

    # Read the literal from the hash-verified historical source. Never resolve it.
    tree = ast.parse(incoming("inference","shared.py").read_bytes())
    legacy = next(ast.literal_eval(node.value) for node in tree.body if isinstance(node,ast.Assign)
                  and any(isinstance(t,ast.Name) and t.id=="REPO" for t in node.targets))
    proxy = tmp/"bin"/"git"
    proxy.parent.mkdir()
    proxy.write_text("""#!/usr/bin/env python3
import os, sys
args = sys.argv[1:]
repo = os.environ["UEOT_UPSTREAM_REPO"]
if args[:1] != ["-C"] or len(args)<3 or args[1] not in (repo, os.environ["REPLAY_LEGACY_CWD"]):
    sys.exit("replay Git: undeclared working directory or missing -C")
cmd = args[2:]
allowed = """ + repr([["cat-file","-e",PIN+"^{commit}"]] + [["show", PREFIX+n] for n in BLOBS]) + """
if cmd not in allowed:
    sys.exit("replay Git: undeclared object read")
real = os.environ["REPLAY_GIT"]
os.execv(real, [real, "-C", repo, "--no-replace-objects", *cmd])
""")
    proxy.chmod(0o700)
    env.update(PATH=str(proxy.parent)+os.pathsep+env["PATH"], REPLAY_GIT=real,
               UEOT_UPSTREAM_REPO=str(repo), REPLAY_LEGACY_CWD=legacy)
    return hashes


def member_hashes(path):
    with ZipFile(path) as z:
        names = z.namelist()
        require(sorted(names) == ["block_setting.npy", "ordered_codes.npy"], "shot archive schema")
        return {name: hashlib.sha256(z.read(name)).hexdigest() for name in names}


def replay(repo, tmp, receipt):
    env = {"HOME": str(tmp), "TMPDIR": str(tmp), "PATH": os.defpath, "LC_ALL": "C",
           "XDG_CACHE_HOME": str(tmp), "XDG_CONFIG_HOME": str(tmp), "TZ": "UTC",
           "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull, "GIT_TERMINAL_PROMPT": "0",
           "GIT_NO_LAZY_FETCH": "1", "GIT_ALLOW_PROTOCOL": "", "PYTHONNOUSERSITE": "1",
           "PYTHONDONTWRITEBYTECODE": "1", "OPENBLAS_NUM_THREADS": "1",
           "OMP_NUM_THREADS": "1", "VECLIB_MAXIMUM_THREADS": "1", "MKL_NUM_THREADS": "1"}
    if sys.platform.startswith("linux"):
        env["LD_LIBRARY_PATH"] = str(Path(sys.base_prefix) / "lib")
    env.update(GIT_ASKPASS="/bin/false", GIT_CONFIG_COUNT="1", GIT_CONFIG_KEY_0="credential.helper",
               GIT_CONFIG_VALUE_0="")
    origin = ROOT / "inference"
    observed = {n:digest(incoming("inference",n)) for n in PINNED}
    compare(observed, PINNED, "archive_sha256")
    frozen = read(origin / "freeze.json")
    compare(frozen["upstream_commit"], PIN, "freeze.upstream_commit")
    for n,h in frozen["files"].items():
        compare(digest(incoming("inference",n)),h,"freeze.files."+n)
    receipt["archive_sha256"] = observed
    receipt["pinned_blob_sha256"] = connect_git(repo,tmp,env,frozen)
    work = tmp / "replay"
    work.mkdir()
    copy_into(work, "inference", [*frozen["files"], "freeze.json", "confidence_geometry.py",
                                 "verify.py", "review_selection.py"])
    copy_into(work, "dynamics", ["correlated_cq.py", "fock.py", "review_inference.py", "observed.json"])
    copy_into(work, "selection", ["check_selection.py", "SELECTION.md", "selection_run.txt",
                                  "review_dynamics.py", "review_certificate.py"])
    copy_into(work, "certificate", ["complete.py", "joint.py", "first-input.json", "first-output.json",
                                    "joint-result.json"])
    receipt["replayed_program_sha256"] = {p.relative_to(work).as_posix(): digest(p)
                                        for p in sorted(work.glob("*/*.py"))}
    inf = work / "inference"

    def run(script, *args):
        label = str(script.relative_to(tmp))
        started = monotonic()
        proc = subprocess.run([sys.executable,"-sB",script.name,*args],cwd=script.parent,env=env,
                              stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        receipt["steps"].append({"step":label,"exit_code":proc.returncode,"seconds":round(monotonic()-started,3)})
        if proc.returncode:
            lines = proc.stdout.strip().splitlines()
            diagnostic = "\n".join(lines[-8:]).replace(str(tmp),"<scratch>").replace(str(repo),"<repo>")
            diagnostic = re.sub(r'File "[^"]*/([^/"]+)"', r'File "\1"', diagnostic)
            raise ValueError(f"{label} exited {proc.returncode}\n{diagnostic}")
        return proc.stdout

    versions = subprocess.check_output(
        [sys.executable, "-IsB", "-c", "import importlib.metadata as m,json;"
         "print(json.dumps({k:m.version(k) for k in ('numpy','scipy','mpmath','sympy')}))"],
        cwd=tmp, env=env, text=True)
    receipt["libraries"] = json.loads(versions)
    # These independent replays generate fresh evidence. The signed fit and
    # holdout predictions remain the inputs for the registered endpoint below.
    for phase in ("calibration","holdout"):
        prod = tmp/phase
        prod.mkdir()
        copy_into(prod,"inference",[*frozen["files"],"freeze.json"])
        if phase=="holdout":
            copy_into(prod,"inference",["calibration.npz","predictions.json"])
        out = prod/"inference"
        run(out/"generate.py", phase)
        name = phase+".npz"
        record = read(out/(phase+"_receipt.json"))
        saved = read(origin/(phase+"_receipt.json"))
        compare(saved["raw_sha256"],observed[name],phase+".frozen_raw_sha256")
        compare(record["raw_sha256"],digest(out/name),phase+".generated_raw_sha256")
        arrays = member_hashes(out/name)
        compare(arrays,member_hashes(origin/name),phase+".ordered_arrays")
        for key in ("shots","seed","freeze_sha256","cdf_sha256","prediction_sha256"):
            compare(record[key],saved[key],phase+"."+key)
        cuts = phase+"_source_cdf.json"
        compare(digest(out/cuts),digest(origin/cuts),cuts)
        receipt[phase] = {"shots":record["shots"],"frozen_sha256":observed[name],"replay_sha256":digest(out/name),
                          "ordered_member_sha256":arrays,"prediction_sha256":record["prediction_sha256"]}

    # Refit on the *archived* raw shots; allow small optimizer variation only
    # in the nominal fit and its derived point probabilities. Bands stay exact.
    fresh = tmp/"refit"
    fresh.mkdir()
    copy_into(fresh,"inference",[*frozen["files"],"freeze.json","calibration.npz","calibration_receipt.json"])
    refit = fresh/"inference"
    run(refit/"estimate.py")
    tolerance = Fraction("5e-7")
    for name, numeric in (("calibration_fit.json",{"nominal","nominal_decimal_enclosures"}),
                          ("predictions.json",{"nominal_ideal_probability"})):
        actual, expected = read(refit/name), read(origin/name)
        compare(sorted(actual),sorted(expected),name+".keys")
        for key in expected:
            if name=="predictions.json" and key=="fit_hash":
                compare(actual[key],digest(refit/"calibration_fit.json"),"refit prediction binding")
            else:
                compare(actual[key],expected[key],name+"."+key,tolerance if key in numeric else None)
    receipt["replay_fit_sha256"] = digest(refit/"calibration_fit.json")
    receipt["replay_predictions_sha256"] = digest(refit/"predictions.json")

    frozen_inputs = ["calibration_fit.json","predictions.json"] + [
        phase+suffix for phase in ("calibration","holdout") for suffix in (".npz","_source_cdf.json","_receipt.json")]
    copy_into(work,"inference",frozen_inputs)
    receipt["scoring_input_sha256"] = {n:digest(inf/n) for n in ("calibration.npz","holdout.npz",
                                                                 "calibration_fit.json","predictions.json")}
    compare(receipt["scoring_input_sha256"],{n:observed[n] for n in receipt["scoring_input_sha256"]},
            "registered scoring inputs")
    for script, result in (("score.py","holdout_results.json"),("confidence_geometry.py","joint_domain.json"),
                           ("verify.py","verification.json"),("review_selection.py","selection_review_result.json")):
        run(inf/script)
        actual, expected = read(inf/result), read(origin/result)
        if script=="verify.py":
            require(actual["standard_nominal_64_cells_vs_interval_midpoint_max"] < 1e-12,
                    f"64-cell baseline error above 1e-12: {actual['standard_nominal_64_cells_vs_interval_midpoint_max']}")
            for k in ("audit_resources","standard_nominal_64_cells_vs_interval_midpoint_max"):
                del actual[k], expected[k]
        if script=="review_selection.py":
            for n,h in actual["reviewed"].items():
                compare(digest(work/"selection"/n), h, "reviewed source "+n)
            del actual["reviewed"],expected["reviewed"]  # public notes may have editorial updates
        compare(actual,expected,result)
    scored = read(inf/"holdout_results.json")
    audit = read(inf/"verification.json")
    run(work/"dynamics/review_inference.py")
    independent = read(work/"dynamics/review_observed.json")
    for k,v in {"status":"PASS","cuts_checked":93,"holdout_bands_checked":100}.items():
        compare(independent[k],v,"independent."+k)
    require(independent["Fock_K20_vs_96_Bell_cells_max_abs"] < 1e-7,
            f"Fock K20 96-cell discrepancy: {independent['Fock_K20_vs_96_Bell_cells_max_abs']}")
    checks = run(work/"selection/check_selection.py")
    require("Ran 5 tests" in checks and checks.rstrip().endswith("OK"), "expected five passing selection tests")
    run(work/"selection/review_dynamics.py")
    # A's reviewer itself recomputes and checks both certificate byte hashes,
    # physical bounds, and the substituted-protocol/raw negative controls.
    run(work/"selection/review_certificate.py")
    cert = work/"certificate"
    receipt["certificate_sha256"] = {n:digest(cert/n) for n in ("first-output.json","joint-result.json")}
    rows = read(cert/"joint-result.json")["results"]
    limits = [["0.033892297103","0.046090140885","0.046090140889"],
              ["0.035357047207","0.047554890989","0.047554890993"]]
    fields = ("complete_upper","terminal_upper","terminal_digitized_upper")
    compare([[Fraction(r[k]) for k in fields] for r in rows],
            [list(map(Fraction,row)) for row in limits], "registered complete/analog/digitized bounds")
    compare([r["verdict"] for r in rows],["CERTIFIED_SYNTHETIC"]*2,"registered verdicts")
    receipt.update(decisions=scored["families"],aligned_phase=scored["aligned_phase"],holdout_cells=scored["number_of_cells"],
                   failed_cells=scored["failed_cells"],CDF_cuts_verified=audit["rounded_CDF_thresholds_checked"],
                   ordered_shots_verified=audit["all_raw_draws_regenerated"],selection_tests=5,
                   exact_bounds=[{k:r[k] for k in fields} for r in rows],hardware=scored["device"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path, help="local Git repository containing the full pinned object")
    parser.add_argument("--receipt", type=Path, help="write observed JSON to a new file")
    args = parser.parse_args()
    report = {"runner_sha256":digest(Path(__file__)), "schema":"ueot-portable-replay/1", "status":"FAIL", "commit":PIN, "steps":[],
              "started_utc":datetime.now(timezone.utc).isoformat(), "system":platform.system(),
              "machine":platform.machine(), "python":platform.python_version()}
    try:
        if args.receipt and args.receipt.exists():
            parser.error("--receipt requires a new file")
        with tempfile.TemporaryDirectory(prefix="ueot-replay-") as directory:
            replay(args.repo.resolve(strict=True), Path(directory), report)
        report["status"] = "PASS"
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        message = str(error)
        report["error"] = message if "/" not in message or isinstance(error, ValueError) else type(error).__name__
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    output = json.dumps(report, indent=2, allow_nan=False) + "\n"
    if args.receipt:
        with args.receipt.open("x") as f:
            f.write(output)
    print(output, end="")
    return int(report["status"] != "PASS")


if __name__ == "__main__":
    sys.exit(main())
