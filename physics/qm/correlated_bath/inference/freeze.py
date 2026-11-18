"""Create before first sample. Replays use the archived freeze and refuse altered inputs."""
from datetime import datetime,timezone
from hashlib import sha256
from shared import ROOT,COMMIT,NAMES,blob,sha,write
from interval_model import altrule

def main():
    if any((ROOT/name).exists() for name in ("freeze.json","calibration.npz","holdout.npz")):
        raise SystemExit("Existing freeze or samples. Replay with the bound inputs.")
    files=("protocol.json","truth.json","shared.py","source_snapshot.py","generate.py",
           "interval_model.py","estimate.py","score.py","freeze.py")
    write("freeze.json",{"utc_before_sampling":datetime.now(timezone.utc).isoformat(),
        "files":{name:sha(name) for name in files},"upstream_commit":COMMIT,
        "upstream_git_blob_sha256":{name:sha256(blob(name)).hexdigest() for name in NAMES},
        "calibration_discrimination_design":altrule("2/3",320000),
        "heldout_discrimination_design":altrule("1",120000)})
    print("frozen",sha("freeze.json"))
if __name__=="__main__":
    main()
