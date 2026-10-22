#!/usr/bin/env python3
from pathlib import Path
import subprocess, base64, hashlib, json, time, datetime
ROOT=Path('/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020')
REPO=ROOT/'repository.git'
OUT=ROOT/'path-realization-evidence-20261022'/'ops-publication-01'
OUT.mkdir(exist_ok=False)
BASE='50a91fb9c81e0f5e698ce2cc02ec1a44c9583b04'
HEAD='91366e9cf38815788978aeaf010f3016942d31dd'
TREE='08e1f9869bdad2c8b1d2a95a602711ffaa1eb92b'
REF='refs/heads/ops/compression-tc-path-realization-evidence'
BUNDLE=OUT/'candidate.bundle'
BUNDLE_B64='IyB2MiBnaXQgYnVuZGxlCi01MGE5MWZiOWM4MWUwZjVlNjk4Y2UyY2MwMmVjMWE0NGM5NTgzYjA0IE1lcmdlIHB1bGwgcmVxdWVzdCAjMzY1IGZyb20gTXVycGh5SG9vcHMvY29tcHJlc3Npb24vdGhlb3J5LWNvbXBsZXRpb24tZmluaXRlLW1lbW9yeQo5MTM2NmU5Y2YzODgxNTc4ODk3OGFlYWYwMTBmMzAxNjk0MmQzMWRkIHJlZnMvaGVhZHMvb3BzL2NvbXByZXNzaW9uLXRjLXBhdGgtcmVhbGl6YXRpb24tZXZpZGVuY2UKClBBQ0sAAAACAAAAB5oPeJyVjVFqwzAQBf91iv0vLSvFdrShhEJPslo9YUFiGUUNIadvS0/Qr4GBYUYHiCN8kbhIypqDxeRzUJl14XD0vhRVjyQhuV07tkEzq/iSxKIHlxmLREMw4wDzOk0mczwknpx+jbV1+mwZD3q3X3y0HZvWN2vXM/mjhOUQhIVeWJjdj73WMfCfxrX9dqK/VX2Cdh3ra4de6lNHbRtd6h2Ee83YDNRROm6r+wYq/k518AKlJwuQiWcvbSIdtSLS4R5lKN5QEHicASAA3//ZBdkFsMkBFNIGHTLgnooNjaZ124GI4XifLpAuk90B/PBOD2SmBHicMzEAAoXS1PwS3eT8olSGi/VBGfUcPFsZZwvWTVlv7VMiv8jVBKGmMJchrMSAc++b+5oVrrpz64897E155nQBAEYqGo/+AflA2RpxUbnrPSnphPJ04l+dsvy+eJxbzbSaaUKJiI1+w+zLJ08aNcWtMLv/zqfli1PS0YkdiwHTiQ8E/AH+F3nmS341g3dHQhVVGXh0GUskUXicW8+2nm2DNLPIxaPPUg1fqt3W15ltV35y2tG8vT4dALDGDRfxAlB+3WY+JR4ep1GaSfGioVZvNMmteJwBIQDe/98k3ySwpwMUMdTJymKuseBevKkt8VUS54G3ak2zuwOkDibtEO/5D7T9U1OYenmmvBLkjd0Ds+Hj4+8XeJxNzrFKxEAQxnEugbMSDwQbm3mA28pSm6CCB6IiZ2M3tzuXDCQ7YXbDGcFSC9v04gsISsp7IN/A2rtgYfvx58f385y+vqSf78nkJptfmNvz7HJ2n81n11fdRyKTGmNhlLDkR4wsvvs63O9P0rfkOGBFJkijlmDJniOZFXsnK7DiHW9j9jmgd3AmstisVY3KQfy0G40Piq0M/+ShrIs2sMUSAi4pttNhpAeyTcRFSZs+5xBJyRmLqkwKp0cQCNUWUKu4xg4W+0i5Dm7/NL4b7f49rKgSbfvvnb31L1alXD6ur5yJbnAO5O4G837KjHuwsOOp2A=='
BUNDLE_SHA='04677b6307239a1c6aaf1b60e2f9fcb7c2a736a59b40b3e6dc901f07efefeed8'
BUNDLE.write_bytes(base64.b64decode(BUNDLE_B64))
assert hashlib.sha256(BUNDLE.read_bytes()).hexdigest()==BUNDLE_SHA

def run(args):
 p=subprocess.run(args,cwd=REPO,capture_output=True)
 assert p.returncode==0,(args,p.stdout.decode(errors='replace'),p.stderr.decode(errors='replace'))
 return p.stdout
run(['git','bundle','verify',str(BUNDLE)])
run(['git','fetch',str(BUNDLE),REF+':'+REF])
assert run(['git','rev-parse',REF]).decode().strip()==HEAD
assert run(['git','rev-parse',HEAD+'^{tree}']).decode().strip()==TREE
before_raw=run(['git','ls-remote','--heads','origin'])
before=dict((s.split()[1],s.split()[0]) for s in before_raw.decode().splitlines())
(OUT/'REMOTE_BEFORE.txt').write_bytes(before_raw)
assert before['refs/heads/main']==BASE and REF not in before
cmd=['git','push','--porcelain','--force-with-lease='+REF+':','origin',HEAD+':'+REF]
t=time.monotonic(); utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
p=subprocess.run(cmd,cwd=REPO,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(OUT/'PUSH.log').write_bytes(p.stdout)
r={'schema':'PATH_REALIZATION_OPS_MAC_PUSH_V1','state':'PUSH_RETURNED_PENDING_VERIFICATION','head':HEAD,'tree':TREE,'base':BASE,'command':cmd,'exit_code':p.returncode,'seconds':time.monotonic()-t,'utc':utc,'bundle_sha256':BUNDLE_SHA,'log_sha256':hashlib.sha256(p.stdout).hexdigest()}
(OUT/'PUSH_EXECUTION.json').write_text(json.dumps(r,indent=2)+'\n')
assert p.returncode==0,p.stdout.decode(errors='replace')
after_raw=run(['git','ls-remote','--heads','origin']); (OUT/'REMOTE_AFTER.txt').write_bytes(after_raw)
after=dict((s.split()[1],s.split()[0]) for s in after_raw.decode().splitlines())
assert after[REF]==HEAD and {k:v for k,v in after.items() if k!=REF}==before
r.update(state='PASS_EXACT_OPS_PUSH_OTHER_REFS_UNCHANGED',before_sha256=hashlib.sha256(before_raw).hexdigest(),after_sha256=hashlib.sha256(after_raw).hexdigest())
(OUT/'PUSH_ACCEPTED.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))

