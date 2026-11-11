#!/usr/bin/env python3
"""Prepare an optional local XeLaTeX format and two pinned CJK packages.

Use only on the Linux TeX Live 2025 runtime lacking ls-R/formats/CJK packages.
A normal full TeX installation does not need this helper. No global tree is
modified. Third-party TeX packages retain their original LPPL notices.
"""
from pathlib import Path
import argparse
import hashlib
import io
import json
import os
import subprocess
import tarfile
import urllib.request

BASE = 'https://ftp.math.utah.edu/pub/tex/historic/systems/texlive/2024/tlnet-final/archive/'
PACKAGES = {
    'xecjk.tar.xz': '3975a09d07169e9c2c3e66b85990a76de6879e635bf428ddfee17118233a2bd4',
    'ctex.tar.xz': '2d8e9bf9ffa0fe0588caf425f2cb8cef3d642b99d7ca54e8fd56feae7ab48f98',
}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'.cache/tex-runtime')
    args=parser.parse_args();runtime=args.output.resolve();tree=runtime/'texmf';tree.mkdir(parents=True,exist_ok=True)
    for filename,digest in PACKAGES.items():
        cached=runtime/filename
        data=cached.read_bytes() if cached.exists() else urllib.request.urlopen(BASE+filename,timeout=60).read()
        if hashlib.sha256(data).hexdigest()!=digest:raise RuntimeError('Package checksum mismatch: '+filename)
        cached.write_bytes(data)
        with tarfile.open(fileobj=io.BytesIO(data),mode='r:xz') as archive:archive.extractall(tree,filter='data')
    env=dict(os.environ)
    env['TEXMF']='{'+str(tree)+',/etc/texmf,/usr/share/texmf,/usr/share/texlive/texmf-dist}'
    env['SOURCE_DATE_EPOCH']='1794355200';env['FORCE_SOURCE_DATE']='1'
    command=['xetex','-ini','-etex','-interaction=nonstopmode','-halt-on-error','-jobname=xelatex','-output-directory='+str(runtime),'xelatex.ini']
    with (runtime/'format-build.log').open('wb') as log:result=subprocess.run(command,env=env,stdout=log,stderr=subprocess.STDOUT)
    if result.returncode:raise RuntimeError('Inspect '+str(runtime/'format-build.log'))
    receipt={'packages':{name:{'url':BASE+name,'sha256':digest} for name,digest in PACKAGES.items()},'format_command':command,'format_sha256':hashlib.sha256((runtime/'xelatex.fmt').read_bytes()).hexdigest(),'source_date_epoch':env['SOURCE_DATE_EPOCH'],'system_tree_modified':False}
    (runtime/'RUNTIME.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
