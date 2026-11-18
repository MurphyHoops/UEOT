"""Reproduce all eight declared Choi certificates, without sampling any data."""
from __future__ import annotations
import hashlib,json,time
from pathlib import Path
from interval_certificate import certificate

def main():
    destination=Path(__file__).resolve().parent
    started=time.perf_counter(); rows=[]
    for value,name in [('3/10','generator'),('0.299314119192','calibrated')]:
        for times,tag in [(('2/3','3/4','1/2'),'original'),(('3/4','2/3','1/2'),'permuted')]:
            for backend in ['weyl','galerkin']:
                result=certificate(value,80,times,backend,20)
                filename=f'interval_{name}_{tag}_{backend}.json'
                path=destination/filename
                path.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
                assert result['galerkin_cutoff_if_applicable']==(20 if backend=='galerkin' else None)
                rows.append({'file':filename,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                    'lambda':result['lambda_exact'],'backend':backend,
                    'galerkin_cutoff':result['galerkin_cutoff_if_applicable'],
                    'raw_half_diamond_upper':result['computed_half_diamond_error_upper_display'],
                    'physical_repair_bound':result['physical_repair']['certified_half_diamond_rational_upper']})
    (destination/'interval_certificate_index.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps({'wall_seconds':time.perf_counter()-started,'certificates':rows},indent=2))

if __name__=='__main__':main()
