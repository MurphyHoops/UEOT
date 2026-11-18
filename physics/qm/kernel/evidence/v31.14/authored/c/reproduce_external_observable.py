"""Reproduce one predeclared processed observable without inventing raw events."""
from __future__ import annotations
import argparse, csv, datetime, hashlib, io, json, zipfile
from pathlib import Path
import numpy as np
import h5py
from common_c import BASE, digest, dump_json, load_json

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--archive',type=Path,help='optional original Zenodo archive; otherwise use the included unchanged HDF5 member')
    parser.add_argument('--hdf5',type=Path,default=BASE/'external'/'zhu_2025_processed_O.h5')
    args=parser.parse_args()
    plan=load_json(BASE/"EXTERNAL_OBSERVABLE_PLAN.json")
    provenance=load_json(BASE/'external'/'PROVENANCE.json')
    if args.archive is not None:
        if digest(args.archive)!=plan["archive_sha256"]:
            raise RuntimeError("external archive identity mismatch")
        with zipfile.ZipFile(args.archive) as z:
            matches=[name for name in z.namelist() if Path(name).name==plan["file"]]
            if len(matches)!=1:raise RuntimeError("ambiguous or missing predeclared data file")
            raw=z.read(matches[0])
    else:
        raw=args.hdf5.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=provenance['hdf5_sha256']:
        raise RuntimeError('included HDF5 identity mismatch')
    with h5py.File(io.BytesIO(raw),"r") as f:
        x=f["thetas_exp"][()]; exp=f["Os_exp"][()]
        noisy_x=f["thetas_sim_noisy"][()]; noisy=f["Os_sim_noisy"][()]
        ideal_x=f["thetas_sim_ideal"][()]; ideal=f["Os_sim_ideal"][()]
        fields=list(f)
    if exp.shape!=(5,11) or not np.allclose(x,noisy_x,rtol=0,atol=1e-12):
        raise RuntimeError("unexpected processing layout; no silent reinterpretation")
    mean=exp.mean(axis=0); sd=exp.std(axis=0,ddof=1); sem=sd/np.sqrt(exp.shape[0])
    ideal_values=[]
    for theta in x:
        idx=np.flatnonzero(np.abs(ideal_x-theta)<1e-12)
        ideal_values.append(float(ideal[idx[0]]) if len(idx)==1 else None)
    rows=[]
    for j in range(len(x)):
        rows.append({"theta":float(x[j]),"theta_over_pi":float(x[j]/np.pi),"processed_mean":float(mean[j]),
                     "processed_sd":float(sd[j]),"processed_sem":float(sem[j]),"author_noisy_simulation":float(noisy[j]),
                     "author_ideal_simulation_matched_grid":ideal_values[j]})
    csvfile=BASE/"EXTERNAL_PROCESSED_OBSERVABLE.csv"
    with csvfile.open("w",newline="") as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    result={"schema":"external-processed-observable-result/1","created_at":datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "plan_sha256":digest(BASE/"EXTERNAL_OBSERVABLE_PLAN.json"),"source":plan["source"],
            "archive_bytes":provenance['archive_bytes'],"archive_sha256":provenance['archive_sha256'],
            "archive_md5":provenance['archive_md5'],"hdf5_member":provenance['archive_member'],
            "input_mode":"original_archive" if args.archive is not None else "included_unchanged_original_HDF5",
            "archive_identity_status":"verified from original retained archive in initial run; member identity reverified in every run",
            "data_license_status":provenance['license_status'],
            "hdf5_sha256":hashlib.sha256(raw).hexdigest(),"read_dataset_fields":fields,
            "predeclared_rows_used":5,"settings":11,"rows":rows,
            "rmse_to_author_noisy_simulation":float(np.sqrt(np.mean((mean-noisy)**2))),
            "max_abs_difference_to_author_noisy_simulation":float(np.max(abs(mean-noisy))),
            "rmse_to_author_ideal_simulation":float(np.sqrt(np.mean((mean-np.array(ideal_values))**2))) if all(v is not None for v in ideal_values) else None,
            "csv_sha256":digest(csvfile),"data_qualification":"EXTERNAL_PROCESSED_DEVICE_OBSERVABLE_REPRODUCED",
            "raw_shots_available":False,"excluded_failures_recoverable":False,
            "uncertainty_interpretation":"SD and SEM summarize five processed rows; no raw-shot confidence coverage or independence claim is inferred",
            "relevance_to_frozen_oscillator_contract":"different physical source and protocol; does not calibrate lambda/eta, vacuum, interventions, leakage, full CQ, or the reference channel",
            "UEOT_device_test_status":"NOT_CERTIFIED_NO_MATCHED_RAW_DATA"}
    dump_json(BASE/"EXTERNAL_OBSERVABLE_RESULT.json",result)
    print({"shape":list(exp.shape),"rmse_noisy":result["rmse_to_author_noisy_simulation"],"rmse_ideal":result["rmse_to_author_ideal_simulation"],"status":result["data_qualification"]})

if __name__ == "__main__":main()
