#!/usr/bin/env python3
"""Run full native ownership/export/type/replay gates for the seven new modules."""
import argparse
import json
from pathlib import Path
from protocol_adapter import adapted_driver, archive_protocol, require

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("prepare", "run"))
    for key in ("repo", "output", "base-ref", "frozen-inputs"):
        parser.add_argument("--" + key, required=True)
    parser.add_argument("--build-receipt")
    args = parser.parse_args()
    require(not Path(args.output).exists(), "NEW_EXECUTION_DIRECTORY_REQUIRED")
    driver, archive = adapted_driver("integration_native", args.repo, args.frozen_inputs, args.base_ref)
    try:
        if args.mode == "run":
            require(args.build_receipt is not None, "EXPLICIT_FULL_BUILD_RECEIPT_REQUIRED")
            result = driver.run(args.repo, args.output, args.base_ref, args.build_receipt)
        else:
            pre = driver.prepare(args.repo, args.output, args.base_ref)
            result = {"status": pre["status"], "modules": len(pre["added_modules"]),
                      "public_source_candidates": len(pre["public_source_candidates"])}
    finally:
        archive_protocol(args.output, archive)
    print(json.dumps(result, indent=2))
