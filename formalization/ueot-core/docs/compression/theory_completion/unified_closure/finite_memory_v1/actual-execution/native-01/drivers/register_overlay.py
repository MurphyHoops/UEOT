#!/usr/bin/env python3
"""Register metadata around exact native bytes; no consumer update or Lean run."""
import argparse
import json
from pathlib import Path
from protocol_adapter import adapted_driver, verify_archived_protocol

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("repo", "native-output", "archive-relative", "build-receipt", "base-ref", "frozen-inputs"):
        parser.add_argument("--" + key, required=True)
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    verify_archived_protocol("integration_native", args.repo, args.frozen_inputs,
                             args.base_ref, args.native_output)
    verify_archived_protocol("full_build", args.repo, args.frozen_inputs,
                             args.base_ref, Path(args.build_receipt).parent)
    driver, _ = adapted_driver("register_overlay", args.repo, args.frozen_inputs, args.base_ref)
    result = driver.run(args.repo, args.native_output, args.archive_relative,
                        args.build_receipt, check_only=args.check_only)
    print(json.dumps(result, indent=2))
