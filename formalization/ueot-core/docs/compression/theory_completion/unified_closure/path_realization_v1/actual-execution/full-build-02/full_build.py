#!/usr/bin/env python3
"""Run the unchanged full-build gates through the documented scope adapter."""
import argparse
import json
from pathlib import Path
from protocol_adapter import adapted_driver, archive_protocol, require

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("repo", "output", "base-ref", "frozen-inputs", "lake", "lean"):
        parser.add_argument("--" + key, required=True)
    args = parser.parse_args()
    require(not Path(args.output).exists(), "NEW_EXECUTION_DIRECTORY_REQUIRED")
    driver, archive = adapted_driver("full_build", args.repo, args.frozen_inputs, args.base_ref)
    try:
        result = driver.run(args.repo, args.output, args.base_ref, args.lake, args.lean)
    finally:
        archive_protocol(args.output, archive)
    print(json.dumps(result, indent=2))
