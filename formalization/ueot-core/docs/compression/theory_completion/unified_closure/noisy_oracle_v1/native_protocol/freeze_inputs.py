#!/usr/bin/env python3
"""Freeze exact source/protocol scope; this is not execution evidence."""
import argparse
import json
from protocol_adapter import freeze

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--base-ref", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    manifest = freeze(args.repo, args.base_ref, args.output)
    print(json.dumps({k: manifest[k] for k in ("state", "baseline_ref", "source_tree_sha256",
        "complete_modules", "new_public", "lexical_hinted")}, indent=2))
