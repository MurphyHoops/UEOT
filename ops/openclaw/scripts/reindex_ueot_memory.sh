#!/usr/bin/env bash
set -euo pipefail

agents=(
  ueot-architect
  ueot-techops
  ueot-formal-foundations
  ueot-physics-cosmos
  ueot-biology-evolution
  ueot-mind-consciousness
  ueot-socioeconomics-civilization
  ueot-meaning-philosophy
)

for agent in "${agents[@]}"; do
  echo "reindexing ${agent}"
  openclaw memory index --agent "${agent}"
done
