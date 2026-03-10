#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../../.." && pwd)"

required_paths=(
  "${repo_root}/constitution/UEOT_CONSTITUTION.md"
  "${repo_root}/constitution/UEOT_METHOD.md"
  "${repo_root}/source/extracted/CHAPTER_SUMMARIES.md"
  "${repo_root}/memory/shared/UEOT_SHARED_MEMORY.md"
  "${repo_root}/ops/openclaw/scripts/provision_ueot_openclaw.sh"
  "${repo_root}/ops/skills/ueot-domain-research/SKILL.md"
  "${repo_root}/book/chapters/12-falsifiability-objections-and-research-roadmap.md"
)

for path in "${required_paths[@]}"; do
  [[ -e "${path}" ]] || {
    echo "missing required path: ${path}" >&2
    exit 1
  }
done

agent_output="$(openclaw agents list)"
for agent in \
  ueot-architect \
  ueot-techops \
  ueot-formal-foundations \
  ueot-physics-cosmos \
  ueot-biology-evolution \
  ueot-mind-consciousness \
  ueot-socioeconomics-civilization \
  ueot-meaning-philosophy; do
  grep -F -- "${agent}" <<<"${agent_output}" >/dev/null || {
    echo "missing OpenClaw agent: ${agent}" >&2
    exit 1
  }
done

cron_json="$(openclaw cron list --json)"
for job in \
  ueot-techops-daily \
  ueot-formal-foundations-daily \
  ueot-physics-cosmos-daily \
  ueot-biology-evolution-daily \
  ueot-mind-consciousness-daily \
  ueot-socioeconomics-civilization-daily \
  ueot-meaning-philosophy-daily \
  ueot-architect-daily \
  ueot-omega-council-wed \
  ueot-omega-council-sun \
  ueot-book-weekly; do
  if ! grep -F -- "\"name\": \"${job}\"" <<<"${cron_json}" >/dev/null; then
    echo "missing cron job: ${job}" >&2
    exit 1
  fi
done

openclaw memory status --json >/dev/null

echo "UEOT Omega validation passed"
