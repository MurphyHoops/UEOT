#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <agent-id> <workspace-dir>" >&2
  exit 1
fi

agent_id="$1"
workspace_dir="$2"
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../../.." && pwd)"
common_dir="${repo_root}/ops/openclaw/templates/common"
agent_dir="${repo_root}/ops/openclaw/templates/agents/${agent_id}"

if [[ ! -d "${agent_dir}" ]]; then
  echo "missing agent template directory: ${agent_dir}" >&2
  exit 1
fi

mkdir -p "${workspace_dir}/memory"

cp -f "${common_dir}/USER.md" "${workspace_dir}/USER.md"
cp -f "${common_dir}/HEARTBEAT.md" "${workspace_dir}/HEARTBEAT.md"
cp -f "${common_dir}/MEMORY.md" "${workspace_dir}/MEMORY.md"
cp -f "${agent_dir}/SOUL.md" "${workspace_dir}/SOUL.md"
cp -f "${agent_dir}/IDENTITY.md" "${workspace_dir}/IDENTITY.md"

today_file="${workspace_dir}/memory/$(date +%F).md"
if [[ ! -f "${today_file}" ]]; then
  cat >"${today_file}" <<EOF
# $(date +%F)

- workspace seeded for ${agent_id}
EOF
fi

gitdir="$(git -C "${workspace_dir}" rev-parse --git-dir)"
exclude_file="${gitdir}/info/exclude"
mkdir -p "$(dirname "${exclude_file}")"
touch "${exclude_file}"
for path in USER.md HEARTBEAT.md MEMORY.md SOUL.md IDENTITY.md memory/; do
  if ! rg -qxF "${path}" "${exclude_file}" >/dev/null 2>&1; then
    printf '%s\n' "${path}" >>"${exclude_file}"
  fi
done
