#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../../.." && pwd)"
src_dir="${repo_root}/ops/skills"

workspace_root=""
for candidate in "${HOME}/.openclaw/workspace-main" "${HOME}/.openclaw/workspace"; do
  if [[ -d "${candidate}" ]]; then
    workspace_root="${candidate}"
    break
  fi
done

if [[ -z "${workspace_root}" ]]; then
  echo "could not locate an OpenClaw main workspace" >&2
  exit 1
fi

dst_dir="${workspace_root}/skills"

mkdir -p "${dst_dir}"

for skill_dir in "${src_dir}"/*; do
  [[ -d "${skill_dir}" ]] || continue
  name="$(basename "${skill_dir}")"
  dest="${dst_dir}/${name}"
  if [[ -e "${dest}" && ! -L "${dest}" ]]; then
    echo "skipping existing non-symlink skill target: ${dest}" >&2
    continue
  fi
  ln -sfn "${skill_dir}" "${dest}"
done
