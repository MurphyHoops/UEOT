#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../../.." && pwd)"
src_dir="${repo_root}/ops/skills"
dst_dir="${HOME}/.openclaw/workspace/skills"

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
