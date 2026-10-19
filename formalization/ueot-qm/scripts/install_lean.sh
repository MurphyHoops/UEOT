#!/usr/bin/env bash
# Install the reviewed official release without depending on the release redirector.
set -euo pipefail

qm_script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
qm_toolchain="$(tr -d '\r\n' < "$qm_script_dir/../lean-toolchain")"
if [[ "$qm_toolchain" != "leanprover/lean4:v4.33.1" ]]; then
  echo "The reviewed Lean archive pin must be updated with lean-toolchain." >&2
  exit 1
fi
if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo "This CI installer supports Linux x86_64 only." >&2
  exit 1
fi

qm_release="lean-4.33.1-linux"
qm_digest="890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235"
qm_install_root="${1:-${RUNNER_TEMP:-/tmp}/ueot-qm-lean}"
mkdir -p "$qm_install_root"

# A supplied archive supports an offline reproduction of the identical verification.
qm_archive="${2:-$qm_install_root/$qm_release.tar.zst}"
if [[ $# -lt 2 ]]; then
  curl --proto '=https' --tlsv1.2 --fail --location \
    --retry 4 --retry-all-errors --retry-delay 3 \
    --connect-timeout 20 --max-time 300 \
    "https://github.com/leanprover/lean4/releases/download/v4.33.1/$qm_release.tar.zst" \
    --output "$qm_archive"
fi
printf '%s  %s\n' "$qm_digest" "$qm_archive" | sha256sum --check --strict
tar --no-same-owner --zstd -xf "$qm_archive" -C "$qm_install_root"
qm_bin="$qm_install_root/$qm_release/bin"
qm_lean_version="$("$qm_bin/lean" --version)"
if [[ "$qm_lean_version" != *"version 4.33.1,"* || \
      "$qm_lean_version" != *"819816b2e0a3bf405af45ae5c7af2491d8f5bee6"* ]]; then
  echo "The installed compiler does not match the reviewed Lean version and commit." >&2
  exit 1
fi
printf '%s\n' "$qm_lean_version"
"$qm_bin/lake" --version
if [[ -n "${GITHUB_PATH:-}" ]]; then
  printf '%s\n' "$qm_bin" >> "$GITHUB_PATH"
fi
printf 'PASS: verified official compiler at %s\n' "$qm_bin"
