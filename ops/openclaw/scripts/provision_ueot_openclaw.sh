#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../../.." && pwd)"
agent_home="${UEOT_AGENT_HOME:-/home/ubuntu/ueot-agents}"
config_file="${OPENCLAW_CONFIG_PATH:-${HOME}/.openclaw/openclaw.json}"
telegram_target="${UEOT_TELEGRAM_TARGET:-}"
main_workspace=""
for candidate in "${HOME}/.openclaw/workspace-main" "${HOME}/.openclaw/workspace"; do
  if [[ -d "${candidate}" ]]; then
    main_workspace="${candidate}"
    break
  fi
done

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

declare -A models=(
  [ueot-architect]="newcli-claude-aws/claude-opus-4-6"
  [ueot-techops]="cliproxyapi/gpt-5.1-codex-max"
  [ueot-formal-foundations]="cliproxyapi/gpt-5.2"
  [ueot-physics-cosmos]="cliproxyapi/gpt-5.2"
  [ueot-biology-evolution]="cliproxyapi/gpt-5.2"
  [ueot-mind-consciousness]="cliproxyapi/gpt-5.2"
  [ueot-socioeconomics-civilization]="cliproxyapi/gpt-5.2"
  [ueot-meaning-philosophy]="cliproxyapi/gpt-5.2"
)

declare -A names=(
  [ueot-architect]="UEOT Architect"
  [ueot-techops]="UEOT TechOps"
  [ueot-formal-foundations]="UEOT Formal Foundations"
  [ueot-physics-cosmos]="UEOT Physics and Cosmos"
  [ueot-biology-evolution]="UEOT Biology and Evolution"
  [ueot-mind-consciousness]="UEOT Mind and Consciousness"
  [ueot-socioeconomics-civilization]="UEOT Socioeconomics and Civilization"
  [ueot-meaning-philosophy]="UEOT Meaning and Philosophy"
)

declare -A emojis=(
  [ueot-architect]="🏛️"
  [ueot-techops]="🛠️"
  [ueot-formal-foundations]="📐"
  [ueot-physics-cosmos]="🌌"
  [ueot-biology-evolution]="🧬"
  [ueot-mind-consciousness]="🧠"
  [ueot-socioeconomics-civilization]="🏙️"
  [ueot-meaning-philosophy]="🧭"
)

declare -A themes=(
  [ueot-architect]="amber"
  [ueot-techops]="slate"
  [ueot-formal-foundations]="blue"
  [ueot-physics-cosmos]="indigo"
  [ueot-biology-evolution]="green"
  [ueot-mind-consciousness]="violet"
  [ueot-socioeconomics-civilization]="teal"
  [ueot-meaning-philosophy]="rose"
)

mkdir -p "${agent_home}"
chmod 700 "${HOME}/.openclaw/credentials" 2>/dev/null || true

ensure_worktree() {
  local agent_id="$1"
  local worktree="${agent_home}/${agent_id}"
  local branch="agent/${agent_id}"

  if [[ -e "${worktree}/.git" || -f "${worktree}/.git" ]]; then
    return 0
  fi

  if git -C "${repo_root}" show-ref --verify --quiet "refs/heads/${branch}"; then
    git -C "${repo_root}" worktree add "${worktree}" "${branch}"
  else
    git -C "${repo_root}" worktree add -b "${branch}" "${worktree}" HEAD
  fi
}

ensure_openclaw_agent() {
  local agent_id="$1"
  local worktree="${agent_home}/${agent_id}"
  if ! openclaw agents list | grep -F -- "${agent_id}" >/dev/null; then
    openclaw agents add "${agent_id}" \
      --workspace "${worktree}" \
      --non-interactive \
      --model "${models[${agent_id}]}"
  fi
  openclaw agents set-identity \
    --agent "${agent_id}" \
    --name "${names[${agent_id}]}" \
    --emoji "${emojis[${agent_id}]}" \
    --theme "${themes[${agent_id}]}" >/dev/null
}

for agent in "${agents[@]}"; do
  ensure_worktree "${agent}"
  "${script_dir}/install_workspace_files.sh" "${agent}" "${agent_home}/${agent}"
  ensure_openclaw_agent "${agent}"
done

"${script_dir}/install_local_skills.sh"
python3 "${script_dir}/build_shared_memory_registry.py" >/dev/null

link_main_workspace() {
  [[ -n "${main_workspace}" ]] || return 0
  local item
  for item in AGENTS.md README.md LICENSE constitution source domains council book ops skills memory UEOT_v3_top.pdf "UEOT_v3_top[1].zip"; do
    local src="${repo_root}/${item}"
    local dest="${main_workspace}/${item}"
    [[ -e "${src}" || -L "${src}" ]] || continue
    if [[ -e "${dest}" && ! -L "${dest}" ]]; then
      continue
    fi
    ln -sfn "${src}" "${dest}"
  done
}

link_main_workspace

python3 - "${config_file}" "${agent_home}" <<'PY'
import json
import os
import sys

config_path = sys.argv[1]
agent_home = sys.argv[2]

with open(config_path, "r", encoding="utf-8") as fh:
    cfg = json.load(fh)

agents = cfg.setdefault("agents", {})
defaults = agents.setdefault("defaults", {})
defaults["userTimezone"] = "Asia/Shanghai"

memory = defaults.setdefault("memorySearch", {})
memory["enabled"] = True
memory["sources"] = ["memory"]
memory["extraPaths"] = [
    "constitution",
    "source/extracted",
    "memory/shared",
    "domains/formal-foundations",
    "domains/physics-cosmos",
    "domains/biology-evolution",
    "domains/mind-consciousness",
    "domains/socioeconomics-civilization",
    "domains/meaning-philosophy",
    "council/resolutions",
]
memory["sync"] = {
    "onSessionStart": True,
    "onSearch": True,
    "watch": True,
    "watchDebounceMs": 2000,
    "intervalMinutes": 15,
}
memory["query"] = {"maxResults": 8, "minScore": 0.0}

agent_models = {
    "ueot-architect": "newcli-claude-aws/claude-opus-4-6",
    "ueot-techops": "cliproxyapi/gpt-5.1-codex-max",
    "ueot-formal-foundations": "cliproxyapi/gpt-5.2",
    "ueot-physics-cosmos": "cliproxyapi/gpt-5.2",
    "ueot-biology-evolution": "cliproxyapi/gpt-5.2",
    "ueot-mind-consciousness": "cliproxyapi/gpt-5.2",
    "ueot-socioeconomics-civilization": "cliproxyapi/gpt-5.2",
    "ueot-meaning-philosophy": "cliproxyapi/gpt-5.2",
}

deny_for_domains = ["gateway", "cron", "telegram", "whatsapp", "discord", "slack", "signal", "imessage"]

agent_list = agents.setdefault("list", [])
by_id = {entry.get("id"): entry for entry in agent_list if entry.get("id")}

for agent_id, model in agent_models.items():
    entry = by_id.get(agent_id, {"id": agent_id})
    entry["workspace"] = os.path.join(agent_home, agent_id)
    entry["model"] = model
    entry.setdefault("tools", {})
    entry["tools"].setdefault("fs", {})["workspaceOnly"] = True
    entry["tools"].setdefault("elevated", {})["enabled"] = agent_id in {"ueot-architect", "ueot-techops"}
    if agent_id not in {"ueot-architect", "ueot-techops"}:
        deny = set(entry["tools"].get("deny", []))
        deny.update(deny_for_domains)
        entry["tools"]["deny"] = sorted(deny)
    by_id[agent_id] = entry

ordered = []
for agent_id in agent_models:
    ordered.append(by_id[agent_id])
for entry in agent_list:
    if entry.get("id") not in agent_models:
      ordered.append(entry)
agents["list"] = ordered

with open(config_path, "w", encoding="utf-8") as fh:
    json.dump(cfg, fh, indent=2)
    fh.write("\n")
PY

openclaw config validate >/dev/null

bind_architect() {
  if ! openclaw agents bindings --json | python3 - <<'PY' >/dev/null
import json, sys
raw = sys.stdin.read()
start = min([i for i in (raw.find("["), raw.find("{")) if i != -1], default=-1)
if start == -1:
    sys.exit(1)
data = json.loads(raw[start:])
if isinstance(data, dict):
    data = data.get("bindings", [])
sys.exit(0 if any(item.get("agentId") == "ueot-architect" for item in data) else 1)
PY
  then
    openclaw agents bind --agent ueot-architect --bind telegram >/dev/null || true
  fi
}

bind_architect

upsert_cron() {
  local name="$1"
  shift
  local id
  id="$(
    openclaw cron list --json | python3 - "$name" <<'PY'
import json
import sys
target = sys.argv[1]
raw = sys.stdin.read()
start = min([i for i in (raw.find("{"), raw.find("[")) if i != -1], default=-1)
if start == -1:
    sys.exit(0)
data = json.loads(raw[start:])
for job in data.get("jobs", []):
    if job.get("name") == target:
        print(job["id"])
        break
PY
  )"
  if [[ -n "${id}" ]]; then
    openclaw cron edit "${id}" "$@" >/dev/null
  else
    openclaw cron add --name "${name}" "$@" >/dev/null
  fi
}

common_args=(--tz Asia/Shanghai --session isolated --thinking medium --timeout-seconds 600 --no-deliver)

upsert_cron ueot-techops-daily \
  "${common_args[@]}" \
  --agent ueot-techops \
  --cron "30 8 * * *" \
  --message "Run the scheduled TechOps cycle. Read ops/runbooks/TECHOPS_DAILY.md and execute exactly."

upsert_cron ueot-formal-foundations-daily \
  "${common_args[@]}" \
  --agent ueot-formal-foundations \
  --cron "0 9 * * *" \
  --message "Run the scheduled domain cycle. Read ops/runbooks/DOMAIN_DAILY_TURN.md and execute for formal foundations."

upsert_cron ueot-physics-cosmos-daily \
  "${common_args[@]}" \
  --agent ueot-physics-cosmos \
  --cron "30 9 * * *" \
  --message "Run the scheduled domain cycle. Read ops/runbooks/DOMAIN_DAILY_TURN.md and execute for physics and cosmos."

upsert_cron ueot-biology-evolution-daily \
  "${common_args[@]}" \
  --agent ueot-biology-evolution \
  --cron "0 10 * * *" \
  --message "Run the scheduled domain cycle. Read ops/runbooks/DOMAIN_DAILY_TURN.md and execute for biology and evolution."

upsert_cron ueot-mind-consciousness-daily \
  "${common_args[@]}" \
  --agent ueot-mind-consciousness \
  --cron "30 10 * * *" \
  --message "Run the scheduled domain cycle. Read ops/runbooks/DOMAIN_DAILY_TURN.md and execute for mind and consciousness."

upsert_cron ueot-socioeconomics-civilization-daily \
  "${common_args[@]}" \
  --agent ueot-socioeconomics-civilization \
  --cron "0 11 * * *" \
  --message "Run the scheduled domain cycle. Read ops/runbooks/DOMAIN_DAILY_TURN.md and execute for socioeconomics and civilization."

upsert_cron ueot-meaning-philosophy-daily \
  "${common_args[@]}" \
  --agent ueot-meaning-philosophy \
  --cron "30 11 * * *" \
  --message "Run the scheduled domain cycle. Read ops/runbooks/DOMAIN_DAILY_TURN.md and execute for meaning and philosophy."

upsert_cron ueot-architect-daily \
  "${common_args[@]}" \
  --agent ueot-architect \
  --cron "0 19 * * *" \
  --message "Run the daily architect synthesis. Read ops/runbooks/ARCHITECT_DAILY_SYNTHESIS.md and execute exactly."

upsert_cron ueot-omega-council-wed \
  "${common_args[@]}" \
  --agent ueot-architect \
  --cron "0 21 * * 3" \
  --message "Run the Omega Council cycle. Read ops/runbooks/OMEGA_COUNCIL.md and execute exactly."

upsert_cron ueot-omega-council-sun \
  "${common_args[@]}" \
  --agent ueot-architect \
  --cron "0 21 * * 0" \
  --message "Run the Omega Council cycle. Read ops/runbooks/OMEGA_COUNCIL.md and execute exactly."

upsert_cron ueot-book-weekly \
  "${common_args[@]}" \
  --agent ueot-architect \
  --cron "0 22 * * 0" \
  --message "Run the weekly monograph integration pass. Read ops/runbooks/WEEKLY_MONOGRAPH_PASS.md and execute exactly."

if [[ -n "${telegram_target}" ]]; then
  daily_id="$(
    openclaw cron list --json | python3 - <<'PY'
import json, sys
raw = sys.stdin.read()
start = min([i for i in (raw.find("{"), raw.find("[")) if i != -1], default=-1)
if start == -1:
    sys.exit(0)
data = json.loads(raw[start:])
for job in data.get("jobs", []):
    if job.get("name") == "ueot-architect-daily":
        print(job["id"])
        break
PY
  )"
  if [[ -n "${daily_id}" ]]; then
    openclaw cron edit "${daily_id}" \
      --announce \
      --channel telegram \
      --to "${telegram_target}" >/dev/null
  fi
fi

"${script_dir}/reindex_ueot_memory.sh"
"${script_dir}/validate_ueot_system.sh"
