#!/usr/bin/env python3
"""Local, read-only branch/worktree inventory. No merges, removals or pushes."""
import argparse
import json
import re
import subprocess
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
OUT = HERE / "UMC_LOCAL_BRANCH_INVENTORY_2026-10-09.json"
REPORT = HERE / "UMC_LOCAL_BRANCH_RECONCILIATION_2026-10-09.md"
DECL = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|structure|class|inductive)\s+([A-Za-z_][A-Za-z_0-9']*)\b",
    re.M,
)

def git(*args, cwd=ROOT, allow_fail=False):
    p = subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True)
    if p.returncode and not allow_fail:
        raise RuntimeError("git " + " ".join(args) + ": " + p.stderr[:300])
    return p.stdout.rstrip("\n") if p.returncode == 0 else None

def is_ancestor(branch, target):
    return subprocess.run(
        ["git", "merge-base", "--is-ancestor", branch, target],
        cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
    ).returncode == 0

def build():
    current = git("symbolic-ref", "--quiet", "--short", "HEAD", allow_fail=True)
    main_sha = (git("rev-parse", "--verify", "refs/heads/main", allow_fail=True)
                or git("rev-parse", "--verify", "refs/remotes/origin/main", allow_fail=True))
    main_known = main_sha is not None
    baseline = main_sha if main_known else git("rev-parse", "HEAD")
    names = git("for-each-ref", "--format=%(refname:short)", "refs/heads").splitlines()
    leanroot = ROOT / "formalization/ueot-core/UEOT"
    current_declarations = set()
    for file in sorted(leanroot.rglob("*.lean")):
        current_declarations.update(DECL.findall(file.read_text()))
    branches = []
    for name in names:
        # A detached/offline clone may have NO local or remote main ref.
        # HEAD is only a comparison fallback and MUST NOT become "main".
        main_ancestor = is_ancestor(name, baseline) if main_known else None
        local_head = name == current
        status = ("MAIN_BASELINE_UNAVAILABLE" if not main_known else
                  "CURRENT_CHECKOUT" if local_head else
                  "ALREADY_REACHABLE_FROM_MAIN" if main_ancestor else
                  "HISTORICAL_DIVERGENCE_REQUIRES_CONTENT_REVIEW")
        changed = []
        missing_symbols = []
        if main_known and not main_ancestor and not local_head:
            changed = git("diff", "--name-only", baseline + "..." + name).splitlines()
            for path in changed:
                if not path.startswith("formalization/ueot-core/UEOT/") or not path.endswith(".lean"):
                    continue
                historical = git("show", name + ":" + path, allow_fail=True)
                if historical is None:
                    continue
                for sym in sorted(set(DECL.findall(historical)) - current_declarations):
                    missing_symbols.append({"path": path, "name": sym})
        branches.append({
            "name": name, "head": git("rev-parse", name), "status": status,
            "is_main_ancestor": main_ancestor,
            "unique_commits_vs_main": (int(git("rev-list", "--count", baseline + ".." + name))
                                       if main_known else None),
            "changed_paths_since_merge_base": changed,
            "changed_path_count": len(changed),
            "historical_decl_names_missing_from_current_source": missing_symbols,
            "historical_decl_missing_count": len(missing_symbols),
            "review_risk": ("HISTORICAL_PROOF_NAME_OR_SEMANTIC_SCOPE" if missing_symbols else
                "FROZEN_ROOT_LEDGER_OR_WORKFLOW" if any(
                    s.endswith(("COMPRESSION_LEDGER.yaml","TheoryCompletion.lean","UEOT.lean"))
                    or s.startswith(".github/") for s in changed
                ) else "HISTORICAL_CONTENT_DIFF"),
            "recommendation": ("PRESERVE_NO_MAIN_ANCESTRY_CLAIM" if not main_known else
              "PRESERVE_CURRENT_CHECKOUT" if local_head else
              "RETAIN_HISTORY_ALREADY_IN_MAIN" if main_ancestor else
              "NO_WHOLE_BRANCH_MERGE_COMPARE_LATEST_SOURCE_AND_KEEP_PROVENANCE"),
        })
    wt = []
    for block in git("worktree", "list", "--porcelain").split("\n\n"):
        lines = block.splitlines()
        path = next((x[9:] for x in lines if x.startswith("worktree ")), None)
        if path is None:
            continue
        tracked = git("status", "--porcelain", "--untracked-files=no", cwd=path)
        untracked = git("ls-files", "--others", "--exclude-standard", cwd=path)
        wt.append({
            "path": path,
            "head": next((x[5:] for x in lines if x.startswith("HEAD ")), None),
            "branch": next((x[7:] for x in lines if x.startswith("branch ")), None),
            "detached": "detached" in lines,
            "tracked_dirty_count": len(tracked.splitlines()) if tracked else 0,
            "untracked_file_count": len(untracked.splitlines()) if untracked else 0,
            "recommendation": "PRESERVE_NO_AUTOMATIC_REMOVE",
        })
    counts = Counter(b["status"] for b in branches)
    return {
        "schema": 1,
        "scope": "LOCAL_GIT_GRAPH_AND_LEXICAL_LEAN_RECONCILIATION_NOT_SEMANTIC_CERTIFICATION",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "main": main_sha,
        "main_comparison_available": main_known,
        "baseline_ref": baseline,
        "baseline_meaning": ("MAIN_ANCESTRY" if main_known else
                             "HEAD_ONLY_NOT_MAIN_DO_NOT_CLASSIFY_MERGED"),
        "active_branch": current,
        "active_local_head": git("rev-parse", "HEAD"),
        "origin_main_local_tracking_snapshot":
            git("rev-parse", "--verify", "refs/remotes/origin/main", allow_fail=True),
        "branch_count": len(branches),
        "branch_status_counts": dict(counts),
        "worktree_count": len(wt),
        "tracked_dirty_worktree_count": sum(x["tracked_dirty_count"] != 0 for x in wt),
        "missing_historical_lean_symbol_count":
            sum(b["historical_decl_missing_count"] for b in branches),
        "branches": branches, "worktrees": wt,
        "limits": [
            "Same Lean theorem name does NOT prove that body, hypotheses or meaning agree.",
            "Non-ancestry can reflect squash, cherry-pick or later improvements.",
            "Local main/origin-main snapshot, no remote fetch.",
            "No branch, worktree, stash, local files, or remote refs are deleted or changed.",
        ],
    }

def run(output=None, report=None):
    # Historic date-stamped snapshots are immutable evidence, not live targets.
    protected = {OUT.resolve(), REPORT.resolve()}
    for target in (output, report):
        if target is not None and Path(target).resolve() in protected:
            raise ValueError("refusing to overwrite historical UMC audit evidence")
    data = build()
    if output is not None:
        Path(output).write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    statuses = data["branch_status_counts"]
    nonmerged = [b for b in data["branches"]
                 if b["status"] == "HISTORICAL_DIVERGENCE_REQUIRES_CONTENT_REVIEW"]
    lines = [
        "# UEOT 本地分支与 worktree 逐项保存性审计（2026-10-09）",
        "",
        f"- 基线：main {(data['main'] or 'UNAVAILABLE')[:12]}，活动研究 {data['active_local_head'][:12]}；仅本地快照。",
        f"- {data['branch_count']} 个分支：main 已包含 {statuses.get('ALREADY_REACHABLE_FROM_MAIN',0)}；"
        f"活动研究 {statuses.get('CURRENT_CHECKOUT',0)}；图上尚未并入 {len(nonmerged)}；"
        f"无法确认 main 祖先关系 {statuses.get('MAIN_BASELINE_UNAVAILABLE',0)}。",
        f"- {data['worktree_count']} 个 worktree；有已跟踪文件修改的工作树数"
        f" {data['tracked_dirty_worktree_count']}。",
        f"- 当前代码查不到的历史 Lean 声明名有"
        f" {data['missing_historical_lean_symbol_count']} 个（不代表语义缺失）。",
        "",
        ("## 图上未并入分支逐项" if data["main_comparison_available"]
         else "## main 祖先关系未知：不作已合并或未合并断言"),
        "| 分支 | 独有提交 | 比较路径数 | 历史声明名缺失数 | 处理 |",
        "|---|---:|---:|---:|---|",
    ]
    for b in nonmerged:
        lines.append(f"| {b['name']} | {b['unique_commits_vs_main']} | "
                     f"{b['changed_path_count']} | {b['historical_decl_missing_count']} | "
                     "保留，不得整支覆盖现有源码 |")
    historical_main_claims = [
        "",
        "## 已核对的几个关键真实内容差异",
        "- 旧 endogenous-object 备份的两个实质 Lean 源已由主线强化："
        "当前主线新增 infinite all-times persistence、wrong-controller no-repair "
        "和 nonempty constitutive persistence certificates。旧备份不能反向覆盖。",
        "- 旧 P7-P12 分支存在 objectScaleMap_does_not_determine_wilsonian_flow，"
        "主线主动收窄到 wilsonianCouplingFlow_nontrivial_of_twoCouplings；"
        "这是去掉未经证明的尺度映射兼容暗示，不恢复旧的强名称。",
        "- formal/p* 等旧分支的具体主要 Lean 证明已在 main；"
        "不可因旧 Git SHA 不可达而重复插入，或覆盖主线引入的根导入。",
        "- 旧 ops/scientific-governance 分支可能保留有价值的历史审计文件，"
        "但当前安全合同和账本更新，不做整体 cherry-pick。",
    ] if data["main_comparison_available"] else [
        "",
        "## main 基线不可用：历史合并结论未验证",
        "- 当前仓库没有可核验的本地或远端 main 引用。本报告不宣称任何历史"
        "分支已合并、被主线替代或应当清理。",
        "- 待取得实际 main ref 后重新执行报告，不使用当前 HEAD 冒充 main。",
    ]
    lines.extend([
        *historical_main_claims,
        "",
        "## 整理决策",
        f"1. {statuses.get('ALREADY_REACHABLE_FROM_MAIN',0)} 个已确认进入 main 的分支；"
        f"其他 {statuses.get('MAIN_BASELINE_UNAVAILABLE',0)} 个主分支基线未知的分支不可判为已合并。",
        f"2. {len(nonmerged)} 个图上分叉分支：仅对当前源码实际缺失的、语义审计通过的"
        "定理作选择性迁移。本轮无已确认可以整支合并的分支。",
        "3. 所有 detached review worktree 保留；其已跟踪内容干净"
        "不等于 untracked 内容可删除。",
        "4. 仅在当前明确授权的研究分支推进；"
        "不改冻结 106/106、四生成器、P12 PARTIAL 和远端 main。",
        "",
        "## 审计方法限制",
        *["- " + x for x in data["limits"]],
        "",
    ])
    if report is not None:
        Path(report).write_text("\n".join(lines), encoding="utf-8")
    print("UMC_LOCAL_BRANCH_AUDIT", json.dumps({
        "branches": data["branch_count"],
        "main_ancestor": statuses.get("ALREADY_REACHABLE_FROM_MAIN",0),
        "historical_nonancestor": len(nonmerged),
        "worktrees": data["worktree_count"],
        "dirty_tracked_worktrees": data["tracked_dirty_worktree_count"],
        "missing_lean_symbol_names": data["missing_historical_lean_symbol_count"],
    }, sort_keys=True))
if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, help="new JSON destination; default stdout summary only")
    ap.add_argument("--report", type=Path, help="new Markdown destination")
    args = ap.parse_args()
    run(args.output, args.report)
