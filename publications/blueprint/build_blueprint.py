#!/usr/bin/env python3
"""Build the interactive Lean 4 Pure-Kernel Blueprint static website.

Parses all 1,051 compiled Lean 4 library modules under `formalization/ueot-core/`
plus `ASSUMPTION_CLASSIFICATION_106.json`, verifies every flagship theorem module
link, and generates a zero-CDN, self-contained interactive site under
`publications/blueprint/site/`.

Usage:
    python3 publications/blueprint/build_blueprint.py
"""
from __future__ import annotations

from collections import Counter, defaultdict
from pathlib import Path
import datetime
import json
import re

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[1]
CORE_DIR = REPO_ROOT / "formalization" / "ueot-core"
ASSUMP_PATH = CORE_DIR / "docs" / "ASSUMPTION_CLASSIFICATION_106.json"
SITE_DIR = HERE / "site"
DATA_DIR = SITE_DIR / "data"

GITHUB_BLOB_BASE = "https://github.com/MurphyHoops/UEOT/blob/main/formalization/ueot-core"
ZENODO_V1_DOI = "10.5281/zenodo.24433585"
ZENODO_CONCEPT_DOI = "10.5281/zenodo.24433584"

IMPORT_RE = re.compile(r"^\s*import\s+(UEOT(?:\.[A-Za-z0-9_']+)*)", re.M)
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|structure|inductive|abbrev|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)",
    re.M,
)
DOC_RE = re.compile(r"/-!\s*(.*?)\s*-/", re.S)


def classify_cluster(mod_name: str, rel_path: str) -> str:
    if mod_name == "UEOT" or mod_name.startswith("UEOT.Core"):
        return "Core Foundations"
    if "ThirdParty" in rel_path:
        return "ThirdParty Verified Bridges"
    if "UnifiedClosure" in rel_path:
        stem = Path(rel_path).stem
        if stem.startswith("Brownian") or "Ito" in stem or "Girsanov" in stem or "HJB" in stem:
            return "Stochastic Calculus & Continuous Bridge"
        return "Control, Risk & Certified Decision DAGs"
    if "TheoryCompletion" in rel_path:
        return "Theory Completion & Structural Compression"
    if "Objecthood" in rel_path or "CrossTrack" in rel_path or "Hierarchy" in rel_path:
        return "Objecthood, Quotients & Cross-Track"
    if mod_name.startswith("UEOT.V3.Compression"):
        return "Compression Core"
    return "Domain Ledger & Adapters (V3)"


def extract_docstring(text: str) -> str:
    m = DOC_RE.search(text[:2500])
    if not m:
        return ""
    raw = m.group(1).strip()
    lines = [ln.strip().lstrip("#").strip() for ln in raw.splitlines() if ln.strip()]
    joined = " ".join(lines)
    if len(joined) > 260:
        joined = joined[:257].rstrip() + "..."
    return joined


def collect_lean_modules() -> tuple[list[dict], dict[str, str]]:
    lean_files = [CORE_DIR / "UEOT.lean"] + sorted((CORE_DIR / "UEOT").rglob("*.lean"))
    lean_files = [p for p in lean_files if p.is_file()]

    modules: list[dict] = []
    stem_to_mod: dict[str, str] = {}
    mod_map: dict[str, dict] = {}

    for p in lean_files:
        rel = p.relative_to(CORE_DIR).as_posix()
        mod_name = rel[:-5].replace("/", ".")
        text = p.read_text(encoding="utf-8", errors="replace")
        imports = sorted(set(IMPORT_RE.findall(text)))
        decls = DECL_RE.findall(text)
        counts = Counter(kind for kind, _ in decls)
        thm_count = counts["theorem"] + counts["lemma"]
        def_count = counts["def"] + counts["abbrev"] + counts["structure"] + counts["inductive"] + counts["class"]
        sample_decls = [name for _, name in decls[:12]]
        cluster = classify_cluster(mod_name, rel)

        entry = {
            "id": mod_name,
            "short": p.stem,
            "path": rel,
            "url": f"{GITHUB_BLOB_BASE}/{rel}",
            "cluster": cluster,
            "lines": text.count("\n") + 1,
            "theorems": thm_count,
            "definitions": def_count,
            "imports": imports,
            "dependents": [],
            "sample_decls": sample_decls,
            "doc": extract_docstring(text),
        }
        modules.append(entry)
        mod_map[mod_name] = entry
        stem_to_mod.setdefault(p.stem, mod_name)

    # Filter imports to library modules and populate reverse edges
    for entry in modules:
        valid_imports = [imp for imp in entry["imports"] if imp in mod_map]
        entry["imports"] = valid_imports
        for imp in valid_imports:
            mod_map[imp]["dependents"].append(entry["id"])

    for entry in modules:
        entry["dependents"].sort()
        entry["in_deg"] = len(entry["imports"])
        entry["out_deg"] = len(entry["dependents"])

    # Compute DAG depth (longest path from leaves)
    memo: dict[str, int] = {}

    def depth(mid: str, stack: set[str]) -> int:
        if mid in memo:
            return memo[mid]
        if mid in stack:
            return 0
        stack.add(mid)
        imps = mod_map[mid]["imports"]
        d = 0 if not imps else 1 + max(depth(i, stack) for i in imps)
        stack.remove(mid)
        memo[mid] = d
        return d

    for entry in modules:
        entry["depth"] = depth(entry["id"], set())

    return modules, stem_to_mod


def build_paper_blueprints(mod_ids: set[str], stem_to_mod: dict[str, str]) -> dict:
    def resolve(stem: str) -> str:
        full = f"UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.{stem}"
        if full in mod_ids:
            return full
        if stem in stem_to_mod:
            return stem_to_mod[stem]
        raise RuntimeError(f"Blueprint module not found in compiled Lean library: {stem}")

    paper2_nodes = [
        {
            "key": "p2_t1",
            "label": "Thm 1: Trace-Support Viability",
            "layer": 0,
            "paper": "Paper 2 (JAR)",
            "module": resolve("FiniteSupportViability"),
            "statement": "Positive-mass Bayesian posterior supports equal combinatorial trace-support recursion S_n(g) across unenumerated observation types Y, yielding non-circular finite-horizon viability.",
            "deps": [],
        },
        {
            "key": "p2_t2",
            "label": "Thm 2: König Compactness",
            "layer": 1,
            "paper": "Paper 2 (JAR)",
            "module": resolve("InfiniteSupportViability"),
            "statement": "Time-inhomogeneous quantifier exchange: arbitrarily long finite-horizon zero-uncovered causal policies exist iff a single all-time policy exists (finite X, finite nonempty A).",
            "deps": ["p2_t1"],
        },
        {
            "key": "p2_t3a",
            "label": "Thm 3a: Winning-Arena GFP",
            "layer": 1,
            "paper": "Paper 2 (JAR)",
            "module": resolve("FiniteSupportFixedPoint"),
            "statement": "Top-down Kleene iteration stabilizes in <= 2^|X|-1 rounds at the greatest fixed point W_* = gfp(Phi), separating 2-state memory from memoryless feedback.",
            "deps": ["p2_t1"],
        },
        {
            "key": "p2_t3b",
            "label": "Thm 3b: Executable Synthesizer",
            "layer": 2,
            "paper": "Paper 2 (JAR)",
            "module": resolve("ExecutableSupportController"),
            "statement": "Purely computable `synthesize : Option (Program X Y A)` is sound and complete, linking killed substochastic matrix powers Q_K^T to Kolmogorov infinite-trajectory safety P(forall n, X_n in K) = 1.",
            "deps": ["p2_t2", "p2_t3a"],
        },
        {
            "key": "p2_t4",
            "label": "Thm 4: Fixed-Sample No-Go",
            "layer": 0,
            "paper": "Paper 2 (JAR)",
            "module": resolve("FixedSampleSupportNoGo"),
            "statement": "No randomized fixed-sample black-box test can uniformly certify exact zero transition leakage above significance level alpha.",
            "deps": [],
        },
        {
            "key": "p2_t5",
            "label": "Thm 5: Calibrated Risk Oracle",
            "layer": 3,
            "paper": "Paper 2 (JAR)",
            "module": resolve("NoisyFiniteRiskOracle"),
            "statement": "Computable rational `NoisyFiniteRiskOracle` decouples sample-free perpetual safety from G_u-calibrated finite-horizon risk across m abstractions without m-union penalties: P_J(accept & E) <= alpha_N + (1-alpha_N)beta.",
            "deps": ["p2_t3b", "p2_t4"],
        },
        {
            "key": "p2_t5w",
            "label": "Witness: N=4096 Risk Oracle",
            "layer": 4,
            "paper": "Paper 2 (JAR)",
            "module": resolve("NoisyFiniteRiskOracleWitness"),
            "statement": "Machine-checked finite witness (N=4096, u=1/20, beta=7/10) with alpha_4096 <= 6.12e-8, 99.988% true acceptance at theta=1/4, and 5.97e-71 false acceptance at theta=1/8.",
            "deps": ["p2_t5"],
        },
        {
            "key": "p2_t6",
            "label": "Thm 6: Measurable Belief Quotient",
            "layer": 1,
            "paper": "Paper 2 (JAR)",
            "module": resolve("ObservableBeliefQuotient"),
            "statement": "On standard Borel spaces with deterministic binary observation, the regular Giry belief kernel descends through c_q(b) iff `ClosedTests` holds, while latent safety can still be erased.",
            "deps": [],
        },
        {
            "key": "p2_t7a",
            "label": "Thm 7a: Prepaid Fault Regret",
            "layer": 2,
            "paper": "Paper 2 (JAR)",
            "module": resolve("RegisterMechanismDecisionRegret"),
            "statement": "Exact 3-step distinguishability Delta_{3,B} = r^2(1-r)1_{B>=c} and Bayes-minimax saddle proving randomized minimax regret R* = 3/128 strictly beats the deterministic lattice barrier 1/32.",
            "deps": ["p2_t6"],
        },
        {
            "key": "p2_t7b",
            "label": "Thm 7b: GCD-Free Kernel `decide`",
            "layer": 3,
            "paper": "Paper 2 (JAR)",
            "module": resolve("RegisterMechanismDecisionConsumer"),
            "statement": "Unnormalized integer-weighted `UBelief` and dyadic `csolveInt` eliminate Nat.gcd blowup so full 7-action POMDP optima verify inside Lean's kernel via `decide` (0 Lean.ofReduceBool).",
            "deps": ["p2_t7a"],
        },
    ]

    paper3_nodes = [
        {
            "key": "p3_t1",
            "label": "Thm 1: Native Store Commutation",
            "layer": 0,
            "paper": "Paper 3 (MOR)",
            "module": resolve("RegisterJointDecisionNativeConsumer"),
            "statement": "Unbounded native lineage store commutes transaction-by-transaction with compressed belief-wallet DP under pathwise prepayment B_t = B_0 - sum C_s >= 0.",
            "deps": [],
        },
        {
            "key": "p3_t2",
            "label": "Thm 2: Single-Repair Thresholds",
            "layer": 1,
            "paper": "Paper 3 (MOR)",
            "module": resolve("RegisterJointDecisionOptimality"),
            "statement": "Universal zero-value impossibility for B_0 < c and exact high-price closed-form optimal value V_{H+1}^* with nested single-crossing thresholds.",
            "deps": ["p3_t1"],
        },
        {
            "key": "p3_t3",
            "label": "Thm 3: Value-of-Information Splits",
            "layer": 1,
            "paper": "Paper 3 (MOR)",
            "module": resolve("RegisterJointDecisionBoundary"),
            "statement": "Separates persistence variance premium d*Var(r_theta), post-fault threshold drop (21/16 -> 5/4), 4-step receipt feedback gain (20925/524288), and zero post-repair EVPI.",
            "deps": ["p3_t1"],
        },
        {
            "key": "p3_t4",
            "label": "Thm 4: Informative Zero Receipts",
            "layer": 2,
            "paper": "Paper 3 (MOR)",
            "module": resolve("RegisterDecisionCountHistory"),
            "statement": "Separates informative operational zero receipts from deterministic damaged-idle/absent-slot zeros; policy factors cancel identically across all causal policies.",
            "deps": ["p3_t2", "p3_t3"],
        },
        {
            "key": "p3_t5a",
            "label": "Thm 5a: 5-Coord Sufficiency",
            "layer": 3,
            "paper": "Paper 3 (MOR)",
            "module": resolve("RegisterDecisionRepresentationModel"),
            "statement": "Proves joint all-action sufficiency of the 5-coordinate counting summary sigma = (t, q, s, f, k) for optimal values and observable trajectory laws.",
            "deps": ["p3_t4"],
        },
        {
            "key": "p3_t5b",
            "label": "Thm 5b: Sharpness Witnesses",
            "layer": 3,
            "paper": "Paper 3 (MOR)",
            "module": resolve("RegisterDecisionRepresentationWitnesses"),
            "statement": "Three-way sharpness: physical-Markov insufficiency (5/8 != 1/2), genealogy-erasing merger across legal actions, and slot-2 dispatch breaking the merger.",
            "deps": ["p3_t4"],
        },
        {
            "key": "p3_t6a",
            "label": "Thm 6a: Certified DAG Soundness",
            "layer": 4,
            "paper": "Paper 3 (MOR)",
            "module": resolve("FiniteJointDecisionDAG"),
            "statement": "Two-layer untrusted memoizer + trusted `certify` checker soundness: every accepted polynomial DAG computes exact Bayes-optimal all-action values.",
            "deps": ["p3_t5a"],
        },
        {
            "key": "p3_t6b",
            "label": "Thm 6b: 24(H+1)^4 Certified Entry",
            "layer": 5,
            "paper": "Paper 3 (MOR)",
            "module": resolve("RegisterDecisionRepresentation"),
            "statement": "Executable `accept` (`certify` + `boundCheck`) certifying N_H <= 24(H+1)^4, compressing 28^8 ~ 3.78e11 branches to 1,661 certified nodes (151 active execution nodes).",
            "deps": ["p3_t5b", "p3_t6a"],
        },
    ]

    return {
        "paper2": {
            "title": "Paper 2 — Pure-Kernel Verified Controller Synthesis & Calibrated Post-Selection Risk (JAR)",
            "subtitle": "End-to-end semantic chain from trace-support viability and computable controller synthesis to candidate-free post-selection risk and GCD-free kernel `decide`.",
            "nodes": paper2_nodes,
        },
        "paper3": {
            "title": "Paper 3 — Prepayment Thresholds, Informative Zero Receipts, & Certified Polynomial DAGs (MOR)",
            "subtitle": "Unbounded native lineage commutation, Bayesian value-of-information boundaries, five-coordinate sufficiency, and certified 24(H+1)^4 decision diagrams.",
            "nodes": paper3_nodes,
        },
    }


def render_html() -> str:
    return """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>Lean 4 Pure-Kernel Formalization Blueprint — Viability, Calibrated Risk & Certified Control</title>
<style>
  :root {
    --bg: #0b1020;
    --surface: #121933;
    --surface-2: #182244;
    --border: #26345e;
    --text: #e6ecf8;
    --muted: #98a6c8;
    --accent: #58a6ff;
    --green: #3fb950;
    --amber: #e3b341;
    --purple: #bc8cff;
    --teal: #39d0d8;
    --rose: #f778ba;
    --mono: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
    --sans: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Inter, Helvetica, Arial, sans-serif;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    font-family: var(--sans);
    background: var(--bg);
    color: var(--text);
    line-height: 1.55;
  }
  a { color: var(--accent); text-decoration: none; }
  a:hover { text-decoration: underline; }
  header {
    background: linear-gradient(135deg, #0d152c 0%, #152147 60%, #111c3a 100%);
    border-bottom: 1px solid var(--border);
    padding: 28px 24px 20px;
  }
  .container { max-width: 1320px; margin: 0 auto; padding: 0 20px; }
  .eyebrow {
    font-size: 12px;
    text-transform: uppercase;
    letter-spacing: 0.12em;
    color: var(--teal);
    font-weight: 700;
  }
  h1 {
    margin: 6px 0 10px;
    font-size: clamp(22px, 3vw, 32px);
    line-height: 1.2;
    font-weight: 750;
  }
  .subtitle {
    color: var(--muted);
    max-width: 900px;
    font-size: 15px;
    margin: 0 0 16px;
  }
  .badges {
    display: flex;
    flex-wrap: wrap;
    gap: 8px;
    margin-bottom: 18px;
  }
  .badge {
    display: inline-flex;
    align-items: center;
    gap: 6px;
    padding: 4px 10px;
    border-radius: 999px;
    font-size: 12.5px;
    font-weight: 600;
    background: rgba(88, 166, 255, 0.12);
    border: 1px solid rgba(88, 166, 255, 0.3);
    color: var(--text);
  }
  .badge.green { background: rgba(63, 185, 80, 0.14); border-color: rgba(63, 185, 80, 0.45); color: #7ee787; }
  .badge.purple { background: rgba(188, 140, 255, 0.14); border-color: rgba(188, 140, 255, 0.4); color: #d2a8ff; }
  .badge.amber { background: rgba(227, 179, 65, 0.14); border-color: rgba(227, 179, 65, 0.4); color: #f2cc60; }

  nav.tabs {
    display: flex;
    flex-wrap: wrap;
    gap: 6px;
    margin-top: 12px;
  }
  nav.tabs button {
    background: transparent;
    color: var(--muted);
    border: 1px solid transparent;
    padding: 8px 14px;
    border-radius: 8px;
    cursor: pointer;
    font-size: 14px;
    font-weight: 600;
    transition: all 0.15s ease;
  }
  nav.tabs button:hover { color: var(--text); background: rgba(255,255,255,0.05); }
  nav.tabs button.active {
    color: #fff;
    background: var(--surface-2);
    border-color: var(--accent);
  }

  main { padding: 24px 0 60px; }
  section.panel { display: none; }
  section.panel.active { display: block; }

  .kpi-grid {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(175px, 1fr));
    gap: 14px;
    margin-bottom: 24px;
  }
  .kpi {
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 12px;
    padding: 16px;
  }
  .kpi .val { font-size: 28px; font-weight: 800; letter-spacing: -0.02em; }
  .kpi .val.green { color: #7ee787; }
  .kpi .lbl { font-size: 12.5px; color: var(--muted); margin-top: 4px; }

  .card {
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 12px;
    padding: 20px;
    margin-bottom: 20px;
  }
  .card h2 { margin: 0 0 10px; font-size: 18px; }
  .card h3 { margin: 0 0 8px; font-size: 15.5px; color: var(--teal); }

  .two-col {
    display: grid;
    grid-template-columns: minmax(0, 1.8fr) minmax(300px, 1fr);
    gap: 18px;
    align-items: start;
  }
  @media (max-width: 980px) { .two-col { grid-template-columns: 1fr; } }

  .graph-controls {
    display: flex;
    flex-wrap: wrap;
    gap: 8px;
    margin-bottom: 12px;
    align-items: center;
  }
  .pill-btn {
    background: var(--surface-2);
    color: var(--text);
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 6px 12px;
    font-size: 13px;
    font-weight: 600;
    cursor: pointer;
  }
  .pill-btn.active { border-color: var(--accent); background: rgba(88,166,255,0.2); }

  #blueprint-svg-wrap {
    background: #090e1c;
    border: 1px solid var(--border);
    border-radius: 10px;
    overflow: auto;
    min-height: 460px;
  }
  svg.bp-svg { width: 100%; height: 480px; display: block; }
  .bp-node { cursor: pointer; transition: opacity 0.15s ease; }
  .bp-node rect { rx: 10; ry: 10; stroke-width: 1.6; }
  .bp-node:hover rect { filter: brightness(1.18); }
  .bp-node.selected rect { stroke: #fff !important; stroke-width: 2.5; }

  .inspector {
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 12px;
    padding: 18px;
    position: sticky;
    top: 16px;
  }
  .inspector h3 { margin: 0 0 6px; font-size: 16px; word-break: break-word; }
  .meta-row { display: flex; flex-wrap: wrap; gap: 6px; margin: 10px 0; }
  .chip {
    font-family: var(--mono);
    font-size: 11.5px;
    background: var(--surface-2);
    border: 1px solid var(--border);
    padding: 2px 8px;
    border-radius: 6px;
    color: var(--text);
  }
  .list-box {
    max-height: 150px;
    overflow-y: auto;
    background: #0a0f1f;
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 8px 10px;
    font-family: var(--mono);
    font-size: 12px;
    margin-top: 6px;
  }
  .list-box div { padding: 2px 0; cursor: pointer; color: var(--accent); }
  .list-box div:hover { text-decoration: underline; }

  .filter-bar {
    display: flex;
    flex-wrap: wrap;
    gap: 10px;
    margin-bottom: 14px;
  }
  .filter-bar input, .filter-bar select {
    background: #0a0f1f;
    color: var(--text);
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 8px 12px;
    font-size: 13.5px;
  }
  .filter-bar input { flex: 1; min-width: 220px; }

  table {
    width: 100%;
    border-collapse: collapse;
    font-size: 13.5px;
  }
  th, td {
    text-align: left;
    padding: 10px 10px;
    border-bottom: 1px solid var(--border);
    vertical-align: top;
  }
  th { color: var(--muted); font-weight: 600; font-size: 12px; text-transform: uppercase; letter-spacing: 0.05em; }
  tr.mod-row { cursor: pointer; }
  tr.mod-row:hover { background: rgba(88, 166, 255, 0.08); }
  code, pre { font-family: var(--mono); }
  pre {
    background: #080d1a;
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 14px;
    overflow-x: auto;
    font-size: 13px;
    line-height: 1.5;
    color: #c9d8f5;
  }
  .bar-row { display: flex; align-items: center; gap: 10px; margin: 8px 0; font-size: 13.5px; }
  .bar-label { width: 290px; color: var(--text); flex-shrink: 0; }
  .bar-track { flex: 1; height: 12px; background: #0a0f1f; border-radius: 999px; overflow: hidden; border: 1px solid var(--border); }
  .bar-fill { height: 100%; background: linear-gradient(90deg, var(--accent), var(--teal)); }
  .bar-num { width: 95px; text-align: right; font-family: var(--mono); color: var(--muted); font-size: 12.5px; }
  footer {
    border-top: 1px solid var(--border);
    padding: 20px 0 36px;
    color: var(--muted);
    font-size: 13px;
    text-align: center;
  }
</style>
</head>
<body>
<header>
  <div class="container">
    <div class="eyebrow">Pure-Kernel Lean 4 Formalization Blueprint · Lean v4.33.1 / Mathlib</div>
    <h1>Certified Viability, Calibrated Post-Selection Risk &amp; Polynomial Decision DAGs</h1>
    <p class="subtitle">
      Interactive dependency graph, module explorer, and assumption-classification ledger for a
      <strong>1,051-module</strong> pure-kernel Lean 4 formalization (<strong>13,004 theorems</strong>,
      <strong>0 <code>sorryAx</code></strong>, <strong>0 <code>Lean.ofReduceBool</code> / <code>native_decide</code></strong>)
      supporting companion articles on executable controller synthesis and partially observed regenerative control.
    </p>
    <div class="badges">
      <span class="badge green">&#10003; Axioms: {propext, Classical.choice, Quot.sound}</span>
      <span class="badge green">&#10003; 0 sorryAx &middot; 0 native_decide</span>
      <span class="badge purple">Apache-2.0 Archive: <a href="https://doi.org/10.5281/zenodo.24433585" target="_blank" rel="noopener">doi:10.5281/zenodo.24433585</a></span>
      <span class="badge amber"><a href="https://github.com/MurphyHoops/UEOT" target="_blank" rel="noopener">GitHub Repository</a></span>
    </div>
    <nav class="tabs" id="nav-tabs">
      <button class="active" data-tab="overview">Overview &amp; Audit</button>
      <button data-tab="graph">Interactive Theorem Blueprint</button>
      <button data-tab="modules">1,051-Module Explorer</button>
      <button data-tab="assumptions">106-Assumption Ledger</button>
      <button data-tab="reproduce">Reproduce &amp; Cite</button>
    </nav>
  </div>
</header>

<main class="container">
  <!-- TAB 1: OVERVIEW -->
  <section id="tab-overview" class="panel active">
    <div class="kpi-grid" id="kpi-grid"></div>
    <div class="two-col">
      <div>
        <div class="card">
          <h2>Library Architecture by Thematic Cluster</h2>
          <p style="color:var(--muted);font-size:13.5px;margin-top:0;">
            Every module count and import edge below is extracted directly from <code>formalization/ueot-core/UEOT.lean</code> and <code>UEOT/**/*.lean</code>.
          </p>
          <div id="cluster-bars"></div>
        </div>
        <div class="card">
          <h2>Flagship Research Articles Grounded in This Formalization</h2>
          <table>
            <thead>
              <tr><th>Track</th><th>Article Title &amp; Target Venue</th><th>Key Verified Lean 4 Contributions</th></tr>
            </thead>
            <tbody>
              <tr>
                <td><span class="chip">Paper 2</span></td>
                <td><strong>Pure-Kernel Verified Controller Synthesis, Fixed-Sample Impossibility, and Calibrated Post-Selection Risk under Partial Observation</strong><br/><span style="color:var(--muted);">Submitted to <em>Journal of Automated Reasoning</em></span></td>
                <td>Executable finite-memory synthesizer <code>synthesize</code> bridged to Kolmogorov infinite-trajectory safety; fixed-sample zero-leakage impossibility; candidate-free <code>NoisyFiniteRiskOracle</code>; GCD-free integer <code>UBelief</code>/<code>csolveInt</code> kernel <code>decide</code> for minimax regret <code>3/128 &lt; 1/32</code>.</td>
              </tr>
              <tr>
                <td><span class="chip">Paper 3</span></td>
                <td><strong>Prepayment Thresholds, Informative Zero Receipts, and Certified Polynomial Decision Diagrams in Partially Observed Regenerative Maintenance</strong><br/><span style="color:var(--muted);">Submitted to <em>Mathematics of Operations Research</em></span></td>
                <td>Unbounded native lineage commutation under pathwise prepayment; Bayesian value-of-information boundaries; informative zero-receipt filtering; five-coordinate counting sufficiency; two-layer certified <code>24(H+1)^4</code> polynomial decision DAGs.</td>
              </tr>
              <tr>
                <td><span class="chip">Paper 1</span></td>
                <td><strong>What Prediction Leaves Out: Relational Objecthood and the Grounds of Purpose</strong><br/><span style="color:var(--muted);">Submitted to <em>The British Journal for the Philosophy of Science</em></span></td>
                <td>Self-contained stochastic register model separating infinite birth-law equivalence from paid repair expenditure, Blackwell non-simulable protocol refinements, and bearer-indexed grounds of purpose.</td>
              </tr>
            </tbody>
          </table>
        </div>
      </div>
      <div>
        <div class="card">
          <h2>Pure-Kernel Axiom Audit Receipt</h2>
          <p style="color:var(--muted);font-size:13.5px;margin-top:0;">
            Verified environment-wide by <code>scripts/ExhaustiveAxiomAudit.lean</code> across all 1,030 constant-defining modules (within the 1,051 compiled modules):
          </p>
          <pre>lake exe cache get
lake build
lake env lean scripts/ExhaustiveAxiomAudit.lean</pre>
          <div id="audit-summary" style="font-size:13.5px;"></div>
        </div>
      </div>
    </div>
  </section>

  <!-- TAB 2: INTERACTIVE GRAPH -->
  <section id="tab-graph" class="panel">
    <div class="card">
      <div class="graph-controls">
        <strong style="font-size:14px;margin-right:6px;">Select Blueprint Graph:</strong>
        <button class="pill-btn active" data-graph="paper2">Paper 2 (JAR): Synthesis, Risk &amp; Kernel DP</button>
        <button class="pill-btn" data-graph="paper3">Paper 3 (MOR): Prepayment &amp; Certified DAGs</button>
        <button class="pill-btn" data-graph="clusters">Global 1,051-Module Cluster DAG</button>
      </div>
      <p id="graph-subtitle" style="color:var(--muted);font-size:13.5px;margin:0 0 12px;"></p>
      <div class="two-col">
        <div id="blueprint-svg-wrap">
          <svg id="blueprint-svg" class="bp-svg"></svg>
        </div>
        <div class="inspector" id="graph-inspector">
          <h3>Click any node to inspect</h3>
          <p style="color:var(--muted);font-size:13.5px;">
            Select a theorem or cluster node in the dependency graph to view its formal statement, exact Lean 4 module path, theorem/definition counts, upstream imports, and direct GitHub source link.
          </p>
        </div>
      </div>
    </div>
  </section>

  <!-- TAB 3: 1,051-MODULE EXPLORER -->
  <section id="tab-modules" class="panel">
    <div class="two-col">
      <div class="card">
        <h2>1,051 Compiled Lean 4 Library Modules</h2>
        <div class="filter-bar">
          <input id="mod-search" type="search" placeholder="Search module name, declaration, or docstring (e.g. ExecutableSupport, NoisyFiniteRisk, DAG)..." />
          <select id="mod-cluster"></select>
          <select id="mod-sort">
            <option value="theorems">Sort: Most Theorems</option>
            <option value="dependents">Sort: Most Imported</option>
            <option value="depth">Sort: Deepest in DAG</option>
            <option value="name">Sort: Alphabetical</option>
          </select>
        </div>
        <div id="mod-count" style="color:var(--muted);font-size:13px;margin-bottom:8px;"></div>
        <div style="max-height:620px;overflow-y:auto;">
          <table>
            <thead>
              <tr><th>Module</th><th>Cluster</th><th>Thms</th><th>Defs</th><th>Deps</th></tr>
            </thead>
            <tbody id="mod-tbody"></tbody>
          </table>
        </div>
      </div>
      <div class="inspector" id="mod-inspector">
        <h3>Module Inspector</h3>
        <p style="color:var(--muted);font-size:13.5px;">
          Click any row in the module table to inspect its docstring, sample declarations, internal imports, reverse dependents, and GitHub source file.
        </p>
      </div>
    </div>
  </section>

  <!-- TAB 4: 106-ASSUMPTION LEDGER -->
  <section id="tab-assumptions" class="panel">
    <div class="card">
      <h2>106 Frozen Source Assumption Classifications</h2>
      <p style="color:var(--muted);font-size:13.5px;margin-top:0;">
        Every source assumption in the frozen ledger is explicitly typed into one of five epistemological classes (zero hidden axioms, zero unexamined domain assumptions).
      </p>
      <div class="filter-bar">
        <input id="assump-search" type="search" placeholder="Search P-ID, Lean theorem, schema label, or summary..." />
        <select id="assump-class"></select>
      </div>
      <div id="assump-count" style="color:var(--muted);font-size:13px;margin-bottom:8px;"></div>
      <div style="max-height:620px;overflow-y:auto;">
        <table>
          <thead>
            <tr><th>P-ID</th><th>Assumption Class</th><th>Lean Theorem(s)</th><th>Summary</th></tr>
          </thead>
          <tbody id="assump-tbody"></tbody>
        </table>
      </div>
    </div>
  </section>

  <!-- TAB 5: REPRODUCE & CITE -->
  <section id="tab-reproduce" class="panel">
    <div class="card">
      <h2>Clean-Environment Reproduction</h2>
      <p style="color:var(--muted);font-size:14px;">
        Download the version-pinned Apache-2.0 archive from Zenodo (<a href="https://doi.org/10.5281/zenodo.24433585" target="_blank" rel="noopener">doi:10.5281/zenodo.24433585</a>; Concept DOI <a href="https://doi.org/10.5281/zenodo.24433584" target="_blank" rel="noopener">doi:10.5281/zenodo.24433584</a>) or clone the repository, then run:
      </p>
      <pre>tar -xzf lean4-pure-kernel-formalization-v1.0.0.tar.gz
cd lean4-pure-kernel-formalization-v1.0.0
lake exe cache get
lake build
lake env lean scripts/ExhaustiveAxiomAudit.lean</pre>
      <p style="color:var(--muted);font-size:13.5px;">
        <em>Note for v1.0.0 unpacks:</em> omit <code>--run</code> when invoking <code>ExhaustiveAxiomAudit.lean</code>, as the audit executes at elaboration time via <code>run_cmd</code> without a <code>main</code> entry point.
      </p>
    </div>
    <div class="card">
      <h2>BibTeX Citation (Software Archive)</h2>
      <pre>@software{qian2026lean4core,
  author       = {Qian, Degui},
  title        = {{Pure-Kernel Lean 4 Formalization of Verified Controller Synthesis,
                   Calibrated Post-Selection Risk, and Certified Decision DAGs}},
  year         = {2026},
  month        = nov,
  publisher    = {Zenodo},
  version      = {v1.0.0},
  doi          = {10.5281/zenodo.24433585},
  url          = {https://doi.org/10.5281/zenodo.24433585}
}</pre>
    </div>
  </section>
</main>

<footer>
  <div class="container">
    Pure-Kernel Lean 4 Formalization Blueprint &middot; Code licensed under Apache-2.0 &middot; Documentation &amp; Blueprint under CC BY 4.0 &middot; Built automatically from verified Lean 4 sources.
  </div>
</footer>

<script>
let DATA = null;
let MOD_BY_ID = {};
let CURRENT_GRAPH = "paper2";

const CLUSTER_COLORS = {
  "Control, Risk & Certified Decision DAGs": "#3fb950",
  "Stochastic Calculus & Continuous Bridge": "#39d0d8",
  "Theory Completion & Structural Compression": "#58a6ff",
  "Objecthood, Quotients & Cross-Track": "#bc8cff",
  "Compression Core": "#e3b341",
  "Core Foundations": "#f778ba",
  "Domain Ledger & Adapters (V3)": "#79c0ff",
  "ThirdParty Verified Bridges": "#ffa657"
};

function esc(s) {
  return String(s || "").replace(/[&<>"]/g, c => ({ "&":"&amp;", "<":"&lt;", ">":"&gt;", '"':"&quot;" }[c]));
}

function initTabs() {
  document.querySelectorAll("#nav-tabs button").forEach(btn => {
    btn.addEventListener("click", () => {
      document.querySelectorAll("#nav-tabs button").forEach(b => b.classList.remove("active"));
      document.querySelectorAll("section.panel").forEach(p => p.classList.remove("active"));
      btn.classList.add("active");
      document.getElementById("tab-" + btn.dataset.tab).classList.add("active");
    });
  });
  document.querySelectorAll(".graph-controls .pill-btn").forEach(btn => {
    btn.addEventListener("click", () => {
      document.querySelectorAll(".graph-controls .pill-btn").forEach(b => b.classList.remove("active"));
      btn.classList.add("active");
      CURRENT_GRAPH = btn.dataset.graph;
      renderGraph(CURRENT_GRAPH);
    });
  });
}

function renderOverview() {
  const a = DATA.audit;
  const kpis = [
    { val: a.total_modules.toLocaleString(), lbl: "Compiled Lean 4 Modules", cls: "" },
    { val: a.constant_defining_modules.toLocaleString(), lbl: "Audited Declaration Modules", cls: "" },
    { val: a.total_theorems.toLocaleString(), lbl: "Verified Theorems (Audit)", cls: "green" },
    { val: a.total_constants.toLocaleString(), lbl: "Kernel-Checked Constants", cls: "" },
    { val: String(a.sorryAx_users), lbl: "sorryAx Dependencies", cls: "green" },
    { val: String(a.native_decide_users), lbl: "Lean.ofReduceBool / native_decide", cls: "green" },
  ];
  document.getElementById("kpi-grid").innerHTML = kpis.map(k =>
    `<div class="kpi"><div class="val ${k.cls}">${esc(k.val)}</div><div class="lbl">${esc(k.lbl)}</div></div>`
  ).join("");

  const maxCount = Math.max(...DATA.clusters.map(c => c.modules));
  document.getElementById("cluster-bars").innerHTML = DATA.clusters.map(c => `
    <div class="bar-row">
      <div class="bar-label">${esc(c.name)}</div>
      <div class="bar-track"><div class="bar-fill" style="width:${(c.modules / maxCount * 100).toFixed(1)}%;background:${CLUSTER_COLORS[c.name] || '#58a6ff'};"></div></div>
      <div class="bar-num">${c.modules} mods</div>
    </div>
  `).join("");

  document.getElementById("audit-summary").innerHTML = `
    <p><strong>Lean Toolchain:</strong> <code>${esc(DATA.toolchain)}</code></p>
    <p><strong>Allowed Transitive Axioms:</strong> <code>{${a.allowed_axioms.join(", ")}}</code></p>
    <p><strong>Internal Import Edges:</strong> ${DATA.total_edges.toLocaleString()} verified DAG edges (max depth ${DATA.max_depth})</p>
    <p><strong>Assumption Ledger:</strong> ${DATA.assumptions.length} classified source entries (SHA-256 prefix <code>${esc(DATA.ledger_sha256.slice(0,16))}</code>)</p>
  `;
}

function renderModuleInspector(targetId, mod, extraNote) {
  const el = document.getElementById(targetId);
  if (!mod) {
    el.innerHTML = `<h3>Module Inspector</h3><p style="color:var(--muted);">Module not found.</p>`;
    return;
  }
  const importsHtml = mod.imports.length
    ? mod.imports.map(id => `<div onclick="inspectById('${esc(targetId)}','${esc(id)}')">${esc(id.replace(/^UEOT\\./, ""))}</div>`).join("")
    : `<span style="color:var(--muted);">None (root leaf)</span>`;
  const depsHtml = mod.dependents.length
    ? mod.dependents.slice(0, 60).map(id => `<div onclick="inspectById('${esc(targetId)}','${esc(id)}')">${esc(id.replace(/^UEOT\\./, ""))}</div>`).join("")
    : `<span style="color:var(--muted);">None (top-level target)</span>`;

  el.innerHTML = `
    <h3>${esc(mod.short)}</h3>
    <div style="font-family:var(--mono);font-size:11.5px;color:var(--muted);word-break:break-all;margin-bottom:8px;">${esc(mod.id)}</div>
    <div class="meta-row">
      <span class="chip">${esc(mod.cluster)}</span>
      <span class="chip">${mod.theorems} thms</span>
      <span class="chip">${mod.definitions} defs</span>
      <span class="chip">${mod.lines} lines</span>
      <span class="chip">depth ${mod.depth}</span>
    </div>
    ${extraNote ? `<p style="font-size:13.5px;background:#0a1226;border-left:3px solid var(--green);padding:8px 10px;border-radius:6px;">${esc(extraNote)}</p>` : ""}
    ${mod.doc ? `<p style="font-size:13px;color:var(--muted);">${esc(mod.doc)}</p>` : ""}
    <p style="margin:10px 0;"><a href="${esc(mod.url)}" target="_blank" rel="noopener"><strong>View Lean 4 Source on GitHub &rarr;</strong></a></p>
    <div style="font-size:12.5px;font-weight:700;margin-top:10px;">Sample Declarations (${mod.sample_decls.length})</div>
    <div class="list-box" style="color:var(--text);">${mod.sample_decls.length ? mod.sample_decls.map(d => `<span class="chip" style="display:inline-block;margin:2px;">${esc(d)}</span>`).join("") : '<span style="color:var(--muted);">Aggregator / import-only module</span>'}</div>
    <div style="font-size:12.5px;font-weight:700;margin-top:10px;">Internal Imports (${mod.imports.length})</div>
    <div class="list-box">${importsHtml}</div>
    <div style="font-size:12.5px;font-weight:700;margin-top:10px;">Imported By (${mod.dependents.length})</div>
    <div class="list-box">${depsHtml}</div>
  `;
}

window.inspectById = function(targetId, modId) {
  renderModuleInspector(targetId, MOD_BY_ID[modId], "");
};

function renderGraph(kind) {
  const svg = document.getElementById("blueprint-svg");
  const sub = document.getElementById("graph-subtitle");

  if (kind === "clusters") {
    sub.textContent = "Macro dependency architecture across all 1,051 compiled Lean 4 modules grouped into 8 thematic clusters (edge thickness reflects cross-cluster import volume).";
    const clusters = DATA.clusters;
    const W = 820, H = 480;
    svg.setAttribute("viewBox", `0 0 ${W} ${H}`);
    const coords = clusters.map((c, idx) => {
      const col = idx % 2;
      const row = Math.floor(idx / 2);
      return { ...c, x: 40 + col * 390, y: 28 + row * 112, w: 340, h: 78 };
    });
    const byName = Object.fromEntries(coords.map(c => [c.name, c]));
    let edgesSvg = "";
    DATA.cluster_edges.forEach(e => {
      const a = byName[e.from], b = byName[e.to];
      if (!a || !b) return;
      const x1 = a.x + a.w / 2, y1 = a.y + a.h / 2;
      const x2 = b.x + b.w / 2, y2 = b.y + b.h / 2;
      const sw = Math.min(4.5, 0.8 + Math.log10(e.count + 1));
      edgesSvg += `<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}" stroke="#3b4d7c" stroke-width="${sw}" stroke-opacity="0.55" />`;
    });
    const nodesSvg = coords.map(c => {
      const col = CLUSTER_COLORS[c.name] || "#58a6ff";
      return `
        <g class="bp-node" data-cluster="${esc(c.name)}">
          <rect x="${c.x}" y="${c.y}" width="${c.w}" height="${c.h}" fill="#141e3d" stroke="${col}" />
          <text x="${c.x + 14}" y="${c.y + 29}" fill="#fff" font-size="13.5" font-weight="700">${esc(c.name)}</text>
          <text x="${c.x + 14}" y="${c.y + 52}" fill="#98a6c8" font-size="12">${c.modules} modules &middot; ${c.theorems.toLocaleString()} parsed thms &middot; ${c.definitions.toLocaleString()} defs</text>
        </g>`;
    }).join("");
    svg.innerHTML = edgesSvg + nodesSvg;
    svg.querySelectorAll(".bp-node").forEach(g => {
      g.addEventListener("click", () => {
        const cname = g.dataset.cluster;
        const c = byName[cname];
        document.getElementById("graph-inspector").innerHTML = `
          <h3>${esc(c.name)}</h3>
          <div class="meta-row">
            <span class="chip">${c.modules} modules</span>
            <span class="chip">${c.theorems.toLocaleString()} parsed thms</span>
            <span class="chip">${c.definitions.toLocaleString()} defs</span>
          </div>
          <p style="font-size:13.5px;color:var(--muted);">Click below to filter the 1,051-Module Explorer to this cluster.</p>
          <button class="pill-btn" onclick="openClusterInExplorer('${esc(c.name)}')">Open Cluster in Module Explorer &rarr;</button>
        `;
      });
    });
    return;
  }

  const bp = DATA.blueprints[kind];
  sub.textContent = bp.subtitle;
  const layers = {};
  bp.nodes.forEach(n => {
    (layers[n.layer] = layers[n.layer] || []).push(n);
  });
  const layerKeys = Object.keys(layers).map(Number).sort((a,b) => a - b);
  const nodeW = 240, nodeH = 62, xGap = 28, yGap = 86;
  const maxCols = Math.max(...layerKeys.map(k => layers[k].length));
  const W = Math.max(820, maxCols * (nodeW + xGap) + 60);
  const H = Math.max(460, layerKeys.length * yGap + 60);
  svg.setAttribute("viewBox", `0 0 ${W} ${H}`);

  const pos = {};
  layerKeys.forEach((lk, rIdx) => {
    const row = layers[lk];
    const rowW = row.length * nodeW + (row.length - 1) * xGap;
    const startX = (W - rowW) / 2;
    row.forEach((n, cIdx) => {
      pos[n.key] = { ...n, x: startX + cIdx * (nodeW + xGap), y: 24 + rIdx * yGap };
    });
  });

  const defs = `<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 1 L 10 5 L 0 9 z" fill="#58a6ff" /></marker></defs>`;
  let edgesSvg = "";
  bp.nodes.forEach(n => {
    n.deps.forEach(d => {
      const src = pos[d], dst = pos[n.key];
      if (!src || !dst) return;
      const x1 = src.x + nodeW / 2, y1 = src.y + nodeH;
      const x2 = dst.x + nodeW / 2, y2 = dst.y - 2;
      const midY = (y1 + y2) / 2;
      edgesSvg += `<path d="M ${x1} ${y1} C ${x1} ${midY}, ${x2} ${midY}, ${x2} ${y2}" fill="none" stroke="#58a6ff" stroke-width="1.6" stroke-opacity="0.72" marker-end="url(#arrow)" />`;
    });
  });

  const nodesSvg = bp.nodes.map(n => {
    const p = pos[n.key];
    const mod = MOD_BY_ID[n.module];
    const col = kind === "paper2" ? "#3fb950" : "#bc8cff";
    return `
      <g class="bp-node" data-key="${esc(n.key)}">
        <rect x="${p.x}" y="${p.y}" width="${nodeW}" height="${nodeH}" fill="#141e3d" stroke="${col}" />
        <text x="${p.x + 12}" y="${p.y + 24}" fill="#fff" font-size="12.5" font-weight="700">${esc(n.label)}</text>
        <text x="${p.x + 12}" y="${p.y + 44}" fill="#98a6c8" font-size="11" font-family="monospace">${esc(mod ? mod.short : n.module)} (${mod ? mod.theorems : 0} thms)</text>
      </g>`;
  }).join("");

  svg.innerHTML = defs + edgesSvg + nodesSvg;
  svg.querySelectorAll(".bp-node").forEach(g => {
    g.addEventListener("click", () => {
      svg.querySelectorAll(".bp-node").forEach(x => x.classList.remove("selected"));
      g.classList.add("selected");
      const n = pos[g.dataset.key];
      renderModuleInspector("graph-inspector", MOD_BY_ID[n.module], `${n.label}: ${n.statement}`);
    });
  });
  if (bp.nodes.length) {
    const first = bp.nodes[0];
    renderModuleInspector("graph-inspector", MOD_BY_ID[first.module], `${first.label}: ${first.statement}`);
  }
}

window.openClusterInExplorer = function(cname) {
  document.querySelector('#nav-tabs button[data-tab="modules"]').click();
  document.getElementById("mod-cluster").value = cname;
  renderModuleTable();
};

function renderModuleTable() {
  const q = document.getElementById("mod-search").value.trim().toLowerCase();
  const cl = document.getElementById("mod-cluster").value;
  const sortKey = document.getElementById("mod-sort").value;

  let rows = DATA.modules.filter(m => {
    if (cl && m.cluster !== cl) return false;
    if (!q) return true;
    return m.id.toLowerCase().includes(q)
      || m.doc.toLowerCase().includes(q)
      || m.sample_decls.some(d => d.toLowerCase().includes(q));
  });

  if (sortKey === "theorems") rows.sort((a,b) => b.theorems - a.theorems || a.id.localeCompare(b.id));
  else if (sortKey === "dependents") rows.sort((a,b) => b.out_deg - a.out_deg || a.id.localeCompare(b.id));
  else if (sortKey === "depth") rows.sort((a,b) => b.depth - a.depth || a.id.localeCompare(b.id));
  else rows.sort((a,b) => a.id.localeCompare(b.id));

  document.getElementById("mod-count").textContent = `Showing ${Math.min(rows.length, 250)} of ${rows.length} matching modules (total ${DATA.modules.length}).`;
  document.getElementById("mod-tbody").innerHTML = rows.slice(0, 250).map(m => `
    <tr class="mod-row" onclick="inspectById('mod-inspector','${esc(m.id)}')">
      <td><strong>${esc(m.short)}</strong><br/><span style="font-family:var(--mono);font-size:11px;color:var(--muted);">${esc(m.id.replace(/^UEOT\\./, ""))}</span></td>
      <td><span class="chip">${esc(m.cluster)}</span></td>
      <td>${m.theorems}</td>
      <td>${m.definitions}</td>
      <td>${m.out_deg}</td>
    </tr>
  `).join("");
}

function renderAssumptions() {
  const q = document.getElementById("assump-search").value.trim().toLowerCase();
  const cls = document.getElementById("assump-class").value;
  const rows = DATA.assumptions.filter(a => {
    if (cls && a.assumption_class !== cls) return false;
    if (!q) return true;
    return a.pid.toLowerCase().includes(q)
      || a.summary.toLowerCase().includes(q)
      || a.lean_theorems.some(t => t.toLowerCase().includes(q))
      || a.schema_labels.some(s => s.toLowerCase().includes(q));
  });
  document.getElementById("assump-count").textContent = `Showing ${rows.length} of ${DATA.assumptions.length} classified source entries.`;
  document.getElementById("assump-tbody").innerHTML = rows.map(a => `
    <tr>
      <td><code>${esc(a.pid)}</code></td>
      <td><span class="chip">${esc(a.assumption_class)}</span></td>
      <td style="font-family:var(--mono);font-size:11.5px;">${a.lean_theorems.map(t => esc(t.replace(/^UEOT\\.V3\\./, ""))).join("<br/>")}</td>
      <td>${esc(a.summary)}</td>
    </tr>
  `).join("");
}

fetch("data/blueprint_data.json")
  .then(r => r.json())
  .then(data => {
    DATA = data;
    MOD_BY_ID = Object.fromEntries(data.modules.map(m => [m.id, m]));
    initTabs();
    renderOverview();
    renderGraph("paper2");

    const clSel = document.getElementById("mod-cluster");
    clSel.innerHTML = `<option value="">All Clusters (${data.modules.length})</option>` +
      data.clusters.map(c => `<option value="${esc(c.name)}">${esc(c.name)} (${c.modules})</option>`).join("");
    ["mod-search", "mod-cluster", "mod-sort"].forEach(id =>
      document.getElementById(id).addEventListener("input", renderModuleTable)
    );
    renderModuleTable();
    inspectById("mod-inspector", data.blueprints.paper2.nodes[3].module);

    const aSel = document.getElementById("assump-class");
    const classCounts = {};
    data.assumptions.forEach(a => classCounts[a.assumption_class] = (classCounts[a.assumption_class] || 0) + 1);
    aSel.innerHTML = `<option value="">All 5 Classes (${data.assumptions.length})</option>` +
      Object.entries(classCounts).sort((a,b) => b[1]-a[1]).map(([k,v]) => `<option value="${esc(k)}">${esc(k)} (${v})</option>`).join("");
    ["assump-search", "assump-class"].forEach(id =>
      document.getElementById(id).addEventListener("input", renderAssumptions)
    );
    renderAssumptions();
  });
</script>
</body>
</html>
"""


def main() -> None:
    modules, stem_to_mod = collect_lean_modules()
    mod_ids = {m["id"] for m in modules}
    mod_by_id = {m["id"]: m for m in modules}

    assump_raw = json.loads(ASSUMP_PATH.read_text(encoding="utf-8"))
    toolchain = (CORE_DIR / "lean-toolchain").read_text(encoding="utf-8").strip()

    # Cluster aggregations and cross-cluster edges
    cluster_stats: dict[str, dict] = defaultdict(lambda: {"modules": 0, "theorems": 0, "definitions": 0})
    cluster_edges: Counter = Counter()
    total_edges = 0
    for m in modules:
        c = cluster_stats[m["cluster"]]
        c["modules"] += 1
        c["theorems"] += m["theorems"]
        c["definitions"] += m["definitions"]
        total_edges += len(m["imports"])
        for imp in m["imports"]:
            ic = mod_by_id[imp]["cluster"]
            if ic != m["cluster"]:
                cluster_edges[(ic, m["cluster"])] += 1

    clusters_list = [
        {"name": k, **v}
        for k, v in sorted(cluster_stats.items(), key=lambda kv: (-kv[1]["modules"], kv[0]))
    ]
    cluster_edges_list = [
        {"from": a, "to": b, "count": cnt}
        for (a, b), cnt in cluster_edges.most_common()
    ]

    assumptions_list = [
        {
            "pid": v["pid"],
            "assumption_class": v["assumption_class"],
            "lean_theorems": v.get("lean_theorems", []),
            "schema_labels": v.get("schema_labels", []),
            "summary": v.get("summary", ""),
        }
        for _, v in sorted(assump_raw["entries"].items())
    ]

    blueprints = build_paper_blueprints(mod_ids, stem_to_mod)

    payload = {
        "schema": "lean4-pure-kernel-blueprint/1",
        "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "toolchain": toolchain,
        "zenodo_v1_doi": ZENODO_V1_DOI,
        "zenodo_concept_doi": ZENODO_CONCEPT_DOI,
        "ledger_sha256": assump_raw["frozen_ledger_sha256"],
        "audit": assump_raw["kernel_axiom_purity"],
        "total_edges": total_edges,
        "max_depth": max(m["depth"] for m in modules),
        "clusters": clusters_list,
        "cluster_edges": cluster_edges_list,
        "blueprints": blueprints,
        "modules": modules,
        "assumptions": assumptions_list,
    }

    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "blueprint_data.json").write_text(
        json.dumps(payload, ensure_ascii=False, separators=(",", ":")),
        encoding="utf-8",
    )
    (SITE_DIR / "index.html").write_text(render_html(), encoding="utf-8")
    (SITE_DIR / ".nojekyll").write_text("", encoding="utf-8")

    print(json.dumps({
        "status": "PASS",
        "compiled_modules": len(modules),
        "internal_import_edges": total_edges,
        "max_dag_depth": payload["max_depth"],
        "paper2_nodes_verified": len(blueprints["paper2"]["nodes"]),
        "paper3_nodes_verified": len(blueprints["paper3"]["nodes"]),
        "assumptions_loaded": len(assumptions_list),
        "site_dir": str(SITE_DIR),
    }, indent=2))


if __name__ == "__main__":
    main()
