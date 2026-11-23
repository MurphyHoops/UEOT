#!/usr/bin/env python3
"""Generate publication-grade vector PDF and 300-DPI PNG figures for
'Prepayment Thresholds, Informative Zero Receipts, and Certified Polynomial
Decision Diagrams in Partially Observed Regenerative Maintenance'.
"""
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

ROOT = Path(__file__).resolve().parent
FIG_DIR = ROOT / "figures"
FIG_DIR.mkdir(exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["Times New Roman", "DejaVu Serif", "Liberation Serif"],
    "mathtext.fontset": "cm",
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "axes.edgecolor": "#222222",
    "axes.linewidth": 0.9,
})

NAVY = "#1B365D"
SLATE = "#334E68"
TEAL = "#1F6F78"
AMBER = "#9C4221"
CRIMSON = "#8B1E3F"
INK = "#1A1A1A"
MUTED = "#555555"
LIGHT_BG = "#F7F9FB"
LIGHT_BLUE = "#E6EEF6"
LIGHT_TEAL = "#E3F2F1"
LIGHT_AMBER = "#FDF0E6"
LIGHT_CRIMSON = "#FBEAEF"


def draw_box(ax, x, y, w, h, text, facecolor="white", edgecolor=INK,
             lw=1.1, fontsize=8.4, fontweight="normal", textcolor=INK,
             linestyle="-", pad=0.014, ha="center"):
    patch = FancyBboxPatch(
        (x, y), w, h,
        boxstyle=f"round,pad={pad},rounding_size=0.018",
        facecolor=facecolor, edgecolor=edgecolor,
        linewidth=lw, linestyle=linestyle, zorder=2
    )
    ax.add_patch(patch)
    tx = x + w / 2 if ha == "center" else x + 0.02
    ax.text(
        tx, y + h / 2, text,
        ha=ha, va="center", fontsize=fontsize,
        fontweight=fontweight, color=textcolor, zorder=3, linespacing=1.25
    )
    return patch


def draw_arrow(ax, p1, p2, color=INK, lw=1.15, style="-|>", ls="-", rad=0.0, mutation=11):
    arr = FancyArrowPatch(
        p1, p2,
        connectionstyle=f"arc3,rad={rad}",
        arrowstyle=style,
        mutation_scale=mutation,
        linewidth=lw,
        linestyle=ls,
        color=color,
        zorder=4,
    )
    ax.add_patch(arr)
    return arr


# Exact rational DAG solver for Figure 3 scaling curve
ALL_ACTIONS = [
    None,
    (False, None),
    (True, None),
    (False, False),
    (False, True),
    (True, False),
    (True, True),
]
OBS_LIST = [(False, False), (False, True), (True, False), (True, True)]


def exact_dag_counts(H, B0=Q(2), tariff=Q(1), price=Q(13, 10), discount=Q(3, 4),
                     r_list=(Q(1, 4), Q(3, 4)), prior_list=(Q(1, 2), Q(1, 2)), goal=True):
    init_q = (not goal, None, False, True)
    init_st = (0, 0, 0, 0, init_q)

    def cap(a):
        return Q(0) if a is None else (Q(1) if a[1] is not None else Q(0))

    def effective(stopped, a):
        return (False, None) if (stopped or a is None) else a

    def normal_receipt(q, a):
        req_j, req_act = effective(q[2], a)
        sel = q[1] if req_j else q[0]
        if sel is None:
            return (False, False)
        post = sel if req_act is None else req_act
        return (post == goal, req_act is not None)

    def update_stat(st, a, o):
        elapsed, s, f, paid, q = st
        nr = normal_receipt(q, a)
        inf = nr[0] or nr[1]
        ns = o[0] or o[1]
        ds = 1 if (inf and ns) else 0
        df = 1 if (inf and not ns) else 0
        dp = 1 if o[1] else 0
        root, child, stopped, fresh = q
        req_j, _ = effective(stopped, a)
        bit_b = goal if o[0] else (not goal)
        new_root = root if req_j else bit_b
        if fresh:
            new_child = goal if o[0] else None
        elif req_j:
            new_child = bit_b if child is not None else None
        else:
            new_child = child
        return (elapsed + 1, s + ds, f + df, paid + dp,
                (new_root, new_child, stopped or (a is None), False))

    memo = {}

    def build(rem, st):
        key = (rem, st)
        if key in memo:
            return memo[key]
        _, s, f, paid, q = st
        wallet = max(Q(0), B0 - paid * tariff)
        if rem == 0:
            memo[key] = {"val": Q(0), "act": None, "succ": {}}
            return memo[key]
        ws = [p * (r ** s) * ((1 - r) ** f) for r, p in zip(r_list, prior_list)]
        Z = sum(ws)
        pw = [w / Z for w in ws]
        legal = [a for a in ALL_ACTIONS if tariff * cap(a) <= wallet]
        best_val = None
        best_idx = None
        all_succ = {}
        for idx, a in enumerate(legal):
            nr = normal_receipt(q, a)
            qv = Q(0)
            asucc = []
            for o in OBS_LIST:
                m = sum(w * ((r if nr == o else Q(0)) + ((1 - r) if (False, False) == o else Q(0)))
                        for r, w in zip(r_list, pw))
                if m > 0:
                    nxt = update_stat(st, a, o)
                    ch = build(rem - 1, nxt)
                    rew = (Q(1) if o[0] else Q(0)) - price * (tariff if o[1] else Q(0))
                    qv += m * (rew + discount * ch["val"])
                    asucc.append(nxt)
            all_succ[idx] = asucc
            if best_val is None or qv > best_val:
                best_val = qv
                best_idx = idx
        memo[key] = {"val": best_val, "act": best_idx, "succ": all_succ}
        return memo[key]

    build(H, init_st)
    exec_vis = set()

    def walk(rem, st):
        k = (rem, st)
        if k in exec_vis:
            return
        exec_vis.add(k)
        if rem == 0:
            return
        nd = memo[k]
        for nxt in nd["succ"][nd["act"]]:
            walk(rem - 1, nxt)

    walk(H, init_st)

    hist_memo = {}

    def count_hist(rem, st):
        k = (rem, st)
        if k in hist_memo:
            return hist_memo[k]
        if rem == 0:
            hist_memo[k] = 1
            return 1
        nd = memo[k]
        tot = sum(count_hist(rem - 1, nxt) for asucc in nd["succ"].values() for nxt in asucc)
        hist_memo[k] = tot
        return tot

    legal_h = count_hist(H, init_st)

    diff_keys = {(rem, (st[1] - st[2], st[3], st[4])) for (rem, st) in memo}
    return len(memo), len(diff_keys), len(exec_vis), legal_h


def build_fig1():
    fig = plt.figure(figsize=(12.2, 5.10))
    ax1 = fig.add_axes([0.012, 0.05, 0.495, 0.89])
    ax2 = fig.add_axes([0.575, 0.13, 0.405, 0.76])

    ax1.set_xlim(0, 1)
    ax1.set_ylim(0, 1)
    ax1.axis("off")

    ax1.text(0.01, 0.98,
             "(a) Native Genealogical Population vs. Prepaid Receipt Control",
             fontsize=10.5, fontweight="bold", color=NAVY, ha="left", va="top")

    draw_box(ax1, 0.02, 0.71, 0.94, 0.18,
             "Persistent Unknown Reliability $\\theta \\sim \\pi_0$ ($r_\\theta \\in [0,1]\\cap\\mathbb{Q}$ drawn ONCE at $t=0$)\n"
             "Native Store $\\mathcal{S}_t$: founder $\\mathrm{root}_0$, $t=0$-provisioned standby $\\mathrm{child}_1$, audit slots $j \\geq 2$,\n"
             "protected target $g$, parent–offspring lineages, clocks, and $\\mathrm{None}$ failed-birth slots",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.0)

    draw_box(ax1, 0.02, 0.40, 0.44, 0.20,
             "Two-Bit Transaction Receipt\n"
             "$o_t = (\\mathrm{birth}_t,\\ \\mathrm{paid}_t) \\in \\{0,1\\}^2$\n"
             "Hides mode, $\\theta$, labels & tail slots",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=8.0)

    draw_box(ax1, 0.52, 0.40, 0.44, 0.20,
             "Hard Sample-Path Prepayment\n"
             "Single non-replenished wallet $B_0 \\geq 0$\n"
             "$0 \\leq C_t \\leq c\\,\\mathrm{cap}(a_t) \\leq B_t$ pathwise",
             facecolor=LIGHT_CRIMSON, edgecolor=CRIMSON, fontsize=8.0)

    draw_arrow(ax1, (0.24, 0.70), (0.24, 0.615), color=AMBER, lw=1.15)
    draw_arrow(ax1, (0.74, 0.70), (0.74, 0.615), color=CRIMSON, lw=1.15)

    draw_box(ax1, 0.02, 0.08, 0.94, 0.21,
             "Seven-Action Menu $\\mathcal{A}$:  $\\mathrm{stop}$ (commits to $\\mathrm{root}_0$ idle)  or  $\\{\\mathrm{root}_0, \\mathrm{child}_1\\} \\times \\{\\mathrm{idle}, \\mathrm{write\\ }0, \\mathrm{write\\ }1\\}$\n"
             "Thm. 1: Exact native-to-compressed commutation & Bayes optimality over all real-randomized policies\n"
             "Thm. 2 ($c \\leq B_0 < 2c,\\ \\forall p \\geq 0$):  $V_{H+1}^* = \\sum_{t=0}^H d^t \\max\\{0, \\Delta_t\\}$  (single-crossing $m^*$ retries; $V^* > 0 \\Leftrightarrow p < p_0^*$)",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=7.85)

    draw_arrow(ax1, (0.24, 0.39), (0.24, 0.305), color=TEAL, lw=1.15)
    draw_arrow(ax1, (0.74, 0.39), (0.74, 0.305), color=TEAL, lw=1.15)

    # Panel (b): Two-step expected repair value vs priced fee p (Theorems 2 & 3)
    # Equal prior on r in {1/4, 3/4}, d = 1/2:
    # mu_1 = 1/2, mu_2 = 5/16, mu_3 = 7/32
    # Prior repair candidate: mu_1*(1-p) + d*mu_2 = 1/2*(1-p) + 5/32
    # Post-fault posterior after (0,0): mu'_1 = (1/2 - 5/16)/(1 - 1/2) = 3/8,
    #   mu'_2 = (5/16 - 7/32)/(1 - 1/2) = 3/16 => candidate: 3/8*(1-p) + 3/32
    # Redraw mean-kernel candidate: mu_1*(1-p) + d*mu_1^2 = 1/2*(1-p) + 1/8
    p_grid = np.linspace(1.10, 1.42, 400)
    val_prior = 0.5 * (1.0 - p_grid) + 5.0 / 32.0
    val_fault_post = 0.375 * (1.0 - p_grid) + 3.0 / 32.0
    val_redraw = 0.5 * (1.0 - p_grid) + 1.0 / 8.0

    ax2.axhline(0.0, color=INK, lw=1.0, ls="-")
    ax2.plot(p_grid, val_prior, color=NAVY, lw=2.3,
             label="Persistent prior ($p^* = 21/16 = 1.3125$)")
    ax2.plot(p_grid, val_fault_post, color=CRIMSON, lw=2.0, ls="--",
             label="Post-fault $(0,0)$ posterior ($p_{\\mathrm{fault}}^* = 5/4 = 1.25$)")
    ax2.plot(p_grid, val_redraw, color=AMBER, lw=1.7, ls="-.",
             label="Redrawn-$\\theta$ mean kernel ($p_{\\mathrm{mean}}^* = 5/4$)")

    ax2.axvspan(1.25, 1.3125, color="#FDE8E8", alpha=0.55,
                label="Prior-freeze trap $(5/4,\\ 21/16)$")
    p0 = 1.30
    ax2.axvline(p0, color=TEAL, lw=1.15, ls=":")
    ax2.scatter([p0, p0, p0], [1.0 / 160.0, -3.0 / 160.0, -1.0 / 40.0],
                color=[NAVY, CRIMSON, AMBER], s=42, zorder=6)

    ax2.annotate("$p = 13/10$:\nPrior $+1/160 > 0$\nPost-fault $-3/160 < 0$",
                 xy=(p0, 1.0 / 160.0), xytext=(1.325, 0.036),
                 arrowprops=dict(arrowstyle="->", color=NAVY, lw=1.0),
                 fontsize=7.85, color=NAVY,
                 bbox=dict(boxstyle="round,pad=0.22", facecolor="white", edgecolor="#CBD5E1"))

    ax2.set_title("(b) Persistence Premium & Post-Fault Threshold Drop ($d=1/2$)",
                  fontsize=10.0, fontweight="bold", color=NAVY, pad=9)
    ax2.set_xlabel("Priced write fee $p = \\lambda c$", fontsize=9.2)
    ax2.set_ylabel("Two-step repair candidate net value", fontsize=9.1)
    ax2.set_xlim(1.10, 1.42)
    ax2.set_ylim(-0.068, 0.115)
    ax2.grid(True, linestyle=":", alpha=0.5)
    ax2.legend(loc="lower left", fontsize=7.35, frameon=True, facecolor="white", framealpha=0.93)

    for ext in ("pdf", "png"):
        fig.savefig(FIG_DIR / f"fig1_architecture_and_thresholds.{ext}", dpi=300)
    plt.close(fig)


def build_fig2():
    fig = plt.figure(figsize=(12.2, 5.05))
    ax1 = fig.add_axes([0.012, 0.04, 0.485, 0.91])
    ax2 = fig.add_axes([0.518, 0.04, 0.470, 0.91])

    for ax in (ax1, ax2):
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        ax.axis("off")

    # Panel (a): Physical-Markov Insufficiency due to Uninformative Zero Receipt
    ax1.text(0.01, 0.98,
             "(a) Informative Zero Filter & Physical-Markov Failure (Thm. 5a)",
             fontsize=10.3, fontweight="bold", color=NAVY, ha="left", va="top")

    draw_box(ax1, 0.02, 0.62, 0.45, 0.26,
             "History $h_A$:\n"
             "$((0,\\mathrm{write}_g),(1,1)),\\ ((0,\\mathrm{idle}),(1,0)),$\n"
             "$((0,\\mathrm{idle}),(0,0))$ [healthy $\\mathrm{root}_0$]\n"
             "$(s,f)=(2,1)$,  Mass $3/32$\n"
             "Posterior $\\pi_{h_A}(1/4) = 1/4$",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=7.6)

    draw_box(ax1, 0.51, 0.62, 0.46, 0.26,
             "History $h_B$:\n"
             "$((0,\\mathrm{write}_g),(1,1)),\\ ((0,\\mathrm{idle}),(0,0)),$\n"
             "$((0,\\mathrm{idle}),(0,0))$ [damaged $\\mathrm{root}_0$: $\\Delta f=0$]\n"
             "$(s,f)=(1,1)$,  Mass $3/16$\n"
             "Posterior $\\pi_{h_B}(1/4) = 1/2$",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=7.6)

    draw_box(ax1, 0.05, 0.34, 0.88, 0.17,
             "Identical Naive Physical Markov State at $t = 3$:\n"
             "Elapsed $t = 3$,  Wallet $B_3 = 0$,  Local $q_* = (\\mathrm{root}_0 = \\neg g,\\ \\mathrm{child}_1 = g)$",
             facecolor=LIGHT_BG, edgecolor=SLATE, fontsize=8.05, linestyle="--")

    draw_arrow(ax1, (0.245, 0.61), (0.35, 0.525), color=NAVY, lw=1.15)
    draw_arrow(ax1, (0.74, 0.61), (0.63, 0.525), color=AMBER, lw=1.15)

    draw_box(ax1, 0.02, 0.06, 0.95, 0.18,
             "Divergent Future Law under Next Action $(1, \\mathrm{idle})$:\n"
             "$\\mathbb{P}(\\mathrm{birth}_3 = 1 \\mid h_A) = 5/8 \\neq 1/2 = \\mathbb{P}(\\mathrm{birth}_3 = 1 \\mid h_B)$  $\\Rightarrow (t,q,B)$ insufficient!",
             facecolor=LIGHT_CRIMSON, edgecolor=CRIMSON, fontsize=8.05, fontweight="bold")

    draw_arrow(ax1, (0.495, 0.33), (0.495, 0.255), color=CRIMSON, lw=1.2)

    # Panel (b): Genealogy-Erasing Lawful Merger & Menu-Relativity
    ax2.text(0.01, 0.98,
             "(b) Lawful History Merger vs. Menu Extension (Thm. 5b–c)",
             fontsize=10.3, fontweight="bold", color=NAVY, ha="left", va="top")

    draw_box(ax2, 0.02, 0.72, 0.45, 0.16,
             "History $m_A$:\n"
             "$((0,\\mathrm{write}_g),(1,1)),\\ ((0,\\mathrm{idle}),(0,0)),\\ ((1,\\mathrm{idle}),(1,0))$\n"
             "Native Store: $[\\neg g,\\ g,\\ \\mathrm{None},\\ g]$",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=7.55)

    draw_box(ax2, 0.51, 0.72, 0.46, 0.16,
             "History $m_B$:\n"
             "$((0,\\mathrm{write}_g),(1,1)),\\ ((1,\\mathrm{idle}),(1,0)),\\ ((0,\\mathrm{idle}),(0,0))$\n"
             "Native Store: $[\\neg g,\\ g,\\ g,\\ \\mathrm{None}]$",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=7.55)

    draw_box(ax2, 0.05, 0.44, 0.88, 0.18,
             "Shared Five-Coordinate Sufficient Summary $\\sigma = (t, q, s, f, k) = (3, q_*, 2, 1, 1)$\n"
             "Identical joint law over $(o,\\ \\sigma',\\ \\mathrm{birth},\\ C,\\ B')$ for ALL legal actions in $\\{\\mathrm{root}_0, \\mathrm{child}_1\\}$ menu\n"
             "Merged into a SINGLE certified DAG node (e.g. node 1294 in $H=8,\\ B_0=2$ graph)",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=7.90)

    draw_arrow(ax2, (0.245, 0.71), (0.35, 0.63), color=TEAL, lw=1.15)
    draw_arrow(ax2, (0.74, 0.71), (0.63, 0.63), color=TEAL, lw=1.15)

    draw_box(ax2, 0.02, 0.06, 0.45, 0.25,
             "Native World Preservation:\n"
             "Distinct parent–child lineages,\n"
             "slot 2 vs. slot 3 identities, and\n"
             "past discounted birth timestamps\n"
             "remain intact in native Store",
             facecolor=LIGHT_BG, edgecolor=SLATE, fontsize=7.85)

    draw_box(ax2, 0.51, 0.06, 0.46, 0.25,
             "Menu-Relativity Boundary:\n"
             "Adding $\\mathrm{idle\\ address\\ 2}$ breaks merge!\n"
             "Slot 2 in $m_A$ is $\\mathrm{None}$ (birth prob. $0$)\n"
             "Slot 2 in $m_B$ is $g$ (birth prob. $r_\\theta > 0$)",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=7.85)

    draw_arrow(ax2, (0.28, 0.43), (0.245, 0.325), color=SLATE, lw=1.15)
    draw_arrow(ax2, (0.70, 0.43), (0.74, 0.325), color=AMBER, lw=1.15)

    for ext in ("pdf", "png"):
        fig.savefig(FIG_DIR / f"fig2_informative_counts_and_sufficiency.{ext}", dpi=300)
    plt.close(fig)


def build_fig3():
    from math import comb
    fig = plt.figure(figsize=(12.2, 5.15))
    ax1 = fig.add_axes([0.065, 0.13, 0.430, 0.76])
    ax2 = fig.add_axes([0.540, 0.05, 0.445, 0.89])

    # Panel (a): Exact scaling from H = 1 to H = 8 at B0 = 2
    hs = np.arange(1, 9)
    raw_tree = np.array([28.0 ** int(h) for h in hs])
    quartic_bound = np.array([24.0 * ((int(h) + 1) ** 4) for h in hs])
    cubic_bound = np.array([
        1.0 + 12.0 * sum(comb(t + 2, 2) * (min(2, t) + 1) for t in range(1, int(h) + 1))
        for h in hs
    ])
    cert_counts, diff_counts, exec_counts, legal_hists = [], [], [], []
    for h in hs:
        cn, dn, en, lh = exact_dag_counts(int(h))
        cert_counts.append(cn)
        diff_counts.append(dn)
        exec_counts.append(en)
        legal_hists.append(lh)
    cert_counts = np.array(cert_counts, dtype=float)
    diff_counts = np.array(diff_counts, dtype=float)
    exec_counts = np.array(exec_counts, dtype=float)
    legal_hists = np.array(legal_hists, dtype=float)

    ax1.semilogy(hs, raw_tree, color="#888888", lw=1.4, ls=":", marker=".", markersize=4.2,
                 label="Syntactic strings $28^H$ ($3.78\\times 10^{11}$)")
    ax1.semilogy(hs, legal_hists, color=CRIMSON, lw=2.0, ls="-.", marker="s", markersize=4.5,
                 label="Legal pos.-prob. histories ($2.38\\times 10^7$)")
    ax1.semilogy(hs, quartic_bound, color=AMBER, lw=1.7, ls="--", marker="^", markersize=4.6,
                 label="Verifier ceiling $24(H+1)^4$ ($157,464$)")
    ax1.semilogy(hs, cubic_bound, color="#6B46C1", lw=1.75, ls="--", marker="v", markersize=4.5,
                 label="Reachable cubic bound $N_{\\mathrm{reach}}$ ($5,869$)")
    ax1.semilogy(hs, cert_counts, color=NAVY, lw=2.25, marker="o", markersize=5.0,
                 label="Certified $(s,f)$ DAG ($1,661$)")
    ax1.semilogy(hs, diff_counts, color="#2B6CB0", lw=1.8, ls="-", marker="x", markersize=5.0,
                 label="Log-odds $(s-f)$ DAG ($1,020$)")
    ax1.semilogy(hs, exec_counts, color=TEAL, lw=2.05, marker="D", markersize=4.4,
                 label="Optimal execution DAG ($151$)")

    ax1.set_title("(a) Feasible History Tree vs. Polynomial DAGs ($B_0 = 2$)",
                  fontsize=10.0, fontweight="bold", color=NAVY, pad=9)
    ax1.set_xlabel("Planning horizon $H$", fontsize=9.2)
    ax1.set_ylabel("Histories / DAG nodes ($\\log_{10}$ scale)", fontsize=9.1)
    ax1.set_xticks(hs)
    ax1.set_ylim(1, 2e12)
    ax1.grid(True, which="both", linestyle=":", alpha=0.5)
    ax1.legend(loc="upper left", fontsize=6.85, frameon=True, facecolor="white", framealpha=0.94, labelspacing=0.28)

    # Panel (b): Certifying Algorithm & All-Action Soundness Architecture
    ax2.set_xlim(0, 1)
    ax2.set_ylim(0, 1)
    ax2.axis("off")

    ax2.text(0.01, 0.98,
             "(b) Certifying DAG Synthesis & All-Action Soundness (Thm. 6)",
             fontsize=10.2, fontweight="bold", color=NAVY, ha="left", va="top")

    draw_box(ax2, 0.03, 0.73, 0.93, 0.16,
             "Canonical Memoized Generator ($\\mathrm{generate}$)\n"
             "Hash-consing on $(n,\\ \\sigma = (t,q,s,f,k))$ in decreasing $n = H - t$\n"
             "Tight $\\Theta(1+H^3)$ for $M \\geq 1$:  $1 + \\binom{H+1}{3} \\leq |G_{\\mathrm{reach}}| \\leq N_{\\mathrm{reach}}(H,M)$,  $\\leq 14|G_{\\mathrm{reach}}|$ edges",
             facecolor=LIGHT_BG, edgecolor=SLATE, fontsize=7.80)

    draw_box(ax2, 0.03, 0.42, 0.93, 0.21,
             "Two-Layer Executable Verifier ($\\mathrm{accept} = \\mathrm{certify} + \\mathrm{boundCheck}$)\n"
             "1. $\\mathrm{certify}$: Unique keys, root binding & ALL-action rational $Q$-value check\n"
             "2. $\\mathrm{boundCheck}(H)$: $n_i + t_i = H,\\ s_i + f_i \\leq t_i,\\ k_i \\leq t_i \\Rightarrow |G| \\leq 24(H+1)^4$\n"
             "3. Returns $\\mathrm{some\\ res}$ ($\\mathrm{Option\\ Result}$) iff both stages pass",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=7.85)

    draw_arrow(ax2, (0.495, 0.72), (0.495, 0.645), color=NAVY, lw=1.2)

    draw_box(ax2, 0.03, 0.09, 0.44, 0.23,
             "Accepted Artifact ($\\mathrm{some\\ res}$)\n"
             "Exact native value $J_H(G) = V_H^*$\n"
             "Dominates all real-randomized\n"
             "full-history policies; pathwise prepaid",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=7.9)

    draw_box(ax2, 0.52, 0.09, 0.44, 0.23,
             "Dual Negative Rejection Probes\n"
             "$\\mathrm{certify}$ rejects omitted alt. edges;\n"
             "$\\mathrm{boundCheck}$ rejects unbound rows\n"
             "(e.g., $25 > 24$ terminal rows at $H=0$)",
             facecolor=LIGHT_CRIMSON, edgecolor=CRIMSON, fontsize=7.85)

    draw_arrow(ax2, (0.28, 0.41), (0.25, 0.335), color=TEAL, lw=1.2)
    draw_arrow(ax2, (0.71, 0.41), (0.74, 0.335), color=CRIMSON, lw=1.2)

    for ext in ("pdf", "png"):
        fig.savefig(FIG_DIR / f"fig3_dag_compression_and_scaling.{ext}", dpi=300)
    plt.close(fig)


if __name__ == "__main__":
    build_fig1()
    build_fig2()
    build_fig3()
    print("Generated figures in", FIG_DIR)
