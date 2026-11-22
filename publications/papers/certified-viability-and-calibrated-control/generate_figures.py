#!/usr/bin/env python3
"""Generate publication-grade vector PDF and 300-DPI PNG figures for
'Pure-Kernel Verified Controller Synthesis, Fixed-Sample Impossibility,
and Calibrated Post-Selection Risk under Partial Observation'.
"""
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
             lw=1.1, fontsize=8.5, fontweight="normal", textcolor=INK,
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
        fontweight=fontweight, color=textcolor, zorder=3, linespacing=1.26
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


def build_fig1():
    fig = plt.figure(figsize=(12.2, 5.15))
    ax1 = fig.add_axes([0.012, 0.05, 0.505, 0.89])
    ax2 = fig.add_axes([0.575, 0.13, 0.405, 0.76])

    ax1.set_xlim(0, 1)
    ax1.set_ylim(0, 1)
    ax1.axis("off")

    ax1.text(0.01, 0.98,
             "(a) Pure-Kernel Synthesis & Candidate-Free Calibration Architecture",
             fontsize=10.6, fontweight="bold", color=NAVY, ha="left", va="top")

    draw_box(ax1, 0.02, 0.72, 0.43, 0.17,
             "Unknown Kernel $P(x,a)$ & Sample $\\omega \\sim \\mu_N$\n"
             "Empirical Rows $\\widehat{P}_{x,a}$ ($N$ i.i.d. draws / pair)\n"
             "Thm. 4: Zero-leakage uncertifiable ($\\mathbb{P}_0 \\leq \\alpha$)",
             facecolor=LIGHT_CRIMSON, edgecolor=CRIMSON, fontsize=8.1)

    draw_box(ax1, 0.52, 0.72, 0.45, 0.17,
             "Single Row-Calibration Event $G_u$ (Thm. 5)\n"
             "$\\forall (x,a),\\ d_{\\mathrm{TV}}(P_{x,a}, \\widehat{P}_{x,a}) \\leq u$\n"
             "$\\alpha_N(u) = \\min\\{1,\\ |X||A|2^{|X|+1} e^{-2Nu^2}\\}$",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.1)

    draw_arrow(ax1, (0.46, 0.805), (0.51, 0.805), color=NAVY, lw=1.2)

    draw_box(ax1, 0.02, 0.42, 0.95, 0.19,
             "Markov Pushforward Contractivity Across Arbitrary Candidate Abstractions $q_0, \\dots, q_{m-1}$\n"
             "On event $G_u$:  $|\\delta_{q_j}(P) - \\widehat{\\delta}_{q_j}(\\omega)| \\leq 2u$  simultaneously for all $j$  (zero $m$-union penalty)\n"
             "Computable Rational Selector $s(\\omega)$ picks first candidate passing $\\widehat{B}_T \\leq \\beta$ (NoisyFiniteRiskOracle)",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=8.05)

    draw_arrow(ax1, (0.745, 0.71), (0.745, 0.625), color=AMBER, lw=1.2)

    draw_box(ax1, 0.02, 0.10, 0.45, 0.21,
             "Executable Finite-Memory Synthesizer (Thm. 3)\n"
             "$\\mathrm{synthesize} : \\mathrm{Option\\ (Program\\ }X\\ Y\\ A\\mathrm{)}$\n"
             "Greatest Winning Fixed Point $\\mathcal{W}_*$ ($\\leq 2^{|X|}-1$ steps)\n"
             "Thms. 1–2: Trace-Support & König Compactness",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=7.95)

    draw_box(ax1, 0.53, 0.10, 0.44, 0.21,
             "End-to-End Measure & Risk Guarantees\n"
             "Safety: $\\mathbf{1}_{\\widetilde{K}}^\\top Q_K^T \\widetilde{\\mu}_0 \\downarrow \\mathbb{P}(\\forall n \\in \\mathbb{N}, X_n \\in K)$\n"
             "Post-Selection: $\\mathbb{P}_J(\\mathrm{accept} \\wedge E) \\leq \\alpha_N + (1-\\alpha_N)\\beta$\n"
             "Kernel Axioms: $\\{\\mathrm{propext},\\ \\mathrm{Classical.choice},\\ \\mathrm{Quot.sound}\\}$",
             facecolor=LIGHT_BG, edgecolor=SLATE, fontsize=7.75)

    draw_arrow(ax1, (0.245, 0.41), (0.245, 0.325), color=TEAL, lw=1.2)
    draw_arrow(ax1, (0.75, 0.41), (0.75, 0.325), color=SLATE, lw=1.2)
    draw_arrow(ax1, (0.48, 0.205), (0.52, 0.205), color=TEAL, lw=1.2)

    # Panel (b): Candidate-Free Joint Risk Envelope vs Naive m-Candidate Union Bounds
    N_grid = np.linspace(500, 4500, 400)
    beta = 0.70
    alpha_1 = np.minimum(1.0, 48.0 * np.exp(-N_grid / 200.0))
    joint_cand_free = np.minimum(1.0, alpha_1 + (1.0 - alpha_1) * beta)
    a20 = np.minimum(1.0, 20.0 * 48.0 * np.exp(-N_grid / 200.0))
    a200 = np.minimum(1.0, 200.0 * 48.0 * np.exp(-N_grid / 200.0))
    joint_union_20 = np.minimum(1.0, a20 + (1.0 - a20) * beta)
    joint_union_200 = np.minimum(1.0, a200 + (1.0 - a200) * beta)

    ax2.plot(N_grid, joint_cand_free, color=NAVY, lw=2.3,
             label="Candidate-free $\\alpha_N + (1-\\alpha_N)\\beta$ (any $m$)")
    ax2.plot(N_grid, joint_union_20, color=AMBER, lw=1.7, ls="--",
             label="Naive $m$-union bound ($m = 20$)")
    ax2.plot(N_grid, joint_union_200, color=CRIMSON, lw=1.7, ls="-.",
             label="Naive $m$-union bound ($m = 200$)")
    ax2.axhline(beta, color=TEAL, lw=1.15, ls=":", label="Budget $\\beta = 7/10$ ($9/16 < 7/10 < 49/64$)")

    n_mark = 4096.0
    a_mark = 48.0 * np.exp(-512.0 / 25.0)
    j_mark = a_mark + (1.0 - a_mark) * beta
    ax2.scatter([n_mark], [j_mark], color=NAVY, s=44, zorder=5)
    ax2.annotate("$N=4096$: $\\alpha_{4096} = 48 e^{-512/25}$\n$\\approx 6.12\\times 10^{-8} < 1$",
                 xy=(n_mark, j_mark), xytext=(2480, 0.57),
                 arrowprops=dict(arrowstyle="->", color=NAVY, lw=1.0),
                 fontsize=8.0, color=NAVY)

    ax2.set_title("(b) Witness Risk Envelope ($|X|=3, |A|=1, u=1/20, \\beta=7/10$)",
                  fontsize=10.1, fontweight="bold", color=NAVY, pad=9)
    ax2.set_xlabel("Samples per state–action pair $N$", fontsize=9.2)
    ax2.set_ylabel("Certified joint risk bound $\\mathbb{P}_J(\\mathrm{accept} \\wedge E)$", fontsize=9.0)
    ax2.set_xlim(500, 4500)
    ax2.set_ylim(0.52, 1.03)
    ax2.grid(True, linestyle=":", alpha=0.5)
    ax2.legend(loc="lower left", fontsize=7.6, frameon=True, facecolor="white", framealpha=0.92)

    for ext in ("pdf", "png"):
        fig.savefig(FIG_DIR / f"fig1_synthesis_and_calibration.{ext}", dpi=300)
    plt.close(fig)


def build_fig2():
    fig = plt.figure(figsize=(12.2, 5.05))
    ax1 = fig.add_axes([0.012, 0.05, 0.495, 0.89])
    ax2 = fig.add_axes([0.575, 0.13, 0.405, 0.76])

    ax1.set_xlim(0, 1)
    ax1.set_ylim(0, 1)
    ax1.axis("off")

    ax1.text(0.01, 0.98,
             "(a) Three-Step Prepaid Fault-Mechanism Divergence ($\\{S, G\\}$, Thm. 7)",
             fontsize=10.5, fontweight="bold", color=NAVY, ha="left", va="top")

    draw_box(ax1, 0.03, 0.76, 0.92, 0.13,
             "$t = 0$:  Initial damaged $\\mathrm{root}_0$ ($\\neg g$), wallet $B = 2,\\ c = 1$.  Action $a_0 = \\mathrm{write}\\ g\\ \\mathrm{to}\\ \\mathrm{root}_0$",
             facecolor=LIGHT_BG, edgecolor=SLATE, fontsize=8.15)

    draw_box(ax1, 0.03, 0.53, 0.56, 0.145,
             "$o_0 = (1,1)$ (prob. $1/2$, wallet $1$)\n"
             "$\\mathrm{root}_0 = g$, spawned backup $\\mathrm{child}_1 = g$\n"
             "$t = 1$: $a_1 = \\mathrm{idle}\\ \\mathrm{root}_0$",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.0)

    draw_box(ax1, 0.64, 0.53, 0.31, 0.145,
             "$o_0 = (0,0)$ (prob. $1/2$)\n"
             "Reduces to $H=2, B=2$\n"
             "Common value $13/16$",
             facecolor="white", edgecolor=MUTED, fontsize=8.0, linestyle="--")

    draw_arrow(ax1, (0.31, 0.742), (0.31, 0.692), color=NAVY, lw=1.15)
    draw_arrow(ax1, (0.79, 0.742), (0.79, 0.692), color=MUTED, lw=1.05, ls="--")

    # Shared ambiguous observation node cleanly placed between rows
    draw_box(ax1, 0.16, 0.375, 0.66, 0.072,
             "Ambiguous prefix $o_1 = (0,0)$ (prob. $1/4$): identical receipt under $S$ and $G$",
             facecolor=LIGHT_CRIMSON, edgecolor=CRIMSON, fontsize=7.85, fontweight="bold")
    draw_arrow(ax1, (0.31, 0.512), (0.38, 0.465), color=CRIMSON, lw=1.1)

    draw_box(ax1, 0.03, 0.06, 0.43, 0.235,
             "Serial Local Mechanism $S$:\n"
             "$\\mathrm{root}_0 = \\neg g$,  $\\mathrm{child}_1$ remains intact ($g$)\n"
             "$\\pi_S$: idle $\\mathrm{child}_1 \\Rightarrow$ mean $1/2$\n"
             "($V_S^* = 41/32$,  $J_G(\\pi_S) = 37/32$)",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=7.95)

    draw_box(ax1, 0.51, 0.06, 0.44, 0.235,
             "Global Correlated Mechanism $G$:\n"
             "$\\mathrm{root}_0 = \\neg g$,  $\\mathrm{child}_1$ corrupted ($\\neg g$)\n"
             "$\\pi_G$: write $g$ to $\\mathrm{root}_0 \\Rightarrow$ mean $3/8$\n"
             "($V_G^* = 40/32 = 5/4$;  $\\Delta_{3,B} = r^2(1-r) = 1/8$)",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=7.95)

    draw_arrow(ax1, (0.33, 0.356), (0.245, 0.313), color=TEAL, lw=1.2)
    draw_arrow(ax1, (0.65, 0.356), (0.72, 0.313), color=AMBER, lw=1.2)

    # Panel (b): Minimax Regret Saddle Geometry
    p = np.linspace(0, 1, 500)
    r_S = (1.0 - p) * (1.0 / 32.0)
    r_G = p * (3.0 / 32.0)
    r_max = np.maximum(r_S, r_G)

    ax2.plot(p, r_S, color=TEAL, lw=1.7, ls="--", label="$R_S(\\rho_p) = (1-p)/32$")
    ax2.plot(p, r_G, color=AMBER, lw=1.7, ls="-.", label="$R_G(\\rho_p) = 3p/32$")
    ax2.plot(p, r_max, color=NAVY, lw=2.4, label="Worst-case regret $\\max\\{R_S, R_G\\}$")

    ax2.axhline(1.0 / 32.0, color=CRIMSON, lw=1.25, ls=":",
                label="Deterministic $\\frac{1}{32}\\mathbb{Z}$ barrier ($1/32 = 4/128$)")
    ax2.scatter([0.0], [1.0 / 32.0], color=CRIMSON, s=46, zorder=5)
    ax2.scatter([0.25], [3.0 / 128.0], color=NAVY, s=54, zorder=6)

    ax2.annotate("Deterministic optimum $\\pi_G$\n$R(\\pi_G) = 1/32$",
                 xy=(0.0, 1.0 / 32.0), xytext=(0.05, 0.048),
                 arrowprops=dict(arrowstyle="->", color=CRIMSON, lw=1.0),
                 fontsize=8.0, color=CRIMSON)

    ax2.annotate("Randomized saddle $\\rho = \\frac{1}{4}\\pi_S + \\frac{3}{4}\\pi_G$\n"
                 "$R^* = L(3/4, 1/4) = 3/128$\n"
                 "($\\mathrm{csolveInt}$: $[41, 40, 160, 37]$)",
                 xy=(0.25, 3.0 / 128.0), xytext=(0.56, 0.032),
                 arrowprops=dict(arrowstyle="->", color=NAVY, lw=1.05),
                 fontsize=7.9, color=NAVY,
                 bbox=dict(boxstyle="round,pad=0.25", facecolor="white", edgecolor="#CBD5E1", alpha=0.95))

    ax2.set_title("(b) Exact Minimax Regret Saddle ($R^* = 3/128 < 1/32$)",
                  fontsize=10.4, fontweight="bold", color=NAVY, pad=9)
    ax2.set_xlabel("Mixing weight $p$ on $\\pi_S$ in $\\rho_p = p\\pi_S + (1-p)\\pi_G$", fontsize=9.1)
    ax2.set_ylabel("Worst-case regret over $\\{S, G\\}$", fontsize=9.1)
    ax2.set_xlim(-0.02, 1.02)
    ax2.set_ylim(0.0, 0.098)
    ax2.set_yticks([0.0, 3.0 / 128.0, 1.0 / 32.0, 2.0 / 32.0, 3.0 / 32.0])
    ax2.set_yticklabels(["$0$", "$3/128$", "$1/32$", "$2/32$", "$3/32$"])
    ax2.grid(True, linestyle=":", alpha=0.5)
    ax2.legend(loc="upper left", fontsize=7.6, frameon=True, facecolor="white", framealpha=0.92)

    for ext in ("pdf", "png"):
        fig.savefig(FIG_DIR / f"fig2_fault_regret_and_kernel_dp.{ext}", dpi=300)
    plt.close(fig)


if __name__ == "__main__":
    build_fig1()
    build_fig2()
    print("Generated figures in", FIG_DIR)
