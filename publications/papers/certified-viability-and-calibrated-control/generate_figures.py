#!/usr/bin/env python3
"""Generate publication-grade vector PDF and 300-DPI PNG figures for
'Pure-Kernel Verified Controller Synthesis, Fixed-Sample Impossibility,
and Calibrated Post-Selection Risk under Partial Observation'.
"""
from __future__ import annotations

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
    "axes.linewidth": 0.95,
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
             lw=1.15, fontsize=8.4, fontweight="normal", textcolor=INK,
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
        fontweight=fontweight, color=textcolor, zorder=3, linespacing=1.22
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
    fig = plt.figure(figsize=(9.6, 4.55))
    ax1 = fig.add_axes([0.01, 0.03, 0.515, 0.92])
    ax2 = fig.add_axes([0.585, 0.13, 0.398, 0.77])

    ax1.set_xlim(0, 1)
    ax1.set_ylim(0, 1)
    ax1.axis("off")

    ax1.text(0.01, 0.985,
             "(a) Structural-Support Synthesis & Calibrated Risk Pipeline",
             fontsize=10.2, fontweight="bold", color=NAVY, ha="left", va="top")

    # Separate Structural Support Prior (left) from Per-Row Sample Experiment (right)
    draw_box(ax1, 0.02, 0.73, 0.44, 0.175,
             "Prior Structural Support $(I_0, R, C)$\n"
             "$I_0 = \\mathrm{supp}(p_0),\\; R = \\mathrm{supp}(P)$\n"
             "(Thm. 4: not from fixed-$N$ rollouts)",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=8.05)

    draw_box(ax1, 0.51, 0.73, 0.465, 0.175,
             "Per-Row Samples $\\omega_{x,a,k} \\sim P(x,a)$\n"
             "Good Event $G_u$: $d_{\\mathrm{TV}}(P_{x,a}, \\widehat{P}_{x,a}) \\leq u$\n"
             "$\\alpha_N = \\min\\{1, |X||A|2^{|X|+1}e^{-2Nu^2}\\}$",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.05)

    draw_box(ax1, 0.02, 0.42, 0.43, 0.21,
             "Executable Synthesizer (Thm. 3)\n"
             "$\\mathrm{synthesize} : \\mathrm{Option\\ (Program)}$\n"
             "Winning $\\mathcal{W}_*$ ($\\leq 2^{|X|}-1$ rounds)\n"
             "All-$\\omega$ safety $\\mathbb{P}_{\\mathrm{prog}}(\\forall n, X_n \\in K)=1$",
             facecolor="white", edgecolor=TEAL, fontsize=7.95)

    draw_box(ax1, 0.52, 0.42, 0.455, 0.21,
             "Candidate-Free Risk Gate (Thm. 5)\n"
             "Fiber discrepancy $|\\delta_{q_j} - \\widehat{\\delta}_{q_j}| \\leq 2u$\n"
             "Zero $m$-union penalty across $q_0..q_{m-1}$\n"
             "Checks coarse envelope $\\widehat{B}_T \\leq \\beta$",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=8.0)

    draw_arrow(ax1, (0.235, 0.715), (0.235, 0.645), color=TEAL, lw=1.2)
    draw_arrow(ax1, (0.745, 0.715), (0.745, 0.645), color=NAVY, lw=1.2)
    draw_arrow(ax1, (0.465, 0.525), (0.505, 0.525), color=TEAL, lw=1.2)

    draw_box(ax1, 0.02, 0.05, 0.955, 0.27,
             "Decoupled Perpetual Safety & Finite-Horizon Risk Guarantees\n"
             "1. Sample-free perpetual safety: $\\mathbb{P}_{\\mathrm{prog}_j}(\\forall n \\in \\mathbb{N}, X_n \\in K) = 1$ ($\\forall \\omega$)\n"
             "2. On $G_u$: accepted $K_j(E) \\leq \\beta$;  uncond. $\\mathbb{P}_J(\\mathrm{accept} \\wedge E) \\leq \\alpha_N + (1-\\alpha_N)\\beta$\n"
             "3. Macro $\\widehat{K}_{q_j}$ (20–62 paths) vs. micro $\\widehat{P}$ (8,248 paths): 72×–147× faster",
             facecolor=LIGHT_BG, edgecolor=SLATE, fontsize=7.95)

    draw_arrow(ax1, (0.24, 0.405), (0.32, 0.335), color=TEAL, lw=1.2)
    draw_arrow(ax1, (0.742, 0.405), (0.66, 0.335), color=AMBER, lw=1.2)

    # Panel (b): Exact Binomial Operating Curve P_theta(selectedAccepts) vs Progress Rate theta
    import math as _math

    def binom_accept_prob_float(n_samp: int, th_val: float, k_lo: int, k_hi: int) -> float:
        if th_val <= 0.0:
            return 0.0
        if th_val >= 1.0:
            return 1.0 if k_hi == n_samp else 0.0
        lp = _math.log(th_val)
        lq = _math.log(1.0 - th_val)
        lg_n = _math.lgamma(n_samp + 1)
        logs = [
            lg_n - _math.lgamma(k + 1) - _math.lgamma(n_samp - k + 1) + k * lp + (n_samp - k) * lq
            for k in range(k_lo, k_hi + 1)
        ]
        m = max(logs)
        return _math.exp(m) * sum(_math.exp(v - m) for v in logs)

    theta_grid = np.linspace(0.11, 0.29, 181)
    curve_4096 = np.array([binom_accept_prob_float(4096, float(t), 924, 3174) for t in theta_grid])
    curve_16384 = np.array([binom_accept_prob_float(16384, float(t), 3175, 13516) for t in theta_grid])

    th_crit = 1.0 - np.sqrt(0.70)     # ~0.16334
    th_pad_05 = 1.0 - np.sqrt(0.60)   # ~0.22540
    th_pad_025 = 1.0 - np.sqrt(0.65)  # ~0.19377

    ax2.axvspan(0.11, th_crit, color="#FCE8EC", alpha=0.65, zorder=0, label="Invalid ($(1{-}\\theta)^2 > 0.7$)")
    ax2.axvspan(th_crit, th_pad_05, color="#FDF0E6", alpha=0.70, zorder=0, label="$2u$ abstention band ($u{=}1/20$)")
    ax2.axvline(th_crit, color=CRIMSON, lw=1.2, ls=":")
    ax2.axvline(th_pad_05, color=AMBER, lw=1.1, ls=":")

    ax2.plot(theta_grid, curve_4096, color=NAVY, lw=2.3,
             label="$N{=}4096, u{=}1/20$ ($\\alpha{\\approx}6.1{\\times}10^{-8}$)")
    ax2.plot(theta_grid, curve_16384, color=TEAL, lw=1.85, ls="--",
             label="$N{=}16384, u{=}1/40$ (same $\\alpha$)")

    pts = [
        (0.125, 0.0, "$\\theta{=}1/8$\n$5.97{\\times}10^{-71}$", (0.113, 0.23), CRIMSON),
        (0.20, binom_accept_prob_float(4096, 0.20, 924, 3174), "$\\theta{=}1/5$: $0.003\\%$\n($97.8\\%$ at $u{=}1/40$)", (0.130, 0.56), AMBER),
        (0.25, binom_accept_prob_float(4096, 0.25, 924, 3174), "$\\theta{=}1/4$\n$99.988\\%$", (0.236, 0.74), NAVY),
    ]
    for tx, ty, lbl, xy_txt, col in pts:
        ax2.scatter([tx], [ty], color=col, s=42, zorder=6)
        ax2.annotate(
            lbl, xy=(tx, ty), xytext=xy_txt,
            arrowprops=dict(arrowstyle="->", color=col, lw=0.95),
            fontsize=7.65, color=col, fontweight="bold",
            bbox=dict(boxstyle="round,pad=0.17", facecolor="white", edgecolor="#CBD5E1", alpha=0.94),
            zorder=7,
        )

    ax2.set_title("(b) Acceptance Operating Curve vs. True Progress $\\theta$",
                  fontsize=9.9, fontweight="bold", color=NAVY, pad=9)
    ax2.set_xlabel("True progress probability $\\theta$ (valid iff $\\theta \\geq 0.1633$)", fontsize=8.9)
    ax2.set_ylabel("Acceptance probability $\\mathbb{P}_{\\theta}(\\mathrm{selectedAccepts})$", fontsize=8.9)
    ax2.set_xlim(0.11, 0.29)
    ax2.set_ylim(-0.04, 1.06)
    ax2.grid(True, linestyle=":", alpha=0.5)
    ax2.legend(loc="upper left", fontsize=7.35, frameon=True, facecolor="white", framealpha=0.95)

    for ext in ("pdf", "png"):
        fig.savefig(FIG_DIR / f"fig1_synthesis_and_calibration.{ext}", dpi=300, bbox_inches="tight")
    plt.close(fig)


def build_fig2():
    fig = plt.figure(figsize=(9.6, 4.45))
    ax1 = fig.add_axes([0.01, 0.04, 0.505, 0.90])
    ax2 = fig.add_axes([0.585, 0.13, 0.398, 0.77])

    ax1.set_xlim(0, 1)
    ax1.set_ylim(0, 1)
    ax1.axis("off")

    ax1.text(0.01, 0.985,
             "(a) Three-Step Prepaid Fault Divergence ($\\{S, G\\}$, Thm. 7)",
             fontsize=10.2, fontweight="bold", color=NAVY, ha="left", va="top")

    draw_box(ax1, 0.02, 0.765, 0.95, 0.13,
             "$t = 0$: Damaged $\\mathrm{root}_0$ ($\\neg g$), wallet $B = 2, c = 1$.  $a_0 = \\mathrm{write}\\ g\\ \\mathrm{to}\\ \\mathrm{root}_0$",
             facecolor=LIGHT_BG, edgecolor=SLATE, fontsize=8.2)

    draw_box(ax1, 0.02, 0.53, 0.58, 0.15,
             "$o_0 = (1,1)$ (prob. $1/2$, wallet $1$)\n"
             "$\\mathrm{root}_0 = g$, backup $\\mathrm{child}_1 = g$\n"
             "$t = 1$: $a_1 = \\mathrm{idle}\\ \\mathrm{root}_0$",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.15)

    draw_box(ax1, 0.64, 0.53, 0.33, 0.15,
             "$o_0 = (0,0)$ (prob. $1/2$)\n"
             "Reduces to $H=2, B=2$\n"
             "Common value $13/16$",
             facecolor="white", edgecolor=MUTED, fontsize=8.1, linestyle="--")

    draw_arrow(ax1, (0.31, 0.75), (0.31, 0.695), color=NAVY, lw=1.15)
    draw_arrow(ax1, (0.80, 0.75), (0.80, 0.695), color=MUTED, lw=1.05, ls="--")

    draw_box(ax1, 0.12, 0.365, 0.74, 0.08,
             "Ambiguous prefix $o_1 = (0,0)$ (prob. $1/4$): identical receipt under $S$ and $G$",
             facecolor=LIGHT_CRIMSON, edgecolor=CRIMSON, fontsize=8.05, fontweight="bold")
    draw_arrow(ax1, (0.31, 0.515), (0.39, 0.46), color=CRIMSON, lw=1.1)

    draw_box(ax1, 0.02, 0.04, 0.45, 0.245,
             "Serial Local Fault $S$:\n"
             "$\\mathrm{root}_0 = \\neg g,\\; \\mathrm{child}_1 = g$\n"
             "$\\pi_S$: idle $\\mathrm{child}_1 \\Rightarrow$ mean $1/2$\n"
             "($V_S^* = 41/32,\\; J_G(\\pi_S) = 37/32$)",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=8.1)

    draw_box(ax1, 0.51, 0.04, 0.46, 0.245,
             "Global Correlated Fault $G$:\n"
             "$\\mathrm{root}_0 = \\neg g,\\; \\mathrm{child}_1 = \\neg g$\n"
             "$\\pi_G$: write $g$ to $\\mathrm{root}_0 \\Rightarrow$ mean $3/8$\n"
             "($V_G^* = 5/4;\\; \\Delta_{3,B} = r^2(1-r) = 1/8$)",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=8.1)

    draw_arrow(ax1, (0.34, 0.35), (0.245, 0.30), color=TEAL, lw=1.2)
    draw_arrow(ax1, (0.64, 0.35), (0.73, 0.30), color=AMBER, lw=1.2)

    p = np.linspace(0, 1, 500)
    r_S = (1.0 - p) * (1.0 / 32.0)
    r_G = p * (3.0 / 32.0)
    r_max = np.maximum(r_S, r_G)

    ax2.plot(p, r_S, color=TEAL, lw=1.7, ls="--", label="$R_S(\\rho_p) = (1-p)/32$")
    ax2.plot(p, r_G, color=AMBER, lw=1.7, ls="-.", label="$R_G(\\rho_p) = 3p/32$")
    ax2.plot(p, r_max, color=NAVY, lw=2.4, label="Worst-case $\\max\\{R_S, R_G\\}$")

    ax2.axhline(1.0 / 32.0, color=CRIMSON, lw=1.25, ls=":",
                label="Det. $\\frac{1}{32}\\mathbb{Z}$ barrier ($1/32$)")
    ax2.scatter([0.0], [1.0 / 32.0], color=CRIMSON, s=46, zorder=5)
    ax2.scatter([0.25], [3.0 / 128.0], color=NAVY, s=54, zorder=6)

    ax2.annotate("Det. best $\\pi_G$\n$R(\\pi_G) = 1/32$",
                 xy=(0.0, 1.0 / 32.0), xytext=(0.05, 0.048),
                 arrowprops=dict(arrowstyle="->", color=CRIMSON, lw=1.0),
                 fontsize=8.1, color=CRIMSON)

    ax2.annotate("Saddle $\\rho = \\frac{1}{4}\\pi_S + \\frac{3}{4}\\pi_G$\n"
                 "$R^* = L(3/4, 1/4) = 3/128$\n"
                 "($\\mathrm{csolveInt}$: $[41, 40, 160, 37]$)",
                 xy=(0.25, 3.0 / 128.0), xytext=(0.45, 0.032),
                 arrowprops=dict(arrowstyle="->", color=NAVY, lw=1.05),
                 fontsize=8.0, color=NAVY,
                 bbox=dict(boxstyle="round,pad=0.22", facecolor="white", edgecolor="#CBD5E1", alpha=0.95))

    ax2.set_title("(b) Minimax Regret Saddle ($R^* = 3/128 < 1/32$)",
                  fontsize=10.1, fontweight="bold", color=NAVY, pad=9)
    ax2.set_xlabel("Weight $p$ on $\\pi_S$ in $\\rho_p = p\\pi_S + (1-p)\\pi_G$", fontsize=9.1)
    ax2.set_ylabel("Worst-case regret over $\\{S, G\\}$", fontsize=9.1)
    ax2.set_xlim(-0.02, 1.02)
    ax2.set_ylim(0.0, 0.098)
    ax2.set_yticks([0.0, 3.0 / 128.0, 1.0 / 32.0, 2.0 / 32.0, 3.0 / 32.0])
    ax2.set_yticklabels(["$0$", "$3/128$", "$1/32$", "$2/32$", "$3/32$"])
    ax2.grid(True, linestyle=":", alpha=0.5)
    ax2.legend(loc="upper left", fontsize=7.8, frameon=True, facecolor="white", framealpha=0.92)

    for ext in ("pdf", "png"):
        fig.savefig(FIG_DIR / f"fig2_fault_regret_and_kernel_dp.{ext}", dpi=300, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    build_fig1()
    build_fig2()
    print("Generated figures in", FIG_DIR)
