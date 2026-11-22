#!/usr/bin/env python3
"""Generate publication-grade vector PDF and 300-DPI PNG figures for
'What Prediction Leaves Out: Relational Objecthood and the Grounds of Purpose'.
"""
from __future__ import annotations

from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Polygon

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
LIGHT_GRAY = "#EFEFEF"


def draw_box(ax, x, y, w, h, text, facecolor="white", edgecolor=INK,
             lw=1.15, fontsize=9.2, fontweight="normal", textcolor=INK,
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


def draw_arrow(ax, p1, p2, color=INK, lw=1.15, style="-|>", ls="-", rad=0.0, mutation=11.5):
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
    # Sized at 9.5 x 4.55 in so boxes print at ~6.5-7.5 pt when scaled to 6.5 in textwidth
    fig = plt.figure(figsize=(9.5, 4.55))
    ax1 = fig.add_axes([0.01, 0.03, 0.485, 0.92])
    ax2 = fig.add_axes([0.515, 0.03, 0.475, 0.92])

    for ax in (ax1, ax2):
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        ax.axis("off")

    # Panel (a): Physical Architecture & 6-Unit Resource Budget
    ax1.text(0.01, 0.985, "(a) Physical Architecture & Six-Unit Flow of $\\mathcal{M}$",
             fontsize=10.5, fontweight="bold", color=NAVY, ha="left", va="top")

    outer = FancyBboxPatch((0.015, 0.455), 0.965, 0.455,
                           boxstyle="round,pad=0.01,rounding_size=0.02",
                           facecolor=LIGHT_BG, edgecolor=SLATE, linewidth=1.1, linestyle="--", zorder=1)
    ax1.add_patch(outer)
    ax1.text(0.035, 0.882, "Token Register Assembly (Genealogy + Silent Tag $\\tau$)",
             fontsize=8.7, fontweight="bold", color=SLATE, ha="left", va="center")

    draw_box(ax1, 0.035, 0.695, 0.43, 0.145,
             "Row $r_H$: [Act] | [Bkp 1] [Bkp 2]\n"
             "Row $r_D$: [Act] | [Bkp 1] [Bkp 2]",
             facecolor="white", edgecolor=NAVY, fontsize=8.4)

    draw_box(ax1, 0.035, 0.485, 0.43, 0.145,
             "Majority Restorer ($b_{\\mathrm{boot}} \\in \\{0,1\\}$)\n"
             "Restores active bits ($R = 3$)",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=8.4)

    draw_box(ax1, 0.535, 0.695, 0.425, 0.145,
             "Internal Gate/Parity Diagnosis\n"
             "$d \\in \\{H, D\\}$ (in $\\Pi_{\\mathrm{pub}}$)",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.4)

    draw_box(ax1, 0.535, 0.485, 0.425, 0.145,
             "Execution Gate $g \\in \\{\\mathrm{open},\\mathrm{closed}\\}$\n"
             "Blocks raw actuation if closed",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=8.4)

    draw_arrow(ax1, (0.25, 0.68), (0.25, 0.642), color=AMBER, lw=1.15)
    draw_arrow(ax1, (0.48, 0.768), (0.52, 0.768), color=NAVY, lw=1.15)
    draw_arrow(ax1, (0.48, 0.558), (0.52, 0.558), color=TEAL, lw=1.15)
    draw_arrow(ax1, (0.748, 0.68), (0.748, 0.642), color=SLATE, lw=1.15)

    draw_box(ax1, 0.015, 0.30, 0.965, 0.095,
             "Per-Step Budget = 6 Units (1 Carried Escrow + 5 Local Inflow)",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.7, fontweight="bold")

    draw_box(ax1, 0.018, 0.03, 0.288, 0.20,
             "Healthy ($H$)\n"
             "care: $0{+}1{+}2=3$\n"
             "bloom: $0{+}2{+}2=4$\n"
             "($s{-}\\delta,\\; b{+}\\gamma$)",
             facecolor="white", edgecolor=TEAL, fontsize=8.15)

    draw_box(ax1, 0.346, 0.03, 0.302, 0.20,
             "Damaged ($D$, care)\n"
             "Pay $3{+}1{+}2 = 6$\n"
             "Restores code, opens $g$,\n"
             "runs care ($s, b$)",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=8.15)

    draw_box(ax1, 0.688, 0.03, 0.288, 0.20,
             "Refusal ($D$, bloom)\n"
             "Need $3{+}2{+}2 = 7 > 6$\n"
             "Rejected: $R=0$,\n"
             "$D$ kept w.p. $1$",
             facecolor=LIGHT_GRAY, edgecolor=CRIMSON, linestyle="--", fontsize=8.15)

    draw_arrow(ax1, (0.19, 0.285), (0.165, 0.245), color=TEAL, lw=1.1)
    draw_arrow(ax1, (0.50, 0.285), (0.50, 0.245), color=TEAL, lw=1.1)
    draw_arrow(ax1, (0.81, 0.285), (0.83, 0.245), color=CRIMSON, lw=1.1, ls="--")

    # Panel (b): Incomparable-Refinement Diamond Lattice of Minimal Predictive Quotients
    ax2.text(0.01, 0.985, "(b) Incomparable Refinements of Minimal Quotients (Prop. 3)",
             fontsize=10.5, fontweight="bold", color=NAVY, ha="left", va="top")
    ax2.text(0.50, 0.934, "Fixed-parameter 4-founder laws (autonomous hereditary execution)",
             fontsize=8.25, fontweight="bold", color=SLATE, ha="center", va="center")

    draw_box(ax2, 0.14, 0.742, 0.72, 0.138,
             "One-Step Birth Protocol $(B_1)$  [2 Minimal Classes]\n"
             "$\\{\\theta_0 H,\\; \\theta_0 D,\\; \\theta_1 D\\} \\quad \\mid \\quad \\{\\theta_1 H\\}$",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.8, fontweight="bold")

    draw_box(ax2, 0.015, 0.375, 0.435, 0.24,
             "Births $(B_1, B_2) \\equiv (B_t)_{t \\geq 1}$\n"
             "[3 Minimal Law Classes]\n"
             "$\\{\\theta_0 H, \\theta_0 D\\} \\mid \\{\\theta_1 D\\} \\mid \\{\\theta_1 H\\}$\n"
             "Erases repair fee $R_1 \\in \\{0,3\\}$",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=8.10)

    draw_box(ax2, 0.550, 0.375, 0.435, 0.24,
             "First Birth + Cost $(B_1, R_1)$\n"
             "[3 Minimal Law Classes]\n"
             "$\\{\\theta_0 H\\} \\mid \\{\\theta_1 H\\} \\mid \\{\\theta_0 D, \\theta_1 D\\}$\n"
             "Erases $\\theta_0 D$ vs. $\\theta_1 D$ ($27/64, 39/64$)",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=8.10)

    draw_box(ax2, 0.09, 0.045, 0.82, 0.165,
             "Two-Step Births + Initial Cost $(B_1, B_2, R_1)$\n"
             "[4 Distinct Joint Laws]:  $\\{\\theta_0 H\\} \\mid \\{\\theta_0 D\\} \\mid \\{\\theta_1 H\\} \\mid \\{\\theta_1 D\\}$\n"
             "(Identifiable in law, single runs overlap; quotients silent tag $\\tau$)",
             facecolor="white", edgecolor=NAVY, lw=1.2, fontsize=8.4)

    draw_arrow(ax2, (0.37, 0.725), (0.235, 0.63), color=NAVY, lw=1.2)
    draw_arrow(ax2, (0.63, 0.725), (0.765, 0.63), color=NAVY, lw=1.2)
    draw_arrow(ax2, (0.235, 0.36), (0.37, 0.225), color=TEAL, lw=1.2)
    draw_arrow(ax2, (0.765, 0.36), (0.63, 0.225), color=AMBER, lw=1.2)

    draw_arrow(ax2, (0.466, 0.475), (0.534, 0.475), color=CRIMSON, lw=1.15, style="<->", ls=":")
    ax2.text(0.50, 0.555, "Incomparable\n3-class refinements", fontsize=7.9,
             color=CRIMSON, ha="center", va="center", fontweight="bold",
             bbox=dict(boxstyle="round,pad=0.16", fc="white", ec="none", alpha=0.93), zorder=5)
    ax2.text(0.15, 0.675, "extend horizon\n$t \\geq 2$", fontsize=8.1, color=SLATE, ha="center")
    ax2.text(0.85, 0.675, "adjoin $t=1$\ncost $R_1$", fontsize=8.1, color=SLATE, ha="center")

    fig.savefig(FIG_DIR / "fig1_architecture_and_lattice.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig1_architecture_and_lattice.png", dpi=300, bbox_inches="tight")
    plt.close(fig)


def build_fig2():
    fig = plt.figure(figsize=(9.5, 4.35))
    ax1 = fig.add_axes([0.01, 0.04, 0.46, 0.89])
    ax2 = fig.add_axes([0.55, 0.13, 0.43, 0.77])

    ax1.set_xlim(0, 1)
    ax1.set_ylim(0, 1)
    ax1.axis("off")

    ax1.text(0.01, 0.99, "(a) Finite-Memory Viability Witness (Prop. 6a)",
             fontsize=10.4, fontweight="bold", color=NAVY, ha="left", va="top")

    pool = FancyBboxPatch((0.385, 0.23), 0.265, 0.62,
                          boxstyle="round,pad=0.012,rounding_size=0.02",
                          facecolor=LIGHT_AMBER, edgecolor=AMBER, linewidth=1.2, linestyle="--", zorder=1)
    ax1.add_patch(pool)
    ax1.text(0.518, 0.812, "Pooled $o_M$", fontsize=8.7,
             fontweight="bold", color=AMBER, ha="center")

    draw_box(ax1, 0.02, 0.63, 0.21, 0.145, "$x_L$\n$h(x_L)=o_L$", facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.7)
    draw_box(ax1, 0.02, 0.27, 0.21, 0.145, "$x_R$\n$h(x_R)=o_R$", facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.7)
    draw_box(ax1, 0.42, 0.60, 0.195, 0.135, "$y_L \\in K^\\star$", facecolor="white", edgecolor=TEAL, fontsize=9.0)
    draw_box(ax1, 0.42, 0.27, 0.195, 0.135, "$y_R \\in K^\\star$", facecolor="white", edgecolor=TEAL, fontsize=9.0)
    draw_box(ax1, 0.75, 0.435, 0.225, 0.145, "$\\bot \\notin S$\n(Failure $o_\\bot$)",
             facecolor=LIGHT_GRAY, edgecolor=CRIMSON, lw=1.2, fontsize=8.6)

    pill = dict(boxstyle="round,pad=0.12", fc="white", ec="none", alpha=0.92)
    draw_arrow(ax1, (0.245, 0.69), (0.405, 0.69), color=TEAL, lw=1.2, rad=-0.12)
    ax1.text(0.32, 0.75, "$a_L, a_R$", fontsize=8.2, color=TEAL, ha="center", bbox=pill, zorder=5)
    draw_arrow(ax1, (0.405, 0.64), (0.245, 0.64), color=TEAL, lw=1.2, rad=-0.15)
    ax1.text(0.32, 0.57, "$a_L$ safe", fontsize=8.2, color=TEAL, ha="center", bbox=pill, zorder=5)

    draw_arrow(ax1, (0.245, 0.37), (0.405, 0.37), color=TEAL, lw=1.2, rad=0.12)
    ax1.text(0.32, 0.43, "$a_L, a_R$", fontsize=8.2, color=TEAL, ha="center", bbox=pill, zorder=5)
    draw_arrow(ax1, (0.405, 0.31), (0.245, 0.31), color=TEAL, lw=1.2, rad=0.15)
    ax1.text(0.32, 0.235, "$a_R$ safe", fontsize=8.2, color=TEAL, ha="center", bbox=pill, zorder=5)

    draw_arrow(ax1, (0.628, 0.65), (0.74, 0.53), color=CRIMSON, lw=1.15, ls="--")
    ax1.text(0.70, 0.625, "$a_R$", fontsize=8.6, color=CRIMSON, fontweight="bold")
    draw_arrow(ax1, (0.628, 0.34), (0.74, 0.47), color=CRIMSON, lw=1.15, ls="--")
    ax1.text(0.70, 0.365, "$a_L$", fontsize=8.6, color=CRIMSON, fontweight="bold")

    draw_box(ax1, 0.02, 0.02, 0.955, 0.145,
             "Safe kernel $K^\\star = S$ is state-defined, yet under $\\mu_0 = \\frac{1}{2}\\delta_{x_L} + \\frac{1}{2}\\delta_{x_R}$:\n"
             "Every reactive $\\pi_0(o_t)$ hits $\\bot$ w.p. $1/2$; 1-step $\\pi_1(o_{t-1}, o_t)$ stays in $K^\\star$ w.p. $1$.",
             facecolor=LIGHT_BG, edgecolor=SLATE, fontsize=8.2)

    # Panel (b): Exact Phase Diagram in (k_c, k_b) plane at q = 1/3
    kc_min, kc_max = 0.65, 1.40
    kb_min, kb_max = 0.65, 1.40

    poly_reg1 = Polygon(
        [(kc_min, kb_min), (1.0, kb_min), (1.0, 1.0), (kc_min, (3.0 - kc_min) / 2.0)],
        closed=True, facecolor="#EFEFEF", edgecolor="none", zorder=1
    )
    poly_reg2 = Polygon(
        [(1.0, kb_min), (kc_max, kb_min), (kc_max, kc_max), (1.0, 1.0)],
        closed=True, facecolor="#DCEAF7", edgecolor="none", zorder=1
    )
    poly_reg3 = Polygon(
        [(kc_min, (3.0 - kc_min) / 2.0), (1.0, 1.0), (kc_max, kc_max), (kc_min, kb_max)],
        closed=True, facecolor="#DDF0EE", edgecolor="none", zorder=1
    )
    ax2.add_patch(poly_reg1)
    ax2.add_patch(poly_reg2)
    ax2.add_patch(poly_reg3)

    kc_left = np.linspace(kc_min, 1.0, 100)
    kc_right = np.linspace(1.0, kc_max, 100)
    ax2.plot([1.0, 1.0], [kb_min, 1.0], color=NAVY, lw=1.6, ls="-", zorder=3)
    ax2.plot(kc_left, (3.0 - kc_left) / 2.0, color=CRIMSON, lw=1.6, ls="--", zorder=3)
    ax2.plot(kc_right, kc_right, color=TEAL, lw=1.8, ls="-", zorder=3)
    ax2.plot(kc_left, kc_left, color=MUTED, lw=0.95, ls=":", zorder=2)

    ax2.scatter([11/12], [25/24], s=68, color=CRIMSON, edgecolor="white", linewidth=0.9, zorder=5, marker="o")
    ax2.annotate(
        "Critical $(11/12, 25/24)$\n$\\lambda_1=1$, $\\mathbb{E}_{\\theta_1 D}[N_t]=11/12$",
        xy=(11/12, 25/24), xytext=(0.668, 1.265),
        fontsize=8.1, color=CRIMSON, fontweight="bold",
        arrowprops=dict(arrowstyle="->", color=CRIMSON, lw=0.95),
        bbox=dict(boxstyle="round,pad=0.20", fc="white", ec=CRIMSON, lw=0.8),
        zorder=6
    )

    ax2.scatter([9/8], [5/4], s=76, color=TEAL, edgecolor="white", linewidth=0.9, zorder=5, marker="^")
    ax2.annotate(
        "Supercritical $(9/8, 5/4)$\n$\\lambda_1 = 29/24$; $t=1$ loss $243/2048$",
        xy=(9/8, 5/4), xytext=(0.935, 1.33),
        fontsize=8.0, color=NAVY,
        arrowprops=dict(arrowstyle="->", color=NAVY, lw=0.95),
        bbox=dict(boxstyle="round,pad=0.20", fc="white", ec=NAVY, lw=0.8),
        zorder=6
    )

    ax2.text(0.84, 0.74, "Regime I: Subcritical\nDormancy $\\rho_* = 1$\n(autonomous $\\theta_0, \\theta_1 < 1$)",
             fontsize=8.2, color=INK, ha="center", va="center", fontweight="bold")
    ax2.text(1.22, 0.82, "Regime II: $\\theta_0$ Attains\n$\\rho_* = \\lambda_0 = k_c \\geq 1$\n($\\gamma \\leq \\delta$)",
             fontsize=8.3, color=NAVY, ha="center", va="center", fontweight="bold")
    ax2.text(1.045, 1.18, "Regime III: $\\theta_1$ Attains\n$\\rho_* = \\lambda_1 \\geq 1$ ($\\gamma \\geq \\delta$)\n($s{-}\\delta < s$)",
             fontsize=8.2, color=TEAL, ha="center", va="center", fontweight="bold")

    ax2.text(1.25, 1.21, "$\\gamma = \\delta$", fontsize=8.1, color=TEAL, rotation=36, fontweight="bold")
    ax2.text(0.70, 1.08, "$\\lambda_1 = 1$", fontsize=8.2, color=CRIMSON, rotation=-24, fontweight="bold")

    ax2.set_xlim(kc_min, kc_max)
    ax2.set_ylim(kb_min, kb_max)
    ax2.set_xlabel("Conservative Maintenance Rate $k_c = s + b$", fontsize=9.4)
    ax2.set_ylabel("Proliferative Output Rate $k_b = s - \\delta + b + \\gamma$", fontsize=9.4)
    ax2.set_title("(b) Autonomous Attainment vs. $\\rho_*$ ($q = 1/3$, Thm. 1)",
                  fontsize=10.2, fontweight="bold", color=NAVY, pad=9)
    ax2.tick_params(labelsize=8.6)

    fig.savefig(FIG_DIR / "fig2_memory_and_phase.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig2_memory_and_phase.png", dpi=300, bbox_inches="tight")
    plt.close(fig)


def build_fig3():
    fig = plt.figure(figsize=(9.5, 4.45))
    ax = fig.add_axes([0.008, 0.02, 0.984, 0.94])
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis("off")

    ax.text(0.50, 0.98,
            "Typed Explanatory Preservation Across Quotients and the Four Stratified Grounds of Purpose",
            fontsize=10.6, fontweight="bold", color=NAVY, ha="center", va="top")

    ax.text(0.20, 0.90, "Representational Quotient & Preserved / Erased Structure",
            fontsize=9.2, fontweight="bold", color=SLATE, ha="center")
    ax.text(0.76, 0.90, "Stratified Purposive Ground, Bearer & Normative Scope",
            fontsize=9.2, fontweight="bold", color=SLATE, ha="center")

    left_specs = [
        (0.685, "Scalar Score / Stationary Density ($J = R - \\lambda I$, $-\\ln p^*$)",
         "Leaves out reward shaping, affine $(R,I)$ gauge & 3D $(s,b,bq)$ map", LIGHT_GRAY, MUTED),
        (0.470, "Decoded Code / Birth-Stream Quotient ($C_{\\mathcal{P}}(h),\\; \\theta$)",
         "Couples infinite births $(B_t)_{t\\geq 1}$ yet erases paid cost $R_1$ & gate $g$", LIGHT_AMBER, AMBER),
        (0.255, "Interventional, Cost-Tracked & Closed-Test Quotient",
         "Adjoins $\\mathrm{do}(\\iota)$ kernels, tracked fee $R_1$ & closure $U_{a,o}\\mathcal{F}\\subseteq\\mathcal{F}$", LIGHT_TEAL, TEAL),
        (0.040, "Genealogical Cohort & Deliberative History",
         "Tracks retention vs. birth, selection cohorts & practical reasons", LIGHT_BLUE, NAVY),
    ]

    for y, title, sub, fc, ec in left_specs:
        draw_box(ax, 0.018, y, 0.376, 0.168, f"{title}\n{sub}",
                 facecolor=fc, edgecolor=ec, fontsize=8.25)

    right_specs = [
        (0.685, "Rung 1: Systemic Causal Role (Cummins; Craver)",
         "Bearer: Sub-mechanism in $\\Psi$  |  Causal role; no malfunction norm",
         "white", SLATE),
        (0.470, "Rung 2: Endogenous Repair & Regulation (Mossio; Bich)",
         "Bearer: Organism token  |  Conditional viability norm (vs. side-effect)",
         LIGHT_TEAL, TEAL),
        (0.255, "Rung 3: Selective Retention / Reproduction (Millikan; Garson)",
         "Bearer: Selected lineage  |  Retrospective proper function (vs. Rung 2)",
         LIGHT_AMBER, AMBER),
        (0.040, "Rung 4: Reflective Practical Reason (Korsgaard; Scanlon)",
         "Bearer: Deliberative agent  |  Justificatory ought (not from Rungs 1–3)",
         LIGHT_BLUE, NAVY),
    ]

    for y, title, sub, fc, ec in right_specs:
        draw_box(ax, 0.532, y, 0.448, 0.168, f"{title}\n{sub}",
                 facecolor=fc, edgecolor=ec, fontsize=8.25)

    badge = dict(boxstyle="round,pad=0.14", fc="white", ec="none", alpha=0.94)
    draw_arrow(ax, (0.404, 0.345), (0.518, 0.525), color=TEAL, lw=1.25)
    ax.text(0.461, 0.432, "evidence for\nRung 2", fontsize=7.6, color=TEAL,
            ha="center", va="center", fontweight="bold", bbox=badge, zorder=5, linespacing=1.08)

    draw_arrow(ax, (0.404, 0.150), (0.518, 0.335), color=AMBER, lw=1.25)
    ax.text(0.461, 0.245, "evidence for\nRung 3", fontsize=7.6, color=AMBER,
            ha="center", va="center", fontweight="bold", bbox=badge, zorder=5, linespacing=1.08)

    draw_arrow(ax, (0.404, 0.088), (0.518, 0.088), color=NAVY, lw=1.25)
    ax.text(0.461, 0.088, "evidence for\nRung 4", fontsize=7.6, color=NAVY,
            ha="center", va="center", fontweight="bold", bbox=badge, zorder=5, linespacing=1.08)

    draw_arrow(ax, (0.404, 0.770), (0.518, 0.605), color=CRIMSON, lw=1.2, ls="--")
    ax.text(0.462, 0.70, "illicit transfer", fontsize=8.0, color=CRIMSON,
            ha="center", va="center", fontweight="bold", bbox=badge, zorder=5)
    draw_arrow(ax, (0.404, 0.555), (0.518, 0.555), color=CRIMSON, lw=1.2, ls="--")
    ax.text(0.462, 0.575, "erases $R_1, g$", fontsize=7.9, color=CRIMSON,
            ha="center", va="center", fontweight="bold", bbox=badge, zorder=5)

    fig.savefig(FIG_DIR / "fig3_preservation_and_rungs.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig3_preservation_and_rungs.png", dpi=300, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    build_fig1()
    build_fig2()
    build_fig3()
    print("Generated all 3 vector PDF and 300-DPI PNG figures in:", FIG_DIR)
