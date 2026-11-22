#!/usr/bin/env python3
"""Generate publication-grade vector PDF and 300-DPI PNG figures for
'What Prediction Leaves Out: Relational Objecthood and the Grounds of Purpose'.
"""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Polygon, Rectangle

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
LIGHT_GRAY = "#EFEFEF"


def draw_box(ax, x, y, w, h, text, facecolor="white", edgecolor=INK,
             lw=1.1, fontsize=9.2, fontweight="normal", textcolor=INK,
             linestyle="-", pad=0.015, ha="center"):
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


def draw_arrow(ax, p1, p2, color=INK, lw=1.1, style="-|>", ls="-", rad=0.0, mutation=11):
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
    fig = plt.figure(figsize=(12.2, 5.35))
    ax1 = fig.add_axes([0.015, 0.04, 0.485, 0.90])
    ax2 = fig.add_axes([0.520, 0.04, 0.465, 0.90])

    for ax in (ax1, ax2):
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        ax.axis("off")

    # Panel (a): Physical Architecture & 6-Unit Resource Budget
    ax1.text(0.01, 0.97, "(a) Physical Architecture & Six-Unit Transaction Flow of Process $\\mathcal{M}$",
             fontsize=11, fontweight="bold", color=NAVY, ha="left", va="top")

    # Outer assembly frame
    outer = FancyBboxPatch((0.02, 0.45), 0.95, 0.44,
                           boxstyle="round,pad=0.01,rounding_size=0.02",
                           facecolor=LIGHT_BG, edgecolor=SLATE, linewidth=1.1, linestyle="--", zorder=1)
    ax1.add_patch(outer)
    ax1.text(0.04, 0.865, "Token Register Assembly (Marked Identity + Silent Tag $\\tau$)",
             fontsize=8.8, fontweight="bold", color=SLATE, ha="left", va="center")

    draw_box(ax1, 0.04, 0.69, 0.41, 0.13,
             "Healthy Row $r_H$:  [Active]  |  [Bkp 1] [Bkp 2]\n"
             "Damaged Row $r_D$: [Active]  |  [Bkp 1] [Bkp 2]",
             facecolor="white", edgecolor=NAVY, fontsize=8.3)

    draw_box(ax1, 0.04, 0.49, 0.41, 0.13,
             "Majority-Vote Restorer ($b_{\\mathrm{boot}} \\in \\{0,1\\}$)\n"
             "Reads 3 cells/row; restores active bits ($R = 3$)",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=8.3)

    draw_box(ax1, 0.53, 0.69, 0.41, 0.13,
             "Internal Parity / Gate Diagnosis\n"
             "$d \\in \\{H, D\\}$ (no external oracle)",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.4)

    draw_box(ax1, 0.53, 0.49, 0.41, 0.13,
             "Physical Execution Gate $g \\in \\{\\mathrm{open}, \\mathrm{closed}\\}$\n"
             "Raw actuation physically blocked if $g = \\mathrm{closed}$",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=8.3)

    draw_arrow(ax1, (0.245, 0.675), (0.245, 0.635), color=AMBER, lw=1.1)
    draw_arrow(ax1, (0.465, 0.755), (0.515, 0.755), color=NAVY, lw=1.1)
    draw_arrow(ax1, (0.465, 0.555), (0.515, 0.555), color=TEAL, lw=1.1)
    draw_arrow(ax1, (0.735, 0.675), (0.735, 0.635), color=SLATE, lw=1.1)

    # Bottom budget flow
    draw_box(ax1, 0.02, 0.29, 0.95, 0.10,
             "Per-Step Budget = 6 Units (1 Unit Carried Escrow + 5 Units Local Inflow)",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.8, fontweight="bold")

    draw_box(ax1, 0.02, 0.04, 0.29, 0.18,
             "Healthy Execution ($H$)\n"
             "care: $0+1+2=3 \\leq 6$ ($s, b$)\n"
             "bloom: $0+2+2=4 \\leq 6$\n"
             "($s-\\delta,\\; b+\\gamma$)",
             facecolor="white", edgecolor=TEAL, fontsize=8.0)

    draw_box(ax1, 0.35, 0.04, 0.30, 0.18,
             "Damaged Repaired ($D$, care)\n"
             "Repair $3 +$ care $1 +$ escrow $2 = 6$\n"
             "Restores code, opens $g$,\n"
             "executes care ($s, b$)",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=8.0)

    draw_box(ax1, 0.69, 0.04, 0.28, 0.18,
             "Damaged Refusal ($D$, bloom)\n"
             "Prepay $3+2+2 = 7 > 6$\n"
             "Rejected: $R=0$, inflow\n"
             "refunded, $D$ kept w.p. $1$",
             facecolor=LIGHT_GRAY, edgecolor=CRIMSON, linestyle="--", fontsize=8.0)

    draw_arrow(ax1, (0.20, 0.275), (0.165, 0.235), color=TEAL, lw=1.05)
    draw_arrow(ax1, (0.50, 0.275), (0.50, 0.235), color=TEAL, lw=1.05)
    draw_arrow(ax1, (0.80, 0.275), (0.83, 0.235), color=CRIMSON, lw=1.05, ls="--")

    # Panel (b): Non-Monotonic Diamond Lattice of Predictive Quotients
    ax2.text(0.01, 0.97, "(b) Non-Monotonic Lattice of Minimal Predictive Quotients (Prop. 3)",
             fontsize=11, fontweight="bold", color=NAVY, ha="left", va="top")

    draw_box(ax2, 0.18, 0.75, 0.64, 0.14,
             "One-Step Birth Protocol $\\mathcal{P}_1 = (B_1)$  [2 Minimal Classes]\n"
             "$\\{\\theta_0 H,\\; \\theta_0 D,\\; \\theta_1 D\\} \\quad \\mid \\quad \\{\\theta_1 H\\}$",
             facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.8, fontweight="bold")

    draw_box(ax2, 0.01, 0.39, 0.45, 0.22,
             "Infinite Birth Record $(B_t)_{t \\geq 1}$\n"
             "[3 Minimal Classes]\n"
             "$\\{\\theta_0 H, \\theta_0 D\\} \\mid \\{\\theta_1 D\\} \\mid \\{\\theta_1 H\\}$\n"
             "Erases repair fee $R_1 \\in \\{0,3\\}$",
             facecolor=LIGHT_TEAL, edgecolor=TEAL, fontsize=8.0)

    draw_box(ax2, 0.54, 0.39, 0.45, 0.22,
             "One-Step Birth + Cost $(B_1, R_1)$\n"
             "[3 Minimal Classes]\n"
             "$\\{\\theta_0 H\\} \\mid \\{\\theta_1 H\\} \\mid \\{\\theta_0 D, \\theta_1 D\\}$\n"
             "Erases latent $\\theta_1$ ($27/64$ vs. $39/64$)",
             facecolor=LIGHT_AMBER, edgecolor=AMBER, fontsize=8.0)

    draw_box(ax2, 0.14, 0.07, 0.72, 0.15,
             "Joint Multi-Step Births + Initial Expenditure $(B_1, B_2, \\dots, R_1)$\n"
             "[4 Singleton Classes]:  $\\{\\theta_0 H\\} \\mid \\{\\theta_0 D\\} \\mid \\{\\theta_1 H\\} \\mid \\{\\theta_1 D\\}$\n"
             "(Still lawfully quotients causally silent physical tag $\\tau$)",
             facecolor="white", edgecolor=NAVY, lw=1.2, fontsize=8.3)

    # Refinement arrows
    draw_arrow(ax2, (0.38, 0.735), (0.24, 0.625), color=NAVY, lw=1.15)
    draw_arrow(ax2, (0.62, 0.735), (0.76, 0.625), color=NAVY, lw=1.15)
    draw_arrow(ax2, (0.24, 0.375), (0.38, 0.235), color=TEAL, lw=1.15)
    draw_arrow(ax2, (0.76, 0.375), (0.62, 0.235), color=AMBER, lw=1.15)

    # Incomparable middle link
    draw_arrow(ax2, (0.472, 0.485), (0.528, 0.485), color=CRIMSON, lw=1.1, style="<->", ls=":")
    ax2.text(0.50, 0.545, "Incomparable\n3-class quotients", fontsize=7.6,
             color=CRIMSON, ha="center", va="center", fontweight="bold",
             bbox=dict(boxstyle="round,pad=0.18", fc="white", ec="none", alpha=0.92), zorder=5)
    ax2.text(0.16, 0.665, "add future\ncensuses $t \\geq 2$", fontsize=7.8, color=SLATE, ha="center")
    ax2.text(0.84, 0.665, "add $t=1$\ncalorimetry $R_1$", fontsize=7.8, color=SLATE, ha="center")

    fig.savefig(FIG_DIR / "fig1_architecture_and_lattice.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig1_architecture_and_lattice.png", dpi=300, bbox_inches="tight")
    plt.close(fig)


def build_fig2():
    fig = plt.figure(figsize=(12.2, 5.15))
    ax1 = fig.add_axes([0.015, 0.06, 0.455, 0.87])
    ax2 = fig.add_axes([0.545, 0.12, 0.435, 0.78])

    ax1.set_xlim(0, 1)
    ax1.set_ylim(0, 1)
    ax1.axis("off")

    ax1.text(0.01, 0.98, "(a) Finite-Memory Viability Separation Witness (Prop. 6a)",
             fontsize=11, fontweight="bold", color=NAVY, ha="left", va="top")

    # Pooled observation box o_M
    pool = FancyBboxPatch((0.39, 0.22), 0.26, 0.62,
                          boxstyle="round,pad=0.012,rounding_size=0.02",
                          facecolor=LIGHT_AMBER, edgecolor=AMBER, linewidth=1.2, linestyle="--", zorder=1)
    ax1.add_patch(pool)
    ax1.text(0.52, 0.805, "Pooled Observation $o_M$", fontsize=8.5,
             fontweight="bold", color=AMBER, ha="center")

    draw_box(ax1, 0.02, 0.63, 0.20, 0.14, "$x_L$\n$h(x_L)=o_L$", facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.6)
    draw_box(ax1, 0.02, 0.27, 0.20, 0.14, "$x_R$\n$h(x_R)=o_R$", facecolor=LIGHT_BLUE, edgecolor=NAVY, fontsize=8.6)
    draw_box(ax1, 0.425, 0.60, 0.19, 0.13, "$y_L \\in K^\\star$", facecolor="white", edgecolor=TEAL, fontsize=8.9)
    draw_box(ax1, 0.425, 0.27, 0.19, 0.13, "$y_R \\in K^\\star$", facecolor="white", edgecolor=TEAL, fontsize=8.9)
    draw_box(ax1, 0.76, 0.435, 0.21, 0.14, "$\\bot \\notin S$\n(Failure $o_\\bot$)",
             facecolor=LIGHT_GRAY, edgecolor=CRIMSON, lw=1.2, fontsize=8.5)

    pill = dict(boxstyle="round,pad=0.12", fc="white", ec="none", alpha=0.9)
    # Safe transitions
    draw_arrow(ax1, (0.235, 0.685), (0.41, 0.685), color=TEAL, lw=1.2, rad=-0.12)
    ax1.text(0.312, 0.742, "$a_L, a_R$", fontsize=7.9, color=TEAL, ha="center", bbox=pill, zorder=5)
    draw_arrow(ax1, (0.41, 0.64), (0.235, 0.64), color=TEAL, lw=1.2, rad=-0.15)
    ax1.text(0.312, 0.575, "$a_L$ (safe)", fontsize=7.9, color=TEAL, ha="center", bbox=pill, zorder=5)

    draw_arrow(ax1, (0.235, 0.365), (0.41, 0.365), color=TEAL, lw=1.2, rad=0.12)
    ax1.text(0.312, 0.422, "$a_L, a_R$", fontsize=7.9, color=TEAL, ha="center", bbox=pill, zorder=5)
    draw_arrow(ax1, (0.41, 0.31), (0.235, 0.31), color=TEAL, lw=1.2, rad=0.15)
    ax1.text(0.312, 0.238, "$a_R$ (safe)", fontsize=7.9, color=TEAL, ha="center", bbox=pill, zorder=5)

    # Lethal transitions
    draw_arrow(ax1, (0.63, 0.65), (0.748, 0.53), color=CRIMSON, lw=1.15, ls="--")
    ax1.text(0.705, 0.625, "$a_R$", fontsize=8.3, color=CRIMSON, fontweight="bold")
    draw_arrow(ax1, (0.63, 0.34), (0.748, 0.47), color=CRIMSON, lw=1.15, ls="--")
    ax1.text(0.705, 0.365, "$a_L$", fontsize=8.3, color=CRIMSON, fontweight="bold")

    draw_box(ax1, 0.03, 0.03, 0.94, 0.13,
             "Viable kernel $K^\\star = S = \\{x_L, x_R, y_L, y_R\\}$ is memoryless, yet under $\\mu_0 = \\frac{1}{2}\\delta_{x_L} + \\frac{1}{2}\\delta_{x_R}$:\n"
             "Every reactive policy $\\pi_0(o_t)$ hits $\\bot$ at $t=2$ w.p. $1/2$; 1-step memory $\\pi_1(o_{t-1}, o_t)$ stays in $K^\\star$ w.p. $1$.",
             facecolor=LIGHT_BG, edgecolor=SLATE, fontsize=7.9)

    # Panel (b): Exact Phase Diagram in (k_c, k_b) plane at q = 1/3
    kc_min, kc_max = 0.65, 1.40
    kb_min, kb_max = 0.65, 1.40

    # Polygon 1: Subcritical Refusal Floor (kc <= 1 and 2/3 kb + 1/3 kc <= 1 => kb <= (3 - kc)/2)
    # At kc = 0.65, (3 - 0.65)/2 = 1.175; at kc = 1.0, kb = 1.0
    poly_reg1 = Polygon(
        [(kc_min, kb_min), (1.0, kb_min), (1.0, 1.0), (kc_min, (3.0 - kc_min) / 2.0)],
        closed=True, facecolor="#EFEFEF", edgecolor="none", zorder=1
    )
    # Polygon 2: Conservative theta_0 Attainment (kc >= 1 and kb <= kc)
    poly_reg2 = Polygon(
        [(1.0, kb_min), (kc_max, kb_min), (kc_max, kc_max), (1.0, 1.0)],
        closed=True, facecolor="#DCEAF7", edgecolor="none", zorder=1
    )
    # Polygon 3: Proliferative theta_1 Attainment (kb >= kc and kb >= (3 - kc)/2)
    poly_reg3 = Polygon(
        [(kc_min, (3.0 - kc_min) / 2.0), (1.0, 1.0), (kc_max, kc_max), (kc_min, kb_max)],
        closed=True, facecolor="#DDF0EE", edgecolor="none", zorder=1
    )
    ax2.add_patch(poly_reg1)
    ax2.add_patch(poly_reg2)
    ax2.add_patch(poly_reg3)

    # Exact phase boundary lines
    kc_left = np.linspace(kc_min, 1.0, 100)
    kc_right = np.linspace(1.0, kc_max, 100)
    ax2.plot([1.0, 1.0], [kb_min, 1.0], color=NAVY, lw=1.6, ls="-", zorder=3)
    ax2.plot(kc_left, (3.0 - kc_left) / 2.0, color=CRIMSON, lw=1.6, ls="--", zorder=3)
    ax2.plot(kc_right, kc_right, color=TEAL, lw=1.8, ls="-", zorder=3)
    ax2.plot(kc_left, kc_left, color=MUTED, lw=0.9, ls=":", zorder=2)

    # Rational witness points
    ax2.scatter([11/12], [25/24], s=70, color=CRIMSON, edgecolor="white", linewidth=0.9, zorder=5, marker="o")
    ax2.annotate(
        "Critical witness $(11/12,\\; 25/24)$\n$\\rho_* = \\lambda_1 = 1$, yet $\\mathbb{E}_{\\theta_1 D}[N_t] = 11/12$",
        xy=(11/12, 25/24), xytext=(0.675, 1.27),
        fontsize=7.9, color=CRIMSON, fontweight="bold",
        arrowprops=dict(arrowstyle="->", color=CRIMSON, lw=0.95),
        bbox=dict(boxstyle="round,pad=0.22", fc="white", ec=CRIMSON, lw=0.8),
        zorder=6
    )

    ax2.scatter([9/8], [5/4], s=80, color=TEAL, edgecolor="white", linewidth=0.9, zorder=5, marker="^")
    ax2.annotate(
        "Supercritical witness $(9/8,\\; 5/4)$\n$\\lambda_1 = 29/24 > \\lambda_0$; $t=1$ loss $243/2048$",
        xy=(9/8, 5/4), xytext=(0.94, 1.335),
        fontsize=7.8, color=NAVY,
        arrowprops=dict(arrowstyle="->", color=NAVY, lw=0.95),
        bbox=dict(boxstyle="round,pad=0.22", fc="white", ec=NAVY, lw=0.8),
        zorder=6
    )

    # Region labels
    ax2.text(0.855, 0.73, "Regime I: Subcritical\nRefusal Floor $\\rho_* = 1$\n($\\lambda_0 < 1,\\; \\lambda_1 < 1$)",
             fontsize=8.2, color=INK, ha="center", va="center", fontweight="bold")
    ax2.text(1.22, 0.83, "Regime II: $\\theta_0$ Attains\n$\\rho_* = \\lambda_0 = k_c \\geq 1$\n($\\gamma \\leq \\delta$: care optimal)",
             fontsize=8.3, color=NAVY, ha="center", va="center", fontweight="bold")
    ax2.text(1.035, 1.185, "Regime III: $\\theta_1$ Attains\n$\\rho_* = \\lambda_1 \\geq 1$ ($\\gamma \\geq \\delta$)\nLineage growth vs.\ntoken survival ($s-\\delta < s$)",
             fontsize=8.0, color=TEAL, ha="center", va="center", fontweight="bold")

    ax2.text(1.255, 1.22, "$\\gamma = \\delta$\n(tie line)", fontsize=7.8, color=TEAL, rotation=36)
    ax2.text(0.71, 1.075, "$\\lambda_1 = 1$", fontsize=8.0, color=CRIMSON, rotation=-24)

    ax2.set_xlim(kc_min, kc_max)
    ax2.set_ylim(kb_min, kb_max)
    ax2.set_xlabel("Conservative Maintenance Output Rate $k_c = s + b$", fontsize=9.3)
    ax2.set_ylabel("Proliferative Output Rate $k_b = s - \\delta + b + \\gamma$", fontsize=9.3)
    ax2.set_title("(b) Full-Policy Growth & Attainment Phase Diagram ($q = 1/3$, Thm. 1)",
                  fontsize=10.5, fontweight="bold", color=NAVY, pad=10)
    ax2.tick_params(labelsize=8.5)

    fig.savefig(FIG_DIR / "fig2_memory_and_phase.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig2_memory_and_phase.png", dpi=300, bbox_inches="tight")
    plt.close(fig)


def build_fig3():
    fig = plt.figure(figsize=(12.2, 4.95))
    ax = fig.add_axes([0.01, 0.03, 0.98, 0.93])
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis("off")

    ax.text(0.50, 0.97,
            "Typed Explanatory Preservation Across Representations and the Four Stratified Grounds of Purpose",
            fontsize=11.2, fontweight="bold", color=NAVY, ha="center", va="top")

    # Left column header
    ax.text(0.195, 0.895, "Representational Quotient & What Compression Leaves Out",
            fontsize=9.4, fontweight="bold", color=SLATE, ha="center")
    ax.text(0.755, 0.895, "Stratified Purposive Ground, Bearer & Normative Scope",
            fontsize=9.4, fontweight="bold", color=SLATE, ha="center")

    left_specs = [
        (0.69, "Scalar Score / Stationary Density Fit ($J = R - \\lambda I$, $-\\ln p^*$)",
         "Leaves out reward shaping, affine $(R,I)$ gauge & rank-3 $(s,b,bq)$ structure", LIGHT_GRAY, MUTED),
        (0.48, "Decoded Symbolic / Output-Stream Quotient ($C_{\\mathcal{P}}(h),\\; \\theta$)",
         "Couples infinite births $(B_t)_{t\\geq 1}$ yet erases paid repair $R_1$ & gate $g$", LIGHT_AMBER, AMBER),
        (0.27, "Closed-Test Belief & Interventional Quotient ($U_{a,o}\\mathcal{F} \\subseteq \\mathcal{F}$)",
         "Preserves counterfactual cuts $\\mathcal{V}_{\\min}$, budget $R_1$ & finite-memory viability", LIGHT_TEAL, TEAL),
        (0.06, "Genealogical & Deliberative History (Marked Tokens + Reasons)",
          "Separates parent retention from strict birth, $\\nu_{\\mathrm{QSD}}$ from Doob law & practical reasons", LIGHT_BLUE, NAVY),
    ]

    for y, title, sub, fc, ec in left_specs:
        draw_box(ax, 0.015, y, 0.365, 0.16, f"{title}\n{sub}",
                 facecolor=fc, edgecolor=ec, fontsize=8.0)

    right_specs = [
        (0.69, "Rung 1: Systemic Causal Role (Cummins; Craver)",
         "Bearer: Sub-mechanism in host capacity $\\Psi$  |  Licenses causal relevance, not malfunction",
         "white", SLATE),
        (0.48, "Rung 2: Endogenous Regulatory & Viability Closure (Mossio; Di Paolo; Bich)",
         "Bearer: Diachronic organism token  |  Licenses conditional viability standard (not categorical)",
         LIGHT_TEAL, TEAL),
        (0.27, "Rung 3: Selective Retention / Reproduction Etiology (Millikan; Garson)",
         "Bearer: Lineage or plastic repertoire  |  Proper function; can conflict with Rung 2 ($s-\\delta < s$)",
         LIGHT_AMBER, AMBER),
        (0.06, "Rung 4: Reflective Practical & Moral Reason (Korsgaard; Scanlon; Street)",
         "Bearer: Deliberative agent / institution  |  Justificatory ought; never entailed by Rungs 1–3",
         LIGHT_BLUE, NAVY),
    ]

    for y, title, sub, fc, ec in right_specs:
        draw_box(ax, 0.525, y, 0.46, 0.16, f"{title}\n{sub}",
                 facecolor=fc, edgecolor=ec, fontsize=8.0)

    badge = dict(boxstyle="round,pad=0.16", fc="white", ec="none", alpha=0.94)
    # Preservation requirement bridges
    draw_arrow(ax, (0.392, 0.35), (0.512, 0.52), color=TEAL, lw=1.2)
    ax.text(0.452, 0.43, "grounds Rung 2", fontsize=7.5, color=TEAL,
            ha="center", va="center", fontweight="bold", bbox=badge, zorder=5)

    draw_arrow(ax, (0.392, 0.16), (0.512, 0.34), color=AMBER, lw=1.2)
    ax.text(0.452, 0.255, "grounds Rung 3", fontsize=7.5, color=AMBER,
            ha="center", va="center", fontweight="bold", bbox=badge, zorder=5)

    draw_arrow(ax, (0.392, 0.11), (0.512, 0.11), color=NAVY, lw=1.2)
    ax.text(0.452, 0.11, "grounds Rung 4", fontsize=7.5, color=NAVY,
            ha="center", va="center", fontweight="bold", bbox=badge, zorder=5)

    # Blocked illicit transfer arrows (both Scalar Score fit AND Output-Stream quotient -> Rung 2)
    draw_arrow(ax, (0.392, 0.77), (0.512, 0.61), color=CRIMSON, lw=1.15, ls="--")
    ax.text(0.452, 0.70, "illicit transfer", fontsize=7.5, color=CRIMSON,
            ha="center", va="center", fontweight="bold", bbox=badge, zorder=5)
    draw_arrow(ax, (0.392, 0.56), (0.512, 0.56), color=CRIMSON, lw=1.15, ls="--")
    ax.text(0.452, 0.575, "erases $R_1, g$", fontsize=7.4, color=CRIMSON,
            ha="center", va="center", fontweight="bold", bbox=badge, zorder=5)

    fig.savefig(FIG_DIR / "fig3_preservation_and_rungs.pdf", bbox_inches="tight")
    fig.savefig(FIG_DIR / "fig3_preservation_and_rungs.png", dpi=300, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    build_fig1()
    build_fig2()
    build_fig3()
    print("Generated all 3 vector PDF and 300-DPI PNG figures in:", FIG_DIR)
