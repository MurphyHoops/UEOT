#!/usr/bin/env python3
"""Generate publication-quality vector PDF (TrueType fonttype=42) and 300-DPI PNG figures."""
from __future__ import annotations

import math
from pathlib import Path
import sys
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from verify_standalone import (
    ramsey_coeffs,
    z_causal_break,
    bell_blocks,
    bell_events_from_blocks,
    exact_duhamel_cutoff_bound,
    kg_field_parameters,
    kg_run_mode_sum,
)

FIG_DIR = ROOT / "figures"
FIG_DIR.mkdir(exist_ok=True)

plt.rcParams.update({
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
    "font.family": "serif",
    "font.serif": ["Times New Roman", "Liberation Serif", "STIXGeneral", "DejaVu Serif"],
    "mathtext.fontset": "stix",
    "font.size": 9.5,
    "axes.titlesize": 10.5,
    "axes.labelsize": 9.5,
    "legend.fontsize": 8.0,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.14,
})


def save_both(fig: plt.Figure, stem: str) -> None:
    fig.savefig(FIG_DIR / f"{stem}.pdf")
    fig.savefig(FIG_DIR / f"{stem}.png", dpi=300)
    plt.close(fig)


def make_fig1_ramsey_and_causal_break() -> None:
    """Fig 1: Ramsey non-identifiability fiber (u,v) vs. causal-break signed phase."""
    u_fixed = 9.0 / 50.0
    v_fixed = 9.0 / 400.0
    lam_lo = math.sqrt(9.0 / 110.0)
    lam_hi = math.sqrt(27.0 / 200.0)
    lams = np.linspace(lam_lo, lam_hi, 221)
    zs_plus_im = []
    zs_minus_im = []
    for lam in lams:
        n_cand = (u_fixed / (lam ** 2) - 1.0) / 2.0
        c_cand = v_fixed / (lam ** 2)
        zs_plus_im.append(z_causal_break(float(lam), n_cand, c_cand, +1).imag)
        zs_minus_im.append(z_causal_break(float(lam), n_cand, c_cand, -1).imag)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.15))

    ax1.plot(lams, zs_plus_im, lw=2.2, color="#1f4e79", label=r"$\mathrm{Im}\,z_{+}(\lambda)$ ($s=+1$)")
    ax1.plot(lams, zs_minus_im, lw=2.2, ls="--", color="#b22222", label=r"$\mathrm{Im}\,z_{-}(\lambda)$ ($s=-1$)")
    ax1.fill_between(lams, zs_minus_im, zs_plus_im, color="#d9e6f2", alpha=0.55, label=r"Signed causal-break gap")
    ax1.axvline(lam_lo, color="#718096", lw=0.8, ls=":")
    ax1.axvline(lam_hi, color="#718096", lw=0.8, ls=":")

    z_p1 = z_causal_break(0.30, 0.50, 0.25, +1)
    z_m1 = z_causal_break(0.30, 0.50, 0.25, -1)
    z_p2 = z_causal_break(1.0 / 3.0, 0.31, 0.2025, +1)
    z_m2 = z_causal_break(1.0 / 3.0, 0.31, 0.2025, -1)

    ax1.scatter([0.30, 1.0 / 3.0], [z_p1.imag, z_p2.imag], color="#1f4e79", zorder=5, s=42)
    ax1.scatter([0.30, 1.0 / 3.0], [z_m1.imag, z_m2.imag], color="#b22222", zorder=5, s=42)
    ax1.annotate(r"$P_1\,(\lambda=0.30)$", xy=(0.30, z_p1.imag), xytext=(0.289, z_p1.imag + 0.048),
                 arrowprops=dict(arrowstyle="->", lw=0.8, color="#333333"), fontsize=8.3)
    ax1.annotate(r"$P_2\,(\lambda=1/3)$", xy=(1.0 / 3.0, z_p2.imag), xytext=(0.336, z_p2.imag + 0.048),
                 arrowprops=dict(arrowstyle="->", lw=0.8, color="#333333"), fontsize=8.3)

    ax1.axhline(0.0, color="#666666", lw=0.7, ls=":")
    ax1.set_xlabel(r"Coupling $\lambda$ along free-Ramsey fiber $(u,v)=(9/50, 9/400)$")
    ax1.set_ylabel(r"Signed imaginary coherence $\mathrm{Im}\,z_s$")
    ax1.set_title(r"(a) Fiber degeneracy broken by causal sign $s=\pm 1$")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.94)
    ax1.set_xlim(0.281, 0.373)
    ax1.set_ylim(-0.22, 0.29)

    A0, B0 = ramsey_coeffs(0.75)
    u_p1 = (0.30 ** 2) * (2.0 * 0.50 + 1.0)
    v_p1 = (0.30 ** 2) * 0.25
    u_p2 = ((1.0 / 3.0) ** 2) * (2.0 * 0.31 + 1.0)
    v_p2 = ((1.0 / 3.0) ** 2) * 0.2025
    m_ramsey_1 = math.exp(-(A0 * u_p1 + B0 * v_p1))
    m_ramsey_2 = math.exp(-(A0 * u_p2 + B0 * v_p2))
    ev1 = bell_events_from_blocks(bell_blocks(0.30, 0.50, 0.25, "original"), 0.96, "YZ")
    ev2 = bell_events_from_blocks(bell_blocks(1.0 / 3.0, 0.31, 0.2025, "original"), 0.96, "YZ")
    p_ppp_1 = ev1[6]
    p_ppp_2 = ev2[6]
    diff_bell = abs(p_ppp_1 - p_ppp_2)

    labels = [
        r"Free Ramsey" + "\n" + r"$m(3/4)$",
        r"Causal break" + "\n" + r"$\mathrm{Im}\,z_+$",
        r"Causal break" + "\n" + r"$|\mathrm{Im}\,z_-|$",
        r"Stopped Bell" + "\n" + r"$P(\mathrm{ppp},\mathrm{YZ}^-)$",
    ]
    p1_vals = [m_ramsey_1, z_p1.imag, -z_m1.imag, p_ppp_1]
    p2_vals = [m_ramsey_2, z_p2.imag, -z_m2.imag, p_ppp_2]
    x = np.arange(len(labels))
    width = 0.34
    ax2.bar(x - width / 2, p1_vals, width, color="#2b6cb0", edgecolor="#1a365d", lw=0.6, label=r"$P_1 = (3/10, 1/2, 1/4)$")
    ax2.bar(x + width / 2, p2_vals, width, color="#dd6b20", edgecolor="#7b341e", lw=0.6, hatch="///", label=r"$P_2 = (1/3, 31/100, 81/400)$")
    ax2.annotate("Exact tie\n(0.730532)", xy=(0, m_ramsey_1), xytext=(0.48, m_ramsey_1 + 0.08),
                 ha="center", fontsize=8.0, color="#222222",
                 arrowprops=dict(arrowstyle="->", lw=0.8, color="#444444"))

    # Zoomed inset for stopped Bell P(ppp, YZ-) split (0.26681 vs 0.26508)
    ax_ins = ax2.inset_axes([0.56, 0.42, 0.40, 0.28])
    ax_ins.bar([0, 1], [p_ppp_1, p_ppp_2], width=0.58, color=["#2b6cb0", "#dd6b20"], edgecolor=["#1a365d", "#7b341e"], hatch=["", "///"], lw=0.6)
    ax_ins.set_ylim(0.2638, 0.2682)
    ax_ins.set_xticks([0, 1])
    ax_ins.set_xticklabels([r"$P_1$", r"$P_2$"], fontsize=7.2)
    ax_ins.set_yticks([0.265, 0.267])
    ax_ins.tick_params(axis="y", labelsize=6.8)
    ax_ins.set_title(rf"$\Delta_{{\mathrm{{YZ}}^-}} = {diff_bell:.5f}$", fontsize=7.5, pad=2.5)
    ax_ins.spines["top"].set_visible(False)
    ax_ins.spines["right"].set_visible(False)

    ax2.set_xticks(x)
    ax2.set_xticklabels(labels)
    ax2.set_ylabel("Coherence amplitude / outcome probability")
    ax2.set_title("(b) Ramsey degeneracy vs. causal-break & Bell splits")
    ax2.set_ylim(0, 0.96)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.94)

    fig.tight_layout(w_pad=2.2, rect=(0.0, 0.03, 1.0, 1.0))
    save_both(fig, "fig1_ramsey_ambiguity_and_causal_break")


def make_fig2_cutoff_bounds() -> None:
    """Fig 2: Exact rational Duhamel B_K decay and certified Weyl vs K=16 Fock error bounds."""
    ks = list(range(4, 25))
    b_vals = [float(exact_duhamel_cutoff_bound(k)) for k in ks]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.05))

    ax1.semilogy(ks, b_vals, "o-", color="#1f4e79", lw=1.8, ms=4.5, label=r"Uniform Duhamel bound $B_K$")
    b16 = float(exact_duhamel_cutoff_bound(16))
    ax1.axhline(b16, color="#2f855a", lw=1.2, ls="--", label=r"$K=16$ cutoff ($0.01168$)")
    ax1.scatter([16], [b16], color="#2f855a", s=65, zorder=5)
    ax1.annotate(r"$K=16$: $0.01168$", xy=(16, b16),
                 xytext=(10.2, 0.0028), arrowprops=dict(arrowstyle="->", lw=0.8, color="#2f855a"),
                 fontsize=8.5, color="#1c4532")
    ax1.set_xlabel(r"Total-number cutoff $K$")
    ax1.set_ylabel(r"Half-trace error bound $B_K$ (log scale)")
    ax1.set_title(r"(a) Exact Duhamel tail decay across shells")
    ax1.set_xticks(range(4, 25, 2))
    ax1.set_ylim(2e-4, 1.35)
    ax1.grid(True, which="major", alpha=0.25, lw=0.6)
    ax1.legend(loc="upper right", frameon=True, framealpha=0.94)

    # Panel (b): Infinite-bath Weyl polytope certificates (original vs swapped timing)
    # alongside separate fixed-parameter uniform K=16 rational Fock Choi bound (0.027603).
    cats = [
        "Complete\n" + r"$\frac{1}{2}\|\Delta\|_\diamond$",
        "Bell 8-cell\nanalog TV",
        "40-bit TV\n" + r"$(+4\times 2^{-40})$",
        "Fixed-param $K=16$\nFock Choi",
    ]
    orig_env = [0.033892297103, 0.046090140885, 0.046090140889]
    swap_env = [0.035357047207, 0.047554890989, 0.047554890993]
    k16_fock_uniform = 0.027602916940

    x3 = np.arange(3)
    w = 0.34
    ax2.bar(x3 - w / 2, orig_env, w, color="#2b6cb0", edgecolor="#1a365d", lw=0.6, label=r"Weyl polytope: original $(2/3, 3/4, 1/2)$")
    ax2.bar(x3 + w / 2, swap_env, w, color="#90cdf4", edgecolor="#1a365d", lw=0.7, hatch="///", label=r"Weyl polytope: swapped $(3/4, 2/3, 1/2)$")
    ax2.bar([3.0], [k16_fock_uniform], w * 1.15, color="#48bb78", edgecolor="#1c4532", lw=0.7, hatch="..", label=r"Fixed-param uniform $K=16$ Fock Choi")

    def fmt_up4(val: float) -> str:
        return f"{math.ceil(val * 1e4 - 1e-12) / 1e4:.4f}"

    for xi, ov, sv in zip(x3, orig_env, swap_env):
        ax2.text(xi - w / 2, ov + 0.0010, fmt_up4(ov), ha="center", va="bottom", fontsize=7.3)
        ax2.text(xi + w / 2, sv + 0.0010, fmt_up4(sv), ha="center", va="bottom", fontsize=7.3)
    ax2.text(3.0, k16_fock_uniform + 0.0010, fmt_up4(k16_fock_uniform), ha="center", va="bottom", fontsize=7.3, color="#1c4532")

    ax2.set_xticks(np.arange(4))
    ax2.set_xticklabels(cats)
    ax2.set_ylabel("Certified half-diamond / TV upper bound")
    ax2.set_title(r"(b) Certified process & finite-$K$ error bounds")
    ax2.set_ylim(0, 0.068)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.94, fontsize=7.4)

    fig.tight_layout(w_pad=2.2)
    save_both(fig, "fig2_cutoff_bounds_and_channel_error")


def make_fig3_local_field_microcausality() -> None:
    """Fig 3: R x S^1 Klein-Gordon field profile and spacelike vs timelike phase contrast."""
    beta, L, p_mix = kg_field_parameters()

    # Exact endpoint=False grid N=1920 divisible by 160, 40, 6, and 2:
    # dx = L/1920 => a_half = 12*dx = L/160 exact, side-lobe shift = 320 = L/6 exact, antipodal = 960 = L/2 exact.
    N = 1920
    xs = np.linspace(-L / 2.0, L / 2.0, N, endpoint=False)
    dx = L / N
    a_half = 12 * dx
    box = np.where(np.abs(xs) <= a_half + 1e-15, 1.0 / (2.0 * a_half), 0.0)
    # Center-shifted circular self-convolution on S^1 avoids edge truncation
    box_fft = np.fft.fft(np.fft.ifftshift(box))
    conv4 = np.fft.fftshift(np.real(np.fft.ifft(box_fft ** 4))) * (dx ** 3)
    shift_pts = N // 6
    prof0 = (1.0 - p_mix) * conv4 + 0.5 * p_mix * (np.roll(conv4, shift_pts) + np.roll(conv4, -shift_pts))
    area = float(np.sum(prof0) * dx)
    prof0 /= area
    prof_anti = np.roll(prof0, N // 2)

    x_plot = np.append(xs / L, 0.5)
    prof0_plot = np.append(prof0, prof0[0])
    prof_anti_plot = np.append(prof_anti, prof_anti[0])

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.05))

    ax1.plot(x_plot, prof0_plot, lw=2.0, color="#1f4e79", label=r"Probe $A$ profile ($x=0$)")
    ax1.plot(x_plot, prof_anti_plot, lw=2.0, ls="--", color="#b22222", label=r"Antipodal probe $B$ ($x=\pm L/2$)")
    R_frac = 1.0 / 6.0 + 1.0 / 40.0
    ax1.axvspan(R_frac, 0.5 - R_frac, color="#ccece6", alpha=0.65, label=r"Spacelike gap ($\Delta x_{\mathrm{gap}} \approx 0.6556 > 2/5$)")
    ax1.axvspan(-0.5 + R_frac, -R_frac, color="#ccece6", alpha=0.65)
    for xb in (-0.5 + R_frac, -R_frac, R_frac, 0.5 - R_frac):
        ax1.axvline(xb, color="#2c7a7b", lw=0.7, ls=":")
    ax1.annotate("", xy=(0.5 - R_frac, 2.3), xytext=(R_frac, 2.3),
                 arrowprops=dict(arrowstyle="<->", lw=1.0, color="#234e52"))
    ax1.text(0.25, 2.45, r"$\Delta x_{\mathrm{gap}}$", ha="center", va="bottom", fontsize=8.0, color="#234e52")

    ax1.set_xlabel(r"Normalized circle coordinate $x / L$")
    ax1.set_ylabel(r"Normalized smearing density $\psi(x)$")
    ax1.set_title(r"(a) Compactly supported $C^2$ probes on $\mathbb{R} \times S^1$")
    ax1.set_xlim(-0.5, 0.5)
    ax1.set_ylim(-0.12, max(prof0) * 1.44)
    ax1.legend(loc="upper center", frameon=True, framealpha=0.95, fontsize=7.6)

    m1_tl = kg_run_mode_sum(1, 2.0 / 3.0, 0.75, False)["phase_rad"]
    m160_tl = kg_run_mode_sum(160, 2.0 / 3.0, 0.75, False)["phase_rad"]
    m1_sl = kg_run_mode_sum(1, 0.2, 0.2, True)["phase_rad"]
    m160_sl_ub = kg_run_mode_sum(160, 0.2, 0.2, True)["phase_tail_upper"]

    labels = [
        "Timelike co-located\n" + r"$|\Phi_{AB}|$ (rad)",
        "Spacelike antipodal\n" + r"$|\Phi_{AB}|$ (rad)",
    ]
    two_mode_vals = [abs(m1_tl), abs(m1_sl)]
    x = np.arange(len(labels))
    w = 0.34
    ax2.bar(x - w / 2, two_mode_vals, w, color="#c53030", edgecolor="#742a2a", lw=0.6, hatch="///", label=r"Two-mode reduction ($M=1$)")
    ax2.bar([0 + w / 2], [abs(m160_tl)], w, color="#2b6cb0", edgecolor="#1a365d", lw=0.6, label=r"Local KG field ($M=160$)")
    ax2.bar([1 + w / 2], [1e-5], w, color="#2b6cb0", edgecolor="#1a365d", lw=0.6, alpha=0.25)
    ax2.annotate("", xy=(1 + w / 2, 1.1e-5), xytext=(1 + w / 2, 5.5e-5),
                 arrowprops=dict(arrowstyle="->", lw=1.2, color="#1a365d"))

    ax2.set_yscale("log")
    ax2.set_ylim(1e-5, 0.85)
    ax2.text(0 - w / 2, abs(m1_tl) * 1.18, f"{abs(m1_tl):.4f}", ha="center", va="bottom", fontsize=8.0)
    ax2.text(0 + w / 2, abs(m160_tl) * 1.18, f"{abs(m160_tl):.4f}", ha="center", va="bottom", fontsize=8.0)
    ax2.text(1 - w / 2, abs(m1_sl) * 1.25, f"{abs(m1_sl):.6f}\n(spurious)", ha="center", va="bottom", fontsize=7.8, color="#9b2c2c")
    ceil_tail = math.ceil(m160_sl_ub * 1e14) / 100.0
    ax2.text(1 + w / 2, 6.2e-5, rf"$< {ceil_tail:.2f}\times 10^{{-12}}$" + "\n(exact $= 0$)", ha="center", va="bottom", fontsize=7.8, color="#1a365d")

    ax2.set_xticks(x)
    ax2.set_xticklabels(labels)
    ax2.set_ylabel(r"Cross-probe phase $|\Phi_{AB}|$ (rad, log scale)")
    ax2.set_title("(b) Two-mode artifact vs. local-field microcausality")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.94)

    fig.tight_layout(w_pad=2.2)
    save_both(fig, "fig3_local_field_microcausality")


if __name__ == "__main__":
    make_fig1_ramsey_and_causal_break()
    make_fig2_cutoff_bounds()
    make_fig3_local_field_microcausality()
    print("Generated all 3 vector PDF (fonttype=42) + 300 DPI PNG figures cleanly.")
