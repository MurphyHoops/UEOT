#!/usr/bin/env python3
"""Generate publication-quality vector PDF and 300-DPI PNG figures."""
from __future__ import annotations

import math
from pathlib import Path
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from verify_standalone import (
    ramsey_coeffs,
    z_causal_break,
    bell_blocks,
    bell_events_from_blocks,
    exact_duhamel_cutoff_bound,
)

ROOT = Path(__file__).resolve().parent
FIG_DIR = ROOT / "figures"
FIG_DIR.mkdir(exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
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
    lams = np.linspace(math.sqrt(9.0 / 110.0), math.sqrt(27.0 / 200.0), 220)
    zs_plus_im = []
    zs_minus_im = []
    for lam in lams:
        n_cand = (u_fixed / (lam ** 2) - 1.0) / 2.0
        c_cand = v_fixed / (lam ** 2)
        zs_plus_im.append(z_causal_break(float(lam), n_cand, c_cand, +1).imag)
        zs_minus_im.append(z_causal_break(float(lam), n_cand, c_cand, -1).imag)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.1))

    ax1.plot(lams, zs_plus_im, lw=2.2, color="#1f4e79", label=r"$\mathrm{Im}\,z_{+}(\lambda)$ ($s=+1$)")
    ax1.plot(lams, zs_minus_im, lw=2.2, ls="--", color="#b22222", label=r"$\mathrm{Im}\,z_{-}(\lambda)$ ($s=-1$)")
    ax1.fill_between(lams, zs_minus_im, zs_plus_im, color="#d9e6f2", alpha=0.55, label=r"Signed causal-break gap")

    z_p1 = z_causal_break(0.30, 0.50, 0.25, +1)
    z_m1 = z_causal_break(0.30, 0.50, 0.25, -1)
    z_p2 = z_causal_break(1.0 / 3.0, 0.31, 0.2025, +1)
    z_m2 = z_causal_break(1.0 / 3.0, 0.31, 0.2025, -1)

    ax1.scatter([0.30, 1.0 / 3.0], [z_p1.imag, z_p2.imag], color="#1f4e79", zorder=5, s=42)
    ax1.scatter([0.30, 1.0 / 3.0], [z_m1.imag, z_m2.imag], color="#b22222", zorder=5, s=42)
    ax1.annotate(r"$P_1\,(\lambda=0.30)$", xy=(0.30, z_p1.imag), xytext=(0.289, z_p1.imag + 0.045),
                 arrowprops=dict(arrowstyle="->", lw=0.8, color="#333333"), fontsize=8.3)
    ax1.annotate(r"$P_2\,(\lambda=1/3)$", xy=(1.0 / 3.0, z_p2.imag), xytext=(0.336, z_p2.imag + 0.045),
                 arrowprops=dict(arrowstyle="->", lw=0.8, color="#333333"), fontsize=8.3)

    ax1.axhline(0.0, color="#666666", lw=0.7, ls=":")
    ax1.set_xlabel(r"Coupling $\lambda$ along exact Ramsey equivalence fiber $(u,v)$")
    ax1.set_ylabel(r"Signed imaginary coherence $\mathrm{Im}\,z_s$")
    ax1.set_title(r"(a) Fiber degeneracy broken by causal sign $s=\pm 1$")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.92)
    ax1.set_xlim(0.282, 0.372)
    ax1.set_ylim(-0.22, 0.29)

    # Right panel: Exact Ramsey free-decay tie m(3/4) vs causal-break vs stopped-Bell at eta=0.96
    A0, B0 = ramsey_coeffs(0.75)
    m_ramsey_1 = math.exp(-(A0 * u_fixed + B0 * v_fixed))
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
    p2_vals = [m_ramsey_1, z_p2.imag, -z_m2.imag, p_ppp_2]
    x = np.arange(len(labels))
    width = 0.34
    ax2.bar(x - width / 2, p1_vals, width, color="#2b6cb0", label=r"$P_1 = (3/10, 1/2, 1/4)$")
    ax2.bar(x + width / 2, p2_vals, width, color="#dd6b20", label=r"$P_2 = (1/3, 31/100, 81/400)$")
    ax2.annotate("Exact tie", xy=(0, m_ramsey_1), xytext=(0.45, m_ramsey_1 + 0.08),
                 ha="center", fontsize=8.0, color="#222222",
                 arrowprops=dict(arrowstyle="->", lw=0.8, color="#444444"))
    ax2.annotate(rf"$\Delta_{{\mathrm{{YZ}}^-}} = {diff_bell:.5f}$", xy=(3, p_ppp_1), xytext=(2.55, 0.39),
                 ha="center", fontsize=8.0, color="#222222",
                 arrowprops=dict(arrowstyle="->", lw=0.8, color="#444444"))

    ax2.set_xticks(x)
    ax2.set_xticklabels(labels)
    ax2.set_ylabel("Coherence amplitude / outcome probability")
    ax2.set_title("(b) Ramsey degeneracy vs. causal-break & Bell splits")
    ax2.set_ylim(0, 0.94)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92)

    fig.tight_layout(w_pad=2.2, rect=(0.0, 0.04, 1.0, 1.0))
    save_both(fig, "fig1_ramsey_ambiguity_and_causal_break")


def make_fig2_cutoff_bounds() -> None:
    """Fig 2: Exact rational Duhamel truncation bound B_K and half-diamond error budget."""
    ks = list(range(4, 25))
    b_vals = [float(exact_duhamel_cutoff_bound(k)) for k in ks]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.0))

    ax1.semilogy(ks, b_vals, "o-", color="#1f4e79", lw=1.8, ms=4.5, label=r"Uniform Duhamel bound $B_K$")
    b16 = float(exact_duhamel_cutoff_bound(16))
    ax1.axhline(b16, color="#2f855a", lw=1.2, ls="--", label=r"$K=16$ cutoff ($0.01168$)")
    ax1.scatter([16], [b16], color="#2f855a", s=65, zorder=5)
    ax1.annotate(r"$K=16$: $0.01168$", xy=(16, b16),
                 xytext=(10.5, 0.003), arrowprops=dict(arrowstyle="->", lw=0.8, color="#2f855a"),
                 fontsize=8.5, color="#1c4532")
    ax1.set_xlabel(r"Total-number cutoff $K$")
    ax1.set_ylabel(r"Half-trace error bound $B_K$ (log scale)")
    ax1.set_title(r"(a) Exact Duhamel tail decay across shells")
    ax1.set_xticks(range(4, 25, 2))
    ax1.grid(True, which="major", alpha=0.25, lw=0.6)
    ax1.legend(loc="upper right", frameon=True, framealpha=0.92)

    cats = [
        r"Complete" + "\n" + r"$\frac{1}{2}\|\Delta\|_\diamond$",
        r"Bell 8-cell" + "\n" + r"analog TV",
        r"40-bit" + "\n" + r"process TV",
        r"Integer $K{=}16$" + "\n" + r"solver gap",
    ]
    tight_env = [0.033892297103, 0.046090140885, 0.046090140889, 0.0276]
    conserv_env = [0.035357047207, 0.047554890989, 0.047554890993, 0.0276]
    x = np.arange(len(cats))
    w = 0.34
    ax2.bar(x - w / 2, tight_env, w, color="#2b6cb0", label=r"Tight envelope ($\gamma=0.391$)")
    ax2.bar(x + w / 2, conserv_env, w, color="#90cdf4", edgecolor="#1a365d", lw=0.7, label=r"Conservative ($\gamma=0.400$)")
    for xi, tv in zip(x, tight_env):
        ax2.text(xi - w / 2, tv + 0.0012, f"{tv:.4f}", ha="center", va="bottom", fontsize=7.5)
    ax2.set_xticks(x)
    ax2.set_xticklabels(cats)
    ax2.set_ylabel("Error / distinguishability bound")
    ax2.set_title(r"(b) Certified process bounds vs. $K{=}16$ solver")
    ax2.set_ylim(0, 0.064)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92)

    fig.tight_layout(w_pad=2.2)
    save_both(fig, "fig2_cutoff_bounds_and_channel_error")


def make_fig3_local_field_microcausality() -> None:
    """Fig 3: R x S^1 Klein-Gordon field profile and spacelike vs timelike phase contrast."""
    beta = math.sqrt(5.0) / 2.0
    L = 2.0 * math.pi / beta
    x1 = math.pi / 80.0
    sinc1 = math.sin(x1) / x1
    p_mix = 2.0 * (1.0 - 0.6 * math.sqrt(0.75) / (sinc1 ** 4))

    xs = np.linspace(-L / 2.0, L / 2.0, 1200)
    dx = xs[1] - xs[0]
    a_half = L / 80.0
    box = np.where(np.abs(xs) <= a_half, 1.0 / (2.0 * a_half), 0.0)
    conv4 = box.copy()
    for _ in range(3):
        conv4 = np.convolve(conv4, box, mode="same") * dx
    shift_pts = int(round((L / 6.0) / dx))
    prof0 = (1.0 - p_mix) * conv4 + 0.5 * p_mix * (np.roll(conv4, shift_pts) + np.roll(conv4, -shift_pts))
    prof0 /= np.trapezoid(prof0, xs)
    half_pts = len(xs) // 2
    prof_anti = np.roll(prof0, half_pts)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10.2, 4.0))

    ax1.plot(xs / L, prof0, lw=2.0, color="#1f4e79", label=r"Probe $A$ profile ($x=0$)")
    ax1.plot(xs / L, prof_anti, lw=2.0, ls="--", color="#b22222", label=r"Antipodal probe $B$ ($x=\pm L/2$)")
    R_frac = 1.0 / 6.0 + 1.0 / 40.0
    ax1.axvspan(R_frac, 0.5 - R_frac, color="#e6fffa", alpha=0.85, label=r"Spacelike gap ($\Delta x = 0.6556$)")
    ax1.axvspan(-0.5 + R_frac, -R_frac, color="#e6fffa", alpha=0.85)
    ax1.set_xlabel(r"Normalized circle coordinate $x / L$")
    ax1.set_ylabel(r"Normalized smearing density $\psi(x)$")
    ax1.set_title(r"(a) Compactly supported $C^2$ probes on $\mathbb{R} \times S^1$")
    ax1.set_xlim(-0.5, 0.5)
    ax1.set_ylim(-0.08, max(prof0) * 1.42)
    ax1.legend(loc="upper center", frameon=True, framealpha=0.95, fontsize=7.8)

    labels = [
        r"Timelike co-located" + "\n" + r"$\Phi_{AB}$ (rad)",
        r"Spacelike antipodal" + "\n" + r"$\Phi_{AB}$ (rad)",
    ]
    two_mode_vals = [0.163731618, 0.001330794]
    x = np.arange(len(labels))
    w = 0.34
    ax2.bar(x - w / 2, two_mode_vals, w, color="#c53030", label=r"Two-mode reduction ($M=1$)")
    ax2.bar(x + w / 2, [0.209161320, 1e-6], w, color="#2b6cb0", label=r"Local KG field ($M=160$)")
    ax2.set_yscale("log")
    ax2.set_ylim(1e-5, 0.85)
    ax2.text(0 - w / 2, 0.1637 * 1.18, "0.1637", ha="center", va="bottom", fontsize=8.0)
    ax2.text(0 + w / 2, 0.2092 * 1.18, "0.2092", ha="center", va="bottom", fontsize=8.0)
    ax2.text(1 - w / 2, 0.00133 * 1.25, "0.001331\n(spurious)", ha="center", va="bottom", fontsize=7.8, color="#9b2c2c")
    ax2.text(1 + w / 2, 2.2e-5, r"$< 2.49\times 10^{-12}$" + "\n(exact $= 0$)", ha="center", va="bottom", fontsize=7.8, color="#1a365d")

    ax2.set_xticks(x)
    ax2.set_xticklabels(labels)
    ax2.set_ylabel(r"Cross-probe phase $|\Phi_{AB}|$ (rad, log scale)")
    ax2.set_title("(b) Two-mode artifact vs. local-field microcausality")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92)

    fig.tight_layout(w_pad=2.2)
    save_both(fig, "fig3_local_field_microcausality")


if __name__ == "__main__":
    make_fig1_ramsey_and_causal_break()
    make_fig2_cutoff_bounds()
    make_fig3_local_field_microcausality()
    print("Generated all 3 vector PDF + 300 DPI PNG figures cleanly.")
