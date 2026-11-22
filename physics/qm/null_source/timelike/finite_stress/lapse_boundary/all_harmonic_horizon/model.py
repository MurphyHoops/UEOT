"""Shared exact Funk-Hecke and rational helpers for the all_harmonic_horizon cohort."""
from __future__ import annotations
import sympy as sp
from mpmath import iv
from common import above, exact, require


def parse_rational(s: str) -> iv.mpf:
    if "/" in s:
        n_str, d_str = s.split("/")
        return exact(int(n_str)) / exact(int(d_str))
    return exact(int(s))


def exact_cap_khat(rho0_num: int, rho0_den: int, k_max: int) -> list[iv.mpf]:
    """Compute exact Funk-Hecke multipliers khat(1..k_max) via exact Chebyshev cosine expansion."""
    rho0 = exact(rho0_num) / exact(rho0_den)
    c0 = iv.cos(rho0)
    z = sp.Symbol("z")
    c_sym = sp.Symbol("c0")
    p = sp.Poly((z**2 + 1 - 2 * c_sym * z) ** 8, z)
    a_iv: dict[int, iv.mpf] = {}
    scale = exact(1) / exact(256)
    for j in range(9):
        coeff_c = sp.Poly(p.coeff_monomial(z ** (8 + j)), c_sym)
        val = exact(0)
        for (dc,), r_val in coeff_c.as_dict().items():
            val += (exact(int(sp.numer(r_val))) / exact(int(sp.denom(r_val)))) * (c0**dc)
        a_iv[j] = scale * val * (exact(1) if j == 0 else exact(2))

    def int_cos(n: int) -> iv.mpf:
        m = abs(n)
        return rho0 if m == 0 else iv.sin(exact(m) * rho0) / exact(m)

    def cap_moment(k: int) -> iv.mpf:
        total = exact(0)
        q = exact(1) / exact(4)
        for j, aj in a_iv.items():
            term = int_cos(k - 1 + j) + int_cos(k - 1 - j) - int_cos(k + 1 + j) - int_cos(k + 1 - j)
            total += aj * q * term
        return total / exact(k)

    norm_int = cap_moment(1)
    require(above(norm_int, 0), "Positive normalization integral")
    return [exact(1) if k == 1 else cap_moment(k) / norm_int for k in range(1, k_max + 1)]
