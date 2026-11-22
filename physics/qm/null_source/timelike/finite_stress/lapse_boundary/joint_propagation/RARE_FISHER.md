# Actual C9 Fisher information: a measurement proof retaining failure

## F1. Claim, parameter and input

For the actual fixed-ordering C9 preparation with the declared regular
low input, let ell=log K, A_K=(ell/K)H_bulk,K(u_i),
M=kappa^-1, I_j=integral |g|^2 kappa^-j and
sigma^2=I_2-I_1^2>0. The frozen rescaled parameter family
exp(-is A_K)rho_C9,K exp(is A_K) has

    liminf F_Q,K^(s)/log K >=2(I_2-I_1^2)>0.             (F.1)

This is also the initial rescaled derivative information of the actual
nonautonomous family. In the original initial-u parameter,

    liminf (log K/K^2) F_Q,K^(u) >=2(I_2-I_1^2).

It is not an all-time nonautonomous QFI theorem or an instrument
calibration. Unlike the mixed-state variance bound, (F.1) follows from
an explicit measurement with its rare probability and failure retained.

## F2. Actual odd-sector graph estimate

For each isotropic one-odd-mode shell-K label j, let V_j encode the
actual no-rare-phase odd branch from H_low into the complete bulk
Hilbert space. With the same regular normal low/reference input tau,
the uniform-label estimates are

    ||(H_K/K-M)V_j sqrt(tau)||_2 ->0,
    ||(H_K/K-M)T_K V_j sqrt(tau)||_2 ->0,

where T_K=exp(i b_K kappa^2/2) is the actual C9 rare current phase.

Here is the full-generator estimate behind these statements. In the
exact adiabatic frame, the occupied source energy is
Omega_K/(K kappa)->kappa^-1. The original low/scalar remainder divided
by K vanishes. On the fixed one-particle input, the complete geometric
operator has norm O(K) from its Gamma^2 term, so alpha_K/K times it
is O(1/ell). The actual branch scalar phase has bounded profile
derivatives uniformly in the label. For the rare T_K, b_K=O(ell^3).
The extra covariant-linear term divided by K has norm
O(ell^2/sqrt K); the quadratic term is O(ell^5/K).
All tend to zero. This uses the actual regular low moment budget and
the full source/geometry connection; trace distance alone would not
give this graph estimate.

## F3. A bounded effect on the physical system

Exactly,

    V_j* M V_j=I_1 I_low, V_j* M^2 V_j=I_2 I_low.

Define the isometries

    W_j=(M-I_1)V_j/sigma,
    Z_j=(V_j+i W_j)/sqrt 2,
    E_j=Z_j Z_j*.

V_j and W_j have orthogonal ranges, so E_j is a bounded projection.
The no-T probability is exactly 1/2 for every shared low density,
without access to a purification. Direct algebra gives

    V_j* [M,E_j] V_j=i sigma I_low.

For U=exp(-is A_K), the graph estimate therefore implies that this
branch's success derivative satisfies q'_K/ell->-sigma.
The rare T branch has derivative O(ell); its weight r_K=ell^-2 makes
its contribution negligible after division by ell. For the actual
current-repaired odd-sector mixture,

    q_K=1/2+O(r_K), q'_K/ell->-sigma,

uniformly in the shell label.

## F4. The complete three-outcome probability and Fisher information

The high-mode parity projections preserve the actual finite-K energy
space and the formal generator. Weak evolution uniqueness therefore
makes them exact invariants of the complete unitary; this is not just
a formal commutator assertion. Distinct one-odd-label sectors are
orthogonal, so the finite sum E=sum_j E_j is a projection with
E<=P_odd. The TOTAL odd probability p_K is constant under this
parameter variation, and p_K ell->1/2.

The three-outcome POVM

    {E, P_odd-E, I-P_odd}

has probabilities p_K q_K, p_K(1-q_K), 1-p_K. Its classical Fisher
information is exactly

    F_cl,K=p_K (q'_K)^2/[q_K(1-q_K)],
    F_cl,K/ell ->2 sigma^2.

The failure outcome has not been deleted, and no normalized
postselection is used. Quantum Fisher information is at least that
of this explicitly defined POVM, proving (F.1).

The effect depends on K and the declared preparation; it is a bounded
mathematical measurement on the physical completion. No uniform
energy-domain bound, local field probe, autonomous controller or
proper-time calibration is claimed. The result is for fixed ordering
and the actual C9 preparation; the ordering sweep and the separately
retuned high-rank hiding family do not automatically inherit it.

## F5. Relation to the other limits

RARE_PREPARATION proves trace distance of order 1/log K from C5 and
contractivity of every fixed bounded complete record. There is no
contradiction: (F.1) probes derivatives in a shrinking parameter
neighborhood through a cutoff-dependent rare-sector measurement.
SNAPSHOT_SPECTRUM separately proves a pure-C5 derivative-information
excess. Neither result turns the full Einstein--CTP source or apparatus
into a solved model.

The executable checks verify the exact isometry-range commutator,
the complete outcome Fisher algebra and the asymptotic coefficient.
The actual graph estimate, parity-domain invariance and information
inequality are the analytic proof F2-F4.
