# N. The spatial response needs an independent Weyl-squared coupling

## N1. A contact invisible to every FLRW mean fit

Consider a pure inhomogeneous lapse on the Einstein cylinder,

 ds²=-N(t,x)²dt²+gamma_ij dx^i dx^j.

For arbitrary time dependence of N, with fixed unit S³ metric,
R_0i0j=N Hess_ij N, R_00=N Delta N,
R_ij=2gamma_ij-N^-1 Hess_ij N, R=6-2N^-1 Delta N.
The electric Weyl tensor is
C_0i0j=(N/2) Hess_TF,ij N; its magnetic part is zero. Therefore

 C_abcd C^abcd=2N^-2 |Hess_TF N|²,
 integral sqrt(-g) C²=2 integral N^-1 |Hess_TF N|².      (N1)

Add gamma_W integral sqrt(-g)C² to the SAME real action.
For N=1+epsilon h(t)Y_m(x), integral Y_m²=1, and
ell=m²-1, Bochner's identity on S³ gives
||Hess_TF Y_m||²=(2/3)ell(ell-3). Consequently

 coefficient of epsilon²=(4/3)gamma_W ell(ell-3) integral h²,
 lapse Hessian=(8/3)gamma_W ell(ell-3) delta(t-t').      (N2)

For m=3 this is 320gamma_W/3. Choose h supported in the interior
of the time interval; S³ is closed. This is a bulk contact, not
an endpoint convention.

Weyl vanishes on ALL FLRW backgrounds, so both this action and
its first variation vanish there. Every homogeneous mean history
and all homogeneous tests leave gamma_W undetermined. Four-dimensional
conformal invariance transports (N1) to a²(t) times this cylinder.
Thus a homogeneous match cannot determine the full spatial response.

The known R² coupling contributes, on this reference-cylinder path,
lambda ell²/(9V) to the lapse Hessian, since
sqrt(-g)R²=36N-24Delta N+4N^-1(Delta N)².
Einstein-Hilbert and cosmological terms are linear in this lapse
on the path and add no quadratic lapse contact.
Nonstatic anomaly/Wess-Zumino contacts require the full conformal
transport and are not silently counted by this reference formula.

## N2. Exact density commutator response and its logarithmic local part

For the fixed-background vacuum density harmonic of SPATIAL_NOISE,
write weights w_n=C_m at n=m+1+2r.
Define chi(t)=+i theta(t)<[rho_m(t),rho_m(0)]> and
chi(z)=integral exp(izt)chi(t)dt, Im z>0. Then

 chi_K(z)=2 sum_n w_(n,K) n/(n²-z²).                    (N3)

A Hamiltonian perturbation +h rho has expectation response -chi;
the source effective-action Hessian, with Gamma_h=-<rho>, has +chi
before primitive contacts. This fixes the sign convention.

On the conformal Einstein cylinder the finite-mode phase-space
Hamiltonian for a pure lapse is exactly integral N T00 after spatial
integration by parts. It is linear in N, so there is no extra
primitive phase-space NN seagull here. A configuration-space
lapse contact must not be added again to this operator response.

The frequency-dependent subtraction is absolutely and locally
uniformly convergent in the upper half-plane:

 chi(z)-chi(0)=2C_m z² sum_n 1/[n(n²-z²)]
 =C_m[psi(a)-psi(a-z/2)/2-psi(a+z/2)/2],
 a=(m+1)/2.                                            (N4)

The unsubtracted static part diverges logarithmically. For m=3,
with the ACTUAL finite field-mode cutoff (including its 2/3 edge),

 chi_K(0)=C_3[H_K-1-1/(3K)].

A single covariant Weyl coefficient cancels the universal log because
C_m/[(8/3)ell(ell-3)]=n_s/(960V).
Choose explicitly the harmonic-number finite scheme

 gamma_(W,K)=gamma_R-n_s H_K/(960V).                    (N5)

The m=3 density row then has the finite limit

 chi_ren(z)=320gamma_R/3+
 C_3[-1+psi(2)-psi(2-z/2)/2-psi(2+z/2)/2].              (N6)

Using log K instead would shift the finite constant by Euler's
constant. These two schemes are not silently identified.
gamma_R remains an independent finite physical coupling.

For z=iy, the omitted subtracted sum has absolute bound
C_3 y²[1/(12K³)+1/(8K²)]. The residual static edge is C_3/(3K).
The certificate supplies an outward enclosure from these bounds
and a separate high-precision digamma regression.

## N3. Scope of this closure

The stationary conformal density susceptibility, its explicit local
renormalization and a previously invisible finite coupling have been
identified. This does not invert the gravitational response operator,
supply the full finite-initial-time CTP boundary blocks, or complete
the scalar/vector/tensor metric system. SCALAR_RESPONSE shows why
even the other commutator rows need their own contact bookkeeping.

Primary comparison: Fröb et al., https://arxiv.org/abs/1301.5261,
independent C² and R² gravitational terms and conformal transformation.
Their order-reduced semiclassical de Sitter stability result is not
a theorem about our unreduced joint quantum model or closed-S³ data.
