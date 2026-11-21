# O. All finite-cutoff scalar causal commutator rows and equal-time contacts

Use the explicit creation convention in SPATIAL_NOISE:
v_n=(1,-in/ell,b(n)), b(z)=[1-3z²/ell]/[2(ell-3)],
and W_ij(t)=sum_n w_n conjugate(v_n,i)v_n,j exp(-int).
Weights are the actual finite-mode contractions, including edge shells.

For chi_ij(t)=+i theta(t)<[T_i(t),T_j(0)]> and Im z>0,

 chi_ij(z)=sum_n w_n[
   conjugate(v_n,i)v_n,j/(n-z)+
   conjugate(v_n,j)v_n,i/(n+z)].                        (O1)

Put chi=2sum_n w_n n/(n²-z²),
M1=2sum_n w_n n, M3=2sum_n w_n n³.
Direct rational algebra gives the COMPLETE scalar commutator block:

 chi_rhorho=chi,
 chi_rhoj=-iz chi/ell, chi_jrho=+iz chi/ell,
 chi_jj=(z²chi+M1)/ell²,

 chi_rhoPi=chi_Pirho=b(z)chi-3M1/[2ell(ell-3)],
 chi_jPi=+iz chi_rhoPi/ell,
 chi_Pij=-iz chi_rhoPi/ell,

 chi_PiPi=b(z)²chi+
   [9M3/ell²+(-6/ell+9z²/ell²)M1]/[4(ell-3)²].         (O2)

Every row is an exact finite sum; the equal-time contact polynomials
are forced by differentiating a RETARDED distribution. Multiplying
the density response by transfer factors alone misses them.

For m=3 and field-mode cutoff K>=2,

 M1=C3(2K²+2K/3-4),
 M3=C3(4K⁴+8K³/3+4K²-16).                             (O3)

They include the 2/3 final shell. The apparent positive powers of z
in (O2) cancel in the large-|z| expansion of the exact finite sums,
which provides an independent consistency check.

These contacts are fixed by the stress commutator. They are NOT
the additional metric-variation seagulls, finite boundary contacts
or gravitational counterterms. The lapse-lapse reference row is
treated in WEYL_RESPONSE; other metric source columns must still be
derived from the same retained-lapse action and initial density
operator. Therefore (O2) is an exact causal source block, not a
complete renormalized Einstein-CTP Hessian or its inverse.

The noise and the causal block share the same w_n and v_n. Their
correlations cannot be independently chosen to engineer cancellation.
