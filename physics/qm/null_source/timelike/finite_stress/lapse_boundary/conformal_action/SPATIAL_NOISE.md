# K. A full conformal-field scalar noise sector on the Einstein universe

## K1. Conditional background and definition by time smearing

This section concerns n_s independent real conformal massless scalar
fields in their conformal vacuum on the unit Einstein universe
ds²=-dt²+dOmega_3². It is a fixed-background QFT calculation.
It is not the unconditional stress of quantum geometry plus the
interacting three-field apparatus.

Let real S³ harmonics Y_kr have eigenvalue -(k²-1), degeneracy k²,
and unit L² norm; V=2pi². Expand q with frequencies k.
The vacuum-subtracted improved density is

 T00=:1/2(pi²+|grad q|²+q²)-Delta(q²)/6:.

For spatial f the pair-creation coefficient is

 b_ij(f)=[(k-l)² integral fY_iY_j
                    +(1/3) integral (Delta f)Y_iY_j]/(8sqrt(kl)).  (K1)

Consequently a real time test g gives

 Var T(g,f)=2n_s sum_ij |b_ij(f)|² |g_hat(k+l)|².        (K2)

It is defined as the L² vacuum limit of finite mode cutoffs.
No sharp-time full stress operator is applied to the vacuum first.
All source density/pressure correlations come from this one stress.

For f smooth and M_f=||f||infinity+||Delta f||infinity/12,
Cauchy-Schwarz and degeneracy sums give

 Var <=n_s M_f²/192 sum_(n>=2) n^5(n²-1)|g_hat(n)|²
     <=n_s M_f² ||g^(5)||1² (zeta(3)-zeta(5))/192.       (K3)

The squared L² norm of the mode-K omitted vector is at most
n_s M_f² ||g^(5)||1²/[384(K+1)²]. Thus g in W^(5,1)
with compact support suffices; a C-infinity assumption is not needed.

## K2. Exact harmonic contraction and positive spatial noise

For one normalized real harmonic Y_m the Gaunt contraction is

 sum_(r,s)|integral Y_m Y_kr Y_ls|²=kl/(mV)

when |k-l|<=m-1, k+l>=m+1 and k+l=m+1 mod 2, and zero otherwise.
This follows from the S³ addition kernel and the SU(2) character product
(or the equivalent Gegenbauer product), with the displayed L²
normalization. Writing d=k-l, the finite arithmetic sum is

 sum_(d=-(m-1),step2)^(m-1)[d²-(m²-1)/3]²
                 =4m(m²-1)(m²-4)/45.

Thus the COMPLETE field result for each harmonic is

 Var T(g,Y_m)=C_m sum_(r>=0)|g_hat(m+1+2r)|²,
 C_m=n_s(m²-1)(m²-4)/(360V).                            (K4)

The m=1 and m=2 vacuum fluctuations vanish. For m=3,
C_3=n_s/(9V)>0. This is a spatially nonconstant scalar harmonic,
not the already matched homogeneous constraint charge.

For arbitrary f in H²(S³), real compactly supported g in L² whose
support diameter is less than pi, the spectral result yields

 Var <= n_s pi ||g||2²/(720V)
             [||Delta f||2²-3||grad f||2²]
     = n_s pi ||g||2²/(480V)||Hess_TF f||2².            (K5)

The low harmonics have zero coefficient, so the form is nonnegative.

## K3. An explicit compact smooth-enough test and exact finite cutoff

Let b_delta=delta^-1 1_[-delta/2,delta/2] and g=b_delta^{*6}.
It has integral one, support diameter 6delta, is C4 and W^(5,1),
and g_hat(omega)=sinc(omega delta/2)^6.
It is NOT claimed C-infinity. Its exact norms obey

 ||g||2²=655177/(1663200 delta), ||g^(5)||1<=32/delta^5.

If 6delta<pi, Poisson summation / period-pi Parseval gives

 Var T(g,Y_3)=C_3[pi*655177/(3326400 delta)
                            -1/2-sinc(delta)^12].       (K6)

For a field-mode cutoff K>=2, put s_j=sinc(j delta)^12. Direct
pair counting, including the incomplete final shell, gives

 Var_K=C_3[sum_(j=2)^(K-1)s_j+(2/3)s_K],
 Var-Var_K=C_3[(1/3)s_K+sum_(j>K)s_j]
 <=C_3[(1/3)min(1,(Kdelta)^-12)+1/(11delta^12 K^11)].    (K7)

The coefficient 2/3 is required; dropping the last shell silently
would change the finite-cutoff statement. The numerical certificate
uses delta=1/600, a normalized conformal-time/spatial-harmonic
smearing. Its RMS is not a relative geometry error or a laboratory
noise level.

## K4. The entire scalar stress block, with cross correlations

For m>=3, let ell=m²-1 and decompose the vacuum fluctuations

 T00=rho_m Y_m,
 T0i=j_m nabla_i Y_m,
 Tij=(rho_m/3)gamma_ij Y_m
             +pi_m[nabla_i nabla_j Y_m+(ell/3)gamma_ij Y_m].

Tracelessness and conservation on this background imply

 j_m=-rho_m'/ell,
 pi_m=[rho_m+3rho_m''/ell]/[2(ell-3)].                  (K8)

For the creation phase exp(+int), the coefficient vector is
v_n=(1,-in/ell,[1-3n²/ell]/[2(ell-3)]).
Therefore the Wightman block <T_i(t)T_j(t')> is

 C_m sum_n conjugate(v_n,i) v_n,j exp[-in(t-t')].        (K9)

Each spectral matrix is the positive outer product u_n u_n*,
u_n=conjugate(v_n). The symmetrized noise is N_ij(t,t')=Re W_ij(t,t').
The density-only L² time-test extension in (K5) does not automatically
supply the momentum/shear domain; their extra time derivatives must
be included. The chosen six-box test is regular enough for the
fixed-m scalar block in (K9).
Density, momentum, pressure and scalar anisotropic stress are not
independent noises. Vector and transverse tensor sectors are not
computed here.

On a prescribed conformal FLRW geometry, connected covariant stress
components transport with a(u)^-2 a(v)^-2; orthonormal density
components with a(u)^-4 a(v)^-4. The anomaly is a c-number on that
fixed background and drops out of connected noise. This fact does
not identify a fixed-background kernel with a joint quantum-geometric
kernel; PROJECTED_NOISE supplies an explicit bounded bridge.

Primary background comparison: Cho and Hu,
https://arxiv.org/abs/1407.3907, exact Einstein-universe conformal
two-point function and noise-kernel transformation. The harmonic
sums and cutoff identities here are derived explicitly for our
declared smearing and normalization.
