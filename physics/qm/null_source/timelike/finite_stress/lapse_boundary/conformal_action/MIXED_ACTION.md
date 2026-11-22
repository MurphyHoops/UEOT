# R. A required curvature--matter term produces a genuine mixed boundary row

## R1. Retain the lapse and the physical scalar coordinates

The heat coefficient in SIGMA_COUNTERTERMS requires the operator
class R Ric_target(partial X,partial X). Select a real finite
representative

 S_mix=alpha integral sqrt(-g) R Ric_AB(X)
                               partial X^A.partial X^B.   (R1)

Its finite alpha is declared input, not fixed by the old FLRW fit.
Running/required operator content does not force nonzero alpha_R at
every chosen scale: a finite condition may set it to zero there.
The nonzero mixed-rank example below concerns an action member with
alpha nonzero. These rows use PHYSICAL target coordinates X.
Use D=N^-1 partial_eta, kappa=Du, chi_g=Dkappa,
v=DX, J=Ric_AB(X)v^Av^B, W=chi_g+kappa²+1, c=6alpha V.
In physical target coordinates the homogeneous density is

 N L_mix=-N c W J.                                     (R2)

For d=1-k_c² the explicit target tensor is
Ric_chichi=k_c k_c''/d+(1+k_c²)k_c'²/(2d²),
Ric_phiphi=Ric_psipsi=k_c'²/(2d), Ric_phipsi=-k_c''/2.
Thus J=Ric_chichi v_chi²+k_c'²(v_phi²+v_psi²)/(2d)
-k_c''v_phi v_psi. Ric is not globally positive, even though G is.

No time-dependent source rescaling is used. This is a genuine
geometry/source interaction from a local covariant action.

The exact Ostrogradsky boundary momenta and energy are

 P_kappa=-cJ,
 Pi_A=-cW J_vA,
 P_u=c(DJ-2kappa J),
 E_mix=c[kappa DJ-(2chi_g+3kappa²+1)J].                 (R3)

The boundary form is
Theta_mix=P_u delta u+P_kappa delta kappa+Pi_A delta X^A.
After integrating the lapse derivatives,

 Gamma_N=-E_mix,
 Gamma_u/N=c[2chi_g J+2kappa DJ-D²J],
 Gamma_A/N=c[D(W J_vA)-W J_XA].                         (R4)

These obey the OFF-SHELL identity
D E_mix+kappa Gamma_u/N+v^A Gamma_A/N=0.
Matter exchange terms are essential: the mixed stress is not
separately conserved on arbitrary solutions of the bare scalar
action. The full sum of action rows has the full on-shell Ward law.

rho_mix=E_mix/(Va⁴), p_mix=(E_mix+Gamma_u/N)/(3Va⁴)
are the corresponding projections. Positivity is not assumed for
this renormalized improvement term.

## R2. The source-dependent endpoint cannot become a free carrier charge

Integration by parts gives the exact finite-boundary identity

 integral N L_mix
 =-c[kappa J]+integral N[c kappa DJ-c(kappa²+1)J].        (R5)

Here
DJ=(nabla_C Ric_AB)v^Cv^Av^B+2Ric_AB v^A a^B,
a=Dv+Gamma_target(v,v).
The transported bulk contains matter accelerations. The endpoint
variation includes delta v and delta X, not just delta kappa.
In the transported representative the source-acceleration momentum
is +c kappa J_vA, consistent with the same boundary form.

Thus this is genuinely a source-containing mixed row; it is not
the independent tensor-factor charge excluded for a fixed bare
source marginal. But it is not a freely adjustable compensator:
its bulk dynamics, canonical momenta, lapse contacts and boundary
state all change together.

The velocity-dependent, generally unbounded endpoint is NOT yet a
bounded quantum phase. A common extended phase space, operator
domain and transported initial density kernel are still required.
A finite classical identity is not a proof of its full-field
quantum implementation or renormalized boundary limit.

## R3. Explicit lapse-derivative contacts at a finite jet

Let w=u', z=u'', M=N', and B_X=Ric_AB(X)X'^A X'^B.
Before any lapse variation, the density is

 -c B_X[(z+w²)/N³-wM/N⁴+1/N].                          (R6)

This determines every primitive contact by ordinary jet
differentiation. In particular,

 S_NN=-c B_X[12(z+w²)/N⁵-20wM/N⁶+2/N³],
 S_N,M=-4c B_X w/N⁵,  S_MM=0,
 S_N,z=3c B_X/N⁴,     S_z,X'_A=-c (B_X)_X'_A/N³,
 S_M,X'_A=c w(B_X)_X'_A/N⁴.                            (R7)

After distributional integrations by parts these contribute
derivatives of delta functions and the corresponding endpoints.
Setting N=1 before varying would erase required columns.
For interior compactly supported lapse variations the COMPLETE
Euler NN contact (measure d eta) simplifies to

 (c/N)[4kappa DJ-(2+8chi_g+12kappa²)J] delta(eta-eta').

The primitive N' derivative contacts cancel only after this full
Euler variation. The mixed source column is
c[(2chi_g+3kappa²+1)-kappa D] composed with
[J_XA+J_vA D]; D acts on its coefficients as well.

At an endpoint F=kappa J=w B_X/N³:
F_N=-3F/N, F_NN=12F/N²,
F_X'_A=w(B_X)_X'_A/N³,
F_N,X'_A=-3w(B_X)_X'_A/N⁴.
Multiply by -c and the endpoint orientation. These are genuine
lapse--source endpoint columns, not yet a quantum initial mixed block.

## R4. The old critical reduction is not automatically inherited

Add the quartic matter density NVF4 and the old critical geometric
bulk, whose chi_g² coefficient is zero. At fixed (u,kappa,X) the
extended velocity Hessian in (chi_g,v) is

 H_vel = [ 0   b^T ],
         [ b    M  ],
 b=-c J_v=-12alpha V Ric v,
 M=Va²G+VF4_vv-cW J_vv.                                (R8)

If M is positive definite and b nonzero on a specified local domain,

 det H_vel=-det(M)b^T M^-1 b !=0,

and completing the square gives one negative and dim(X) positive
directions. This is a local rank statement for the displayed
EXACT finite action representative. It does not by itself prove
a global ghost, a quantum spectrum, normal-state existence or a
no-go for a completed theory.

Crucially b=O(alpha), so its Schur complement is O(alpha²).
A STRICT first-order/one-loop EFT truncation does not control that
determinant. Order reduction, higher-order terms and degenerate
completions can change the degree-of-freedom inference. What is
already required at O(alpha) is the new mixed canonical/boundary
row (R3)-(R7); silently keeping the old bare critical row is invalid.

A concrete comparison prevents a universal exclusion: add an
independent beta integral sqrt(-g) R_mu nu Ric_AB
partial^mu X^A partial^nu X^B. Homogeneously it is -3beta V chi_g J.
Choosing beta=-2alpha cancels chi_g J exactly and gives the
covariant combination -2alpha G_mu nu Ric_AB partial^mu X^A
partial^nu X^B, with homogeneous bulk -6alpha V(kappa²+1)J.
The (chi_g,v) b block vanishes for this combination.
That finite coefficient relation is not selected by the present
one-loop calculation. Full four-dimensional multi-scalar degeneracy
is not proved. The remaining kappa-dependent source kinetic metric
still does not restore the old single fK propagation.

## R5. An additional operator-ordering obligation for noncommuting energies

Even if a controlled reduction yields a time-dependent self-adjoint
T(u), the new coefficients generally give [T(u),T(v)] nonzero.
For the selected normal form C=R(P_u+h)R with kappa=R² and h
commuting with R at each time, the exact expansion is

 C=kappa P_u-i R R_u+kappa h
  =kappa P_u-(i/2)kappa_u-(i/2)[R,R_u]+kappa h.          (R9)

The commutator term is Hermitian and vanishes only in the previous
commuting case. A new T cannot simply be inserted into the old
scalar connection formula. The actual reduction, common domain,
initial mixed block and full lapse/contact equations must first be
derived from the completed action.

This closes the requested CLASSIFICATION for this explicit new
counterterm: its boundary/constraint row really contains source
variables. It does not yet close the normal joint preparation or
four-dimensional Einstein-CTP evolution demanded by physical unification.
