# Finite-slice matter data, their true embedding derivatives, and the ultraviolet gate

This is a constructive next step inside the ORIGINAL two-field minimal
massless action. It provides an actual family of matter Cauchy states
for declared smooth prescribed geometries and computes the boundary
canonical map. It does not yet solve the coupled Einstein/CTP initial
constraints or specify a quantum gravitational density.

There are two separate calculations. Section 1 differentiates the
already constructed normal annulus state under an actual static time
embedding. Sections 2-6 change the initial geometric jets and transport
one legal past state by the exact Klein-Gordon equation. The static
energy ledger is not silently carried into the second calculation.

## 1. An actual normal-density embedding derivative

For the rank-two state (68), the shell N=0 and N=2 sectors are orthogonal
and each branch has the SAME total-energy characteristic profile W.
Write H=H_s and Ebar=E_c+E_* on the static background. In each branch,
\[
 (H-Ebar)\psi_N=\sigma x_N(P)\psi_N,\quad
 \langle x_N\rangle=0,\quad\langle x_N^2\rangle=\mu_2 .
\]
The complete source evolves as rho(t)=exp(-itH) rho exp(itH); it need
not be stationary even though its stress mean is static.

An initial proper-time advance has the trace-class derivative
\[
 {d\rho(t)\over dt}\bigg|_{0}=-i[H,\rho],\qquad
 \|[H,\rho_\pm]\|_1=2\sigma\sqrt{\mu_2}.
\tag{91}
\]
For a pure branch, restrict the commutator to the orthonormal span of
psi and (H-Ebar)psi/(sigma sqrt(mu2)); its two singular values are
sigma sqrt(mu2). Orthogonal shell blocks add with weights 1-p and p,
giving (91), without a Gaussian approximation.

The bare trace distance along this SAME static free history is exactly
\[
 D_{\rm tr}(\rho_\pm(t),\rho_\pm(0))
       =\sqrt{1-|W(\sigma t)|^2}
       \le |t|\sigma\sqrt{\mu_2}.
\tag{92}
\]
Each pure branch has the same overlap modulus; the orthogonal blocks
again add. The inequality follows from two independent copies X,Y of
the w^2 law and 1-cos(z)<=z^2/2. At the example sigma=epsilon2/100 and
proper time |t|<=2A this is STRICTLY less than 1/50, since mu2<1/3.
It controls a bare source state on the declared static source window,
not the complete apparatus or a changed metric.

At the initial density kernel, independent forward/backward advances
are -iH rho dt_plus and +i rho H dt_minus. In a constant-a lapse
description the relative propagation depends on the proper elapsed-time
difference s, so
\[
 F(s)=e^{-iEbar s}W(\sigma s).
\]
The centered log begins -sigma^2 mu2 s^2/2; its fourth cumulant is
sigma^4(mu4-3mu2^2). All odd centered cumulants vanish.
For an anchored time diffeomorphism, delta N=f' with endpoints fixed,
s=0. A nonzero relative elapsed time is an endpoint displacement,
not a pure anchored gauge transformation. In lapse coordinates the
restricted Hamiltonian N H_s is linear in N; this does not remove the
contact terms of a g00 variation or a changing initial embedding.

Under an explicitly DECLARED stochastic extension reproducing this
commuting energy law, the old zero density-response row would require
X=0 almost surely. In fact X has a continuous w^2 density and sigma>0,
so that requirement fails without assuming Gaussian noise.
The finite residual law is exactly
Pr(|R0|<=r)=integral_(|x|<=r V/sigma) w(x)^2 dx.
This is not a derivation of a quantum Dirac-constraint operator.

Crucially, sigma is not a weak-noise parameter for the complete tensor:
(73) has pressure terms of order sigma^0. The sigma->0 family has no
normal limiting bare state and has diverging Q/dilation spreads.
Neither an implicit-function theorem about a normal sigma=0 state
nor a sqrt(sigma) metric expansion with all source components shrinking
is justified by the small density variance alone.

## 2. A genuine smooth past-to-slice state construction

Choose one C-infinity cutoff chi with chi=0 for eta<=-1 and chi=1 for
eta>=-1/4. Fix four real numbers h0,b0,c0,d0 and set, on a finite
neighborhood of eta=0 and its entire past,
\[
 u(\eta)=\chi(\eta)
  \left(h_0\eta+\tfrac12 b_0\eta^2+\tfrac16 c_0\eta^3
                         +\tfrac1{24}d_0\eta^4\right),\qquad
 a(\eta)=A e^{u(\eta)} .
\tag{93}
\]
For example chi can be made from the standard smooth step
s(x)=r(x)/(r(x)+r(1-x)), r(x)=exp(-1/x) for x>0 and zero otherwise,
with x=4(eta+1)/3. It is identically one near the initial slice.
The metric is smooth and positive, has a static past, and fixes a(0)=A.
Its conformal Hubble value is h(0)=h0; the other jets are specified once.

Let q_k=a phi_k for k>=2, omega_k=sqrt(k^2-1), and
\[
 h=a'/a,\qquad {\cal V}=a''/a=h'+h^2,\qquad
 q_k''+(\omega_k^2-{\cal V})q_k=0 .
\]
The symbol calV is an effective mode potential, not the spatial volume V.
Starting from the static positive-frequency mode at eta=-1, define its
EXACT continuation by the Volterra equation
\[
 v_k(\eta)={e^{-i\omega_k(\eta+1)}\over\sqrt{2\omega_k}}
 +\int_{-1}^{\eta}{\sin[\omega_k(\eta-s)]\over\omega_k}
                    {\cal V}(s)v_k(s)\,ds .
\tag{94}
\]
This is an exact linear initial-value problem on every finite smooth
window, not a new numerical ODE run or a finite adiabatic replacement.

Use the same original normal zero-mode density and selected finite k=2
NOON/thermal source, and the static vacuum for k>=3 in the static past.
Propagate them with this ONE exact field evolution. Positivity, the CCR
and the Wronskian are preserved. Hadamard propagation preserves the
ultraviolet singularity; the finite zero/shell changes are smooth.
The zero mode is transported by its conserved original canonical P,
with phi_z'=P/a^2, not reset at a later slice. Thus this is an actual
legal matter Cauchy-state family with a specified preparation history.

The prescribed past curve chi and its jets remain new state-selection
inputs. They have not been shown to satisfy the Einstein equations or
to arise from an autonomous local controller. The construction solves
the matter-state legality problem for that declared geometry, not the
missing total-source constraint.

## 3. Exact positive covariance and its universal high-frequency terms

The Wronskian v v*'-v' v*=i implies v never vanishes. Define
\[
 \Omega_k={1\over2|v_k|^2}>0,\qquad
 v_k'=(-i\Omega_k-\Omega_k'/(2\Omega_k))v_k .
\tag{95}
\]
This is an exact amplitude-phase description of (94).
It obeys
\[
 \Omega^2=\omega^2-{\cal V}
     -{\Omega''\over2\Omega}
     +{3(\Omega')^2\over4\Omega^2}.
\]
The smooth static-past construction has the all-order high-frequency
asymptotic expansion, whose first terms are
\[
 \Omega=\omega-{{\cal V}\over2\omega}
       +{{\cal V}''-{\cal V}^2\over8\omega^3}
       +O(\omega^{-5}),\quad
 {\Omega'\over2\Omega}=-{{\cal V}'\over4\omega^2}
       +O(\omega^{-4}).
\tag{96}
\]
These are asymptotic coefficients of the exact state, not a claim that
a fixed finite WKB order is Hadamard.

On the initial slice a=A, use the SAME raw canonical pair when comparing
to the old static preparation:
\[
 q=A\phi,\qquad p_{\rm raw}=\pi_\phi/A=q'-h_0q .
\]
For a high-mode vacuum put c=h0+Omega'/(2Omega). Its real symmetrized
covariance in this pair is
\[
 C_{\rm raw}=
 \begin{pmatrix}
 1/(2\Omega)&-c/(2\Omega)\\
 -c/(2\Omega)&(\Omega^2+c^2)/(2\Omega)
 \end{pmatrix},\qquad \det C_{\rm raw}=1/4 .
\tag{97}
\]
It is positive and exactly satisfies the pure-state uncertainty relation.
Finite occupied/non-Gaussian modes are transported separately by the
same exact symplectic evolution; they do not change the ultraviolet test.

The chosen geometry gives
calV0=b0+h0^2,
calV0'=c0+2h0 b0,
calV0''=d0+2b0^2+2h0 c0.
These coefficients expose which initial geometric jets already enter
the required state data. Higher symbol coefficients need higher jets;
four numbers alone do not specify the full Hadamard state.

## 4. Why adding initial expansion cannot keep the old raw state for free

The old static oscillator convention is
b_omega=(sqrt(omega) q+i p_raw/sqrt(omega))/sqrt(2).
Relative to the pure high-mode state (97), its antilinear coefficient is
\[
 \beta_{\rm raw}={\omega-\Omega-i c\over2\sqrt{\omega\Omega}},\qquad
 |\beta_{\rm raw}|^2={(\omega-\Omega)^2+c^2\over4\omega\Omega}.
\tag{98}
\]
Equations (96)-(98) yield
\[
 |\beta_{\rm raw}|^2=
 {h_0^2\over4\omega^2}
 +{h_0^2{\cal V}_0/8+{\cal V}_0^2/16-h_0{\cal V}_0'/8
     \over\omega^4}
 +O(\omega^{-6}).
\tag{99}
\]
There are 2 k^2 real oscillators per shell for the two fields.
If h0 is nonzero,
\[
 2k^2|\beta_{\rm raw,k}|^2\longrightarrow h_0^2/2 ,
\]
so the Shale Hilbert-Schmidt sum diverges. The pure quasifree
ultraviolet representation in this raw identification is not unitarily
equivalent to the old static Fock representation. The finite NOON/zero
modifications cannot repair the divergent high-mode sum.

Independently, keeping the complete old raw marginal would keep its
old W2 Cauchy data. Their mixed covariance lacks the required
-h0/(2 omega) term, so it does not have the new geometry's Hadamard
short-distance form. Thus the proposed operation "add nonzero initial
Hubble while retaining the old complete raw matter state" fails its
stated state-regularity gate.

The Shale statement here is about the explicitly specified pure
quasifree high-mode family and its representations. It is NOT asserted
as a blanket theorem that every non-Gaussian normal old-Fock state is
impossible. Normality of arbitrary states with infinite particle-number
expectation must not be inferred merely from a particle-number sum.

If h0=0 but calV0 is nonzero, the leading coefficient instead is
\[
 |\beta_{\rm raw}|^2={{\cal V}_0^2\over16\omega^4}
                         +O(\omega^{-6}) .
\]
The Shale sum converges. However, the old positive proper-time static
excitation energy has the two-field contribution
\[
 \sum_{k\ge3}2k^2{\omega_k\over A}|\beta_k|^2
 ={{\cal V}_0^2\over8A}\sum_{k\ge3}{1\over k}
                         +\hbox{a convergent remainder},
\tag{100}
\]
which diverges logarithmically. Finite particle number, finite old
Hamiltonian energy and finite new renormalized stress are different
requirements. This is NOT a divergence of the new geometry's Hadamard
RSET: that RSET uses the new equation, geometry and covariant subtraction.

## 5. A legal canonical transport also has an action boundary term

The rescaled pair (q,p_q=q') is a different, metric-dependent Cauchy
identification. The exact smooth-potential dynamics in this pair has
beta_k=O(k^-2) on finite windows; with degeneracy k^2 its Shale sum
converges. This is the standard compact-three-dimensional result.
It allows a common normal Fock evolution for the declared q description.

It does not preserve the old raw pair. The difference is visible in
the SAME original action, per real mode or at a finite cutoff:
\[
 S_{\rm raw}={1\over2}\int[(q'-hq)^2-\omega^2q^2]d\eta
 = {1\over2}\int[q'^2-(\omega^2-{\cal V})q^2]d\eta
                     -[hq^2/2]_{\eta_i}^{\eta_f}.
\tag{101}
\]
Thus p_raw=q'-hq and p_q=q'. For wavefunctions at a finite cutoff,
\[
 \Psi_{\rm raw}(q,\eta)=e^{-ih(\eta)q^2/2}\Psi_{\rm bulk}(q,\eta).
\]
The initial CTP density kernel transforms with
\[
 \rho_{\rm raw}(q_+,q_-)=
 e^{-ih_+q_+^2/2}\rho_{\rm bulk}(q_+,q_-)
 e^{+ih_-q_-^2/2}.
\tag{102}
\]
These factors cancel the corresponding initial action boundary phases
on the two branches. Final phases cancel only with the declared common
endpoint identification. Varying h0 therefore varies the initial
density/embedding factors, as well as the dynamical mode data.
Holding the old raw density fixed while discarding (101)-(102) is not
a covariant CTP comparison.

The displayed shear formula is exact at a finite cutoff. When h0 is
nonzero, its infinite product is not a unitary on the old raw Fock
space, precisely as (99) shows. It must not be presented as such.
A full infinite-field common phase, representation, boundary Ward
prescription and gravity/matter cross block remain to be constructed.
The shear is one explicit boundary contribution, not the complete
metric derivative of the state: Omega and its past-history dependence
also vary.

## 6. What this actually supplies to the next coupled problem

The candidate now has more than an assigned PSD covariance:

1. One fixed, smooth prescribed geometry with stated initial jets and
   a stated common past.
2. A positive, Hadamard matter state obtained by exact KG transport of
   one past density, including the legal non-Gaussian finite modes.
3. Exact finite-slice covariance, its controlled ultraviolet asymptotic
   terms, and an explicit test of the chosen canonical representation.
4. Actual initial-time density derivatives and the action's canonical
   boundary phase, with their precise finite-cutoff/infinite-field scope.

It still lacks the coupled geometry-matter-device boundary density,
the finite-slice density/momentum constraint solution, the complete
initial CTP cross blocks, and a causal interval solving the total
equations. The prescribed past curve cannot be signed off as a
self-consistent preparation merely because its matter state is legal.
The static total-energy concentration theorem applies on its static
endpoint contract; a new embedding or Hamiltonian must be recomputed,
not used to claim that physical energy has vanished.

The next constructive calculation should insert (94)-(102), with one
declared preparation/controller action, into the finite-slice full
constraint map. Both the geometric jets and the quantum state are then
varied together. The response must retain the initial boundary terms
and the complete ultraviolet prescription before a residual is called
a physical geometry error.

## 7. Primary-source scope

The high-frequency and representation arguments use standard results,
not a new quantization principle derived from Core.

- Cortez, Mena Marugan, Olmedo and Velhinho, Phys. Rev. D 83 (2011) 025002,
  https://arxiv.org/abs/1101.2397, especially the S3 beta asymptotic and
  degeneracy-weighted square-summability criterion.
- The same authors, Phys. Rev. D 86 (2012) 104003,
  https://arxiv.org/abs/1202.6330: time-dependent canonical scalings and
  momentum choices cannot generally be treated as unitary re-labelings.
- Junker and Schrohe, Ann. Henri Poincare 3 (2002) 1113-1181,
  https://arxiv.org/abs/math-ph/0109010, Sections 5-6: compact-surface
  Cauchy-state construction and the distinction between finite adiabatic
  order and Hadamard. Its massive construction is not blindly applied
  to the massless zero mode here; that finite sector is handled separately,
  and (94) propagates the already Hadamard high-mode state.
- Juarez-Aubry, Kay, Miramontes and Sudarsky,
  https://arxiv.org/abs/2205.11671: the general surface-Hadamard
  semiclassical initial-value statement is presented as a conjecture.
- Meda, Pinamonti and Siemssen, https://arxiv.org/abs/2007.14665:
  their proved local existence theorem is for spatially flat
  cosmologies with a massive scalar and compatible regular initial data.
  The author's 2026 review, https://doi.org/10.1007/s10773-026-06339-9,
  retains that flat cosmological setting; it is not a theorem supplying
  the present closed massless full-tensor or stochastic boundary problem.

This is an analytic construction and asymptotic/symbolic certificate,
not a numerical integration of all modes or a machine-formal proof.
No predecessor scientific checker, mode ODE or geometry ODE is run.
