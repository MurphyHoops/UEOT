# JC22 — The retained controller changes the actual first-harmonic response

## The additional closure

For K=64 the actual total source, including the free X/Y fields and the entire interaction, has an invertible limiting eight-dimensional density/longitudinal-momentum mean response. The full autonomous finite-K mean map has a local inverse for sufficiently small positive g. It follows that some normal same-program actual preparations cancel all eight **total-source first-harmonic mean projections** of sufficiently small common codes, while retaining a positive complete mathematical probe record.

The control radius 1e-16 and target radius 5e-23 can be retained, as proved below. The coupling threshold remains existential. Taking eta=1e-13 and some 0<g<min(g_total,*(64),1e-40) gives the combined result; the specifically fixed g=1e-40 has not been proved below that threshold. The homogeneous clock density, higher spatial modes, operator-level constraints, geometry evolution, continuum renormalization and autonomous pointer remain open. “Eight projections” is not the complete Einstein system.

## 1. The controller response survives the small-coupling limit

At fixed K write
\[
 v_K=\langle\Phi_+^2\rangle_{\Omega}
 ={1\over2V_0}\sum_{k=1}^K{k^2\over\sqrt{k^2+1/5}},\quad c(t)=\cos2t.
\]
Let u_0=epsilon,u_1=zeta, h=sum u_j cF_j=sum u_j (b,b'). The leading controller mean corrections are
\[
 \langle Y_j\rangle={(\mathbf u_j\cdot Z)c\over g}
                         +g z_{j0}(t)+\cdots,\qquad
 \langle X\rangle={t\over g}+g\,\mathbf z_X(t)\cdot Z+\cdots .
\]
To first order in the program the exact finite-mode equations give
\[
 z_{j0}''+z_{j0}=-{v_K\over2}F_j,\qquad
 \mathbf z_X''+3\mathbf z_X
       =-{v_K\over2}c\sum_j\mathbf u_jF_j',
\]
with zero retarded initial data. These equations are for the leading coherent-frame coefficients, not an assertion that the full quantum controller remains classical.

The complete free-controller density/momentum coefficients are
\[
 \mathbf R_{\rm app}=\mathbf z_X'
       +\sum_j(c'z_{j0}'+cz_{j0})\mathbf u_j,\qquad
 \mathbf J_{\rm app}=\mathbf z_X
       +\sum_jc z_{j0}'\mathbf u_j .
\]
The actual tested charges are \(A_{\rm app}=V_0R_{\rm app}/4\) and
\(P_{\rm app}=3V_0J_{\rm app}/4\). Thus these terms are of order u, not g u. A controller mean correction of order g multiplies the clock/program mean of order 1/g.

A direct differentiation checks
\[
 R_{\rm app}'=-3J_{\rm app}
                   -{v_K\over2}\sum_j(cF_j)'\mathbf u_j .
\]
This is the appropriate leading exchange balance. It does not delete the general local projection residual of a spectral cutoff. The raw tadpole v_K is part of this specified Hamiltonian and grows like K^2. Normal-ordering it away would change the actuator Hamiltonian and its force; it cannot be omitted during this comparison.

## 2. An explicit full-rank controller matrix without a mode ODE run

Set a=sqrt(3), S=sin(a pi), C=cos(a pi). At T=pi parity of F_0,F_1 reduces the retarded integrals to four positive numbers:
\[
 U=\int b(s)[a\cos(as)-2\sin(as)\tan2s]\,ds,
\]
\[
 V=\int b(s)[(3+4\sec^22s)\cos(as)-2a\sin(as)\tan2s]\,ds,
\]
\[
 R=\int b(s){\cos s\over\cos2s}\,ds,\qquad
 Q=\int b(s)\left[{\cos s\over\cos2s}
             +{2\sin s\sin2s\over\cos^22s}\right]ds .
\]
The repeated two by two controller block is
\[
 J_{\rm app}={V_0v_K\over8}
 \begin{pmatrix}
 S U& C V+Q\\
 3(R-CU/a)&3SV/a
 \end{pmatrix}.                                                \tag{1}
\]
The time and longitudinal-momentum sign is the same one as
P=-partial_t A in JOINT_PREPARATION. In particular z_00(pi)=0,
z_00'(pi)>0, z_10'(pi)=0 and z_10(pi)>0.

Here is a fully analytic enclosure. Since
\(w(s)=\exp[-s^2/(1-s^2)]\le1-s^2\) on [-1,1], I>5/7 and the half-width of a is 1/10, the second moment of b=a*tilde a obeys
\[
 m_2=\int s^2b(s)\,ds
 \le2(1/10)^2 {4/15\over5/7}={14\over1875}.
\]
Let d=cos(.4)>0. Then
\[
 1-(3/2+4/d)m_2\le U/a\le1,\qquad
 1\le R\le1+2m_2/d,
\]
\[
 7-(21/2+12/d)m_2\le V\le3+4/d^2<8,
\]
\[
 1\le Q\le1+(2/d+4/d^2)m_2 .
\]
They follow directly from sin x<=x, cos x>=1-x^2/2, the support |s|<=.2 and normalization of b. Applying the unrounded interval bounds, rather than prematurely rounded decimal endpoints, gives for the inner matrix M in (1)
\[
 \det M=3[(U/a-CR)V+(CU/a-R)Q]>4.5,\qquad \|M\|_F<13.
\]
At K=64,
\[
 {V_0v_K\over8}\ge{130\over\sqrt{1.2}}>118,
 \qquad\|J_{\rm app}^{-1}\|<.0245.
\]
The independent matter-only block has norm below six by QUANTIFIED_PREPARATION. Therefore
\[
 J_{\rm total}=J_{\rm body}+J_{\rm app}
\]
is invertible by a Neumann estimate, since .0245 times 6 is below one, and
\[
 \boxed{\|J_{\rm total}^{-1}\|<.03.}                            \tag{2}
\]
The controller response is essential to (1)--(2); using the old body Jacobian as the total one would be incorrect.

## 3. Why this is a limit of actual total means

Use the high-order physical parametrix and energy-form estimates of ACTUATOR_MEANS. Every fixed-K total dipole/longitudinal charge is a uniformly bounded form of the positive total Hamiltonian. The full uniform form bound can be made explicit. Complete the
canonical local potential into positive squares as in CLOCK_ACTUATOR.
For any unit four-vector a, |Z_a|<=1 and |grad Z_a|<=1, so the
canonical density dipole is bounded by H_pos and the canonical current
dipole by the kinetic/gradient part of H_pos. The conformal body
improvement contributes
\[
 A_a^{\rm imp}=+\tfrac12\int Z_a(\phi^2+\psi^2),\qquad
 P_a^{\rm imp}=-\int Z_a\,\operatorname{sym}(\phi\pi_\phi+\psi\pi_\psi).
\]
With kappa=1-r=.8 the two absolute form bounds are
\[
 |A_{{\rm total},a}|\le(1+1/\kappa)H_{\rm pos}=9H_{\rm pos}/4,
 \quad
 |P_{{\rm total},a}|\le(1+1/\sqrt\kappa)H_{\rm pos}<9H_{\rm pos}/4.
\]
No uncontrolled massless X zero-mode coordinate is used in these bounds.

After the coherent controller displacement it has the expansion
\[
 g^{-2}a_{-2}(u)\mathbf1+g^{-1}L_u+Q_{\rm app}
                              +A_{\rm body}+V_{\rm int}.
\]
For these particular eight first-harmonic tests a_-2 is identically zero: the clock's classical stress is homogeneous, while every classical Y stress is an even quadratic in the four coordinates Z. Its integral against a first harmonic or its longitudinal gradient vanishes. This does not make the homogeneous or second-harmonic controller source small.

The centered reference has zero mean L_u. In
chi_N=chi_0+g chi_1+... the first finite contribution to the g^-1 term is
\[
 2\operatorname{Re}\langle\chi_0,L_u\chi_1\rangle .
\]
It is precisely the retained leading controller force/exchange response above. Deleting chi_1 would delete a finite physical source. All remaining terms and their first u derivatives are O(g), uniformly in a fixed small u ball. The endpoint interaction has the flat-profile estimate proved in ACTUATOR_MEANS. The N=7 energy-form interpolation controls the actual-state error. Hence the **actual total** mean map converges in C^1 to a smooth map whose derivative at zero is (2).

SO(4) gives F_total,g(0)=0 exactly. The control and target radii can
also be kept explicit, while the coupling threshold remains existential.

Write C_u(t,x)=<Phi_+^2> in the prescribed reference. Its symplectic
Dyson expansion gives a coefficient-wise majorant
\(v_K\exp(58\|u\|)\), since integral |h|<=29||u||. This is an estimate
on every coefficient, not a Taylor bound inferred only from a real-axis
norm inequality. The general spatial leading controller corrections solve
\[
 (\partial_t^2-\Delta+1)z_j=-F_j P_K C_u/2,\qquad
 (\partial_t^2-\Delta)z_X
       =-\tfrac12c\sum_jF_j'P_K[(\mathbf u_j\cdot Z)C_u].
\]
Here P_K is the same finite-mode orthogonal projector on every controller equation. It is an L2 contraction and commutes with the free propagators and first-harmonic projection, so the following bounds retain their stated constants.

The mass-one retarded energy bound controls z_j, dot z_j and grad z_j.
Only the first-harmonic part of z_X is used, with frequency sqrt(3);
its zero mode is not inverted. Let
B_sum=sum ||F_j||_1<144 and D_sum=sum ||F_j'||_1<4143, from the support
length .4 and CLOCK_ACTUATOR's sup bounds. Projecting all four axes,
including the Y gradient cross term, bounds the X eight-vector by
V_0 v_K D_sum ||u|| exp(58||u||), and the Y contribution by
(9/4)V_0 v_K B_sum ||u|| exp(58||u||). Since V_0<20 and v_64<55,
the coefficient constant is below 5e6; take the safe C_0=1e8.

The antipodal transformation makes the first-harmonic map odd in u.
For x=58||u||<.01, its coefficient-wise derivative remainder obeys
\[
 \|DF_{\rm app,lim}-J_{\rm app}\|
 \le C_0[(1+x)e^x-1-2x]<2C_0x^2.
\]
At r_0=1e-16 this is below 6.728e-21. The independent body derivative
remainder is at most 4.096e-9. Actual C1 convergence supplies some
g_total,*(64)>0 such that its additional derivative error is <=1e-7
on this same ball. Multiplication by the inverse bound .03 yields a
contraction below 3.2e-9. The target radius y_0=5e-23 is therefore
well inside the self-map margin. The actual program satisfies
||u_(g,eta)||<.016 eta^2 for the common code target.

This proves a definite target/control neighborhood and existence of a
positive coupling threshold. No numerical value of g_total,* is asserted.

## 4. Combine the inverse and the complete record on one actual state

Choose eta=10^-13 (or any smaller positive value) and a common code target in the proved y_0 ball. Choose one fixed 0<g<min(g_total,*(64),1e-40) and also require
\[
 C_{1,64}g+C_{2,64}g^2<d_{\rm ref}(\eta)/4 .
\]
For eta=1e-13 the stated g ceiling already implies this contrast inequality. For a smaller eta the displayed inequality is an additional requirement. Select g once; the resulting Hamiltonian stays fixed for all programs and both code signs.

For every such finite choice, the same actual program u_(g,eta) solves the total eight projections after either code sign. The same complete Gaussian instrument then has positive contrast at least d_ref/2. The reference contrast is bounded below by 2.70e-4 eta^2 at K=64. At eta=1e-13 the same uniform clock bounds give an actual gap above 2.69e-30. No apparatus outcome or failure sector is discarded. The eight means are matched at the encoding slice T=pi; their vanishing has not been propagated through the subsequent interval or through the readout.

This is an existence chain with genuine normal finite-mode joint states and one fixed autonomous Hamiltonian. It does not assign the new thresholds the old numerical values, and it does not bound its energy by the fixed-g example's upper bound. Its free controller stress and kinetic cost remain in the complete source.

## What has and has not closed

The earlier matter-only inverse is now extended to the retained total source in eight first-harmonic mean directions at K=64. The enormous zero harmonic fails the old background test, other harmonics and all operator constraints remain, and CLOCK_UV blocks the unmodified bare continuum gate. A physical unified solution requires the complete geometry, continuum total stress/noise and actual pointer, not only these eight means.

The large scale of J_app is the raw vacuum tadpole v_K of this specified
positive finite-K Hamiltonian. A future Wick/renormalized interaction
containing a compensating linear controller term changes or removes this
column and requires a new stability/phase/response proof. It is not a
scheme-independent continuum repair.
