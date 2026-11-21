# A causal preparation-time obstruction and a bounded local witness

## 1. The actual localized contract

Use the common static spacetime ds^2=A^2(-deta^2+dOmega3^2).
All preparation interactions, controls and nonselective operations occur
inside the north-pole cap chi<=chi0 during -T<=eta<=0. The two protocols
have the same complete initial input (or at least the same restriction on
the protected exterior algebra). Operations are causal and localized, not
merely labelled as local because their output has a field interpretation.

The argument works on the full joint algebra. A localized scattering
automorphism, or an appropriate unital CP map, acts as identity on every
observable spacelike to the coupling region K. Thus it works for a fixed
initial target-apparatus state even if correlated. For such correlated
inputs one must not presume a reduced CPTP map on arbitrary target states.
The product-probe instrument formulas and this joint-algebra identity are
different statements. A precise local scattering formulation is
Fewster-Verch, arXiv:1810.06512, Proposition 3.1(b).

If delta=pi-chi0-T>0, choose a small causal diamond around the south pole,
center eta_c=delta/4, radius delta/8. Its latest time is 3delta/8 and every
spatial point is within delta/8 of the south pole. Its distance from the cap
exceeds T+3delta/8, so this entire diamond O is spacelike to K.
The two actual nonselective outputs must agree on A(O).

## 2. The desired global NOON states disagree on every such open region

Their smooth pressure-noise difference already suggests this, but an
explicit bounded Weyl observable avoids any stress self-adjointness issue.
Take a real test g supported in O and
W_lambda=W1(lambda g)W2(lambda g), of norm 1.
Let the k=2 displacement vector for each species be lambda zeta in C^d.
The exact selected-shell connecting matrix element is
\[
 \langle A_2|W_{\rm shell}|A_1\rangle
 ={e^{-\lambda^2\|\zeta\|^2}\lambda^4
                  |\sum_m\zeta_m^2|^2\over2d}.
\]
The reverse matrix element is the same. Thus
\[
 \boxed{\Delta\langle W_\lambda\rangle
 ={2c\over d}e^{-\lambda^2\|\zeta\|^2}\lambda^4
      |\sum_m\zeta_m^2|^2 F_R(\lambda g)}.
\]
F_R is the COMMON rest expectation, allowing both original zero modes to
be correlated with each other. Only the shell/rest product already present
in the specified preparation is used.

Choose g=h_t(eta-eta_c)h_x(x), with real even compact h_t of nonzero Fourier
component at omega and real h_x having a nonzero k=2 projection in O.
Then zeta=z r with nonzero real vector r and z!=0, so sum zeta_m^2!=0.
Strong continuity of Weyl operators in the normal rest state gives F_R(0)=1;
hence the boxed difference is nonzero for every sufficiently small nonzero
lambda. A phase-adjusted Hermitian part of W_lambda is also a bounded local
witness. No coincident stress product is used.

Consequently the two global target states cannot both be outputs of the
localized common-input preparation when T+chi0<pi:
\[
                  \boxed{T\ge\pi-\chi_0}
\]
is necessary. Equality is not excluded by this argument and is not an
existence theorem. The proper duration bound is A(pi-chi0).

## 3. Approximation also has a fixed-witness lower bound

Let actual outputs sigma_plus/minus agree on A(O). With trace distance
D=rho,sigma ->||rho-sigma||1/2 and
d_lambda=|Delta<W_lambda>|>0, duality gives
\[
 D(\rho_+,\sigma_+)+D(\rho_-,\sigma_-)\ge d_\lambda/2,\qquad
 \max_\pm D(\rho_\pm,\sigma_\pm)\ge d_\lambda/4 .
\]
This lower bound depends on the chosen exterior witness. No uniform
numerical approximation error is claimed as the uncovered region shrinks.

For the explicit cap example chi0=1/128 the necessary preparation duration
is more than 6.14 million times the old response window T_resp=1/(24A).
This compares causal model times, not laboratory seconds or an optimized
distributed protocol.

The obstruction concerns exact global target preparation, not merely local
noise engineering. Distributed apparatus, a longer common past, genuinely
different exterior initial resources, or selective postselection are
different contracts. Postselection may change conditional distant
statistics without signalling; it is not the nonselective output required
here. Thus the abstract global equal-energy gate is not already the former
short small-cap instrument.

If the preparation geometry itself changes, the joint-algebra causal-complement
statement remains the relevant criterion, but J(K) must be recomputed on
that common geometry. The numerical pi-chi0 bound is not transferred.
