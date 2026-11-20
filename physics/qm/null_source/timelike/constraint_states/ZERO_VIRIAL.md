# The actual zero-mode quantum floor and its variable-volume extension

## Actual state, not a newly chosen covariance

Use the accepted unfiltered state in its common de-sheared seed frame:
[Qj,Pk]=i delta_jk, v=Var(Pj)=x0/4,
Var(Qj)=1/(4v), Cov(Qj,Pj)=0.
Each coherent component has Q mean zero and momentum mean
sqrt(K2)(y,z), K2=2*pi^2*M2. The radial distribution has mean
L=1+sqrt(3)/4. No uniform angle or vanishing overall momentum mean is
required. The covariance specification and order of preparation are the
frozen ones, not a new boost applied after a differently ordered shear.

Set S=P1^2+P2^2 and
D0=sum_j(Qj Pj+Pj Qj)/2. For one centered pure Gaussian with a momentum
displacement m, Weyl ordering gives
\[
 (D_j^2)_W=q^2p^2+1/4,\qquad
 \langle D_j\rangle=0,\quad {\rm Var}D_j=1/2+m^2/(4v).
\]
Summing both independent centered components and averaging the common
radial labels therefore gives exactly
\[
 \langle S\rangle=2v+K2 L,\qquad
 {\rm Var}D_0=1+K2 L/(4v).
\]
A common subsequent canonical shear Q=Qseed+beta P is retained by using
D0=D-beta S. It is not reset physically.

## Fixed-radius additive constraint

The complete static proper-time source Hamiltonian is
H=Ec+S/(2A^3)+H_high. The nonzero-mode and c-number terms commute with D0.
For every normal joint extension with an independent G commuting with the
source algebra, on the weak commutator domain,
\[
 [H+G,D_0]=-iS/A^3.
\]
Robertson then yields
\[
 \boxed{{\rm Var}(H+G)\ge
 { (2v+K2L)^2\over4 A^6[1+K2L/(4v)]}>0.}
\]
This bound does not assume a positive generator G or independent source
and geometry states. It is an explicit lower bound on FQ/4, not a
calculation of the exact infinite-dimensional QFI optimum.

Dividing by V^2=(2*pi^2*A^3)^2 gives the corresponding proper energy-density
constraint variance in this additive model. The saved interval uses the
frozen actual source parameters, not their midpoint. A finite positive
floor is not an observed gravitational fluctuation or a universal precision
limit for relational observables.

## Genuine geometry-dependent coefficient

The candidate canonical free-zero-mode constraint has the form
\[
 C=C_0+\tfrac12\hat a^{-3}S,\quad K=\tfrac12\hat a^{-3}S\ge0 .
\]
Assume a>0, its inverse volume strongly commutes with matter, and C0
commutes with the zero-mode dilation group. All additional P-dependent
interactions must be differentiated explicitly; being P-only is NOT
enough to commute with D0. For finite moments and the legitimate weak
commutator form,
\[
 {\rm Var}C\,{\rm Var}D_0\ge\tfrac14\langle \hat a^{-3}S\rangle^2 .
\]
If the full joint state's radius support obeys 0<a<=a_max and its source
marginal is the same actual state, replace A in the preceding bound by
a_max. This does not require independence of a and S.

There is also an exact form-domain exclusion. Let S_lambda=exp(-i lambda D0)
and require the self-adjoint constraint's Hermitian form c and the kinetic
form k to share a dilation-invariant domain, with the identity
\[
 c(S_\lambda u,S_\lambda v)
 =c(u,v)+(e^{-2\lambda}-1)k(u,v)
\]
valid there. For psi in ker C with finite k(psi,psi), insert
u=S_lambda^dagger psi, v=psi. Both c terms vanish, so
k(S_lambda^dagger psi,psi)=0 for lambda !=0.
The covariance of K^(1/2) under dilations and strong continuity as
lambda tends to zero imply k(psi,psi)=0. Positive inverse volume and the
absence of a normal zero-momentum eigenvector then give psi=0.
Normal mixed strong solutions are excluded under the same hypotheses.

This last proof is conditional on the actual self-adjoint extension and
dilation domain. A formal commutator alone does not establish that domain,
and boundary terms can invalidate it. Physical-inner-product solutions,
clock conditioning, new zero-mode interactions, or a different constraint
algebra are not covered. GRAVITY_CONTRACT.md states the next domain
responsibilities rather than pretending this is a full quantum-GR theorem.
