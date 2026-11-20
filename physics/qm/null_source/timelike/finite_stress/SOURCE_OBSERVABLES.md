# What is preserved, and the actual normal derivatives

## 1. A physical measurement is not automatically a canonical compression

P commutes strongly with H and its spectral projection Pi. Its complete
joint spectral law is exactly preserved by the initial isometry and by
the subsequent unitary history. For bounded source operators commuting
with P, V* (I tensor O) V=O. On a prescribed classical background this
includes the free shift-invariant zero-mode stress algebra. Attaching the
same independent Hadamard ultraviolet sector would preserve the
prescribed-background stress/influence comparison previously proved.

Q_j=i partial_(P_j), however, generally does not preserve Pi. Its safe
physical measurement is the normalized compressed POVM
E_Q^phys(B)=Pi E_Q(B) Pi. For physical psi in D(Q),
\[
 \int q^2\,d\langle\psi,E_Q^{phys}(q)\psi\rangle
 =\|Q\psi\|^2=\|\Pi Q\psi\|^2+\|(1-\Pi)Q\psi\|^2.
\tag{30}
\]
One cannot silently replace this by the square of a self-adjoint
compressed canonical Q. The last norm is a nonnegative extra term.

The encoded joint effects V O V* recover the original source records on
the code range. A normalized measurement on the whole physical space
requires an additional effect on its orthogonal complement. Such effects
are joint geometry-source measurements, not a claim that the bare local
source operator is unchanged.

## 2. Hadamard scope

On any fixed globally hyperbolic classical metric, changing finitely many
mode correlations by finite moments changes the two-point distribution
by a smooth function. If the unchanged ultraviolet sector was Hadamard,
that fixed-background property persists. This is the usual microlocal
Hadamard criterion (Radzikowski, CMP 179 (1996), DOI 10.1007/BF02100096).

The evolving quantum-volume model has not supplied a single classical
Klein-Gordon bidistribution, a covariant local subtraction scheme, or
the nonzero-mode backreaction. Its normality and zero-mode moments do not
establish a quantum-geometry Hadamard/RSET theorem.

## 3. The actual first and second time derivatives

On the common finite-support smooth-P core,
\[
 \dot P_j=0,\qquad \dot Q_j=i[H,Q_j]=P_j/v,
 \qquad \ddot Q_j=iP_j[H,v^{-1}].
\tag{31}
\]
These expressions extend as the indicated quadratic forms/moments on
the constructed regular state. They are actual derivatives of the fixed
new Hamiltonian, not derivatives obtained by adjusting a parameter root.

For the old static radius A, the corresponding free zero-mode first
derivative was P_j/A^3. The squared discrepancy summed over both modes is
exactly
\[
 \mathcal D_1^2=
 \int p_{\rm old}(P)|P|^2
       \langle(v^{-1}-A^{-3})^2\rangle_{\Omega(P)}\,d^2P.
\tag{32}
\]
It is finite but has not been computed as a small number for the spectral
filter state. Equality of the P law alone cannot set (32) to zero.

The inverse-volume commutator has off-diagonal entries
\[
 [H,v^{-1}]_{n,n+1}=-{\gamma\over\sqrt{n(n+1)}}.
\]
Its Schur bound is
\[
 \|[H,v^{-1}]\|\le\gamma(1/\sqrt2+1/\sqrt6).
\]
Therefore the sum of the squared second-derivative norms is bounded by
gamma^2(1/sqrt2+1/sqrt6)^2 <P^2>. This supplies a finite normal-derivative
domain and an explicit comparison quantity, not agreement with old
static Klein-Gordon data.

## 4. A bounded expansion observable

A declared symmetric reduced expansion operator is
\[
 {\cal H}={1\over3}v^{-1/2}i[H,v]v^{-1/2}
         ={i\gamma\delta\over3}(S^*-S),
 \qquad \|{\cal H}\|\le{1\over2V_0\ell}.
\tag{33}
\]
The sign depends on the shift convention; with (S u)_n=u_(n-1) the
displayed sign is used. Its physical compression has the same bound.

A bounded expansion observable and finite stress do not show that its
mean and variance define a classical metric, or that the original
Einstein/AE normal residuals vanish. The next comparison must use (31),
the actual mean geometry and the local stress prescription together.

## 5. Finite moments do not automatically supply the Ward identity

There is a concrete ordering test. In the normal clock representation
put S=P^2, E_+=qv+p+S/(2v), and define the classical volume-work
coefficient P_cl=V0*pressure=-q+S/(2v^2).
The exact Heisenberg derivatives satisfy
\[
 \dot E_++\tfrac12\{P_{\rm cl},\dot v\}
 ={S\over4}[v^{-1},[v^{-1},\dot v]].
\tag{34a}
\]
The right-hand side is generally nonzero. Its upper adjacent entry is
i S gamma/[4(n(n+1))^(3/2)], and its fiber norm is at most
S gamma[2^(-3/2)+6^(-3/2)]/4. The original P4 moment makes the
residual's second moment finite.

This follows directly from dot(v^-1)=-v^-1 dot(v) v^-1. It is an
obstruction to automatically importing this classical symmetric work
formula into the declared quantum operators. It neither disproves every
possible covariant quantum stress prescription nor supplies a uniquely
justified replacement pressure. A compatible variational stress/Ward
prescription must be derived before calling these finite moments the
original AE/RSET source.
