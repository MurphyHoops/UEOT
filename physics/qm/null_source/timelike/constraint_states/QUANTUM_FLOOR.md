# A fixed quantum marginal has an irreducible additive constraint floor

## 1. Strong constraint versus a mean equation

Let H be the complete static source Hamiltonian and G an independent
self-adjoint geometric/reference generator. On the ordinary tensor product
take C=H tensor I + I tensor G. This is an explicitly proposed additive
quantum constraint, not a consequence of mean-SCE.

A normal joint density R with support in ker C is invariant under exp(-itC).
Taking the partial trace gives
\[
              e^{-itH}\rho e^{itH}=\rho .
\]
Thus an exact strong constraint requires a stationary source marginal.
The weaker condition Tr RC=0 does not give this conclusion.

For the original two noncompact zero modes H0=(P1^2+P2^2)/(2A^3), H0 has
purely continuous spectrum. There is no nonzero trace-class stationary
density operator on L2(R2): if a positive compact operator rho commuted with
every e^{-itH0}, any nonzero finite-dimensional eigen-subspace of rho would
be invariant under this unitary group and would contain an H0 eigenvector,
which does not exist. Adding the discrete static nonzero-mode spectrum and
a fixed c-number leaves the full H with no eigenvectors. Therefore this
normal additive implementation has no exact constrained state with the
specified full source marginal, regardless of the sign of G.

This does not exclude physical Hilbert spaces obtained from distributional
constraint solutions. RELATIONAL.md supplies that distinction constructively.

## 2. The known Fisher-information bound and its application here

Use the symmetric-logarithmic-derivative quantum Fisher information:
\[
 F_Q(\rho,H)=2\sum_{i,j:r_i+r_j>0}
  { (r_i-r_j)^2\over r_i+r_j}|H_{ij}|^2 .
\]
Partial trace is covariant under the additive evolution, so monotonicity
and FQ<=4 variance imply
\[
       \boxed{{\rm Var}_R C\ge F_Q(\rho,H)/4 .}
\]
This is a known general result, not a new UEOT theorem. See I. Marvian,
Phys. Rev. Lett. 129, 190502 (2022), Theorem 3, arXiv:2112.04694.
The new use is to reject an arbitrary-correlation repair of our fixed
normal source state. For infinite-dimensional H, finite variance and the
relevant differentiability/domain conditions are required; infinite FQ
also forbids finite variance.

The finite-dimensional optimum can be derived directly. Purify
rho=sum_i r_i |i><i| as Psi=sum_i sqrt(r_i)|i,i>. For each pair set
\[
 G_{ii}=-H_{ii},\qquad
 G_{ji}=-{2\sqrt{r_ir_j}\over r_i+r_j}H_{ij}\quad(i\ne j).
\]
The transpose/conjugation is essential for complex H. The coefficient of
|i,j> in C Psi is sqrt(r_j)H_ij+sqrt(r_i)G_ji. Pairwise minimization gives
\[
 \|C\Psi\|^2=
 \sum_{i<j}{(r_i-r_j)^2\over r_i+r_j}|H_{ij}|^2=F_Q/4,
 \qquad\langle C\rangle=0 .
\]
The zero-eigenvalue blocks are handled by the same expression where the
denominator is nonzero; the remaining block is arbitrary. This realizes
the optimum only when G is freely designable, without spectrum, locality
or physical-gravity restrictions. Infinite-dimensional attainability is
not inferred from this matrix construction.

The checker includes rho=diag(3/4,1/4), H=sigma_x and H=sigma_y:
FQ=1, minimum variance=1/4. The optimal G has opposite signs in these two
examples because sigma_y transposes to -sigma_y.

## 3. Degenerate coherence survives an energy-matching code

For a purely discrete source H, a designed generator with orthogonal
vectors |-E> permits the isometry
\[
 V\psi=\sum_E|-E\rangle\otimes\Pi_E\psi,\quad CV=0 .
\]
Tracing its first factor gives sum_E Pi_E rho Pi_E. A stationary source
is preserved, including arbitrary coherence within a degenerate energy
block. The accepted thermal-shell NOON pair is of this kind. Its full
infinite thermal sum is normal; G is then unbounded below and is not a
positive-energy apparatus.

The original zero-mode marginal is not of this kind. Replacing it by a
diagonal energy distribution is not an innocuous choice of geometric
correlations: it changes the full state and its Q correlations. The
finite matrix example checks the distinction exactly; it does not claim
a gravity action for the designed G.
