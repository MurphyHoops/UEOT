# Three regimes: a positive-source domain test

Use the fixed operator (1) in MODEL.md, including its complete curvature
term. Put q=V0U0>0. Positive dust requires H<=0. The following statements
apply to normal states; no diagonal delta(P-P') density is used.

## 1. Subcritical 0<q<4gamma: no positive volume moment

For (H_P-z)u=0 set w_n=sqrt(n)u_n. Exactly,
\[
 w_{n+1}+w_{n-1}=t_n(z)w_n,\quad
 t_n(z)=2-q/\gamma+(d/\alpha)n^{-2/3}
                 +z/(\alpha n)-\epsilon/(\alpha n^2).
\tag{2}
\]
The transfer matrix [[t_n,-1],[1,0]] has determinant one.

Fix a real E. For all sufficiently large n, t_n(E) is in a compact
subinterval of (-2,2), and
sum |t_(n+1)(E)-t_n(E)| < infinity. Diagonalize these matrices with a
smooth matrix of eigenvectors S(t). Its eigenvalues have unit modulus;
S and its inverse are uniformly bounded on this compact interval.
The sum of ||S_(n+1)^-1 S_n-I|| is finite. Products of these perturbations
and their inverses are bounded, even when interspersed with the diagonal
unitary matrices. Consequently every nonzero real-energy solution has
\[
 0<c\le |w_n|^2+|w_{n-1}|^2\le C.
\]
Summing with weights 1/n shows that no nonzero homogeneous tail belongs
to ell2.

Every real E belongs to the spectrum: otherwise (H_P-E)^-1 e1 would
be an ell2 vector with a homogeneous nonzero tail. A tail that vanished
identically would force the entire vector to vanish by the nonzero
off-diagonal recurrence, contradicting the inhomogeneous first row.
Thus sigma(H_P)=R. The Jacobi vector e1 is cyclic, so its scalar spectral
measure mu_P has support R. Absolute continuity is not needed.

Let p_n(z) be the spectral polynomial for e_n (p_1=1). Around any fixed
real E0, compare the complex transfer matrices with the real fundamental
solution:
\[
 M_n(z)-M_n(E0)={(z-E0)\over\alpha n}
                 \begin{pmatrix}1&0\\0&0\end{pmatrix}.
\]
The uniformly bounded real fundamental solution and inverse give
\[
 |p_n(z)|\le C n^{-1/2+C_0|z-E0|}
\tag{3}
\]
in a small disk. This follows from the product estimate
prod(1+C|z-E0|/n)<=C' n^(C|z-E0|); the finite initial segment is analytic
and bounded on a smaller disk.

If sum n^r |psi_n|^2 is finite for any r>0, then
F_psi(z)=sum psi_n p_n(z) converges normally in a sufficiently small
disk about E0, by Cauchy-Schwarz and (3). These locally defined functions
agree on overlaps. Their union contains the entire real line and is
connected. On the real axis the series agrees mu_P-almost everywhere
with the unitary spectral transform: uniform convergence on compact
intervals and L2(mu_P) convergence of partial sums identify the limits.

If psi is in 1_(-infinity,0](H_P), its transform vanishes mu_P-almost
everywhere on (0,infinity). Full support and continuity force it to
vanish everywhere on that open interval. Analytic uniqueness then gives
psi=0. Hence
\[
 \boxed{\psi=1_{H_P\le0}\psi,\quad
 \langle N^r\rangle_\psi<\infty,\ r>0\quad\Longrightarrow\quad\psi=0.}
\tag{4}
\]
No finite-H2 assumption is required. The direct-integral and mixed-state
extensions follow by spectral decomposition, positivity and Tonelli.
In particular a nonzero normal positive-dust state cannot have finite
positive vacuum total energy q<v>. The bound on inverse-volume K0
alone therefore did not solve the source problem.

## 2. Supercritical mu=q-4gamma>0: finite momentum cap

Since L<=4,
\[
 H_P\ge F_P(v):=\mu v-{3V_0\over2}v^{1/3}+{|P|^2\over2v}.
\]
Writing y=v^(2/3) gives
\[
 \sup_{v>0}(3V_0v^{4/3}-2\mu v^2)
 ={V_0^3\over\mu^2},\qquad y_{\max}=V_0/\mu .
\tag{5}
\]
For P^2 greater than this threshold, F_P is strictly positive, the form
is confining, and no H<=0 state exists. Equality is also excluded:
H_P=F_P+gamma sqrt(v)(4-L)sqrt(v), both forms are nonnegative,
and 4-L has no kernel on the half line. A vector of zero energy would
have to be in that kernel. The confining form controls <v>, so the
square-root factors here have their proper domains.

The necessary cap is therefore
\[
 |P|^2<{V_0^3\over(q-4\gamma)^2}.
\tag{6}
\]
It is not a sufficient condition for a negative eigenstate. The original
Gaussian mixture has strictly positive mass beyond every finite cap;
the complete original momentum law cannot be embedded in this regime.

## 3. What the selection does and does not say

Within this specific family, positive dust, finite positive vacuum energy,
and the exact original unbounded momentum law can coexist only at
\[
 q=4\gamma,\quad \ell^2={3\over2V_0^2U_0},\quad \rho_c=U_0.
\tag{7}
\]
CRITICAL_STATE.md and VOLUME_MOMENTS.md establish existence there.

This is a conditional selection among declared models, not a prediction
of an independently determined fundamental constant. It is sensitive to
the exact-support demand. If a small change of source law is allowed,
a smooth momentum cutoff has finite Q moments and can remove a Gaussian
tail with controlled source trace distance. Nearby supercritical models
then have negative bound states on any fixed compact P set for a
sufficiently small positive mu. The cutoff error refers to the source
before a P-dependent geometric embedding; that embedding can introduce
additional decoherence. Any stronger approximation must budget it.

For a cutoff radius squared K2*r_cap above the largest ring r_hi,
\[
 \epsilon_{\rm tail}\le
 \exp[-\nu_0(\sqrt{r_{\rm cap}}-\sqrt{r_{\rm hi}})^2].
\]
A normalized smooth filter changes a source state by at most sqrt(epsilon)
in trace distance if its discarded probability is at most epsilon.
This is a theoretical state operation, not an implemented controller.

## 4. Certificate scope

phase_diagram.py verifies the exact recurrence, the maximization in (5),
the critical relation and the tail/cap normalization. The transfer,
spectral-transform analyticity and domain arguments above are separately
reviewed analysis, not an automated theorem prover output.
