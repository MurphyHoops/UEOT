# AG. Sharp force, finite-energy domains, and a separate Hadamard gate

## AG1. Contract and actual Hamiltonian

This entry uses the accepted full-field global-controller Hamiltonian \(H_M\) and
the actual canonical cutoff \(H_{M,K}\) from frozen Z
(\`../conformal_action/QUANTUM_CONTROLLER.md\`). It does not replace the controller
by a classical path. The coupling is
\[
 r(x)=\tfrac15\exp[4-1/(x(1-x))]\quad(0<x<1),\qquad r=0\ \text{otherwise}.
\]
The scalar counterterm and its fixed finite part \(c_r=0\) are retained.

At fixed \(x\), the diagonal modes have
\(\omega_{k,\pm}=\sqrt{k^2\pm r}\), multiplicity \(k^2\), and
\(\theta_{k,\pm}=\frac14\log(1\pm r/k^2)\). Write \(W_K\) for the actual
diagonalizing squeeze and \(A_K=W_K^\dagger\partial_x W_K\). The frozen AA
correlated preparation has envelope
\(u(x)=\sqrt{630}x^2(1-x)^2\) on \([0,1]\), low source coherent displacement
\(q=\pm1,p=0\), low probe vacuum, and high tail \(W_{\rm tail}(x)\Omega\).
AA proved this vector lies in \(D(H_M)\), using the actual graph limit. In
particular its second total-energy spectral moment is finite.

This assertion does not put the vector in the domain of every derivative
of \(H_M\). The force is the particular derivative that must now be tested.

## AG2. Actual high-tail lower bound

For finite \(K\), let \(F_K=-\partial_xH_{{\rm field},K}\), including the
derivative of the scalar counterterm. Conjugating to the moving frame gives
\[
 W_K^\dagger(\partial_xH_{{\rm field},K})W_K
   =D_K'+[A_K,D_K]+e_K'.
\]
The component orthogonal to the high-tail vacuum contains pair creation with
amplitude \(\theta_{k,\pm}'\omega_{k,\pm}\). Its squared norm is
\[
 2\sum_{k=2}^K k^2\sum_{\pm}
       (\theta'_{k,\pm}\omega_{k,\pm})^2
 =\frac{r'(x)^2}{4}\sum_{k=2}^K
            \frac{k^4}{k^4-r(x)^2}
 \ge \frac{K-1}{4}r'(x)^2.                         \tag{AG.1}
\]
The two signs, degeneracy, and normalized two-particle norm are all included.
Low-mode excitations do not cancel an orthogonal high-pair component.
Subtracting the joint mean also acts in the high-vacuum sector. A scalar
counterterm does not change a fixed-\(x\) conditional variance; in the joint
\(x\)-packet it can change the vacuum-sector variance, but still cannot cancel
the orthogonal component in (AG.1).

An explicit lower bound needs no numerical mode extrapolation:
\[
 u^2r'^2=\frac{126}{5}
 e^{8-2/[x(1-x)]}(1-2x)^2.
\]
On \([1/3,2/5]\) and its reflected interval, of total length \(2/15\),
\(1/[x(1-x)]\le9/2\) and \((1-2x)^2\ge1/25\). Therefore
\[
 \int u^2r'^2dx\ge\frac{84}{625e},\qquad
 \boxed{\operatorname{Var}_{\Psi_K}(F_K)
       \ge\frac{21}{625e}(K-1)>0.0123(K-1).}        \tag{AG.2}
\]
Finite total-energy variance and actual Hamiltonian graph convergence do not
provide a finite sharp-time force variance in this preparation. This is not
a no-go theorem for time-smeared force; AH constructs that observable.

## AG3. Hadamard regularity is a separate requirement

The divergence above does not diagnose a non-Hadamard state. Even the free
Hadamard vacuum has infinite variance for the sharp-time spatial integral of
the product of two independent fields. Time smearing is essential for that
composite. Conversely, normality and finite total-energy moments alone do
not establish Hadamard regularity. Here is a separate explicit free example.

For one conformal scalar on the unit ESU, choose real squeeze coefficients
\[
 \beta_k=\gamma k^{-3},\qquad \alpha_k=(1+\beta_k^2)^{1/2},\quad\gamma>0,
\]
in every mode of degeneracy \(k^2\). The Hilbert-Schmidt sum is
\(\gamma^2\zeta(4)<\infty\), hence the squeezed vacuum is a normal Fock vector.
For the normal-ordered \(H_0=\sum k\,a^\dagger a\),
\[
 \langle H_0\rangle=\gamma^2\zeta(3),\qquad
 \operatorname{Var}H_0=2\gamma^2\zeta(2)+2\gamma^4\zeta(8),               \tag{AG.3}
\]
\[
 \langle H_0^2\rangle
  =2\gamma^2\zeta(2)+\gamma^4[2\zeta(8)+\zeta(3)^2]<\infty.
\]
Choose the squeeze phase so that the equal-time covariance difference has
harmonic eigenvalues
\[
 \frac{\beta_k^2-\alpha_k\beta_k}{k}
     =-\gamma k^{-4}+O(k^{-7}).                    \tag{AG.4}
\]
These eigenvalues do not decay rapidly. The difference kernel on the compact
Cauchy slice is not smoothing. Since two Hadamard two-point functions have
smooth difference, this normal finite-energy vector is not Hadamard relative
to the free ESU vacuum.

The positive vacuum overlap obeys
\(\langle\Omega,\Omega_\gamma\rangle\ge
 \exp[-\gamma^2\zeta(4)/4]\). Thus
\[
 \|\Omega_\gamma-\Omega\|^2\le\gamma^2\zeta(4)/2,
\]
\[
 \|(H_0+1)(\Omega_\gamma-\Omega)\|^2
 \le\gamma^2[2\zeta(2)+2\zeta(3)+\zeta(4)/2]
    +\gamma^4[2\zeta(8)+\zeta(3)^2]\longrightarrow0.                 \tag{AG.5}
\]
Moreover truncating \(\beta_k\) to zero above \(K\) gives Hadamard states,
because each difference is a finite sum of smooth modes. Tail moments and
the product overlap imply convergence to \(\Omega_\gamma\) in the
\(D(H_0)\) graph norm. Hence even a sequence of Hadamard cutoffs with this
graph convergence can have a non-Hadamard limit.

This does not say the AB outside coherent/vacuum input is non-Hadamard:
its field part is Hadamard. Propagation under the operator-valued
controller and the domain of the complete local stress still require a
separate argument. The general relation of Hadamard regularity and Wick
fluctuations is discussed by Fewster and Verch,
[arXiv:1307.5242](https://arxiv.org/abs/1307.5242); (AG.3)–(AG.5) are the
explicit estimates for this entry, not a claim that that paper proves the
present coupled model.

## Acceptance

Accepted: the finite-\(K\) orthogonal-sector force lower bound and a free
counterexample to the proposed finite-energy/Hadamard implication.
Open: the interacting four-dimensional stress, its joint tensor noise,
Einstein constraints and physical unification. The certificate checks
algebra and bounds; the functional-analytic statements are the proofs above,
not a machine-formal theorem or an ODE integration.
