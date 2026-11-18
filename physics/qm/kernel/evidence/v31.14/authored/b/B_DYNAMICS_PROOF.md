# Persistent two-mode source: domain, histories and certified finite prediction

Status: research proof and executed numerical/interval certificates; no new Lean theorem is claimed. The model is the previously frozen `SHARED_MODEL.json` dated 2026-11-14 in client time. Existing Core is a read-only dependency. Complex Hilbert space, the Born rule, tensor composition, CP instruments, the oscillator Hamiltonian and vacuum preparation are physical inputs.

## 1. Exact source and quantifiers (P-MICRO-08)

Let S=C², let R be any finite-dimensional untouched reference, and let E be the two-mode bosonic Fock space. Put

\[
N=n_1+n_2,\quad H_E=n_1+\tfrac32n_2,\quad
B=(a_1+a_1^\dagger)+\tfrac35(a_2+a_2^\dagger),\quad
H_\lambda=I_S\otimes H_E+\lambda Z\otimes B,
\]

with lambda in [1/5,2/5], hbar=1, and initial rho_SR tensor |00><00|_E. The times are (2/3,3/4,1/2), of total T=23/12. After each joint evolution apply F=diag(sqrt(1/8),sqrt(1/4)) or P=diag(sqrt(7/8),sqrt(3/4)). F stops and retains the actual unnormalized SR state. P is followed by Ry(pi/2), Rx(pi/3), I respectively. All terminal records f,pf,ppf,ppp remain visible. The same E survives every live slot. No normalized conditional state is substituted for an unnormalized branch.

The distance is D_full=(1/2) sum_r ||rho_r-sigma_r||_1. A statement uniform in rho_SR and R is a half-diamond statement for this fixed-policy terminal CQ channel. It is not a statement that every possible multi-time intervention has been experimentally characterized.

### 1.1 Self-adjointness and common domain

For any finite number of positive-frequency modes and bounded self-adjoint L, a(g)=sum g_k* a_k obeys

\[
\|a(g)\psi\|\le\Bigl(\sum_k|g_k|^2/\omega_k\Bigr)^{1/2}\|H_E^{1/2}\psi\|,
\quad
\|a(g)^\dagger\psi\|^2=\|a(g)\psi\|^2+\|g\|_2^2\|\psi\|^2.
\]

Consequently the linear field is H_E-bounded with relative bound zero. Kato--Rellich gives self-adjointness on D(H_E), uniformly for a compact set of finite couplings and positive frequencies bounded away from zero. The frozen domain is C² tensor D(H_E). Finite Fock vectors form an invariant domain for the finite-order calculations below; they need not remain finite-support under exact evolution.

Here a still more explicit construction fixes the domain. In a Z-sector z=+/-1, c=(1,3/5), omega=(1,3/2), and alpha_k(t)=lambda*c_k/omega_k*(exp(-i omega_k t)-1),

\[
U_z(t)=e^{i\phi(t)}D(z\alpha(t))e^{-itH_E},\qquad
\phi(t)=\sum_k(\lambda c_k/\omega_k)^2[\omega_k t-\sin(\omega_k t)].
\]

This follows by completing the square, with the exact Weyl phase retained. Weyl displacement by finitely many finite amplitudes preserves D(H_E). Thus this unitary is the self-adjoint source just described, not a formal power series definition.

### 1.2 Full-record energy control

Let gamma=||c||_2=sqrt(34/25). Dilate the complete instruments into a finite record register. Once a branch stops, decouple Z from its bath and allow free bath evolution until the common horizon. This padding leaves its terminal SR record state unchanged. All controller operations commute with N. The live coupling has system/record norm at most one. Initially the bath is vacuum, and the finitely many displacement histories make the relevant number moments finite. Differentiating on this actual finite-history domain and using Cauchy--Schwarz gives

\[
\left|\frac{d}{dt}\langle N\rangle\right|
\le2|\lambda|\gamma\sqrt{\langle N\rangle},\qquad
\sqrt{\langle N(t)\rangle}\le|\lambda|\gamma t.
\tag{B1}
\]

The zero initial value is handled by replacing sqrt(n) with sqrt(n+epsilon) and taking epsilon down to zero. This is an unconditional complete-record estimate. Normalizing an individual rare branch can increase its conditional energy. In particular one cannot insert an unconditional bound into every normalized postselected branch without its branch probability.

For a fixed finite-energy Gaussian initial bath, the analogous bound is sqrt(<N(t)>) <= sqrt(<N(0)>)+||L|| ||g||_2 t, with <N(0)>=(Tr V+||d||²-m)/2. The executed and calibrated certificate in this release uses vacuum only.

## 2. Actual multi-time influence functional

For a history s=(z_1,...,z_n), recursively define beta_0=0 and theta_0=0. With R_j=diag(exp(-i omega_k t_j)) and alpha_j=lambda*c/omega*(exp(-i omega*t_j)-1),

\[
\beta_j=R_j\beta_{j-1}+z_j\alpha_j,
\]
\[
\theta_j=\theta_{j-1}+\phi(t_j)+\operatorname{Im}\sum_k(z_j\alpha_{jk})(R_j\beta_{j-1})_k^*.
\tag{B2}
\]

Then W_s=U_(z_n)(t_n)...U_(z_1)(t_1)=exp(i theta_s)D(beta_s)exp(-iH_E T_n). The second term in theta is the Weyl exchange phase. Omitting it changes the process when the system is manipulated between slots.

For a physical Gaussian initial state with real quadrature mean d and covariance V in (q1,p1,q2,p2), V+iOmega/2 >=0, define

\[
\xi(\zeta)=\sqrt2(\operatorname{Im}\zeta_1,-\operatorname{Re}\zeta_1,
\operatorname{Im}\zeta_2,-\operatorname{Re}\zeta_2).
\]

Let S_T be the real phase-space free rotation, d_T=S_T d, V_T=S_T V S_T^T. The exact pair factor is

\[
F_{s,r}=\exp\{i[\theta_s-\theta_r+
\operatorname{Im}(\beta_r^\dagger\beta_s)+\xi(\beta_s-\beta_r)^Td_T]
-\tfrac12\xi(\beta_s-\beta_r)^TV_T\xi(\beta_s-\beta_r)\}.
\tag{B3}
\]

This follows directly from Tr(W_s sigma W_r†), cyclicity, the Weyl multiplication law and the Gaussian characteristic function. It retains correlations between modes through all of V. No product factorization of a correlated initial bath is made. For vacuum it becomes exp(i(theta_s-theta_r)-||beta_s-beta_r||²/2+i Im(beta_r†beta_s)).

For a terminal record h, let M_(h,j) be its actual F/P/rotation Kraus factor, with F only at its final failed slot. Put A_(h,s)=M_(h,n) P_(z_n)...M_(h,1)P_(z_1). Then

\[
\rho_h^{SR}=\sum_{s,r}F_{s,r}
(A_{h,s}\otimes I_R)\rho_{SR}(A_{h,r}^\dagger\otimes I_R).
\tag{B4}
\]

Equation B4 sums coherent histories, including their off-diagonal pairs. It does not replace a conditional bath by a single Gaussian. Positivity follows either from the actual joint-unitary construction or because F is a positive Gram matrix: sum u_s* F_sr u_r=Tr[(sum u_s* W_s) sigma (sum u_r W_r†)] >=0, with matching index convention. F†=F. Summing complete F/P outcomes uses F†F+P†P=I, and rotations are unitary. Repeatedly cancelling the final summed instrument proves trace preservation and the causal prefix constraints. The untouched reference passes through every formula.

The probability of ppp is not assumed constant. Because (3/4)I <= P†P <= (7/8)I, recursively

\[
(3/4)^3\le\Pr(ppp)\le(7/8)^3
\tag{B5}
\]

for every input and lambda. The actual accepted effect is nonscalar; its two eigenvalues are computed from the source and reported separately. Normalizing the accepted branch is not a linear CPTP channel.

## 3. Genuine Galerkin error (P-MICRO-09)

Let P_K project onto n1,n2 <= K, let J_K be its inclusion, and define H_(lambda,K)=J_K†H_lambda J_K. This is the actual product-Fock Galerkin compression, with the same instruments acting on S. The first K interaction orders from the bath vacuum fit inside total N<=K, which is contained in the rectangular carrier. The free bath and every system/record operation preserve total N.

For interaction order j define

\[
x=\lambda_{\max}\gamma T,\quad
c_j=\frac{x^j}{j!}\prod_{k=1}^j(\sqrt{k-1}+\sqrt{k}).
\tag{B6}
\]

On total N<=k-1, a(c) has norm <=gamma sqrt(k-1) and a(c)† has norm <=gamma sqrt(k). Expand Duhamel finitely with the true propagator on the LEFT as a unitary suffix and only free evolutions, bounded controller operations and finite-support coupling factors on its right. Stop after K+1 factors. The time-simplex volume is T^(K+1)/(K+1)!. Thus the full and compressed remainders are each at most c_(K+1), and their first K terms agree exactly. No convergence of an infinite Dyson series is assumed, and no unbounded true evolved state is inserted on the uncontrolled right-hand side of a field operator.

Purify rho_SR, include all instrument records, use the pure-state trace-distance/vector-distance inequality, then discard E and unused dilating registers. This gives, uniformly over arbitrary rho_SR and finite R,

\[
D_{\rm full}(\Phi_\lambda,\Phi_{\lambda,K})
\le d_K:=\min(1,2c_{K+1}).
\tag{B7}
\]

The argument also covers arbitrary number-preserving-on-E complete S-only interventions and stopping trees within the same total exposure budget. The present executed interface is the frozen three-slot tree. A change of times preserving total T retains B7. The present interval evaluation gives d_20 < 0.00001344. Agreement for one Bell input is an additional numerical observation, not the proof of B7.

### 3.1 The actual boundary residual and reference prefixes

For this rectangular cutoff,

\[
R_K=H_\lambda J_K-J_KH_{\lambda,K},\qquad
R_K^\dagger R_K=\lambda^2(K+1)I_S\otimes
[c_1^2\Pi_{n_1=K}+c_2^2\Pi_{n_2=K}].
\tag{B8}
\]

The two outgoing faces are orthogonal, so cross terms vanish. For an actual finite-model prefix sigma_h of mass m_h, evolve sigma_h(s) with H_(lambda,K) and define r_h(s)=Tr[R_K†R_K sigma_h(s)]. Duhamel with the finite prefix and true suffix gives

\[
D_{\rm full}\le\sum_{h\,\rm live}\int_0^{t_h}
\sqrt{m_h r_h(s)}\,ds.
\tag{B9}
\]

This can be sharper than B7 if the integrals are rigorously enclosed. The masses and occupations in B9 belong to the actual finite reference prefixes. Infinite-source occupations must not be silently substituted. This release certifies B7 by scalar interval arithmetic; it does not call ordinary numerical quadrature of B9 rigorous.

### 3.2 Initial tails, deleted modes and other error terms

For the frozen vacuum preparation, the initial tail is zero, there are no deleted modes, no time splitting is used, and the stipulated Hamiltonian is exact as a model. These terms are zero only inside that mathematical contract. They are unknown device mismatches without preparation/control/model/readout evidence.

For a separate fixed general initial sigma_E, if epsilon=1-Tr(P_M sigma_E)<1, comparison with the normalized fixed P_M sigma_E P_M costs at most sqrt(epsilon) in trace distance; this approximation is performed on the declared bath state, independently of rho_SR. A mean total occupation nbar gives epsilon<=nbar/(M+1). Its internal mode correlations remain in P_M sigma_E P_M. This initial-state term does not replace a propagation residual. No numerical Gaussian nonvacuum certificate is claimed here.

Deleting a mode can be compared on the SAME Hilbert space by switching off its coupling while keeping its initial joint bath state and free dynamics. On a chosen finite carrier, ordinary Duhamel contributes sum_j t_j ||V_drop,K,j||. The same initial truncation and boundary errors must still be paid. Tracing a correlated omitted mode can create a mixed retained bath; this is not a new product vacuum. Resetting the bath after each slot is a different process, not a mode-deletion approximation.

For a verified bounded finite-domain effective-Hamiltonian discrepancy, add the corresponding integrated operator norm. A finite-dimensional time-discretization algorithm needs its own error bound. Our per-mode matrix exponential backend does not introduce a Trotter approximation, but its floating arithmetic is accounted separately by the interval comparison below.

## 4. Parameter stability from the infinite source

Fix the same controller and stopping records for lambda and lambda_hat. Duhamel's parameter difference is delta_lambda times B. On the exact infinite source, B1 gives

\[
\|B\psi(t)\|\le\gamma(\sqrt{\langle N\rangle}+\sqrt{\langle N\rangle+1})
\le\gamma(1+2\lambda_{\max}\gamma t).
\]

Thus

\[
D_{\rm full}(\Phi_\lambda,\Phi_{\hat\lambda})
\le |\lambda-\hat\lambda|[\gamma T+\lambda_{\max}\gamma^2T^2]
<\tfrac{51}{10}|\lambda-\hat\lambda|.
\tag{B10}
\]

The sharper displayed constant is 4.23364267080181...; the previously frozen 51/10 constant is retained. For a fully rational comparison, gamma<7/6 yields the sharper bracket <38111/9000<51/10. B10 precedes addition of the Galerkin error and makes no assertion that a compressed Hamiltonian preserves every invariant of its infinite source. The swapped times (3/4,2/3,1/2) have the same T and admit exactly the same constants. Frequencies, relative couplings, vacuum, source controls and shared detector model remain independent calibration premises.

## 5. Interval Choi representation and exact physical repair (P-NUM-01)

For input dimension 2, each normalized Bell output J_r=(Phi_r tensor id)(|Bell><Bell|) is a normalized-convention Choi block of dimension 4. Independent 80-digit `mpmath.iv` evaluation computes every complex entry of the exact infinite-source B4. Exact dyadic interval endpoints are exported. They enclose the error of the actual stored binary64 Choi entries, including the rounded representation of the nominal parameter. The intervals are not inferred from agreement of two floating solvers.

For any stored Hermitian blocks Q_r, put e_F=2 sum_r ||Q_r-J_r||_F. Since a 4-by-4 matrix has trace norm at most twice its Frobenius norm,

\[
\sum_r\|Q_r-J_r\|_1\le e_F,
\qquad \tfrac12\|\mathcal Q-\Phi\|_\diamond
\le\tfrac{d_{in}}2\sum_r\|Q_r-J_r\|_1\le e_F.
\tag{B11}
\]

The interval runner verifies e_F < e=10^-12. The same number bounds the sum of Choi trace norms and the half-diamond error because d_in=2. Both the direct Weyl stored backend and the independent K20 Galerkin stored backend are compared to the exact infinite Choi. For the latter this fixed-parameter a-posteriori certificate covers both its actual truncation discrepancy and floating matrix-exponential error. B7 remains a separate uniform-in-parameter analytic theorem.

Raw Q need not be exactly positive or trace preserving. To obtain an actual finite terminal CQ instrument, convert stored binary64 entries to exact rational numbers and Hermitianize exactly. Choose delta=10^-10, a=1/(1+20delta), and define

\[
\widetilde Q_r=Q_r+\delta I_4,
\quad R=I_2/2-a\sum_r\operatorname{Tr}_{out}\widetilde Q_r.
\tag{B12}
\]

The raw operator error of every block is <=e<delta, so each Qtilde_r is PSD. Partial trace is trace-norm contractive on Hermitian matrices, hence the aggregate marginal error is <=e<2delta. Four added delta I4 terms contribute 8delta I2. Therefore a sum Tr_out Qtilde <=a(1/2+10delta)I2=I2/2, and R is PSD. Set Jrepair_r=a Qtilde_r, and add |0><0|_out tensor R to the existing `f` block. All entries, a, delta and R are stored as exact fractions. Hermiticity and sum Tr_out Jrepair=I2/2 are verified by exact rational arithmetic. Positivity is certified by the perturbation proof, not by floating eigenvalues.

If e bounds sum_r ||Q_r-J_r||_1, positivity of R and exact trace accounting give

\[
\sum_r\|J^{repair}_r-J_r\|_1
\le a(40\delta+2e)<10^{-8}.
\tag{B13}
\]

By B11 this is also a uniform half-diamond bound. It explicitly pays for physicalization. No terminal label is added or omitted. This is a physical fixed-policy terminal instrument, not a construction of the entire process tensor for arbitrary counterfactual interventions; it does not identify the repaired `f` branch with the original microscopic F event. The approximation to that original event is included in B13.

The exported rational map is defined in exact arithmetic. A subsequent arbitrary-input floating contraction introduces additional rounding and is not automatically covered by the stored-map certificate. The exact model and rational representation suffice for the stated mathematical prediction contract; hardware preparation/readout errors remain separate.

## 6. Executed controls and extension responsibilities (C-QMEM-01)

The source runner executes lambda=.2,.3,.4, K=0,2,4,6,8,12,20, entangled Bell input and a further input with untouched R dimension 3. It checks positivity and TP of the exact Choi diagnostic, prefix causality, nonscalar acceptance, and independent Weyl/Galerkin convergence. Results and resources are in `dynamics_results.json`.

* At lambda=.3, the first-slot true and reset channels are exactly equal for every input/reference: both use the same vacuum one-slot source and complete instrument. Their complete three-slot CQ outputs have floating distance 0.10125185621002683. A separate 80-digit interval evaluation of the actual frozen event `ppp and X_S tensor X_R=+1` proves p_reset-p_true>0.03164037538529123569>3/100, hence D_full>3/100. `memory_event_witness.json` exports its exact dyadic endpoints. This strict witness uses the same three-slot source, not a substituted causal-break protocol. Thus identical isolated single-slot channels do not determine this multi-time process.
* Omitting the exchange phase gives distance 0.05022546990230467 at lambda=.3.
* The vacuum initial tail above K=0 is exactly zero; its actual propagation error at lambda=.4 is 0.2389578616352383. A small initial tail alone is not a dynamical certificate.
* The actual first-pass bath marginal is a mixture of opposite coherent states with weights 7/13 and 6/13. Along the displacement-aligned mode-1 quadrature, its fourth cumulant is mu^4(-2+8/169-6/28561), where mu=sqrt(2)|alpha_1|. It is nonzero whenever the displacement is nonzero. Even this initial Gaussian bath cannot remain described by one Gaussian after conditioning.
* A separate declared rare-acceptance toy has full CQ distance 10^-6 and conditional accepted distance 1. It is not substituted for the actual acceptance lower bound 27/64.
* A separate qutrit leakage extension loses 0.05 probability if its third level is silently omitted. This flags an unsupported extension of the frozen qubit carrier, not leakage observed in the ideal model.
* The parameter certificate rejects lambda=.5, outside its frozen interval.

Finite positive frequencies avoid an IR problem only for this finite model. An infinite-mode limit must specify at least the coupling integrability needed for a field/form realization, the representation and possible displacement implementability (typically involving g/omega), UV renormalization where required, finite energy/covariance control, and convergence under the actual tester family. A local field-theory extension additionally needs localized interaction supports, causal factorization and a quantified cutoff causality defect. QND is not a proof of energy exchange, equilibration, Markovianity, or a selected Lorentzian geometry.

## Sources and contribution boundary

The present finite-history formulas and bounds are derived above for the frozen source. Standard bosonic truncation and operational-memory theory are prior work, not claimed as UEOT discoveries:

1. Woods, Cramer and Plenio, *Simulating Bosonic Baths with Error Bars*, Phys. Rev. Lett. 115, 130401 (2015), https://arxiv.org/abs/1504.01531.
2. Pollock et al., *Operational Markov condition for quantum processes*, Phys. Rev. Lett. 120, 040405 (2018), https://arxiv.org/abs/1801.09811.
3. Goan, Jian and Chen, *Non-Markovian finite-temperature two-time correlation functions of system operators of a pure-dephasing model*, Phys. Rev. A 82, 012111 (2010), https://arxiv.org/abs/1007.3791.
4. Liu and Lu, *Error Bounds for Open Quantum Systems with Harmonic Bosonic Bath*, Quantum 9, 1896 (2025), https://arxiv.org/abs/2408.04009. Its correlation-function results do not silently replace our full tester-level contract.

The UEOT increment is a common-source, complete-record, reference-preserving connection between explicit assumptions, true finite approximation, calibration and a physical numerical representation. The standard persistent joint model is the strong baseline and predicts the same physics. No extra empirical prediction or superiority is manufactured from the reset ablation.
