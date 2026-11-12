# B — Segmented excitation growth, finite rectangular instruments, and omission bounds

## Status and source identity

This is a newly reconstructed research proof and independent review for the interrupted v31.12 iteration. It is based on actual v31.11 files at main `aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d`, particularly `physics/qm/audits/OPERATIONAL_MICRO_ROBUST_v31.11/SHARED_MODEL.md`, `B_MICRO_TRUNCATION.md`, the frozen model, and Chapter 67. It does not represent recovery of the missing previous scratch files or their execution receipts. New computations have their own receipt.

The scientific increment is narrow: replace the conserving label-one gate by one **segmented** red-then-blue pulse, derive exact finite growth from that microscopic operator, and bound an implementation that omits the blue pulse. Complex quantum mechanics, oscillator Fock space, the Born rule, the control model and independently justified device error bounds remain inputs. Core is unchanged. There is no new hardware dataset.

## 1. Exact model and independent physical inputs

Let

\[
\mathcal H_S=\mathbb C^2\otimes\ell^2(\mathbb N_0),\quad
P_e=|e\rangle\langle e|,\quad P_g=|g\rangle\langle g|,
\quad G=a^\dagger a+P_e.
\]

The reference \(R\) is any finite positive-dimensional complex system, is never acted on, and may initially be entangled with \(S\). The joint input is a normal density operator with \(\operatorname{Tr}G\rho_S\le\bar n<\infty\). Auxiliary flags are freshly prepared independently of the joint input and previous flags. Define

\[
A=a\sigma_++a^\dagger\sigma_-,\qquad
B=a^\dagger\sigma_++a\sigma_-,\qquad
U_0=e^{-i\phi P_e},\quad U_1=e^{-i\alpha A},\quad
B_\beta=e^{-i\beta B},\quad
V_0=U_0,\quad V_1=B_\beta U_1.
\tag{B.1}
\]

Here \(\alpha,\beta,\phi\) are dimensionless integrated pulse areas. For a real scalar coupling rate \(g_b(t)\), \(H_b(t)=\hbar g_b(t)B\) and \(\beta=\int g_b(t)dt\). Its time ordering is trivial within that pulse because all its generators are scalar multiples of the same self-adjoint operator. The red and blue pulses in \(V_1\) occur **in that order** and do not overlap. Their product is not silently replaced by the exponential of their sum. The generator \(B\) is self-adjoint but is not a positive operator; the excitation observable \(G\) is positive.

The fixed shared unknown parameter is now \(\theta=(q,\phi,\alpha,\beta)\), with

\[
q\in[12/25,13/25],\qquad s=1-q/2.
\]

The unchanged fresh three-level logical flag preparation and complete readout yield the actual instrument

\[
K_0=\sqrt{s(1-q)}V_0,\quad
K_1=\sqrt{sq}V_1,\quad K_f=\sqrt{1-s}I.
\tag{B.2}
\]

This can be realized either by preparing and reading a classical flag before feed-forward, or by coherently controlling the gates and reading the flag afterwards. Both implement (B.2) under the declared ideal control model. Their hardware scheduling costs need not agree. The new control injects excitation; a degenerate flag does not supply a conserving dilation for it. A classical external drive supplies work, with laboratory work and heat accounting left as separate operational data.

Red and blue sidebands are standard physical inputs, not new UEOT laws. Wineland et al., *Quantum information processing with trapped ions*, Phil. Trans. R. Soc. Lond. A **361**, 1349–1361 (2003), DOI [10.1098/rsta.2003.1205](https://doi.org/10.1098/rsta.2003.1205), derive the red/blue operators and number-dependent couplings in the interaction picture under Lamb–Dicke and rotating-wave assumptions (pp. 1350–1351; [NIST full text](https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=105685)). Their laboratory approximation does not establish this project's device accuracy. In particular, extending a linear sideband approximation to every vector in the analytic cutoff \(N=4095\) requires a valid device-domain or error bound over that domain. A small mean excitation alone is not a uniform Lamb–Dicke condition on every allowed Fock component.

## 2. Self-adjoint realization, not formal notation

The red operator \(A\) reduces the one-dimensional vacuum block \(|g,0\rangle\) and the two-dimensional blocks

\[
F_m=\operatorname{span}\{|e,m-1\rangle,|g,m\rangle\},\qquad m\ge1.
\]

On \(F_m\), \(A=\sqrt m\sigma_x\), and \(G=mI\). Thus \(A^2=G\), \(D(A)=D(G^{1/2})\), and \(U_1\) strongly commutes with every spectral projection of \(G\). The phase gate does so as well.

The blue operator reduces the orthogonal blocks

\[
E_n=\operatorname{span}\{|g,n\rangle,|e,n+1\rangle\},\qquad n\ge0,
\]

and the separate vector \(|e,0\rangle\). On \(E_n\), it is \(\sqrt{n+1}\sigma_x\); on \(|e,0\rangle\) it vanishes. For

\[
\psi=c_{e,0}|e,0\rangle+
\sum_{n\ge0}(c_{g,n}|g,n\rangle+c_{e,n+1}|e,n+1\rangle),
\]

the self-adjoint domain is exactly

\[
D(B)=\left\{\psi:\sum_{n\ge0}(n+1)
   (|c_{g,n}|^2+|c_{e,n+1}|^2)<\infty\right\}.
\tag{B.3}
\]

To verify self-adjointness directly, the block inverses of \(B\pm iI\) have norm at most one. Their direct sum is a bounded inverse mapping every Hilbert-space vector into the stated graph domain, because
\(\|B(B\pm iI)^{-1}x\|\le\|x\|\).
Consequently both ranges are the whole Hilbert space, so the densely defined symmetric direct sum is self-adjoint. Finite block truncations converge in graph norm, giving a core. The spectral theorem defines \(B_\beta\) for every real \(\beta\), and on each block

\[
B_\beta|g,n\rangle=
\cos(\beta\sqrt{n+1})|g,n\rangle
-i\sin(\beta\sqrt{n+1})|e,n+1\rangle.
\tag{B.4}
\]

The reverse formula has the same coefficients. The isolated \(|e,0\rangle\) is fixed. This is a proof on normal Hilbert-space/trace-class objects, not a claim that a finite-matrix Lean build verifies unbounded operator domains.

## 3. Derived finite growth and rectangular branch completeness

Put \(\Pi_M=1_{G\le M}\) for a nonnegative integer \(M\). Its dimension is \(2M+1\). The two \(G\)-eigenvalues in \(E_n\) are \(n\) and \(n+2\). Therefore (B.4), together with the reverse formula, proves

\[
B_\beta\Pi_M=\Pi_{M+2}B_\beta\Pi_M,
\qquad V_1\Pi_M=\Pi_{M+2}V_1\Pi_M,
\qquad V_0\Pi_M=\Pi_MV_0\Pi_M.
\tag{B.5}
\]

These identities hold for all real pulse areas. Small \(\beta\) is not required for exact support growth. For any product containing at most \(L\) blue pulses, the support of an input in \(\Pi_N\) is contained in \(\Pi_{N+2L}\). A finite adaptive tree inherits this by induction over its actual branches. Any added hidden Kraus refinement must represent the same already admitted CP event, or have its own source-derived bound (B.5); this phrase does not authorize arbitrary extra operations. For an equivalent Kraus decomposition, positivity of the summed outside-support norm shows that each refined Kraus operator has the same support property. The allowed controller and its observation fibres remain fixed. A controller is not given the unknown \(\theta\), an unobserved Kraus index, or future labels.

Let \(J_M:\mathbb C^{2M+1}\to\mathcal H_S\) be the canonical isometry onto the cutoff. A uniform one-slot output carrier \(\mathbb C^{2(M+2)+1}\) allows the exact rectangular branches

\[
K_{o,M}^{\rm fin}=J_{M+2}^\dagger K_oJ_M,
\qquad o\in\{0,1,f\}.
\tag{B.6}
\]

The larger output carrier is used even for outcomes that do not raise excitation. From (B.5), not from an assumed certificate field,

\[
K_oJ_M=J_{M+2}K_{o,M}^{\rm fin}.
\]

Completeness follows:

\[
\sum_o(K_{o,M}^{\rm fin})^\dagger K_{o,M}^{\rm fin}
=J_M^\dagger\sum_oK_o^\dagger K_oJ_M=I.
\tag{B.7}
\]

Thus each full rectangular instrument is CPTP on its **entire declared input carrier**, while each event is CP and trace-nonincreasing. It is unnecessary and generally false to assert that the rectangular \(V_1\) is onto its larger carrier. Path-specific carriers are also possible, but all final outputs must be embedded into the common \(\Pi_{N+2L}\) carrier, keeping their terminal records distinct, before a trace distance is computed.

For a finite complete tree \(\pi\), let \(\Omega_\beta^\pi\) be its full CQ output, including all failure and stop labels and the terminal \(SR\) state. Its finite version \(\Omega_{N,\beta}^\pi\) is built from (B.6). Multiplying the derived intertwining identities and retaining all terminal branches proves

\[
\Omega_\beta^\pi((J_N\otimes I_R)\rho_N(J_N^\dagger\otimes I_R))
=\iota_{N+2L}\Omega_{N,\beta}^\pi(\rho_N).
\tag{B.8}
\]

The completed tree is normal CPTP. If \(\operatorname{Tr}G\rho_S\le\bar n<N+1\), spectral Markov gives \(\delta_N=1-\operatorname{Tr}\Pi_N\rho_S\le\bar n/(N+1)\), so \(s_N=1-\delta_N>0\). Define the finite normalized projected joint input exactly as

\[
\rho_N=\frac{(J_N^\dagger\otimes I_R)\rho(J_N\otimes I_R)}{s_N}.
\]

When writing its excitation expectation below, use the restricted observable \(J_N^\dagger GJ_N\), equivalently first embed the state using \(J_N\). The inherited purification projection estimate and complete-output contractivity yield

\[
D\bigl(\Omega_\beta^\pi(\rho),
        \iota_{N+2L}\Omega_{N,\beta}^\pi(\rho_N)\bigr)
\le\sqrt{\bar n/(N+1)}.
\tag{B.9}
\]

This is uniform over the declared finite-height classical policies and finite untouched references. There is no extra \(L\) factor on this initial-tail term: the growing carriers represent the projected-input dynamics exactly. It is not a statement about a fixed cutoff, an arbitrary nonconserving Hamiltonian, infinite-time stopping, coherent controllers, or an energy-constrained diamond norm of two fixed channels.

## 4. Same source, seven records, and conditional target

Run at most two source steps and stop at the first \(f\). All seven terminal records remain

\[
\mathcal R=\{f,0f,1f,00,01,10,11\}.
\]

Each \(V_o\) is unitary on the full Hilbert space. Hence the seven source probabilities are unchanged from Chapter 67:

\[
1-s,\quad s(1-q)(1-s),\quad sq(1-s),\quad
s^2(1-q)^2,\quad s^2q(1-q),\quad s^2q(1-q),\quad s^2q^2.
\tag{B.10}
\]

The terminal states use chronological products, e.g. record \(01\) has \(V_1V_0\rho V_0^\dagger V_1^\dagger\). A failure step applies identity and then stops; the prior successful gates are not undone. The actual source acceptance effect is still \(s^2I\), and effects on still-successful prefixes are \(H_t=s^{2-t}I\). Failure leaves have zero acceptance effect.

Normalizing exactly the four successful branches therefore produces a CPTP conditional channel \(T_\beta\) with Bernoulli \(q\) record weights. The three source-failure blocks remain present with zero target mass. The raw source remains a different complete instrument with nonzero failures. The compiler approximates \(T_\beta\), not the unconditional raw source with its failures deleted.

The same-source compiled policy \(C_\beta\) uses \(V_0,V_1\), first-label probability \(1/2\), and second-label-one probabilities \(312/625\) after zero and \(313/625\) after one. Its path probabilities are

\[
Q_{00}=Q_{11}=313/1250,
\qquad Q_{01}=Q_{10}=312/1250.
\tag{B.11}
\]

For each record the target and compiler have identical conditional terminal states, now including the blue dynamics. Orthogonality of the classical records gives their full CQ distance as the classical TV distance exactly, for every legal joint input and reference. Thus Chapter 67's \(1/50\) design-region bound and its minimax scope are inherited without imposing \(\beta=0\). Its optimality is still restricted to the frozen full interval and labelled-action policy class; it is not optimality for every narrower calibration set or for additional parameter-sensitive queries.

## 5. Low-spectrum filtering and its complete output

The physical filter is the two-outcome projective test \(\{\Pi_N,Q_N\}\), \(Q_N=I-\Pi_N\). It records pass/fail. On failure reset only \(S\) to \(\tau_0=|g,0\rangle\langle g,0|\) and retain the actual reference output

\[
\rho_R^{\rm fail}=\operatorname{Tr}_S[(Q_N\otimes I_R)\rho(Q_N\otimes I_R)].
\tag{B.12}
\]

This subnormalized reference state has trace \(\delta_N\); it is not a fresh reference and must not be replaced by a fixed reference state. The complete filtered preparation is

\[
|\mathrm{pass}\rangle\langle\mathrm{pass}|\otimes P\rho P
 +|\mathrm{prep\_fail}\rangle\langle\mathrm{prep\_fail}|\otimes
      \tau_0\otimes\rho_R^{\rm fail},
\quad P=\Pi_N\otimes I_R.
\tag{B.13}
\]

Against ideal always-pass preparation of \(\rho\), P-MICRO-02 already proves the sharper full-output bound

\[
f(\delta_N)=\frac{\delta_N+\sqrt{\delta_N(4-3\delta_N)}}2.
\tag{B.14}
\]

For completeness: purify \(\rho\), resolve its pass and fail components, and diagonalize the difference in their two-dimensional span. The successful block's trace norm is \(\sqrt{4\delta_N-3\delta_N^2}\); the orthogonal failure block contributes \(\delta_N\). Partial trace and common subsequent CPTP processing contract this difference. The bound is attained for pure two-sector inputs. It is increasing on \([0,1]\), allowing substitution of the spectral tail bound.

**Specific correction to a generic warning.** Passing an arbitrary heralded operation can raise normalized excitation. Passing this particular low-spectrum filter cannot. Let \(p=1-\delta_N>0\), and let \(m_-\) and \(m_+\) be the conditional \(G\) means below and above the cutoff. When both components are nonzero,

\[
m_-\le N<N+1\le m_+,
\qquad \operatorname{Tr}G\rho_S=pm_-+(1-p)m_+\ge m_-.
\tag{B.15}
\]

The cases with zero tail are immediate. Since \(\Pi_N\) commutes with \(G\), off-diagonal input blocks do not contribute to the energy expectation. Therefore

\[
\operatorname{Tr}G(\rho_N)_S\le\operatorname{Tr}G\rho_S\le\bar n.
\tag{B.16}
\]

This uses the actual low-spectrum ordering, not merely trace-nonincreasing CP or a generic success probability. It must not be generalized to arbitrary postselected protocol branches. No physical source-copy or retry permission follows from projection.

## 6. Omission bound from the conserving reference prefixes

The proposed cheaper implementation \(C_0\) uses the same visible adaptive weights (B.11) but omits \(B_\beta\), using the red gate \(U_1\). The target remains \(T_\beta\); \(\beta\) is not set to zero in the source to make the compiler exact.

On the blue blocks,

\[
B^2=a^\dagger a+P_g=G+I-2P_e\le G+I.
\tag{B.17}
\]

For a purification \(\psi\) of a normal input of finite excitation mean \(E\), the spectral inequality \(|e^{-ix}-1|\le|x|\) gives

\[
\|(B_\beta-I)\otimes I\,\psi\|^2
\le\beta^2\langle\psi|B^2\otimes I|\psi\rangle
\le\beta^2(E+1).
\tag{B.18}
\]

Finite \(E\) ensures that the purification belongs to the quadratic-form domain needed here. The pure-state trace distance does not exceed the vector distance, and partial trace contracts, so the same bound holds for arbitrary joint input and untouched reference:

\[
D((B_\beta\otimes I_R)\rho(B_\beta^\dagger\otimes I_R),\rho)
\le\min\{1,|\beta|\sqrt{E+1}\}.
\tag{B.19}
\]

For a fixed record \(r=(r_1,\ldots,r_L)\), expand the difference between the actual and no-blue ordered products by the telescoping identity

\[
V_{r_L}\cdots V_{r_1}-U_{r_L}\cdots U_{r_1}
=\sum_{j=1}^L
 V_{r_L}\cdots V_{r_{j+1}}
 (V_{r_j}-U_{r_j})
 U_{r_{j-1}}\cdots U_{r_1}.
\tag{B.20}
\]

Every right-hand prefix is the **no-blue reference** prefix, so it strongly preserves \(G\), even though the actual prefixes need not. Terms with \(r_j=0\) vanish; terms with \(r_j=1\) contain \((B_\beta-I)U_1\). All left-hand suffixes are unitary and do not increase vector norm. Hence the pathwise state error is at most

\[
n_1(r)|\beta|\sqrt{E+1},
\tag{B.21}
\]

where \(n_1(r)\) is the number of ones in that actual record. Because the two compared policies use the same record probabilities \(Q_r\), full CQ trace distance sums the pathwise errors with those probabilities. For (B.11),

\[
\sum_rQ_r n_1(r)
=Q_{01}+Q_{10}+2Q_{11}=1,
\]

so

\[
D(C_\beta(\rho),C_0(\rho))
\le\min\{1,|\beta|\sqrt{E+1}\}.
\tag{B.22}
\]

This proof controls terminal states as well as all records. It does not infer an operator-norm bound independent of energy for the unbounded blue generator. It also does not use the source target's expected count \(2q\) in place of the compiler's exact expected count one. For more general operations with state-dependent label probabilities, the common \(Q_r\) argument must be replaced by a correctly weighted hybrid-prefix defect proof. Arbitrary postselected reference paths need not retain the same energy budget.

## 7. Integrated precision and its limited margin

Let \(\widetilde T_\beta\) denote the ideal conditional target with deterministic preparation-pass, and let \(\widetilde C_{0,N}\) be the physical low-spectrum filter followed, on pass, by the no-blue compiler; retain the preparation-failure state (B.12). All outputs use the same prep flag, seven source-record labels, terminal-state embedding and reference.

Compare first with the filtered target using (B.14), then the matched-blue compiler using the inherited full CQ bound \(\Delta=1/50\), then omit blue using (B.22) on the filtered input. Equation (B.16) controls its energy. Therefore

\[
D(\widetilde T_\beta(\rho),\widetilde C_{0,N}(\rho))
\le f(\delta_N)+s_N\Delta+s_N|\beta|\sqrt{E_N+1}
\le f\!\left(\frac{\bar n}{N+1}\right)+\Delta+
      |\beta|\sqrt{\bar n+1}.
\tag{B.23}
\]

This route includes physical filter failure and preserves the same source parameter throughout. The source acceptance effect is scalar, so \(T_\beta\) is CPTP and no omitted \(1/s^2\) posterior factor is hidden here. General state-dependent acceptance still requires the inherited sharp postselection theorem and a positive success floor.

For the inherited budget and cutoff, with the **independent** pulse-area bound \(|\beta|\le1/100\),

\[
\bar n=1,\quad N=4095,\quad\Delta=1/50,
\]

\[
D_{\rm complete}\le
\frac1{50}+\frac{1+\sqrt{16381}}{8192}
+\frac{\sqrt2}{100}
=0.0498877753592667266948\ldots<\frac1{20}.
\tag{B.24}
\]

The remaining allowance for additional independently bounded complete-output discrepancies is only

\[
0.0001122246407332733051\ldots.
\tag{B.25}
\]

Using the earlier looser filter bound \(65/4096\) instead gives \(0.050011276248730950\ldots\), which **fails** the fixed \(0.05\) requirement. Thus neither rounding nor an unmeasured ideal-device assumption may consume the remaining margin unnoticed. The sharper bound was already proved in P-MICRO-02 and is being used, not retroactively added as empirical evidence.

No physical measurement has supplied \(|\beta|\le0.01\), source/action gate matching, Lamb–Dicke/RWA error, filtering accuracy, preparation/readout error, or a terminal-state statistical certificate. All are model or data obligations. The theorem is a conditional mathematical sufficient bound, not a current real-device precision claim.

## 8. Failure controls and explicit non-extensions

### 8.1 Fixed cutoff loses mass

For \(|g,N\rangle\), a blue pulse creates \(|e,N+1\rangle\) of total excitation \(N+2\). A fixed \(\Pi_N\) compression loses

\[
\sin^2(\beta\sqrt{N+1})
\]

probability for generic \(\beta\). Renormalizing this compression does not make it the original deterministic gate and can change state-dependent record probabilities. The valid replacement is the rectangular growth carrier or an explicit leakage instrument with a separate error budget.

### 8.2 Actual CP order is consequential

With \(\beta=\pi/2\), \(\alpha=\pi/(2\sqrt2)\), and input \(|g,0\rangle\), red then blue ends in \(|e,1\rangle\) up to phase, while blue then red ends in \(|g,2\rangle\) up to phase. The two terminal density matrices have trace distance one. This is a channel-level noncommuting witness, not merely a statement about a Kraus-matrix commutator. These large angles are a semantic negative control, not part of the small-\(\beta\) deployment certificate.

### 8.3 Simultaneous Rabi interaction has an infinite tail

On the finite Fock core, the red-plus-blue expression is

\[
A+B=\sigma_x(a+a^\dagger)
\]

For this counterexample choose its self-adjoint quadrature realization: let \(X=a+a^\dagger\) denote the canonical self-adjoint oscillator quadrature, agreeing with the displayed expression on the finite Fock core, and set \(H_{\rm sim}=\sigma_x\otimes X\) with the corresponding direct-sum domain \(D(X)\oplus D(X)\) in the \(\sigma_x\) basis. This specifies the self-adjoint extension/closure and does not infer self-adjointness merely from a formal sum of two unbounded operators on an arbitrary intersection domain. For a \(\sigma_x\) eigenvector \(|+\rangle\) and oscillator vacuum,

\[
e^{-i\tau H_{\rm sim}}|+\rangle|0\rangle
=|+\rangle|-i\tau\rangle,
\quad
\langle n|-i\tau\rangle=e^{-\tau^2/2}
\frac{(-i\tau)^n}{\sqrt{n!}}.
\tag{B.26}
\]

For every nonzero \(\tau\), all these amplitudes are nonzero. The input lies within \(\Pi_1\), but no finite \(\Pi_M\) contains the output. This exact counterexample disproves transfer of (B.5) to an arbitrary simultaneous Rabi pulse. It does not assert that every Rabi Hamiltonian has this simple coherent-state solution, or that controlled approximations for simultaneous dynamics are impossible.

### 8.4 Flag calibration cannot identify blue area

All record probabilities (B.10) are independent of \(\beta\). Consequently every amount of flag-only calibration has the same law for any two \(\beta\) values. Terminal-state responses can differ: starting from \(|g,0\rangle\), one label-one action produces \(\cos\beta|g,0\rangle-i\sin\beta|e,1\rangle\), whose excitation mean is \(2\sin^2\beta\). A phase-sensitive observable can distinguish signed small \(\beta\), whereas energy alone sees an even periodic function. A pulse-area interval therefore requires genuinely additional observations or an independent control guarantee; it cannot be read from a flag confidence set.

## 9. Cost interface and actual success probability

One attempted source delivery first prepares the input and performs the physical filter. Only on pass are the at-most-two source steps run. The total successful-delivery probability is

\[
p_{\rm attempt}=s_Ns^2.
\tag{B.27}
\]

Under the measured-flag/feed-forward implementation, the expected number of blue pulses per complete source attempt is

\[
s_Nsq(1+s).
\]

For the matched-blue compiler it is \(s_N\); for the no-blue compiler it is zero. A coherently controlled implementation can schedule one blue-control slot on every reached source step, giving \(s_N(1+s)\) scheduled source slots, or \(2s_N\) compiled slots, even though the mathematical random branch uses the blue action less often. Which quantity is billed is an implementation fact, not a consequence of the record law alone.

Let \(\mu\) be the actual expected cost of one complete attempt, including input preparation, filter, all failures, reset, auxiliary flags, gates, control, readout, classical computation and records. If each new attempt is an independent fresh re-preparation with this same joint cost/success law, renewal gives expected cost \(\mu/(s_Ns^2)\). Outcome and cost within an attempt may be correlated; fresh attempts are the required independence. One-time calibration cost is amortized separately per delivered output. Unknown input states and their reference correlations are not free reproducible resources. No measured time, energy or economic advantage follows from the model count.

## 10. Verification scope and next exact responsibility

The proofs above are analytical. Existing finite rectangular-channel and operational-equivalence Lean results are reused only for their actual finite domain; no new unbounded self-adjointness, trace-class, continuum-time or robust omission theorem has been machine-checked here. The independent numerical script checks finite rectangular completeness, growing-carrier/full-ambient agreement, every raw record, reference-retaining complete distances, and the stated negative controls. These numerical checks do not prove universal quantifiers and are not hardware data.

The next precise dynamical responsibility, after this segmented family, is an **approximate** finite-CQ bridge for a specified simultaneous red/blue Hamiltonian. It must control an actual per-prefix boundary or Duhamel defect (with the same interventions, reference and terminal records), not assume a hard finite support that (B.26) disproves. For a proposed device realization, the immediate data responsibility is a calibrated \(\beta\) bound and all additional complete-output errors small enough to fit (B.25). The existing QFT/EFT, particle, gravity, independent quantum-selection and empirical responsibilities remain open.
