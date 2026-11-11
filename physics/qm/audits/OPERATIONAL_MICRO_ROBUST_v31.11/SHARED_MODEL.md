# Shared model and frozen acceptance contract — v31.11

Research baseline: `16a89154183c22030d4526413167d095d94e6890` (current main read back on 2026-11-11). Scientific inheritance: v31.10 / Kernel 1.10; bilingual publication inheritance: 3.7. This is a new physics research iteration. The 96 historical claim objects and their execution identities are not reclassified. Core is read-only. Three native AI research agents A/B/C work in isolated drafts; root alone integrates shared sources and metadata. Their review is internal AI review.

## 1. Scope, physical inputs, and units

The system is \(\mathcal H_S=\mathbb C^2_P\otimes\ell^2(\mathbb N_0)\), with \(G=I\otimes a^\dagger a+P_e\otimes I\). G and the budget \(\bar n\) are dimensionless. \(\Pi_N=1_{G\le N}\) has rank \(2N+1\). The reference R is any finite positive-dimensional complex system, untouched throughout. The initial joint density \(\rho_{SR}\) may be entangled, with \(\operatorname{Tr}G\rho_S\le\bar n<N+1\); fresh auxiliary registers are initially independent of SR and of earlier auxiliaries.

Complex Hilbert spaces, tensor composition, the Born rule, quantum instruments, oscillator Fock structure, external controls, and the chosen Hamiltonians are P/S inputs. They are not derived from generic Core. Rotating-wave/exact Jaynes–Cummings use is a declared E/model assumption when relating the mathematical Hamiltonian to a device. No device accuracy is assumed measured.

On excitation blocks, use phase and exchange gates
\[
U_0=e^{-i\phi P_e},\qquad
U_1=e^{-i\alpha(a\sigma_++a^\dagger\sigma_-)}.
\]
The phases \(\phi,\alpha\) are dimensionless integrated pulse areas; a Hamiltonian has units of energy, with \(\alpha=gt\) for coupling angular frequency g. Direct-sum self-adjointness and the natural square-summable graph domain are proved in B's report. Both gates strongly preserve G. A vacuum two-level collision producing actual excitation loss is an additional admitted control, with its microscopic derivation and a noncommuting CP-map pressure test supplied separately.

## 2. Same-source flagged instrument

The unknown but fixed shared parameter is \(\theta=(q,\phi,\alpha)\). Define \(s(q)=1-q/2\) and freeze \(q\in[12/25,13/25]\) for the certified deployment case. Phase/exchange uncertainties are shared nuisance parameters: the source, conditional target, and physical action library use the same actual gates, not independently substituted nominal gates.

A fresh three-level logical flag F has a degenerate excitation operator \(G_F=0\), initial state \(|f_*\rangle\), and a unitary preparation W(q) whose selected column is
\[
\sqrt{s(1-q)}|0\rangle+\sqrt{sq}|1\rangle+\sqrt{1-s}|f\rangle.
\]
Controlled application of \(U_0,U_1,I\), followed by complete flag readout, derives
\[
K_0=\sqrt{s(1-q)}U_0,\quad K_1=\sqrt{sq}U_1,\quad K_f=\sqrt{1-s}I.
\]
The preparation and controlled gates commute with total excitation \(G+G_F\). Degeneracy of the logical flag does not mean its preparation, control, measurement, storage, or reset has zero laboratory cost. W(q) is explicit in the micro report; its column is not a target-output certificate.

Perform at most two source steps, stop immediately on f, and accept exactly two successful steps. Keep all seven terminal records:
\[
\mathcal R=\{f,0f,1f,00,01,10,11\}.
\]
Record order is chronological; terminal system and R are retained. Source acceptance is derived as \(p=s^2\ge1369/2500\). On still-successful prefixes the backward effects are \(H_t=s^{2-t}I\); the acceptance effect at a failure leaf is zero. the normalized conditional channel has Bernoulli(q) weights on its four successful histories and zero blocks on the three failure histories. This consumes the already proved Chapter 66 source construction. It is a conditioned target, not an assertion that an unconditional source has no failures.

## 3. Allowed implementation, visibility, and precision

At every visible history the allowed library can implement the same actual gate U0 or U1 and emit its corresponding visible label. Deploy a classical independent coin of fixed weight \(w=1/2\), chosen before unknown θ is known. The coin result is exactly the visible action/flag label, not an extra erased record. There is no access to a hidden Kraus index, true q, or future result. All nodes in one declared observation fiber use the same w. Fresh randomization and ancillary reset are explicit physical inputs; arbitrary correlated or coherent controllers are outside this instance.

All comparisons use normalized complete CQ trace distance
\(D(\Omega,\Gamma)=\tfrac12\|\Omega-\Gamma\|_1\), including every terminal record and terminal SR state, with the same finite-state embedding. Never replace this with success-only record frequencies or terminal marginal distance. Conditional target failures have zero weight but remain in the output alphabet.

The precomputed required deployment precision is **1/20**. For two steps and identical path-conditioned system states the target/compiled discrepancy is exactly
\[
|q-w|(1+|q+w-1|)\le51/2500.
\]
This formula is to be proved and independently checked, not taken as input to a certificate. The all-state/all-reference scope follows from the equality of the path-conditioned states, which is separately proved. A finite family of observed testers alone cannot certify that scope on a real device.

## 4. Truncation and physical preparation

B must derive branch filtration from the microscopic unitary/vacuum conditions and derive finite adaptive complete-record CPTP semantics. It may inherit the initial projection estimate P-QINF-02 but must not assume branch intertwining or the requested output error.

Set \(s_N=\operatorname{Tr}[(\Pi_N\otimes I_R)\rho]\) and \(\rho_N=(\Pi_N\otimes I_R)\rho(\Pi_N\otimes I_R)/s_N\). The general analytic certificate uses \(\bar n=1,N=4095\), so \(1-s_N\le1/4096\) and the normalized truncation error is at most 1/64. No numerical allocation of this large matrix is needed to prove the uniform bound. The exact finite matrix instance uses N=1, a known supported state, phase factor \((3+4i)/5\), and exchange cosine/sine 3/5 and 4/5. This second instance is a calculation, not proof over all oscillator states.

Because acceptance is scalar and input-independent, the conditioned target here is CPTP, so its truncation error is directly at most 1/64. A generic state-dependent accepted process instead requires the separately proved trace-class posterior theorem and a positive success floor. That distinction must be preserved.

Physical projection preparation uses the explicitly enlarged common alphabet {prep_fail} ∪ {pass}×R and keeps all pass/fail records; the ideal comparison has zero mass on prep_fail. For general energy-bounded input, compare the ideal always-pass target with the actual filter's full output, adding the proved preparation-failure allowance (a simple additional 1/4096 is sufficient). The exact supported instance has s_N=1. Unknown quantum input is never assumed repeatable. Retry costs apply only to explicitly re-preparable iid source trials. End-to-end error budgets must list cutoff, physical preparation, gate mismatch, numerical rounding, calibration coverage, and statistical testing separately; absent device-error bounds are not silently set to zero for nature.

## 5. Data, costs, and evidence

No matching real hardware counts have been supplied or acquired. C may implement a synthetic calibration pipeline with 80000 independent model shots, \(\widehat q=2k_f/n\), and a Hoeffding confidence radius 1/100; retain all flags in the raw file and state the iid/fixed-nuisance assumptions. A model-based confidence set is not certification that a device belongs to the model. Calibration and held-out tests are separate. A supplied set [12/25,13/25] is first a mathematical uncertainty set; deployment only claims statistical coverage when the observed confidence set lies within its stated domain.

Costs include source preparation, physical projection and its failed attempts, auxiliary preparation, randomization, gates, readout, resets, classical computation, records, calibration, and retained failures. Per-attempt expected additions enter the retry numerator. A one-time calibration campaign cost is separately amortized per delivered output, not divided by the success probability twice. Report symbolic exact source/compiled costs and conditions; no measured time, joule, or monetary advantage is claimed.

Evidence axes remain separate: mathematical proof; machine proof; exact finite arithmetic; floating diagnostic; synthetic statistics; real external/project measurement. The latter two empirical categories remain unverified without matched data. The full quantum/field/particle/gravity program stays on the existing ROADMAP, with precise next statements.

## 6. File ownership and acceptance

A: isolated operational proof, OPT inventory, candidate Lean module, exact controls. B: isolated micro/analytic proof and finite controls. C: isolated robust-certificate proof, checker, synthetic analysis and data contract. Root: shared contract, independent end-to-end computation, one continuous bilingual chapter, existing dossier/manifest/ledger/CURRENT/ROADMAP, source-bound evidence, integration. Cross-review is A→B, B→C, C→A, with two strongest-claim attacks and resolved findings recorded. No extra subagents are created.

## 7. Analytic refinement after the original freeze

Before inspecting synthetic data, root derived and C independently checked a visible-history policy within the already declared library. Put δ=1/50. Choose the first label with weight 1/2; choose label 1 at step two with weight 313/625 after history 1 and 312/625 after history 0. Its path law is Q00=Q11=313/1250 and Q01=Q10=312/1250. For t=q−1/2 and u=δ²−t², the complete CQ distance is max(|t|,u)+u≤δ. Any policy with θ-independent record law has worst-case error at least δ from the two endpoint record marginals, so this policy is minimax for the stated allowed history/label-only library. Extra q-sensitive in-run queries or intermediate testers would change the decision problem.

This does not revise the original precision 1/20 or source model. It improves the full physical preparation bound from 65/4096+51/2500 to 65/4096+1/50=0.035869140625. It sacrifices exact nominal q=1/2 matching (nominal error 1/1250) to improve worst-case error. Both policies and their observation assumptions remain recorded.

A subsequent narrow long-time statement fixes the actual rational phase/exchange gates above and restricts states to exactly G=1. The source's scalar Doob channel has an explicit uniform two-step Bloch contraction bound 49/50 for q in the same interval. Excitation weights remain invariant in the full oscillator, so this is not global uniqueness or oscillator-wide mixing. Its exact rational checker and proof are separate from the finite two-step implementation certificate.
