<a id="ch-68"></a>

# 68. Segmented excitation growth and controlled blue-pulse omission

Chapter 67 established finite truncation for excitation-preserving operations. This chapter permits one specific form of excitation growth: an independently applied blue-sideband pulse follows the original red-sideband pulse. The essential step is to derive a support increase of at most two from the actual generator. Finite carriers then grow with the steps and preserve complete predictions. A separate small-pulse premise supports a bound for omitting the blue pulse. This is a specified nonconserving extension; it does not cover general Rabi dynamics, infinite time, or all continuous fields.

## 68.1 The common model and additional inputs

Retain the probe, oscillator, excitation observable, any finite positive-dimensional reference, and a bounded initial mean. The reference is untouched and may initially be entangled with the system. The parameter is now a four-tuple. Phase, red, and blue areas are dimensionless integrated couplings. The order below is red first and blue second; separated operations are not replaced by simultaneous evolution.

$$
\begin{gathered}
\mathcal H_S=\mathbb C^2\otimes\ell^2(\mathbb N_0),\quad
G=a^\dagger a+P_e,\quad \Pi_M=1_{G\le M},\quad
\theta=(q,\phi,\alpha,\beta),\\
A=\sigma_+a+\sigma_-a^\dagger,\quad
B=\sigma_+a^\dagger+\sigma_-a,\quad
U_0=e^{-i\phi P_e},\quad U_1=e^{-i\alpha A},\\
B_\beta=e^{-i\beta B},\quad V_0=U_0,\quad V_1=B_\beta U_1,\quad
q\in[12/25,13/25],\quad s=1-q/2.
\end{gathered}
$$

Complex Hilbert structure, the Born rule, tensor composition, the Fock representation, and CP instruments remain explicit P/S inputs. A chapter using these inputs cannot establish that Core uniquely selects complex quantum theory. An external drive supplies work to the blue pulse; a degenerate logical flag does not turn the operation into an excitation-conserving closed system.

Red and blue sidebands and their number-state couplings are standard physics. Wineland and colleagues derive these operators and square-root couplings in the interaction picture under Lamb-Dicke and rotating-wave assumptions [*Quantum information processing with trapped ions*, DOI 10.1098/rsta.2003.1205, pp.1350-1351]. Here the separated effective Hamiltonians define an exact mathematical model. A device application separately needs bounds for detuning, pulse overlap, readout, filtering, and effective-model errors. A large analytic cutoff does not establish Lamb-Dicke validity throughout its carrier.

## 68.2 A growth window derived from a self-adjoint generator

<a id="p-micro-04"></a>

**P-MICRO-04 (Finite excitation growth under segmented blue pulses).** For every nonnegative integer cutoff and every real pulse area, the blue unitary maps the cutoff carrier into the carrier whose upper bound is two larger. Any legal finite classical control tree with a bounded number of blue pulses satisfies the accumulated branchwise growth bound. This is a consequence of the source operator, not an input certificate field.

**Proof.** The red generator vanishes on the vacuum and acts as the square root of total excitation times the Pauli exchange matrix on each fixed-excitation block. The blue generator instead decomposes into an isolated vector and the following orthogonal two-dimensional blocks:

$$
\begin{gathered}
E_n=\operatorname{span}\{|g,n\rangle,|e,n+1\rangle\},\quad
B|_{E_n}=\sqrt{n+1}\,\sigma_x,\quad B|e,0\rangle=0,\\
D(B)=\left\{\psi:\sum_{n\ge0}(n+1)
\bigl(|c_{g,n}|^2+|c_{e,n+1}|^2\bigr)<\infty\right\},\\
B_\beta|g,n\rangle=
\cos(\beta\sqrt{n+1})|g,n\rangle
-i\sin(\beta\sqrt{n+1})|e,n+1\rangle,\\
B_\beta\Pi_M=\Pi_{M+2}B_\beta\Pi_M,\qquad
V_1\Pi_M=\Pi_{M+2}V_1\Pi_M.
\end{gathered}
$$

On the stated graph domain the blue generator is self-adjoint. Each finite block is symmetric, and the two shifts $B± iI$ have inverses of norm at most one. The direct sums are bounded, everywhere-defined inverses whose ranges lie in the graph domain. Both shifted ranges are therefore the whole space, establishing self-adjointness. Finite-block vectors are dense in graph norm. The spectral theorem defines the unitary for every real area, and exponentiation in each block gives the displayed formula and its reverse.

The two total excitations in a blue block differ by two, proving the support statement. Red, phase, and failure-identity operations do not raise the bound; induction along the tree gives cumulative growth. Small blue area is unnecessary. A hidden Kraus refinement must represent the same already established CP event or have an independent microscopic support proof. Arbitrary additional operations do not inherit the statement. ∎

## 68.3 Rectangular instruments, stopping records, and composition

<a id="p-opt-04"></a>

**P-OPT-04 (Complete rectangular operations on growing carriers).** For fixed finite actions, outcomes, observation permissions, and maximum height, the microscopic source defines complete rectangular finite instruments at every step. After embedding all stopping branches into one final carrier, their complete CQ output equals that of the infinite system on the projected input. The equality preserves every visible label and any finite untouched reference.

Explicitly let $L$ be the maximum number of operation slots, with at most one blue pulse per slot, and assume $\operatorname{Tr}G\rho_S\le\bar n<N+1$. Set $s_N=\operatorname{Tr}[(\Pi_N\otimes I_R)\rho]>0$ and the finite-coordinate state $\rho_N=(J_N^\dagger\otimes I_R)\rho(J_N\otimes I_R)/s_N$. On each CQ label block, $\iota_{N+2L}$ conjugates by $J_{N+2L}\otimes I_R$ into the common physical Fock space and preserves the label. The ideal output for an untruncated input may still have an infinite tail; a common finite-carrier calculation here applies only to projected inputs or examples with known support. Let each embedding have the corresponding spectral carrier as its range. The original three-state flag preparation and complete readout give the source branches; finite branches are restrictions of the actual maps:

$$
\begin{gathered}
K_0=\sqrt{s(1-q)}V_0,\quad K_1=\sqrt{sq}V_1,\quad K_f=\sqrt{1-s}I,\\
J_M:\mathbb C^{2M+1}\longrightarrow\mathcal H_S,\quad
K_{o,M}^{\rm fin}=J_{M+2}^\dagger K_oJ_M,\\
K_oJ_M=J_{M+2}K_{o,M}^{\rm fin},\qquad
\sum_o(K_{o,M}^{\rm fin})^\dagger K_{o,M}^{\rm fin}=I,\\
\Omega_\beta^\pi\bigl((J_N\otimes I_R)\rho_N(J_N^\dagger\otimes I_R)\bigr)
=\iota_{N+2L}\Omega_{N,\beta}^\pi(\rho_N),\\
D\bigl(\Omega_\beta^\pi(\rho_{SR}),
\iota_{N+2L}\Omega_{N,\beta}^\pi(\rho_N)\bigr)
\le\sqrt{\bar n/(N+1)}.
\end{gathered}
$$

**Proof.** The preceding support theorem shows that inserting the output projection leaves each source branch unchanged. Substituting the derived intertwining identities into source completeness proves completeness on the entire finite input carrier. A rectangular restriction of the unitary is an isometry and need not be onto. Multiply the intertwining identities along each path and take the direct sum over orthogonal terminal records to obtain complete-output equality. Nodes within an observation fiber have the same control weights; distinguishable histories may have different weights. Composition on the operational quotient remains legitimate.

Every early stopping block is embedded into the common final carrier before comparison. The completed finite tree is normal CPTP. The spectral Markov bound and Chapter 67's projected-state estimate then give the final inequality. The finite-coordinate state is obtained by restricting the normalized projected joint state through the embedding. No extra height factor multiplies the initial tail term, because growing carriers represent its subsequent dynamics exactly. This is an ordinary trace-distance comparison on a declared input family, not a renamed energy-constrained diamond norm. ∎

Compressing the blue pulse into the old fixed carrier loses probability: a boundary ground state transfers squared-sine mass into its excluded partner. This is a failure of the actual CP output mass, not a conclusion drawn merely from anticommuting Kraus matrices. The program compares the rectangular construction with Chapter 66's original interpreter using a unitary completion on the common carrier. Its action at unreachable boundary columns is not asserted to equal the full oscillator unitary.

## 68.4 Low-spectral filtering, the reference, and a correction

The previous wording of section 67.5 placed the general possibility of increased conditional energy after the particular low-spectral filter. That scope was too broad. This edition makes a minimal bilingual correction there, while retaining old execution records and result objects. In this model the retained spectrum is at most the cutoff and the rejected spectrum is at least one greater. When rejection has positive probability, the full mean is a convex combination of the two conditional means, so the retained mean is no larger. If rejection probability is zero, the passing state is the original state and the failure reference block is zero; no normalized zero-probability failure state is defined.

$$
\begin{gathered}
s_N=\operatorname{Tr}[(\Pi_N\otimes I_R)\rho_{SR}],\quad
\delta_N=1-s_N\le e_N:=\bar n/(N+1)<1,\\
\rho_N^{\rm emb}=\frac{(\Pi_N\otimes I_R)\rho_{SR}(\Pi_N\otimes I_R)}{s_N},
\qquad \operatorname{Tr}G(\rho_N^{\rm emb})_S\le\operatorname{Tr}G\rho_S,\\
\rho_R^{\rm fail}=\operatorname{Tr}_S[(Q_N\otimes I_R)\rho_{SR}(Q_N\otimes I_R)],
\quad Q_N=I-\Pi_N,\quad \tau_S=|g,0\rangle\langle g,0|,\\
\mathcal F_N(\rho)=
|{\rm pass}\rangle\langle{\rm pass}|\otimes s_N\rho_N^{\rm emb}
+|{\rm prep\_fail}\rangle\langle{\rm prep\_fail}|\otimes\tau_S\otimes\rho_R^{\rm fail},\\
f(e)=\frac{\sqrt{4e-3e^2}+e}{2},\quad
D\bigl(|{\rm pass}\rangle\langle{\rm pass}|\otimes\rho,\mathcal F_N(\rho)\bigr)
\le f(e_N).
\end{gathered}
$$

The last bound reuses P-MICRO-02 and is not counted as a new theorem. It follows from at most two nonzero eigenvalues of the purified pass-block difference and the failure mass, followed by contractivity under discarding the purification. Failure resets only the system; the reference retains its actual subnormalized failure-conditioned marginal. Replacing it by the failure probability times the unconditional reference changes the complete output, as an entangled-input control shows. The filter, reset, and record are physical operation assumptions, not free consequences of writing a projection.

## 68.5 Energy-weighted omission of the blue pulse

<a id="p-micro-05"></a>

**P-MICRO-05 (Complete-record omission bound using a no-blue reference).** Fix the same legal record policy and the same red and phase gates. Compare complete outputs with and without the blue pulses. If the normalized states along no-blue reference paths preserve the stated mean-excitation bound, local errors add with their subnormalized prefix masses. For this chapter's two-step visible policy, the mean selected blue-pulse count is exactly one, yielding the following uniform bound.

$$
\begin{gathered}
B^2=G+I-2P_e\le G+I,\qquad
\|(e^{-i\beta B}-I)\psi\|^2\le\beta^2\|B\psi\|^2,\\
D\bigl((B_\beta\otimes I_R)\sigma(B_\beta^\dagger\otimes I_R),\sigma\bigr)
\le|\beta|\sqrt{\operatorname{Tr}G\sigma_S+1},\\
Q_{00}=Q_{11}=313/1250,\qquad Q_{01}=Q_{10}=312/1250,\\
\mathbb E_Q[\#1]=1,\qquad
D(C_\beta(\rho),C_0(\rho))\le|\beta|\sqrt{\bar n+1}.
\end{gathered}
$$

**Proof.** Squaring on the blue blocks gives the first identity. The spectral theorem and the scalar exponential inequality give the vector bound. Purify a mixed state without acting on either reference or purification, bound pure-state trace distance by vector distance, and then discard the purification. Finite mean excitation places the purified vector in the domain of $B\otimes I$. The displayed expression uses $\|B\psi\|^2$ and does not require the operator domain of $B^2$.

Telescope the difference between the two complete processes slot by slot. After each local difference, the same actual future channel is applied and cannot increase trace norm. Before that difference, use the no-blue reference, so red and phase gates preserve the input energy bound. Zero-mass prefixes contribute zero without normalizing their states. Orthogonal record blocks give each contribution the mass of reaching its prefix and selecting label one. Both label-one marginals of the displayed policy are one half, so their mass sum is one. The preceding section ensures that the same mean budget holds after passing the low-spectral filter. ∎

This proof does not assume that actual blue-containing paths retain their initial energy, and it does not let the controller use hidden true parameters. The source's conditional selected-pulse mean is twice its probability parameter; the raw source including failures has yet another count. Neither replaces the deployed policy's count in this comparison. State-dependent readout, additional energy-injecting gates, or altered observation permissions require a new prefix budget.

## 68.6 Simultaneous interaction does not preserve a hard window

<a id="c-micro-02"></a>

**C-MICRO-02 (An infinite-tail counterexample for simultaneous red and blue interaction).** The segmented result does not imply finite excitation support after finite-time simultaneous red-plus-blue evolution. Let $X$ be the canonical self-adjoint closure of $a+a^\dagger$ on finite Fock vectors, and choose $H_{\rm sim}=\sigma_x\otimes X$ with domain $D(X)\oplus D(X)$ in the exchange eigenbasis. It agrees with the formal sum $A+B$ on the common finite core. The parameter $t$ below is dimensionless pulse area.

$$
\begin{gathered}
H_{\rm sim}=\sigma_x\otimes X,\qquad
e^{-itH_{\rm sim}}(|+_x\rangle\otimes|0\rangle)
=|+_x\rangle\otimes|-it\rangle,\\
\Pr(n=k)=e^{-t^2}\frac{t^{2k}}{k!}>0\quad(t\ne0,\ k\ge0).
\end{gathered}
$$

**Proof.** On the positive eigenstate of the probe exchange operator, the generator reduces to the oscillator position quadrature. The Weyl exponential of its self-adjoint closure is a displacement that sends vacuum to the displayed coherent state. Every number-state mass is strictly positive, leaving nonzero mass outside every finite cutoff. The initial probe-vacuum state nevertheless has total excitation support at most one. ∎

The counterexample refutes exact hard-support extrapolation. It does not rule out controlled tails, Trotter approximation, or study of the full Rabi model. General simultaneous interactions, weak leakage, and mode deletion need their own budgets. A refuted implication is not relabeled as a proved positive statement.

## 68.7 A certificate for the complete common-source chain

<a id="p-rob-03"></a>

**P-ROB-03 (A joint certificate for growth, physical filtering, and pulse omission).** Use the source, two-step acceptance event, and legal policy above. On the declared design interval, initial mean budget, and ideal operation contract, both the matched-blue and omitted-blue implementations have sufficient complete-CQ error bounds. The latter additionally requires an independent small-pulse guarantee.

$$
\begin{gathered}
H=s^2I,\quad p_{\rm source}=s^2\ge1369/2500,\quad
p_{\rm actual}=s_Ns^2,\\
\bar n=1,\quad N=4095,\quad |\beta|\le1/100,\quad
\varepsilon_{\rm required}=1/20,\\
\varepsilon_{\rm matched}\le\frac1{50}+\frac{1+\sqrt{16381}}{8192},\\
\varepsilon_{\rm omitted}\le\frac1{50}+\frac{1+\sqrt{16381}}{8192}
+\frac{\sqrt2}{100}
<0.049887775359266728<\frac1{20}.
\end{gathered}
$$

Here $p_{\rm actual}$ denotes an original-source attempt including the filter. The compiler has no original-source failure after filter passage and delivers with probability $s_N$.

**Proof.** The original seven-leaf instrument gives the scalar backward effect in the first line. Its complete conditional target is therefore itself CPTP, and preparation error contracts through it. For a common input, shared actual gates make the conditional quantum state identical on each target/compiler path. Complete-CQ distance is exactly path TV, bounded by one fiftieth on the design interval by P-ROB-02. Insert the actual filter and add its sharp error by the triangle inequality. The omitted implementation adds the preceding blue-omission bound. Failure records, system, and reference all belong to the same output space.

An independent rational checker encloses both radicals using integer square roots, proving the strict precision inequality without floating-point rounding. Its upper endpoint is 4988777535926672699 divided by ten to the twentieth power; the remaining allowed error is approximately 0.000112224640733273. The looser filtering bound used for Chapter 67's simpler example would instead give approximately 0.05001127625 and would not certify this precision. Failure of a weaker upper bound is not physical impossibility. ∎

A real device must additionally combine gate-matching, filtering, effective-model, and readout errors on this same complete output. None is measured here. Floating calculation tolerance, calibration coverage probability, and physical trace-distance error are distinct quantities. The general sharp postselection extension remains available, but this example requires no additional division by acceptance: source construction has already established linearity and trace preservation of its conditional target.

## 68.8 Flag counts do not identify blue pulse area

<a id="c-rob-02"></a>

**C-ROB-02 (Identical flag probabilities do not certify the blue-pulse terminal state).** All original flag-record probabilities in this model depend only on the probability component of the parameter. They cannot identify blue pulse area or certify complete terminal-state accuracy after omission.

**Proof.** Every labelled event is a parameter scalar times a unitary, so path masses are products of scalars. Use a vacuum input and compare zero blue area with an area of half pi. The original red and phase gates fix the vacuum. On deployed word zero-one, the latter model sends it to an orthogonal excitation state. That visible path alone contributes the lower bound

$$
D(C_{\pi/2}(|g,0\rangle\langle g,0|),C_0(|g,0\rangle\langle g,0|))
\ge Q_{01}=156/625>1/20.
$$

All flag distributions remain identical. This control deliberately violates the independent small-area premise to show why flag calibration cannot establish that premise. It does not refute the sufficient bound when the premise holds. ∎

Deployment therefore still chooses one set of legal weights from independent calibration and requires validity for every parameter in the resulting joint set. The inherited flag calibration can constrain the probability parameter, but cannot certify blue area, shared gate identity, or terminal testers. Independent pulse, spectral, or process calibration is needed, preserving common nuisance correlations. Without it, the device conclusion is insufficient evidence, not certified success or certified impossibility.

## 68.9 Complete costs and two physical schedules

One instrument may have different physical schedules. Reading an independent flag before applying its selected gate gives a selected-call count derived from all successful and failed leaves. Coherently controlling gates before flag readout may schedule exactly one blue control in every active slot. The scheduled equalities below refer specifically to that implementation, not to every coherent-control device. The compiler formulas concern the matched-blue implementation; the omitted implementation has zero blue calls. Labels alone do not decide which hardware contract applies.

$$
\begin{gathered}
\mathbb E[\#B]_{\rm source,feedforward}=s_Nsq(1+s),\quad
\mathbb E[\#B]_{\rm compiled,feedforward}=s_N,\\
\mathbb E[\#B]_{\rm source,scheduled}=s_N(1+s),\quad
\mathbb E[\#B]_{\rm compiled,scheduled}=2s_N,\\
\mathbb E[C_{\rm per\ delivery}]
=\frac{\mu_{\rm complete\ attempt}}{s_Ns^2}
+\frac{C_{\rm calibration}}{m}.
\end{gathered}
$$

The last formula is restricted to genuinely re-preparable, fresh-reset, independent identically distributed source attempts; calibration is amortized over delivered outputs. The attempt mean includes preparation, filtering, failed resets, auxiliaries, control, randomness, readout, records, and classical computation, charged on each item's actual occurrence event. A cost conditional on filter passage is multiplied by passage probability before entering the numerator. Unknown quantum inputs are not freely repeatable. Omitting a pulse does not itself establish measured time, energy, or monetary advantage.

## 68.10 Evidence, integration, and continuing responsibilities

The six additions are analytic proofs or counterexamples in their stated domains, supported by independent exact arithmetic and finite floating checks. There are no new Lean declarations. The unchanged 158 proof/configuration inputs and 13 runtime inputs are reused by source identity; their original receipts are not rewritten as chapter-68 executions. New source calculations, rectangular composition, reference and failure blocks, noncommuting CP maps, and invalid-boundary controls have new actual execution identities. Three native research tasks performed cross-review. This is internal AI review, not external human peer review.

The main numerical witness uses initial cutoff $N=1$, a two-dimensional reference, and final carrier $G\le5$. The nonzero-failure control uses input support $G\le2$, filter cutoff $N=1$, and common output $G\le6$, with a deliberately chosen tail mass $1/4096$. It checks the physical filtering interface, not numerical execution of the analytic $N=4095$ carrier.

No protocol-matched raw device data were acquired. The inherited synthetic calibration pipeline remains synthetic evidence and cannot certify the new blue-area premise. The next verifiable theoretical responsibility is a common-intervention tail bound for simultaneous evolution or finite-bath mode deletion, together with an assessment of whether actual control errors fit the remaining precision margin. Complete OPT, independent complex-quantum selection, mechanism identification, long-time limits, QFT and EFT, particle and flavour predictions, gravity, and cosmology retain separate responsibilities in the current roadmap. Completing this finite growth example does not complete physics across those domains.


