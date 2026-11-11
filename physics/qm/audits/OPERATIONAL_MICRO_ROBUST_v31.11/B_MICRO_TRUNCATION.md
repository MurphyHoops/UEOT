# Microscopic excitation-preserving instruments and complete-record truncation

Research draft B, 2026-11-11. Source inspected: `MurphyHoops/UEOT` main
`16a89154183c22030d4526413167d095d94e6890`. This draft is for integration by the
main agent; its provisional names do not create a second authoritative ledger.
Core is read-only. No hardware or newly executed Lean result is asserted here.

## 1. Inheritance and the new arrow

The current monograph already proves **P-QINF-02**: a spectral energy tail bounds
the trace distance between a normal state and its normalized spectral
projection. It also already provides the complete finite-instrument,
finite-accepted-tree, support, implementation, cost and sharp finite-matrix
postselection chain in Chapter 66. Those responsibilities are inherited.

The new arrow is narrower and genuinely additional:

**a specified self-adjoint microscopic model and fresh auxiliary preparation
→ every microscopic branch preserves the excitation cutoff
→ the restricted instrument is complete
→ the same entire bounded classical protocol intertwines
→ one initial tail bounds its entire record and terminal quantum state.**

The second added proof extends the sharp accepted-output inequality to normal
trace-class states. It does not relabel the existing finite Lean theorem as an
infinite-dimensional one. The physical preparation record requires a separate
bound, proved below; normalized projection is not a free deterministic map on
unknown input.

Dependency classes: **P** complex Hilbert quantum mechanics, Born readout,
tensor-product preparation, and the stated Hamiltonians; **E** the selected
rotating-wave/collision description when used to model a laboratory device,
fresh auxiliaries, a finite control tree, and any calibration region; **B** the
proved microscopic-to-finite operational bridge; **O** complete record/state
and cost predictions. No additional Core theorem is needed to select this
Hamiltonian, and no selection of complex quantum mechanics is claimed.

## 2. System, units, domains and actual actions

Let

\[
\mathcal H_S=\mathbb C^2_P\otimes\ell^2(\mathbb N_0),\qquad
G=a^\dagger a+P_e,\qquad P_e=|e\rangle\langle e|.
\]

Here `G` is a **dimensionless total excitation count**, not an arbitrary
physical energy. It has the one-dimensional zero sector
\(\mathcal H_0=\operatorname{span}\{|g,0\rangle\}\) and, for \(m\ge1\),

\[
\mathcal H_m=\operatorname{span}\{|e,m-1\rangle,|g,m\rangle\}.
\]

Consequently \(\Pi_N=1_{G\le N}\) has rank \(2N+1\). The positive-dimensional
cutoff system is \(\mathcal H_N=\Pi_N\mathcal H_S\), with its literal inclusion
\(V_N:\mathcal H_N\hookrightarrow\mathcal H_S\). This notation distinguishes
the integer cutoff from the number operator.

### 2.1 Self-adjoint Jaynes–Cummings and phase generators

For real \(\omega,\Delta,g,\varphi\), specify

\[
H=\hbar\{\omega G+\Delta P_e+
g(e^{i\varphi}\sigma_+a+e^{-i\varphi}\sigma_-a^\dagger)\}.
\]

In the displayed basis of \(\mathcal H_m\), its finite block is

\[
H_m=\hbar\begin{pmatrix}
\omega m+\Delta &g\sqrt m\,e^{i\varphi}\\
g\sqrt m\,e^{-i\varphi}&\omega m
\end{pmatrix},\qquad H_0=0.
\]

The definition of the unbounded operator is the direct sum with domain

\[
D(H)=\{\psi=\bigoplus_m\psi_m:
\sum_m\|H_m\psi_m\|^2<\infty\}.
\]

This operator is self-adjoint, not merely formally symmetric. Indeed, each
block is Hermitian and \(\|(H_m-z)^{-1}\|\le|\operatorname{Im}z|^{-1}\) for
nonreal \(z\). The direct sum of these resolvents is bounded and takes every
vector into the displayed domain: if \(\psi_m=(H_m-z)^{-1}\eta_m\), then
\(H_m\psi_m=\eta_m+z\psi_m\), a square-summable sequence. Thus \(H-z\)
is onto, with the indicated inverse, for \(z=\pm i\) after fixing compatible
units; the densely defined symmetric direct sum is self-adjoint. Finite-sector
vectors are a graph-norm core because truncating the two defining square sums
converges. Its unitary group is the strongly continuous direct sum
\(U(t)=\bigoplus_m e^{-itH_m/\hbar}\). Every \(\Pi_N\) commutes with it.

The independently controlled bounded phase
\(U_0(\phi)=e^{-i\phi P_e}\) and the exchange pulse
\(U_1(\alpha)=e^{-i\alpha(\sigma_+a+\sigma_-a^\dagger)}\) therefore preserve
each cutoff. The angles are dimensionless; an experimental specification must
supply the frequencies and pulse durations whose products they are. A finite
sequence of these pulses also preserves the cutoff. No continuously varying
unbounded-generator theorem is needed for a finite piecewise pulse sequence.

This is the standard rotating-wave Jaynes–Cummings family, with model choice
and domain made explicit; it is not a new fundamental Hamiltonian. The
historical source is Jaynes and Cummings, *Proceedings of the IEEE* 51 (1963),
89–109, DOI [10.1109/PROC.1963.1664](https://doi.org/10.1109/PROC.1963.1664),
with [the author's archived paper](https://bayes.wustl.edu/etj/articles/comparison.qm.scr.pdf).

### 2.2 Vacuum auxiliary collision and complete readout

Let \(A\) be a fresh qubit in \(|0\rangle_A\), with auxiliary excitation
\(E_A=|1\rangle\langle1|\). Either of the following is allowed:

\[
W_o(\chi)=e^{-i\chi(a\tau_++a^\dagger\tau_-)},\qquad
W_P(\chi)=e^{-i\chi(\sigma_-\tau_++\sigma_+\tau_-)}.
\]

Both commute with \(J=G+E_A\). The oscillator collision is again a
self-adjoint direct sum on finite total-excitation sectors; the probe collision
is bounded. The number-basis readout of the oscillator collision gives

\[
L_0|q,n\rangle=\cos(\chi\sqrt n)|q,n\rangle,\qquad
L_1|q,n\rangle=-i\sin(\chi\sqrt n)|q,n-1\rangle
\quad(n\ge1),
\]

with \(L_1|q,0\rangle=0\). This formula is derived by exponentiating the
actual two-dimensional exchange blocks. The probe collision instead gives

\[
L_0=P_g+\cos\chi P_e,\qquad L_1=-i\sin\chi|g\rangle\langle e|,
\]

tensored with the oscillator identity. At \(\chi=\pi/2\), it is a complete
probe readout with energy transferred to the auxiliary: one cannot describe
the reset as energy-free. A common JC/phase prefix \(U\) produces actual
instrument Kraus operators \(K_o=L_oU\).

Fresh preparation means that, at each use, the auxiliary is in the declared
product state and has no undeclared correlation with \(SR\) or another
auxiliary. Initial \(S:R\) correlation is unrestricted. If the auxiliary is
reused or initially correlated with \(S\), it must be included in the state
carrier and budget; the fixed instrument assumption does not follow from the
same formula alone.

### 2.3 General conservation-to-filtration lemma

Let an auxiliary have finite nonnegative excitation \(E_A\), let its ready
state \(|0\rangle\) lie in \(\ker E_A\), and let the actual joint unitary
\(W\) commute with the spectral projections of \(J=G+E_A\). The statement
means strong spectral commutation, not merely a formal unbounded commutator.
After \(W\), apply any complete auxiliary-only finite readout
\(M_{o\ell}:\mathcal H_A\to\mathcal H_{A'}\), where a common finite
output auxiliary can be obtained by explicit padding, and
\(\sum_{o,\ell}M_{o\ell}^\dagger M_{o\ell}=I_A\). The label \(o\) is
visible; \(\ell\) and the basis index \(b\) of the discarded output
auxiliary are hidden. Its actual system Kraus operators are

\[
K_{o\ell b}=(I_S\otimes\langle b|)
(I_S\otimes M_{o\ell})W(I_S\otimes|0\rangle).
\]

Write \(k=(\ell,b)\).
For every \(N\),

\[
K_{ok}\Pi_N=\Pi_NK_{ok}\Pi_N. \tag{B-filtration}
\]

**Proof.** An input in \(\Pi_N\mathcal H_S\otimes|0\rangle\) has total
excitation at most \(N\). Conservation keeps it in \(1_{J\le N}\). Since
\(E_A\ge0\), this subspace is contained in
\(\Pi_N\mathcal H_S\otimes\mathcal H_A\). Any auxiliary-only operation or
contraction leaves the system leg in that same subspace. This proves every
hidden branch statement, including a readout basis that is not an excitation
eigenbasis. Summing \(K_{o\ell b}^\dagger K_{o\ell b}\) first over \(b\)
uses \(\sum_b|b\rangle\langle b|=I_{A'}\), then summing over \(o,\ell\)
uses the readout completeness, and finally \(W^\dagger W=I\) and
\(\langle0|0\rangle=1\) give \(I_S\). This independently proves the
system instrument complete. ∎

This argument also covers mixed ready states supported in the zero-excitation
space by resolving their preparation index as hidden. It does not cover an
excited auxiliary merely because its **average** energy is small.

## 3. The frozen shared source, constructed microscopically

The integrated model uses a degenerate three-level flag, rather than confusing
it with the nondegenerate vacuum qubit above. Its basis is \(0,1,f\), its
excitation observable is **exactly zero**, and its fresh ready state is
\(|0\rangle\). Degeneracy is an explicit apparatus input; it does not imply
zero preparation time, work, readout, reset or record cost.

Let

\[
\theta=(q,\phi,\alpha),\quad q\in[12/25,13/25],\quad s=1-q/2.
\]

Put \(\gamma=\arcsin\sqrt q\), \(\beta=\arcsin\sqrt{1-s}\), and use
real plane rotations

\[
W(q)=R_{01}(\gamma)R_{0f}(\beta).
\]

It sends the ready vector to

\[
W(q)|0\rangle=
\sqrt{s(1-q)}|0\rangle+\sqrt{sq}|1\rangle+\sqrt{1-s}|f\rangle.
\]

Both rotations are finite unitaries; their complete columns, not merely the
first column, specify a legitimate apparatus. Next apply

\[
C=U_0\otimes|0\rangle\langle0|
+U_1\otimes|1\rangle\langle1|
+I\otimes|f\rangle\langle f|,
\qquad V=C(I\otimes W).
\]

This \(V\) is unitary and commutes spectrally with \(G\otimes I\).
Reading the flag gives the **derived** original instrument

\[
K_0=\sqrt{s(1-q)}U_0,\qquad
K_1=\sqrt{sq}U_1,\qquad K_f=\sqrt{1-s}I. \tag{B-source}
\]

All three branches preserve every cutoff. They satisfy
\(\sum_o K_o^\dagger K_o=I\). The parameter shared by source flagging,
conditional target, control gates and calibration is the same \(\theta\).
Independent variation of gates in these objects would define a different
uncertainty set and require a different error bound.

Stop immediately at \(f\), otherwise make a second source call. The raw
terminal records are
\(f,0f,1f,00,01,10,11\). Their Kraus maps are respectively
\(K_f,K_fK_0,K_fK_1,K_bK_a\). Direct multiplication proves completeness and
the accepted effect

\[
H_{\rm acc}=\sum_{a,b=0}^1(K_bK_a)^\dagger(K_bK_a)=s^2I.
\]

Thus the backward effect at prefix length \(t\) is
\(H_t=s^{2-t}I\), a conclusion from the source rather than a supplied
certificate. Conditioning on two successes produces the complete labelled
channel with step Kraus \(\sqrt{1-q}U_0,\sqrt qU_1\). On the seven-label
output carrier, the failed leaves have zero target mass. The map is linear
and CPTP on **all** normal inputs and finite references because its success
probability is the input-independent scalar \(s^2>0\).

This scalar-acceptance feature is a deliberate limitation. It does not resolve
general state-dependent deterministic normalization. The vacuum-collision
family above supplies genuinely state-dependent readout examples, and the
general truncation theorem below covers those original complete protocols too.

The raw success probability belongs to
\([1369/2500,361/625]=[0.5476,0.5776]\). With unit cost per source call,
the raw mean calls per trial are \(1+s\), and independent fresh trials would
cost \((1+s)/s^2\) calls per accepted pair. This is a count within a declared
cost model, not a measured time or an established advantage over the compiled
implementation.

## 4. Uniform complete-CQ truncation theorem

**Statement (provisional B-truncation).** Fix a finite action library, finite
visible result sets, finite hidden Kraus refinements, and a maximum tree height
\(L\). Every action is a complete normal instrument derived as above, or any
instrument for which the same microscopic argument has established
(B-filtration). Fix an observation function on classical histories. A legal
controller uses only that observation and fresh classical randomization; it
uses the same probabilities on every history in the same observation fibre.
No action touches the reference.

For every such controller \(\pi\), every finite-dimensional reference
\(R\) of positive dimension, every normal joint state \(\rho_{SR}\), and
every \(N\in\mathbb N_0\) satisfying

\[
\operatorname{Tr}(G\rho_S)\le\bar n<N+1,
\]

define

\[
s_N=\operatorname{Tr}[(\Pi_N\otimes I_R)\rho_{SR}]>0,\qquad
\rho_N=\frac{(V_N^\dagger\otimes I_R)\rho_{SR}
                  (V_N\otimes I_R)}{s_N}.
\]

Let \(\Omega^\pi\) be the complete classical leaf record and terminal
quantum-state output, including failure, stopping and timeout labels. A named
`leakage` outcome is included only when **its actual Kraus operators also
obey the filtration condition**; physical excitation leakage beyond the
cutoff requires a separate defect budget and is excluded from this theorem.
Let \(\Omega_N^\pi\) use the literal
restricted branches \(K^N_{aok}=V_N^\dagger K_{aok}V_N\), the same
controller, and the same record labels. Embed only the terminal quantum leg,
leaving the record and reference unchanged. Then

\[
D\bigl(\Omega^\pi(\rho_{SR}),
        \iota_N\Omega_N^\pi(\rho_N)\bigr)
\le\sqrt{\frac{\bar n}{N+1}},\qquad
D(X,Y)=\tfrac12\|X-Y\|_1. \tag{B-CQ}
\]

**Proof, without an assumed intertwining certificate.**

1. The spectral inequality
   \(G\ge(N+1)(I-\Pi_N)\) gives
   \(1-s_N\le\bar n/(N+1)<1\). P-QINF-02 applied on \(SR\) gives
   \(D(\rho_{SR},(V_N\otimes I_R)\rho_N(V_N^\dagger\otimes I_R))
   \le\sqrt{1-s_N}\). Its purification proof is valid for a normal
   trace-class state; finite rank of \(\Pi_N\) is separately established.

2. (B-filtration), derived from the actual microscopic conservation and
   preparation, implies the **vector** identity
   \(K_{aok}V_N=V_NK^N_{aok}\). Therefore
   \(\sum_{o,k}(K^N_{aok})^\dagger K^N_{aok}
    =V_N^\dagger(\sum_{o,k}K_{aok}^\dagger K_{aok})V_N=I_N\).
   The finite instrument is complete, not a trace-losing compression.

3. Products along a branch inherit that identity by induction. Legal
   classical randomization multiplies the same products on both sides by
   the same square roots of probabilities. Summing hidden refinements
   preserves each visible branch equality. Coarsening or stopping must use
   exactly the same labels on both sides. Consequently
   \(\Omega^\pi(\iota_NX)=\iota_N\Omega_N^\pi(X)\) for every finite
   cutoff input, including every reference correlation.

4. Complete finite branching and termination at height at most \(L\) make
   \(\Omega^\pi\) a normal CPTP channel into a finite direct sum of
   trace-class spaces. One can prove trace preservation by induction on the
   tree, or by summing the terminal Kraus products to the identity. Trace-norm
   contraction for Hermitian differences follows from the dual unital
   positive map and the characterization
   \(\|X\|_1=\sup_{-I\le E\le I}|\operatorname{Tr}(EX)|\).
   Applying it to step 1 and using step 3 proves (B-CQ). ∎

There is no \(L\)-fold tail penalty in this theorem: the exact cutoff is an
invariant space throughout the specified physical protocol. This is not an
assertion about controls that inject excitation, weak nonconserving terms,
or postselection that changes a normalized energy bound. The output error is
uniform over the declared legal finite controllers, but \(\rho\mapsto\rho_N\)
is nonlinear. Hence the displayed expression is **not** a norm of a difference
of two channels, and must not be renamed an energy-constrained diamond norm.
Energy-constrained channel norms have distinct definitions and reference
quantifiers; see [Shirokov, arXiv:1706.00361v2](https://arxiv.org/abs/1706.00361v2)
and [Winter, arXiv:1712.10267v1](https://arxiv.org/abs/1712.10267v1).

For the scalar-acceptance shared source, the conditional two-success process
is itself CPTP. Apply (B-CQ) directly to that process: **no division by the raw
acceptance probability is required for this particular cutoff comparison**.
For a general accepted subinstrument use the next theorem instead.

## 5. Sharp normal trace-class postselection, with the complete-output premise

Let \(\omega,\sigma\) be normal states on the same (possibly separable
infinite-dimensional) output Hilbert space. Let \(\mathcal E\) be the **same**
normal completely positive trace-nonincreasing accepted-output extractor for
both, retaining any accepted records and terminal state. Put
\(A=\mathcal E(\omega)\), \(B=\mathcal E(\sigma)\), \(p=\operatorname{Tr}A\),
\(q=\operatorname{Tr}B\), and suppose \(p,q>0\). If
\(D(\omega,\sigma)\le\varepsilon\), then

\[
|p-q|\le\varepsilon,\qquad
D(A/p,B/q)\le\min\{1,\varepsilon/\max(p,q)\}. \tag{B-post}
\]

**Proof.** Complete the extractor with one discarded-state failure flag:
\(\widehat{\mathcal E}(X)=\mathcal E(X)\oplus
\operatorname{Tr}[(I-\mathcal E^*(I))X]\,|f\rangle\langle f|\).
Normality, complete positivity and trace preservation hold because the
missing effect is positive. Trace-distance contraction gives

\[
\|A-B\|_1+|p-q|\le2\varepsilon. \tag{B-joint}
\]

The trace functional gives \(\|A-B\|_1\ge|p-q|\), proving the probability
bound. If \(p\ge q\), use
\(A/p-B/q=(A-B)/p+(1/p-1/q)B\) and positivity of \(B\) to obtain

\[
\|A/p-B/q\|_1\le
\{\|A-B\|_1+p-q\}/p\le2\varepsilon/p.
\]

Interchange \(A,B\) for \(q\ge p\); normalized-state distance is at most
one. No finite matrix spectral decomposition or limit exchange appears. ∎

This proof is an analytic extension of P-FCOND-10's **scope**, not a new claim
of a sharper constant. Sharp finite classical examples embed in the normal
trace-class setting, so the constant does not improve without extra input.
The existing finite Lean bindings remain finite; this extension is paper
proved only. If a target success probability is known to satisfy
\(q\ge q_{\min}>\varepsilon\), then \(p>0\) and
\(D(A/p,B/q)\le\varepsilon/q_{\min}\). If the resulting bound reaches one,
it provides no conditional precision guarantee. Success-only observations do
not supply the complete-output premise.

## 6. Actual preparation, failure records and costs

The projection \(\rho_N\) can be a mathematical approximation or the output
of a physical filter; those are different experimental contracts.

### 6.1 A single physical filter

The ideal two-outcome filter has Kraus \(\Pi_N,I-\Pi_N\). Its pass output is
\(s_N\rho_N\); its fail output remains part of the complete record. For a
known repeatable preparation, \(s_N\ge1-\bar n/(N+1)\) gives a cost bound.
For a single unknown joint input, failure does not provide a fresh copy of the
input or preserve its unknown reference correlations for another attempt.

Let \(\delta=1-s_N\). Compare an ideal protocol with a fixed `pass` label to
the actual complete filter followed by that same protocol on its pass branch,
with the fail branch retained. Then

\[
D_{\rm complete}\le b(\delta):=
\tfrac12\{\sqrt{\delta(4-3\delta)}+\delta\}
\le\min\{1,\sqrt\delta+\delta\}. \tag{B-prep}
\]

**Proof.** At \(\delta=0\) both complete outputs coincide, so the bound is
zero. For \(0<\delta<1\), purify the input and write its unit vector as
\(\sqrt{1-\delta}|p\rangle+\sqrt\delta|f\rangle\), with orthogonal
projected components. In the `pass` block, ideal minus filtered input has
matrix
\(\left(\begin{smallmatrix}0&\sqrt{\delta(1-\delta)}\\
\sqrt{\delta(1-\delta)}&\delta\end{smallmatrix}\right)\).
Its trace norm is \(\sqrt{\delta^2+4\delta(1-\delta)}\). The additional
orthogonal fail block has trace norm \(\delta\). Divide their sum by two.
Taking the partial trace and applying the subsequent common complete channel
cannot increase the distance. The coarser bound also follows by inserting the
normalized pass input: projection distance at most \(\sqrt\delta\), and
changing the pass/fail mixture costs exactly \(\delta\). ∎

This explains why retaining filter failure can give a distance **larger than
\(\sqrt\delta\)**. The exact finite pure-state control with \(\delta=1/4\)
has normalized-projection distance \(1/2\), but complete physical distance
\((\sqrt{13}+1)/8\approx0.575694\).

For root's general budget \(\bar n=1,N=4095\), \(\delta\le1/4096\).
Combining the safe bound with the memoryless compilation radius \(51/2500\)
gives \(65/4096+51/2500=0.036269140625<1/20\). With the subsequently
improved legal adaptive radius \(1/50\), it is
\(65/4096+1/50=0.035869140625<1/20\). These are model guarantees; all
unmodelled hardware, calibration, numerical and preparation discrepancies
would consume the remaining budget. A support-known \(G\le1\) prepared
state instead has \(\delta=0\), including any finite reference.

An ideal spectral filter is an additional allowed preparation operation. The
conservation theorem does not prove that a particular laboratory can measure
\(\Pi_N\) perfectly. Exact known-support preparation is the directly
constructive finite instance; a general high-cutoff physical guarantee is
conditional on implementing or separately certifying the specified filter.

### 6.2 Fresh-reset resource accounting

If a complete fresh trial has success probability \(p>0\) and nonnegative
mean total cost \(\mu\), independent repetition until success has expected
cost \(\mu/p\), as inherited from P-FCOND-09. All preparation, source-flag
rotations, gate control, auxiliary readout, failures, reset, randomization,
record storage, classical calculation and allocated calibration cost belong
in \(\mu\). Within-trial cost and success need not be independent.

If each failed spectral-filter trial resets at cost \(c_r\), and a fresh
input and filter together cost \(c_0\), the cost of obtaining one successful
filter output is \([c_0+(1-s_N)c_r]/s_N\). Additional accepted source trials
must be charged consistently. If a complete trial begins with that filter
and only a passed input is run through the raw two-call source, its success
probability is \(s_Ns^2\), and the mean trial cost is the actual average over
all fail and pass leaves—not merely two successful gates. Unknown input
cannot be assumed to satisfy the fresh-reset premise.

### 6.3 Excitation versus energy and rare events

For resonant uncoupled laboratory reference energy
\(E_{\rm ref}=\hbar\omega G\), \(\bar n=E/(\hbar\omega)\) follows from
an independently justified energy bound. If probe and oscillator frequencies
differ and are positive, their free energy obeys
\(E_{\rm ref}\ge\hbar\min(\omega_P,\omega_o)G\). Interaction energy is not
silently identified with this reference.

For the Hamiltonian in §2.1 with \(\omega>0\), its exchange term \(T\)
satisfies \(T^2=G\). Hence, as quadratic forms,

\[
H/\hbar\ge\omega G-|\Delta|I-|g|\sqrt G
\ge(\omega/2)G-(|\Delta|+g^2/(2\omega))I.
\]

Thus a bound on the nonnegative shifted Hamiltonian
\(\widetilde H=H+\hbar(|\Delta|+g^2/(2\omega))I\) implies
\(\operatorname{Tr}(G\rho)\le2\operatorname{Tr}(\widetilde H\rho)/(\hbar\omega)\).
The shift and parameters must be fixed; a varying unknown energy zero is not
calibration. For uncertain parameters use a common certified lower frequency
and upper coupling/detuning bounds. These operators have discrete
finite-multiplicity sectors growing at large excitation, but the cutoff here
is explicitly \(G\), not a newly inferred continuum spectral projector.

After a positive event of probability \(p\), a normalized excitation budget
can grow to \(\bar n/p\), even when the unnormalized mass-weighted energy is
nonincreasing. In particular \(\operatorname{Tr}G\rho_N\le\bar n/s_N\),
also bounded by \(N\). One cannot reuse the original \(\bar n\) on every
rare branch. Extending to controls with leakage requires explicit per-prefix
unnormalized energy and operation-defect budgets; it is not covered here.

## 7. Necessary-premise counterexamples and finite checks

### 7.1 Average energy preservation does not preserve cutoff branches

Take \(G=\operatorname{diag}(0,1,2)\) and Kraus

\[
|0\rangle\langle0|,\quad
|0\rangle\langle1|/\sqrt2,\quad
|2\rangle\langle1|/\sqrt2,\quad
|2\rangle\langle2|.
\]

They form a complete channel and satisfy \(\sum K^\dagger GK=G\) for
**every** input. Nevertheless the third Kraus takes the \(G\le1\) input
\(|1\rangle\) outside that cutoff. Compressing the output discards mass
\(1/2\). Therefore average-energy nonincrease—even equality as an operator
identity—is insufficient for (B-filtration). A low initial tail cannot
repair this omitted dynamical premise.

### 7.2 Noncommuting maps, rather than only noncommuting Kraus matrices

In \(G\le1\), a JC swap sends \(|e,0\rangle\) to \(-i|g,1\rangle\).
Full oscillator loss after the swap sends it to \(|g,0\rangle\); reversing
the two channels sends it to \(|g,1\rangle\). Their outputs have distance
exactly one. This tests actual CP maps, avoiding the false criterion that
anticommuting Kraus matrices must imply noncommuting conjugation maps.

The shared rational phase/JC example also has noncommuting actual maps:
\(e^{-i\phi}=(3+4i)/5\), \(\cos\alpha=3/5\), \(\sin\alpha=4/5\).
For input \(|e,0\rangle\), reversing their order gives squared pure-state
distance \(576/3125\), hence distance \(24\sqrt5/125>0\). The matrices
and this equality are independently checked by exact symbolic arithmetic.

### 7.3 Scope of the executable evidence

`check_micro_truncation.py` constructs the flag's full joint unitary, extracts
the source Kraus matrices from its input/output blocks, and checks the raw
seven-leaf effects and scalar acceptance at exact rational parameters. It
also constructs the nondegenerate vacuum-exchange block and the
average-energy counterexample. Its second section numerically constructs
finite JC sectors, vacuum collision readout, a stopping adaptive tree and a
reference-correlated input; it checks the **complete CQ** distance and the
filter-failure correction. These numerical diagnostics are explicitly
floating computations, not interval bounds or empirical data. The universal
claims are supported by the proofs above, not by finite sampling.

The first execution reached receipt serialization and failed because a NumPy
boolean had not been converted to a JSON boolean. The conversion was fixed
and the source was rerun; the retained successful receipt is bound to the
corrected file hash. No failed scientific candidate was removed.

## 8. Same-source B2 continuation: marginal mixing and retained-memory obstruction

The root's follow-up calculation can be completed inside the same model.
Fix the one-excitation sector **exactly**, in ordered basis
\((|g,1\rangle,|e,0\rangle)\). Use
\(U_0=\operatorname{diag}(1,(3+4i)/5)\) and
\(U_1=(3I-4iX)/5\). Forgetting the successful branch label gives the
Doob channel

\[
\mathcal T_q(\rho)=(1-q)U_0\rho U_0^\dagger+qU_1\rho U_1^\dagger.
\]

This is the source's actual conditional one-step map; its success probability
is \(s\). In the Bloch representation its matrix is
\(M(q)=(1-q)R_0+qR_1\), with rotations derived from
\((R_a)_{ij}=\operatorname{Tr}(\sigma_i U_a\sigma_jU_a^\dagger)/2\):

\[
R_0=\begin{pmatrix}3/5&-4/5&0\\4/5&3/5&0\\0&0&1\end{pmatrix},\qquad
R_1=\begin{pmatrix}1&0&0\\0&-7/25&-24/25\\0&24/25&-7/25\end{pmatrix}.
\]

Let \(M_0=M(1/2)\) and \(A=M_0^2\). Direct rational multiplication gives

\[
A=\begin{pmatrix}
12/25&-48/125&24/125\\
48/125&-228/625&-156/625\\
24/125&156/625&-63/625
\end{pmatrix}.
\]

The successive leading principal minors of
\((9/10)^2I-A^TA\) are exactly

\[
\frac{4941}{12500},\qquad
\frac{422733249}{3906250000},\qquad
\frac{29552508909}{390625000000}.
\]

They are strictly positive. Sylvester's criterion gives
\(\|M_0^2\|_2<9/10\). Every \(M(q)\) is a convex combination of
orthogonal matrices, so \(\|M(q)\|_2\le1\), and

\[
\|M(q)-M_0\|_2\le2|q-1/2|,\qquad
\|M(q)^2-M_0^2\|_2\le4|q-1/2|.
\]

For the entire frozen region \(|q-1/2|\le1/50\), therefore
\(\|M(q)^2\|_2\le49/50\). The channel is unital, with stationary
state \(I_2/2\); the strict two-step contraction proves it is the unique
stationary state **in this exact sector**, and for every reduced system
state there,

\[
D(\mathcal T_q^n(\rho),I_2/2)
\le(49/50)^{\lfloor n/2\rfloor}D(\rho,I_2/2). \tag{B-mix}
\]

This uses the qubit identity
\(D(\rho(r),\rho(r'))=\|r-r'\|_2/2\). It is a complete paper proof
with an independent exact symbolic matrix check. It is not a newly executed
Lean result. The same coefficient has not been proved here for arbitrary
reference-correlated joint states.

Two essential failures of a stronger statement are explicit:

1. **The whole oscillator is not mixing to one state.** Every excitation
   sector is invariant under \(U_0,U_1\). Vacuum and \(I_2/2\) on the
   one-excitation sector are distinct stationary states; sector weights
   persist. This is a physical invariant-sector obstruction, not a numerical
   degeneracy that may be deleted.
2. **The complete record and quantum memory do not forget initial states.**
   Retain the word \(r\) of successful labels. For any two input states,
   including a common untouched reference,
   \(\Omega_n(\rho)=\bigoplus_r p_q(r)V_r\rho V_r^\dagger\), so

   \[
   D(\Omega_n(\rho),\Omega_n(\sigma))
   =\sum_r p_q(r)D(V_r\rho V_r^\dagger,V_r\sigma V_r^\dagger)
   =D(\rho,\sigma). \tag{B-memory}
   \]

   Hence (B-mix) applies to the **discarded-record system marginal**. It does
   not make the complete CQ process contractive to a common state. Orthogonal
   inputs retain distance one with their full word record; applying the
   corresponding inverse word recovers either input.

The raw success mass is \(s^n\to0\), since \(s\le19/25<1\). Conditioning
each finite prefix gives a consistent Bernoulli word family and the above
Doob marginal. The infinite-success event has zero raw probability; this
construction must not be described as ordinary conditional probability on a
positive-probability infinite event. QSD, stationary Doob state, marginal
mixing, complete-record memory and infinite path measures remain different
objects.

## 9. B2–B5: preserved long-term responsibilities

| Responsibility | Current source and established boundary | Next exact acceptance target |
|---|---|---|
| Long time and conditional persistence | Chapters 52–59 distinguish invariant states, Cesàro averages, QSD and Doob states. The added §8 now proves one-sector marginal mixing and exact persistence of complete-record distinguishability. | Add a specified genuinely dissipative vacuum-collision component, derive a checkable contraction/mixing criterion on a stated support and reference domain, and estimate its finite-prefix and long-time errors. Do not infer one-state mixing across invariant sectors or interchange rare-event and time limits. |
| Memory and finite Gaussian bath | Chapters 13,17,18 already state Gaussian CP, weak-coupling inputs and an operational memory counterexample. | Couple the same probe to a specified finite-mode bath and compare **all allowed intervention slots and recorded outputs** after deleting one mode or resetting memory. Prove one common-input full-CQ error bound from a trace-distance dilation or Duhamel bound on a controlled invariant sector. Correlation-function matching alone fails the target. |
| EFT and QFT | Chapters 21–29 give typed standard free-field, perturbative, Ward and matching inputs; Chapter 45 is a finite regulated lattice model. | Freeze one regulated action, matching scheme, observable and order, then propagate a same-source mode-elimination bound to that observable. For a scattering application calculate the complete stated order including thresholds and required real/virtual cancellation; do not call beta running physical time or claim removal of a four-dimensional regulator. |
| Particle/three-generation and flavor | Chapters 31,36 retain both high-energy candidates \((3,3,1),(5,5,2)\); Chapter 37 proves rank-one FCNC identities and a matching-scale aggregate bound, with masses/mixing/threshold inputs open. | Freeze the full spectrum, scalar/Yukawa sector and thresholds for both candidates. For the chosen rank-one neutral vector, derive one coefficient ratio/phase relation not used for fitting, then run its complete operator basis to a specified low scale with matrix elements and covariance. If unrestricted Yukawas absorb the relation, report no prediction. |
| Information gravity and cosmology | Original `UEOT_v3_top.pdf` §4.2.3, printed lines 1632–1803, calls Fisher-derived Lorentzian geometry and Einstein dynamics a grand conjecture; current Chapter 47.13 explicitly leaves geometric dynamics and semiclassical consistency open. | First record the narrow positivity obstruction below, then fix a globally hyperbolic background, free field, Hadamard state and compactly switched local probe; derive one regulated/renormalized response with controlled error. Any added geometric feedback must satisfy stress-energy conservation/Bianchi consistency. Dark matter, dark energy, cosmic initial state and black-hole information require separate specified models. |

### Narrow Fisher obstruction, not a ban on information gravity

For a regular positive probability model with real parameters, its Fisher
matrix is
\(I_{ij}=\mathbb E_\theta[(\partial_i\log p)
(\partial_j\log p)]\). For every real vector \(v\),
\(v^TIv=\mathbb E[(\sum_i v_i\partial_i\log p)^2]\ge0\).
A real parameter reparameterization or pullback gives \(J^TIJ\succeq0\).
Positive averaging also preserves that inequality. Therefore **directly
identifying** such a matrix, its real pullback, or its positive average with
a nondegenerate Lorentzian metric cannot produce a negative eigenvalue.
The original §4.2.3 passage needs additional signed/causal/analytic structure;
none is supplied by changing coordinates. This conclusion does not exclude
indirect emergent metric constructions, constrained statistical dynamics,
analytic continuation with a separately justified reality condition, or any
other bridge whose additional structure is stated and tested.

## 10. Exact remaining limits

Paper proved: the stated self-adjoint model, microscopic branch filtration,
complete restricted instrument, bounded classical-protocol CQ truncation,
normal trace-class sharp postselection, and complete filter-record bound.
Finite symbolic and floating evidence are separately recorded. The new
infinite-dimensional results are not Lean-checked. No raw laboratory counts,
cost measurements or independent hardware calibration have been acquired.

Still open: nonconserving drives and leakage budgets; unrestricted coherent
controllers; infinite-dimensional references in the formal contract; unbounded
stopping and its integrability; exchanges of \(N\to\infty\), \(T\to\infty\)
and rare-event limits; weak-coupling/rotating-wave error for a specific device;
physical implementation or certification of high-cutoff spectral filtering;
full bath/QFT/EFT, particle and gravity responsibilities. No finite example
or count of passing checks is a fraction of completed fundamental physics.
