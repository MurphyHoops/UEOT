# A: finite operation semantics, stable external tests, and memory witnesses

Date: 2026-11-14 (Asia/Shanghai). Author: native research agent A. This is an
internal AI research deliverable, not external human peer review.

## 1. Source, scope, and result identities

The shared source is the exact `SHARED_MODEL.json` supplied by the master agent:
two persistent vacuum modes, frequencies `(1,3/2)`, relative real couplings
`(1,3/5)`, `lambda in [1/5,2/5]`, `L=Z`, `H_S=0`, three slot lengths
`(2/3,3/4,1/2)`, and complete non-scalar `f/p` tests. The code records its SHA256.
The external output consists of all stopped records and terminal S/R blocks.
The optional causal-break witness below has separately declared controls. It is
not a change to the source's frozen three-slot test.

The following existing results are reused: P-OPT-02 (operational/map
equivalences), P-OPT-03 (composition congruence), the finite full-effect
separation/local-tomography results, and the classical/real selection witnesses.
`finite_operations.py` makes the finite composition interface executable;
these old paper conclusions are not counted again as new results.

New project results proposed for integration are:

* **C-QSEL-02:** Reachable-sector hidden completion and the boundary of global
  quantum selection. Precise statement and proof: `A_SELECTION_DECISION.md`.
* **P-TOM-01:** An explicit legal finite-tester stability bound, with SPAM,
  leakage, and physical-repair obligations.
* **P-QMEM-02:** A causal-break response-rank lower bound for persistent memory.

No Core file is edited. Complex vector spaces, Born probabilities, the tensor
product, CP tests, and the bosonic Hamiltonian are physical/model inputs here.
There is no new Lean claim. SymPy exact checks and floating calculations are
separately identified in `A_VERIFICATION.json`.

## 2. Complete finite tests and operational composition

A test `T:A -> B` is a finite family `K[y,alpha]: C^dA -> C^dB` satisfying

\[
\sum_{y,\alpha}K_{y\alpha}^{\dagger}K_{y\alpha}=I_A.
\]

Its y-branch is `Phi_y(X)=sum_alpha K[y,alpha] X K[y,alpha]^dagger`.
Zero branches are permitted. Failure and stopped outcomes are labels, not
discarded samples. With an untouched reference R, the full output is
`direct_sum_y (Phi_y tensor id_R)(rho_AR)`.

The implemented operations have the following actual Kraus formulas.

| Operation | Kraus formula | Completeness reason |
|---|---|---|
| Conditional sequence after y | `L[y,z,beta] K[y,alpha]` | Every continuation is complete; summing z,beta gives `K^dagger K` |
| Parallel tests | `K[y,alpha] tensor L[z,beta]` | Tensor of the two completeness identities |
| Coarse graining `c(y)` | Concatenate all Kraus lists with a common new label | Finite sum is unchanged |
| Discard B, retain y | `bra(j) K[y,alpha]` for every output basis j | `sum_j ket(j)bra(j)=I_B` |
| Binary effect E after y | `sqrt(E)K` and `sqrt(I-E)K` | The two positive effects sum to identity |
| Stop branch | Identity continuation, with an explicit terminal label | No environment reset or renormalization |

Equality is equality of each visible branch's **CP map**, equivalently its
Choi matrix; it is not equality of the chosen Kraus lists. Every listed
construction preserves that equality. This is the executable interface to
P-OPT-03, not a replacement of its quantifiers by a finite random test.

The input/output carrier in a compositional claim must contain every retained
memory. Equality of reduced maps on S does not permit substitution inside an
experiment that reuses an unobserved E. The executed negative control uses one
classical environment bit to choose I or Z once. Each isolated slot is the
same dephasing channel as a reset model. Two persistent applications cancel;
two reset applications dephase. For input `|+>`, their final trace distance is
exactly `1/2`.

### Future-response quotient

At a fixed time and interface, let `F_t` be the set of all allowed future
subnormalized response functionals, including terminal mass. Define

\[
x\sim_t x'\quad\Longleftrightarrow\quad
f(x)=f(x')\quad\text{for every }f\in\mathcal F_t.
\]

If the legal tester family is closed under prefixing an allowed branch A,
then `x~_t x'` implies `Ax~_(t+1) Ax'`: apply the definition to `f composed A`.
If an adaptive action is to descend to this quotient, it must be constant on
the relevant observable-history fiber. The quotient preserves all declared
future probabilities, including zero events and failure mass. It does not,
by itself, supply a positive/CP compression channel, a smaller Hilbert memory,
or a stochastic transition on arbitrary equivalence classes. Those are
separate realization obligations. Normalizing a branch before checking its
mass would lose this guarantee.

## 3. P-TOM-01: explicit finite tests certify a fixed external channel

Let `d>=2`. For `0<=j<k<d`, define the legal pure preparations and binary
effects

\[
P_j=|j\rangle\langle j|,\quad
P^x_{jk}=\frac{(|j\rangle+|k\rangle)(\langle j|+\langle k|)}2,\quad
P^y_{jk}=\frac{(|j\rangle+i|k\rangle)(\langle j|-i\langle k|)}2.
\]

There are `d^2` preparations. An output setting tests `{P_q,I-P_q}`; the
`d^2` projectors are **different binary settings**, not one purported POVM.
Write

\[
X_{jk}=|j\rangle\langle k|+|k\rangle\langle j|,\quad
Y_{jk}=-i|j\rangle\langle k|+i|k\rangle\langle j|.
\]

Their Hermitian dual basis is

\[
F^x_{jk}=X_{jk},\quad F^y_{jk}=Y_{jk},\qquad
F_j=P_j-\frac12\sum_{\{j,k\}}(X_{\min(j,k),\max(j,k)}+
Y_{\min(j,k),\max(j,k)}).
\]

The sum contains each pair incident to j once. Direct substitution proves
`tr(P_q F_r)=delta_qr`. Thus, for every complex matrix X,

\[
X=\sum_r\operatorname{tr}(F_rX)P_r
 =\sum_q\operatorname{tr}(P_qX)F_q.
\]

For two complete labelled instruments Phi and Psi on the same `dA -> dB`
carriers and the same label set Y, put

\[
\delta p_{yqr}=\operatorname{tr}
 [P_q(\Phi_y-\Psi_y)(P_r)].
\]

Then the **complete CQ map**, with all labels, obeys

\[
\boxed{
\frac12\|\Phi_{\rm CQ}-\Psi_{\rm CQ}\|_\diamond
\le\frac12\sum_r\|F_r^{(A)}\|_\infty
  \sum_{y,q}\|F_q^{(B)}\|_1|\delta p_{yqr}|.}
\tag{A-T1}
\]

The left side may also be capped at one. No restriction to a Bell input is
made: it bounds every finite untouched reference and every joint input.

### Proof with the reference retained

Complex-linearly expanding both input and output gives

\[
\Delta_y(X)=\sum_{r,q}\delta p_{yqr}
 F_q^{(B)}\operatorname{tr}(F_r^{(A)}X).
\]

For arbitrary auxiliary R and trace-class X on A/R,

\[
(\Delta_y\otimes\mathrm{id})(X)
=\sum_{r,q}\delta p_{yqr}F_q^{(B)}\otimes
 \operatorname{tr}_A[(F_r^{(A)}\otimes I_R)X].
\]

Trace-norm duality gives, for any Hermitian F (positivity is unnecessary),

\[
\|\operatorname{tr}_A[(F\otimes I)X]\|_1
\le\|F\|_\infty\|X\|_1:
\]

pair the partial trace with an arbitrary operator of operator norm at most
one, move it back inside the full trace, and use
`||F tensor V||_infinity <= ||F||_infinity`. Apply the triangle inequality,
multiplicativity of trace norm on tensor products, and add the orthogonal
label blocks. Taking the supremum over R and `||X||_1=1` proves (A-T1).
This proves the full norm inequality; the numerical reconstruction check is
only an independent check of the indexing and formulas.

### Explicit constants for dimensions 2–4

The two nonzero eigenvalues of each `F_j` are
`(1 +/- sqrt(2d-1))/2`. Each pair dual has eigenvalues `+1,-1`.
Therefore

\[
A_d=\sum_r\|F_r\|_\infty
 =\frac d2(1+\sqrt{2d-1})+d(d-1),\qquad
B_d=\sum_q\|F_q\|_1=d\sqrt{2d-1}+2d(d-1).
\]

If `delta=max_(q,r) sum_y |delta p_yqr|`, the simpler bound is
`half diamond <= (A_dA B_dB/2) delta`.

| dA=dB | Settings d^4 | Half-diamond coefficient `A_d B_d/2` |
|---|---:|---:|
| 2 | 16 | `9+5 sqrt(3) = 17.660254037844386...` |
| 3 | 81 | `(225+81 sqrt(5))/4 = 101.53037654437074...` |
| 4 | 256 | `196+52 sqrt(7) = 333.5790681753587...` |

These are explicit sufficient constants, not claimed optimal constants.
The exact script checks duality, rank-one legality, and the characteristic
polynomial of every diagonal dual. Poor conditioning can make a complete
frame statistically useless; completeness alone is not an error bound.
For example, with four labels, d=2, failure probability alpha=0.01 and the
entire error budget 0.05 assigned to a per-entry Hoeffding/union bound,
researcher C independently obtains 9,438,576 shots per setting, or
151,017,216 shots across sixteen settings. This is one sufficient conservative
budget, not a sample-complexity lower bound. It is not the experiment executed
by the two-parameter calibration program.

### Why the external dimension matters in this source

After fixing all three durations, instruments, feedback, and stop rules,
the persistent-bath experiment is one complete channel

\[
\mathcal P:\mathcal T(\mathbb C^2)
\longrightarrow\bigoplus_{y\in\{f,pf,ppf,ppp\}}
\mathcal T(\mathbb C^2).
\]

The known independent bath preparation is part of the channel. Its unobserved
internal dimension is not the dimension to be tomographed. Four trusted input
preparations and four trusted binary terminal effects, recording every label,
give the d=2 bound on this fixed channel, including arbitrary untouched R.
This removes a separate requirement to prepare a reference-entangled test
state for the *upper bound*, provided the finite external dimension and SPAM
assumptions are independently warranted.

It does not certify a different middle operation or all process-tensor
testers. For those targets, one must span the permitted multi-time operation
spaces or validate a separately declared structural model. Neither the
current two-parameter calibration nor one Bell-output calculation is the
16-setting experiment just described.

### Statistical error, SPAM, projection, leakage, and conditioning

Suppose the actual prepared state differs from nominal `P_r` by trace
distance at most `tau_r`, and the actual binary effect differs from nominal
`P_q` in operator norm by at most `xi_q`. With a complete instrument,

\[
\sum_y|\widetilde p_{yqr}-p_{yqr}|
\le 2\tau_r+\xi_q.
\tag{A-T2}
\]

For preparation error, the positive outcome operators `Phi_y^*(P_q)` plus
their complements form a complete POVM; its full l1 distance is at most
`2 tau_r`, and deleting complementary outcomes cannot increase it. For
effect error, sum the bound `xi_q tr Phi_y(tilde P_r)` over y; completeness
makes this sum at most `xi_q`. Independent errors on both devices add.

A simultaneous statistical confidence region must bound every used
probability discrepancy. A fitted CP/TP projection contributes its **actual
probability residual** against the data. No assertion that Euclidean or
likelihood projection is diamond-norm contracting is used. Unknown SPAM can
admit a common similarity/gauge transform preserving every experiment; an
absolute channel norm then requires an independently fixed physical frame.
The executed unitary gauge example exchanges Z and X and preserves all
transformed test probabilities, although their distance in one fixed frame
is one in half-diamond norm.

The dimension assumption is essential. If leakage is possible, either model
and observe the leakage carrier/flag in the channel, or supply an independent
bound in the same output metric. An isometry sending
`|0> -> sqrt(1-l)|0>+sqrt(l)|leak>` has leakage probability l but trace
distance `sqrt(l)` from `|0>`, so adding only l is invalid for coherent
leakage. An actual measured leakage flag changes the channel and must be
declared. Unrecorded leakage cannot be repaired by renormalizing successes.

The rare-acceptance control has identical failure blocks and accept mass q,
but opposite accepted states. Full trace distance is q and conditional trace
distance is one. Thus the full-CQ guarantee must not be reused after
postselection without a suitable acceptance lower bound. The shared source
has an independently derived lower bound `(3/4)^3`; its acceptance effect
is not assumed scalar.

## 4. A physical repair for a rigorously enclosed Choi calculation

This lemma applies to **four labels, input and output dimension two**, using
normalized Choi blocks in `output tensor reference` order. Let the true
blocks `J_y` be positive and satisfy `sum_y tr_output J_y=I_2/2`. Suppose
exact Hermitian rational matrices `Q_y` obey a rigorously established bound

\[
e=\sum_y\|Q_y-J_y\|_1\le\delta.
\]

Here delta is a positive rational; choose `delta=10^-10` only if the
enclosure actually proves this hypothesis. Set

\[
\widehat J_y=Q_y+\delta I_4,\quad
a=(1+20\delta)^{-1},\quad
R=I_2/2-a\sum_y\operatorname{tr}_{\rm out}\widehat J_y,
\]

and define `J_phys_y=a Jhat_y` except that the declared failure block gets
the additional `|0><0| tensor R`.

Each `Jhat_y` is positive because `||Q_y-J_y||_infinity<=e<=delta`.
Writing `E=sum_y tr_out(Q_y-J_y)` yields
`R=a(2 delta I_2-E)>=0`, since partial trace contracts the trace norm of
Hermitian matrices and hence `||E||_infinity<=e<=delta`. Completeness is an
exact identity. The repair therefore defines a genuine complete instrument.
The failure addition is an explicit mathematical repair of the predictor;
it is charged as prediction error, not described as a new device outcome.

By the triangle inequality, positivity, and `tr R<=a(4 delta+e)`,

\[
\sum_y\|J_y^{\rm phys}-J_y\|_1
\le a(40\delta+2e).
\tag{A-T3}
\]

For input dimension d and normalized Choi matrices,
`||Delta||_diamond <= d ||J_Delta||_1`; one proof writes a purified input
as `(I tensor A)|Bell_d>` with `||A||_infinity^2<=d`, then uses trace-norm
submultiplicativity. With d=2, half-diamond is bounded by the right side of
(A-T3). Thus this source's delta and e hypotheses give a cost no larger than
`42*10^-10`, safely below `10^-8`. A floating eigenvalue check alone would
not establish the hypothesis or positivity.

This lemma is conditional until the B/root interval calculation supplies
the actual rational matrices and e. It is not a claim that A independently
ran that full interval calculation.

## 5. P-QMEM-02: rank across a causal break

Fix a cut, a set of preparation histories h, and a set of future test events t.
If only a D-dimensional quantum carrier crosses the cut, then

\[
H_{ht}=\operatorname{tr}(F_t\sigma_h),\qquad
\operatorname{rank}_{\mathbb R}H\le D^2.
\tag{A-M1}
\]

Indeed, expand the Hermitian subnormalized states and Hermitian effects in
one real basis of dimension `D^2`; H factors through that space. If a visible
system S and memory M cross, `D=d_S d_M`. If an observable reference also
crosses and varies with history, its dimension belongs in D too. After a
true causal break that discards S and prepares the same independent state,
with no varying accessible R, only M carries history and
`d_M>=ceil(sqrt(rank H))`. This is a necessary bound, not a constructive CP
compression theorem. The analogous purely classical bound is `rank H<=m`.
The future test t must be implemented identically for every h; it cannot read
the past-history label to choose a different output. Any retained log of h
available to the simulator or future controller is a memory crossing the cut
and must be included in D. Merely indexing the separately collected response
rows in the experimenter's final analysis does not supply such a physical
forward channel.

### Diagnostic in the same microscopic bath

Use the same two modes, Hamiltonian and vacuum. This *auxiliary* tester has
two histories: prepare `Z=s`, `s=+1,-1`, evolve `t=2/3`, discard S and
reprepare `|+>`, evolve `tau=3/4`, and measure `{(I+Y)/2,(I-Y)/2}`. R is
not used. The causal break erases S's historical information and does not
reset E. Writing `kappa_k=lambda c_k/omega_k`, the coherence is

\[
f_s=v e^{is\theta},\quad
v=\exp[-4\sum_k\kappa_k^2(1-\cos\omega_k\tau)],
\]
\[
\theta=4\sum_k\kappa_k^2
[\sin\omega_k t+\sin\omega_k\tau-\sin\omega_k(t+\tau)].
\tag{A-M2}
\]

To derive it, the first conditional evolution produces the coherent
amplitude `s alpha_k(t)`, where
`alpha_k(t)=kappa_k(exp(-i omega_k t)-1)`. The second conditional overlap
uses `U_-^dagger U_+=D(2 alpha_k(tau) exp(i omega_k tau))`. Evaluating the
coherent-state characteristic function gives (A-M2), including its Weyl
exchange phase.

For the standard Pauli Y convention, `p(Y+|s)=(1-s v sin(theta))/2`.
Consequently

\[
H=\frac12\begin{pmatrix}1-b&1+b\\1+b&1-b\end{pmatrix},
\qquad b=v\sin\theta.
\]

Throughout the frozen lambda interval, theta is strictly positive:
`sin x+sin y-sin(x+y)=4 sin(x/2)sin(y/2)sin((x+y)/2)`, and all three
sines are positive for both source modes. The elementary upper bound
`theta < 12(2/5)^2[1+(2/5)^2]=2.2272<pi` proves `b>0`. Thus H has rank
two for **every** `lambda in [1/5,2/5]`, and any finite quantum memory
realizing this diagnostic has dimension at least two. This does not prove
that two dimensions suffice for all bath histories.

| lambda | v | theta | smallest singular value `b` |
|---:|---:|---:|---:|
| 0.2 | 0.9441297623658087 | 0.07276960794228493 | 0.06864333270676033 |
| 0.3 | 0.8786608957699220 | 0.16373161787014107 | 0.14322264314572950 |
| 0.4 | 0.7945601017527617 | 0.29107843176913970 | 0.22802719571047592 |

Independent K=14 per-mode matrix exponentials reproduce the two
coherences with maximum floating residual `3.35e-16`. The interval-wide
rank proof above is analytic, not inferred from these three grid points.

A laboratory rank claim would need a simultaneous confidence region and
SPAM bounds excluding every rank-one response matrix. For example, an
operator-norm uncertainty below a certified positive second singular value
preserves rank at least two. Shared detector visibility rescales the signal;
unbounded history-dependent preparation/readout drift can imitate it.
The present result is a source-model theorem and synthetic calculation.

## 6. Evidence and sources

Run `python verify_a.py --contract PATH/TO/SHARED_MODEL.json` in this directory. It produces exact d=2–4 dual
identities, reference-retaining reconstruction checks, completeness and
congruence checks for the finite API, and the declared negative controls.
The first run found an unevaluated symbolic equality in SymPy; applying
symbolic simplification fixed the check without changing the theorem.

External context, not a claim of new literature priority:

1. G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of
   Quantum Theory*, Phys. Rev. A 84, 012311 (2011),
   https://arxiv.org/abs/1011.6451 . Its full background and axiom package
   cannot be replaced by the finite interface above.
2. E. Nielsen et al., *Gate Set Tomography*, Quantum 5, 557 (2021),
   https://arxiv.org/abs/2009.07301 . This supplies the standard context for
   simultaneous SPAM treatment and gauge freedom.
3. S. Milz and K. Modi, *Quantum Stochastic Processes and Quantum
   non-Markovian Phenomena*, PRX Quantum 2, 030201 (2021),
   https://doi.org/10.1103/PRXQuantum.2.030201 . Multi-time operational
   memory is the relevant comparison, rather than a one-time purification
   rank or a reset approximation.

The explicit formulas, norm constants, hidden-completion construction, and
source-specific causal-break witness are proved in this delivery. They are
project research increments; no claim of first discovery in the literature
is made.
