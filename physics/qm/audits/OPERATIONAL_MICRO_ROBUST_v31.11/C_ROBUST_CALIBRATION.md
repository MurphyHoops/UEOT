# Joint calibration and robust complete-record implementation

Internal research draft by agent C, 2026-11-11. This is a physics bridge in the
selected complex quantum model. It is not external peer review, a hardware
certification, or an independent selection of complex quantum mechanics.
The shared specification is `OPERATIONAL_MICRO_ROBUST_v31.11/SHARED_MODEL.md`.

## 1. Sources and the increment actually needed

The current scientific source is v31.10 / Kernel 1.10 at main
`16a89154183c22030d4526413167d095d94e6890`; publication 3.7 is a distinct
release. `QuantumActionRealizability.lean` already proves labelled Choi
realizability, support-restricted realizability, common observation-fibre
weights, and exact separating certificates. Its `choi_injective` concerns
actual complex-linear maps, not finitely sampled density matrices. Chapter 66
already connects the complete accepted finite source law, actual allowed
actions, initialization, retry costs and finite trace-distance error. Those
responsibilities are inherited, not reopened here.

The new arrows are: jointly uncertain physical source -> one deployable
parameter-independent policy -> robust complete-CQ guarantee, and a finite
microscopic instance -> that same guarantee including physical projection
failure. The general robust inequality below is a standard norm argument;
the substantive integration is the shared-parameter quantum instrument,
uniform all-input/reference cancellation, exact finite check and correctly
typed preparation/error/resource accounting.

## 2. General robust statement and proof

Fix one finite visible record alphabet R, one common terminal Hilbert space
(including the same untouched reference), and one declared input/reference
family X. For a complete physical protocol F write F_theta(x) for its
normalized complete CQ output. The output contains failure, leakage and stop
labels. Define

    d_X(F,G) = sup[x in X] (1/2)||F(x)-G(x)||_1.

X may be one prescribed input or all states of a declared support and
reference family. These scopes are different. The theorem does not convert
one scope into another and does not rename this supremum an energy-constrained
diamond norm. In finite dimensions it is a norm-derived operational distance
on the stated response family; on trace-class outputs the same argument uses
the trace norm.

Let C=C(D_cal) be a joint parameter set. A target T_theta and finite library
{A_a,theta} use the same theta. Let w_a(D_cal)>=0 sum to one, chosen without
access to unknown theta. Nominal objects T_hat,A_hat_a must have the same
record, support and reference contract. Suppose, for every theta in C,

    d_X(T_theta,T_hat) <= eta_T,
    d_X(A_a,theta,A_hat_a) <= eta_a,
    d_X(T_hat,sum_a w_a A_hat_a) <= r_nominal.

Then a real classical randomization of complete instruments gives

    sup[theta in C] d_X(T_theta,sum_a w_a A_a,theta)
        <= r_nominal + eta_T + sum_a w_a eta_a.                 (C.1)

Proof: for every theta and input x, insert T_hat(x) and the nominal mixture.
The triangle inequality gives three terms. The last is at most the weighted
sum of the action errors by homogeneity and the triangle inequality. Take
the two suprema. The randomized instrument is complete by nonnegative
normalized mixing; the randomization choice is a hidden implementation
index except insofar as its actual emitted visible label is part of R.
No solver, Choi-entry residual or average gate fidelity appears in this
proof. If w varies by history, this argument applies to a complete policy
library or to each legal observation fibre followed by a separate finite
hybrid/contractivity argument. Local errors do not become a global error
without that composition argument.

Calibration coverage is a separate probabilistic statement: if the model is
correct and P_theta(theta in C(D_cal))>=1-alpha_cal, then the deterministic
guarantee (C.1), on that coverage event, holds for the data-dependent legal
deployment. It does not establish membership of nature in the model.

### Robust impossibility and three-way decisions

Fix one legal witness input x* in X (including its reference) and one
full-record quantum effect 0<=F<=I. Define f_x*(A)=Tr[F A(x*)]. On output
states, f(Omega)=Tr(F Omega) obeys
|f(Omega)-f(Gamma)|<=D(Omega,Gamma) on normalized states. If for every theta,

    f(T_hat)-e_T > max_a [f(A_hat_a)+e_a] + epsilon,            (C.2)

where every f on a protocol means f_x*, and the e's bound the corresponding
expectation errors. Then every mixture
is farther than epsilon for every theta in C. Proof: a mixture's expectation
is bounded by the maximum of its components and the target expectation by
the displayed lower bound; apply the effect bound. A more general real
linear functional requires its actual dual norm; there is no implicit
unit-Lipschitz assumption.

The exact checker returns `CERTIFIED_FEASIBLE` only from an upper bound,
`CERTIFIED_INFEASIBLE` only from a valid lower/separation bound, and
`INSUFFICIENT_CERTIFICATE` otherwise. A failure to optimize is never a
physical impossibility result. A bound equal to the maximum distance one
is explicitly uninformative for any precision below one.

## 3. One microscopic source and one complete output

Use the shared qubit-oscillator model with G=n+P_e, positive finite reference
R, theta=(q,phi,alpha), and s=1-q/2. The two actual gates are

    U0(theta)=exp(-i phi P_e),
    U1(theta)=exp[-i alpha(a sigma_+ + a^dagger sigma_-)].

The three-level flag has excitation operator zero and independent pure
ready state. Preparing amplitudes sqrt[s(1-q)],sqrt[sq],sqrt[1-s], controlling
the actual U0,U1,I and measuring the flag derives the source instrument

    K0=sqrt[s(1-q)] U0, K1=sqrt[sq] U1, Kf=sqrt[1-s] I.

B supplies a unitary construction and its domain/filtration proof. The
chosen degeneracy allows excitation conservation; preparation, readout and
erasure are not free. The source, target, actions and calibration must use
the same q and same actual gates. Treating three independently uncertain
gates as equal is an additional false assumption, not a robustness theorem.

The source has height two, stops on the first f, and accepts two successes.
The complete terminal alphabet is {f,0f,1f,00,01,10,11}. For a word r of
successes, V_r is the chronological product of its gates. Raw probabilities
and terminal states are

| record | probability | terminal state on SR |
|---|---:|---|
| f | 1-s | rho |
| 0f | s(1-q)(1-s) | U0 rho U0^* |
| 1f | sq(1-s) | U1 rho U1^* |
| 00 | s^2(1-q)^2 | U0 U0 rho U0^* U0^* |
| 01 | s^2(1-q)q | U1 U0 rho U0^* U1^* |
| 10 | s^2 q(1-q) | U0 U1 rho U1^* U0^* |
| 11 | s^2 q^2 | U1 U1 rho U1^* U1^* |

All operators act as identity on R. The probabilities sum to one. The
backward effects are H_t=s^(2-t)I, and p_accept=s^2. The normalized accepted
source law T_theta has the four successful weights divided by s^2 and has
zero blocks for f,0f,1f. This is the existing finite conditioning theorem
on this derived source. The raw source still has its three failure leaves;
it is not asserted equal to a failure-free protocol.

The allowed library emits 0 with gate U0 or 1 with gate U1. Deploy an
independent w=1/2 coin at both times, fixed using the calibration record,
never the true q. The coin result is the visible emitted action label; its
seed and implementation refinements are not extra visible records. The
same w is used in every observation fibre, including hidden nodes sharing
one visible history. The compiled protocol C_w has four product Bernoulli(w)
record weights and exactly the same V_r rho V_r^* as T_theta on each word.

## 4. Exact all-input robust certificate

For every normalized joint input rho_SR and every allowed finite reference,
each successful difference block is a real scalar times the same density.
Its trace norm is the absolute scalar because the density is positive with
trace one. Direct sums add trace norms. Therefore, without tomography or a
Choi approximation,

    D(T_theta(rho), C_w,theta(rho))
      = 1/2 sum[r in {00,01,10,11}] |P_q(r)-P_w(r)|
      = |q-w| (1+|q+w-1|).                                  (C.3)

For q>=w, the 00 and 11 absolute differences sum to 2(q-w); the two mixed
blocks contribute 2(q-w)|1-q-w|. The opposite ordering follows by symmetry.
This proves the formula for every q,w in [0,1]. With q in [12/25,13/25]
and w=1/2, set d=|q-1/2|<=1/50. Then

    D <= d(1+d) <= (1/50)(51/50)=51/2500=0.0204.              (C.4)

The uncertain phi,alpha cancel exactly because they are the same on each
path; their numerical sizes need not be estimated for this comparison.
This retains source correlations and is strictly stronger than separately
bounding each uncertain gate against an unrelated nominal gate. No optimality
over all adaptive/correlated controller policies is claimed. The product
coin is one legal certificate, not a universal optimal-policy theorem.

### A strictly better legal policy using the visible first label

For the larger permission class that observes the first visible label, root
derived and C independently checked the following improvement. Set
delta=1/50 and deploy the fixed word law

    Q00=Q11=1/4+delta^2=313/1250,
    Q01=Q10=1/4-delta^2=312/1250.

It is implemented by a first fair coin and a second label-1 probability
313/625 after visible 1, or 312/625 after visible 0. The policy uses no
unknown q and no hidden source branch. It is legal only if the first label
is available to the controller; a controller that sees no first label must
retain the memoryless certificate above.

Put t=q-1/2, x=|t|<=delta and u=delta^2-t^2>=0. The four signed differences
are -t-u,u,u,t-u, so complete-CQ distance equals max(x,u)+u. If x>=u then
x+delta^2-x^2<=delta because x-x^2 is increasing on [0,delta]. If x<=u then
2u<=2delta^2<=delta. Thus

    sup_q D(T_q,C_adaptive)=delta=1/50.                     (C.4a)

This value is minimax over the **full frozen design region**
Theta*=[12/25,13/25], under the stated library and observation permissions:
the compiled first-label marginal is a fixed number m for one deployed
policy, and max(|m-(1/2-delta)|,|m-(1/2+delta)|)>=delta.
That follows from the triangle inequality on real numbers. The constructed
policy attains this lower bound. This lower bound allows arbitrary
correlation in the two choices. Its critical premises are that each library
action emits its predetermined label and that no extra q-dependent source
query or quantum tester is inserted during the run. Additional observation
would be a different optimization problem. Unknown phases cannot change
these deterministic-label probabilities. This is a genuine finite benefit
from permitted memory, not a claim about unrestricted coherent controllers.
The realized calibration interval below is narrower than Theta*. This
design-region lower bound must not be transferred to every realized
C(D_cal), nor used to claim the fixed policy is optimal for that dataset.
A smaller confidence set can support better weights; this iteration uses
the design certificate conservatively after verifying subset containment.

For the supported matrix witness, basis order is |g,0>,|e,0>,|g,1>,
U0=diag(1,(3+4i)/5,1), and U1 has the 2x2 block
[[3/5,-4i/5],[-4i/5,3/5]]. Both are exactly unitary and preserve G. A retained
two-dimensional reference is entangled with the one-excitation doublet.
The independent exact checker derives all seven raw blocks and the four
target/compiled blocks and verifies the equality by rational/symbolic
algebra. A separate root computation checks the same bound independently.

### Quantifier and visibility failure controls

For every q individually, choosing w(q)=q realizes T_q exactly. Over the
full frozen design region Theta*, no fixed
legal policy independent of q realizes both q=12/25 and q=13/25: the first
visible-label-1 marginal would have to be two different numbers. More
strongly, for any fixed response distribution its first marginal m obeys
max(|m-12/25|,|m-13/25|)>=1/50. Thus uniform precision 1/100 is impossible
even if arbitrary legal history-dependent or correlated second choices are
allowed. This is `forall policy exists theta`, not `forall theta forall
policy`. At each theta exact realization remains possible if an oracle
reveals it, which deployment forbids.
The 1/100 impossibility statement is for Theta*, not for a narrower realized
confidence interval that does not contain both design endpoints.

Restricting the library to the 0 action gives the stronger different result:
for every q in the interval and every available policy, the first-label-1
effect has target probability at least 12/25 and compiled probability zero.
That library is uniformly separated at every physical candidate.

Relabeling an otherwise identical deterministic gate from 0 to 1 leaves the
summed CP map and terminal marginal unchanged while full-CQ distance is one.
Checking only the vacuum input also produces false success: U0 and U1 both
leave vacuum invariant, whereas I and U1 differ on |e,0> by trace distance
4/5. A fixed reachable-input check does not certify the full-support map.

## 5. From microscopic truncation to physical output

B proves the normal trace-class truncation theorem and branch intertwining
from microscopic excitation conservation, not from an assumed error field.
For Tr(G rho_S)<=1, N=4095, the discarded weight delta is at most 1/4096
and D(rho,rho_N)<=1/64 after the declared embedding.

Here conditioning is an input-independent CPTP channel because H_0=s^2I.
Consequently its truncation bound remains 1/64 directly by contraction.
The normalized target/compiled comparison is bounded by

    1/64+51/2500 = 0.036025.

This is not yet free physical preparation. Retain an initial projection
pass/fail flag and compare the ideal always-pass target with the actual
filter output. The common alphabet is extended to `prep_fail` and every
`pass/r` with r in the original seven-record alphabet. The target has a
zero prep_fail block; no failed mass is deleted from the physical output.
B's safe complete-output bound is sqrt(delta)+delta, so the
actual preparation plus compilation guarantee is

    65/4096+51/2500 = 0.036269140625 < 1/20.                  (C.5)

With the visible-history policy, the stronger full-output bound is

    65/4096+1/50 = 0.035869140625 < 1/20.                    (C.5a)

Its remaining unmeasured physical-error allowance is 0.014130859375.

Failure has its own terminal record, and unknown input/reference states
are not retried. The remaining margin 1/20-(C.5)=0.013730859375 is an
allowance for independently bounded actual gate/preparation/readout/model
errors, not evidence those errors fit. On the exactly supported G<=1
witness delta=0. There is no eigensolver or near-zero-support cutoff in this
certificate. For a non-scalar acceptance effect, B's distinct trace-class
posterior theorem and a positive success floor are needed; (C.5) cannot be
silently transferred to that case.

Numerical rounding, model approximation, calibration coverage and finite
statistical testing are different quantities. The analytic bound has zero
rounding error in the rational checker, and no empirical estimate of the
physical model discrepancy. The RWA/JC model relation to a device remains
an explicit E assumption.

## 6. Independent calibration and held-out record analysis

Measure n=80000 independent complete source flags in separate preparations,
with fixed q during calibration and deployment and the same flag apparatus.
All 0,1,f records are retained. Since P(f)=1-s=q/2, let qhat=2 k_f/n and

    C(D_cal)=[qhat-1/100,qhat+1/100] intersect [0,1].

More precisely this is C_q. The joint set is
C_q(D_cal) x Phi_allowed x Alpha_allowed, with s=1-q/2 retained as a
deterministic relation. The flags identify q only. They do not identify
phi or alpha or establish that the source and library gates match. That
equality is a separately declared physical premise; mismatches need their
own nuisance set and error allowance.

One should reject an empty set as a model/data inconsistency. No arbitrary
clipping of an estimate conceals it. The deployment rule certifies (C.4)
only if the entire confidence interval lies in [12/25,13/25]. Otherwise it
returns insufficient certificate for this frozen deployment.

The coverage proof is transparent. For a Bernoulli X with mean p, the
second derivative of log E exp[t(X-p)] is the variance under exponential
tilting and is at most 1/4. Its value and first derivative at zero vanish,
so log E exp[t(X-p)]<=t^2/8. Independence, exponential Markov and optimizing
t give P(|Xbar-p|>u)<=2 exp(-2 n u^2). Use p=q/2 and u=1/200:

    P(q outside C)<=2 exp(-4)<1/20.

The last inequality has an exact rational certificate: a finite positive
Taylor sum for exp(4) exceeds 40. This is the bounded-variable argument of
Hoeffding, *Probability Inequalities for Sums of Bounded Random Variables*,
JASA 58 (1963), 13–30, DOI 10.1080/01621459.1963.10500830. Original paper
metadata were checked; the proof used here is written out above.

This coverage does not survive arbitrary correlations. If all shots share
one latent flag, with P(f)=1/4 and P(0)=P(1)=3/8, each shot has the correct
marginal at q=1/2 but the interval excludes q=1/2 with probability one.
Likewise arbitrary preparation failures, readout confusion or leakage alter
the likelihood. They need calibrated nuisance parameters and explicit
records; they cannot be dropped before counting.

`synthetic_calibration.py` creates explicitly synthetic time-ordered flag
records, computes the interval, and analyzes distinct held-out source and
compiled record files. It does not take the generating q as an analysis
input. A model-theta field exists only in synthetic provenance. Held-out
tests compare the seven record probabilities within the joint calibrated
q interval; they never claim full quantum-state tomography. The exact
checker separately verifies a rational simultaneous testing allowance.
This runnable path is an algorithmic/synthetic validation, not an executed
natural experiment.

## 7. Costs, identifiability and missing data

For independent fresh source trials, the original expected number of
source steps per attempt is 1+s and success probability s^2. If c_p is
preparation cost, c_s the complete source-step cost, and c_r failure-reset
cost, then

    E[cost per accepted source] =
        [c_p+(1+s)c_s+(1-s^2)c_r]/s^2.

Here c_s includes flag preparation, controlled gate, readout, classical
processing and record storage; calibration amortization is separate.
Compiled cost after a successful prepared input is two actual gates plus
two randomizations, readouts, classical updates and records, with their
actual action-dependent expectations. Physical cutoff preparation costs,
its rejected output and any permissible known-state re-preparations are
separate. For genuinely re-preparable iid known states only, a filter of
success s_N gives expected preparation cost
[c_p+c_filter+(1-s_N)c_reset]/s_N. This formula is not applied to an unknown
input or a retained reference that cannot be re-prepared. No time, joule,
money, hardware speed or amortized cost advantage has been measured.

The present model already has an ordinary unitary quantum-environment
dilation. A competing interpretation admitting that same environment has
identical p(r|pi,theta) for every allowed intervention, not just these seven
records. This example therefore does not identify objective collapse or a
new UEOT law. There is no independent activation law, positive rate lower
bound or new coherence/heating relation in this iteration.

The inspected current source, conditioning reference and empirical audits
provide no acquired protocol-matched hardware data. The old receipt states
`new_hardware_data=false`. This is a scoped finding, not an assertion that
no data exist anywhere. To run a real test we still need:

1. Ordered calibration shots with raw 0/1/f, preparation failures, leakage,
   readout-confusion calibration and source/device identity.
2. The same gates' independently bounded source/action mismatch and the
   actual pulse/JC regime, oscillator excitation budget and drift window.
3. Held-out complete source and compiled records, fixed acceptance and
   stopping rules, shot allocation and preregistered test thresholds.
4. Terminal-state/reference tester outcomes if a measured full-CQ error is
   claimed; seven record counts alone measure only a finite tester family.
5. Operation, failed preparation, reset, storage/classical processing and
   calibration costs with units and uncertainty; data authorization.

## 8. Verification axes and next admissible result

Paper: (C.1)–(C.5), uniform/pointwise quantifiers and the failure controls
are proved above under explicit inputs. Machine theorem status: no new
Lean theorem is claimed by this C draft; A supplies the actual new
operational-semantics formality, and v31.10 exact action proofs remain
inherited. Exact arithmetic: the independent script checks source/target
probabilities, rational matrices, reference retention and stated numerical
certificate values. Synthetic: records, interval and held-out analysis
are generated and labeled. External/project empirical: unverified.

The next C target is a genuinely joint calibrated nuisance set including
readout confusion, source/action pulse mismatch and drift, with a
full-response certificate still below the remaining 0.013730859375 margin.
If only finite testers are accessible, state that narrower norm. Removing
the scalar backward effect or certifying an actual device spectral support
requires a separate stability proof; this example does not supply it.
