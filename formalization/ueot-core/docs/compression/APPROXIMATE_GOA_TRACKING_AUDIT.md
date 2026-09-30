# Approximate Agency / Near-GOA Tracking — Audit

Status: **LOCAL FOCUSED LEAN PASS / M-TC RE-ENTERS END-TO-END CHAIN / UNCOUNTED**

Module:

`UEOT/V3/Compression/ApproximateGoaTracking.lean`

This lane extends the exact finite Agency -> GOD -> GOA assembly into a
quantitative perturbative setting.  Its main purpose is to test whether M-TC
can participate essentially in an end-to-end result rather than only in local
transport certificates.

## 1. Why stationary perturbation alone is not enough

Approximate state representations, online estimates, or drifting models need
not induce one stationary Markov kernel.  Requiring the perturbed system to
already possess its own invariant law would therefore be too strong and would
hide the most interesting error-propagation problem.

The local theorem instead permits a sequence of stochastic kernels

\[
P_0,P_1,P_2,\ldots
\]

driving an actual law sequence

\[
\mu_{n+1}=\mu_nP_n.
\]

Only one reference kernel `Pstar` is required to be Dobrushin stable.

## 2. Reference GOA

Assume

\[
\alpha(P_*)<1.
\]

The theorem does not assume a reference invariant law.  It obtains one through
the registered M-OI / P-GOA-01 occupation-limit route and then obtains
uniqueness through M-CF.

Thus the reference GOA remains a conclusion of the formalized architecture.

## 3. Local drifting-kernel defect

For every time `n` and state `x`, assume

\[
D_{TV}(P_*(x,\cdot),P_n(x,\cdot))\le \epsilon_n.
\]

`FiniteDobrushin.tv_step_cross_le` turns this rowwise certificate into the
one-step law defect

\[
D_{TV}(\mu_nP_*,\mu_nP_n)\le\epsilon_n.
\]

This is the local error injected after one reference contraction step.

## 4. M-TC weighted near-GOA theorem

`timeVarying_kernel_near_goa` instantiates

`TransportCertificate.weighted_chain_bound`

with:

- ideal trajectory: the constant invariant law `μ*`;
- actual trajectory: `μ_n`;
- reference step: `ν -> ν Pstar`;
- transport coefficient: `α(Pstar)`;
- local defect: `ε_n`.

The resulting bound is

\[
D_{TV}(\mu_*,\mu_n)
\le
\left(\prod_{j<n}\alpha\right)
D_{TV}(\mu_*,\mu_0)
+
\sum_{k<n}\epsilon_k
\prod_{k<j<n}\alpha.
\]

The power-form theorem `timeVarying_kernel_near_goa_power` gives

\[
D_{TV}(\mu_*,\mu_n)
\le
\alpha^nD_{TV}(\mu_*,\mu_0)
+
\sum_{k<n}\epsilon_k\alpha^{n-1-k}.
\]

This is the exact finite discrete-Gronwall form expected from the UEOT
transport architecture.

## 5. Uniform near-GOA tube

If

\[
\epsilon_k\le\bar\epsilon,
\]

then `timeVarying_kernel_near_goa_uniform` proves

\[
D_{TV}(\mu_*,\mu_n)
\le
\alpha^nD_{TV}(\mu_*,\mu_0)
+
\bar\epsilon\sum_{j<n}\alpha^j.
\]

This exposes the standard engineering interpretation: contraction forgets the
initial-condition error while persistent local model error leaves a finite
geometric tracking tube.

## 6. Approximate-control specialization

For one

`ApproxControlQuotient Q`,

define the implemented stationary policy as the lifted macro-greedy selector:

`approximateGodPolicy Q = quotientLiftedPolicy Q`.

P-QUO-02 already proves on the baseline micro model:

\[
0\le
V^*_{micro}(x)-V^{\pi_{approx}}_{micro}(x)
\le 2D.
\]

The theorem

`approximate_god_and_timeVarying_near_goa`

combines that control certificate with the time-varying kernel theorem.

Its reference closed loop is exactly

`policyMatrix Q.micro (approximateGodPolicy Q)`.

A sequence of other models on the same state/action carrier may vary with
time.  Under the exact same implemented policy, rowwise policy-kernel defects
`ε_n` give the weighted near-GOA tracking certificate.

Hence one theorem now contains:

\[
\boxed{
\text{P-QUO-02 near-optimal control}
+
\text{M-TC finite defect propagation}
+
\text{M-OI invariant existence}
+
\text{M-CF contraction stability}
}
\]

without assuming the perturbed process is stationary.

## 7. Essential boundaries

### Baseline near-optimality only

The `2D` regret certificate belongs to `Q.micro`.

The theorem does **not** infer that the same policy is near-optimal for every
time-varying model `Mseq n`.  Rowwise transition closeness alone is insufficient
for such a statement because reward and value geometry also matter.

To certify per-time near-optimality, each `Mseq n` needs its own value/quotient
certificate or a stronger shared perturbation theorem.

### Same implemented policy

The near-GOA comparison uses exactly one stationary policy across the reference
and drifting models.  This identity guard is deliberate.  If the controller
itself changes with time, an additional policy-variation defect must enter the
transport bound.

### Same state/action carrier

The drifting control specialization works on the baseline micro state/action
carrier.  It does not by itself compare laws on different quotient state
spaces.

### Approximate sufficient-state learning is not yet proved

The current result begins from controlled-model and row-TV certificates.  It
does not infer those certificates from raw history data or from a learned
state encoder.  That remains a separate representation-learning/estimation
problem.

### Reference Dobrushin margin

Strict Dobrushin contraction is sufficient, not necessary.  The theorem does
not rule out meaningful near-GOA behavior in recurrent/noncontractive systems.

## 8. Compression significance

This result is more important as a **composition theorem** than as a candidate
new generator.

It demonstrates that the four-generator/bridge architecture can handle both:

- exact structural assembly; and
- quantitative nonstationary perturbations.

In particular, M-TC is now essential in an end-to-end control/long-run theorem
rather than appearing only in its original finite transport families.

Recommended classification:

**APPROXIMATE AGENCY -> near-GOD / near-GOA TRACKING: GENERATIVE BRIDGE PASS,
UNCOUNTED.**

The four counted generators remain unchanged.

## 9. Next pressure test

The next harder step should connect the local row-TV certificates back to a
history-level approximate sufficient-state representation.  A valid theorem
must distinguish:

1. encoder/fibre defect;
2. reward defect;
3. transition-law defect;
4. optional controller/policy defect.

Only then can one honestly state an end-to-end result from **approximate learned
state** all the way to near-optimal action and near-GOA tracking.
