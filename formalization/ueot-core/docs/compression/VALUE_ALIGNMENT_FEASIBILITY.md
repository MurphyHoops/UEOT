# Value Alignment Compression — Feasibility Audit

Status: **LOCAL LEAN PASS / EXACT P-ALI-02 + P-ALI-03 ADAPTERS / GENERATIVE BRIDGE / UNCOUNTED**

This audit tests a proposed M-VA compression for the alignment chapter.  The
candidate is intentionally restricted to P-ALI-02 and P-ALI-03.  P-ALI-01 is
retained as a separate integrability boundary.

## 1. Shared mathematical object

Let `g` be the gradient of the parent value.  For any candidate update
direction `v`, define the first-order parent directional score

\[
S_g(v)=\langle g,v\rangle.
\]

This is the common object behind the two frozen source theorems:

- P-ALI-02 studies the score of imperfect child directions relative to the
  parent gradient;
- P-ALI-03 studies how the score changes when a misaligned direction is
  interpolated toward the parent gradient.

The local Lean module is

`UEOT/V3/Compression/ValueAlignment.lean`.

## 2. Robust-direction core from P-ALI-02

For an imperfect target direction

\[
v=g+e,
\]

M-VA proves the exact decomposition

\[
S_g(g+e)=\|g\|^2+\langle g,e\rangle
\]

and the Cauchy--Schwarz lower certificate

\[
S_g(g+e)
\ge
\|g\|\bigl(\|g\|-\|e\|\bigr).
\]

The finite weighted direct-sum theorem

`p_ali_02_core_via_mva`

reconstructs the algebraic P-ALI-02 core.  The source-facing theorem

`p_ali_02_via_mva`

has the exact frozen P-ALI-02 signature.  Its calculus-specific obligations are
still explicit:

- the parent `HasGradientAt` certificate;
- the actual trajectory `HasDerivAt` certificate;
- the Hilbert direct-sum chain rule;
- the component expansion.

M-VA supplies the shared directional robustness certificate rather than hiding
those source assumptions.

## 3. Coordination-threshold core from P-ALI-03

For scalar endpoint scores `base` and `target`, define

\[
S_\eta=(1-\eta)\,base+\eta\,target.
\]

If

\[
base<0,
\qquad
target\ge0,
\]

then Lean proves

\[
S_\eta>0
\iff
\eta>
\frac{-base}{target-base}.
\]

The inner-product identity

\[
S_g((1-\eta)G+\eta T)
=
(1-\eta)S_g(G)+\eta S_g(T)
\]

then specializes this scalar theorem back to Hilbert-space directions.

`p_ali_03_via_mva` has the exact frozen P-ALI-03 signature, including the
source domain assumptions `0 <= eta <= 1` even though the bare scalar
zero-crossing equivalence itself does not need both bounds.

## 4. New cross-theorem consequence

The main out-of-sample theorem is

`robust_coordination_positive`.

P-ALI-03 coordinates from a bad direction `G` toward the *ideal* target `g`.
The new theorem instead allows the target itself to be imperfect:

\[
T=g+e.
\]

Assume

\[
S_g(G)<0,
\qquad
\|e\|<\|g\|.
\]

P-ALI-02's robustness certificate gives the guaranteed positive target margin

\[
m=\|g\|\bigl(\|g\|-\|e\|\bigr)>0,
\]

with

\[
m\le S_g(g+e).
\]

Therefore the conservative coordination threshold

\[
\eta>
\frac{-S_g(G)}{m-S_g(G)}
\]

is sufficient for

\[
S_g((1-\eta)G+\eta(g+e))>0.
\]

This result is not one of the frozen 106 P-ID endpoints.  It is a genuine
composition of the robust-direction content of P-ALI-02 and the threshold
content of P-ALI-03.

## 5. Why P-ALI-01 must remain separate

P-ALI-01 proves a fundamentally different statement:

\[
\text{IsExactForm}(\omega)
\iff
\text{ClosedPeriods}(\omega)
\]

on the specified connected manifold setting.

Its role is prior to M-VA.  It asks whether a local directional one-form can be
integrated into a globally defined scalar value at all.  M-VA assumes that the
parent scalar value/gradient needed for `S_g(v)` is already meaningful and then
studies local directional improvement.

Therefore the correct architecture is

\[
\text{P-ALI-01 integrability boundary}
\longrightarrow
\text{global parent value, when available}
\longrightarrow
\text{M-VA local directional alignment}.
\]

Absorbing P-ALI-01 into M-VA would erase a genuine no-go condition: a locally
specified “good direction” need not arise from any globally consistent value
landscape.

## 6. Alignment is not GOA

M-VA proves instantaneous directional improvement certificates.  It does not
prove:

- existence of a long-run attractor;
- convergence of the closed-loop trajectory;
- uniqueness of an invariant law;
- compactness/tightness;
- Lyapunov recurrence;
- contraction.

Those are separate long-run obligations handled by M-OI, M-CF, M-PE, or other
domain-specific machinery.

Thus

\[
S_g(v)>0
\]

must not be promoted to “the system converges to GOA” without an additional
bridge theorem.

## 7. Does M-VA qualify as a new counted generator?

### Positive evidence

- exact source-facing adapters exist for two frozen P-IDs;
- the common directional-score representation is non-cosmetic;
- the same robustness/threshold components generate a new imperfect-target
  coordination theorem;
- the abstraction clarifies the UEOT hierarchy from parent value to local
  aligned motion.

### Blocking evidence

The two source theorems still have materially different principal proof
obligations:

- P-ALI-02 needs differential calculus, heterogeneous Hilbert direct sums, and
  a Cauchy--Schwarz robustness estimate;
- P-ALI-03 needs affine interpolation and a scalar zero-crossing calculation.

There is not yet one minimal theorem from which both complete source theorems
fall out as genuinely thin adapters.  The current module is better described as
a **typed directional-value calculus** whose pieces compose, not one generator
that replaces two theorem families.

## 8. Classification

Recommended classification:

**M-VA = VALID VALUE-ALIGNMENT BRIDGE CALCULUS, GENERATIVE, UNCOUNTED.**

The canonical counted core remains

\[
\{M\text{-QD-01},M\text{-TC-01},M\text{-PE-01},M\text{-OI-01}\}.
\]

No compression-ledger promotion is justified by the present evidence.

## 9. UEOT architectural consequence

The formal picture now supports the following typed chain more strongly:

\[
\text{global value, if integrable}
\to
\text{parent gradient}
\to
\text{directional score}
\to
\text{robust local alignment / coordination}
\to
\text{closed-loop dynamics}
\to
\text{separate long-run GOA analysis}.
\]

This is stricter than identifying local “GOD-like” improvement with a global
attractor.  The formal boundaries are now explicit.
