# UEOT MINCORE — Calibrated Defect Comparison V1

Status: **research bridge candidate; additive / uncounted**  
Active PR: **#323**  
Frozen Core impact: **NONE**  
Counted compression generators: unchanged — `M-QD-01`, `M-TC-01`, `M-PE-01`, `M-OI-01`.

## 1. Question

The preceding MINCORE relation/defect no-go established two separate facts.

1. An exact relation, even when represented as the zero set of a nonnegative defect, does not determine the quantitative scale of that defect.
2. Nonnegativity plus exact zero-set compatibility does not force the triangle/composition regularity required by the transport-certificate generator.

The next admissible question is therefore not whether the exact relation alone determines M-TC. It does not. The correct question is:

> If an independent quantitative calibration bridge between two defect presentations is supplied, exactly which M-TC conclusions transport, with which constants, and which quantities remain gauge-dependent?

This note records the Lean answer implemented in
`UEOT/V3/Compression/TheoryCompletion/MinCore/CalibratedDefectComparison.lean`.

## 2. Minimal calibration object

For two `RelationDefectPresentation X` objects `P` and `Q`, define

`DefectCalibration P Q a b`

by the four assumptions

```text
0 < a
0 <= b
a * P.defect x y <= Q.defect x y
Q.defect x y <= b * P.defect x y
```

for every `x,y`.

Two assumptions deliberately **are not** fields of the structure:

- `P.rel = Q.rel`;
- `a <= b`.

They are unnecessary for the stated bridge. In particular, equality of exact relations is a theorem, not an input: positive two-sided comparability forces equality of the zero sets, and each presentation already identifies its zero set with its exact relation.

Thus the bridge is quantitative and non-circular. It does not smuggle the qualitative conclusion into its premises.

## 3. Machine-checked conclusions

The module proves the following hierarchy.

### 3.1 Zero-set covariance

`DefectCalibration.zero_defect_iff`

```text
P.defect x y = 0  <->  Q.defect x y = 0.
```

The forward direction uses the upper comparison and nonnegativity of `Q`; the reverse direction uses the positive lower factor `a` and nonnegativity of `P`.

### 3.2 Exact-relation covariance

`DefectCalibration.rel_iff`

```text
P.rel x y  <->  Q.rel x y.
```

This is derived from zero-set covariance plus the two presentations' registered `zero_iff` contracts. No independent same-relation assumption is used.

### 3.3 Finite-budget transport

`DefectCalibration.forward_budget`

```text
P.defect x y <= epsilon
---------------------------------
Q.defect x y <= b * epsilon.
```

`DefectCalibration.reverse_budget`

```text
Q.defect x y <= epsilon
---------------------------------
P.defect x y <= epsilon / a.
```

Therefore a numerical certificate is not invariant, but it is controllably transportable once its calibration is independently supplied.

### 3.4 Qualitative asymptotic covariance

`DefectCalibration.tendsto_zero_iff`

For fixed finite calibration constants and arbitrary sequences `x n, y n`,

```text
P.defect (x n) (y n) -> 0
    <->
Q.defect (x n) (y n) -> 0.
```

This sharply separates a gauge-covariant qualitative conclusion from gauge-dependent finite-time numbers.

The theorem intentionally concerns a fixed calibration. It does not assert that an arbitrary unbounded stage-dependent upper factor preserves convergence.

### 3.5 Canonical gauge example

`rescaleCalibration`

Positive rescaling of a defect by `c` supplies a calibration with `a=b=c`. This connects the comparison theorem directly to the preceding MINCORE rescaling no-go.

### 3.6 M-TC finite-horizon certificate transport

`calibrated_weighted_chain_bound`

For heterogeneous stage types `A n`, stagewise presentations `P n, Q n`, and a stagewise calibration `C n`, assume the registered M-TC local recurrence hypotheses for **P**:

- one-step contraction bound;
- triangle/composition bound;
- local defect budget;
- nonnegative contraction coefficients.

The theorem first invokes the registered generator theorem
`TransportCertificate.weighted_chain_bound` exactly once, obtaining the complete P-side finite-horizon envelope. It then transports that already-established conclusion through the target-stage upper calibration:

```text
Q_n(ideal_n, actual_n)
  <= b_n * [
       (product_{j<n} L_j) P_0(ideal_0,actual_0)
       + sum_{k<n} epsilon_k product_{k<j<n} L_j
     ].
```

The terminal factor `b_n` is explicit.

Crucially, this theorem does **not** claim that calibration alone transports the local contraction or triangle hypotheses from P to Q. Those are independent structural properties of the source M-TC certificate unless additional assumptions are supplied.

## 4. No-calibration failure witness

`same_relation_does_not_transport_unit_budget`

uses the Boolean equality presentation with unit off-diagonal defect and its factor-two positive rescaling.

Both presentations have exactly the same equality relation, but

```text
P.defect false true = 1
Q.defect false true = 2.
```

Hence the unit numerical budget holds for P and fails for Q.

This is the required finite counterexample showing why the exact relation cannot substitute for a quantitative calibration bridge.

## 5. What is gauge-covariant and what is gauge-dependent?

| Quantity / conclusion | Under fixed two-sided calibration |
|---|---|
| zero defect | invariant |
| exact relation | invariant |
| qualitative defect -> 0 | invariant |
| numerical defect value | not invariant |
| finite epsilon-budget | not invariant; scales by explicit bridge constants |
| registered P-side M-TC finite-horizon conclusion | transports with terminal factor `b_n` |
| local triangle hypothesis | **not established as invariant** |
| local contraction coefficient | **not established as invariant** |
| four-generator counted core | unchanged |

This is the key structural result of the round: calibration is a **bridge between typed quantitative presentations**, not an identification of all quantitative structure.

## 6. Scientific interpretation

The new theorem closes the route left open by the relation/defect no-go as far as finite M-TC certificate transport is concerned:

- relation alone: insufficient;
- relation plus an uncalibrated defect: insufficient;
- explicit quantitative calibration: sufficient to move an already-proved finite certificate, with computable scale change.

This strengthens the current MINCORE interpretation of UEOT as a typed network of primitives and bridge theorems. Exact relation/quotient information and quantitative transport information are related, but one does not determine the other without extra calibration data.

This is a positive unification result at the level where the mathematics supports it, and a no-go against stronger identification where it does not.

## 7. Non-claims

This work does not establish:

- an absolute logical independence theorem for the four generators in every possible formal system;
- reduction or deletion of `M-TC-01`;
- a universal physical Ω;
- a unique physical Π/Φ mechanism;
- universal GOD/GOA;
- objecthood uniqueness;
- full C1-C7 closure;
- full Unified Mathematical Closure.

Issue #302 therefore remains OPEN / NOT_ESTABLISHED for the full UMC objective.

## 8. Validation state

Local preflight on the active research worktree:

- focused Lean check of `CalibratedDefectComparison.lean`: PASS;
- full Lake build through public `TheoryCompletion` root before the asymptotic extension: PASS;
- UMC global DAG regeneration after the final theorem extension: PASS;
- unified-closure negative-control suite: PASS;
- regenerated DAG: 635 first-party Lean modules, all 635 reachable from `UEOT` root, 0 cycles, 0 missing internal imports;
- total theorem/lemma tokens: 3985;
- total source lines: 111967;
- Theory Completion category: 56 modules;
- source-tree SHA-256: `938e5b30c09df1f317156ee4d91e395a8aa3f5287626f2fa505502eefe336a3d`.

GitHub exact-head CI and independent review receipts are intentionally not frozen into this report until the final research head is stable.
