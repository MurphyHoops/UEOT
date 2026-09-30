# Approximate Recurrent GOA Stability Modulo Gauge — Audit

Status: **LOCAL LEAN PASS / P-GOA-03 GAUGE LIFT FORMALIZED / UNCOUNTED**

Module:

`UEOT/V3/Compression/ApproximateRecurrentGaugeStability.lean`

## 1. Problem closed by this lane

Frozen P-GOA-03 is intentionally coordinate-specific: it compares two
`FiniteRecurrentDecomposition`s that share the same transient type and the same
recurrent-class partition.  Its perturbation radius is built from

- transient-block error `epsQ`;
- recurrent-entry error `epsR`;
- class-law TV errors `epsStat`;
- the source fundamental-matrix condition
  `‖N‖ * epsQ < 1`.

That is exactly the correct setting for measuring **real dynamical change**,
but a physically equivalent target may use different state labels.  Comparing
that target before gauge alignment would mix representation error with model
error.

## 2. Gauge-aligned representative

The theorem `p_goa_03_mod_state_gauge` therefore separates two layers.

First choose `Mhat`, a gauge-aligned representative of the physical target.
`M` and `Mhat` share P-GOA-03's fixed `T/R/C` bookkeeping, so the frozen theorem
measures only genuine perturbation.

Then let `Ptarget` be any finite stochastic kernel exactly conjugate to
`Mhat.P` through a state equivalence `e`:

\[
\widehat P(s,t)=P_{target}(e(s),e(t)).
\]

No compatibility between the concrete state labels of `Ptarget` and the frozen
`T/R/C` bookkeeping is required.

## 3. Frozen P-GOA-03 constants are preserved exactly

The lifted theorem reuses, unchanged, the frozen absorption bound

\[
\|\widehat H-H\|
\le
\frac{\|N\|^2\epsilon_Q+\|N\|\epsilon_R}
{1-\|N\|\epsilon_Q}.
\]

It also preserves the two aligned Cesaro-limit certificates supplied by
P-GOA-03.

No new perturbation constant is introduced for the gauge map.

## 4. Recurrent structure is transported to the physical target

For every recurrent class `c`, the theorem invokes the already checked exact
recurrent bridge to prove that:

1. the relabeled carrier `e '' A_c` is recurrent for `Ptarget`;
2. the relabeled class law `e_# pi_hat_c` is an invariant law supported on that
   carrier.

Thus the approximate theorem does not merely bound an abstract mixture.  It
connects the mixture components to actual recurrent structures of the physical
target kernel.

## 5. Gauge contributes zero TV penalty

Let

\[
\nu=\sum_c w_c\pi_c,
\qquad
\widehat\nu=\sum_c \widehat w_c\widehat\pi_c.
\]

The physical target mixture is

\[
\nu_{target}
=
\sum_c \widehat w_c\,e_\#\widehat\pi_c
=
e_\#\widehat\nu.
\]

Using finite-mixture relabel covariance plus TV invariance under equivalence,
the theorem proves

\[
\operatorname{TV}(e_\#\nu,\nu_{target})
=
\operatorname{TV}(\nu,\widehat\nu).
\]

Therefore the final P-GOA-03 radius remains exactly

\[
\frac12
\frac{\|N\|^2\epsilon_Q+\|N\|\epsilon_R}
{1-\|N\|\epsilon_Q}
+
\sum_c \widehat w_c\epsilon_{stat}(c).
\]

Pure label change adds **zero** physical error.

## 6. Class-law defect is itself gauge invariant

`classLaw_tv_relabel_both` proves

\[
\operatorname{TV}
(e_\#\pi_c,e_\#\widehat\pi_c)
=
\operatorname{TV}(\pi_c,\widehat\pi_c).
\]

Hence the classwise `epsStat` term is also semantic rather than representational.

## 7. Scientific interpretation

The recurrent GOA lane now distinguishes three objects cleanly:

1. **representation gauge** — exact state relabeling, zero error;
2. **recurrent structure** — closed communicating carriers and their invariant
   law families, transported exactly through gauge;
3. **physical perturbation** — changes in transient dynamics, recurrent-entry
   probabilities and class stationary laws, controlled quantitatively by
   P-GOA-03.

This yields the chain

\[
\boxed{
\text{aligned recurrent perturbation}
\xrightarrow{\text{P-GOA-03}}
\text{mixture TV bound}
\xrightarrow{\text{exact gauge}}
\text{same physical bound in target coordinates}.
}
\]

## 8. Boundaries retained

- P-GOA-03 still requires a gauge-aligned representative with the same
  transient type and recurrent partition.  This theorem does **not** claim that
  arbitrary small kernel perturbations preserve recurrent decomposition.
- Exact state gauge is free; decomposition change is not.
- The theorem does not yet construct the best/aligned representative
  automatically from two arbitrary decompositions.
- It does not weaken the frozen smallness condition `‖N‖ * epsQ < 1`.
- No frozen source theorem, counted generator, P-ID disposition, or ledger count
  changes.

## 9. Next pressure test

The next mathematical boundary is now explicit:

> characterize when two nearby finite kernels admit a common recurrent
> decomposition up to gauge, and when recurrent classes can split/merge under
> perturbation.

That is a qualitatively harder structural-stability problem.  It should not be
hidden inside P-GOA-03.  A safe next lane is therefore a **recurrent support
margin / graph-gap theorem**: positive transition margins and zero-pattern
separation should give sufficient conditions for eventual class-structure lock,
after which the gauge-lifted P-GOA-03 theorem applies automatically.
