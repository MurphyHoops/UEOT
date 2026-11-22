# `ueot-physics-unification` — Pure-Kernel Lean 4 Formalization of UEOT Physics Unification Gates

Toolchain: `leanprover/lean4:v4.33.1` (exact byte match to `formalization/ueot-core` and `formalization/ueot-qm`).  
Kernel audit: **4 modules, 109 constants, 71 theorems, 0 `sorryAx`, 0 `Lean.ofReduceBool` (`native_decide`), 0 nonstandard axioms**.

This package extends formal machine-checked coverage beyond the frozen `v31.11` QM proof inventory without modifying any historical file in `formalization/ueot-core` or `formalization/ueot-qm`.

## Modules and Main Theorems

| Module | Result IDs | Key Machine-Checked Theorems |
| :--- | :--- | :--- |
| `UEOTPhysicsUnification.RealQuotientSelection` | `C-QSEL-05` | `real_holonomic_gap_pos`, `hwTau_complex_eq_rhoPlus`, `single_copy_real_product_blind`, `two_copy_hwTau_witness_one`, `two_copy_real_separable_witness_zero`, `phaseQuotientEquiv`, `phase_invariant_observable_existsUnique_complex_descent` (direct bridge to `UEOT.V3.Compression.QuotientDescent.existsUnique_descend`) |
| `UEOTPhysicsUnification.CorrelatedBathIdentifiability` | `P-MICRO-10` | `exists_distinct_admissible_indistinguishable_ramsey`, `invert_signedInterventionTriple`, `signedInterventionTriple_injective`, `signed_phase_separates_witnesses`, `correlation_inverse_stability` |
| `UEOTPhysicsUnification.GaugeFlavorSelection` | `P-MATTER-02`, `P-FLAVOR-03` | `uv_331_complete_classification`, `multiscale_su3L_to_su2L_uniquely_selects_331`, `witten_doublet_count_always_even`, `abj_pion_diphoton_invariant`, `r_tau_unitarity_excludes_five_color`, `rank_one_cyclic_real_nonneg`, `rank_one_wilson_closure` |
| `UEOTPhysicsUnification.ConformalControlGravityGates` | `P-UNIF-CTRL-01`, `P-UNIF-CHI-02`, `P-UNIF-CTP-03` | `conformal_xi_simultaneous_vanishing`, `pure_trilinear_unbounded_below`, `stabilized_control_exact_sos_decomposition`, `stabilized_control_nonneg_iff_mass_threshold`, `stabilized_control_global_lower_bound`, `covariant_stress_divergence_cancels`, `weyl_counterterm_cancels_all_harmonics` |

## Local Build & Exhaustive Kernel Audit

```sh
cd formalization/ueot-physics-unification
python3 scripts/check_dependencies.py
lake build UEOTPhysicsUnification
lake env lean scripts/ExhaustiveAxiomAudit.lean
```
