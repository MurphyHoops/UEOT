# `ueot-physics-unification` — Pure-Kernel Lean 4 Formalization of UEOT Physics Unification Gates

Toolchain: `leanprover/lean4:v4.33.1` (exact byte match to `formalization/ueot-core` and `formalization/ueot-qm`).  
Kernel audit: **15 modules, 239 constants, 159 theorems, 77 definitions, 0 `sorryAx`, 0 `Lean.ofReduceBool` (`native_decide`), 0 nonstandard axioms**.

This package extends formal machine-checked coverage across all non-`PR #468` sectors of the UEOT Physics responsibility matrix (`PREMISES_AND_RESPONSIBILITIES.md` & `CORE_PHYSICS_CONTRACT.md`) without modifying any historical file in `formalization/ueot-core` or `formalization/ueot-qm`.

## Modules and Main Theorems

| Module | Result IDs | Key Machine-Checked Theorems |
| :--- | :--- | :--- |
| `UEOTPhysicsUnification.RealQuotientSelection` | `C-QSEL-05` | `real_holonomic_gap_pos`, `hwTau_complex_eq_rhoPlus`, `single_copy_real_product_blind`, `two_copy_hwTau_witness_one`, `two_copy_real_separable_witness_zero`, `phaseQuotientEquiv`, `phase_invariant_observable_existsUnique_complex_descent` |
| `UEOTPhysicsUnification.CorrelatedBathIdentifiability` | `P-MICRO-10` | `exists_distinct_admissible_indistinguishable_ramsey`, `invert_signedInterventionTriple`, `signedInterventionTriple_injective`, `signed_phase_separates_witnesses`, `correlation_inverse_stability` |
| `UEOTPhysicsUnification.GaugeFlavorSelection` | `P-MATTER-02`, `P-FLAVOR-03` | `uv_331_complete_classification`, `multiscale_su3L_to_su2L_uniquely_selects_331`, `witten_doublet_count_always_even`, `abj_pion_diphoton_invariant`, `r_tau_unitarity_excludes_five_color`, `rank_one_wilson_closure` |
| `UEOTPhysicsUnification.ConformalControlGravityGates` | `P-UNIF-CTRL-01`, `P-UNIF-CHI-02`, `P-UNIF-CTP-03` | `conformal_xi_simultaneous_vanishing`, `pure_trilinear_unbounded_below`, `stabilized_control_exact_sos_decomposition`, `stabilized_control_nonneg_iff_mass_threshold`, `stabilized_control_global_lower_bound`, `covariant_stress_divergence_cancels`, `weyl_counterterm_cancels_all_harmonics` |
| `UEOTPhysicsUnification.RGBridgeAndEFTMatching` | `C-RG-01`, `P-EFT-02` | `markov_lumping_iff_fiberCompatible`, `markov_lumping_iterates`, `mori_zwanzig_memory_defect_exact`, `two_step_semigroup_failure`, `wilson_effective_action_is_fibre_minimum`, `eft_propagator_remainder_bounds`, `scheme_cancellation_identity` |
| `UEOTPhysicsUnification.ThermodynamicsAndLandauerBounds` | `P-THERMO-01`, `P-OMEGA-02` | `swap_energy_conservation`, `fresh_bath_iterated_contraction`, `persistent_vs_fresh_second_cycle_excess`, `persistent_excess_ch71_benchmark`, `bistochastic_purity_strict_decrease`, `participation_return_lower_bound` |
| `UEOTPhysicsUnification.SpacetimeEquivalenceAndGravityBounds` | `B-SIG-01`, `P-EP-02`, `P-GRAV-03`, `P-HORIZON-04` | `fisher_pullback_no_timelike_vector`, `null_cone_uniquely_determines_minkowski_conformal_class`, `soft_spin2_universal_coupling`, `reducible_kinematics_nonuniversal_counterexample`, `starobinsky_ppn_unscreened_vs_screened`, `page_unitarity_thermal_deficit_pos` |
| `UEOTPhysicsUnification.TopologicalCarrierAndIndex` | `P-TOPO-01` | `torus_cocycle_flux_quantized_iff`, `chiral_partner_eigenvalue`, `graded_supertrace_index_invariant`, `periodic_torus_zero_mode_iff`, `antiperiodic_torus_strict_spectral_gap` |
| `UEOTPhysicsUnification.FlavorCyclicAndSPAMContract` | `P-FLAVOR-04`, `P-SPAM-05` | `cyclicJ_quark_rephasing_invariant`, `rank_one_cyclicJ_real_nonneg`, `two_channel_bd_bs_always_realizable`, `uncalibrated_visibility_contrast_degeneracy`, `spam_leakage_affine_exact_recovery`, `spam_leakage_estimator_lipschitz` |
| `UEOTPhysicsUnification.QuantumSuperselectionAndBorn` | `C-QSEL-06`, `P-QBORN-03` | `continuous_path_cannot_bridge_superselection_sectors`, `discrete_swap_bridges_superselection_sectors`, `mermin_peres_no_noncontextual_valuation`, `mermin_peres_classical_bound_four`, `envariance_equal_weights_uniform` |
| `UEOTPhysicsUnification.CorrelatedGaussianTailAndGalerkin` | `P-MICRO-06B`, `P-MICRO-11` | `galerkin_telescoping_defect`, `bose_geometric_partial_sum`, `two_mode_box_leakage_le_sum`, `correlated_two_mode_fock_tail_bound` |
| `UEOTPhysicsUnification.SymplecticSpinStatisticsAndQED` | `P-QCCR-04`, `P-SPIN-01`, `P-QED-02` | `sp2_preserves_covariance_det`, `robertson_schrodinger_heisenberg_chain`, `two_particle_exchange_dim_split`, `pauli_exclusion_diagonal_zero`, `bosonic_equal_time_commutator_cancels`, `wrong_statistics_anticommutator_coincident_pos` |
| `UEOTPhysicsUnification.ElectroweakCustodialAndSeesaw` | `P-EW-01`, `P-QFLAV-02`, `P-QNU-02` | `photon_zero_mode_and_z_eigenmode`, `custodial_rho_tree_level_one`, `higgs_triplet_breaks_custodial_rho`, `dirac_cp_phases_pos_iff_three_generations`, `type_one_seesaw_exact_roots_and_bound` |
| `UEOTPhysicsUnification.SpacetimeDimensionAndEarlyLateCosmology` | `B-CAUS-01`, `S-DIM-03`, `P-QG-15`, `P-GRAV-FM-05` | `strict_monotone_forces_causal_antisymmetry`, `periodic_three_cycle_not_antisymmetric`, `spacetime_dim_four_unique_from_gravitons_and_orbits`, `yang_mills_and_conformal_sixth_select_dim_four`, `pure_gravity_loop_divergence_grows`, `fischer_marsden_s3_kernel_iff_ell_one`, `matter_response_lifts_ell_one_obstruction` |
| `UEOTPhysicsUnification.ActionSelectionAndAttractorRates` | `P-PIPHI-01`, `P-GOA-02` | `posthoc_quadratic_objective_tautological`, `ostrogradsky_hamiltonian_unbounded_below`, `reducible_sector_stationary_continuum`, `doeblin_contraction_iterated_rate` |

## Local Build & Exhaustive Kernel Audit

```sh
cd formalization/ueot-physics-unification
python3 scripts/check_dependencies.py
python3 scripts/check_no_escapes.py
lake build UEOTPhysicsUnification
lake env lean scripts/ExhaustiveAxiomAudit.lean
```
