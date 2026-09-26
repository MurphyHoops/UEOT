# CrooksJarzynskiLean provenance

This vendored subset comes from:

- upstream repository: `https://github.com/kiyo-e/CrooksJarzynskiLean.git`
- upstream commit: `b415db75eb8189544a90adb55009441d35ab5c04`
- upstream license: Apache License 2.0 (`LICENSE` in this directory is byte-identical to the upstream file at that commit)

UEOT Core v3 vendors only the finite-jump continuous-time path-law infrastructure needed for P-KL-04.

All vendored Lean files retain the upstream copyright/author header and carry a UEOT modification notice.  Most files differ from upstream only by module import paths.  Two files have additional, explicitly documented changes:

- `ContinuousTimeJumpFiniteGenerator.lean`: omits the standalone upstream `ThreeStateBranching` example namespace; the general finite-generator definitions and theorem statements used by UEOT are unchanged.
- `ContinuousTimeJumpHorizon.lean`: adapts the proof body of `map_horizonMeasure_reverse` to the pinned Mathlib API; the theorem statement and surrounding path-space definitions are unchanged.

No upstream Crooks/Jarzynski detailed-balance KL theorem is used as a proof of UEOT P-KL-04.  The UEOT theorem constructs its own controlled-vs-baseline likelihood and Campbell/renewal argument on top of the vendored finite-jump path-law infrastructure.
