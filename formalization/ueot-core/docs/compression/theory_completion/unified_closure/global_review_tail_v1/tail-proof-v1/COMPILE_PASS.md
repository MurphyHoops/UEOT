# Same-source infinite survival tail — actual focused PASS

Status: `PRIVATE_FOCUSED_PASS_NOT_PRODUCTION_INTEGRATED`; independent execution review is recorded separately.

## Result

The sole endpoint `killed_survival_mass_tendsto_homogeneous_neverHit_real` has actually compiled. It proves convergence of the original unnormalized killed safe-mass sequence `eta0 Q^n 1` to the real mass of `neverHitSet Kᶜ` under the same infinite trajectory built from the actual original `p0` and the same `M`, `q`, and stationary current-observation randomized `sigma`.

It applies existing continuity from above directly to that measure, uses the existing antitone/intersection event identities and finite-measure `toReal` continuity, then rewrites the finite sequence with the passed SafePrefix S3 theorem. No Dirac-mixture reconstruction, additional source-equality hypothesis, safe initial support, positive survival or nonempty-safe-set assumption occurs.

## Actual execution

- Attempt: `lean-attempt-001`; exit `0`; `8.895` seconds; no timeout.
- Final/original/attempt source SHA256: `fd56b62549a68bc06caf9542c84d43e388becff304901241fa8746693c919357`.
- Actual axiom output: `propext, Classical.choice, Quot.sound` only.
- One `letI` style warning is preserved in the actual log; it is not a proof failure and no repeat compilation was run to remove it.
- There were no Lean failures. A separate initial Python metadata-field lookup failure was retained in `preparation-001.log`; it occurred before Lean started and was repaired using the manifest's actual `dependencies` field.

## Declaration and evidence scope

The entire original source is byte-identical to the passed source. The one complete public declaration header was compared through its top-level `:=`, with nested named arguments excluded as delimiters. There are no new definitions, instances or options. See `DECLARATION_COMPARISON.json`; `SOURCE_DELTA.patch` is genuinely empty.

The runner rechecked all 666 production source files against the completed-build identity `29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`, the environment/toolchain files and runtime binaries, all 25 declared API/evidence inputs, and all four private source/olean pairs before the actual run. The actual Lake environment and import resolution are saved; private search roots resolve the expected frozen SafePrefix, G1–G3, K1 and source-bridge oleans. Existing completed-build dependency revision/clean-state evidence is reused without claiming a fresh Git scan.

Original contract, API inputs, initial status and draft are preserved in `v1-original/`; original pending fields are not rewritten. The static contract review is `../independent/TAIL_CONTRACT_REVIEW.json` with SHA256 `5214646b1f15618f166e35df9e111856c0ac3a91b507191c2da34382353b0218`.

This result retains time zero and initial failure mass, empty `K`, and zero survival. It does not prove positivity of infinite survival, a maximal fixed point characterization, QSD/Doob existence, or Markovization of arbitrary causal policies. No production, frozen Stage1–7, book, Git or remote files were changed; no whole-project build or native export was run.
