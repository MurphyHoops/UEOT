# Canonical source audit evidence — 2026-09-13

This record separates **source-theorem verification** from **public-repository artifact reproducibility**.

## Canonical source identity

- canonical file: `UEOT_Core_Mathematics_v3.0_Complete.md`
- frozen manifest SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- canonical source object was re-opened from the project File Library during the 2026-09-13 audit
- exact source bytes are still **not** present in the public GitHub repository
- the SHA-256 above was **not recomputed from local bytes in this audit session**, because the exact File Library object is not mounted into the repository/runtime filesystem

Therefore this audit proves source-statement semantic matching against the canonical source object, while public byte-level reproducibility remains a separate pending repository task. No regenerated substitute is accepted as the canonical source.

## P-INFO-02 audit

Canonical source statement:

- standard Borel variables `H,Y,M,U`;
- `M,U` are functions of history;
- `ε = I(H;Y | M,U)`;
- conclusion
  `E TV(P(Y|H), P(Y|M,U)) <= sqrt(ε/2)`.

Canonical Lean theorem:

`UEOT.V3.InformationPInfo02.p_info_02_ennreal`

Audit result:

- deterministic history statistics are represented by measurable `fM : H -> M` and `fU : H -> U` and paired as `(M,U)`;
- the left side is the expectation of TV between the true history predictive kernel and the `(M,U)` statistic predictive kernel;
- the right side is the all-cases ENNReal form of `sqrt(I(H;Y|M,U)/2)`;
- the infinite-information case is handled explicitly, so no source-level finiteness assumption is added;
- `[Nonempty Y]` is a Mathlib `condKernel` elaboration requirement implied by existence of a probability law on `H × Y`, not an added physical assumption.

Promotion evidence already on `main`:

- PR #46;
- main commit `c1d0d94b7d01a5d6f370d2de4f40e8c1674bcd8f`;
- post-main CI `34692828935`: success.

**Conclusion:** P-INFO-02 is source-theorem proved. Public canonical-source byte synchronization remains pending only as a reproducibility task.

## P-INFO-04 audit

The frozen P-ID contains two clauses.

### Multiway Fano clause

Canonical source statement:

- `J` is uniform over `K >= 2` identities;
- a measurable decoder from future record `Y_T` has error rate `e`;
- conclusion
  `I(J;Y_T) >= log K - h2(e) - e log(K-1)`.

Canonical Lean theorem:

`UEOT.V3.InformationPInfo04.p_info_04`

Audit result:

- the first marginal is constrained to the uniform `Fin K` law;
- the theorem accepts an arbitrary measurable decoder;
- the decoder error is exactly the complement of the correct-decoding event;
- the conclusion is the ENNReal embedding of the exact frozen lower bound;
- the proof uses KL data processing to the correctness event and exact Bernoulli KL, not a MAP substitution.

Promotion evidence:

- PR #47;
- main commit `94e16dfb9cc9a2db6e000d8f5394c1b07869ce40`;
- post-main CI `34693509298`: success.

### Conditional binary clause

Canonical source statement:

- `B in {0,1}` is decoded from `(M,U)`;
- decoder error is at most `epsilon <= 1/2`;
- conclusion
  `I(M;B|U) >= H(B|U) - h2(epsilon)`.

Canonical Lean theorem:

`UEOT.V3.InformationConditionalBinaryMutualEntropy.p_info_04_conditional_binary`

Audit result:

- the theorem uses the true law on `U × (M × Fin 2)` and a measurable decoder `(U,M) -> Fin 2`;
- the hypothesis is the actual decoder error `<= epsilon` with `epsilon <= 1/2`;
- conditional mutual information is defined as one global KL against the true `U` marginal and fiberwise conditional-independence reference;
- finite CMI is bridged to `H(B|U)-H(B|M,U)` by a separately machine-checked theorem;
- the `CMI = top` case is handled separately, so no finite-CMI assumption is added to the source theorem;
- `[Nonempty M]` is a Mathlib disintegration elaboration requirement implied by existence of the source probability law, not an additional source axiom.

Promotion evidence:

- compose CI `34705230951`: success;
- clean commit `8c76777e78e8d7f73b0d71397f8c81aeaa6e9c54`;
- clean CI `34705560077`: success;
- PR #51 CI `34706303512`: success;
- main merge `e19eee7082418f1826650316b533c0380a9a451f`;
- post-main CI `34706528781`: success.

**Conclusion:** both frozen clauses are source-theorem proved; therefore P-INFO-04 is proved. Public canonical-source byte synchronization remains pending only as a reproducibility task.

## Governance rule clarified by this audit

A P-ID may be counted `proved` when all of the following hold:

1. its statement has been audited directly against the canonical frozen source object;
2. its source-faithful Lean theorem is reachable from the official graph;
3. the relevant full-target feature/clean/PR gates have passed;
4. the theorem is integrated on `main` with green post-main `lake build UEOT`;
5. no prohibited placeholder proof or new unsourced axiom is used;
6. the coverage ledger is synchronized.

Separately, `public_source_artifact_synced` records whether exact canonical source bytes are present in the public repository and can be independently hashed there. This is a reproducibility/property-of-packaging gate and must not be conflated with mathematical/source-theorem proof status.
