# Real local tomography: independent read-only source review

Reviewer: `/root/q316_classical_core`.

Reviewed source: `formalization/ueot-qm/UEOTQM/RealLocalTomography.lean`.
SHA256: `76dfea1aa3ad7f16e699a8529bde5f22120badac9a1db60f0265eaef4eeddc9e`.

Disposition: **no mathematical or scope blocker found**. This is a source and interface audit; the author and root own compilation and axiom evidence.

1. The source uses the actual existing `Density`, `Effect`, trace pairing and matrix Kronecker product. `Effects.lean` was also read to confirm `Effect.probability` is the existing Born pairing and both effect order bounds are actual PSD fields.
2. Both states are normalized positive densities, explicitly real, with matrices `(I ± Y ⊗ Y) / 4`. Positivity follows from the independently derived positive projectors of a Hermitian involution, not from assuming the desired separation.
3. `trace_mul_pauliY_zero` quantifies every real Hermitian local operator. The factorized trace identity therefore gives indistinguishability for **all** real product effects, rather than a finite sampled family or a diagonal-only subfamily.
4. `productEffect` proves both PSD bounds of the actual tensor product. Its complement decomposition `(I-E) ⊗ I + E ⊗ (I-F)` is valid without a commutativity assumption between unrelated local operators.
5. The joint effect is genuinely real and produces probabilities 1 and 0. State distinctness follows from this actual separating effect, independently of any visual matrix comparison.
6. The deletion control removes the local-reality restriction, supplies a provably non-real local effect, and computes distinct product responses 1/2 and 0 on the same two states. It is correctly limited to this pair, rather than claiming general complex reconstruction.
7. The source explicitly treats reality, local effect restriction, and composite rule as model inputs. It does not claim a complete real operational probabilistic theory, real-sector purification, empirical selection, or an unconditional UEOT derivation of complex QM.

No reviewed source was edited. A future change to declarations or source identity requires rebinding this review.
