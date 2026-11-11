# A → B independent internal review

Reviewer: native research agent A. This is internal AI review, not external human peer review.
Reviewed draft: `research_b/MICRO_TRUNCATION_BRIDGE.md`.
Reviewed SHA256: `69cf8100f0ca09b5fef9a62779beb0420607bff46b4a8cd43bea92487c0877fc`.

## Strong-claim attack 1: microscopic conservation versus branch preservation

The claim is valid under the stated strong spectral commutation, nonnegative auxiliary excitation, fresh auxiliary supported in its zero eigenspace, and complete auxiliary-only readout. Formal commutator equality alone would not suffice for unbounded operators; B explicitly avoids it. Initial S:R entanglement is allowed because each operator acts as identity on R. Reused or correlated auxiliaries are correctly excluded unless included in the enlarged system.

The initial draft's description of the readout as contractions/sums was not fully explicit. I requested the physical Kraus formula with both hidden indices and completeness. The final draft now states K_{oℓb}=(I⊗<b|)(I⊗M_{oℓ})W(I⊗|0>) and Σ_{o,ℓ} M†M=I. Nonnegativity of the auxiliary excitation ensures the joint low-excitation subspace lies in Π_N H_S⊗H_A; each auxiliary contraction therefore preserves the system cutoff. Summing o,ℓ,b proves instrument completeness. This fixes the interface rather than assuming it as a certificate field.

**Disposition:** passed after correction. The average-energy-preserving three-level channel is a valid necessary-premise counterexample, including full operator equality of mean energy while one branch escapes Π_1.

## Strong-claim attack 2: uniform complete-output error and physical preparation

The theorem preserves all finite-tree terminal records and quantum outputs, including a finite untouched reference. K V_N=V_N K_N follows from the proved branch support statement. This implies completeness of the restricted instrument and branch/path intertwining. The full bounded protocol is CPTP, so one initial normalized projection error contracts once; no per-step tail penalty is needed in this invariant-cutoff domain. The joint input/reference may be correlated.

I requested a clarification that a label named leakage is covered only when its actual Kraus still obey the cutoff-preservation hypothesis. The final draft explicitly excludes excitation leakage from this theorem and leaves separate defect budgets open. I also checked the physical filter calculation: normalized projection distance sqrt(δ) cannot alone bound the complete pass/fail output. The displayed 2×2 Hermitian pass-block calculation gives b(δ)=[sqrt(δ(4−3δ))+δ]/2, with δ=0 now handled explicitly. A common alphabet must retain `prep_fail` or a pass/fail prefix. A perfect spectral filter remains an extra physical operation assumption; B explicitly identifies it.

The normal trace-class sharp postselection proof is valid: completing the same CP TNI extractor by an orthogonal scalar failure block produces ||A−B||_1+|p−q|≤2ε, from which both bounds follow. This is paper coverage only, with the earlier finite Lean result preserved as finite.

**Disposition:** passed after corrections. Infinite references, coherent controllers, unbounded stopping and approximation-limit exchanges remain outside the declared coverage.

## Added B2 result and boundary

I independently recomputed R_0^T R_0=R_1^T R_1=I, M_0², and all three leading principal minors of (9/10)²I−(M_0²)^T M_0² using exact SymPy arithmetic. The values match 4941/12500, 422733249/3906250000 and 29552508909/390625000000. The perturbation estimate 4|q−1/2| yields the stated uniform two-step factor49/50. The Bloch-vector proof establishes unique stationary state and mixing only for the discarded-record reduced system in the exact one-excitation sector.

The stronger full-record forgetting claim is correctly rejected: Ω_n is a flagged random-unitary channel with input-independent weights, so each block preserves trace distance and their weights sum to one. Controlled inversion also shows recoverability. This identity holds with a retained reference, while the marginal mixing coefficient has not been claimed in that stronger joint norm. Whole-oscillator invariant sector weights and zero raw infinite-survival probability are retained.

**Final review outcome:** no remaining mathematical blocker found within the explicitly declared paper domain. This review does not certify device accuracy, external data, or unexecuted machine proofs.
