# B — bilingual Chapter 68 scientific review

Reviewer: native research subagent B. Date: 2026-11-12 (Asia/Shanghai).

Scope: the newly reconstructed `recovery_reviews/root/ch68.zh.md` and `ch68.en.md`, with the independent B/C proofs and the already executed exact certificate as comparison sources. This review does not rerun previously verified code and does not validate hardware data.

## Scientific findings

The Chinese and English chapters agree on the microscopic gate order `V1=B_beta U1`, the actual blue blocks, the graph-domain self-adjoint realization, derived two-excitation support growth, rectangular source restrictions, complete terminal-record embedding, no-blue reference-prefix omission proof, filtering failure reference state, and same-source conditional target. The manuscript does not silently replace segmented dynamics by simultaneous evolution, and it does not introduce an unproved finite-dimensional Hamiltonian compression as the source model.

The exact numerical formula is correct:

`1/50+(1+sqrt(16381))/8192+sqrt(2)/100`.

The printed rational upper endpoint `4988777535926672699/10^20` matches the actual previously executed C-checker output consumed by B. The conservative displayed decimal upper bound is strictly larger than that endpoint and remains below 0.05. The approximately `0.000112224640733273` remaining allowance is not presented as measured apparatus precision. The loose-bound failure and independent beta premise remain visible.

The Rabi counterexample is valid when the exponent denotes the canonical self-adjoint quadrature realization of the finite-Fock-core expression. The finite-support input `|+_x,0>` yields a coherent state with nonzero number probabilities at all levels for nonzero pulse area. This disproves hard finite-support extrapolation only, and the text correctly retains controlled simultaneous-dynamics approximations as a future responsibility.

The standard physical-source citation is correctly identified as Wineland et al., *Quantum information processing with trapped ions*, Phil. Trans. R. Soc. Lond. A 361 (2003), DOI `10.1098/rsta.2003.1205`, pp.1350–1351. The [NIST original PDF](https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=105685) was independently read during B's research: those pages state the interaction-picture, Lamb–Dicke and rotating-wave assumptions, red/blue operators and number-state square-root couplings. The chapter attributes those physical ingredients to standard work and correctly refuses to infer validity over the large analytic cutoff from a small average energy.

Both versions explicitly separate analytic proof, finite exact/numerical evidence, inherited Lean scope, and the absence of new device data. New results do not overwrite old execution identities. The continued long-term responsibilities are preserved.

## Precision corrections requested before final freeze

1. **Define the quantified finite carrier comparison before using it.** In section 68.3, set `L` to the fixed maximum number of operation slots, each containing at most one blue pulse. State `Tr(G rho_S)<=nbar<N+1`, define the positive projection success probability, and give the finite-coordinate formula for `rho_N`. This avoids conflating the tighter branchwise count of blue pulses with the uniform construction that enlarges the declared carrier by two at every operation slot. All actual two-step formulas are already consistent.

2. **Name the resolvents.** In section 68.2, replace the unspecified “two nonreal shifts” by `B+iI` and `B−iI`. The stated norm bound one is then exact. It would not hold for every nonreal shift with arbitrarily small imaginary part.

3. **Use the quadratic-form quantity explicitly.** In section 68.5, change the display's `beta² <psi,B² psi>` to `beta² ||B psi||²`, or explicitly declare the expression to be a quadratic form. Finite mean G ensures the vector is in `D(B)`; it does not generally put it in the operator domain `D(B²)`. The proof already uses the correct weaker condition.

4. **Specify the simultaneous self-adjoint realization and units.** In section 68.6, take `X` to be the canonical self-adjoint closure of `a+a†` on the finite Fock core, and define `H_sim=sigma_x tensor X`. Its domain in the sigma-x basis is `D(X) direct-sum D(X)`. Use `exp(−it H_sim)` and say that `t` is the dimensionless simultaneous pulse area. The original `A+B` identity remains an identity on the finite Fock core; this wording does not infer self-adjointness from an arbitrary unbounded sum. In Chinese, “位置象限算符” should read “位置正交分量算符”.

Suggested concise bilingual wording for correction 4:

> 在有限 Fock 核上有下列红蓝生成元恒等式。令 X 为该核上 a+a† 的规范自伴闭包，取 H_sim=σ_x⊗X，其定义域在 σ_x 本征基下为 D(X)⊕D(X)。以下 t 表示无量纲同时脉冲面积。

> The red-plus-blue identity below holds on the finite Fock core. Let X be the canonical self-adjoint closure of a+a† on that core and set H_sim=σ_x⊗X, with domain D(X)⊕D(X) in the sigma-x basis. Here t denotes the dimensionless simultaneous pulse area.

These are notation and quantified-domain corrections, not changes to the derived scientific result or to the executed numerical certificate.

## Bilingual consistency and disposition

At the first review read, both chapter drafts contained **nine** displayed-equation groups, and the groups matched literally. This is the present reconstructed draft; an old interrupted-process count of ten is not substituted for this observation. Both versions contained the same six new stable result labels.

Initial scientific disposition was PASS subject to the four precision edits above. They were subsequently applied and narrowly reread as recorded below.

## Final readback and accepted scope

The current Chinese and English bytes were reread after root's corrections. All four requested changes are present: `L` is now maximum operation-slot count with at most one blue pulse in each slot; the input energy domain and finite-coordinate `rho_N` are explicit; the shifted resolvents are `B±iI`; and the local norm display uses `||B psi||²`, with text stating membership in `D(B tensor I)` rather than requiring `D(B²)`. The simultaneous counterexample explicitly selects the canonical self-adjoint quadrature realization and `D(X) direct-sum D(X)`, calls `t` dimensionless pulse area, and uses `exp(−it H_sim)`. The Chinese quadrature terminology is corrected.

The final text also handles zero-mass prefixes without normalizing them and distinguishes the N=1 finite witness, its G<=5 final carrier, and the separate filtering stress control (input support G<=2, filter N=1, common output G<=6, deliberately chosen tail mass 1/4096) from the analytic N=4095 certificate. These clarifications agree with the inspected runtime. Both languages still have nine literally identical display-math groups and the same six result identifiers.

**Final scientific disposition: PASS for the current manuscript bytes and the declared analytic model. No outstanding correction from B remains.** No already accepted computation was rerun during this narrow readback. The completed result remains a finite-height segmented-model closure and a conditional omission certificate; the empirical axis remains unverified.

## Checker authorship versus execution identity

B also inspected root's integration of `independent_growth_check.py` as `physics/qm/growing_cutoff/check_micro_growth.py`. The complete source diff changes only the fixed `actor` metadata into `checker_author: native research subagent B` and a statement that actual execution/workflow identity comes from the invoking runner. The mathematics, checks, parameters, algorithm and numerical acceptance predicates are unchanged. The common `run_verification.py` separately records its actual provider (local Python or GitHub Actions), checkout, dirty-worktree status, workflow metadata when available, command times, input hashes, output hashes and logs.

The original B script and original B receipt in `audits/GROWING_CUTOFF_v31.12/reviewer_originals/b/` are byte-identical to B's retained originals. The original receipt's source hash still matches that archived original script. Thus the original actual B execution remains independently attributable, while later executions of the integrated checker do not falsely claim that B personally executed them. This is an appropriate provenance-only change. The new integrated script must be identified by its own changed source hash when run; the old B receipt does not certify execution of that later byte sequence.
