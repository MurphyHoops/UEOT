# B → C: review of the joint calibration and nominal predictor certificate

Reviewer: native research role B. Date: 2026-11-12 UTC. This is an internal AI review, not external human peer review. The reviewed research entry is `cb17211653fde30aa50e0e9848798a6a5b3b3f12`, physics v31.12 / Kernel 1.12 / book 3.9. The increment under review is P-ROB-04 and the P-ROB-05 interface in Chapter 69.

## Verdict and scope

**PASS on the declared ideal model, fixed-sample design and complete-output contract.** I found no remaining blocking mathematical or statistical issue in the final C draft. I attacked its two strongest claims: that observed calibration can select one nominal finite predictor uniformly over a jointly valid parameter set, and that its error/holdout/cost conclusions refer to the same source and allowed observations. Both now retain their needed qualifications.

The certificate is conditional on the specified complex Fock model, common physical pulse, ideal filter/preparation/readout, input mean bound and fresh fixed-parameter calibration trials. It neither establishes hardware membership nor infers universal CQ trace distance from the limited holdout testers. No new Lean proof or real measurement is asserted.

## Attack 1: hidden true parameter, coverage after admission, and nuisance identifiability

The original source flags have scalar unitary branch effects. All seven word probabilities are therefore independent of x. The new signed calibration genuinely adds a different permitted observation: prepare the sigma-x positive probe and oscillator vacuum, apply the same force pulse, and measure the binary momentum half-axis. The coherent displacement is `-i x`, the momentum mean is `-sqrt(2) x`, its variance is `1/2`, and the event `P<=0` has probability `Phi(2 x)`. This sign and normalization agree with the microscopic Hamiltonian.

The analyzer receives only the six declared record streams and the frozen plan. It does not import the generator or open its truth/provenance file. Its actual observed values are `qhat=2503/5000`, `phat=547267/1000000`, and the deterministic grid rule returns `xhat=2969/50000`. The returned `Delta_x` uses the full outward inverse endpoints and the actual rounded nominal value. The same fixed legal Q policy is deployed for every theta in the admitted set; no hidden-parameter weight selection has replaced the required quantifiers.

The rational inverse construction has been read directly. Its Gaussian integral uses a monotone alternating remainder in the declared interval, the prefactor is enclosed using a rational pi interval and integer square roots, and bisection returns outward endpoints. The earlier fallback-width issue was corrected: the adjacent fallback points are now `m±width/2`, and the analyzer consumes the frozen `inverse_bracket_width` field. Failure to enclose a probability returns no certificate. The computational inverse bracket is not silently treated as a physical prior. The full data-derived set must lie inside the design; it is not trimmed to make the bound pass.

The failure-frequency radius is 0.005, because q is twice that frequency. With 120000 such trials, the two-sided failure bound is `2 exp(-6)`. The drive frequency radius 0.002 with 1000000 trials gives `2 exp(-8)`. Their sum bounds joint failure without requiring independence between the two confidence events. Independence within each fixed-size trial stream remains a substantive premise.

I specifically challenged selection after admission. The final text correctly states

`Pr(true theta outside C) <= alpha`

and

`Pr(certificate emitted and invalid because calibration missed theta) <= alpha`,

with `alpha=2 exp(-6)+2 exp(-8)<0.01`. It does not claim 99% conditional coverage given admission. Repeated sampling until admission and optional stopping are excluded from this fixed-sample guarantee.

The nuisance counterexample has the correct sign and access scope. With observed momentum equal to physical momentum plus b, one dose gives `Phi(2x-sqrt(2)b)`, invariant under `(x,b)->(x+c,b+sqrt(2)c)`. Two doses with the same fixed b give a second inverse argument `4x-sqrt(2)b`; together the settings identify fixed x and b. Arbitrary setting-dependent biases retain a different nonidentifiability symmetry. The final draft distinguishes all three claims and keeps the second-dose data held out from the present b=0 calibration fit.

**Result:** the paper argument and the finite arithmetic certificate support a data-selected nominal model under the declared calibration model. They do not establish the calibration model itself.

## Attack 2: complete-CQ triangle, actual Galerkin error, tester scope and costs

The nominal bridge uses the correct comparison order:

`actual infinite C(x) -> nominal infinite C(xhat) -> genuine Galerkin C_K(xhat)`.

For the first comparison, `X=a+a†` obeys the positive-form inequality `X²<=4n+2`. Exact force propagators and spin-only phase gates strongly preserve the X spectral measure. Finite mean n places a purification in D(X), the quadratic-form domain of positive X²; D(X²) is not needed. Every exact nominal prefix therefore retains the same X² budget. The Q average number of force calls is exactly one, which produces `sqrt(6) Delta_x` on the E<=1 passing state.

This reasoning is deliberately not applied to finite Galerkin prefixes. A's K=1 counterexample shows that compression need not preserve X². The final text keeps that counterexample and does not hide it inside a finite-model assumption.

For the second comparison, the B/A finite Duhamel theorem controls the actual compressed generator. It is not a projected-state tail estimate or a matrix-exponential solver residual. The Q-weighted error is

`(624/1250) d_4095,40(|xhat|) + (313/1250) d_4095,40(2|xhat|)`.

The complete physical filtering term retains `prep_fail`, system vacuum reset, and the actual failure-conditioned reference marginal. The accepted source effect is derived as `s² I`, so its normalized target is CPTP and preparation error contracts without an omitted posterior factor. The robust record-law term remains the inherited full-design `1/50`; it is not redescribed as a new minimax result on a narrower calibration interval. All four terms belong to the same full CQ output.

Independent B arithmetic reproduced the final sufficient upper-bound formula below `0.0419301587941104`. The independent calculation is an enclosure of a proved upper-bound formula, not a lower bound on the actual error. The wider-calibration control correctly returns insufficient precision rather than physical impossibility.

C's numerical `1e-8` reserve is explicitly conditional. The uniform mathematical certificate concerns every input in the specified energy/reference domain; a separately returned finite numerical state can have narrower, specified-input coverage. Root's later outward-integer prediction and B's analytic displacement diagnostic are distinct evidence, not a reason to enlarge C's claimed numerical scope.

The holdout forecast uses `Phi(4x)` at the genuinely different two-dose setting and only the one-dose calibration set. It keeps the same prediction interval and threshold for the ordinary synthetic holdout and the prespecified nonshared-pulse control. The counts 29878/50000 and 32050/50000 respectively give nonrejection and rejection. These checks measure the declared 15 probability cells, not arbitrary terminal quantum states. The final false-rejection allowance includes both calibration failure and the holdout sampling-family bound. Nonrejection is not described as mechanism identification or empirical validation.

The original-source success denominator is `s_N s(q)^2`; it includes physical filter failure. The compiler denominator is `s_N` in the ideal implementation. Retry formulas are conditioned on genuine fresh reset and resupply, with no free repeat of an unknown entangled input. One-time calibration is amortized across delivered outputs. The expected visible force-label count equals executed physical force count only for the stated flag-first schedule; coherent control may schedule every slot. No time/energy/money advantage has been measured or certified.

**Result:** the same-source and same-metric chain is valid on the declared domain. General detector error, nonideal gate error, hidden memory, unbounded stopping, real costs and device membership remain separate responsibilities.

## Actual review evidence and immutable identities

`B_C_CALIBRATION_AUDIT.json` records the 17 previously executed independent B checks of counts, hashes, rational radical enclosures, total arithmetic and held-out decisions. Its four consumed source hashes still match the final C files below, so those checks were reused rather than relabelled as a new execution. Its inverse/holdout transcendental evaluations are explicitly high-precision diagnostics; C's independent rational checker supplies the separate finite interval checks.

The final C checker receipt reports 112 checks passed. This inventory is not a percentage of physical theory completion. The final C paper and source identities reviewed here are:

| File | SHA-256 |
| --- | --- |
| C_CALIBRATION_AND_CERTIFICATE.md | c4a1c185f47c9b612dde84e52a73ad33240a581b1a99c5872e8d7ebaf0967d2c |
| FROZEN_CERTIFICATE_PLAN.json | a27a61ea157d9ae958213a5377d3a93295022a8a9d28f68d022f86f9fa269108 |
| certified_intervals.py | 8833a6192298eb3d91ada7f5b57471c424613b0cb0a9cd7d62828b34ffa59d5b |
| certify_from_records.py | 6ba96a6150e63ba0834aaa41f47dee1f661deab11cbe8fa5fdab882a9db25753 |
| generate_synthetic.py | db3abaea47ecd42ed545cd7ef7b1f48eb5407a289b140e64aa69a8516798db31 |
| independent_certificate_check.py | f8f430434dbed0dcd1c0912c2902c0c9cd103e49fceef69231d5f8ed31d67d06 |
| C_INDEPENDENT_CERTIFICATE_CHECK.json | 5f1687bb029b52ad06aba984778f80b888623787b1e7619a88ba47b18c7557d4 |
| C_CALIBRATION_CERTIFICATE.json | 67bb7cfd9ccc35a80d6ac6dc128e4b16c22997860d102fb9cb9ff0bc431fc5ab |

The files are in the isolated `iteration_v31_13/research_c` directory. Public copies and root/CI executions must retain their own actual execution and checkout identities. This review does not authorize relabelling one receipt as another.
