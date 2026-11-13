# Shared simultaneous-dynamics contract

Research entry: `cb17211653fde30aa50e0e9848798a6a5b3b3f12`, v31.12 / Kernel 1.12, book 3.9. Exactly three native A/B/C research roles were resumed. Core, formalized QM dependencies and physics interfaces are read-only. This increment does not reopen the established finite-conditioning chain or the separated-pulse growth theorem.

## Physical and operational objects

The system is the selected complex qubit–Fock model with `G=n+P_e`; a finite reference is untouched and may be initially entangled. Action durations are nonnegative; coupling coefficients and signed pulse areas may have either sign. The primary slot is the simultaneous force `V1(x)=exp[-i x sigma_x(a+a_dagger)]`, not the previous product of separated red and blue exponentials. `V0=exp[-i(pi/3)P_e]`. The real parameter `x` is a dimensionless pulse area; external driving supplies energy. Standard complex states, tensor products, Born readout, CP instruments and this effective control model are independent physical inputs (P/E), not consequences of Core selection.

The original source has `K0=sqrt(s(1-q))V0`, `K1=sqrt(sq)V1`, `Kf=sqrt(1-s)I`, with `s=1-q/2`. Two slots stop on the visible failure label. All seven terminal records `f,0f,1f,00,01,10,11` and their terminal system/reference states are retained. The accepted words are the last four. The acceptance effect must be computed from these events; it is not a certificate input. The established visible-history policy has path weights `Q00=Q11=313/1250`, `Q01=Q10=312/1250`. It never reads the unknown true parameter.

Physical preparation uses the low spectral projector `P_N`, N=4095, on an input with mean G at most one. Failure receives a separate `prep_fail` label, resets only the system to vacuum, and retains `Tr_S[(I-P_N)rho(I-P_N)]` on the reference. It does not replace that reference by an unrelated unconditional state. Unknown inputs cannot be freely repeated.

## Four distinct comparisons

1. `T_infinity(q,x)` is the normalized accepted source target on the unfiltered input. Derivation of its scalar acceptance effect makes this map CPTP in this model.
2. `C_infinity(x)` is the physically permitted visible-history compiler, including the actual preparation filter and its failure output. It uses the same physical gates as the source.
3. `C_infinity(xhat)` is a mathematical comparison process at the data-chosen nominal pulse area. It is not secretly supplied with the true area.
4. `C_K(xhat)` uses the actual finite generator `P_K H_xhat P_K`, K=N+2L=4175, L=40. It is a finite predictor, not an assumed available hardware action. Ordinary floating matrix exponentials are diagnostics; a numerical allowance is accepted only for separately verified output arithmetic.

All outputs occupy one declared record alphabet and common terminal Hilbert space via explicit embedding, with source-failure records retained with zero mass where appropriate. Every distance is one half of the full trace norm, equivalently the sum of the terminal-block trace distances. Arbitrary coarse observations inherit a bound by contraction; finite tester observations alone do not prove that full bound.

## Frozen parameters, calibration and precision

Design set: q in [12/25,13/25], |x|<=1/10, phase pi/3, mean G<=1. Complete-output precision is 1/20. Source-flag calibration uses 120000 independent fresh trials and estimates q from twice the original failure frequency, with half-width 1/100. Independent drive calibration uses 1000000 fresh plus-x/vacuum trials with a binary momentum-half-axis readout; its probability is Phi(2x), with probability half-width 1/500. A deterministic inverse/rounding rule produces xhat and a certified displacement Delta_x. The joint Hoeffding coverage is at least 99/100 under this frozen iid and ideal-readout model. The nuisance/readout model is not calibrated by synthetic counts.

The parameter set retains the exact shared relation s=1-q/2. Deployment weights are fixed functions of legal visible histories, so the quantifier is one deployed policy for every parameter in the calibrated set. A design-set inclusion failure, or excessive calibration radius, returns insufficient certification. A numerical allowance 1e-8 is reserved only for outputs with a separately accepted interval arithmetic certificate.

The source-data generator, calibration analyzer and held-out tester analysis have separate inputs. Synthetic truth is provenance and is inaccessible to the analyzer. No real apparatus data were obtained; simulated acceptance does not upgrade the empirical axis.

## Research ownership and required closure

A owns the complete-record prefix stability proof and operational cross-review. B owns selfadjoint source construction, source-derived energy/boundary-flow estimates and finite Duhamel remainder for true versus compressed dynamics. C owns joint calibration, nominal-parameter certification, independent rational checks and synthetic held-out controls. Root owns the common-source interpreter, numerical output certification, bilingual integration and all authoritative repository state.

The required new arrow is simultaneous unbounded dynamics to a controlled Galerkin predictor of the same complete intervention process. State projection alone, a successful finite matrix exponential, or an average-energy statement alone cannot close this arrow. Existing hard-window and flag-only counterexamples remain valid. The long-term roadmap retains full OPT, independent complex selection, memory/limits, bath/EFT, particles, gravity and cosmology responsibilities.
