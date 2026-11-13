# UEOT QM v31.13 / Kernel 1.13 — simultaneous dynamics to calibrated predictions

Research entry is verified main `cb17211653fde30aa50e0e9848798a6a5b3b3f12`, carrying v31.12 / Kernel 1.12 and bilingual book 3.9. This increment adds Chapter 69 to the same continuous books and keeps all 188 prior result objects and 111 ledger claims. The authoritative execution and integration state is [CURRENT](status/CURRENT.json); a paper result, a computer-checked certificate, and a verified device have different status axes.

## Closed arrow and exact scope

**Specified self-adjoint simultaneous dynamics → genuine compressed Hamiltonian → controlled complete-record prediction → independently calibrated nominal parameter → an exact finite and, for a specified input, interval-certified numerical prediction.**

The previous simultaneous-force infinite-tail counterexample remains valid. It is not converted into a finite-support theorem. The new bound concerns `exp(-it P_K H P_K)`, not a normalized projection of the already evolved state. A small state tail, equality between two sampled cutoffs, or a tiny matrix-exponentiation residual cannot establish it.

| Stable result | New statement |
| --- | --- |
| P-OPT-05 | Complete normal CQ-tree distance is bounded by the sum of local errors on a consistently chosen unnormalized finite/reference prefix family, retaining labels, failure, stopping and finite references |
| P-MICRO-06 | The declared simultaneous Hamiltonian has a self-adjoint source construction, a source-derived excitation-growth budget and a two-edge Galerkin boundary-flow defect |
| P-MICRO-07 | A finite, domain-safe Duhamel expansion bounds true versus genuine Galerkin dynamics on `P_N` by `min(1,2 c_(L+1))` at `K=N+2L` |
| C-MICRO-03 | Compression need not preserve the exact infinite `X²` form invariant; a three-dimensional counterexample fixes the order of parameter and cutoff comparisons |
| P-ROB-04 | Original failure counts plus a signed momentum tester give joint fixed-sample calibration; one data-chosen nominal area works uniformly over the entire admitted set |
| P-ROB-05 | The same source, full preparation, visible controller, nominal parameter and Galerkin predictor obey one complete-output error certificate |

Full statements and proofs are in [Chapter 69](book/UEOT_PHYSICS.md#ch-69), its [English counterpart](book/UEOT_PHYSICS.en.md#ch-69), and the [binding ledger](audits/SIMULTANEOUS_CUTOFF_v31.13/chapter69_formal_bindings.json). All six new claims are paper-only at the universal theorem level; no new Lean declaration is implied.

## One shared source

The system is a complex qubit and Fock oscillator, `G=n+P_e`, with an untouched finite reference and arbitrary initial entanglement. The calibrated simultaneous slot is `V1(x)=exp[-i x sigma_x(a+a†)]`; `V0=exp[-i(pi/3)P_e]`. The more general proved source is `omega n+Delta P_e+gA+hB`, with `omega>0` and real coefficients, self-adjoint on `D(n)`. The zero-frequency force subfamily has its own specified quadrature realization.

Original labelled events are `sqrt(s(1-q)) V0`, `sqrt(sq) V1`, and `sqrt(1-s) I`, where `s=1-q/2`. The complete two-slot record alphabet is `f,0f,1f,00,01,10,11`; failures stop, and the last four are accepted. Computing backward from these events gives `s²I`, making the normalized target CPTP. The unchanged legal policy has `Q00=Q11=313/1250`, `Q01=Q10=312/1250`, reads only visible history and has expected force-call count one. Its design-region record error is at most `1/50`.

The physical compiler calls the same unknown real gates as the source. The numerical predictor uses a nominal area selected solely from calibration. A compressed Hamiltonian is not presumed to be a physically available action. The actual low-spectral filter includes `prep_fail`, vacuum reset of S and the actual failure-conditioned reference marginal.

## Error and calibration

For initial budget `Tr G rho<=1`, `N=4095`, `L=40`, `K=4175`, define

`c_j(N,z)=z^j/j! product_(r=1)^j sqrt(N+2r-1)`.

The joint bound is

`D_full <= (sqrt(4e-3e²)+e)/2 + 1/50 + sqrt(6) Delta_x + epsilon_Gal(xhat)`,

where `e=1/4096` and

`epsilon_Gal=(624/1250) min(1,2c41(N,|xhat|)) +(313/1250) min(1,2c41(N,2|xhat|))`.

Parameter comparison is made between two exact infinite models before applying the Galerkin estimate; the finite model does not inherit the required invariant. For the design `|x|<=0.1`, the full-design cutoff term is below `0.000045417199842`. The calibrated nominal area gives a much smaller term.

The independent ideal calibration protocol has 120000 original-source trials for failure probability `q/2`, and 1000000 fresh plus-x/vacuum trials for a binary momentum event with probability `Phi(2x)`. The frozen radii give family failure at most `2 exp(-6)+2 exp(-8)<0.01`. This is a fixed-sample unconditional false-certificate bound, not post-admission conditional coverage or permission to resample until passing. All device/readout assumptions remain explicit.

The synthetic raw streams yield `qhat=0.5006`, `xhat=2969/50000`, and `Delta_x<0.002524819334`. Independent rational checks give the exact finite-predictor bound **below 0.041930158795**. For one specified entangled `G<=1` input, outward integer Taylor arithmetic actually evaluates the large-carrier predictor and certifies numerical error below `1e-8`; that numerical output has total bound **below 0.041930168795**. The all-input paper theorem concerns the exact finite map; the numerical output certificate is not extrapolated to every input.

Independent held-out data use a different protocol, two consecutive shared pulses with response `Phi(4x)`, as well as complete source and compiler records. A deliberately mismatched pulse control is rejected using the same frozen threshold. All streams are synthetic, with their generating truth inaccessible to the analyzer. Single-dose detector-offset ambiguity is retained with its correct access scope; two doses with a shared fixed offset can resolve it, while setting-dependent offsets need additional information.

## Evidence and boundaries

The [runtime directory](simultaneous_cutoff/README.md) contains the original-source interpreter, separately authored checks, calibration generator/analyzer, a genuinely independent rational checker and a directed-integer numerical predictor. Its runner records the actual environment, checkout, commands, inputs and outputs. Original subagent reviews keep their authorship and execution identity; root or CI execution is not relabelled as the author's run.

The unchanged 158 proof/configuration inputs, 13 previous runtime inputs and full proof/tool inventory are checked before reusing the original v31.11 proof execution. No new Lean execution is needed for the paper-only increment. Actual PR and main runtime evidence, when observed, is separately recorded rather than predicted in this document.

Standard complex/Born/tensor/CP structure, the Fock/control model, ideal filter/reset/readout, fixed shared parameters and iid calibration remain independent physical inputs. No protocol-matched real device counts, complete-state calibration or measured resource advantage were obtained. Full OPT, independent complex selection, bath/EFT, particle/flavour, gravity and cosmology responsibilities remain on the [continuous roadmap](ROADMAP.md). Standard Hamiltonian truncation and Duhamel methods are not relabelled as new physical laws.
