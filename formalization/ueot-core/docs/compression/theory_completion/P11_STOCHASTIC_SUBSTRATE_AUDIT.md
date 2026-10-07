# Theory Completion P11 — Stochastic-Calculus Substrate Audit

Status: **LOCAL COMPLETE / PARTIAL EXPLICIT BOUNDARY / TRACK TC / UNCOUNTED**

Immediate local dependency: P10 exact head `9b0407ed4bb9971365d722253da323d9eda572b7`.

## Source-level audit

P11 does not treat all continuous-time results as equally external.

The finite CTMC P-KL-04 path is deeply internalized: the formalization builds the
finite jump path law, density/Radon–Nikodym route, jump/holding rewards,
renewal/Campbell identities, literal clock-time integral and final KL equality.
Its terminal wrapper needs only the concrete finite jump generators and support
inclusion.

The general diffusion branches retain honest process-specific adapters:

- P-KL-05 consumes `TerminalGirsanovData`, which records the terminal exponential
  density, stochastic-integral shift, martingale and energy integrability output
  of a valid Girsanov theorem;
- P-CTL-03 consumes `ControlFamily`/`ItoRun`, whose runs contain the valid
  Itô/localization expectation identity and integrability output;
- P-REC-02 similarly consumes `DynkinExpectationCertificate` rather than deriving
  domain/localization/nonexplosion from a symbolic generator inequality.

## P11 formal surface

`StochasticSubstrate.lean` exports:

- `p11_finiteCTMC_internal_pathKL`;
- `p11_girsanov_terminal_adapter`;
- `p11_diffusionHJB_terminal_adapter`;
- `p11_terminal_stochastic_substrate`.

The terminal theorem deliberately puts an internally derived CTMC formula next
to the terminal-adapter Girsanov formula so that the difference is present in
the type signature, not only in prose.

## Verdict

P11's numbered integration task is **locally complete** as a stochastic substrate
classification/integration layer. The stronger claim “full general SDE/Itô/
Girsanov foundations are constructed internally in Lean” is **NOT proved**.
That stronger task remains an explicit lower-level formalization project and
should only be activated when it removes a material scientific adapter.

Claim class: **THEOREM + ADAPTER + PARTIAL/EXPLICIT BOUNDARY**.
