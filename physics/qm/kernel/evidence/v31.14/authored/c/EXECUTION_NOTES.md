# C execution identity and correction notes

The 400,000 calibration trials were generated once after the calibration
contract was frozen. The 1,200,000 held-out trials were generated once after
the nominal model and executable held-out rule were frozen. No subsequent
review correction resampled or refitted either dataset.

Before the held-out rule was frozen, the independent interval preflight
exposed an mpmath complex-interval conjugation implementation error. The
helper was replaced by the algebraically identical `real - i*imag` formula,
and the final helper hash was bound before held-out generation.

B's separated review identified a reporting issue: nearest-decimal printing
of an exact upper bound could round inward by less than 1e-12. The original
frozen nominal/model files were preserved. `FINAL_CERTIFICATE.json` gives
exact fractions and directed conservative displays and confirms that all
original decisions are unchanged. Its event intervals are enlarged by
1e-12 around the prior displayed endpoints, which safely contains their
underlying exact Fraction intervals.

The finalizer's initial schema lookup used `lambda` instead of B's actual
`lambda_exact` key. It was corrected before a final certificate was
produced. Following B's revision 2, the finalizer alone was rerun to bind
the corrected certificate hashes; neither sampling nor fitting was repeated.

The structural thermal negative-control preflight initially compared two
high-precision floating expressions with exact equality. The mathematical
identity is now checked with Python Fraction, and the high-precision values
only serve as diagnostic calculations. The declared physical model and
counterexample were unchanged.

The external processed observable was first reproduced from the original
retained archive. To provide a portable artifact, the unchanged 6,584-byte
HDF5 member and provenance were included and the same predeclared observable
was reproduced once from that member. `EXTERNAL_OBSERVABLE_RESULT.initial.json`
preserves the first result. No new observable or selection threshold was
chosen after observing its values.

The phase times in the generation and held-out receipts cover those actual
program invocations. They exclude derivation, source reading, packaging,
the preflight corrections listed above, and separate-agent proof work;
they are not represented as total research wall time or total compute use.

For reproduction, copy the delivery directory and required B files to a new
working directory. Running the scripts in place regenerates execution
timestamps and output identities; it must not be represented as recovery
of the original frozen bytes. All source/model equivalence and certification
claims are conditional on the explicit physical assumptions. Hardware
validation and Core-only selection of quantum structure remain open.
