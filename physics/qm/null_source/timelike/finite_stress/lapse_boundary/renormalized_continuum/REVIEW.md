# Cohort Boundary, Certificate, and Audit Verification (`review.py`)

`review.py` enforces:
1. AST import hygiene across all Python scripts in `renormalized_continuum/` (`predecessor_scientific_modules_imported_or_executed == 0`, zero dynamic execution).
2. Exact `source_sha256` bindings, `"status": "PASS"`, `"mode_ODE_integrations": 0`, `"geometry_ODE_integrations": 0`, and `"physical_unification": "OPEN"` across every scientific certificate in `ENTRIES[:-1]`.
3. Immutable Git blob SHA-256 verification (`git show <commit>:<file>`) for all 3 native read-only research reviewers in `source_audits.json`, requiring zero unresolved findings at final sign-off.
4. Exact wall-clock timestamp consistency in `session_timing.json` with `prior_session_time_counted == false`.
