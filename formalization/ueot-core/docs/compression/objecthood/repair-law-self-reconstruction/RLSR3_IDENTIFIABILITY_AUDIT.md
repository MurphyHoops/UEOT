# RLSR3 — corruption / identifiability no-go audit

Status: **LOCAL PASS**

## Result

The strongest stage statement is not merely a two-program contradiction.
`observation_separates_behavior_of_exact_reconstructor` proves a necessary
condition for any deterministic exact behavioral reconstructor:

> equal corrupted observations may occur only inside one carrier-relative
> behavioral program class.

The explicit collision no-go follows immediately.

## Independent audit / optimization

This prevents RLSR from claiming recovery after arbitrary destruction.  If all
information distinguishing two operationally different repair laws is erased,
there is no deterministic internal inference rule that can know which behavior
to restore from the shared observation alone.

The theorem is deliberately behavioral and carrier-relative, matching RLSR2.
It does not overclaim an impossibility for probabilistic/Bayesian recovery under
additional priors or side information; those are outside this exact-recovery
statement.
