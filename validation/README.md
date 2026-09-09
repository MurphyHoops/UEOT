# UEOT Validation

This layer closes the loop between theory and nature.

## Required categories

- `benchmarks/` — recovery of established calculations and limiting cases
- `experiments/` — experimental protocols and preregistered/null-test logic
- `data/` — schemas, provenance records and adapters
- `pipelines/` — reproducible analysis code
- `falsification/` — explicit failure criteria and competing models
- `reports/` — dated execution results

## Evidence contract

A validation artifact should identify:

1. theory/core version or commit;
2. claim/P-ID or physics result under test;
3. external assumptions;
4. dataset, hardware or simulation provenance;
5. statistical/numerical method;
6. uncertainty and failure criterion;
7. conclusion without silently promoting a conjecture to theorem.

A successful benchmark shows consistency with that benchmark. It does not by itself establish UEOT as a unique explanation.
