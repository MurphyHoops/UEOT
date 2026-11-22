# Audited Apache-2.0 Export Package — Pure-Kernel Lean 4 Proof Archive

This directory provides the audited open-source software licensing artifacts and deterministic Zenodo archive packager for the **1,051-module pure-kernel Lean 4 (`v4.33.1` / Mathlib) formalization** accompanying Papers 2 and 3.

## License & Compliance Summary

- **Published Zenodo Software DOI (v1.0.0):** [10.5281/zenodo.24433585](https://doi.org/10.5281/zenodo.24433585) (concept DOI: [10.5281/zenodo.24433584](https://doi.org/10.5281/zenodo.24433584), record: <https://zenodo.org/records/24433585>).
- **Exported Software & Lean 4 Proof License:** **Apache License, Version 2.0 (`Apache-2.0`)** — verbatim license text at [`../../LICENSES/Apache-2.0.txt`](../../LICENSES/Apache-2.0.txt).
- **Upstream & Dependency Audit:** [`SOFTWARE_LICENSE_AUDIT.md`](SOFTWARE_LICENSE_AUDIT.md) verifies 100% `Apache-2.0` compatibility across all 1,051 Lean modules, all 5 attributed upstream Lean projects (`CrooksJarzynskiLean`, `CausalSmith`, `StatLean`, `TauCeti`, `LML`), and all 9 Lake dependencies (`mathlib4`, `batteries`, `aesop`, `Qq`, `proofwidgets`, `importGraph`, `LeanSearchClient`, `plausible`, `Cli`).
- **Section 4(d) Attribution Notice:** [`NOTICE`](NOTICE) preserves all copyright and modification notices.
- **Zenodo & Citation Metadata:** [`.zenodo.json`](.zenodo.json) and [`CITATION.cff`](CITATION.cff) (`license: Apache-2.0`).
- **Scope Separation:** Non-code research prose under `formalization/ueot-core/docs/` is excluded from the exported software tarball and remains governed by `CC BY 4.0` per root `LICENSE_SCOPE.md`.

## Deterministic Archive Generation

```bash
python3 export_lean4_archive.py
```

Generates `dist/lean4-pure-kernel-formalization-v1.0.0.tar.gz` (gitignored to avoid duplicating 1,051 `.lean` files in Git) and records deterministic SHA-256 provenance in [`EXPORT_RECEIPT.json`](EXPORT_RECEIPT.json). Version `1.0.0` is permanently archived on Zenodo at <https://doi.org/10.5281/zenodo.24433585> (SHA-256 `5419665d1c0d6d402e0cc0e769339f6ef4aba454f4ac48858543b43e1fd4cefc`, MD5 `1be76e0f670f698b501817e239dbc23a`).
