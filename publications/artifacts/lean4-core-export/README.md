# Audited Apache-2.0 Export Package — Pure-Kernel Lean 4 Proof Archive

This directory provides the audited open-source software licensing artifacts, deterministic archive packager, and automated Zenodo concept-lineage release pipeline for the **1,051-module pure-kernel Lean 4 (`v4.33.1` / Mathlib) formalization** accompanying Papers 2 and 3.

## License & Compliance Summary

- **Published Zenodo Software DOI (v1.0.0):** [10.5281/zenodo.24433585](https://doi.org/10.5281/zenodo.24433585) (Concept DOI: [10.5281/zenodo.24433584](https://doi.org/10.5281/zenodo.24433584), record: <https://zenodo.org/records/24433585>).
- **Exported Software & Lean 4 Proof License:** **Apache License, Version 2.0 (`Apache-2.0`)** — verbatim license text at [`../../LICENSES/Apache-2.0.txt`](../../LICENSES/Apache-2.0.txt).
- **Upstream & Dependency Audit:** [`SOFTWARE_LICENSE_AUDIT.md`](SOFTWARE_LICENSE_AUDIT.md) verifies 100% `Apache-2.0` compatibility across all 1,051 Lean modules, all 5 attributed upstream Lean projects (`CrooksJarzynskiLean`, `CausalSmith`, `StatLean`, `TauCeti`, `LML`), and all 9 Lake dependencies (`mathlib4`, `batteries`, `aesop`, `Qq`, `proofwidgets`, `importGraph`, `LeanSearchClient`, `plausible`, `Cli`).
- **Section 4(d) Attribution Notice:** [`NOTICE`](NOTICE) preserves all copyright and modification notices.
- **Zenodo & Citation Metadata:** [`.zenodo.json`](.zenodo.json) and [`CITATION.cff`](CITATION.cff) (`license: Apache-2.0`).
- **Scope Separation:** Non-code research prose under `formalization/ueot-core/docs/` is excluded from the exported software tarball and remains governed by `CC BY 4.0` per root `LICENSE_SCOPE.md`.

## Deterministic Archive Generation

```bash
python3 export_lean4_archive.py
```

Generates `dist/lean4-pure-kernel-formalization-v1.0.0.tar.gz` (gitignored to avoid duplicating 1,051 `.lean` files in Git) and records deterministic SHA-256/MD5 provenance in `dist/EXPORT_RECEIPT-v1.0.0.json` (pass `--write-tracked-receipt` only when intentionally updating tracked [`EXPORT_RECEIPT.json`](EXPORT_RECEIPT.json)). Version `1.0.0` is permanently archived on Zenodo at <https://doi.org/10.5281/zenodo.24433585> (SHA-256 `5419665d1c0d6d402e0cc0e769339f6ef4aba454f4ac48858543b43e1fd4cefc`, MD5 `1be76e0f670f698b501817e239dbc23a`).

## Automated GitHub Actions ↔ Zenodo Concept-Lineage Releases

Rather than mirroring the full repository via Zenodo's repository-wide GitHub switch (which would mint a disconnected DOI and bundle CC BY 4.0 book prose), [`.github/workflows/zenodo-lean4-release.yml`](../../../.github/workflows/zenodo-lean4-release.yml) and [`publish_zenodo_version.py`](publish_zenodo_version.py) publish **only** the pure `Apache-2.0` Lean 4 tarball directly into existing Concept DOI **`10.5281/zenodo.24433584`**.

1. **One-time secret setup (`ZENODO_TOKEN`):** Create a Zenodo Personal Access Token at <https://zenodo.org/account/settings/applications/tokens/new/> (scopes: `deposit:write`, `deposit:actions`) and store it securely:
   ```bash
   gh secret set ZENODO_TOKEN --repo MurphyHoops/UEOT
   ```
2. **Safe draft creation via GitHub Actions UI:** Open **Actions → Zenodo Lean 4 Release → Run workflow**, enter a new semantic version (e.g. `1.0.1`), keep `mode = draft`, and inspect/publish the created draft in Zenodo (`Actions` summary prints the draft URL and pre-reserved DOI).
3. **One-command tag release (auto-publish):**
   ```bash
   git tag lean4-export-v1.1.0 && git push origin lean4-export-v1.1.0
   ```
4. **Local dry-run & verification (no token required):**
   ```bash
   python3 -m unittest test_zenodo_release.py -v
   python3 publish_zenodo_version.py --version 1.1.0 --mode dry-run
   ```
