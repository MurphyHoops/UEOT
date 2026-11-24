# Lean 4 Pure-Kernel Formalization Blueprint

Interactive dependency graph, 1,051-module explorer, and 106-assumption ledger for the pure-kernel Lean 4 (`v4.33.1` / Mathlib) formalization accompanying our submitted articles on verified controller synthesis, calibrated post-selection risk, and certified polynomial decision DAGs.

- **Live Blueprint Site (GitHub Pages):** <https://murphyhoops.github.io/UEOT/>
- **Archived Apache-2.0 Release (Zenodo v1.0.0):** <https://doi.org/10.5281/zenodo.24433585> (Concept DOI: <https://doi.org/10.5281/zenodo.24433584>)
- **Lean Zulip `#announce` Post Draft:** [`ZULIP_ANNOUNCE_DRAFT.md`](ZULIP_ANNOUNCE_DRAFT.md)

## Local Build & Preview

```bash
python3 publications/blueprint/build_blueprint.py
python3 -m http.server --directory publications/blueprint/site 8080
```

Then open `http://localhost:8080/` in your browser. Deployment to GitHub Pages is automated via [`.github/workflows/deploy-blueprint.yml`](../../.github/workflows/deploy-blueprint.yml).
