# Software License & Dependency Audit — Exported Lean 4 Core Proof Archive

**Audit Date:** 2026-11-22  
**Target Export Package:** `publications/artifacts/lean4-core-export/` (exporting pure-kernel Lean 4 proof sources from `formalization/ueot-core/`)  
**Selected Export License:** **Apache License, Version 2.0 (`Apache-2.0`)**

---

## 1. Governance Authority & Scope Boundary

Pursuant to root `LICENSE` (Section D), `COPYRIGHT.md` ("Software and patent caution"), and `LICENSE_SCOPE.md` ("What a new release must do", Item 4), declaring an explicit open-source software license for exported Lean 4 code requires a documented review of:
1. authorship and prior historical grants;
2. embedded third-party/adapted Lean source files and their upstream licenses;
3. Lake toolchain and external library dependencies; and
4. separation between exported software/proof source files (`Apache-2.0`) and non-code scientific prose (`CC BY 4.0`).

This audit applies **specifically to the exported pure-kernel Lean 4 software & proof archive** assembled by `export_lean4_archive.py` (`UEOT.lean`, `UEOT/**/*.lean`, `UEOT/V3/ThirdParty/CrooksJarzynski/{LICENSE,UPSTREAM.md}`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, and `scripts/*.{lean,py}`). Non-code documentation under `formalization/ueot-core/docs/` is intentionally excluded from the software tarball and remains governed by `CC BY 4.0` per `LICENSE_SCOPE.md`. Prior historical `CC BY 4.0` grants over earlier public repository snapshots remain unrevoked. Separate directories (`formalization/ueot-qm/`, `physics/`, `UEOT-GI`) are outside the scope of this export grant.

---

## 2. Upstream & Attributed Lean Source Inventory (100% Apache-2.0 Compatible)

An exhaustive scan across all 1,051 compiled Lean 4 library modules under `formalization/ueot-core/` identifies five upstream Lean 4 projects from which specific foundational lemmas or continuous-time path-law infrastructure were vendored or adapted. **Every single upstream source is licensed under `Apache-2.0`**, making `Apache-2.0` (with an accompanying Section 4(d) `NOTICE` file and preserved file headers) 100% license-compatible:

| Local Path in `formalization/ueot-core/` | Upstream Project & Copyright Holder | Upstream License | Attribution & Modification Record |
|:---|:---|:---:|:---|
| `UEOT/V3/ThirdParty/CrooksJarzynski/*.lean` (11 files) | `kiyo-e/CrooksJarzynskiLean` (`b415db75...`), Copyright (c) 2026 kiyo-e | `Apache-2.0` | Preserves upstream headers, verbatim `LICENSE`, and modification log in `UPSTREAM.md` |
| `UEOT/V3/InformationBernoulliKL.lean`, `InformationKernelKL.lean`, `InformationPinsker.lean` | `Jiyuan-Tan/CausalSmith` (`Causalean`), Copyright (c) 2026 Jiyuan Tan | `Apache-2.0` | Explicit attribution & Lean 4.33.1 adaptation notes in module headers |
| `UEOT/V3/InformationKernelTV.lean`, `InformationSharpFano.lean` | `StatLean` (2026, StatLean contributors) | `Apache-2.0` | Explicit attribution & adaptation notes in module headers |
| `UEOT/V3/InformationKernelKLMeasurable.lean` (part 1) | `TauCetiProject/TauCeti` (2026, Tau Ceti contributors) | `Apache-2.0` | Explicit attribution & adaptation notes in module header |
| `UEOT/V3/InformationKernelKLMeasurable.lean` (part 2) | `LeanMachineLearning/LML` (2026, Rémy Degenne) | `Apache-2.0` | Explicit attribution & adaptation notes in module header |

All remaining owned Lean 4 modules in `formalization/ueot-core/` (including all modules underlying Papers 2 and 3 in `UEOT/V3/Compression/` and `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/`) are authored for the project by Degui Qian (copyright holder).

---

## 3. Toolchain & Lake Dependency Inventory (100% Apache-2.0)

From `lean-toolchain` and `lake-manifest.json` (fetched externally by Lake during build, not redistributed inside the source tarball):

- **Lean 4 Toolchain:** `leanprover/lean4:v4.33.1` — `Apache-2.0`
- **Direct & Transitive Lake Packages:**
  1. `mathlib` (`leanprover-community/mathlib4` @ `0df444a360eaa60ab8c11dca51a86af692955474`) — `Apache-2.0`
  2. `batteries` (`leanprover-community/batteries` @ `4488d40d...`) — `Apache-2.0`
  3. `aesop` (`leanprover-community/aesop` @ `3448c0bc...`) — `Apache-2.0`
  4. `Qq` (`leanprover-community/quote4` @ `92c15be1...`) — `Apache-2.0`
  5. `proofwidgets` (`leanprover-community/ProofWidgets4` @ `4be2e3d5...`) — `Apache-2.0`
  6. `importGraph` (`leanprover-community/import-graph` @ `16f02aa7...`) — `Apache-2.0`
  7. `LeanSearchClient` (`leanprover-community/LeanSearchClient` @ `5f4d51b8...`) — `Apache-2.0`
  8. `plausible` (`leanprover-community/plausible` @ `b7eb3304...`) — `Apache-2.0`
  9. `Cli` (`leanprover/lean4-cli` @ `6130a478...`) — `Apache-2.0`

---

## 4. Patent & Redistribution Considerations Noted

- Under `Apache-2.0` Section 3, Licensor grants a narrow affirmative patent license limited strictly to patent claims licensable by Licensor that are necessarily infringed by the exported Lean 4 proof Contribution(s), subject to Apache-2.0 defensive termination.
- Under `Apache-2.0` Section 4, every exported archive bundles the verbatim `LICENSE` (`Apache-2.0`) and `NOTICE` file preserving all upstream copyright and modification notices.
