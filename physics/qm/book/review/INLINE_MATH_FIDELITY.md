# Inline-mathematics translation-fidelity audit

**Result: PASS for the exact frozen 3.7 bilingual manuscripts below: Chapters 0–66 and Appendices A–F.** All differences are attributed by the ten explicitly reviewed occurrence-bound exceptions or by within-subsection order changes. Chapter 66 introduces no additional exception. This is a fresh run on the new source identity, not a transfer of the earlier 66-chapter PASS.

## Scope and source identity

| Input | SHA-256 | UTF-8 bytes |
|---|---|---:|
| zh | `fd651a93cc4f38b755409f184bab231c43e889f648efda852340f8b594fb9060` | 706234 |
| en | `437d4239be7a4239e701b760af1fcccdaf30f5b7ab976e9703c532990acb9a91` | 858402 |

Parser: `pandoc 3.1.11.1`, reader `markdown+tex_math_dollars`, Pandoc API `[1, 23, 1]`. Checker SHA-256: `1be429bcd9d45219a88b4802f8f0f927b419574fa1d6b5e883222b3ef2b888fd`. Both caller-supplied freeze hashes matched the actual input bytes.

The checker extracts every Pandoc `Math` node of type `InlineMath`, including nested structures, tables and headings. All 67 chapters and six appendices have their 73 stable anchors in the required order. Front matter and metadata contain no inline-math nodes. Fenced code is not treated as mathematical prose. Display mathematics has a separate audit. This PASS certifies the stated translation-fidelity comparison; it is not a theorem-prover result, new Lean build, PDF inspection, experiment, or remote acceptance.

## Conservative method

The baseline is the literal Pandoc math payload, including internal whitespace. Chapter-level `Counter` objects preserve multiplicity while allowing prose to reorder occurrences. Additional subsection-level Counters prevent cancellation across separate sections. There is no generic whitespace removal, TeX-command stripping, comma splitter, variable deletion, equation rearrangement or algebraic simplification.

Every exception requires one exact chapter/subsection, a specific paragraph marker, an exact contiguous math group and a unique located match. Original occurrence IDs and full paragraph contexts remain in JSON. An extra English variable mention requires locating both its Chinese context and the existing defining expression. Missing or repeated anchors, ambiguous matches, overlaps and unexplained differences fail the check. The complete original inventory retains all nodes, including the two explicitly attributed extra mentions.

The script requires an explicit `--book-dir` and always records the exact two input hashes. Optional paired `--expected-zh-sha256` and `--expected-en-sha256` arguments enforce a caller-selected frozen identity; this final execution supplied both. A later input is a distinct audit and cannot inherit this receipt merely because the script also accepts explicit paths for subsequent editions.

## Actual results

- Raw nodes: Chinese **3073**, English **3080**.
- Literal Counters already agree for **64/73** chapters/appendices; literal sequences agree for **48/73**.
- Exactly **10** located exceptions: six enumeration splits, two identities already stated in prose made explicit, and two references to existing variables.
- After attribution: **3078** comparison tokens on each side, **73/73** chapter/appendix Counters and all **320** inline-bearing subsection Counters agree.
- **28** subsections have order variation only. Complete edit scripts and sequence hashes are in JSON.
- **0 unexplained differences**, zero reported errors, exit code 0.

The seven-node raw difference is exactly six extra English nodes from enumeration splits, minus one from the Chapter 8 consolidation, plus the two existing-variable references. The Chapter 26 explicit decomposition remains one node on each side. New Chapter 66 contributes 176 inline nodes to each language, with no new exception.

## Exhaustive exception ledger

### IM-01 — ch-2, §2.2

Chinese: `A,B`.

English: `A` + `B`.

The same two channel carriers are separated by English prose; no generic comma normalization is allowed.

Exactly one match on each side, in AST blocks Chinese 106 and English 106. The JSON retains all consumed occurrence IDs and context hashes.

### IM-02 — ch-7, §7.2

Chinese: `L_{ab},K_{ab}`.

English: `L_{ab}` + `K_{ab}`.

The two successive block multipliers retain their order and indices; only the prose separator changes.

Exactly one match on each side, in AST blocks Chinese 250 and English 250. The JSON retains all consumed occurrence IDs and context hashes.

### IM-03 — ch-8, §8.1

Chinese: `X` + `\sum_{a,b}P_aXP_b`.

English: `X=\sum_{a,b}P_aXP_b`.

Chinese says to expand X into the displayed sum; English places that already asserted equality inside one math node. This is an explicit reviewed exception, not a general rule for inserting equals signs.

Exactly one match on each side, in AST blocks Chinese 268 and English 268. The JSON retains all consumed occurrence IDs and context hashes.

### IM-04 — ch-11, §11.4

Chinese: `(A-\langle A\rangle)\psi,(B-\langle B\rangle)\psi`.

English: `(A-\langle A\rangle)\psi` + `(B-\langle B\rangle)\psi`.

The same two vectors in the Cauchy–Schwarz inner product are separated by English prose; operators and ordering are unchanged.

Exactly one match on each side, in AST blocks Chinese 363 and English 363. The JSON retains all consumed occurrence IDs and context hashes.

### IM-05 — ch-18, §18.2

Chinese: `|0\rangle,|1\rangle`.

English: `|0\rangle` + `|1\rangle`.

The adjacent two future-state nodes are the two outcomes of the memory counterexample. The earlier re-preparation of |0> is not consumed.

Exactly one match on each side, in AST blocks Chinese 482 and English 482. The JSON retains all consumed occurrence IDs and context hashes.

### IM-06 — ch-22, §22.2

Chinese: `m>0,r=|\mathbf x|`.

English: `m>0` + `r=|\mathbf x|`.

The positive-mass assumption and radial-coordinate definition are unchanged and separated by prose.

Exactly one match on each side, in AST blocks Chinese 562 and English 562. The JSON retains all consumed occurrence IDs and context hashes.

### IM-07 — ch-22, §22.2

Chinese: (no separate inline node).

English: `x`.

English explicitly names x as the argument carried by the Lorentz transformation. Chinese refers to the same spacelike argument implicitly; both retain x^2<0 and x^0=0. Only this one located mention is attributed as extra prose notation.

Exactly one match on each side, in AST blocks Chinese 561 and English 561. The JSON retains all consumed occurrence IDs and context hashes.

### IM-08 — ch-26, §26.1

Chinese: `\phi_<+\phi_>`.

English: `\phi=\phi_<+\phi_>`.

Chinese says to split the field into low and high modes. English names the existing field on the left of that same decomposition. No new operator or condition is asserted.

Exactly one match on each side, in AST blocks Chinese 623 and English 623. The JSON retains all consumed occurrence IDs and context hashes.

### IM-09 — ch-28, §28.3

Chinese: (no separate inline node).

English: `y`.

English names y when explaining the inner integral already present in the identical displayed integral. This does not add an integration, a bound, or a physical variable.

Exactly one match on each side, in AST blocks Chinese 671 and English 671. The JSON retains all consumed occurrence IDs and context hashes.

### IM-10 — ch-31, §31.5

Chinese: `3X_L^3,3N_cX_{Q\pm}^3`.

English: `3X_L^3` + `3N_cX_{Q\pm}^3`.

The same two triplet anomaly contributions are listed separately; coefficients, powers, and signs remain literal.

Exactly one match on each side, in AST blocks Chinese 744 and English 744. The JSON retains all consumed occurrence IDs and context hashes.

## Chapter-by-chapter accounting

| Chapter/appendix | Chinese nodes | English nodes | Raw Counter equal | Explicit exceptions | Final Counter equal |
|---|---:|---:|:---:|---|:---:|
| ch-0 | 19 | 19 | yes | — | yes |
| ch-1 | 57 | 57 | yes | — | yes |
| ch-2 | 26 | 27 | no | IM-01 | yes |
| ch-3 | 57 | 57 | yes | — | yes |
| ch-4 | 58 | 58 | yes | — | yes |
| ch-5 | 48 | 48 | yes | — | yes |
| ch-6 | 28 | 28 | yes | — | yes |
| ch-7 | 38 | 39 | no | IM-02 | yes |
| ch-8 | 37 | 36 | no | IM-03 | yes |
| ch-9 | 22 | 22 | yes | — | yes |
| ch-10 | 41 | 41 | yes | — | yes |
| ch-11 | 32 | 33 | no | IM-04 | yes |
| ch-12 | 37 | 37 | yes | — | yes |
| ch-13 | 28 | 28 | yes | — | yes |
| ch-14 | 41 | 41 | yes | — | yes |
| ch-15 | 23 | 23 | yes | — | yes |
| ch-16 | 16 | 16 | yes | — | yes |
| ch-17 | 25 | 25 | yes | — | yes |
| ch-18 | 24 | 25 | no | IM-05 | yes |
| ch-19 | 23 | 23 | yes | — | yes |
| ch-20 | 15 | 15 | yes | — | yes |
| ch-21 | 14 | 14 | yes | — | yes |
| ch-22 | 11 | 13 | no | IM-06, IM-07 | yes |
| ch-23 | 13 | 13 | yes | — | yes |
| ch-24 | 20 | 20 | yes | — | yes |
| ch-25 | 39 | 39 | yes | — | yes |
| ch-26 | 21 | 21 | no | IM-08 | yes |
| ch-27 | 30 | 30 | yes | — | yes |
| ch-28 | 22 | 23 | no | IM-09 | yes |
| ch-29 | 39 | 39 | yes | — | yes |
| ch-30 | 26 | 26 | yes | — | yes |
| ch-31 | 80 | 81 | no | IM-10 | yes |
| ch-32 | 27 | 27 | yes | — | yes |
| ch-33 | 10 | 10 | yes | — | yes |
| ch-34 | 19 | 19 | yes | — | yes |
| ch-35 | 6 | 6 | yes | — | yes |
| ch-36 | 64 | 64 | yes | — | yes |
| ch-37 | 35 | 35 | yes | — | yes |
| ch-38 | 26 | 26 | yes | — | yes |
| ch-39 | 64 | 64 | yes | — | yes |
| ch-40 | 66 | 66 | yes | — | yes |
| ch-41 | 2 | 2 | yes | — | yes |
| ch-42 | 4 | 4 | yes | — | yes |
| ch-43 | 33 | 33 | yes | — | yes |
| ch-44 | 32 | 32 | yes | — | yes |
| ch-45 | 29 | 29 | yes | — | yes |
| ch-46 | 35 | 35 | yes | — | yes |
| ch-47 | 40 | 40 | yes | — | yes |
| ch-48 | 0 | 0 | yes | — | yes |
| ch-49 | 55 | 55 | yes | — | yes |
| ch-50 | 69 | 69 | yes | — | yes |
| ch-51 | 47 | 47 | yes | — | yes |
| ch-52 | 40 | 40 | yes | — | yes |
| ch-53 | 77 | 77 | yes | — | yes |
| ch-54 | 63 | 63 | yes | — | yes |
| ch-55 | 40 | 40 | yes | — | yes |
| ch-56 | 70 | 70 | yes | — | yes |
| ch-57 | 54 | 54 | yes | — | yes |
| ch-58 | 73 | 73 | yes | — | yes |
| ch-59 | 73 | 73 | yes | — | yes |
| ch-60 | 109 | 109 | yes | — | yes |
| ch-61 | 147 | 147 | yes | — | yes |
| ch-62 | 182 | 182 | yes | — | yes |
| ch-63 | 84 | 84 | yes | — | yes |
| ch-64 | 78 | 78 | yes | — | yes |
| ch-65 | 85 | 85 | yes | — | yes |
| ch-66 | 176 | 176 | yes | — | yes |
| appendix-a | 46 | 46 | yes | — | yes |
| appendix-b | 2 | 2 | yes | — | yes |
| appendix-c | 1 | 1 | yes | — | yes |
| appendix-d | 0 | 0 | yes | — | yes |
| appendix-e | 0 | 0 | yes | — | yes |
| appendix-f | 0 | 0 | yes | — | yes |

## Reproduction

From a repository containing the frozen manuscripts, after placing this unchanged checker at the chosen publication build path:

```bash
python3 physics/qm/book/build/verify_inline_math.py \
  --book-dir physics/qm/book \
  --expected-zh-sha256 fd651a93cc4f38b755409f184bab231c43e889f648efda852340f8b594fb9060 \
  --expected-en-sha256 437d4239be7a4239e701b760af1fcccdaf30f5b7ab976e9703c532990acb9a91 \
  --output physics/qm/book/evidence/v3.7/inline-math-fidelity.json
```

The companion JSON contains the full **6153-node** original inventory, exception contexts, chapter/subsection comparisons and order-variation edits. It was computed directly from the final manuscripts. The earlier root `math-differences.json` was only a diagnostic clue.

## Preserved initial checkpoint

The earlier Chapter 0–65 audit remains in `INLINE_MATH_FIDELITY_INITIAL_66_CHAPTER_CHECKPOINT.md`, `inline_math_fidelity_initial_66_chapter_checkpoint.json`, and `verify_inline_math_initial_66_chapter_checkpoint.py`. Its hashes and 2897/2904 counts are historical provenance, not the current 3.7 acceptance. The original ten narrow exceptions are preserved; the new chapter was actually compared rather than broadly exempted.
