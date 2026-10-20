# UEOT Publications

This directory holds dated publication and release snapshots: papers, figures
and artifacts prepared for citation or distribution. Each snapshot describes
a particular state of the theory.

## Maintained books

The two books are developed independently in their own directories and inform
one another through explicit cross-references:

| Book | Maintained manuscript | Reading formats and source history |
|---|---|---|
| *客体、演化与意义：一种开放的统一自然哲学* | [UEOT_PHILOSOPHY.md](../philosophy/UEOT_PHILOSOPHY.md) | [philosophy/](../philosophy/README.md) |
| UEOT Core Mathematics | [UEOT_MATHEMATICS.md](../mathematics/UEOT_MATHEMATICS.md) | [mathematics/](../mathematics/README.md) |

Revise the maintained sources when developing a new edition. A released
edition can be recorded here together with its source identity and build
provenance. A philosophical argument, mathematical theorem and empirical
claim retain their respective standards of justification in every edition.

## Snapshot provenance

A release should identify:

- its title, edition or version, date and source commit;
- the source files and integrity hashes needed to reproduce the artifact;
- the mathematical specification and formalization state relevant to its
  claims, including the scope of any cited proof result;
- any additional model assumptions and validation reports on which its
  interpretation depends;
- the build instructions and reading formats supplied with the release.

For the frozen Core v3.0 source, use the
[specification manifest](../core/specifications/manifest.yaml) and the exact
[mathematical source](../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md).
A later maintained book has its own version; it does not replace those frozen
bytes or silently revise their 106 source P-IDs.

## Historical publications

The original philosophical paper and its source provenance are documented in
[philosophy/source/original/](../philosophy/source/original/README.md).
Historical root PDF and ZIP files retain their existing addresses. Extracted
texts and former book scaffolding are archived under
[philosophy/source/](../philosophy/source/), including
[source/legacy/](../philosophy/source/legacy/README.md).

The retired root `book/` and `source/` layouts are historical references. The
current book entries are `philosophy/` and `mathematics/`; historical RFCs and
decisions continue to record the repository state in which they were written.
