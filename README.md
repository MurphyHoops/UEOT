# Universal Evolutionary Object Theory (UEOT)

This repository hosts the manuscript and LaTeX source for:

**Degui Qian, _A Universal Evolutionary Object Theory (UEOT): A Framework and Research Program for a Unified Science_**

UEOT is a first-principles research framework aimed at unifying the physical,
biological, cognitive, and social domains under a single object-based theory of
evolution. The manuscript introduces two central postulates:

- the **Topological Ontology of Existence**, where persistent objects are
  maintained by self-sustaining feedback structures called **Omega-loops**
  (`\Omega`-loops)
- the **Dual Drive of Evolution**, where change is shaped by a balance between
  physical efficiency (`\Pi`) and informational optimization (`\Phi`)

From these foundations, the work develops concepts such as the **Global
Optimal Direction (GOD)** and **Global Optimal Attractor (GOA)** to explain how
goal-directed behavior can emerge from underlying physical dynamics.

## Repository Contents

- [UEOT_v3_top.pdf](./UEOT_v3_top.pdf): compiled manuscript
- [UEOT_v3_top[1].zip](./UEOT_v3_top%5B1%5D.zip): LaTeX source archive for the
  manuscript
- [LICENSE](./LICENSE): repository license terms

## Build From Source

The source archive contains the manuscript file `main.tex`, bibliography data,
and the journal/template files used to compile the paper.

Typical build flow after extracting the archive:

```bash
unzip "UEOT_v3_top[1].zip" -d ueot-src
cd ueot-src
xelatex main.tex
bibtex main
xelatex main.tex
xelatex main.tex
```

Depending on your TeX environment, `latexmk` can also be used.

## Citation

If you reference this work, please cite:

```text
Degui Qian. A Universal Evolutionary Object Theory (UEOT): A Framework and
Research Program for a Unified Science. 2026.
```

## License

The original manuscript and repository-authored materials are released under
the [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) license. The
LaTeX source archive is included in that grant for the original UEOT content,
while bundled third-party template or style files remain under their own
respective licenses.

## Contact

- Author: Degui Qian
- Email: `deven.qian@gmail.com`
