# Universal Evolutionary Object Theory (UEOT)

This repository contains the manuscript and LaTeX source for:

**Degui Qian, _A Universal Evolutionary Object Theory (UEOT): A Framework and Research Program for a Unified Science_**

UEOT is an attempt to build a single conceptual language for matter, life,
mind, society, and meaning. The manuscript does not present itself as a closed
final theory; it is explicitly framed as an **open research program** with
clear conceptual commitments, proposed formal directions, and falsifiable
empirical ambitions.

## What UEOT Claims

At the center of the manuscript are two foundational postulates.

- **Topological Ontology of Existence**
  Persistent objects exist because they maintain at least one internal,
  self-regenerating feedback loop, called an **Omega-loop** (`\Omega`-loop).
  In this view, objecthood is not defined primarily by static substance, but by
  the persistence of a self-maintaining topological pattern.

- **Dual Drive of Evolution**
  Every object's evolution is governed by a coupled optimization between:
  - **`\Pi`**: a physical efficiency or immediate payoff drive
  - **`\Phi`**: an informational drive that reduces uncertainty and supports
    adaptive complexity

From these postulates, the manuscript derives a naturalized account of
teleology:

- **GOD (Global Optimal Direction)**: the local direction of evolution
- **GOA (Global Optimal Attractor)**: the long-run stable optimum toward which
  the object tends

The main philosophical move of UEOT is that apparent purpose is not treated as
something external to physics. It is treated as an emergent consequence of the
object's own dynamical structure and optimization landscape.

## Internal Architecture of the Theory

The manuscript develops UEOT as a layered framework rather than a single
isolated hypothesis.

- **Ontology of objects**
  Objects are characterized by feedback topology, not merely by composition.
  UEOT classifies them through loop complexity, loop openness, and dynamical
  mode.
- **Type I / Type II distinction**
  A key distinction is drawn between relatively closed, stable objects and
  environmentally coupled, adaptive objects. Openness is treated as
  lifecycle-dependent rather than fixed.
- **Lifecycle logic**
  Objects pass through emergence, optimization/maturation, and
  decay/dissolution, with openness rising, then selectively narrowing, then
  breaking down again.
- **Diagnostic formalism**
  The manuscript proposes a profile of the form
  `(L_c, L_o; Mode; v_RG)` together with diagnostic indices such as
  `eta_pref` and `rho` for evaluating how local behavior aligns with global
  evolutionary direction.

This makes UEOT more than a metaphysical proposal. It tries to become a usable
cross-domain analysis framework.

## What Distinguishes UEOT

UEOT is not just another appeal to "systems" or "complexity" in general terms.
Its distinctive moves are more specific.

- It treats **feedback topology as the condition of persistent existence**, not
  merely as a useful descriptive mechanism.
- It treats **openness as dynamically variable across an object's lifecycle**,
  rather than as a fixed label attached to a system forever.
- It tries to **naturalize teleology** by describing purpose as an attractor
  structure internal to the dynamics, rather than as something imposed from
  outside physics.
- It links local behavior to long-run development through an
  **RG-style evolutionary picture**, which is why the framework repeatedly
  moves between instantaneous dynamics and lifecycle-scale direction.
- It does not stop at philosophical synthesis; it attempts to supply
  **diagnostic tools and falsifiable research directions**.

## What the Manuscript Actually Does

The paper is broad in ambition, but it is organized around a clear progression.

- **Chapter 1**
  Frames the central fracture in modern knowledge: the gap between law-governed
  matter and purpose-laden life and mind. It situates UEOT in relation to
  systems theory, cybernetics, information-centric physics, autopoiesis, and
  related unification efforts.
- **Chapter 2**
  Introduces the core ontology and dynamics: Omega-loops, object taxonomy,
  the `\Pi/\Phi` principle, and the emergence of GOD and GOA.
- **Chapter 3**
  Turns the framework into a diagnostic program and applies it across domains,
  including biological evolution, mind dynamics, socioeconomic systems, and the
  problem of meaning, value, and will.
- **Chapter 4**
  Opens the long-range research agenda: mathematical formalization,
  reinterpretations of quantum mechanics and particle ontology, an
  emergent-information reading of general relativity, and decisive experimental
  proposals intended to make UEOT vulnerable to falsification.

## Why the Cross-Domain Case Studies Matter

One of the strongest structural features of the manuscript is that it does not
stop at abstract ontology. It repeatedly asks whether the same formal language
can diagnose very different systems.

- In **biology**, UEOT interprets evolution through adaptive optimization under
  the `\Pi/\Phi` tension.
- In **mind science**, it treats the self and consciousness as high-complexity,
  nested Omega-loop dynamics rather than mysterious exceptions to natural law.
- In **economics and social systems**, it frames bubbles, crises, coordination,
  and regulation as outcomes of multi-scale feedback structure and drive
  imbalance.
- In the domain of **meaning and value**, it advances the strongest and most
  controversial claim of the project: that purpose and meaning can be described
  naturalistically as dynamical relations between local trajectory and global
  attractor.

Whether or not one accepts all of these claims, the manuscript is best read as
an attempt to use one theoretical grammar across traditionally disconnected
levels of reality.

## Research Status

UEOT is presented here as a **research program**, not as a finished formal
theory with all equations settled. That distinction is important.

The manuscript already provides:

- a conceptual ontology of persistent objects
- a dynamical principle for evolution
- a cross-domain diagnostic vocabulary
- a set of conjectural bridges to fundamental physics
- explicit experimental directions intended to test or pressure the framework

The manuscript also openly leaves major tasks unfinished, especially full
mathematical formalization, derivation of predictive equations, and sharper
empirical benchmarks.

## Repository Contents

- [UEOT_v3_top.pdf](./UEOT_v3_top.pdf): compiled manuscript
- [UEOT_v3_top[1].zip](./UEOT_v3_top%5B1%5D.zip): LaTeX source archive
- [LICENSE](./LICENSE): license terms for repository-authored materials

## Build From Source

The source archive contains `main.tex`, bibliography data, and the supporting
template/style files used to build the manuscript.

Typical build flow:

```bash
unzip "UEOT_v3_top[1].zip" -d ueot-src
cd ueot-src
xelatex main.tex
bibtex main
xelatex main.tex
xelatex main.tex
```

If your TeX setup supports it, `latexmk` can be used as a wrapper around the
same compilation sequence.

## Citation

If you reference this work, please cite:

```text
Degui Qian. A Universal Evolutionary Object Theory (UEOT): A Framework and
Research Program for a Unified Science. 2025.
```

## License

The original manuscript and repository-authored materials are released under
the [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) license. This
includes the author-authored LaTeX source content. Bundled third-party class,
style, and bibliography-support files remain under their own respective
licenses.

## Contact

- Author: Degui Qian
- Email: `deven.qian@gmail.com`
