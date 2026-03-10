---
name: ueot-constitution-loader
description: Load the minimum UEOT constitutional context before any theory work. Use when an agent is about to analyze, extend, or summarize UEOT and needs the non-negotiable core plus the relevant extracted source files.
---

# UEOT Constitution Loader

Use this skill before any substantive UEOT reasoning.

## Load Order

1. `constitution/UEOT_CONSTITUTION.md`
2. `constitution/UEOT_METHOD.md`
3. `constitution/UEOT_GLOSSARY.md`
4. The relevant file from `source/extracted/`

## Rules

- Treat the original paper as the baseline constitution.
- Do not rewrite canon silently.
- Escalate potential core-theory changes into RFC + architect resolution flow.

## References

- See [references/load-order.md](references/load-order.md)
