# Issue #100 — Persistent GitOps Agent Runtime v3

## Goal

Make long-running UEOT development survive ordinary ChatGPT conversation limits without requiring the user to reconstruct context, while minimizing reliance on agentic Work/Codex resources.

A fresh ordinary Chat must recover the exact next action from GitHub alone. Repository AI is authorized to complete the full development lifecycle, including integration into `main`, while preserving independent review, base-anchored trust and auditable rollback.

## v3 architecture

- Primary execution: ordinary ChatGPT Chat + GitHub connector.
- Deterministic execution/verification: GitHub Actions.
- Primary continuation: fresh ordinary Chat + `/ueot-resume`.
- Authorization: trust policy from PR base / integrated main, never candidate HEAD.
- Merge authority: AI-autonomous under evidence gates.
- Normal integration: branch -> PR -> CI/elevated review -> independent PASS -> AI merge.
- Direct-main exception: recovery or explicitly justified maintenance only.
- Optional Work Event/Heartbeat and Codex remain disabled by default.

## Success criteria

1. Repository truth/Issue/state hierarchy is explicit and compatible with branch governance.
2. Builder and Reviewer have separate bounded protocols; Builder cannot self-approve.
3. State is machine-validated with bounded retry/loop guards and explicit AI merge authority.
4. Disabling Work/Event/Heartbeat/Codex does not make an active task unrecoverable.
5. A fresh ordinary Chat can reconstruct the task and execute exactly one correct bounded next transition from GitHub alone.
6. Reviewer authorization and ordinary protected CI resolve from PR base / integrated trust policy, not candidate HEAD/state.
7. Trust/runtime/protected-input changes route to independent elevated review instead of relying on mutable candidate CI semantics.
8. Protected Lean build semantics cannot be silently weakened while retaining an ordinary protected green gate.
9. Structured signal/review identity binds exact `(base_sha, head_sha)`; base movement invalidates old evidence and arbitrary markers cannot suppress trusted relay output.
10. Repository-owner GitHub authorization can establish initial bootstrap authority without allowing candidate policy to self-authorize.
11. Current-pair PASS plus applicable CI/elevated-review evidence permits AI to merge with `expected_head_sha` and then validate resulting `main`.
12. Direct-main authority exists but is constrained to explicit recovery/maintenance exceptions with recorded validation and rollback plans.

## Non-goals

- Removing ChatGPT product limits.
- Keeping one conversation alive indefinitely.
- Requiring Work/Codex for correctness or recovery.
- Letting Builder approve its own implementation.
- Treating candidate policy as its own trust root.
- Force-rewriting repository history as a normal repair technique.
- Storing chain-of-thought, full logs or large diffs in task state.
