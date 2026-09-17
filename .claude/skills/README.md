# Agent skills

Skills vendored from the official Lean skills repository,
<https://github.com/leanprover/skills> (Apache-2.0), at commit
`7d3da0282e7b724b07620e45cf212f2e05e19334` (2026-02-21). Files are unmodified
copies of `skills/<name>/SKILL.md`.

| Skill        | Why it is here                                                        |
|--------------|-----------------------------------------------------------------------|
| `lean-proof` | Proof methodology: one tactic at a time, error priority, hardest case first. |
| `lean-mwe`   | Minimising a Lean error into a self-contained bug report for lean4 / Mathlib. |

Not vendored: `lean-setup`, `lean-bisect`, `lean-pr`, `nightly-testing`
(for working on the lean4 compiler itself), `mathlib-pr`, `mathlib-review`
(for contributing to Mathlib) and `mathlib-build` (its build targets are
Mathlib's own, not this project's).

To refresh, re-copy the two `SKILL.md` files from upstream and bump the commit
above. Project rules in `AGENTS.md` take precedence where they overlap.
