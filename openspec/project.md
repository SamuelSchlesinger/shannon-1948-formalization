# Project Context

## Purpose
This project is a collaborative learning effort to formalize ideas from Claude
Shannon's 1948 information theory paper in Lean 4.
Goals:
- Build definitions and proofs incrementally, with readable proof scripts.
- Learn theorem proving and information theory together.
- Keep project decisions explicit with OpenSpec.

## Tech Stack
- Lean 4 (`leanprover/lean4:v4.28.0`)
- Lake build tool (`lakefile.toml`)
- Mathlib (allowed dependency)
- OpenSpec for planning and spec documentation (`openspec/`)
- Reference artifact: `shannon1948.pdf`

## Project Conventions

### Code Style
- Prefer readable, instructional proofs over overly compact proof golf.
- Use clear, descriptive names for definitions and lemmas.
- Keep modules focused on one concept at a time (for example: entropy,
  probability mass functions).
- Add short comments only when they clarify non-obvious mathematical intent.

### Architecture Patterns
- Organize formalization by concept under `Shannon/` (for example
  `Shannon/Entropy.lean`).
- Use `Shannon.lean` as the main import surface for the library.
- Develop in layers: definitions first, helper lemmas second, main theorems
  third.
- Keep abstractions simple unless reuse pressure clearly justifies complexity.

### Testing Strategy
- Treat successful `lake build` as the baseline correctness gate.
- Add small sanity-check lemmas/examples as concepts are introduced.
- When fixing a mistake, add a lemma/theorem that would have caught it
  (regression check).

### Git Workflow
- Commit directly to `main` (no branch/PR requirement for this project).
- Prefer small, focused commits with clear messages.
- Keep commits coherent: one conceptual change per commit when possible.

## Domain Context
- Domain: mathematical information theory inspired by Shannon (1948).
- Primary near-term focus: entropy and related foundational definitions.
- The project balances mathematical faithfulness with Lean-friendly
  formalization choices.

## Important Constraints
- Learning value and readability are prioritized over maximal generality.
- Dependencies should be introduced intentionally; `mathlib` is allowed when
  it improves clarity or progress.
- Non-trivial planned changes should go through OpenSpec proposals.

## External Dependencies
- Lean 4 toolchain pinned in `lean-toolchain`
- Lake for build/package management
- Mathlib (when added to support formalization)
- No external runtime services or APIs
