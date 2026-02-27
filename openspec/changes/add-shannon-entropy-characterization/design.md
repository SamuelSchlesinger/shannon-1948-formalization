## Context
Section 6 of Shannon (1948) introduces three axioms for a finite-choice
uncertainty measure `H(p_1, ..., p_n)`:
1) continuity in probabilities, 2) monotonic growth on uniform
`(1/n, ..., 1/n)`, and 3) decomposition into successive choices via weighted
sum.

Appendix 2 gives the derivation strategy:
- show `A(n) = H(1/n, ..., 1/n)` behaves like `K * log n`,
- derive entropy form for rational probabilities using grouped equiprobable
  outcomes,
- extend to all real probabilities by continuity.

The project requires this formalization to teach, not only certify. The Lean
artifact should preserve Shannon's proof narrative.

## Goals / Non-Goals
- Goals:
  - Formalize the three Shannon axioms for finite distributions.
  - Prove the base-parametric uniqueness theorem:
    for fixed `b > 1`, `H(p) = -K * sum p_i * log_b p_i` for some `K > 0`.
  - Organize lemmas to mirror Appendix 2 proof steps.
  - Include a worked decomposition example (`1/2, 1/3, 1/6`) as an explanatory
    theorem.
- Non-Goals:
  - Proving downstream coding theorems (Theorems 3+).
  - Infinite alphabets or measure-theoretic entropy.
  - Optimization of proof brevity over readability.

## Decisions
- Decision: model a finite distribution as `Fin n -> Real` with explicit
  simplex constraints (`0 <= p i` and `sum p = 1`).
  - Why: this makes finite combinatorics and Appendix 2 decomposition direct.
  - Alternative considered: mathlib `PMF`.
    - Tradeoff: `PMF` is elegant but introduces additional abstraction that may
      obscure the pedagogical mapping to Shannon's notation.

- Decision: define an axiom bundle structure `ShannonEntropyAxioms` over a
  candidate `H`.
  - Why: keeps theorem statements clear and lets each axiom be reused in
    intermediate lemmas.

- Decision: parameterize the final theorem by logarithm base `b > 1`.
  - Why: user requirement is "any base"; this avoids locking to bits/nats while
    preserving the "change of base is a scale factor" interpretation.

- Decision: formal proof decomposition will follow Appendix 2 in three phases.
  - Phase 1: equiprobable case (`A(sm) = m * A(s)` and `A(n) = K * log n`).
  - Phase 2: rational probabilities (`p_i = n_i / sum n_i`) from grouped
    equiprobable outcomes.
  - Phase 3: real probabilities from continuity and rational approximation.
  - Why: this is the core "illustrate truth" requirement.

- Decision: include named pedagogical lemmas and one worked decomposition
  theorem matching Shannon's Figure 6 arithmetic identity.
  - Why: preserves explanatory value for learners reading the proof.

## Risks / Trade-offs
- Risk: continuity on simplex boundary (`p_i = 0`) can complicate log
  expressions.
  - Mitigation: define theorem statements carefully (interior first if needed),
    then extend with continuity and conventional `0 * log 0 = 0` handling.

- Risk: excessive abstraction could hide the Shannon argument.
  - Mitigation: keep a direct finite-index formulation and explicit "phase"
    theorem names.

- Risk: proof may become long before user-facing value appears.
  - Mitigation: milestone tasks produce intermediate theorems that already
    explain parts of the argument.

## Migration Plan
1. Add/confirm mathlib dependency.
2. Add entropy foundation definitions and axioms.
3. Prove phase lemmas in Appendix 2 order.
4. Assemble final uniqueness theorem and worked example.
5. Export from `Shannon.lean`.

## Open Questions
- Normalization policy: resolved for this change. Keep constant `K` abstract
  because this theorem characterizes the entropy family up to positive scale.
  Choosing a normalization (e.g., `H(1/2, 1/2) = 1`) is a separate unit
  convention, intentionally out of scope here.
- Module granularity: keep everything in `Shannon/Entropy.lean` initially, or
  split to `Shannon/Entropy/Axioms.lean` and
  `Shannon/Entropy/Characterization.lean` once proof grows.
