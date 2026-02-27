## 1. Foundations
- [ ] 1.1 Add or confirm mathlib dependency and imports needed for finite sums,
  real logarithms, and continuity tools.
- [ ] 1.2 Define finite probability vectors and simplex constraints used by the
  theorem statements.
- [ ] 1.3 Define the Shannon axiom bundle (continuity, uniform monotonicity,
  grouping/decomposition).

## 2. Appendix 2 Proof Phases
- [ ] 2.1 Formalize the equiprobable case `A(n) = H(1/n, ..., 1/n)` and prove
  multiplicative decomposition lemmas (`A(sm) = m * A(s)`, `A(t^n) = n * A(t)`).
- [ ] 2.2 Prove `A(n) = K * log n` with `K > 0` from monotonicity and
  decomposition.
- [ ] 2.3 Prove entropy form for rational probabilities using grouped
  equiprobable refinement.
- [ ] 2.4 Extend rational result to real probabilities using continuity and
  approximation.

## 3. Final Statement and Pedagogy
- [ ] 3.1 State and prove the base-parametric uniqueness theorem for fixed
  `b > 1`:
  `H(p) = -K * sum p_i * log_b p_i`.
- [ ] 3.2 Add named pedagogical bridge lemmas matching Appendix 2 steps so the
  proof narrative is readable.
- [ ] 3.3 Add the explicit decomposition example for `(1/2, 1/3, 1/6)` and
  verify the weighted-sum identity.

## 4. Validation
- [ ] 4.1 Run `lake build` successfully.
- [ ] 4.2 Add a minimal theorem index comment or doc block summarizing the proof
  roadmap for learners.
