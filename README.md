# Shannon Entropy Characterization in Lean

![Lean](https://img.shields.io/badge/Lean-4.28.0-0f766e)
![License: MIT](https://img.shields.io/badge/License-MIT-2563eb)

This repository formalizes Shannon's finite-alphabet characterization theorem
from Shannon (1948), Appendix 2.

The central result is:

- For any uncertainty functional `H` satisfying the Shannon-style axiom bundle
  (continuity, strict monotonicity on uniform distributions, grouping, and
  relabel invariance), there is a positive constant `K` such that
  `H(p) = -K * Σ p_i log p_i`.
- Equivalently, for any base `b > 1`, there is `Kb > 0` such that
  `H(p) = -Kb * Σ p_i log_b p_i`.

## Formalization Scope

- Finite alphabets only.
- Real-valued probability vectors with explicit simplex proofs.
- Proof structure follows Shannon's Appendix-2 phases:
  1. Equiprobable case (`A(n)` behaves logarithmically).
  2. Rational probabilities via grouped equiprobable refinement.
  3. Extension to real probabilities via continuity and rational approximation.

## Main Theorems

### Characterization (Appendix 2)

- `entropyNat_unique`: `Shannon/Entropy/Final.lean`
- `entropyBase_unique`: `Shannon/Entropy/Final.lean`

### Section 6 Properties

- `entropyNat_eq_zero_iff`: H = 0 iff deterministic — `Shannon/Entropy/Properties.lean`
- `entropyNat_eq_log_card_iff`: H = log|α| iff uniform — `Shannon/Entropy/Properties.lean`
- `entropyNat_joint_le_add`: subadditivity H(X,Y) ≤ H(X) + H(Y) — `Shannon/Entropy/Properties.lean`
- `entropyNat_doublyStochastic_le`: Schur-concavity H(Ap) ≥ H(p) — `Shannon/Entropy/Properties.lean`
- `condEntropy_le_entropyNat`: conditioning reduces entropy — `Shannon/Entropy/Properties.lean`
- `condEntropy_nonneg`: conditional entropy ≥ 0 — `Shannon/Entropy/Properties.lean`
- `chain_rule`: H(X,Y) = H(X) + H_X(Y) — `Shannon/Entropy/Joint.lean`
- `entropyNat_prodDist`: H(X×Y) = H(X) + H(Y) — `Shannon/Entropy/Joint.lean`

## Module Layout

- `Shannon/Entropy/Core.lean`
  Foundations: probability distributions, axiom bundle, core constructions.
- `Shannon/Entropy/Uniform.lean`
  Phase 1: equiprobable characterization.
- `Shannon/Entropy/Rational.lean`
  Phase 2: rational case + worked `(1/2, 1/3, 1/6)` grouping example.
- `Shannon/Entropy/Approx.lean`
  Phase 3: floor-count rational approximants and convergence lemmas.
- `Shannon/Entropy/Final.lean`
  Final uniqueness theorems.
- `Shannon/Entropy/Gibbs.lean`
  Gibbs inequality, negMulLog bridge, entropy nonnegativity, uniform entropy.
- `Shannon/Entropy/Joint.lean`
  Joint distributions, marginals, conditional entropy, chain rule.
- `Shannon/Entropy/Properties.lean`
  Section 6 properties: deterministic iff, uniform iff, subadditivity, Schur-concavity, conditioning.
- `Shannon/Entropy.lean`
  Facade import.
- `Shannon.lean`
  Project entrypoint.

## How To Read The Proof

If you want to read this like a paper:

1. Start in `Shannon/Entropy/Core.lean` for definitions and axioms.
2. Read `Shannon/Entropy/Uniform.lean` for the equiprobable logarithm law
   (`Apos H n = K * log n`).
3. Read `Shannon/Entropy/Rational.lean` for rational distributions via grouping.
4. Read `Shannon/Entropy/Approx.lean` for the continuity bridge
   (`approxProb p N → p`).
5. Finish in `Shannon/Entropy/Final.lean` for the final uniqueness theorems.
6. Continue to `Shannon/Entropy/Gibbs.lean` for the Gibbs inequality.
7. Read `Shannon/Entropy/Joint.lean` for joint distributions and the chain rule.
8. Read `Shannon/Entropy/Properties.lean` for the Section 6 entropy properties.

For pedagogical context, see the worked decomposition theorem in
`Shannon/Entropy/Rational.lean`:

- `worked_grouping_identity`
- `workedCompose_masses`

## Build and Verify

Requirements:

- Lean toolchain from `lean-toolchain`
- Lake (bundled with Lean)

Commands:

```bash
lake build
```

CI workflow:

- `.github/workflows/lean_action_ci.yml` (`Lean Action CI`)

## Notes on Axioms

Shannon's symmetry principle ("depends only on probabilities, not labels") is
represented explicitly as:

- `ShannonEntropyAxioms.relabelInvariant`

This makes permutation/relabeling steps fully explicit in Lean proofs.

## Reference

- Claude E. Shannon, *A Mathematical Theory of Communication* (1948).
  The repository includes `shannon1948.pdf` for study context.

## License

This project is licensed under the MIT License. See `LICENSE`.
