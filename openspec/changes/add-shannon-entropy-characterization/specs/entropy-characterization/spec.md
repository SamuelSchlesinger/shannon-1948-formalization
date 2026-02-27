## ADDED Requirements

### Requirement: Shannon Axiom Interface
The system SHALL define a formal interface for Shannon's three axioms over finite probability distributions: 1) continuity in probabilities, 2) monotonic increase on uniform distributions `(1/n, ..., 1/n)`, and 3) grouping/decomposition as a weighted sum over successive choices.

#### Scenario: Axiom bundle can be instantiated
- **WHEN** a candidate finite-distribution uncertainty function `H` is provided
- **THEN** each of the three Shannon axioms is expressible and checkable as Lean
  propositions attached to `H`

### Requirement: Base-Parametric Uniqueness Theorem
The system SHALL provide a theorem that for any fixed logarithm base `b > 1`, every `H` satisfying Shannon's three axioms has the form `H(p) = -K * sum p_i * log_b p_i` for some positive constant `K`.

#### Scenario: Uniqueness theorem applies to an axiom-satisfying H
- **WHEN** a base `b > 1` and an `H` satisfying all three axioms are given
- **THEN** Lean can derive existence of `K > 0` and the entropy-form equation
  for all finite probability distributions in scope

### Requirement: Appendix 2 Proof Structure
The system SHALL expose intermediate lemmas that mirror Shannon Appendix 2: equiprobable reduction, rational-probability derivation, and continuity-based extension to real probabilities.

#### Scenario: Proof steps are individually inspectable
- **WHEN** a learner reads theorem dependencies in the entropy characterization
  module
- **THEN** they can trace a clear path from the three axioms to the final
  entropy formula through the same three phases as Appendix 2

### Requirement: Worked Decomposition Example
The system SHALL include a formal worked decomposition example equivalent to Shannon's three-way split `(1/2, 1/3, 1/6)`, showing the weighted-sum property for successive choices.

#### Scenario: Example demonstrates the grouping axiom concretely
- **WHEN** the example theorem is evaluated in the module docs or code
- **THEN** the weighted composition identity is explicit and type-checked
