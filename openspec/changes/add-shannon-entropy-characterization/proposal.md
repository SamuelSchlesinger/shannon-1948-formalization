# Change: Add Shannon Entropy Characterization Proposal

## Why
The project goal is to learn information theory by formalizing core results in Lean.
Shannon's Theorem 2 and Appendix 2 give a canonical uniqueness result for entropy:
the three axioms (continuity, monotonic growth on uniform distributions, and the
grouping/composition law) force the form `H = -K * sum p_i * log p_i`.

Formalizing this theorem will provide a foundational result for all later entropy
and coding theorems, while also matching the project's pedagogical emphasis:
the proof should show why the formula is true, not only that Lean accepts it.

## What Changes
- Add a new `entropy-characterization` capability spec.
- Specify an implementation that formalizes Shannon's three axioms for finite
  discrete distributions.
- Specify a base-parametric uniqueness theorem (`b > 1`) with a positive scale
  constant `K`.
- Require the formal proof structure to mirror Appendix 2:
  equal-probability lemma, rational-probability reduction, and continuity
  extension to real probabilities.
- Require an explicit formal worked example of the decomposition law for
  probabilities `(1/2, 1/3, 1/6)` to support explanation and learning.

## Impact
- Affected specs: `entropy-characterization` (new)
- Affected code:
  - `Shannon/Entropy.lean` (or split modules under `Shannon/Entropy/`)
  - `Shannon.lean` exports
  - `lakefile.toml` and `lake-manifest.json` if mathlib setup changes are needed
- Dependencies:
  - mathlib finite sums, real logarithms, continuity lemmas, rational
    approximation tools
