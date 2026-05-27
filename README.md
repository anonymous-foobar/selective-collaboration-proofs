> **Disclaimer:** Repository content was mainly AI-generated. The models, assumptions, and theorems were manually and carefully reviewed.

# Lean Verification

This artifact formalizes the core game-theoretic model and proofs from the accompanying anonymous paper.

Primary paper references used in this repository:
- Section 2 (system model and utility/effectiveness/cost definitions)
- Section 3 (vote-collection game semantics)
- Equation (1): effectiveness definition
- Equation (2): cost definition
- Equations (3)-(5): utility equations in the vote-collection game
- Theorem 5: cost-balance relationship
- Theorem 7: effectiveness-balance relationship

Current scope:
- model and metric definitions
- targeted attack profiles for omission and delay
- paper proofs formalized in Lean:
  - Lemma 4 is proven as [ulv_of_utilityFromReward](LeanVerification/VoteGame.lean#L104)
  - Theorem 5 is proven as [costbalance](LeanVerification/CoreResults.lean#L14)
  - Theorem 7 is proven as [effbalance](LeanVerification/CoreResults.lean#L61)
- additional formalization details (not explicit paper theorems):
  - utility semantics are specified in detail via [UtilityFromReward](LeanVerification/VoteGame.lean#L23)
  - cost and effectiveness of the combined attack (omission and delay) are related to the other attacks in [cost_omitDelay_as_sumRatio](LeanVerification/CoreResults.lean#L178) and [cost_omitDelay_weightedByEffectiveness](LeanVerification/CoreResults.lean#L244)


Ethereum/Cosmos/Harmony-specific derivations are out of scope.


## Build

```bash
lake build
```

## Layout

- `LeanVerification/Model.lean`: core game primitives
- `LeanVerification/Metrics.lean`: utility loss, effectiveness, cost
- `LeanVerification/VoteGame.lean`: core vote-game attack profile abstraction
- `LeanVerification/CoreResults.lean`: Ulv lemma and balance theorem contracts


## Status

Theorem proves have been verified in Lean.
