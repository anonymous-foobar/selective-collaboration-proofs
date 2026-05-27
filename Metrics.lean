import LeanVerification.Model

set_option autoImplicit false

namespace LeanVerification

/-- Utility loss of player `p` when moving from designated strategy `se` to attack profile `sa`. -/
def utilityLoss
  {σ : Type}
  (U : Player -> σ -> Rat)
  (p : Player)
  (se sa : σ) : Rat :=
  U p se - U p sa

/-- Targeted effectiveness used in the vote-game section.
  This follows Equation (1) in the anonymous paper without the max-operator,
  assuming a targeted victim. -/
def effectivenessTargeted
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (attacker victim : Player)
  (se sa : σ) : Rat :=
  utilityLoss U victim se sa / (U victim se * pow attacker)

/-- Targeted attack cost ratio used in the vote-game section.
  This follows Equation (2) in the anonymous paper without the max-operator,
  assuming a targeted victim. -/
def costTargeted
  {σ : Type}
  (U : Player -> σ -> Rat)
  (attacker victim : Player)
  (se sa : σ) : Rat :=
  utilityLoss U attacker se sa / utilityLoss U victim se sa

end LeanVerification
