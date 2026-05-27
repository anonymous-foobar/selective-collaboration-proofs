set_option autoImplicit false

namespace LeanVerification

/-- Explicit player type used by the formalization. -/
structure Player where
  id : Nat
deriving DecidableEq, Repr

/-- Core aliases used throughout the artifact. -/
abbrev PowerFn := Player -> Rat

/-- A normal-form game abstraction specialized to what we need in this artifact. -/
structure Game where
  StrategyProfile : Type
  utility : Player -> StrategyProfile -> Rat
  power : PowerFn

/-- Strategy profile aliases mirroring paper notation. -/
structure CoreProfiles (Profile : Type) where
  se : Profile
  sa : Profile

end LeanVerification
