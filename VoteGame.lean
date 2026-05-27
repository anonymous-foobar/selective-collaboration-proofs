import LeanVerification.Model

set_option autoImplicit false

namespace LeanVerification

/-- Reward-function type from the vote-game model in the anonymous paper (Section 3):
`R(delta_l, delta_i, power_i, powersum)` with boolean indicators for `delta_l` and `delta_i`. -/
abbrev RewardFn := Bool -> Bool -> Rat -> Rat -> Rat

/-- Core attack profiles needed for omission and delay results. -/
structure VoteProfiles (Profile : Type) where
  se : Profile
  omission : Player -> Player -> Profile
  delay : Player -> Player -> Profile
  omitDelay : Player -> Player -> Profile

/-- Paper-faithful semantic assumptions that connect utilities to a reward function and
leader-election probabilities for the vote collection game.

This encodes all role-specific utility equations needed for omission, delay,
and the combined omit+delay strategy: attacker, victim, and bystander. -/
structure UtilityFromReward
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (leaderProb : Player -> Rat)
  (R : RewardFn)
  (profiles : VoteProfiles σ) : Prop where
  se_eq :
    ∀ i : Player,
      U i profiles.se
        = leaderProb i * R true true (pow i) 1
          + (1 - leaderProb i) * R false true (pow i) 1
  omission_attacker_eq :
    ∀ attacker victim : Player,
      U attacker (profiles.omission attacker victim)
        = leaderProb attacker * R true true (pow attacker) (1 - pow victim)
          + (1 - leaderProb attacker) * R false true (pow attacker) 1
  omission_victim_eq :
    ∀ attacker victim : Player,
      U victim (profiles.omission attacker victim)
        = leaderProb victim * R true true (pow victim) 1
          + leaderProb attacker * R false false (pow victim) (1 - pow victim)
          + (1 - leaderProb attacker - leaderProb victim) * R false true (pow victim) 1
  omission_bystander_eq :
    ∀ attacker victim bystander : Player,
      bystander ≠ attacker -> bystander ≠ victim ->
      U bystander (profiles.omission attacker victim)
        = leaderProb bystander * R true true (pow bystander) 1
          + leaderProb attacker * R false true (pow bystander) (1 - pow victim)
          + (1 - leaderProb bystander - leaderProb attacker) * R false true (pow bystander) 1
  delay_attacker_eq :
    ∀ attacker victim : Player,
      U attacker (profiles.delay attacker victim)
        = leaderProb attacker * R true true (pow attacker) 1
          + leaderProb victim * R false false (pow attacker) (1 - pow attacker)
          + (1 - leaderProb victim - leaderProb attacker) * R false true (pow attacker) 1
  delay_victim_eq :
    ∀ attacker victim : Player,
      U victim (profiles.delay attacker victim)
        = leaderProb victim * R true true (pow victim) (1 - pow attacker)
          + (1 - leaderProb victim) * R false true (pow victim) 1
  delay_bystander_eq :
    ∀ attacker victim bystander : Player,
      bystander ≠ attacker -> bystander ≠ victim ->
      U bystander (profiles.delay attacker victim)
        = leaderProb bystander * R true true (pow bystander) 1
          + leaderProb victim * R false true (pow bystander) (1 - pow attacker)
          + (1 - leaderProb bystander - leaderProb victim) * R false true (pow bystander) 1
  omitDelay_attacker_eq :
    ∀ attacker victim : Player,
      U attacker (profiles.omitDelay attacker victim)
        = leaderProb attacker * R true true (pow attacker) (1 - pow victim)
          + leaderProb victim * R false false (pow attacker) (1 - pow attacker)
          + (1 - leaderProb attacker - leaderProb victim) * R false true (pow attacker) 1
  omitDelay_victim_eq :
    ∀ attacker victim : Player,
      U victim (profiles.omitDelay attacker victim)
        = leaderProb victim * R true true (pow victim) (1 - pow attacker)
          + leaderProb attacker * R false false (pow victim) (1 - pow victim)
          + (1 - leaderProb attacker - leaderProb victim) * R false true (pow victim) 1
  omitDelay_bystander_eq :
    ∀ attacker victim bystander : Player,
      bystander ≠ attacker -> bystander ≠ victim ->
      U bystander (profiles.omitDelay attacker victim)
        = leaderProb bystander * R true true (pow bystander) 1
          + leaderProb attacker * R false true (pow bystander) (1 - pow victim)
          + leaderProb victim * R false true (pow bystander) (1 - pow attacker)
          + (1 - leaderProb bystander - leaderProb attacker - leaderProb victim)
              * R false true (pow bystander) 1

/-- Paper Lemma Ulv abstraction:
    utility under omission attack `S^l_{j -> i}` equals utility under delay attack `S^v_{i -> j}`. -/
def UlvProperty
  {σ : Type}
  (U : Player -> σ -> Rat)
  (profiles : VoteProfiles σ) : Prop :=
  ∀ (attacker victim r : Player),
    U r (profiles.omission attacker victim) = U r (profiles.delay victim attacker)

/-- The utility equations induced by `UtilityFromReward` imply Lemma Ulv.
The proof is a case split on whether `r` is the attacker, the victim, or a bystander. -/
theorem ulv_of_utilityFromReward
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (leaderProb : Player -> Rat)
  (R : RewardFn)
  (profiles : VoteProfiles σ)
  (hUtility : UtilityFromReward U pow leaderProb R profiles) :
  UlvProperty U profiles := by
  intro attacker victim r
  by_cases hr_attacker : r = attacker
  · subst r
    rw [hUtility.omission_attacker_eq attacker victim]
    rw [hUtility.delay_victim_eq victim attacker]
  · by_cases hr_victim : r = victim
    · subst r
      rw [hUtility.omission_victim_eq attacker victim]
      rw [hUtility.delay_attacker_eq victim attacker]
    · rw [hUtility.omission_bystander_eq attacker victim r hr_attacker hr_victim]
      rw [hUtility.delay_bystander_eq victim attacker r hr_victim hr_attacker]

theorem ulv
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (leaderProb : Player -> Rat)
  (R : RewardFn)
  (profiles : VoteProfiles σ)
  (hUtility : UtilityFromReward U pow leaderProb R profiles)
  (attacker victim r : Player) :
  U r (profiles.omission attacker victim) = U r (profiles.delay victim attacker) :=
  ulv_of_utilityFromReward U pow leaderProb R profiles hUtility attacker victim r

end LeanVerification
