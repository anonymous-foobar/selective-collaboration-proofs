import Init.Data.Rat.Lemmas
import Init.GrindInstances.Ring.Rat
import LeanVerification.Metrics
import LeanVerification.VoteGame

set_option autoImplicit false

namespace LeanVerification

/-- Proof of Theorem 5 (cost-balance) from the anonymous paper.

The proof derives Lemma Ulv from `UtilityFromReward`, then rewrites both losses to
the delay profile and closes the reciprocal identity algebraically. -/
theorem costbalance
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (leaderProb : Player -> Rat)
  (R : RewardFn)
  (profiles : VoteProfiles σ)
  (i j : Player)
  (hUtilityFromReward : UtilityFromReward U pow leaderProb R profiles)
  (hVictimLossNZ : utilityLoss U i profiles.se (profiles.omission j i) ≠ 0)
  (hAttackerLossNZ : utilityLoss U j profiles.se (profiles.delay i j) ≠ 0) :
  costTargeted U j i profiles.se (profiles.omission j i)
    =
  1 / costTargeted U i j profiles.se (profiles.delay i j) := by
  let _ := hVictimLossNZ
  let _ := hAttackerLossNZ
  let hUlv : UlvProperty U profiles :=
    ulv_of_utilityFromReward U pow leaderProb R profiles hUtilityFromReward
  have hAttackerLossEq :
      utilityLoss U j profiles.se (profiles.omission j i)
        = utilityLoss U j profiles.se (profiles.delay i j) := by
    unfold utilityLoss
    rw [hUlv j i j]
  have hVictimLossEq :
      utilityLoss U i profiles.se (profiles.omission j i)
        = utilityLoss U i profiles.se (profiles.delay i j) := by
    unfold utilityLoss
    rw [hUlv j i i]
  calc
    costTargeted U j i profiles.se (profiles.omission j i)
      = utilityLoss U j profiles.se (profiles.omission j i)
          / utilityLoss U i profiles.se (profiles.omission j i) := by
            rfl
    _ = utilityLoss U j profiles.se (profiles.delay i j)
          / utilityLoss U i profiles.se (profiles.delay i j) := by
            rw [hAttackerLossEq, hVictimLossEq]
    _ = 1 / (utilityLoss U i profiles.se (profiles.delay i j)
          / utilityLoss U j profiles.se (profiles.delay i j)) := by
          rw [Rat.div_def, Rat.div_def, Rat.div_def]
          rw [Rat.one_mul, Rat.inv_mul_rev, Rat.inv_inv]
    _ = 1 / costTargeted U i j profiles.se (profiles.delay i j) := by
            rfl

/-- Proof of Theorem 7 (effectiveness-balance) from the anonymous paper.

The proof derives Lemma Ulv from `UtilityFromReward`, rewrites victim loss from
omission to the corresponding delay profile, and normalizes the rational identity. -/
theorem effbalance
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (leaderProb : Player -> Rat)
  (R : RewardFn)
  (profiles : VoteProfiles σ)
  (i j : Player)
  (hUtilityFromReward : UtilityFromReward U pow leaderProb R profiles)
  (hDenomNZ :
    effectivenessTargeted U pow i j profiles.se (profiles.delay i j) ≠ 0)
  (hVictimBaseNZ : U i profiles.se ≠ 0)
  (hAttackerPowerNZ : pow j ≠ 0)
  (hVictimPowerNZ : pow i ≠ 0) :
  effectivenessTargeted U pow j i profiles.se (profiles.omission j i)
    /
  effectivenessTargeted U pow i j profiles.se (profiles.delay i j)
    =
  costTargeted U i j profiles.se (profiles.delay i j)
    * ((U j profiles.se * pow i) / (U i profiles.se * pow j)) := by
  let _ := hDenomNZ
  let _ := hVictimBaseNZ
  let _ := hAttackerPowerNZ
  let _ := hVictimPowerNZ
  let hUlv : UlvProperty U profiles :=
    ulv_of_utilityFromReward U pow leaderProb R profiles hUtilityFromReward
  have hVictimLossEq :
      utilityLoss U i profiles.se (profiles.omission j i)
        = utilityLoss U i profiles.se (profiles.delay i j) := by
    unfold utilityLoss
    rw [hUlv j i i]
  calc
    effectivenessTargeted U pow j i profiles.se (profiles.omission j i)
      /
    effectivenessTargeted U pow i j profiles.se (profiles.delay i j)
      =
    (utilityLoss U i profiles.se (profiles.omission j i) / (U i profiles.se * pow j))
      /
    (utilityLoss U j profiles.se (profiles.delay i j) / (U j profiles.se * pow i)) := by
        rfl
    _ =
    (utilityLoss U i profiles.se (profiles.delay i j) / (U i profiles.se * pow j))
      /
    (utilityLoss U j profiles.se (profiles.delay i j) / (U j profiles.se * pow i)) := by
        rw [hVictimLossEq]
    _ =
    (utilityLoss U i profiles.se (profiles.delay i j)
        / utilityLoss U j profiles.se (profiles.delay i j))
      * ((U j profiles.se * pow i) / (U i profiles.se * pow j)) := by
        grind
    _ =
    costTargeted U i j profiles.se (profiles.delay i j)
      * ((U j profiles.se * pow i) / (U i profiles.se * pow j)) := by
        rfl

/-- Under the `omitDelay` profile, attacker loss decomposes into the sum of
the omission and delay attacker losses (same attacker/victim orientation). -/
theorem attackerLoss_omitDelay_eq_sum
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (leaderProb : Player -> Rat)
  (R : RewardFn)
  (profiles : VoteProfiles σ)
  (attacker victim : Player)
  (hUtilityFromReward : UtilityFromReward U pow leaderProb R profiles) :
  utilityLoss U attacker profiles.se (profiles.omitDelay attacker victim)
    =
  utilityLoss U attacker profiles.se (profiles.omission attacker victim)
    + utilityLoss U attacker profiles.se (profiles.delay attacker victim) := by
  unfold utilityLoss
  rw [hUtilityFromReward.se_eq attacker]
  rw [hUtilityFromReward.omitDelay_attacker_eq attacker victim]
  rw [hUtilityFromReward.omission_attacker_eq attacker victim]
  rw [hUtilityFromReward.delay_attacker_eq attacker victim]
  grind

/-- Under the `omitDelay` profile, victim loss decomposes into the sum of
the omission and delay victim losses (same attacker/victim orientation). -/
theorem victimLoss_omitDelay_eq_sum
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (leaderProb : Player -> Rat)
  (R : RewardFn)
  (profiles : VoteProfiles σ)
  (attacker victim : Player)
  (hUtilityFromReward : UtilityFromReward U pow leaderProb R profiles) :
  utilityLoss U victim profiles.se (profiles.omitDelay attacker victim)
    =
  utilityLoss U victim profiles.se (profiles.omission attacker victim)
    + utilityLoss U victim profiles.se (profiles.delay attacker victim) := by
  unfold utilityLoss
  rw [hUtilityFromReward.se_eq victim]
  rw [hUtilityFromReward.omitDelay_victim_eq attacker victim]
  rw [hUtilityFromReward.omission_victim_eq attacker victim]
  rw [hUtilityFromReward.delay_victim_eq attacker victim]
  grind

/-- Cost of the combined `omitDelay` strategy as ratio of summed losses.
This is the exact decomposition induced by `UtilityFromReward`. -/
theorem cost_omitDelay_as_sumRatio
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (leaderProb : Player -> Rat)
  (R : RewardFn)
  (profiles : VoteProfiles σ)
  (attacker victim : Player)
  (hUtilityFromReward : UtilityFromReward U pow leaderProb R profiles) :
  costTargeted U attacker victim profiles.se (profiles.omitDelay attacker victim)
    =
  (utilityLoss U attacker profiles.se (profiles.omission attacker victim)
      + utilityLoss U attacker profiles.se (profiles.delay attacker victim))
    /
    (utilityLoss U victim profiles.se (profiles.omission attacker victim)
      + utilityLoss U victim profiles.se (profiles.delay attacker victim)) := by
  have hAttackerSplit :=
    attackerLoss_omitDelay_eq_sum U pow leaderProb R profiles attacker victim hUtilityFromReward
  have hVictimSplit :=
    victimLoss_omitDelay_eq_sum U pow leaderProb R profiles attacker victim hUtilityFromReward
  unfold costTargeted
  rw [hAttackerSplit, hVictimSplit]

/-- Cost of `omitDelay` as a victim-loss-weighted average of omission and delay costs.

This shows the main relationship: `omitDelay` cost is not determined by the two
costs alone; it also depends on the victim-loss magnitudes that weight them. -/
theorem cost_omitDelay_weightedByVictimLoss
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (leaderProb : Player -> Rat)
  (R : RewardFn)
  (profiles : VoteProfiles σ)
  (attacker victim : Player)
  (hUtilityFromReward : UtilityFromReward U pow leaderProb R profiles)
  (hOmissionVictimLossNZ :
    utilityLoss U victim profiles.se (profiles.omission attacker victim) ≠ 0)
  (hDelayVictimLossNZ :
    utilityLoss U victim profiles.se (profiles.delay attacker victim) ≠ 0) :
  costTargeted U attacker victim profiles.se (profiles.omitDelay attacker victim)
    =
  ((costTargeted U attacker victim profiles.se (profiles.omission attacker victim)
      * utilityLoss U victim profiles.se (profiles.omission attacker victim))
    + (costTargeted U attacker victim profiles.se (profiles.delay attacker victim)
      * utilityLoss U victim profiles.se (profiles.delay attacker victim)))
    /
    (utilityLoss U victim profiles.se (profiles.omission attacker victim)
      + utilityLoss U victim profiles.se (profiles.delay attacker victim)) := by
  let _ := hOmissionVictimLossNZ
  let _ := hDelayVictimLossNZ
  let LAo := utilityLoss U attacker profiles.se (profiles.omission attacker victim)
  let LAd := utilityLoss U attacker profiles.se (profiles.delay attacker victim)
  let LVo := utilityLoss U victim profiles.se (profiles.omission attacker victim)
  let LVd := utilityLoss U victim profiles.se (profiles.delay attacker victim)
  have hCostSum :=
    cost_omitDelay_as_sumRatio U pow leaderProb R profiles attacker victim hUtilityFromReward
  have hNumerator :
      LAo + LAd = ((LAo / LVo) * LVo) + ((LAd / LVd) * LVd) := by
    grind [Rat.div_def]
  calc
    costTargeted U attacker victim profiles.se (profiles.omitDelay attacker victim)
      = (LAo + LAd) / (LVo + LVd) := by
          simpa [LAo, LAd, LVo, LVd] using hCostSum
    _ = (((LAo / LVo) * LVo) + ((LAd / LVd) * LVd)) / (LVo + LVd) := by
          exact congrArg (fun t => t / (LVo + LVd)) hNumerator
    _ = ((costTargeted U attacker victim profiles.se (profiles.omission attacker victim)
            * utilityLoss U victim profiles.se (profiles.omission attacker victim))
          + (costTargeted U attacker victim profiles.se (profiles.delay attacker victim)
            * utilityLoss U victim profiles.se (profiles.delay attacker victim)))
          /
          (utilityLoss U victim profiles.se (profiles.omission attacker victim)
            + utilityLoss U victim profiles.se (profiles.delay attacker victim)) := by
          rfl

/-- Cost of `omitDelay` as an effectiveness-weighted average of omission and delay costs.

This rewrites `cost_omitDelay_weightedByVictimLoss` using
`effectivenessTargeted = victimLoss / (U_v(se) * p_attacker)`. -/
theorem cost_omitDelay_weightedByEffectiveness
  {σ : Type}
  (U : Player -> σ -> Rat)
  (pow : Player -> Rat)
  (leaderProb : Player -> Rat)
  (R : RewardFn)
  (profiles : VoteProfiles σ)
  (attacker victim : Player)
  (hUtilityFromReward : UtilityFromReward U pow leaderProb R profiles)
  (hOmissionVictimLossNZ :
    utilityLoss U victim profiles.se (profiles.omission attacker victim) ≠ 0)
  (hDelayVictimLossNZ :
    utilityLoss U victim profiles.se (profiles.delay attacker victim) ≠ 0)
  (hVictimBaseNZ : U victim profiles.se ≠ 0)
  (hAttackerPowerNZ : pow attacker ≠ 0) :
  costTargeted U attacker victim profiles.se (profiles.omitDelay attacker victim)
    =
  ((costTargeted U attacker victim profiles.se (profiles.omission attacker victim)
      * effectivenessTargeted U pow attacker victim profiles.se
          (profiles.omission attacker victim))
    + (costTargeted U attacker victim profiles.se (profiles.delay attacker victim)
      * effectivenessTargeted U pow attacker victim profiles.se
          (profiles.delay attacker victim)))
    /
    (effectivenessTargeted U pow attacker victim profiles.se
        (profiles.omission attacker victim)
      + effectivenessTargeted U pow attacker victim profiles.se
          (profiles.delay attacker victim)) := by
  let _ := hOmissionVictimLossNZ
  let _ := hDelayVictimLossNZ
  let _ := hVictimBaseNZ
  let _ := hAttackerPowerNZ
  let B := U victim profiles.se * pow attacker
  have hBaseNZ : B ≠ 0 := by
    grind
  let LVo := utilityLoss U victim profiles.se (profiles.omission attacker victim)
  let LVd := utilityLoss U victim profiles.se (profiles.delay attacker victim)
  let Eo :=
    effectivenessTargeted U pow attacker victim profiles.se (profiles.omission attacker victim)
  let Ed :=
    effectivenessTargeted U pow attacker victim profiles.se (profiles.delay attacker victim)
  have hLVo : LVo = Eo * B := by
    unfold Eo effectivenessTargeted
    grind [Rat.div_def]
  have hLVd : LVd = Ed * B := by
    unfold Ed effectivenessTargeted
    grind [Rat.div_def]
  have hCostByLoss :=
    cost_omitDelay_weightedByVictimLoss
      U pow leaderProb R profiles attacker victim hUtilityFromReward
      hOmissionVictimLossNZ hDelayVictimLossNZ
  calc
    costTargeted U attacker victim profiles.se (profiles.omitDelay attacker victim)
      = ((costTargeted U attacker victim profiles.se (profiles.omission attacker victim)
            * LVo)
          + (costTargeted U attacker victim profiles.se (profiles.delay attacker victim)
            * LVd))
          /
          (LVo + LVd) := by
            simpa [LVo, LVd] using hCostByLoss
    _ = ((costTargeted U attacker victim profiles.se (profiles.omission attacker victim)
            * (Eo * B))
          + (costTargeted U attacker victim profiles.se (profiles.delay attacker victim)
            * (Ed * B)))
          /
          ((Eo * B) + (Ed * B)) := by
            rw [hLVo, hLVd]
    _ = ((costTargeted U attacker victim profiles.se (profiles.omission attacker victim)
            * Eo)
          + (costTargeted U attacker victim profiles.se (profiles.delay attacker victim)
            * Ed))
          /
          (Eo + Ed) := by
            let Co := costTargeted U attacker victim profiles.se (profiles.omission attacker victim)
            let Cd := costTargeted U attacker victim profiles.se (profiles.delay attacker victim)
            have hNumFactor :
                (Co * (Eo * B) + Cd * (Ed * B)) = (Co * Eo + Cd * Ed) * B := by
              grind [Rat.mul_assoc, Rat.mul_comm]
            have hDenFactor :
                ((Eo * B) + (Ed * B)) = (Eo + Ed) * B := by
              grind [Rat.mul_assoc, Rat.mul_comm]
            rw [hNumFactor, hDenFactor]
            have hCancelB :
                ((Co * Eo + Cd * Ed) * B) / ((Eo + Ed) * B)
                  = (Co * Eo + Cd * Ed) / (Eo + Ed) := by
              have hCancelRight : ∀ {c x y : Rat}, c ≠ 0 → (x * c) / (y * c) = x / y := by
                intro c x y hc
                grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]
              simpa [Rat.mul_assoc, Rat.mul_comm] using
                (hCancelRight (c := B) (x := (Co * Eo + Cd * Ed)) (y := (Eo + Ed)) hBaseNZ)
            simpa [Co, Cd] using hCancelB
    _ = ((costTargeted U attacker victim profiles.se (profiles.omission attacker victim)
            * effectivenessTargeted U pow attacker victim profiles.se
                (profiles.omission attacker victim))
          + (costTargeted U attacker victim profiles.se (profiles.delay attacker victim)
            * effectivenessTargeted U pow attacker victim profiles.se
                (profiles.delay attacker victim)))
          /
          (effectivenessTargeted U pow attacker victim profiles.se
              (profiles.omission attacker victim)
            + effectivenessTargeted U pow attacker victim profiles.se
                (profiles.delay attacker victim)) := by
            rfl

end LeanVerification
