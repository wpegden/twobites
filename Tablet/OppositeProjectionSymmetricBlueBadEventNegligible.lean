import Tablet.NegligibleProbability
import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteSample
import Tablet.OppositeProjectionBlueConditioning
import Tablet.OppositeProjectionBlueExposureTailBound
import Tablet.OppositeProjectionAsymptoticBound
import Tablet.OppositeProjectionIntersectionContainment
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.OppositeProjectionSymmetricBlueBadEventExponentialBound
import Tablet.TwoBiteEventProbabilityNonnegative

-- [TABLET NODE: OppositeProjectionSymmetricBlueBadEventNegligible]

theorem OppositeProjectionSymmetricBlueBadEventNegligible :
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        NegligibleProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                let sizeBound : Prop :=
                  ∀ x : TwoBiteBaseVertex (m n),
                  ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                    2 * TwoBiteEdgeProbability β n * (n : ℝ)
                let blueBad : Prop :=
                  ∃ b c : Fin (m n), b ≠ c ∧
                  (((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                        (TwoBiteRedProjection ω)) ∩
                      ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                        (TwoBiteRedProjection ω))).card : ℝ)
                    >
                    (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                        TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
                      100 * (Real.log (n : ℝ)) ^ 3))
                sizeBound ∧ blueBad)) := by
-- BODY
  classical
  intro β hβ m hm
  subst β
  unfold NegligibleProbability
  rcases OppositeProjectionSymmetricBlueBadEventExponentialBound m hm with ⟨c, hc, hbound⟩
  have hnonneg :
      ∀ᶠ n in Filter.atTop,
        (0 : ℝ) ≤
          TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability (1 / 2 : ℝ) n)
            (fun ω =>
              let sizeBound : Prop :=
                ∀ x : TwoBiteBaseVertex (m n),
                ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                  2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
              let blueBad : Prop :=
                ∃ b c : Fin (m n), b ≠ c ∧
                (((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                      (TwoBiteRedProjection ω)) ∩
                    ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                      (TwoBiteRedProjection ω))).card : ℝ)
                  >
                  (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
                    100 * (Real.log (n : ℝ)) ^ 3))
              sizeBound ∧ blueBad) := by
    filter_upwards [OppositeProjectionEdgeProbBounds] with n hp
    exact TwoBiteEventProbabilityNonnegative hp.1 hp.2 _
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (OppositeProjectionAsymptoticBound c hc m hm) hnonneg hbound
