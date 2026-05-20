import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.UniformInjectionWeight
import Tablet.GnpGraphWeight
import Tablet.WithHighProbability
import Tablet.OppositeProjectionBlueConditioning
import Tablet.OppositeProjectionRowInjectionLaw
import Tablet.OppositeProjectionWTailBound
import Tablet.OppositeProjectionBlueExposureTailBound
import Tablet.OppositeProjectionAsymptoticBound
import Tablet.OppositeProjectionIntersectionContainment
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.OppositeProjectionSymmetricBlueBadEventNegligible
import Tablet.OppositeProjectionSymmetricBlueNegligibleBadToWHP

-- [TABLET NODE: OppositeProjectionSymmetricBlue]

theorem OppositeProjectionSymmetricBlue :
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        WithHighProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                let sizeBound : Prop :=
                  ∀ x : TwoBiteBaseVertex (m n),
                  ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                    2 * TwoBiteEdgeProbability β n * (n : ℝ)
                let blueBound : Prop :=
                  ∀ b c : Fin (m n), b ≠ c →
                  ((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                        (TwoBiteRedProjection ω)) ∩
                      ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                        (TwoBiteRedProjection ω))).card : ℝ)
                    ≤
                    (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                        TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
                      100 * (Real.log (n : ℝ)) ^ 3)
                sizeBound → blueBound)) := by
-- BODY
  intro β hβ m hm
  exact
    OppositeProjectionSymmetricBlueNegligibleBadToWHP β hβ m hm
      (OppositeProjectionSymmetricBlueBadEventNegligible β hβ m hm)
