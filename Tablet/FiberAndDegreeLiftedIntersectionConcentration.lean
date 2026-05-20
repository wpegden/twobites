import Tablet.WithHighProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch
import Tablet.TwoBiteNaturalTotalMassOneEventually
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.UniformInjectionWeight
import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.FiberAndDegreeBaseDegreeConcentration
import Tablet.HypergeometricMgfComparison
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.FiberAndDegreeBaseCodegreeConcentration
import Tablet.WithHighProbabilityOfNegligibleBadOnRegular
import Tablet.FiberAndDegreeSameColorLiftedIntersectionNegligible

open Classical

-- [TABLET NODE: FiberAndDegreeLiftedIntersectionConcentration]

theorem FiberAndDegreeLiftedIntersectionConcentration :
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        WithHighProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                (∀ r s : Fin (m n), r ≠ s →
                  ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
                    ≤ 100 * (Real.log (n : ℝ)) ^ 3) ∧
                (∀ b c : Fin (m n), b ≠ c →
                  ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
                    ≤ 100 * (Real.log (n : ℝ)) ^ 3))) := by
-- BODY
  intro β hβ m hm
  classical
  let p := fun n => TwoBiteEdgeProbability β n
  let Good := fun (n : ℕ) (ω : TwoBiteSample n (m n) (p n)) =>
                (∀ r s : Fin (m n), r ≠ s →
                  ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
                    ≤ 100 * (Real.log (n : ℝ)) ^ 3) ∧
                (∀ b c : Fin (m n), b ≠ c →
                  ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
                    ≤ 100 * (Real.log (n : ℝ)) ^ 3)
  let R := fun (n : ℕ) (ω : TwoBiteSample n (m n) (p n)) =>
                (∀ r s : Fin (m n), r ≠ s →
                  ((Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ 100 * Real.log (n : ℝ)) ∧
                (∀ b c : Fin (m n), b ≠ c →
                  ((Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ 100 * Real.log (n : ℝ))
  
  have hR : WithHighProbability (fun n => TwoBiteEventProbability n (m n) (p n) (R n)) := by
    exact FiberAndDegreeBaseCodegreeConcentration β hβ m hm

  have hBad : NegligibleProbability (fun n => TwoBiteEventProbability n (m n) (p n) (fun ω => ¬ Good n ω ∧ R n ω)) := by
    have h_neg := FiberAndDegreeSameColorLiftedIntersectionNegligible β hβ m hm
    unfold NegligibleProbability at h_neg ⊢
    apply Filter.Tendsto.congr' _ h_neg
    filter_upwards with n
    apply congrArg
    ext ω
    dsimp [Good, R]
    constructor
    · rintro ⟨h_bad, h_reg⟩
      constructor
      · rintro ⟨h_all1, h_all2⟩
        rcases h_bad with ⟨r, s, hrs, hr⟩ | ⟨b, c, hbc, hb⟩
        · exact not_le_of_gt hr (h_all1 r s hrs)
        · exact not_le_of_gt hb (h_all2 b c hbc)
      · exact h_reg
    · rintro ⟨h_not, h_reg⟩
      constructor
      · by_cases h1 : (∀ r s : Fin (m n), r ≠ s → ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) ≤ 100 * Real.log (n : ℝ) ^ 3)
        · right
          have h2 : ¬ (∀ b c : Fin (m n), b ≠ c → ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) ≤ 100 * Real.log (n : ℝ) ^ 3) := fun h => h_not ⟨h1, h⟩
          push_neg at h2
          exact h2
        · left
          push_neg at h1
          exact h1
      · exact h_reg
  have hweight : ∀ᶠ n in Filter.atTop, ∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω := by
    have h_prob_bounds : ∀ᶠ n in Filter.atTop, 0 ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n ∧ TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ 1 :=
      OppositeProjectionEdgeProbBounds
    filter_upwards [h_prob_bounds] with n hn ω
    apply TwoBiteSampleWeightNonnegative
    · rw [← hβ] at hn; exact hn.1
    · rw [← hβ] at hn; exact hn.2
  exact WithHighProbabilityOfNegligibleBadOnRegular m p Good R hR hBad hweight
