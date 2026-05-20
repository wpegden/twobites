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

  import Tablet.WithHighProbabilityOfNegligibleBadOnRegular
import Tablet.FiberAndDegreeMixedLiftedIntersectionNegligible

-- [TABLET NODE: FiberAndDegreeMixedLiftedIntersectionConcentration]

theorem FiberAndDegreeMixedLiftedIntersectionConcentration :
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        WithHighProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                ∀ r b : Fin (m n),
                  ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ)
                    ≤ 100 * (Real.log (n : ℝ)) ^ 3)) := by
-- BODY
  intro β hβ m hm
  classical
  let p := fun n => TwoBiteEdgeProbability β n
  let Good := fun (n : ℕ) (ω : TwoBiteSample n (m n) (p n)) =>
                ∀ r b : Fin (m n),
                  ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ)
                    ≤ 100 * (Real.log (n : ℝ)) ^ 3
  let R := fun (n : ℕ) (ω : TwoBiteSample n (m n) (p n)) =>
             (∀ r : Fin (m n), (GraphDegreeCount ω.1 r : ℝ) ≤ 2 * TwoBiteEdgeProbability β n * (m n : ℝ)) ∧
             (∀ b : Fin (m n), (GraphDegreeCount ω.2.1 b : ℝ) ≤ 2 * TwoBiteEdgeProbability β n * (m n : ℝ))
  have hR : WithHighProbability (fun n => TwoBiteEventProbability n (m n) (p n) (R n)) := by
    have hDeg := FiberAndDegreeBaseDegreeConcentration 1 β (by norm_num) hβ m hm
    unfold WithHighProbability at hDeg ⊢
    apply Filter.Tendsto.congr' _ hDeg
    filter_upwards with n
    apply congrArg
    ext ω
    dsimp [R]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · intro r
        have h_rel := h1 r
        unfold WithinRelativeError at h_rel
        have h_le : (GraphDegreeCount ω.1 r : ℝ) - TwoBiteEdgeProbability β n * (m n : ℝ) ≤ 1 * (TwoBiteEdgeProbability β n * (m n : ℝ)) := by
          exact le_trans (le_abs_self _) h_rel
        linarith
      · intro b
        have h_rel := h2 b
        unfold WithinRelativeError at h_rel
        have h_le : (GraphDegreeCount ω.2.1 b : ℝ) - TwoBiteEdgeProbability β n * (m n : ℝ) ≤ 1 * (TwoBiteEdgeProbability β n * (m n : ℝ)) := by
          exact le_trans (le_abs_self _) h_rel
        linarith
    · rintro ⟨h1, h2⟩
      constructor
      · intro r
        have h_le := h1 r
        unfold WithinRelativeError
        change |(GraphDegreeCount ω.1 r : ℝ) - TwoBiteEdgeProbability β n * (m n : ℝ)| ≤ 1 * (TwoBiteEdgeProbability β n * (m n : ℝ))
        rw [abs_le]
        constructor
        · have h_pos : 0 ≤ (GraphDegreeCount ω.1 r : ℝ) := Nat.cast_nonneg _
          linarith
        · linarith
      · intro b
        have h_le := h2 b
        unfold WithinRelativeError
        change |(GraphDegreeCount ω.2.1 b : ℝ) - TwoBiteEdgeProbability β n * (m n : ℝ)| ≤ 1 * (TwoBiteEdgeProbability β n * (m n : ℝ))
        rw [abs_le]
        constructor
        · have h_pos : 0 ≤ (GraphDegreeCount ω.2.1 b : ℝ) := Nat.cast_nonneg _
          linarith
        · linarith
  have hBad : NegligibleProbability (fun n => TwoBiteEventProbability n (m n) (p n) (fun ω => ¬ Good n ω ∧ R n ω)) := by
    have h_neg := FiberAndDegreeMixedLiftedIntersectionNegligible β hβ m hm
    unfold NegligibleProbability at h_neg ⊢
    apply Filter.Tendsto.congr' _ h_neg
    filter_upwards with n
    apply congrArg
    ext ω
    dsimp [Good, R]
    constructor
    · rintro ⟨h_not, h_reg⟩
      constructor
      · intro h_all
        rcases h_not with ⟨r, b, hr⟩
        have h_le := h_all r b
        exact not_le_of_gt hr h_le
      · exact h_reg
    · rintro ⟨h_not, h_reg⟩
      constructor
      · simp only [not_forall, not_le] at h_not
        exact h_not
      · exact h_reg
  have hweight : ∀ᶠ n in Filter.atTop, ∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω := by
    have h_prob_bounds : ∀ᶠ n in Filter.atTop, 0 ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n ∧ TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ 1 :=
      OppositeProjectionEdgeProbBounds
    filter_upwards [h_prob_bounds] with n hn ω
    apply TwoBiteSampleWeightNonnegative
    · rw [← hβ] at hn; exact hn.1
    · rw [← hβ] at hn; exact hn.2
  exact WithHighProbabilityOfNegligibleBadOnRegular m p Good R hR hBad hweight
