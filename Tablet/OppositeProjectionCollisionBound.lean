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
import Tablet.OppositeProjectionRedFailureBound
import Tablet.OppositeProjectionSymmetricBlue
import Tablet.WithHighProbabilityThreeIntersection
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.OppositeProjectionConditioning
import Tablet.OppositeProjectionRowInjectionLaw
import Tablet.OppositeProjectionWTailBound
import Tablet.OppositeProjectionIntersectionContainment
import Tablet.TwoBiteEventProbabilityTotalMassBound

open Filter

-- [TABLET NODE: OppositeProjectionCollisionBound]

theorem OppositeProjectionCollisionBound :
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
                let redBound : Prop :=
                  ∀ r s : Fin (m n), r ≠ s →
                  ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                        (TwoBiteBlueProjection ω)) ∩
                      ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                        (TwoBiteBlueProjection ω))).card : ℝ)
                    ≤
                    (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                        TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
                      100 * (Real.log (n : ℝ)) ^ 3)
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
                sizeBound → redBound ∧ blueBound)) := by
-- BODY
  intro β hβ m hm
  have h_red := OppositeProjectionRedFailureBound β hβ m hm
  have h_blue := OppositeProjectionSymmetricBlue β hβ m hm
  have h_prob :
      ∀ᶠ n in Filter.atTop,
        0 ≤ TwoBiteEdgeProbability β n ∧
          TwoBiteEdgeProbability β n ≤ 1 := by
    filter_upwards [OppositeProjectionEdgeProbBounds] with n hn
    simpa [hβ] using hn
  have h_weight :
      ∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (TwoBiteEdgeProbability β n),
          0 ≤ TwoBiteSampleWeight ω := by
    filter_upwards [h_prob] with n hn
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hn.1 hn.2
  have h_int := WithHighProbabilityThreeIntersection
    m (fun n => TwoBiteEdgeProbability β n) _ _ _ h_red h_blue h_red h_weight
  have prob_mono :
      ∀ {n : ℕ} {E F : TwoBiteSample n (m n) (TwoBiteEdgeProbability β n) → Prop},
        (∀ ω : TwoBiteSample n (m n) (TwoBiteEdgeProbability β n), 0 ≤ TwoBiteSampleWeight ω) →
        (∀ ω, E ω → F ω) →
        TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) E ≤
          TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n) F := by
    intro n E F hweight_n hEF
    classical
    unfold TwoBiteEventProbability
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        exact hEF ω hω)
      (by
        intro ω hωF hωnotE
        exact hweight_n ω)
  unfold WithHighProbability at h_int ⊢
  have hle_lower : ∀ᶠ n in Filter.atTop,
    TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
      (fun ω =>
        let sizeBound : Prop :=
          ∀ x : TwoBiteBaseVertex (m n),
          ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
            2 * TwoBiteEdgeProbability β n * (n : ℝ)
        let redBound : Prop :=
          ∀ r s : Fin (m n), r ≠ s →
          ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                (TwoBiteBlueProjection ω)) ∩
              ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                (TwoBiteBlueProjection ω))).card : ℝ)
            ≤
            (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
              100 * (Real.log (n : ℝ)) ^ 3)
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
        (sizeBound → redBound) ∧ (sizeBound → blueBound) ∧ (sizeBound → redBound))
    ≤
    TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
      (fun ω =>
        let sizeBound : Prop :=
          ∀ x : TwoBiteBaseVertex (m n),
          ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
            2 * TwoBiteEdgeProbability β n * (n : ℝ)
        let redBound : Prop :=
          ∀ r s : Fin (m n), r ≠ s →
          ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                (TwoBiteBlueProjection ω)) ∩
              ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                (TwoBiteBlueProjection ω))).card : ℝ)
            ≤
            (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
              100 * (Real.log (n : ℝ)) ^ 3)
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
        sizeBound → redBound ∧ blueBound) := by
    filter_upwards [h_weight] with n hnw
    refine prob_mono hnw ?_
    intro ω hω
    dsimp only at hω ⊢
    intro hs
    rcases hω with ⟨hr, hb, _⟩
    exact ⟨hr hs, hb hs⟩
  have hle_upper : ∀ᶠ n in Filter.atTop,
    TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
      (fun ω =>
        let sizeBound : Prop :=
          ∀ x : TwoBiteBaseVertex (m n),
          ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
            2 * TwoBiteEdgeProbability β n * (n : ℝ)
        let redBound : Prop :=
          ∀ r s : Fin (m n), r ≠ s →
          ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                (TwoBiteBlueProjection ω)) ∩
              ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                (TwoBiteBlueProjection ω))).card : ℝ)
            ≤
            (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
              100 * (Real.log (n : ℝ)) ^ 3)
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
        sizeBound → redBound ∧ blueBound)
    ≤ 1 := by
    filter_upwards [h_weight] with n hnw
    exact le_trans
      (prob_mono hnw (by intro ω hω; trivial))
      (TwoBiteEventProbabilityTotalMassBound n (m n) (TwoBiteEdgeProbability β n))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_int tendsto_const_nhds hle_lower hle_upper
