import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: NaturalParameterApproximation]

theorem NaturalParameterApproximation :
    ∀ (κ : ℝ) (n : ℕ),
      0 ≤ TwoBiteReducedVertexCount n →
      0 ≤ TwoBiteIndependenceScale κ n →
      (TwoBiteNaturalReducedVertexCount n : ℝ) ≤
          TwoBiteReducedVertexCount n ∧
        TwoBiteReducedVertexCount n <
          (TwoBiteNaturalReducedVertexCount n : ℝ) + 1 ∧
        TwoBiteIndependenceScale κ n ≤
          (TwoBiteNaturalIndependenceScale κ n : ℝ) ∧
        (TwoBiteNaturalIndependenceScale κ n : ℝ) <
          TwoBiteIndependenceScale κ n + 1 := by
-- BODY
  intro κ n hm_nonneg hk_nonneg
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [TwoBiteNaturalReducedVertexCount] using
      (Nat.floor_le (a := TwoBiteReducedVertexCount n) hm_nonneg)
  · simpa [TwoBiteNaturalReducedVertexCount] using
      (Nat.lt_floor_add_one (a := TwoBiteReducedVertexCount n))
  · simpa [TwoBiteNaturalIndependenceScale] using
      (Nat.le_ceil (a := TwoBiteIndependenceScale κ n))
  · simpa [TwoBiteNaturalIndependenceScale] using
      (Nat.ceil_lt_add_one hk_nonneg)
