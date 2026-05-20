import Tablet.RealChooseTwo

-- [TABLET NODE: RealChooseTwoQuadraticBounds]

theorem RealChooseTwoQuadraticBounds :
    ∀ x : ℝ, 0 ≤ x →
      (2 ≤ x → x ^ 2 / 4 ≤ RealChooseTwo x ∧
        RealChooseTwo x ≤ x ^ 2 / 2) ∧
        RealChooseTwo x ≤ x ^ 2 := by
-- BODY
  intro x hx_nonneg
  have hupper_square : RealChooseTwo x ≤ x ^ 2 := by
    unfold RealChooseTwo
    have hsquare : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith [hx_nonneg, hsquare]
  refine ⟨?_, hupper_square⟩
  intro hx
  have hx_minus : 0 ≤ x - 2 := by linarith
  have hprod : 0 ≤ x * (x - 2) := mul_nonneg hx_nonneg hx_minus
  refine ⟨?_, ?_⟩
  · unfold RealChooseTwo
    nlinarith [hprod]
  · unfold RealChooseTwo
    nlinarith [hx_nonneg]
