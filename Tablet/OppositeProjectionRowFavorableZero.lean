import Tablet.Preamble

-- [TABLET NODE: OppositeProjectionRowFavorableZero]

open scoped Classical BigOperators

theorem OppositeProjectionRowFavorableZero (S h : ℕ) (h_gt_S : S < h) :
  (Nat.descFactorial S h : ℝ) = 0 := by
-- BODY
  have : Nat.descFactorial S h = 0 := Nat.descFactorial_of_lt h_gt_S
  rw [this]
  simp
