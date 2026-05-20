import Tablet.RealChooseTwo

-- [TABLET NODE: HugeSameColorProjectionPairNumerics]

theorem HugeSameColorProjectionPairNumerics :
    ∀ {H k t1 p m ε1 : ℝ},
      H ≤ 2 * k / t1 →
      1 ≤ 2 * p * m →
      (2 * k / t1) * RealChooseTwo (2 * p * m) ≤ ε1 * k ^ 2 →
      H * RealChooseTwo (2 * p * m) ≤ ε1 * k ^ 2 := by
-- BODY
  intro H k t1 p m ε1 hH hpm hnum
  have hD_nonneg : 0 ≤ 2 * p * m := by
    linarith
  have hD_minus_nonneg : 0 ≤ 2 * p * m - 1 := by
    linarith
  have hchoose_nonneg : 0 ≤ RealChooseTwo (2 * p * m) := by
    unfold RealChooseTwo
    nlinarith [mul_nonneg hD_nonneg hD_minus_nonneg]
  exact le_trans (mul_le_mul_of_nonneg_right hH hchoose_nonneg) hnum
