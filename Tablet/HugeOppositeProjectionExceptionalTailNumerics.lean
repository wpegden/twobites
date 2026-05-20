import Tablet.RealChooseTwo

-- [TABLET NODE: HugeOppositeProjectionExceptionalTailNumerics]

theorem HugeOppositeProjectionExceptionalTailNumerics :
    ∀ {ε1 ε2 d r u : ℝ},
      0 ≤ ε2 →
      30 * ε2 ≤ ε1 →
      98 ≤ d →
      0 ≤ r →
      0 ≤ u →
      u ≤ 1 →
      r ≤ d →
      r + u ≤ ε2 * d →
        RealChooseTwo (d + r) ≤
          (1 + ε1) * (RealChooseTwo (d - u) + RealChooseTwo u) := by
-- BODY
  intro ε1 ε2 d r u hε2 h30 hd hr hu hu_le_one hr_le_d hru_le
  let Q : ℝ := RealChooseTwo (d - u) + RealChooseTwo u
  have hd_nonneg : 0 ≤ d := by
    linarith
  have hQ_ge_C :
      RealChooseTwo (d - 1) ≤ Q := by
    unfold Q RealChooseTwo
    have hone_minus_nonneg : 0 ≤ 1 - u := by
      linarith
    have htail_nonneg : 0 ≤ d - u - 1 := by
      linarith
    have hprod : 0 ≤ (1 - u) * (d - u - 1) :=
      mul_nonneg hone_minus_nonneg htail_nonneg
    nlinarith only [hprod]
  have hC_d_minus_one_nonneg : 0 ≤ RealChooseTwo (d - 1) := by
    unfold RealChooseTwo
    nlinarith
  have hQ_nonneg : 0 ≤ Q := le_trans hC_d_minus_one_nonneg hQ_ge_C
  have hdiff_bound :
      RealChooseTwo (d + r) - Q ≤ (3 / 2 : ℝ) * d * (r + u) := by
    have hformula :
        RealChooseTwo (d + r) - Q =
          d * r + r * (r - 1) / 2 + u * (d - u) := by
      unfold Q RealChooseTwo
      ring
    have hr_sq_le_dr : r ^ 2 ≤ d * r := by
      nlinarith [hr_le_d, hr]
    have hu_sq_nonneg : 0 ≤ u ^ 2 := sq_nonneg u
    have hu_part_le_du : u * (d - u) ≤ d * u := by
      nlinarith only [hu_sq_nonneg]
    have hdu_nonneg : 0 ≤ d * u := mul_nonneg hd_nonneg hu
    nlinarith only [hformula, hr_sq_le_dr, hr, hu_part_le_du, hdu_nonneg]
  have htail_eps :
      (3 / 2 : ℝ) * d * (r + u) ≤ (3 / 2 : ℝ) * ε2 * d ^ 2 := by
    have hcoef_nonneg : 0 ≤ (3 / 2 : ℝ) * d :=
      mul_nonneg (by norm_num) hd_nonneg
    have hmul := mul_le_mul_of_nonneg_left hru_le hcoef_nonneg
    nlinarith [hmul]
  have hC_d_minus_one_big :
      (3 / 2 : ℝ) * d ^ 2 ≤ 30 * RealChooseTwo (d - 1) := by
    unfold RealChooseTwo
    nlinarith
  have htail_to_C :
      (3 / 2 : ℝ) * ε2 * d ^ 2 ≤
        30 * ε2 * RealChooseTwo (d - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hC_d_minus_one_big hε2
    nlinarith [hmul]
  have htail_to_Q :
      30 * ε2 * RealChooseTwo (d - 1) ≤ 30 * ε2 * Q := by
    have hcoef_nonneg : 0 ≤ 30 * ε2 := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hQ_ge_C hcoef_nonneg
    nlinarith [hmul]
  have hthirty_eps_Q_le :
      30 * ε2 * Q ≤ ε1 * Q := by
    have hmul := mul_le_mul_of_nonneg_right h30 hQ_nonneg
    nlinarith [hmul]
  have hdiff_le_eps_Q : RealChooseTwo (d + r) - Q ≤ ε1 * Q :=
    le_trans hdiff_bound
      (le_trans htail_eps
        (le_trans htail_to_C (le_trans htail_to_Q hthirty_eps_Q_le)))
  nlinarith [hdiff_le_eps_Q]
