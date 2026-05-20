import Tablet.RealChooseTwo

-- [TABLET NODE: HugeOppositeProjectionLargeExceptionalNumerics]

set_option maxHeartbeats 1000000 in
theorem HugeOppositeProjectionLargeExceptionalNumerics :
    ∀ {ε1 ε2 d b y u : ℝ},
      0 ≤ ε1 →
      0 ≤ ε2 →
      ε2 ≤ 1 →
      30 * ε2 ≤ ε1 →
      98 ≤ d →
      0 ≤ b →
      0 ≤ y →
      y ≤ 1 →
      0 ≤ u →
      u ≤ 1 →
      b + u = d →
      |y - u| ≤ 2 * ε2 * d →
        RealChooseTwo ((1 + ε2) * b) + RealChooseTwo y ≤
          (1 + ε1) * (RealChooseTwo b + RealChooseTwo u) := by
-- BODY
  intro ε1 ε2 d b y u hε1 hε2 hε2_le_one h30 hD hb hy hy_le_one hu hu_le_one hsum habs
  have hd_nonneg : 0 ≤ d := by
    linarith only [hD]
  have hb_le_d : b ≤ d := by
    linarith only [hsum, hu]
  have hb_sq_le_d_sq : b ^ 2 ≤ d ^ 2 := by
    have hgap : 0 ≤ (d - b) * (d + b) :=
      mul_nonneg (by linarith only [hb_le_d]) (by linarith only [hd_nonneg, hb])
    nlinarith only [hgap]
  have hQ_ge_d_minus_one :
      RealChooseTwo (d - 1) ≤ RealChooseTwo b + RealChooseTwo u := by
    have htail : 0 ≤ (1 - u) * (b - 1) :=
      mul_nonneg (by linarith only [hu_le_one]) (by linarith only [hsum, hD, hu_le_one])
    have hdiff :
        RealChooseTwo b + RealChooseTwo u - RealChooseTwo (d - 1) =
          (1 - u) * (b - 1) := by
      unfold RealChooseTwo
      rw [← hsum]
      ring
    nlinarith only [htail, hdiff]
  have hCd_minus_one_nonneg : 0 ≤ RealChooseTwo (d - 1) := by
    unfold RealChooseTwo
    have hprod : 0 ≤ (d - 1) * (d - 2) :=
      mul_nonneg (by linarith only [hD]) (by linarith only [hD])
    nlinarith only [hprod]
  have hQ_nonneg : 0 ≤ RealChooseTwo b + RealChooseTwo u :=
    le_trans hCd_minus_one_nonneg hQ_ge_d_minus_one
  have hblock :
      RealChooseTwo ((1 + ε2) * b) - RealChooseTwo b ≤
        (3 / 2) * ε2 * d ^ 2 := by
    have hcoef_le : 2 + ε2 ≤ 3 := by
      linarith only [hε2_le_one]
    have hmul_coef :
        (2 + ε2) * b ^ 2 ≤ 3 * b ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef_le (sq_nonneg b)
    have h3b_le_d : 3 * b ^ 2 ≤ 3 * d ^ 2 := by
      nlinarith only [hb_sq_le_d_sq]
    have hinner_le : (2 + ε2) * b ^ 2 - b ≤ 3 * d ^ 2 := by
      nlinarith only [hmul_coef, h3b_le_d, hb]
    have hmul_inner :
        ε2 * ((2 + ε2) * b ^ 2 - b) ≤ ε2 * (3 * d ^ 2) :=
      mul_le_mul_of_nonneg_left hinner_le hε2
    unfold RealChooseTwo
    nlinarith only [hmul_inner]
  have hCy_diff :
      RealChooseTwo y - RealChooseTwo u ≤ ε2 * d := by
    have hlow : -(2 * ε2 * d) ≤ y - u := (abs_le.mp habs).1
    have hhigh : y - u ≤ 2 * ε2 * d := (abs_le.mp habs).2
    have hfac_upper : y + u - 1 ≤ 1 := by
      linarith only [hy_le_one, hu_le_one]
    have hfac_lower : -1 ≤ y + u - 1 := by
      linarith only [hy, hu]
    unfold RealChooseTwo
    by_cases hdiff_nonneg : 0 ≤ y - u
    · have hprod_le : (y - u) * (y + u - 1) ≤ (y - u) * 1 :=
        mul_le_mul_of_nonneg_left hfac_upper hdiff_nonneg
      nlinarith only [hprod_le, hhigh]
    · have hdiff_nonpos : y - u ≤ 0 := le_of_not_ge hdiff_nonneg
      have hprod_le : (y - u) * (y + u - 1) ≤ (y - u) * (-1) :=
        mul_le_mul_of_nonpos_left hfac_lower hdiff_nonpos
      nlinarith only [hprod_le, hlow]
  have hcoeff :
      (3 / 2) * d ^ 2 + d ≤ 30 * RealChooseTwo (d - 1) := by
    unfold RealChooseTwo
    nlinarith only [hD]
  have herror_le_cd :
      (3 / 2) * ε2 * d ^ 2 + ε2 * d ≤
        30 * ε2 * RealChooseTwo (d - 1) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hcoeff hε2
    nlinarith only [hmul]
  have herror_le_Q :
      (3 / 2) * ε2 * d ^ 2 + ε2 * d ≤
        30 * ε2 * (RealChooseTwo b + RealChooseTwo u) := by
    have hthirty_eps_nonneg : 0 ≤ 30 * ε2 :=
      mul_nonneg (by norm_num) hε2
    have hmul :=
      mul_le_mul_of_nonneg_left hQ_ge_d_minus_one hthirty_eps_nonneg
    exact le_trans herror_le_cd hmul
  have herror_le_epsQ :
      (3 / 2) * ε2 * d ^ 2 + ε2 * d ≤
        ε1 * (RealChooseTwo b + RealChooseTwo u) := by
    have hmul :=
      mul_le_mul_of_nonneg_right h30 hQ_nonneg
    exact le_trans herror_le_Q hmul
  have hdiff :
      RealChooseTwo ((1 + ε2) * b) + RealChooseTwo y -
          (RealChooseTwo b + RealChooseTwo u) ≤
        ε1 * (RealChooseTwo b + RealChooseTwo u) := by
    nlinarith only [hblock, hCy_diff, herror_le_epsQ]
  nlinarith only [hdiff]
