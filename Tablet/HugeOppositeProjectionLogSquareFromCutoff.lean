import Mathlib.Analysis.Complex.ExponentialBounds
import Tablet.TwoBiteHugeCutoff

-- [TABLET NODE: HugeOppositeProjectionLogSquareFromCutoff]

theorem HugeOppositeProjectionLogSquareFromCutoff :
    ∀ n : ℕ, 0 < n → (100 : ℝ) ≤ TwoBiteHugeCutoff n →
      (2 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
-- BODY
  intro n hn_pos_nat ht1_ge_hundred
  let L : ℝ := Real.log (n : ℝ)
  have hn_ge_one_nat : 1 ≤ n := Nat.succ_le_of_lt hn_pos_nat
  have hn_pos_real : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_ge_one_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos_real
  have hL_nonneg : 0 ≤ L := by
    simpa [L] using Real.log_nonneg hn_ge_one_real
  have hcutoff_pos : 0 < TwoBiteHugeCutoff n :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 100) ht1_ge_hundred
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((n : ℝ) * L) :=
    Real.sqrt_nonneg _
  have hlogL_pos : 0 < Real.log L := by
    by_contra hnot
    have hlogL_nonpos : Real.log L ≤ 0 := le_of_not_gt hnot
    have hcutoff_nonpos : TwoBiteHugeCutoff n ≤ 0 := by
      simpa [TwoBiteHugeCutoff, L] using
        (div_nonpos_of_nonneg_of_nonpos hsqrt_nonneg hlogL_nonpos)
    linarith only [hcutoff_pos, hcutoff_nonpos]
  have hL_gt_one : (1 : ℝ) < L :=
    (Real.log_pos_iff hL_nonneg).mp hlogL_pos
  have hL_pos : 0 < L := lt_trans zero_lt_one hL_gt_one
  have hn_gt_exp_one : Real.exp 1 < (n : ℝ) := by
    exact (Real.lt_log_iff_exp_lt hn_pos_real).mp (by simpa [L] using hL_gt_one)
  have hn_gt_two_real : (2 : ℝ) < (n : ℝ) :=
    lt_trans Real.exp_one_gt_two hn_gt_exp_one
  have hn_ge_three_nat : 3 ≤ n := by
    have hn_gt_two_nat : 2 < n := by exact_mod_cast hn_gt_two_real
    omega
  have hlog_three_le_L : Real.log (3 : ℝ) ≤ L := by
    have hthree_le_n_real : (3 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn_ge_three_nat
    simpa [L] using Real.log_le_log (by norm_num : (0 : ℝ) < 3) hthree_le_n_real
  have hexp_one_lt_fourteen_fifths : Real.exp 1 < (14 : ℝ) / 5 := by
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp_one_nineteenth_le : Real.exp ((1 : ℝ) / 19) ≤ (19 : ℝ) / 18 := by
    have hbound := Real.exp_bound_div_one_sub_of_interval
      (show (0 : ℝ) ≤ 1 / 19 by norm_num)
      (show ((1 : ℝ) / 19) < 1 by norm_num)
    norm_num at hbound ⊢
    exact hbound
  have hexp_twenty_nineteenths_lt_three :
      Real.exp ((20 : ℝ) / 19) < 3 := by
    have hleft :
        Real.exp 1 * Real.exp ((1 : ℝ) / 19) ≤
          Real.exp 1 * ((19 : ℝ) / 18) :=
      mul_le_mul_of_nonneg_left hexp_one_nineteenth_le (Real.exp_pos 1).le
    have hright :
        Real.exp 1 * ((19 : ℝ) / 18) <
          ((14 : ℝ) / 5) * ((19 : ℝ) / 18) :=
      mul_lt_mul_of_pos_right hexp_one_lt_fourteen_fifths (by norm_num)
    calc
      Real.exp ((20 : ℝ) / 19) = Real.exp (1 + (1 : ℝ) / 19) := by
        norm_num
      _ = Real.exp 1 * Real.exp ((1 : ℝ) / 19) := by
        rw [Real.exp_add]
      _ < 3 := by nlinarith only [hleft, hright]
  have htwenty_nineteenths_le_log_three :
      (20 : ℝ) / 19 ≤ Real.log (3 : ℝ) :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).mpr
      (le_of_lt hexp_twenty_nineteenths_lt_three)
  have htwenty_nineteenths_le_L : (20 : ℝ) / 19 ≤ L :=
    le_trans htwenty_nineteenths_le_log_three hlog_three_le_L
  have hexp_twentieth_le : Real.exp ((1 : ℝ) / 20) ≤ (20 : ℝ) / 19 := by
    have hbound := Real.exp_bound_div_one_sub_of_interval
      (show (0 : ℝ) ≤ 1 / 20 by norm_num)
      (show ((1 : ℝ) / 20) < 1 by norm_num)
    norm_num at hbound ⊢
    exact hbound
  have hlogL_ge_twentieth : (1 : ℝ) / 20 ≤ Real.log L :=
    (Real.le_log_iff_exp_le hL_pos).mpr
      (le_trans hexp_twentieth_le htwenty_nineteenths_le_L)
  have hsqrt_ge_five : (5 : ℝ) ≤ Real.sqrt ((n : ℝ) * L) := by
    have hmul :=
      mul_le_mul_of_nonneg_right ht1_ge_hundred hlogL_pos.le
    have hcutoff_mul :
        TwoBiteHugeCutoff n * Real.log L =
          Real.sqrt ((n : ℝ) * L) := by
      simpa [TwoBiteHugeCutoff, L] using
        (div_mul_cancel₀ (Real.sqrt ((n : ℝ) * L)) (ne_of_gt hlogL_pos))
    have hlarge :
        (100 : ℝ) * Real.log L ≤ Real.sqrt ((n : ℝ) * L) := by
      calc
        (100 : ℝ) * Real.log L ≤ TwoBiteHugeCutoff n * Real.log L := hmul
        _ = Real.sqrt ((n : ℝ) * L) := hcutoff_mul
    nlinarith only [hlarge, hlogL_ge_twentieth]
  have hnL_ge_twenty_five : (25 : ℝ) ≤ (n : ℝ) * L := by
    have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5)
      hsqrt_ge_five 2
    have hsqrt_sq :
        Real.sqrt ((n : ℝ) * L) ^ 2 = (n : ℝ) * L :=
      Real.sq_sqrt (mul_nonneg hn_nonneg hL_pos.le)
    nlinarith only [hsquare, hsqrt_sq]
  by_contra hnot
  have hlog_sq_lt_two : (Real.log (n : ℝ)) ^ 2 < 2 := lt_of_not_ge hnot
  have hL_sq_lt_two : L ^ 2 < 2 := by simpa [L] using hlog_sq_lt_two
  have hL_lt_two : L < 2 := by
    by_contra hnot_lt
    have htwo_le_L : (2 : ℝ) ≤ L := le_of_not_gt hnot_lt
    have hfour_le_L_sq : (4 : ℝ) ≤ L ^ 2 := by
      nlinarith only [htwo_le_L]
    nlinarith only [hfour_le_L_sq, hL_sq_lt_two]
  have hn_lt_exp_two : (n : ℝ) < Real.exp 2 :=
    (Real.log_lt_iff_lt_exp hn_pos_real).mp (by simpa [L] using hL_lt_two)
  have hexp_two_lt_nine : Real.exp 2 < 9 := by
    have he1lt3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have he1pos : 0 < Real.exp 1 := Real.exp_pos 1
    calc
      Real.exp 2 = Real.exp (1 + 1 : ℝ) := by norm_num
      _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
      _ < 9 := by nlinarith only [he1lt3, he1pos]
  have hn_lt_nine_real : (n : ℝ) < 9 :=
    lt_trans hn_lt_exp_two hexp_two_lt_nine
  have hn_lt_nine_nat : n < 9 := by
    by_contra hnot_lt
    have hn_ge_nine_nat : 9 ≤ n := le_of_not_gt hnot_lt
    have hn_ge_nine_real : (9 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn_ge_nine_nat
    linarith only [hn_lt_nine_real, hn_ge_nine_real]
  have hn_le_eight_nat : n ≤ 8 := by omega
  have hn_le_eight_real : (n : ℝ) ≤ 8 := by exact_mod_cast hn_le_eight_nat
  have hnL_lt_sixteen : (n : ℝ) * L < 16 := by
    nlinarith only [hn_le_eight_real, hL_lt_two, hL_pos, hn_nonneg]
  nlinarith only [hnL_ge_twenty_five, hnL_lt_sixteen]
