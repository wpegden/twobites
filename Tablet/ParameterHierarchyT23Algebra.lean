import Tablet.TwoBiteLargeCutoff

-- [TABLET NODE: ParameterHierarchyT23Algebra]

theorem ParameterHierarchyT23Algebra :
    ∀ η : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      0 < (n : ℝ) →
      0 ≤ L →
      200 * L ^ 3 / Real.rpow (n : ℝ) η ≤ 1 →
      100 * (Real.rpow (n : ℝ) (1 / 4 : ℝ) + (1 / 2 : ℝ)) * L ^ 3 ≤
        TwoBiteLargeCutoff η n := by
-- BODY
  intro η n
  dsimp
  let L := Real.log (n : ℝ)
  intro hn_pos hL_nonneg hthreshold
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hn_nat_pos : 0 < n := by
    have hn_ne_zero : n ≠ 0 := by
      intro hn_zero
      simp [hn_zero] at hn_pos
    exact Nat.pos_of_ne_zero hn_ne_zero
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_nat_pos
  have hquarter_nonneg : 0 ≤ Real.rpow (n : ℝ) (1 / 4 : ℝ) :=
    Real.rpow_nonneg hn_nonneg _
  have hquarter_ge_one : 1 ≤ Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
    calc
      (1 : ℝ) = Real.rpow (1 : ℝ) (1 / 4 : ℝ) := by
        exact (Real.one_rpow (1 / 4 : ℝ)).symm
      _ ≤ Real.rpow (n : ℝ) (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hn_ge_one
          (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hsum_le :
      Real.rpow (n : ℝ) (1 / 4 : ℝ) + (1 / 2 : ℝ) ≤
        2 * Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
    linarith
  have hL_cube_nonneg : 0 ≤ L ^ 3 := by positivity
  have hleft_le :
      100 * (Real.rpow (n : ℝ) (1 / 4 : ℝ) + (1 / 2 : ℝ)) * L ^ 3 ≤
        Real.rpow (n : ℝ) (1 / 4 : ℝ) * (200 * L ^ 3) := by
    have hcoef :
        100 * (Real.rpow (n : ℝ) (1 / 4 : ℝ) + (1 / 2 : ℝ)) ≤
          100 * (2 * Real.rpow (n : ℝ) (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    calc
      100 * (Real.rpow (n : ℝ) (1 / 4 : ℝ) + (1 / 2 : ℝ)) * L ^ 3 ≤
          100 * (2 * Real.rpow (n : ℝ) (1 / 4 : ℝ)) * L ^ 3 :=
        mul_le_mul_of_nonneg_right hcoef hL_cube_nonneg
      _ = Real.rpow (n : ℝ) (1 / 4 : ℝ) * (200 * L ^ 3) := by ring
  have heta_power_pos : 0 < Real.rpow (n : ℝ) η :=
    Real.rpow_pos_of_pos hn_pos _
  have hthreshold_num :
      200 * L ^ 3 ≤ Real.rpow (n : ℝ) η := by
    have hthreshold_L :
        200 * L ^ 3 / Real.rpow (n : ℝ) η ≤ 1 := by
      simpa [L] using hthreshold
    rw [div_le_iff₀ heta_power_pos] at hthreshold_L
    simpa [one_mul] using hthreshold_L
  have hprod_le :
      Real.rpow (n : ℝ) (1 / 4 : ℝ) * (200 * L ^ 3) ≤
        Real.rpow (n : ℝ) (1 / 4 : ℝ) * Real.rpow (n : ℝ) η :=
    mul_le_mul_of_nonneg_left hthreshold_num hquarter_nonneg
  have hprod_eq :
      Real.rpow (n : ℝ) (1 / 4 : ℝ) * Real.rpow (n : ℝ) η =
        TwoBiteLargeCutoff η n := by
    dsimp [TwoBiteLargeCutoff]
    exact (Real.rpow_add hn_pos (1 / 4 : ℝ) η).symm
  exact le_trans hleft_le (le_trans hprod_le (le_of_eq hprod_eq))
