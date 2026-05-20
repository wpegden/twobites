import Tablet.Preamble

-- [TABLET NODE: FixedSetCellAnalyticSummationBound]

theorem FixedSetCellAnalyticSummationBound :
    ∀ {k : ℕ} {p ε1 f : ℝ},
      (k : ℝ) ^ 4 *
          Real.exp
            (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 -
              p * (f - 10 * ε1 * (k : ℝ) ^ 2))
        ≤
        Real.exp
          (-(p * f) +
            8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 +
            10 * ε1 * p * (k : ℝ) ^ 2 +
            4 * Real.log (k : ℝ)) := by
-- BODY
  intro k p ε1 f
  by_cases hk_zero : (k : ℝ) = 0
  · have hleft :
        (k : ℝ) ^ 4 *
            Real.exp
              (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 -
                p * (f - 10 * ε1 * (k : ℝ) ^ 2)) = 0 := by
      simp [hk_zero]
    rw [hleft]
    exact (Real.exp_pos _).le
  · have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    have hk_pos : 0 < (k : ℝ) := lt_of_le_of_ne hk_nonneg (Ne.symm hk_zero)
    have hk_pow :
        (k : ℝ) ^ 4 = Real.exp (4 * Real.log (k : ℝ)) := by
      calc
        (k : ℝ) ^ 4 = (Real.exp (Real.log (k : ℝ))) ^ 4 := by
          rw [Real.exp_log hk_pos]
        _ = Real.exp ((4 : ℕ) * Real.log (k : ℝ)) := by
          rw [Real.exp_nat_mul]
        _ = Real.exp (4 * Real.log (k : ℝ)) := by norm_num
    rw [hk_pow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf
    exact le_rfl
