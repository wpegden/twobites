import Tablet.OppositeProjectionChooseExponentialBound
import Mathlib.Tactic

-- [TABLET NODE: OppositeProjectionBinomialTailBaseReduction]

theorem OppositeProjectionBinomialTailBaseReduction
    (V M t : ℕ) (q : ℝ) (hq : 0 ≤ q) (hM : 0 < (M : ℝ)) :
    (Nat.choose V t : ℝ) * (q / (M : ℝ)) ^ t ≤
      ((Real.exp 1 * (V : ℝ) * q) / ((t : ℝ) * (M : ℝ))) ^ t := by
-- BODY
  by_cases ht_zero : t = 0
  · subst t
    simp
  have ht_nat_pos : 0 < t := Nat.pos_of_ne_zero ht_zero
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht_nat_pos
  have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt ht_pos
  have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM
  have hqM_nonneg : 0 ≤ q / (M : ℝ) := div_nonneg hq hM.le
  have hchoose := OppositeProjectionChooseExponentialBound V t
  have hmul :
      (Nat.choose V t : ℝ) * (q / (M : ℝ)) ^ t ≤
        ((Real.exp 1 * (V : ℝ)) / (t : ℝ)) ^ t * (q / (M : ℝ)) ^ t :=
    mul_le_mul_of_nonneg_right hchoose (pow_nonneg hqM_nonneg t)
  calc
    (Nat.choose V t : ℝ) * (q / (M : ℝ)) ^ t
        ≤ ((Real.exp 1 * (V : ℝ)) / (t : ℝ)) ^ t * (q / (M : ℝ)) ^ t := hmul
    _ = (((Real.exp 1 * (V : ℝ)) / (t : ℝ)) * (q / (M : ℝ))) ^ t := by
          rw [← mul_pow]
    _ = ((Real.exp 1 * (V : ℝ) * q) / ((t : ℝ) * (M : ℝ))) ^ t := by
          congr 1
          field_simp [ht_ne, hM_ne]
