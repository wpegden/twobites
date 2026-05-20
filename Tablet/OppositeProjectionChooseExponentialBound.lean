import Tablet.Preamble
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic

-- [TABLET NODE: OppositeProjectionChooseExponentialBound]

theorem OppositeProjectionChooseExponentialBound (N t : ℕ) :
    (Nat.choose N t : ℝ) ≤ ((Real.exp 1 * (N : ℝ)) / (t : ℝ)) ^ t := by
-- BODY
  by_cases ht_zero : t = 0
  · subst t
    simp
  have ht_nat_pos : 0 < t := Nat.pos_of_ne_zero ht_zero
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht_nat_pos
  have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt ht_pos
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hpow_base_pos : 0 < ((t : ℝ) / Real.exp 1) ^ t :=
    pow_pos (div_pos ht_pos hexp_pos) t
  have hpow_base_nonneg : 0 ≤ ((t : ℝ) / Real.exp 1) ^ t := hpow_base_pos.le
  have hsqrt_ge_one : 1 ≤ Real.sqrt (2 * Real.pi * (t : ℝ)) := by
    rw [Real.one_le_sqrt]
    have ht_one : (1 : ℝ) ≤ t := by exact_mod_cast ht_nat_pos
    have hpi_two : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    nlinarith
  have hfactorial_lower : ((t : ℝ) / Real.exp 1) ^ t ≤ (t.factorial : ℝ) := by
    have hstirling := Stirling.le_factorial_stirling t
    have hmul :
        ((t : ℝ) / Real.exp 1) ^ t ≤
          Real.sqrt (2 * Real.pi * (t : ℝ)) * ((t : ℝ) / Real.exp 1) ^ t := by
      simpa [one_mul] using
        mul_le_mul_of_nonneg_right hsqrt_ge_one hpow_base_nonneg
    exact le_trans hmul hstirling
  have hchoose :
      (Nat.choose N t : ℝ) ≤ (N : ℝ) ^ t / (t.factorial : ℝ) :=
    Nat.choose_le_pow_div t N
  have hNpow_nonneg : 0 ≤ (N : ℝ) ^ t := pow_nonneg (by positivity) t
  have hdiv :
      (N : ℝ) ^ t / (t.factorial : ℝ) ≤
        (N : ℝ) ^ t / (((t : ℝ) / Real.exp 1) ^ t) :=
    div_le_div_of_nonneg_left hNpow_nonneg hpow_base_pos hfactorial_lower
  have halg :
      (N : ℝ) ^ t / (((t : ℝ) / Real.exp 1) ^ t) =
        ((Real.exp 1 * (N : ℝ)) / (t : ℝ)) ^ t := by
    rw [div_pow, div_pow]
    field_simp [ht_ne, hexp_pos.ne', pow_ne_zero _ ht_ne,
      pow_ne_zero _ hexp_pos.ne']
    ring
  exact le_trans hchoose (le_trans hdiv (le_of_eq halg))
