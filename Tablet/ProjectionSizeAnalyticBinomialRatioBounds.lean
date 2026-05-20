import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Tablet.Preamble

-- [TABLET NODE: ProjectionSizeAnalyticBinomialRatioBounds]

theorem ProjectionSizeAnalyticBinomialRatioBounds (n k N : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    (Nat.choose n k : ℝ) ≤ (Real.exp 1 * n / k) ^ k ∧ ((N : ℝ) / k) ^ k ≤ (Nat.choose N k : ℝ) := by
-- BODY
  constructor
  · have hk_cases : k = 0 ∨ 0 < k := Nat.eq_zero_or_pos k
    rcases hk_cases with rfl | hk_pos
    · simp
    have hk_real_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
    have h1 : (Nat.choose n k : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) := by
      have h_desc : k.factorial * Nat.choose n k = n.descFactorial k := (Nat.descFactorial_eq_factorial_mul_choose n k).symm
      have h_pow : n.descFactorial k ≤ n ^ k := Nat.descFactorial_le_pow n k
      have h_mul_le : k.factorial * Nat.choose n k ≤ n ^ k := by omega
      have h_mul_le_real : (Nat.choose n k : ℝ) * (k.factorial : ℝ) ≤ (n : ℝ) ^ k := by
        calc (Nat.choose n k : ℝ) * (k.factorial : ℝ) = (k.factorial : ℝ) * (Nat.choose n k : ℝ) := mul_comm _ _
          _ = ((k.factorial * Nat.choose n k : ℕ) : ℝ) := by exact_mod_cast rfl
          _ ≤ ((n ^ k : ℕ) : ℝ) := Nat.cast_le.mpr h_mul_le
          _ = (n : ℝ) ^ k := by exact_mod_cast rfl
      have h_kfact_pos : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr k.factorial_pos
      exact (le_div_iff₀ h_kfact_pos).mpr h_mul_le_real
    have h2 : (k : ℝ) ^ k / Real.exp (k : ℝ) ≤ (k.factorial : ℝ) := by
      have h_exp_bound := Real.pow_div_factorial_le_exp (k : ℝ) hk_real_pos.le k
      have h_exp_pos : 0 < Real.exp (k : ℝ) := Real.exp_pos (k : ℝ)
      have h_kfact_pos : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr k.factorial_pos
      rw [div_le_iff₀ h_kfact_pos] at h_exp_bound
      rw [mul_comm] at h_exp_bound
      exact (div_le_iff₀ h_exp_pos).mpr h_exp_bound
    have h3 : (n : ℝ) ^ k / (k.factorial : ℝ) ≤ (n : ℝ) ^ k / ((k : ℝ) ^ k / Real.exp (k : ℝ)) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact div_pos (by positivity) (Real.exp_pos (k : ℝ))
      · exact h2
    have h4 : (n : ℝ) ^ k / ((k : ℝ) ^ k / Real.exp (k : ℝ)) = (n : ℝ) ^ k * Real.exp (k : ℝ) / (k : ℝ) ^ k := by
      rw [div_div_eq_mul_div]
    have h5 : (n : ℝ) ^ k * Real.exp (k : ℝ) / (k : ℝ) ^ k = (Real.exp 1 * n / k) ^ k := by
      have h_exp : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
        rw [← Real.exp_nat_mul]
        ring_nf
      rw [h_exp]
      rw [div_pow, mul_pow]
      ring
    calc (Nat.choose n k : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) := h1
      _ ≤ (n : ℝ) ^ k / ((k : ℝ) ^ k / Real.exp (k : ℝ)) := h3
      _ = (n : ℝ) ^ k * Real.exp (k : ℝ) / (k : ℝ) ^ k := h4
      _ = (Real.exp 1 * n / k) ^ k := h5
  · have hk_real_pos : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have h_kfact_pos : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr k.factorial_pos
    have h_prod1 : (Nat.choose N k : ℝ) * (k.factorial : ℝ) = (N.descFactorial k : ℝ) := by
      calc (Nat.choose N k : ℝ) * (k.factorial : ℝ) = (k.factorial : ℝ) * (Nat.choose N k : ℝ) := mul_comm _ _
        _ = ((k.factorial * Nat.choose N k : ℕ) : ℝ) := by exact_mod_cast rfl
        _ = ((N.descFactorial k : ℕ) : ℝ) := by congr 1; exact (Nat.descFactorial_eq_factorial_mul_choose N k).symm
    have h_prod2 : (N.descFactorial k : ℝ) = ∏ i ∈ Finset.range k, ((N : ℝ) - i) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i hi
      have hi_lt : i < k := Finset.mem_range.mp hi
      have hi_le : i ≤ N := le_trans (le_of_lt hi_lt) hkN
      rw [Nat.cast_sub hi_le]
    have h_prod3 : (k.factorial : ℝ) = ∏ i ∈ Finset.range k, ((k : ℝ) - i) := by
      have : (k.factorial : ℕ) = k.descFactorial k := by
        have : k.factorial * Nat.choose k k = k.descFactorial k := (Nat.descFactorial_eq_factorial_mul_choose k k).symm
        rw [Nat.choose_self k, mul_one] at this
        exact this
      rw [this, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i hi
      have hi_lt : i < k := Finset.mem_range.mp hi
      have hi_le : i ≤ k := le_of_lt hi_lt
      rw [Nat.cast_sub hi_le]
    have h_prod_div : (Nat.choose N k : ℝ) = ∏ i ∈ Finset.range k, (((N : ℝ) - i) / ((k : ℝ) - i)) := by
      have : (Nat.choose N k : ℝ) = (N.descFactorial k : ℝ) / (k.factorial : ℝ) := by
        rw [← h_prod1]
        rw [mul_div_cancel_right₀ _ h_kfact_pos.ne']
      rw [this, h_prod2, h_prod3, ← Finset.prod_div_distrib]
    have h_le_terms : ∀ i ∈ Finset.range k, (N : ℝ) / (k : ℝ) ≤ ((N : ℝ) - i) / ((k : ℝ) - i) := by
      intro i hi
      have hi_lt : i < k := Finset.mem_range.mp hi
      have h_denom_pos : (0 : ℝ) < (k : ℝ) - i := by 
        rw [sub_pos]
        exact_mod_cast hi_lt
      rw [div_le_div_iff₀ hk_real_pos h_denom_pos]
      have step1 : (N : ℝ) * ((k : ℝ) - i) = (N : ℝ) * (k : ℝ) - (N : ℝ) * i := by ring
      have step2 : ((N : ℝ) - i) * (k : ℝ) = (N : ℝ) * (k : ℝ) - i * (k : ℝ) := by ring
      have h_n_ge_k : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
      have h_i_nonneg : (0 : ℝ) ≤ i := by exact_mod_cast (Nat.zero_le i)
      nlinarith
    rw [h_prod_div]
    have h_pow_prod : ((N : ℝ) / k) ^ k = ∏ i ∈ Finset.range k, ((N : ℝ) / k) := by
      rw [Finset.prod_const, Finset.card_range]
    rw [h_pow_prod]
    apply Finset.prod_le_prod
    · intro i hi
      positivity
    · exact h_le_terms
