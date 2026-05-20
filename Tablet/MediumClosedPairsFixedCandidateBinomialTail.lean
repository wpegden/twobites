import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: MediumClosedPairsFixedCandidateBinomialTail]

theorem MediumClosedPairsFixedCandidateBinomialTail
    (N : ℕ) (p A P : ℝ)
    (hp0 : 0 ≤ p)
    (hApos : 0 < A)
    (hmean : p * (N : ℝ) ≤ A / (4 * Real.exp 1))
    (hunion : P ≤ (Nat.choose N ⌈A⌉₊ : ℝ) * p ^ ⌈A⌉₊) :
    P ≤ Real.exp (-A / 4) := by
-- BODY
  let t : ℕ := ⌈A⌉₊
  let μ : ℝ := p * (N : ℝ)
  have ht_pos : 0 < t := by
    simpa [t] using (Nat.ceil_pos.mpr hApos : 0 < ⌈A⌉₊)
  have ht_real_pos : 0 < (t : ℝ) := Nat.cast_pos.mpr ht_pos
  have hA_le_t : A ≤ (t : ℝ) := by
    simpa [t] using (Nat.le_ceil A)
  have hμ_nonneg : 0 ≤ μ := by
    exact mul_nonneg hp0 (Nat.cast_nonneg N)
  have hp_pow_nonneg : 0 ≤ p ^ t := pow_nonneg hp0 t
  have hchoose_div :
      (Nat.choose N t : ℝ) ≤ (N : ℝ) ^ t / (Nat.factorial t : ℝ) := by
    exact Nat.choose_le_pow_div (α := ℝ) t N
  have hchoose_pow :
      (Nat.choose N t : ℝ) * p ^ t ≤ μ ^ t / (Nat.factorial t : ℝ) := by
    calc
      (Nat.choose N t : ℝ) * p ^ t
          ≤ ((N : ℝ) ^ t / (Nat.factorial t : ℝ)) * p ^ t := by
            exact mul_le_mul_of_nonneg_right hchoose_div hp_pow_nonneg
      _ = μ ^ t / (Nat.factorial t : ℝ) := by
            dsimp [μ]
            rw [div_mul_eq_mul_div, ← mul_pow]
            ring
  have hfactorial_exp :
      (t : ℝ) ^ t / (Nat.factorial t : ℝ) ≤ Real.exp (t : ℝ) :=
    Real.pow_div_factorial_le_exp (t : ℝ) (Nat.cast_nonneg t) t
  have hμ_div_nonneg : 0 ≤ μ / (t : ℝ) :=
    div_nonneg hμ_nonneg ht_real_pos.le
  have hμ_factor_bound :
      μ ^ t / (Nat.factorial t : ℝ) ≤
        ((Real.exp 1 * μ) / (t : ℝ)) ^ t := by
    have hfac_ne : (Nat.factorial t : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero t
    have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt ht_real_pos
    have htpow_ne : (t : ℝ) ^ t ≠ 0 := pow_ne_zero t ht_ne
    calc
      μ ^ t / (Nat.factorial t : ℝ)
          = (μ / (t : ℝ)) ^ t *
              ((t : ℝ) ^ t / (Nat.factorial t : ℝ)) := by
            field_simp [hfac_ne, ht_ne, htpow_ne]
            rw [← mul_pow, div_mul_cancel₀ μ ht_ne]
      _ ≤ (μ / (t : ℝ)) ^ t * Real.exp (t : ℝ) := by
            exact mul_le_mul_of_nonneg_left hfactorial_exp
              (pow_nonneg hμ_div_nonneg t)
      _ = ((Real.exp 1 * μ) / (t : ℝ)) ^ t := by
            have hexp_t : Real.exp (t : ℝ) = (Real.exp 1) ^ t := by
              simpa only [mul_one] using (Real.exp_nat_mul 1 t)
            rw [hexp_t, ← mul_pow]
            field_simp [ht_ne]
  have hbase_nonneg : 0 ≤ (Real.exp 1 * μ) / (t : ℝ) :=
    div_nonneg (mul_nonneg (Real.exp_pos 1).le hμ_nonneg) ht_real_pos.le
  have hbase_le_quarter : (Real.exp 1 * μ) / (t : ℝ) ≤ (1 / 4 : ℝ) := by
    have hμ_mean : μ ≤ A / (4 * Real.exp 1) := by
      simpa [μ] using hmean
    have hexp_mul_le :
        Real.exp 1 * μ ≤ Real.exp 1 * (A / (4 * Real.exp 1)) :=
      mul_le_mul_of_nonneg_left hμ_mean (Real.exp_pos 1).le
    have hexp_mu_le_A : Real.exp 1 * μ ≤ A / 4 := by
      calc
        Real.exp 1 * μ ≤ Real.exp 1 * (A / (4 * Real.exp 1)) := hexp_mul_le
        _ = A / 4 := by
              field_simp [ne_of_gt (Real.exp_pos 1)]
    have hA_div_le_t_div : A / 4 ≤ (t : ℝ) / 4 := by
      linarith
    rw [div_le_iff₀ ht_real_pos]
    linarith
  have hpow_quarter :
      ((Real.exp 1 * μ) / (t : ℝ)) ^ t ≤ (1 / 4 : ℝ) ^ t :=
    pow_le_pow_left₀ hbase_nonneg hbase_le_quarter t
  have hquarter_pos : 0 < (1 / 4 : ℝ) := by norm_num
  have hlog_quarter_le : Real.log (1 / 4 : ℝ) ≤ -(1 / 4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hquarter_pos
    norm_num at h ⊢
    linarith
  have hlog_quarter_nonpos : Real.log (1 / 4 : ℝ) ≤ 0 := by
    linarith
  have hquarter_pow_exp :
      (1 / 4 : ℝ) ^ t =
        Real.exp ((t : ℝ) * Real.log (1 / 4 : ℝ)) := by
    have h := Real.exp_nat_mul (Real.log (1 / 4 : ℝ)) t
    rw [Real.exp_log hquarter_pos] at h
    exact h.symm
  have hquarter_exponent :
      (t : ℝ) * Real.log (1 / 4 : ℝ) ≤ -A / 4 := by
    have hfirst :
        (t : ℝ) * Real.log (1 / 4 : ℝ) ≤
          A * Real.log (1 / 4 : ℝ) :=
      mul_le_mul_of_nonpos_right hA_le_t hlog_quarter_nonpos
    have hsecond :
        A * Real.log (1 / 4 : ℝ) ≤ A * (-(1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_quarter_le hApos.le
    linarith
  have hquarter_tail : (1 / 4 : ℝ) ^ t ≤ Real.exp (-A / 4) := by
    rw [hquarter_pow_exp]
    exact Real.exp_le_exp.mpr hquarter_exponent
  calc
    P ≤ (Nat.choose N ⌈A⌉₊ : ℝ) * p ^ ⌈A⌉₊ := hunion
    _ = (Nat.choose N t : ℝ) * p ^ t := by simp [t]
    _ ≤ μ ^ t / (Nat.factorial t : ℝ) := hchoose_pow
    _ ≤ ((Real.exp 1 * μ) / (t : ℝ)) ^ t := hμ_factor_bound
    _ ≤ (1 / 4 : ℝ) ^ t := hpow_quarter
    _ ≤ Real.exp (-A / 4) := hquarter_tail
