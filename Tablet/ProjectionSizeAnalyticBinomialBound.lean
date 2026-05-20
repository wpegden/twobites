import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.ProjectionSizeAnalyticParameterBounds
import Tablet.ProjectionSizeAnalyticLogRatioBound
import Tablet.ProjectionSizeAnalyticBinomialRatioBounds
import Tablet.ProjectionSizeAnalyticErrorAbsorption
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

-- [TABLET NODE: ProjectionSizeAnalyticBinomialBound]

theorem ProjectionSizeAnalyticBinomialBound :
    ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ n0 : ℕ, ∀ {n m k ℓR ℓB : ℕ},
        n0 ≤ n →
        m = TwoBiteNaturalReducedVertexCount n →
        k = TwoBiteNaturalIndependenceScale (1 + ε) n →
        ℓR * ℓB ≥ k →
        2 * δ * (k : ℝ) < ((2 : ℝ) - (ℓR : ℝ) / (k : ℝ) - (ℓB : ℝ) / (k : ℝ)) * (k : ℝ) →
        let xR : ℝ := (ℓR : ℝ) / (k : ℝ)
        let xB : ℝ := (ℓB : ℝ) / (k : ℝ)
        ((Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k : ℝ) / (Nat.choose (m * m) k : ℝ))
        ≤ Real.exp ((δ - (2 - xR - xB) / 2) * (k : ℝ) * Real.log (n : ℝ)) := by
-- BODY
  intro δ ε hδ hε
  obtain ⟨n0_params, h_params⟩ := ProjectionSizeAnalyticParameterBounds ε hε
  obtain ⟨n0_err, h_err⟩ := ProjectionSizeAnalyticErrorAbsorption δ ε hδ hε
  use max n0_params n0_err
  intro n m k ℓR ℓB hn hm hk hℓR h_s
  
  subst hm
  subst hk
  have hn_ge_n0 : n0_params ≤ n := le_trans (le_max_left _ _) hn
  have hn_ge_err : n0_err ≤ n := le_trans (le_max_right _ _) hn
  have h_params_n := h_params n hn_ge_n0
  have h_err_n := h_err n hn_ge_err
  
  let m := TwoBiteNaturalReducedVertexCount n
  let k := TwoBiteNaturalIndependenceScale (1 + ε) n
  let xR : ℝ := (ℓR : ℝ) / (k : ℝ)
  let xB : ℝ := (ℓB : ℝ) / (k : ℝ)
  let L := Real.log (n : ℝ)
  
  have hk_pos_real : 1 ≤ (k : ℝ) := by exact_mod_cast h_params_n.2.2.1
  have hk_le_n : k ≤ n := h_params_n.2.2.2.1
  have hn_le_m2 : (n : ℝ) ≤ (m : ℝ) ^ 2 := h_params_n.2.2.2.2
  have hk_le_m2 : (k : ℝ) ≤ (m : ℝ) ^ 2 := le_trans (by exact_mod_cast hk_le_n) hn_le_m2
  
  -- Handle the zero numerator cases (ℓR > m or ℓB > m)
  by_cases hm_cases : m < ℓR ∨ m < ℓB
  · rcases hm_cases with hm_R | hm_B
    · have h_zero : Nat.choose m ℓR = 0 := Nat.choose_eq_zero_of_lt hm_R
      have : (Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k : ℝ) = 0 := by
        rw [h_zero]
        simp
      rw [this, zero_div]
      exact (Real.exp_pos _).le
    · have h_zero : Nat.choose m ℓB = 0 := Nat.choose_eq_zero_of_lt hm_B
      have : (Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k : ℝ) = 0 := by
        rw [h_zero]
        simp
      rw [this, zero_div]
      exact (Real.exp_pos _).le
  
  push Not at hm_cases
  have hlR_le_m : ℓR ≤ m := hm_cases.1
  have hlB_le_m : ℓB ≤ m := hm_cases.2
  
  have hk_nat_ge_1 : 1 ≤ k := h_params_n.2.2.1
  have hk_le_lRlB : k ≤ ℓR * ℓB := hℓR
  have hk_le_m_mul_m : k ≤ m * m := by
    have h_sq : m ^ 2 = m * m := by ring
    rw [← h_sq]
    exact_mod_cast hk_le_m2
    
  have hlR_ge_1 : 1 ≤ ℓR := by
    by_contra! h
    have h0 : ℓR = 0 := by omega
    rw [h0, zero_mul] at hℓR
    omega
  have hlB_ge_1 : 1 ≤ ℓB := by
    by_contra! h
    have h0 : ℓB = 0 := by omega
    rw [h0, mul_zero] at hℓR
    omega
  
  -- The numerator and denominator bounds via the helper
  have h_bound_R := (ProjectionSizeAnalyticBinomialRatioBounds m ℓR m hlR_ge_1 hlR_le_m).1
  have h_bound_B := (ProjectionSizeAnalyticBinomialRatioBounds m ℓB m hlB_ge_1 hlB_le_m).1
  have h_bound_k := (ProjectionSizeAnalyticBinomialRatioBounds (ℓR * ℓB) k (ℓR * ℓB) hk_nat_ge_1 hk_le_lRlB).1
  have h_bound_den := (ProjectionSizeAnalyticBinomialRatioBounds (m * m) k (m * m) hk_nat_ge_1 hk_le_m_mul_m).2
  
  have hL_ge_1 : 1 ≤ L := h_err_n.1
  have hk_pos_strict : (0 : ℝ) < k := by linarith
  have hL_pos : 0 < L := by linarith
  have hm_pos : (0 : ℝ) < m := by
    have hn_pos : (0 : ℝ) < n := by
      by_contra! h
      have : (n : ℝ) = 0 := le_antisymm h (by exact_mod_cast Nat.zero_le n)
      have hL_ge_1_unfold : 1 ≤ Real.log (n : ℝ) := hL_ge_1
      rw [this, Real.log_zero] at hL_ge_1_unfold
      linarith
    calc (0 : ℝ) < (n : ℝ) / (2 * L ^ 2) := div_pos hn_pos (by positivity)
      _ ≤ m := h_params_n.1
  have h_denom_lb_pos : (0 : ℝ) < ((m * m : ℝ) / k) ^ k := by positivity
  have h_bound_den_cast : ((m * m : ℝ) / k) ^ k ≤ (Nat.choose (m * m) k : ℝ) := by exact_mod_cast h_bound_den
  have h_denom_pos : (0 : ℝ) < Nat.choose (m * m) k := lt_of_lt_of_le h_denom_lb_pos h_bound_den_cast
  have hlR_pos_real : (0 : ℝ) < ℓR := by exact_mod_cast hlR_ge_1
  have hlB_pos_real : (0 : ℝ) < ℓB := by exact_mod_cast hlB_ge_1

  have h_bound_k_cast : (Nat.choose (ℓR * ℓB) k : ℝ) ≤ (Real.exp 1 * (ℓR * ℓB : ℝ) / k) ^ k := by exact_mod_cast h_bound_k
  have h_num_le : (Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k : ℝ) ≤
      (Real.exp 1 * m / ℓR) ^ ℓR * (Real.exp 1 * m / ℓB) ^ ℓB * (Real.exp 1 * (ℓR * ℓB) / k) ^ k := by
    apply mul_le_mul
    · apply mul_le_mul h_bound_R h_bound_B (by positivity) (by positivity)
    · exact h_bound_k_cast
    · positivity
    · apply mul_nonneg (by positivity) (by positivity)

  have h_div_le : ((Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k : ℝ) / (Nat.choose (m * m) k : ℝ)) ≤
      ((Real.exp 1 * m / ℓR) ^ ℓR * (Real.exp 1 * m / ℓB) ^ ℓB * (Real.exp 1 * (ℓR * ℓB) / k) ^ k) / ((m * m : ℝ) / k) ^ k := by
    calc ((Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k : ℝ) / (Nat.choose (m * m) k : ℝ))
      _ ≤ ((Real.exp 1 * m / ℓR) ^ ℓR * (Real.exp 1 * m / ℓB) ^ ℓB * (Real.exp 1 * (ℓR * ℓB) / k) ^ k) / (Nat.choose (m * m) k : ℝ) := div_le_div_of_nonneg_right h_num_le (le_of_lt h_denom_pos)
      _ ≤ ((Real.exp 1 * m / ℓR) ^ ℓR * (Real.exp 1 * m / ℓB) ^ ℓB * (Real.exp 1 * (ℓR * ℓB) / k) ^ k) / ((m * m : ℝ) / k) ^ k := by
        have h_num_nonneg : 0 ≤ (Real.exp 1 * m / ℓR) ^ ℓR * (Real.exp 1 * m / ℓB) ^ ℓB * (Real.exp 1 * (ℓR * ℓB) / k) ^ k := by positivity
        exact (div_le_div_iff₀ h_denom_pos h_denom_lb_pos).mpr (mul_le_mul_of_nonneg_left h_bound_den_cast h_num_nonneg)

  let RHS_div := ((Real.exp 1 * m / ℓR) ^ ℓR * (Real.exp 1 * m / ℓB) ^ ℓB * (Real.exp 1 * (ℓR * ℓB) / k) ^ k) / ((m * m : ℝ) / k) ^ k
  
  have hxR : xR = (ℓR : ℝ) / (k : ℝ) := rfl
  have hxB : xB = (ℓB : ℝ) / (k : ℝ) := rfl

  have h_log_RHS : Real.log RHS_div = k * (xR + xB + 1) + k * (xR + xB - 2) * Real.log (m / k) - k * (xR - 1) * Real.log xR - k * (xB - 1) * Real.log xB := by
    have epos : 0 < Real.exp 1 := Real.exp_pos 1
    have t1 : 0 < Real.exp 1 * m / ℓR := by positivity
    have t2 : 0 < Real.exp 1 * m / ℓB := by positivity
    have t3 : 0 < Real.exp 1 * (ℓR * ℓB) / k := by positivity
    have t4 : 0 < (m * m : ℝ) / k := by positivity
    have t4_pow : 0 < (((m * m : ℝ) / k) ^ k) := by positivity
    have t5 : 0 < (Real.exp 1 * m / ℓR) ^ ℓR * (Real.exp 1 * m / ℓB) ^ ℓB * (Real.exp 1 * (ℓR * ℓB) / k) ^ k := by positivity
    rw [Real.log_div t5.ne' t4_pow.ne']
    have h_num_mul1 : Real.log ((Real.exp 1 * m / ℓR) ^ ℓR * (Real.exp 1 * m / ℓB) ^ ℓB * (Real.exp 1 * (ℓR * ℓB) / k) ^ k) =
        Real.log ((Real.exp 1 * m / ℓR) ^ ℓR) + Real.log ((Real.exp 1 * m / ℓB) ^ ℓB) + Real.log ((Real.exp 1 * (ℓR * ℓB) / k) ^ k) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    rw [h_num_mul1]
    have h_pow1 : Real.log ((Real.exp 1 * m / ℓR) ^ ℓR) = ℓR * Real.log (Real.exp 1 * m / ℓR) := by
      have : ((Real.exp 1 * m / ℓR) ^ ℓR) = ((Real.exp 1 * m / ℓR) : ℝ) ^ (ℓR : ℝ) := by norm_cast
      rw [this, Real.log_rpow t1]
    have h_pow2 : Real.log ((Real.exp 1 * m / ℓB) ^ ℓB) = ℓB * Real.log (Real.exp 1 * m / ℓB) := by
      have : ((Real.exp 1 * m / ℓB) ^ ℓB) = ((Real.exp 1 * m / ℓB) : ℝ) ^ (ℓB : ℝ) := by norm_cast
      rw [this, Real.log_rpow t2]
    have h_pow3 : Real.log ((Real.exp 1 * (ℓR * ℓB) / k) ^ k) = k * Real.log (Real.exp 1 * (ℓR * ℓB) / k) := by
      have : ((Real.exp 1 * (ℓR * ℓB) / k) ^ k) = ((Real.exp 1 * (ℓR * ℓB) / k) : ℝ) ^ (k : ℝ) := by norm_cast
      rw [this, Real.log_rpow t3]
    have h_pow4 : Real.log (((m * m : ℝ) / k) ^ k) = k * Real.log ((m * m : ℝ) / k) := by
      have : (((m * m : ℝ) / k) ^ k) = (((m * m : ℝ) / k) : ℝ) ^ (k : ℝ) := by norm_cast
      rw [this, Real.log_rpow t4]
    rw [h_pow1, h_pow2, h_pow3, h_pow4]
    
    have log_m : Real.log (m / k) = Real.log m - Real.log k := Real.log_div hm_pos.ne' hk_pos_strict.ne'
    have log_xR : Real.log xR = Real.log ℓR - Real.log k := by rw [hxR, Real.log_div hlR_pos_real.ne' hk_pos_strict.ne']
    have log_xB : Real.log xB = Real.log ℓB - Real.log k := by rw [hxB, Real.log_div hlB_pos_real.ne' hk_pos_strict.ne']
    
    have log1 : Real.log (Real.exp 1 * m / ℓR) = 1 + Real.log m - Real.log ℓR := by
      rw [Real.log_div (by positivity) hlR_pos_real.ne', Real.log_mul epos.ne' hm_pos.ne', Real.log_exp]
    have log2 : Real.log (Real.exp 1 * m / ℓB) = 1 + Real.log m - Real.log ℓB := by
      rw [Real.log_div (by positivity) hlB_pos_real.ne', Real.log_mul epos.ne' hm_pos.ne', Real.log_exp]
    have log3 : Real.log (Real.exp 1 * (ℓR * ℓB) / k) = 1 + Real.log ℓR + Real.log ℓB - Real.log k := by
      rw [Real.log_div (by positivity) hk_pos_strict.ne', Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp]
      ring
    have log4 : Real.log ((m * m : ℝ) / k) = Real.log m + Real.log m - Real.log k := by
      rw [Real.log_div (by positivity) hk_pos_strict.ne', Real.log_mul hm_pos.ne' hm_pos.ne']

    rw [log1, log2, log3, log4, log_m, log_xR, log_xB]
    have hxR_mul : (ℓR : ℝ) = xR * k := by
      rw [hxR]
      exact (div_mul_cancel₀ (ℓR : ℝ) hk_pos_strict.ne').symm
    have hxB_mul : (ℓB : ℝ) = xB * k := by
      rw [hxB]
      exact (div_mul_cancel₀ (ℓB : ℝ) hk_pos_strict.ne').symm
    rw [hxR_mul, hxB_mul]
    ring

  have hL_eq : L = Real.log (n : ℝ) := rfl
  have h_bound_logm : (1/2 : ℝ) * L - (5/2 : ℝ) * Real.log L - Real.log (4 * (1 + ε)) ≤ Real.log ((m : ℝ) / (k : ℝ)) := by
    exact ProjectionSizeAnalyticLogRatioBound hL_eq h_params_n.1 h_params_n.2.1 hk_nat_ge_1 hε h_err_n.1

  have hxR_pos : 0 < xR := by rw [hxR]; positivity
  have hxB_pos : 0 < xB := by rw [hxB]; positivity
  have hR_le : -(xR - 1) * Real.log xR ≤ 0 := by
    have : -(xR - 1) * Real.log xR = (1 - xR) * Real.log xR := by ring
    rw [this]
    by_cases h_le : xR ≤ 1
    · have h1 : 0 ≤ 1 - xR := sub_nonneg.mpr h_le
      have h2 : Real.log xR ≤ 0 := Real.log_nonpos hxR_pos.le h_le
      exact mul_nonpos_of_nonneg_of_nonpos h1 h2
    · push Not at h_le
      have h1 : 1 - xR ≤ 0 := sub_nonpos.mpr h_le.le
      have h2 : 0 ≤ Real.log xR := Real.log_nonneg h_le.le
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2
      
  have hB_le : -(xB - 1) * Real.log xB ≤ 0 := by
    have : -(xB - 1) * Real.log xB = (1 - xB) * Real.log xB := by ring
    rw [this]
    by_cases h_le : xB ≤ 1
    · have h1 : 0 ≤ 1 - xB := sub_nonneg.mpr h_le
      have h2 : Real.log xB ≤ 0 := Real.log_nonpos hxB_pos.le h_le
      exact mul_nonpos_of_nonneg_of_nonpos h1 h2
    · push Not at h_le
      have h1 : 1 - xB ≤ 0 := sub_nonpos.mpr h_le.le
      have h2 : 0 ≤ Real.log xB := Real.log_nonneg h_le.le
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2

  have h_log_bound : Real.log RHS_div ≤ (δ - (2 - xR - xB) / 2) * (k : ℝ) * L := by
    have h_neg : xR + xB - 2 < 0 := by
      have h1 : 2 * δ * (k : ℝ) < (2 - xR - xB) * (k : ℝ) := h_s
      have h2 : 0 < 2 * δ * (k : ℝ) := mul_pos (mul_pos zero_lt_two hδ) hk_pos_strict
      have h3 : 0 < (2 - xR - xB) * (k : ℝ) := lt_trans h2 h1
      have h3_comm : 0 < (k : ℝ) * (2 - xR - xB) := by rwa [mul_comm] at h3
      have h_sub : 0 < 2 - xR - xB := pos_of_mul_pos_right h3_comm hk_pos_strict.le
      linarith only [h_sub]
    have h_log_m_term : (xR + xB - 2) * Real.log (m / k) ≤ (xR + xB - 2) * ((1/2 : ℝ) * L - (5/2 : ℝ) * Real.log L - Real.log (4 * (1 + ε))) :=
      mul_le_mul_of_nonpos_left h_bound_logm h_neg.le

    have h_alg1 : k * (xR + xB + 1) + k * (xR + xB - 2) * Real.log (m / k) - k * (xR - 1) * Real.log xR - k * (xB - 1) * Real.log xB =
        k * (xR + xB + 1) + k * ((xR + xB - 2) * Real.log (m / k)) + k * (-(xR - 1) * Real.log xR) + k * (-(xB - 1) * Real.log xB) := by ring

    have h_alg2 : k * (xR + xB + 1) + k * ((xR + xB - 2) * ((1/2 : ℝ) * L - (5/2 : ℝ) * Real.log L - Real.log (4 * (1 + ε)))) + 0 + 0 =
        (k : ℝ) * ((xR + xB + 1) - (2 - xR - xB) / 2 * L + (2 - xR - xB) * ((5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε)))) := by ring

    calc Real.log RHS_div = k * (xR + xB + 1) + k * (xR + xB - 2) * Real.log (m / k) - k * (xR - 1) * Real.log xR - k * (xB - 1) * Real.log xB := h_log_RHS
      _ = k * (xR + xB + 1) + k * ((xR + xB - 2) * Real.log (m / k)) + k * (-(xR - 1) * Real.log xR) + k * (-(xB - 1) * Real.log xB) := h_alg1
      _ ≤ k * (xR + xB + 1) + k * ((xR + xB - 2) * ((1/2 : ℝ) * L - (5/2 : ℝ) * Real.log L - Real.log (4 * (1 + ε)))) + 0 + 0 := by
        apply add_le_add
        · apply add_le_add
          · apply add_le_add (le_refl _)
            exact mul_le_mul_of_nonneg_left h_log_m_term hk_pos_strict.le
          · exact mul_nonpos_of_nonneg_of_nonpos hk_pos_strict.le hR_le
        · exact mul_nonpos_of_nonneg_of_nonpos hk_pos_strict.le hB_le
      _ = (k : ℝ) * ((xR + xB + 1) - (2 - xR - xB) / 2 * L + (2 - xR - xB) * ((5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε)))) := h_alg2
      _ ≤ (k : ℝ) * (δ * L - (2 - xR - xB) / 2 * L) := by
        apply mul_le_mul_of_nonneg_left _ hk_pos_strict.le
        have h_C_nonneg : 0 ≤ (5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε)) := by
          have h1 : 0 ≤ Real.log L := Real.log_nonneg h_err_n.1
          have h2 : 0 ≤ Real.log (4 * (1 + ε)) := by
            have : (1 : ℝ) ≤ 4 * (1 + ε) := by linarith
            exact Real.log_nonneg this
          positivity
        have h_sum_le : xR + xB + 1 ≤ 3 := by
          have h1 : 2 * δ * (k : ℝ) < (2 - xR - xB) * (k : ℝ) := h_s
          have h2 : 0 < 2 * δ * (k : ℝ) := mul_pos (mul_pos zero_lt_two hδ) hk_pos_strict
          have h3 : 0 < (2 - xR - xB) * (k : ℝ) := lt_trans h2 h1
          have h3_comm : 0 < (k : ℝ) * (2 - xR - xB) := by rwa [mul_comm] at h3
          have h_sub : 0 < 2 - xR - xB := pos_of_mul_pos_right h3_comm hk_pos_strict.le
          linarith only [h_sub]
        have h_prod_le : (2 - xR - xB) * ((5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε))) ≤ 2 * ((5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε))) := by
          apply mul_le_mul_of_nonneg_right _ h_C_nonneg
          have h_xR_pos : 0 ≤ xR := by positivity
          have h_xB_pos : 0 ≤ xB := by positivity
          linarith only [h_xR_pos, h_xB_pos]
        have h_bound_add : xR + xB + 1 + (2 - xR - xB) * ((5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε))) ≤ 3 + 2 * ((5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε))) := add_le_add h_sum_le h_prod_le
        have h_bound_delta : xR + xB + 1 + (2 - xR - xB) * ((5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε))) ≤ δ * L := le_trans h_bound_add h_err_n.2
        calc xR + xB + 1 - (2 - xR - xB) / 2 * L + (2 - xR - xB) * ((5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε)))
          _ = xR + xB + 1 + (2 - xR - xB) * ((5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε))) - (2 - xR - xB) / 2 * L := by ring
          _ ≤ δ * L - (2 - xR - xB) / 2 * L := sub_le_sub_right h_bound_delta _
      _ = ((δ - (2 - xR - xB) / 2) * (k : ℝ) * L) := by ring

  have RHS_div_pos : 0 < RHS_div := by positivity
  have h_exp_bound : RHS_div ≤ Real.exp ((δ - (2 - xR - xB) / 2) * (k : ℝ) * L) := (Real.log_le_iff_le_exp RHS_div_pos).mp h_log_bound
  exact le_trans h_div_le h_exp_bound
