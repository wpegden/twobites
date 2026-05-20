import Tablet.ParameterHierarchy
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteNaturalIndependenceScale
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Monoid
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

open Filter Topology

-- [TABLET NODE: FixedSetProjectionBinomialSummationMargins]

theorem FixedSetProjectionBinomialSummationMargins :
    ∀ {ε ε1 ε2 η δ : ℝ} {n0 : ℕ},
      ParameterHierarchy ε ε1 ε2 n0 →
      0 < η →
      0 < δ →
        ∃ N : ℕ, n0 ≤ N ∧
          ∀ n : ℕ, N < n →
            let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
            1 ≤ K ∧ K ≤ n ∧
              Real.log (Nat.choose n K : ℝ) ≤
                ((1 / 2 : ℝ) + η) * (K : ℝ) * Real.log (n : ℝ) ∧
              2 * Real.log ((K + 1 : ℕ) : ℝ) + Real.log δ⁻¹ ≤
                η * (K : ℝ) * Real.log (n : ℝ) := by
-- BODY
  intro ε ε1 ε2 η δ n0 h_param hη hδ
  have h_ε_pos : 0 < ε := lt_trans h_param.1 h_param.2.1 |>.trans h_param.2.2.1
  have h_ε_lt1 : ε < 1 := h_param.2.2.2.1
  have h_comps := h_param.2.2.2.2.2.2.2.2
  have fixed_set_margins_eventually :
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ Real.log n ∧
      (1 : ℝ) ≤ Real.sqrt (n * Real.log n) ∧
      9 * Real.log n ≤ n ∧
      η⁻¹ ≤ Real.log n ∧
      2 * Real.log 4 + max 0 (Real.log δ⁻¹) ≤ Real.log n ∧
      (3 : ℝ) ≤ η * Real.sqrt (n * Real.log n) := by
    have t_cast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have t1 : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Tendsto.comp Real.tendsto_log_atTop t_cast
    have t2 : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) atTop atTop := by
      refine Tendsto.comp Real.tendsto_sqrt_atTop ?_
      exact Tendsto.atTop_mul_atTop₀ t_cast t1
    have ev1 := t1.eventually (eventually_ge_atTop 1)
    have ev2 := t2.eventually (eventually_ge_atTop 1)
    have ev3 : ∀ᶠ n : ℕ in atTop, 9 * Real.log (n : ℝ) ≤ (n : ℝ) := by
      have o1 : (fun n : ℝ => Real.log n) =o[atTop] (fun n : ℝ => n) := Real.isLittleO_log_id_atTop
      have o2 := Asymptotics.IsLittleO.comp_tendsto o1 t_cast
      have bnd := o2.bound (by norm_num : (0 : ℝ) < 1/9)
      filter_upwards [bnd, ev1, t_cast.eventually (eventually_ge_atTop 0)] with n hn h1 h_n_nonneg
      dsimp at hn
      rw [abs_of_pos (lt_of_lt_of_le zero_lt_one h1)] at hn
      rw [abs_of_nonneg h_n_nonneg] at hn
      linarith
    have ev4 := t1.eventually (eventually_ge_atTop η⁻¹)
    have ev5 := t1.eventually (eventually_ge_atTop (2 * Real.log 4 + max 0 (Real.log δ⁻¹)))
    have ev6 : ∀ᶠ n : ℕ in atTop, 3 ≤ η * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      have t3 : Tendsto (fun n : ℕ => η * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) atTop atTop :=
        Tendsto.const_mul_atTop hη t2
      exact t3.eventually (eventually_ge_atTop 3)
    filter_upwards [ev1, ev2, ev3, ev4, ev5, ev6] with n h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp fixed_set_margins_eventually
  use max n0 N1
  refine ⟨le_max_left _ _, fun n hn => ?_⟩
  have hn_n0 : n0 < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn_N1 : N1 < n := lt_of_le_of_lt (le_max_right _ _) hn
  have h_margins := hN1 n (le_of_lt hn_N1)
  have h_comp := h_comps n hn_n0
  obtain ⟨h_margin_1, h_margin_2, h_margin_3, h_margin_4, h_margin_5, h_margin_6⟩ := h_margins
  let S := Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  have hkReal_le : (1 + ε) * S ≤ (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) := h_comp.2.2.2.2.1
  have hkReal_lt : (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) < (1 + ε) * S + 1 := h_comp.2.2.2.2.2.1
  let K := TwoBiteNaturalIndependenceScale (1 + ε) n
  have h1_le_K_real : (1 : ℝ) ≤ K := by
    calc (1 : ℝ) ≤ S := h_margin_2
      _ ≤ 1 * S := by rw [one_mul]
      _ ≤ (1 + ε) * S := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ K := hkReal_le
  have h1_le_K : 1 ≤ K := Nat.cast_le.mp (by exact_mod_cast h1_le_K_real)
  have hn_pos_nat : 0 < n := Nat.zero_lt_of_lt hn_N1
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hK_le_n_real : (K : ℝ) ≤ n := by
    have h_K_lt_3S : (K : ℝ) < 3 * S := by
      have h1_S : 1 ≤ S := h_margin_2
      have hs_pos : 0 < S := by linarith
      have h_mul : (1 + ε) * S < 2 * S := by
        calc (1 + ε) * S = S + ε * S := by ring
          _ < S + 1 * S := by
            have : ε * S < 1 * S := mul_lt_mul_of_pos_right h_ε_lt1 hs_pos
            linarith
          _ = 2 * S := by ring
      calc (K : ℝ) < (1 + ε) * S + 1 := hkReal_lt
        _ < 2 * S + 1 := by linarith [h_mul]
        _ ≤ 3 * S := by linarith
    have h_3S_le_n : 3 * S ≤ (n : ℝ) := by
      have h_sqrt_n_log_n_nonneg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by
        apply mul_nonneg hn_nonneg
        linarith
      have hs : 9 * S ^ 2 = 9 * ((n : ℝ) * Real.log (n : ℝ)) := by
        calc 9 * S ^ 2 = 9 * (Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ^ 2 := rfl
          _ = 9 * ((n : ℝ) * Real.log (n : ℝ)) := by rw [Real.sq_sqrt h_sqrt_n_log_n_nonneg]
      have h_9S2_le_n2 : 9 * S ^ 2 ≤ (n : ℝ) ^ 2 := by
        calc 9 * S ^ 2 = (n : ℝ) * (9 * Real.log (n : ℝ)) := by rw [hs]; ring
          _ ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left h_margin_3 hn_nonneg
          _ = (n : ℝ) ^ 2 := by ring
      have h_sqrt : Real.sqrt (9 * S ^ 2) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt h_9S2_le_n2
      have h_left : Real.sqrt (9 * S ^ 2) = 3 * S := by
        have h_9_nonneg : (0 : ℝ) ≤ 9 := by norm_num
        have h_S_nonneg : 0 ≤ S := by positivity
        rw [Real.sqrt_mul h_9_nonneg, Real.sqrt_sq h_S_nonneg]
        have h_sqrt9 : Real.sqrt 9 = 3 := by
          have : (9 : ℝ) = 3 ^ 2 := by norm_num
          rw [this, Real.sqrt_sq (by norm_num)]
        rw [h_sqrt9]
      have h_right : Real.sqrt ((n : ℝ) ^ 2) = n := Real.sqrt_sq hn_nonneg
      rwa [h_left, h_right] at h_sqrt
    exact le_trans (le_of_lt h_K_lt_3S) h_3S_le_n
  have hK_le_n : K ≤ n := Nat.cast_le.mp hK_le_n_real

  have h_choose_le : (Nat.choose n K : ℝ) ≤ ((Real.exp 1 * (n : ℝ)) / (K : ℝ)) ^ K := by
    have h_desc : K.factorial * Nat.choose n K = n.descFactorial K := (Nat.descFactorial_eq_factorial_mul_choose n K).symm
    have h_pow : n.descFactorial K ≤ n ^ K := Nat.descFactorial_le_pow n K
    have h_mul_le : K.factorial * Nat.choose n K ≤ n ^ K := by omega
    have h_mul_le_real : (Nat.choose n K : ℝ) * (K.factorial : ℝ) ≤ (n : ℝ) ^ K := by
      calc (Nat.choose n K : ℝ) * (K.factorial : ℝ) = (K.factorial : ℝ) * (Nat.choose n K : ℝ) := mul_comm _ _
        _ ≤ (n : ℝ) ^ K := by exact_mod_cast h_mul_le
    have h_kfact_pos : (0 : ℝ) < K.factorial := Nat.cast_pos.mpr K.factorial_pos
    have h_choose_le_div : (Nat.choose n K : ℝ) ≤ (n : ℝ) ^ K / (K.factorial : ℝ) :=
      (le_div_iff₀ h_kfact_pos).mpr h_mul_le_real
    have h_K_nonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
    have h_exp_bound := Real.pow_div_factorial_le_exp (K : ℝ) h_K_nonneg K
    have h_kfact_lower : (K : ℝ) ^ K / Real.exp (K : ℝ) ≤ (K.factorial : ℝ) := by
      have h_exp_pos : 0 < Real.exp (K : ℝ) := Real.exp_pos (K : ℝ)
      rw [div_le_iff₀ h_kfact_pos] at h_exp_bound
      exact (div_le_iff₀' h_exp_pos).mpr h_exp_bound
    have h_choose_le_pow : (Nat.choose n K : ℝ) ≤ (n : ℝ) ^ K / ((K : ℝ) ^ K / Real.exp (K : ℝ)) := by
      have h_denom_pos : 0 < (K : ℝ) ^ K / Real.exp (K : ℝ) :=
        div_pos (pow_pos (Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) h1_le_K)) K) (Real.exp_pos (K : ℝ))
      calc (Nat.choose n K : ℝ) ≤ (n : ℝ) ^ K / (K.factorial : ℝ) := h_choose_le_div
        _ ≤ (n : ℝ) ^ K / ((K : ℝ) ^ K / Real.exp (K : ℝ)) := by
          apply div_le_div_of_nonneg_left
          · positivity
          · exact h_denom_pos
          · exact h_kfact_lower
    have h_simplify : (n : ℝ) ^ K / ((K : ℝ) ^ K / Real.exp (K : ℝ)) = ((Real.exp 1 * (n : ℝ)) / (K : ℝ)) ^ K := by
      have h_exp : Real.exp (K : ℝ) = Real.exp 1 ^ K := by
        have := Real.exp_nat_mul 1 K
        rw [mul_one] at this
        exact this
      calc
        (n : ℝ) ^ K / ((K : ℝ) ^ K / Real.exp (K : ℝ)) = Real.exp (K : ℝ) * (n : ℝ) ^ K / (K : ℝ) ^ K := by
          rw [div_eq_mul_inv, inv_div, ←mul_div_assoc, mul_comm]
        _ = (Real.exp 1) ^ K * (n : ℝ) ^ K / (K : ℝ) ^ K := by rw [h_exp]
        _ = ((Real.exp 1) * (n : ℝ)) ^ K / (K : ℝ) ^ K := by rw [← mul_pow]
        _ = ((Real.exp 1 * (n : ℝ)) / (K : ℝ)) ^ K := by rw [← div_pow]
    exact le_trans h_choose_le_pow (le_of_eq h_simplify)

  have hk_pos_real : 0 < (K : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) h1_le_K)
  have h_choose_pos : 0 < (Nat.choose n K : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hK_le_n)
  have h_exp_n_div_k_pos : 0 < (Real.exp 1 * (n : ℝ)) / (K : ℝ) :=
    div_pos (mul_pos (Real.exp_pos 1) hn_pos) hk_pos_real
  
  have h_log_choose : Real.log (Nat.choose n K : ℝ) ≤ (K : ℝ) * Real.log (Real.exp 1 * (n : ℝ) / (K : ℝ)) := by
    have h_pow_pos : 0 ≤ ((Real.exp 1 * (n : ℝ)) / (K : ℝ)) := le_of_lt h_exp_n_div_k_pos
    calc
      Real.log (Nat.choose n K : ℝ) ≤ Real.log (((Real.exp 1 * (n : ℝ)) / (K : ℝ)) ^ K) :=
        Real.log_le_log h_choose_pos h_choose_le
      _ = (K : ℝ) * Real.log ((Real.exp 1 * (n : ℝ)) / (K : ℝ)) := by
        rw [← Real.log_rpow h_exp_n_div_k_pos, Real.rpow_natCast]

  have h_log_S : Real.log S = (1 / 2 : ℝ) * Real.log (n : ℝ) + (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) := by
    calc Real.log S = (1 / 2 : ℝ) * Real.log ((n : ℝ) * Real.log (n : ℝ)) := by
          have : S = ((n : ℝ) * Real.log (n : ℝ)) ^ (1 / 2 : ℝ) := by
            dsimp [S]
            rw [Real.sqrt_eq_rpow]
          rw [this, Real.log_rpow (by positivity)]
      _ = (1 / 2 : ℝ) * (Real.log (n : ℝ) + Real.log (Real.log (n : ℝ))) := by
          rw [Real.log_mul (ne_of_gt hn_pos) (ne_of_gt (lt_of_lt_of_le zero_lt_one h_margin_1))]
      _ = (1 / 2 : ℝ) * Real.log (n : ℝ) + (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) := by ring

  have h_log_K_lower : (1 / 2 : ℝ) * Real.log (n : ℝ) + (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) ≤ Real.log (K : ℝ) := by
    calc (1 / 2 : ℝ) * Real.log (n : ℝ) + (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) = Real.log S := h_log_S.symm
      _ ≤ Real.log (K : ℝ) := Real.log_le_log (by positivity) (by
        calc S ≤ 1 * S := by rw [one_mul]
          _ ≤ (1 + ε) * S := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
          _ ≤ K := hkReal_le)

  have h_log_choose_final : Real.log (Nat.choose n K : ℝ) ≤ ((1 / 2 : ℝ) + η) * (K : ℝ) * Real.log (n : ℝ) := by
    calc Real.log (Nat.choose n K : ℝ) ≤ (K : ℝ) * Real.log (Real.exp 1 * (n : ℝ) / (K : ℝ)) := h_log_choose
      _ = (K : ℝ) * (Real.log (Real.exp 1 * (n : ℝ)) - Real.log (K : ℝ)) := by
        rw [Real.log_div (ne_of_gt (mul_pos (Real.exp_pos 1) hn_pos)) (ne_of_gt hk_pos_real)]
      _ = (K : ℝ) * (Real.log (Real.exp 1) + Real.log (n : ℝ) - Real.log (K : ℝ)) := by
        rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hn_pos)]
      _ = (K : ℝ) * (1 + Real.log (n : ℝ) - Real.log (K : ℝ)) := by rw [Real.log_exp]
      _ ≤ (K : ℝ) * (1 + Real.log (n : ℝ) - ((1 / 2 : ℝ) * Real.log (n : ℝ) + (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)))) := by
        gcongr
      _ = (K : ℝ) * (1 + (1 / 2 : ℝ) * Real.log (n : ℝ) - (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ))) := by ring
      _ ≤ (K : ℝ) * ((1 / 2 : ℝ) * Real.log (n : ℝ) + η * Real.log (n : ℝ)) := by
        gcongr
        have h_log_log_pos : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg h_margin_1
        calc 1 + (1 / 2 : ℝ) * Real.log (n : ℝ) - (1 / 2 : ℝ) * Real.log (Real.log (n : ℝ)) ≤ 1 + (1 / 2 : ℝ) * Real.log (n : ℝ) := by linarith
          _ ≤ η * Real.log (n : ℝ) + (1 / 2 : ℝ) * Real.log (n : ℝ) := by
            have : (1 : ℝ) ≤ η * Real.log (n : ℝ) := by
              calc (1 : ℝ) = η * η⁻¹ := (mul_inv_cancel₀ (ne_of_gt hη)).symm
                _ ≤ η * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left h_margin_4 (le_of_lt hη)
            linarith
          _ = (1 / 2 : ℝ) * Real.log (n : ℝ) + η * Real.log (n : ℝ) := by ring
      _ = ((1 / 2 : ℝ) + η) * (K : ℝ) * Real.log (n : ℝ) := by ring

  have hk_plus_one_le : (K : ℝ) + 1 ≤ 2 * (n : ℝ) := by
    have h_n_lower : (1 : ℝ) ≤ (n : ℝ) := by
      have h_exp : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
      have h_n : Real.exp (1 : ℝ) ≤ (n : ℝ) := by
        rw [← Real.log_le_log_iff (Real.exp_pos 1) (by positivity)]
        rw [Real.log_exp]
        exact h_margin_1
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp 1 := Real.exp_le_exp.mpr zero_le_one
        _ ≤ (n : ℝ) := h_n
    linarith

  have h_log_k_plus_one : Real.log ((K : ℝ) + 1) ≤ Real.log 2 + Real.log (n : ℝ) := by
    calc Real.log ((K : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
        Real.log_le_log (by positivity) hk_plus_one_le
      _ = Real.log 2 + Real.log (n : ℝ) := Real.log_mul (by norm_num) (ne_of_gt hn_pos)

  have h_bound1 : 2 * Real.log ((K : ℝ) + 1) + Real.log δ⁻¹ ≤ 3 * Real.log (n : ℝ) := by
    have h_log4 : 2 * Real.log 2 = Real.log 4 := by
      have : (4 : ℝ) = 2^2 := by norm_num
      rw [this, Real.log_pow, Nat.cast_two]
    have h_log4_pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h_max_le : 2 * Real.log 2 + max 0 (Real.log δ⁻¹) ≤ Real.log (n : ℝ) := by
      calc 2 * Real.log 2 + max 0 (Real.log δ⁻¹) = Real.log 4 + max 0 (Real.log δ⁻¹) := by rw [h_log4]
        _ ≤ 2 * Real.log 4 + max 0 (Real.log δ⁻¹) := by linarith
        _ ≤ Real.log (n : ℝ) := h_margin_5
    calc 2 * Real.log ((K : ℝ) + 1) + Real.log δ⁻¹ ≤ 2 * (Real.log 2 + Real.log (n : ℝ)) + Real.log δ⁻¹ := by gcongr
      _ = 2 * Real.log 2 + 2 * Real.log (n : ℝ) + Real.log δ⁻¹ := by ring
      _ ≤ 2 * Real.log 2 + 2 * Real.log (n : ℝ) + max 0 (Real.log δ⁻¹) := by gcongr; exact le_max_right 0 (Real.log δ⁻¹)
      _ = 2 * Real.log 2 + max 0 (Real.log δ⁻¹) + 2 * Real.log (n : ℝ) := by ring
      _ ≤ Real.log (n : ℝ) + 2 * Real.log (n : ℝ) := by linarith
      _ = 3 * Real.log (n : ℝ) := by ring

  have h_bound2 : 3 * Real.log (n : ℝ) ≤ η * (K : ℝ) * Real.log (n : ℝ) := by
    calc 3 * Real.log (n : ℝ) ≤ (η * S) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right h_margin_6 (by linarith)
      _ = η * S * Real.log (n : ℝ) := by ring
      _ ≤ η * (K : ℝ) * Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left
          · calc S ≤ 1 * S := by rw [one_mul]
              _ ≤ (1 + ε) * S := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
              _ ≤ K := hkReal_le
          · exact le_of_lt hη
        · linarith

  have h_log_bound_final : 2 * Real.log ((K + 1 : ℕ) : ℝ) + Real.log δ⁻¹ ≤ η * (K : ℝ) * Real.log (n : ℝ) := by
    have : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := Nat.cast_add_one K
    rw [this]
    exact le_trans h_bound1 h_bound2

  exact ⟨h1_le_K, hK_le_n, h_log_choose_final, h_log_bound_final⟩