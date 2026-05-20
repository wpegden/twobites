import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.ParameterHierarchyBaseThreshold
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field

open Filter Topology

-- [TABLET NODE: ProjectionSizeAnalyticParameterBounds]

theorem ProjectionSizeAnalyticParameterBounds :
    ∀ ε : ℝ, 0 < ε →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        let m := TwoBiteNaturalReducedVertexCount n
        let k := TwoBiteNaturalIndependenceScale (1 + ε) n
        let L := Real.log (n : ℝ)
        ((n : ℝ) / (2 * L ^ 2) ≤ (m : ℝ)) ∧
        ((k : ℝ) ≤ 2 * (1 + ε) * Real.sqrt ((n : ℝ) * L)) ∧
        (1 ≤ k) ∧ (k ≤ n) ∧ ((n : ℝ) ≤ (m : ℝ) ^ 2) := by
-- BODY
  intro ε hε
  have t_cast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop (R := ℝ)
  
  have he1 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
    have ho : (fun x : ℝ => (Real.log x) ^ 2) =o[atTop] (fun x : ℝ => x) :=
      Real.isLittleO_pow_log_id_atTop
    have ho_comp := ho.comp_tendsto t_cast
    have h_bound := ho_comp.bound (by norm_num : 0 < (1 / 2 : ℝ))
    filter_upwards [h_bound, t_cast.eventually (eventually_ge_atTop (1 : ℝ)),
      (Real.tendsto_log_atTop.comp t_cast).eventually (eventually_ge_atTop (1 : ℝ))] with n hn hn1 hlog
    dsimp at hn
    have h_sq_pos : 0 < Real.log (n : ℝ) ^ 2 := by positivity
    rw [abs_of_pos h_sq_pos] at hn
    rw [abs_of_pos (lt_of_lt_of_le zero_lt_one hn1)] at hn
    rw [le_div_iff₀ h_sq_pos]
    linarith

  have he2 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 4 := by
    have ho : (fun x : ℝ => (Real.log x) ^ 4) =o[atTop] (fun x : ℝ => x) :=
      Real.isLittleO_pow_log_id_atTop
    have ho_comp := ho.comp_tendsto t_cast
    have h_bound := ho_comp.bound (by norm_num : 0 < (1 / 4 : ℝ))
    filter_upwards [h_bound, t_cast.eventually (eventually_ge_atTop (1 : ℝ)),
      (Real.tendsto_log_atTop.comp t_cast).eventually (eventually_ge_atTop (1 : ℝ))] with n hn hn1 hlog
    dsimp at hn
    have h_sq_pos : 0 < Real.log (n : ℝ) ^ 4 := by positivity
    rw [abs_of_pos h_sq_pos] at hn
    rw [abs_of_pos (lt_of_lt_of_le zero_lt_one hn1)] at hn
    rw [le_div_iff₀ h_sq_pos]
    linarith

  have hlog_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp t_cast
    
  obtain ⟨n0_base, hn0_base⟩ := ParameterHierarchyBaseThreshold ε hε
  have he3 : ∀ᶠ n : ℕ in atTop, n0_base < n := eventually_gt_atTop n0_base
  have he4 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) < Real.log (n : ℝ) := hlog_atTop.eventually_gt_atTop 1

  have h_all : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 ∧
      (4 : ℝ) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 4 ∧
      n0_base < n ∧ (1 : ℝ) < Real.log (n : ℝ) := by
    filter_upwards [he1, he2, he3, he4] with n hn1 hn2 hn3 hn4
    exact ⟨hn1, hn2, hn3, hn4⟩
  
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_all
  use N
  intro n hn
  have h_props := hN n hn
  have hn_base := hn0_base n h_props.2.2.1
  rcases hn_base with ⟨hm_pos, hp_nonneg, hp_le_half, h_one_le_two_pm,
    hkReal_le_k, hk_lt_kReal_add, hm_le_mReal, hmReal_lt_m_add, hK_le_n,
    hk_lt_two_kReal, hlogL_pos, hD⟩
  let m := TwoBiteNaturalReducedVertexCount n
  let k := TwoBiteNaturalIndependenceScale (1 + ε) n
  let L := Real.log (n : ℝ)
  
  have hm_lower : (n : ℝ) / (2 * L ^ 2) ≤ (m : ℝ) := by
    have h_mReal_ge_2 : (2 : ℝ) ≤ (n : ℝ) / L ^ 2 := h_props.1
    have h_mReal_lt_m_add : (n : ℝ) / L ^ 2 < (m : ℝ) + 1 := hmReal_lt_m_add
    have h_eq : (n : ℝ) / (2 * L ^ 2) = ((n : ℝ) / L ^ 2) / 2 := by ring
    rw [h_eq]
    linarith
  
  have hk_upper : (k : ℝ) ≤ 2 * (1 + ε) * Real.sqrt ((n : ℝ) * L) := by linarith
  
  have hk_lower_real : 1 ≤ (k : ℝ) := by
    have h_kReal_le_k : (1 + ε) * Real.sqrt ((n : ℝ) * L) ≤ (k : ℝ) := hkReal_le_k
    have h_L_pos : 0 < L := by linarith [h_props.2.2.2]
    have h_L_ge_1 : (1 : ℝ) ≤ L := le_of_lt h_props.2.2.2
    have hz : 0 < L ^ 4 := by positivity
    have h4 : (4 : ℝ) ≤ (n : ℝ) / L ^ 4 := h_props.2.1
    have h_n_pos_aux : (0 : ℝ) < (n : ℝ) / L ^ 4 := by linarith
    have h_n_pos : 0 < (n : ℝ) := (div_pos_iff_of_pos_right hz).mp h_n_pos_aux
    have h_sqrt_pos : 0 < Real.sqrt ((n : ℝ) * L) := Real.sqrt_pos.mpr (by positivity)
    have h_n_ge_1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h4_copy := h4
      rw [le_div_iff₀ hz] at h4_copy
      have h_L2_ge_1 : (1 : ℝ) ≤ L * L := by nlinarith [h_L_ge_1]
      have h_L4_ge_1 : (1 : ℝ) ≤ (L * L) * (L * L) := by nlinarith [h_L2_ge_1]
      have h_L4 : (1 : ℝ) ≤ L ^ 4 := by
        have : L ^ 4 = (L * L) * (L * L) := by ring
        rwa [this]
      have : (4 : ℝ) * 1 ≤ (4 : ℝ) * L ^ 4 := mul_le_mul_of_nonneg_left h_L4 (by positivity)
      linarith
    have h_1_le : 1 ≤ (1 + ε) * Real.sqrt ((n : ℝ) * L) := by
      have h_1_le_sqrt : 1 ≤ Real.sqrt ((n : ℝ) * L) := by
        rw [← Real.sqrt_one]
        apply Real.sqrt_le_sqrt
        nlinarith
      nlinarith [h_1_le_sqrt, hε]
    linarith

  have hK_le_n_real : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hK_le_n
  
  have h_n_le_m2 : (n : ℝ) ≤ (m : ℝ) ^ 2 := by
    have h_4 : (4 : ℝ) ≤ (n : ℝ) / L ^ 4 := h_props.2.1
    have h_L_pos : 0 < L := by linarith [h_props.2.2.2]
    have h_m_sq_lower : ((n : ℝ) / (2 * L ^ 2)) ^ 2 ≤ (m : ℝ) ^ 2 := by
      apply pow_le_pow_left₀
      · positivity
      · exact hm_lower
    have h_eq : ((n : ℝ) / (2 * L ^ 2)) ^ 2 = (n : ℝ) ^ 2 / (4 * L ^ 4) := by
      have h_denom : (2 * L ^ 2) ^ 2 = 4 * L ^ 4 := by ring
      rw [div_pow, h_denom]
    rw [h_eq] at h_m_sq_lower
    have h_n_le_n2_div_4L4 : (n : ℝ) ≤ (n : ℝ) ^ 2 / (4 * L ^ 4) := by
      have h_n_pos : (0 : ℝ) < (n : ℝ) := by
        have hz : 0 < L ^ 4 := by positivity
        have h_n_pos_aux : (0 : ℝ) < (n : ℝ) / L ^ 4 := by linarith
        exact (div_pos_iff_of_pos_right hz).mp h_n_pos_aux
      rw [le_div_iff₀ (by positivity)]
      have : (n : ℝ) * (4 * L ^ 4) ≤ (n : ℝ) * ((n : ℝ) / L ^ 4) * L ^ 4 := by
        have h_sub : (4 : ℝ) * L ^ 4 ≤ ((n : ℝ) / L ^ 4) * L ^ 4 := by
          have hz : 0 ≤ L ^ 4 := by positivity
          exact mul_le_mul_of_nonneg_right h_4 hz
        nlinarith
      calc (n : ℝ) * (4 * L ^ 4) ≤ (n : ℝ) * ((n : ℝ) / L ^ 4) * L ^ 4 := this
        _ = (n : ℝ) ^ 2 := by
          have hneq : L ^ 4 ≠ 0 := by positivity
          have h_div : ((n : ℝ) / L ^ 4) * L ^ 4 = (n : ℝ) := div_mul_cancel₀ (n : ℝ) hneq
          nlinarith
    linarith

  have hk_lower_nat : 1 ≤ k := by exact_mod_cast hk_lower_real
  have hK_le_n_nat : k ≤ n := by exact_mod_cast hK_le_n_real
  exact ⟨hm_lower, hk_upper, hk_lower_nat, hK_le_n_nat, h_n_le_m2⟩
