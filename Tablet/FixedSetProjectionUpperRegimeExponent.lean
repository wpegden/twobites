import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Tablet.ParameterHierarchy
import Tablet.RealChooseTwo
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: FixedSetProjectionUpperRegimeExponent]

theorem FixedSetProjectionUpperRegimeExponent :
    ∀ {ε ε1 ε2 η : ℝ} {n0 : ℕ},
      ParameterHierarchy ε ε1 ε2 n0 →
      0 < η →
      η ≤ ε ^ 2 / 320 →
        ∃ N : ℕ, n0 ≤ N ∧
          ∀ {n ℓR ℓB : ℕ}, N < n →
            let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
            let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
            let xR : ℝ := (ℓR : ℝ) / (K : ℝ)
            let xB : ℝ := (ℓB : ℝ) / (K : ℝ)
            ℓR ≤ K →
            ℓB ≤ K →
            1 + ε / 2 ≤ xR + xB →
              (η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) *
                    (K : ℝ) * Real.log (n : ℝ) -
                  p *
                    (RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) -
                      RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) -
                      RealChooseTwo ((K : ℝ) - (ℓB : ℝ)) -
                      ε ^ 3 * (K : ℝ) ^ 2)
                ≤
                  -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) *
                      (K : ℝ) * Real.log (n : ℝ) +
                    3 * η * (K : ℝ) * Real.log (n : ℝ) := by
-- BODY
  intros ε ε1 ε2 η n0 h_param h_eta h_eta_bound
  let N_real := max (n0 : ℝ) ((16 / η) ^ 2 + Real.exp 1)
  let N := ⌈N_real⌉₊
  use N
  have hN_ge : (n0 : ℝ) ≤ N := le_trans (le_max_left _ _) (Nat.le_ceil N_real)
  refine ⟨by exact_mod_cast hN_ge, ?_⟩
  intros n ℓR ℓB hn K p xR xB h_lR h_lB h_regime
  
  have h_comps : ParameterHierarchyEventualComparisons ε ε1 ε2 n0 := h_param.2.2.2.2.2.2.2.2
  have hn_real : (N : ℝ) < n := by exact_mod_cast hn
  have hn_N_real : N_real < n := lt_of_le_of_lt (Nat.le_ceil N_real) hn_real
  have hn0 : (n0 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn_N_real
  have hn0_nat : n0 < n := by exact_mod_cast hn0
  have hn_sq : (16 / η) ^ 2 ≤ (n : ℝ) := by
    have h1 : (16 / η) ^ 2 + Real.exp 1 ≤ N_real := le_max_right _ _
    linarith [Real.exp_pos 1, hn_N_real]
  have hn_e : Real.exp 1 ≤ (n : ℝ) := by
    have h1 : (16 / η) ^ 2 + Real.exp 1 ≤ N_real := le_max_right _ _
    have h2 : 0 ≤ (16 / η) ^ 2 := sq_nonneg _
    linarith [hn_N_real]
  have h_comps_n := h_comps n hn0_nat
  have hk_lower : (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (K : ℝ) := h_comps_n.2.2.2.2.1
  have hk_upper : (K : ℝ) < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 := h_comps_n.2.2.2.2.2.1
  have h_p_pos : 0 ≤ p := h_comps_n.2.1
  have hlog_pos : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    have : (1 : ℝ) < Real.exp 1 := by
      calc
        (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp 1 := Real.exp_lt_exp.mpr zero_lt_one
    linarith
  have hn_pos : 0 < (n : ℝ) := by linarith
  have h_sqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  
  have h_k_pos : 0 < (K : ℝ) := by
    calc
      0 < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
        apply mul_pos
        · linarith [h_param.2.2.2.1, h_param.2.2.1, h_param.2.1, h_param.1]
        · apply Real.sqrt_pos.mpr
          apply mul_pos
          · linarith
          · apply Real.log_pos
            have : (1 : ℝ) < Real.exp 1 := by
              calc
                (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
                _ < Real.exp 1 := Real.exp_lt_exp.mpr zero_lt_one
            linarith
      _ ≤ (K : ℝ) := hk_lower

  have hp : p = (1 / 2 : ℝ) * (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ)) := by dsimp [p, TwoBiteEdgeProbability]; rw [Real.sqrt_div hlog_pos]
  have h_p_bound : p ≤ (η / 16) * Real.log (n : ℝ) := by
    have h_inv_sqrt_n : 1 / Real.sqrt (n : ℝ) ≤ η / 16 := by
      rw [div_le_iff₀ h_sqrt_n_pos]
      have h_mul : (1 : ℝ) ≤ (η / 16) * Real.sqrt (n : ℝ) := by
        calc
          (1 : ℝ) = (η / 16) * (16 / η) := by
            have h1 : 16 / η = (η / 16)⁻¹ := by exact inv_div η 16 |>.symm
            rw [h1]
            refine (mul_inv_cancel₀ (a := η / 16) ?_).symm
            positivity
          _ ≤ (η / 16) * Real.sqrt (n : ℝ) := by
            gcongr
            have h1 : Real.sqrt ((16 / η) ^ 2) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hn_sq
            have h2 : 0 ≤ 16 / η := by positivity
            rwa [Real.sqrt_sq h2] at h1
      exact h_mul
    have h_sqrt_log_le : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨hlog_pos, ?_⟩
      have : Real.log (Real.exp 1) ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos 1) hn_e
      rw [Real.log_exp] at this
      nlinarith
    calc
      p = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ)) * (1 / Real.sqrt (n : ℝ)) := by rw [hp]; ring
      _ ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) * (η / 16) := by gcongr
      _ = (η / 32) * Real.log (n : ℝ) := by ring
      _ ≤ (η / 16) * Real.log (n : ℝ) := by nlinarith [h_eta.le, hlog_pos]
  
  have h_pK_lower : (1 + ε) / 2 * Real.log (n : ℝ) ≤ p * (K : ℝ) := by
    calc
      (1 + ε) / 2 * Real.log (n : ℝ) = (1 + ε) / 2 * Real.log (n : ℝ) * 1 := by ring
      _ = (1 + ε) / 2 * (Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ))) * (Real.sqrt (n : ℝ) / Real.sqrt (n : ℝ)) := by
        have h1 : Real.sqrt (n : ℝ) / Real.sqrt (n : ℝ) = 1 := div_self (ne_of_gt h_sqrt_n_pos)
        have h2 : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) = Real.log (n : ℝ) := by
          rw [← sq, Real.sq_sqrt hlog_pos]
        rw [h1, h2]
      _ = (1 / 2 : ℝ) * (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ)) * ((1 + ε) * (Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)))) := by ring
      _ = p * ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
        rw [← hp]
        have h3 : Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) = Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
          rw [Real.sqrt_mul hn_pos.le]
        rw [h3]
      _ ≤ p * (K : ℝ) := by
        gcongr
  
  have h_xR_bounds : 0 ≤ xR ∧ xR ≤ 1 := by
    dsimp [xR]
    refine ⟨div_nonneg (Nat.cast_nonneg _) h_k_pos.le, ?_⟩
    rw [div_le_iff₀ h_k_pos]
    calc
      (ℓR : ℝ) ≤ (K : ℝ) := by exact_mod_cast h_lR
      _ = 1 * (K : ℝ) := by ring
  
  have h_xB_bounds : 0 ≤ xB ∧ xB ≤ 1 := by
    dsimp [xB]
    refine ⟨div_nonneg (Nat.cast_nonneg _) h_k_pos.le, ?_⟩
    rw [div_le_iff₀ h_k_pos]
    calc
      (ℓB : ℝ) ≤ (K : ℝ) := by exact_mod_cast h_lB
      _ = 1 * (K : ℝ) := by ring
  
  let u := xR + xB - 1
  have h_u_def : u = xR + xB - 1 := rfl
  
  have h_binom_id : RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) -
                      RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) -
                      RealChooseTwo ((K : ℝ) - (ℓB : ℝ)) = u * ((K : ℝ) ^ 2 - (K : ℝ)) := by
    dsimp [RealChooseTwo]
    have hlR : (ℓR : ℝ) = xR * (K : ℝ) := by
      calc
        (ℓR : ℝ) = (ℓR : ℝ) / (K : ℝ) * (K : ℝ) := by exact (div_mul_cancel₀ _ (ne_of_gt h_k_pos)).symm
        _ = xR * (K : ℝ) := rfl
    have hlB : (ℓB : ℝ) = xB * (K : ℝ) := by
      calc
        (ℓB : ℝ) = (ℓB : ℝ) / (K : ℝ) * (K : ℝ) := by exact (div_mul_cancel₀ _ (ne_of_gt h_k_pos)).symm
        _ = xB * (K : ℝ) := rfl
    rw [hlR, hlB]
    dsimp [u]
    ring
  
  have hu_bounds : 0 ≤ u ∧ u ≤ 1 := by
    dsimp [u]
    refine ⟨?_, ?_⟩
    · linarith [h_regime, h_param.1, h_param.2.1, h_param.2.2.1]
    · linarith [h_xR_bounds.2, h_xB_bounds.2]
  
  have hk_sq_sub_k_nonneg : 0 ≤ (K : ℝ) ^ 2 - (K : ℝ) := by
    have : 1 ≤ (K : ℝ) := by
      apply Nat.one_le_cast.mpr
      apply Nat.pos_of_ne_zero
      intro hk_zero
      have : (K : ℝ) = 0 := by exact_mod_cast hk_zero
      linarith
    nlinarith
  
  have h_p_u_K_sq : (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) - (η / 16) * (K : ℝ) * Real.log (n : ℝ) ≤ p * u * ((K : ℝ) ^ 2 - (K : ℝ)) := by
    calc
      (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) - (η / 16) * (K : ℝ) * Real.log (n : ℝ)
        = ((1 + ε) / 2 * Real.log (n : ℝ)) * (u * (K : ℝ)) - (η / 16) * Real.log (n : ℝ) * (K : ℝ) * 1 := by ring
      _ ≤ (p * (K : ℝ)) * (u * (K : ℝ)) - (η / 16) * Real.log (n : ℝ) * (K : ℝ) * 1 := by
        apply sub_le_sub_right
        apply mul_le_mul_of_nonneg_right h_pK_lower
        exact mul_nonneg hu_bounds.1 h_k_pos.le
      _ ≤ (p * (K : ℝ)) * (u * (K : ℝ)) - p * (K : ℝ) * 1 := by
        apply sub_le_sub_left
        calc
          p * (K : ℝ) * 1 = p * (K : ℝ) := mul_one _
          _ ≤ ((η / 16) * Real.log (n : ℝ)) * (K : ℝ) := mul_le_mul_of_nonneg_right h_p_bound h_k_pos.le
          _ = (η / 16) * Real.log (n : ℝ) * (K : ℝ) * 1 := by ring
      _ = p * u * ((K : ℝ) ^ 2 - (K : ℝ)) + p * (K : ℝ) * (u - 1) := by ring
      _ ≤ p * u * ((K : ℝ) ^ 2 - (K : ℝ)) + 0 := by
        apply add_le_add (le_refl _)
        apply mul_nonpos_of_nonneg_of_nonpos
        · positivity
        · linarith [hu_bounds.2]
      _ = p * u * ((K : ℝ) ^ 2 - (K : ℝ)) := add_zero _
  
  have h_eps_pos : 0 ≤ ε := by linarith [h_param.1, h_param.2.1, h_param.2.2.1]
  have h_eps3_pos : 0 ≤ ε^3 := by positivity
  have h_eps_le_one : ε ≤ 1 := h_param.2.2.2.1.le

  have h_p_eps3_K_sq : p * ε ^ 3 * (K : ℝ) ^ 2 ≤ ((1 + ε) / 2 + η / 16) * ε ^ 3 * (K : ℝ) * Real.log (n : ℝ) := by
    calc
      p * ε ^ 3 * (K : ℝ) ^ 2 = (K : ℝ) * (p * ε ^ 3 * (K : ℝ)) := by ring
      _ ≤ ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1) * (p * ε ^ 3 * (K : ℝ)) := by
        apply mul_le_mul_of_nonneg_right (le_of_lt hk_upper)
        apply mul_nonneg (mul_nonneg h_p_pos h_eps3_pos) h_k_pos.le
      _ = (p * (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + p) * ε ^ 3 * (K : ℝ) := by ring
      _ = (p * Real.sqrt (n : ℝ) * (1 + ε) * Real.sqrt (Real.log (n : ℝ)) + p) * ε ^ 3 * (K : ℝ) := by
        rw [Real.sqrt_mul hn_pos.le]
        ring
      _ = ((1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ)) * (1 + ε) * Real.sqrt (Real.log (n : ℝ)) + p) * ε ^ 3 * (K : ℝ) := by
        have : p * Real.sqrt (n : ℝ) = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ)) := by
          calc
            p * Real.sqrt (n : ℝ) = ((1 / 2 : ℝ) * (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ))) * Real.sqrt (n : ℝ) := by rw [hp]
            _ = ((1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ))) / Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) := by ring
            _ = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ)) := by exact div_mul_cancel₀ _ (ne_of_gt h_sqrt_n_pos)
        rw [this]
      _ = ((1 + ε) / 2 * (Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ))) + p) * ε ^ 3 * (K : ℝ) := by ring
      _ = ((1 + ε) / 2 * Real.log (n : ℝ) + p) * ε ^ 3 * (K : ℝ) := by
        have h_log_sq : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) = Real.log (n : ℝ) := by
          rw [← sq, Real.sq_sqrt hlog_pos]
        rw [h_log_sq]
      _ ≤ ((1 + ε) / 2 * Real.log (n : ℝ) + (η / 16) * Real.log (n : ℝ)) * ε ^ 3 * (K : ℝ) := by
        have h_add : (1 + ε) / 2 * Real.log (n : ℝ) + p ≤ (1 + ε) / 2 * Real.log (n : ℝ) + (η / 16) * Real.log (n : ℝ) :=
          add_le_add (le_refl _) h_p_bound
        have h_mul1 : ((1 + ε) / 2 * Real.log (n : ℝ) + p) * ε ^ 3 ≤ ((1 + ε) / 2 * Real.log (n : ℝ) + (η / 16) * Real.log (n : ℝ)) * ε ^ 3 :=
          mul_le_mul_of_nonneg_right h_add h_eps3_pos
        exact mul_le_mul_of_nonneg_right h_mul1 h_k_pos.le
      _ = ((1 + ε) / 2 + η / 16) * ε ^ 3 * (K : ℝ) * Real.log (n : ℝ) := by ring

  have h_LHS : (η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ) -
                  p *
                    (RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) -
                      RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) -
                      RealChooseTwo ((K : ℝ) - (ℓB : ℝ)) -
                      ε ^ 3 * (K : ℝ) ^ 2)
              = (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) - p * u * ((K : ℝ) ^ 2 - (K : ℝ)) + p * ε ^ 3 * (K : ℝ) ^ 2 := by
    rw [h_binom_id]
    dsimp [u]
    clear_value K p xR xB u N N_real
    clear h_comps_n
    ring

  have h_final_algebra : (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) - ((1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) - (η / 16) * (K : ℝ) * Real.log (n : ℝ)) + ((1 + ε) / 2 + η / 16) * ε ^ 3 * (K : ℝ) * Real.log (n : ℝ) =
    -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * (K : ℝ) * Real.log (n : ℝ) + (2 + 1 / 16 + ε ^ 3 / 16) * (η * (K : ℝ) * Real.log (n : ℝ)) := by
    dsimp [u]
    clear_value K p xR xB u N N_real
    clear h_comps_n h_p_eps3_K_sq h_p_u_K_sq h_binom_id h_pK_lower h_p_bound
    ring

  calc
    (η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ) -
                  p *
                    (RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) -
                      RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) -
                      RealChooseTwo ((K : ℝ) - (ℓB : ℝ)) -
                      ε ^ 3 * (K : ℝ) ^ 2)
      = (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) - p * u * ((K : ℝ) ^ 2 - (K : ℝ)) + p * ε ^ 3 * (K : ℝ) ^ 2 := h_LHS
    _ ≤ (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) - ((1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) - (η / 16) * (K : ℝ) * Real.log (n : ℝ)) + ((1 + ε) / 2 + η / 16) * ε ^ 3 * (K : ℝ) * Real.log (n : ℝ) := by
      apply add_le_add
      · apply sub_le_sub_left h_p_u_K_sq
      · exact h_p_eps3_K_sq
    _ = -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * (K : ℝ) * Real.log (n : ℝ) + (2 + 1 / 16 + ε ^ 3 / 16) * (η * (K : ℝ) * Real.log (n : ℝ)) := h_final_algebra
    _ ≤ -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * (K : ℝ) * Real.log (n : ℝ) + 3 * η * (K : ℝ) * Real.log (n : ℝ) := by
      have h_eta_K_log : 0 ≤ η * (K : ℝ) * Real.log (n : ℝ) := by
        apply mul_nonneg
        · apply mul_nonneg h_eta.le h_k_pos.le
        · exact hlog_pos
      have h_eps3_le_one : ε ^ 3 ≤ 1 := pow_le_one₀ h_eps_pos h_eps_le_one
      have h_coeff_le : (2 + 1 / 16 + ε ^ 3 / 16) ≤ 3 := by linarith
      have h_bound : (2 + 1 / 16 + ε ^ 3 / 16) * (η * (K : ℝ) * Real.log (n : ℝ)) ≤ 3 * (η * (K : ℝ) * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right h_coeff_le h_eta_K_log
      calc
        -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * (K : ℝ) * Real.log (n : ℝ) + (2 + 1 / 16 + ε ^ 3 / 16) * (η * (K : ℝ) * Real.log (n : ℝ))
          ≤ -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * (K : ℝ) * Real.log (n : ℝ) + 3 * (η * (K : ℝ) * Real.log (n : ℝ)) := add_le_add (le_refl _) h_bound
        _ = -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * (K : ℝ) * Real.log (n : ℝ) + 3 * η * (K : ℝ) * Real.log (n : ℝ) := by ring