import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Tablet.ParameterHierarchy
import Tablet.RealChooseTwo
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale

set_option maxHeartbeats 4000000


-- [TABLET NODE: FixedSetProjectionMiddleRegimeExponent]

theorem FixedSetProjectionMiddleRegimeExponent :
    ∀ {ε ε1 ε2 η : ℝ} {n0 : ℕ},
      ParameterHierarchy ε ε1 ε2 n0 →
      0 < η →
      η ≤ ε * (1 - ε - 22 * ε ^ 2) / (320 * (1 + ε)) →
        ∃ N : ℕ, n0 ≤ N ∧
          ∀ {n ℓR ℓB : ℕ}, N < n →
            let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
            let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
            let xR : ℝ := (ℓR : ℝ) / (K : ℝ)
            let xB : ℝ := (ℓB : ℝ) / (K : ℝ)
            ℓR ≤ K →
            ℓB ≤ K →
            1 - ε / 2 < xR + xB →
            xR + xB < 1 + ε / 2 →
            xB ≤ xR →
              p * (n : ℝ) < (K : ℝ) - (ℓB : ℝ) ∧
                (η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) *
                      (K : ℝ) * Real.log (n : ℝ) -
                    p *
                      (RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) -
                        RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) -
                        RealChooseTwo (p * (n : ℝ)) -
                        RealChooseTwo ((K : ℝ) - (ℓB : ℝ) - p * (n : ℝ)) -
                        ε ^ 3 * (K : ℝ) ^ 2)
                  ≤
                    (ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε))) *
                        (K : ℝ) * Real.log (n : ℝ) +
                      3 * η * (K : ℝ) * Real.log (n : ℝ) := by
-- BODY
  intros ε ε1 ε2 η n0 h_param h_eta h_eta_bound
  let N_real := max (n0 : ℝ) ((16 / η) ^ 2 + Real.exp 1)
  let N := ⌈N_real⌉₊
  use N
  have hN_ge : (n0 : ℝ) ≤ N := le_trans (le_max_left _ _) (Nat.le_ceil N_real)
  refine ⟨by exact_mod_cast hN_ge, ?_⟩
  intros n ℓR ℓB hn K p xR xB h_lR h_lB h_regime_lower h_regime_upper h_xB_le_xR
  
  have C0_identity : ∀ (u xB eps d : ℝ) (heps : 1 + eps ≠ 0)
    (h_xB_u_d : xB = (1 + u - d) / 2),
    - (eps * u) / 2 - (1 - xB) / 4 + (1 / 8 * (1 / (1 + eps)))
    = - eps / (8 * (1 + eps)) - d / 8 + (1/8 - eps/2) * u := by
    intros u xB eps d heps h_xB_u_d
    have h_denom : 8 * (1 + eps) ≠ 0 := mul_ne_zero (by norm_num) heps
    have h_cancel : (1 / 8 * (1 / (1 + eps))) * (8 * (1 + eps)) = 1 := by
      calc
        (1 / 8 * (1 / (1 + eps))) * (8 * (1 + eps)) = (1 / 8 * 8) * (1 / (1 + eps) * (1 + eps)) := by ring
        _ = 1 * 1 := by
          have h1 : 1 / 8 * (8 : ℝ) = 1 := by norm_num
          have h2 : 1 / (1 + eps) * (1 + eps) = 1 := div_mul_cancel₀ 1 heps
          rw [h1, h2]
        _ = 1 := by ring
    have h_cancel2 : (- eps / (8 * (1 + eps))) * (8 * (1 + eps)) = - eps := by
      have : - eps / (8 * (1 + eps)) = (- eps) / (8 * (1 + eps)) := rfl
      rw [this, div_mul_cancel₀ (- eps) h_denom]
    have h_mul_eq : (- (eps * u) / 2 - (1 - xB) / 4 + (1 / 8 * (1 / (1 + eps)))) * (8 * (1 + eps))
                  = (- eps / (8 * (1 + eps)) - d / 8 + (1/8 - eps/2) * u) * (8 * (1 + eps)) := by
      calc
        (- (eps * u) / 2 - (1 - xB) / 4 + (1 / 8 * (1 / (1 + eps)))) * (8 * (1 + eps))
        = (- (eps * u) / 2 - (1 - xB) / 4) * (8 * (1 + eps)) + (1 / 8 * (1 / (1 + eps))) * (8 * (1 + eps)) := by ring
        _ = (- (eps * u) / 2 - (1 - xB) / 4) * (8 * (1 + eps)) + 1 := by rw [h_cancel]
        _ = - 4 * eps * u * (1 + eps) - 2 * (1 - (1 + u - d) / 2) * (1 + eps) + 1 := by
          rw [h_xB_u_d]
          ring
        _ = - eps - d * (1 + eps) + u * (1 - 3 * eps - 4 * eps^2) := by ring
        _ = (- eps / (8 * (1 + eps))) * (8 * (1 + eps)) + (- d / 8 + (1/8 - eps/2) * u) * (8 * (1 + eps)) := by
          rw [h_cancel2]
          ring
        _ = (- eps / (8 * (1 + eps)) - d / 8 + (1/8 - eps/2) * u) * (8 * (1 + eps)) := by ring
    exact mul_right_cancel₀ h_denom h_mul_eq

  have binom_id_pn : ∀ (ℓR ℓB K pn xR xB u eps : ℝ) 
    (h_lR : ℓR = xR * K) (h_lB : ℓB = xB * K) (h_u : u = xR + xB - 1),
    RealChooseTwo ℓR + RealChooseTwo ℓB - RealChooseTwo (K - ℓR) - RealChooseTwo pn - RealChooseTwo (K - ℓB - pn) - eps^3 * K^2
    = u * K^2 + pn * K * (1 - xB) - pn^2 - eps^3 * K^2 + K * (1 - xR - xB) := by
    intros ℓR ℓB K pn xR xB u eps h_lR h_lB h_u
    dsimp [RealChooseTwo]
    rw [h_lR, h_lB, h_u]
    ring

  have h_comps : ParameterHierarchyEventualComparisons ε ε1 ε2 n0 := h_param.2.2.2.2.2.2.2.2
  have hn_real : (N : ℝ) < n := by exact_mod_cast hn
  have hn_N_real : N_real < n := lt_of_le_of_lt (Nat.le_ceil N_real) hn_real
  have hn0 : (n0 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn_N_real
  have hn0_nat : n0 < n := by exact_mod_cast hn0
  have h_comps_n := h_comps n hn0_nat
  
  have hk_lower : (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (K : ℝ) := h_comps_n.2.2.2.2.1
  have hk_upper : (K : ℝ) < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1 := h_comps_n.2.2.2.2.2.1
  have h_p_pos : 0 ≤ p := h_comps_n.2.1
  
  have hn_pos : 0 < (n : ℝ) := by
    have h1 : (16 / η) ^ 2 + Real.exp 1 ≤ N_real := le_max_right _ _
    have h2 : 0 ≤ (16 / η) ^ 2 := sq_nonneg _
    linarith [Real.exp_pos 1, hn_N_real]
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    have hn_e : Real.exp 1 ≤ (n : ℝ) := by
      have h1 : (16 / η) ^ 2 + Real.exp 1 ≤ N_real := le_max_right _ _
      have h2 : 0 ≤ (16 / η) ^ 2 := sq_nonneg _
      linarith [hn_N_real]
    have : (1 : ℝ) < Real.exp 1 := by
      calc
        (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp 1 := Real.exp_lt_exp.mpr zero_lt_one
    linarith
  have h_sqrt_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  
  have h_k_pos : 0 < (K : ℝ) := by
    calc
      0 < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
        apply mul_pos
        · linarith [h_param.2.2.2.1, h_param.2.2.1, h_param.2.1, h_param.1]
        · apply Real.sqrt_pos.mpr (mul_pos hn_pos hlog_pos)
      _ ≤ (K : ℝ) := hk_lower
      
  have hp : p = (1 / 2 : ℝ) * (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ)) := by dsimp [p, TwoBiteEdgeProbability]; rw [Real.sqrt_div hlog_pos.le]
  
  have hpn : p * (n : ℝ) = (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    rw [hp]
    calc
      (1 / 2 : ℝ) * (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ)) * (n : ℝ) = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ)) * ((n : ℝ) / Real.sqrt (n : ℝ)) := by ring
      _ = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (n : ℝ) := by
        have : (n:ℝ) / Real.sqrt (n:ℝ) = Real.sqrt (n:ℝ) := by
          have h_eq : (n:ℝ) = Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) := (Real.mul_self_sqrt hn_pos.le).symm
          nth_rw 1 [h_eq]
          exact mul_div_cancel_right₀ _ (ne_of_gt h_sqrt_n_pos)
        rw [this]
      _ = (1 / 2 : ℝ) * (Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by ring
      _ = (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by rw [Real.sqrt_mul hn_pos.le]

  let q := p * (n : ℝ) / (K : ℝ)
  have hq : q = p * (n : ℝ) / (K : ℝ) := rfl
  
  have hk_pn_bound : p * (n : ℝ) ≤ (K : ℝ) / (2 * (1 + ε)) := by
    have h_eps_pos : 0 < ε := by linarith [h_param.1, h_param.2.1, h_param.2.2.1]
    rw [hpn, le_div_iff₀ (by linarith)]
    calc
      (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) * (2 * (1 + ε)) = (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by ring
      _ ≤ (K : ℝ) := hk_lower
      
  have hq_bound : q ≤ 1 / (2 * (1 + ε)) := by
    dsimp [q]
    rw [div_le_iff₀ h_k_pos]
    calc
      p * (n : ℝ) ≤ (K : ℝ) / (2 * (1 + ε)) := hk_pn_bound
      _ = 1 / (2 * (1 + ε)) * (K : ℝ) := by ring
      
  have h_eps_pos : 0 < ε := by linarith [h_param.1, h_param.2.1, h_param.2.2.1]
  have h_xB_bound : xB < 1 / 2 + ε / 4 := by linarith [h_regime_upper, h_xB_le_xR]
  have h_eps_lt_one : ε < 1 := by linarith [h_param.2.2.2.1]
  have h_eps_le : ε ≤ 1 / 16 := h_param.2.2.2.2.1.le
  
  have hq_lt_1_sub_xB : q < 1 - xB := by
    have h1 : 1 / (2 * (1 + ε)) < 1 / 2 - ε / 4 := by
      rw [div_lt_iff₀ (by linarith)]
      calc
        (1 : ℝ) = 1 + ε / 2 - ε / 2 := by ring
        _ < 1 + ε / 2 - ε ^ 2 / 2 := by
          have h_sq_lt : ε ^ 2 < ε := by nlinarith
          linarith
        _ = (1 / 2 - ε / 4) * (2 * (1 + ε)) := by ring
    linarith [hq_bound, h_xB_bound, h1]

  refine ⟨?_, ?_⟩
  · have hlB : (ℓB : ℝ) = xB * (K : ℝ) := by
      dsimp [xB]
      exact (div_mul_cancel₀ _ (ne_of_gt h_k_pos)).symm
    rw [hlB]
    calc
      p * (n : ℝ) = q * (K : ℝ) := by dsimp [q]; exact (div_mul_cancel₀ _ (ne_of_gt h_k_pos)).symm
      _ < (1 - xB) * (K : ℝ) := (mul_lt_mul_of_pos_right hq_lt_1_sub_xB h_k_pos)
      _ = (K : ℝ) - xB * (K : ℝ) := by ring
      
  · let u := xR + xB - 1
    have h_u : u = xR + xB - 1 := rfl
    have h_u_neg : -1 ≤ u := by linarith [h_regime_lower]
    have h_u_pos : u < ε / 2 := by linarith [h_regime_upper]
    have hu_abs : |u| ≤ 1 := by
      have : xR ≤ 1 := by
        dsimp [xR]
        rw [div_le_iff₀ h_k_pos]
        calc
          (ℓR : ℝ) ≤ (K : ℝ) := by exact_mod_cast h_lR
          _ = 1 * (K : ℝ) := by ring
      have : xB ≤ 1 := by
        dsimp [xB]
        rw [div_le_iff₀ h_k_pos]
        calc
          (ℓB : ℝ) ≤ (K : ℝ) := by exact_mod_cast h_lB
          _ = 1 * (K : ℝ) := by ring
      exact abs_le.mpr ⟨by linarith, by linarith⟩
      
    have h_lR_eq : (ℓR : ℝ) = xR * (K : ℝ) := by dsimp [xR]; exact (div_mul_cancel₀ _ (ne_of_gt h_k_pos)).symm
    have h_lB_eq : (ℓB : ℝ) = xB * (K : ℝ) := by dsimp [xB]; exact (div_mul_cancel₀ _ (ne_of_gt h_k_pos)).symm
    
    have h_binom : RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) - RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) - RealChooseTwo (p * (n : ℝ)) - RealChooseTwo ((K : ℝ) - (ℓB : ℝ) - p * (n : ℝ)) - ε ^ 3 * (K : ℝ) ^ 2
      = u * (K : ℝ)^2 + (p * (n : ℝ)) * (K : ℝ) * (1 - xB) - (p * (n : ℝ))^2 - ε^3 * (K : ℝ)^2 + (K : ℝ) * (1 - xR - xB) := binom_id_pn _ _ _ _ _ _ _ _ h_lR_eq h_lB_eq h_u
      
    have h_LHS : (η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ) - p * (RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) - RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) - RealChooseTwo (p * (n : ℝ)) - RealChooseTwo ((K : ℝ) - (ℓB : ℝ) - p * (n : ℝ)) - ε ^ 3 * (K : ℝ) ^ 2)
      = (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) - p * u * (K : ℝ)^2 - p * (p * (n : ℝ)) * (K : ℝ) * (1 - xB) + p * (p * (n : ℝ))^2 + p * ε^3 * (K : ℝ)^2 - p * (K : ℝ) * (1 - xR - xB) := by
      rw [h_binom, h_u]
      ring
      
    clear h_comps_n h_comps h_param
    
    have hpK_lower : (1 + ε) / 2 * Real.log (n : ℝ) ≤ p * (K : ℝ) := by
      calc
        (1 + ε) / 2 * Real.log (n : ℝ) = (1 + ε) / 2 * (Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ))) * (Real.sqrt (n : ℝ) / Real.sqrt (n : ℝ)) := by
          have h1 : Real.sqrt (n : ℝ) / Real.sqrt (n : ℝ) = 1 := div_self (ne_of_gt h_sqrt_n_pos)
          have h2 : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) = Real.log (n : ℝ) := by
            rw [← sq, Real.sq_sqrt hlog_pos.le]
          rw [h1, h2]
          ring
        _ = 1 / 2 * (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ)) * ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
          have h3 : Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) = Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
            rw [Real.sqrt_mul hn_pos.le]
          rw [← h3]
          ring
        _ = p * ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by rw [hp]
        _ ≤ p * (K : ℝ) := by { apply mul_le_mul_of_nonneg_left; exact hk_lower; exact h_p_pos }
        
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
              have hn_sq : (16 / η) ^ 2 ≤ (n : ℝ) := by
                have h1 : (16 / η) ^ 2 + Real.exp 1 ≤ N_real := le_max_right _ _
                linarith [Real.exp_pos 1, hn_N_real]
              have h1 : Real.sqrt ((16 / η) ^ 2) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hn_sq
              have h2 : 0 ≤ 16 / η := by positivity
              rwa [Real.sqrt_sq h2] at h1
        exact h_mul
      have h_sqrt_log_le : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
        rw [Real.sqrt_le_iff]
        refine ⟨hlog_pos.le, ?_⟩
        have hn_e : Real.exp 1 ≤ (n : ℝ) := by
          have h1 : (16 / η) ^ 2 + Real.exp 1 ≤ N_real := le_max_right _ _
          have h2 : 0 ≤ (16 / η) ^ 2 := sq_nonneg _
          linarith [hn_N_real]
        have : Real.log (Real.exp 1) ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos 1) hn_e
        rw [Real.log_exp] at this
        nlinarith
      calc
        p = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ)) * (1 / Real.sqrt (n : ℝ)) := by rw [hp]; ring
        _ ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) * (η / 16) := by gcongr
        _ = (η / 32) * Real.log (n : ℝ) := by ring
        _ ≤ (η / 16) * Real.log (n : ℝ) := by nlinarith [h_eta.le, hlog_pos.le]
        
    have hpK_upper : p * (K : ℝ) ≤ (1 + ε) / 2 * Real.log (n : ℝ) + (η / 16) * Real.log (n : ℝ) := by
      calc
        p * (K : ℝ) ≤ p * ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1) := mul_le_mul_of_nonneg_left hk_upper.le h_p_pos
        _ = p * ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) + p := by ring
        _ = (1 + ε) / 2 * Real.log (n : ℝ) + p := by
          have h1 : p * ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) = (1 + ε) / 2 * Real.log (n : ℝ) := by
            rw [hp]
            have h3 : Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) = Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
              rw [Real.sqrt_mul hn_pos.le]
            calc
              1 / 2 * (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ)) * ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
              = (1 + ε) / 2 * (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by rw [← h3]; ring
              _ = (1 + ε) / 2 * (Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ))) := by rw [div_mul_cancel₀ _ (ne_of_gt h_sqrt_n_pos)]
              _ = (1 + ε) / 2 * Real.log (n : ℝ) := by rw [← sq, Real.sq_sqrt hlog_pos.le]
          rw [h1]
        _ ≤ (1 + ε) / 2 * Real.log (n : ℝ) + (η / 16) * Real.log (n : ℝ) := add_le_add (le_refl _) h_p_bound
        
    have hp2nK : p * (p * (n : ℝ)) * (K : ℝ) = 1 / 4 * (K : ℝ) * Real.log (n : ℝ) := by
      have hp_sq : p^2 = 1 / 4 * (Real.log (n : ℝ) / (n : ℝ)) := by
        rw [hp]
        calc
          (1 / 2 * (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ))) ^ 2 = (1 / 2) ^ 2 * (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ)) ^ 2 := mul_pow _ _ _
          _ = 1 / 4 * (Real.sqrt (Real.log (n : ℝ)) ^ 2 / (Real.sqrt (n : ℝ)) ^ 2) := by ring
          _ = 1 / 4 * (Real.log (n : ℝ) / (n : ℝ)) := by rw [Real.sq_sqrt hlog_pos.le, Real.sq_sqrt hn_pos.le]
      calc
        p * (p * (n : ℝ)) * (K : ℝ) = p^2 * (n : ℝ) * (K : ℝ) := by ring
        _ = 1 / 4 * (Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) * (K : ℝ) := by rw [hp_sq]
        _ = 1 / 4 * (Real.log (n : ℝ) / (n : ℝ) * (n : ℝ)) * (K : ℝ) := by ring
        _ = 1 / 4 * Real.log (n : ℝ) * (K : ℝ) := by rw [div_mul_cancel₀ _ (ne_of_gt hn_pos)]
        _ = 1 / 4 * (K : ℝ) * Real.log (n : ℝ) := by ring
        
    have hsqrt_le : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (K : ℝ) / (1 + ε) := by
      have h_denom : 0 < 1 + ε := by linarith [h_eps_pos]
      rw [le_div_iff₀ h_denom]
      calc
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) * (1 + ε) = (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by ring
        _ ≤ (K : ℝ) := hk_lower

    have hp3n2 : p * (p * (n : ℝ))^2 ≤ (1 / 8 * (1 / (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) := by
      have hpn2 : (p * (n : ℝ))^2 = 1 / 4 * (n : ℝ) * Real.log (n : ℝ) := by
        calc
          (p * (n : ℝ))^2 = (1 / 2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))^2 := by rw [hpn]
          _ = 1 / 4 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))^2 := by ring
          _ = 1 / 4 * ((n : ℝ) * Real.log (n : ℝ)) := by rw [Real.sq_sqrt (by positivity)]
          _ = 1 / 4 * (n : ℝ) * Real.log (n : ℝ) := by ring
      calc
        p * (p * (n : ℝ))^2 = p * (1 / 4 * (n : ℝ) * Real.log (n : ℝ)) := by rw [hpn2]
        _ = 1 / 4 * (p * (n : ℝ)) * Real.log (n : ℝ) := by ring
        _ = 1 / 4 * (1 / 2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) * Real.log (n : ℝ) := by rw [hpn]
        _ = 1 / 8 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) * Real.log (n : ℝ) := by ring
        _ ≤ 1 / 8 * ((K : ℝ) / (1 + ε)) * Real.log (n : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
          · exact hlog_pos.le
        _ = (1 / 8 * (1 / (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) := by
          calc
            1 / 8 * ((K : ℝ) / (1 + ε)) * Real.log (n : ℝ)
            = 1 / 8 * (K : ℝ) * (1 / (1 + ε)) * Real.log (n : ℝ) := by ring
            _ = (1 / 8 * (1 / (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) := by ring
        
    have h_bound1 : - p * u * (K : ℝ)^2 ≤ - (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ) := by
      by_cases hu : 0 ≤ u
      · calc
          - p * u * (K : ℝ)^2 = - (p * (K : ℝ)) * (u * (K : ℝ)) := by ring
          _ ≤ - ((1 + ε) / 2 * Real.log (n : ℝ)) * (u * (K : ℝ)) := by
            apply mul_le_mul_of_nonneg_right
            · linarith [hpK_lower]
            · exact mul_nonneg hu h_k_pos.le
          _ = - (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) := by ring
          _ ≤ - (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ) := by
            apply le_add_of_nonneg_right
            positivity
      · have : u ≤ 0 := by linarith
        calc
          - p * u * (K : ℝ)^2 = (p * (K : ℝ)) * (-u * (K : ℝ)) := by ring
          _ ≤ ((1 + ε) / 2 * Real.log (n : ℝ) + (η / 16) * Real.log (n : ℝ)) * (-u * (K : ℝ)) := by
            apply mul_le_mul_of_nonneg_right
            · exact hpK_upper
            · exact mul_nonneg (by linarith) h_k_pos.le
          _ = - (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) + (-u) * (η / 16) * (K : ℝ) * Real.log (n : ℝ) := by ring
          _ ≤ - (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) + 1 * (η / 16) * (K : ℝ) * Real.log (n : ℝ) := by
            apply add_le_add (le_refl _)
            calc
              (-u) * (η / 16) * (K : ℝ) * Real.log (n : ℝ)
              = (-u) * ((η / 16) * (K : ℝ) * Real.log (n : ℝ)) := by ring
              _ ≤ 1 * ((η / 16) * (K : ℝ) * Real.log (n : ℝ)) := by
                apply mul_le_mul_of_nonneg_right
                · linarith [h_u_neg]
                · exact mul_nonneg (mul_nonneg (by linarith [h_eta.le]) h_k_pos.le) hlog_pos.le
              _ = 1 * (η / 16) * (K : ℝ) * Real.log (n : ℝ) := by ring
          _ = - (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ) := by ring

    have h_bound2 : -(p * (p * (n : ℝ)) * (K : ℝ) * (1 - xB)) = -(1 / 4 * (K : ℝ) * Real.log (n : ℝ) * (1 - xB)) := by
      calc
        -(p * (p * (n : ℝ)) * (K : ℝ) * (1 - xB)) = -(p * (p * (n : ℝ)) * (K : ℝ)) * (1 - xB) := by ring
        _ = -(1 / 4 * (K : ℝ) * Real.log (n : ℝ)) * (1 - xB) := by rw [hp2nK]
        _ = -(1 / 4 * (K : ℝ) * Real.log (n : ℝ) * (1 - xB)) := by ring
      
    have h_bound4 : p * ε^3 * (K : ℝ)^2 ≤ ((1 + ε) / 2 + η / 16) * ε^3 * (K : ℝ) * Real.log (n : ℝ) := by
      calc
        p * ε^3 * (K : ℝ)^2 = (p * (K : ℝ)) * ε^3 * (K : ℝ) := by ring
        _ ≤ ((1 + ε) / 2 * Real.log (n : ℝ) + (η / 16) * Real.log (n : ℝ)) * ε^3 * (K : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_right hpK_upper (by positivity)
          · exact h_k_pos.le
        _ = ((1 + ε) / 2 + η / 16) * ε^3 * (K : ℝ) * Real.log (n : ℝ) := by ring
        
    have h_bound5 : -(p * (K : ℝ) * (1 - xR - xB)) ≤ (η / 16) * (K : ℝ) * Real.log (n : ℝ) := by
      have : -(1 - xR - xB) ≤ 1 := by linarith [h_u, hu_abs]
      calc
        -(p * (K : ℝ) * (1 - xR - xB)) = (p * (K : ℝ)) * -(1 - xR - xB) := by ring
        _ ≤ (p * (K : ℝ)) * 1 := by
          apply mul_le_mul_of_nonneg_left this
          exact mul_nonneg h_p_pos h_k_pos.le
        _ = p * (K : ℝ) := mul_one _
        _ ≤ ((η / 16) * Real.log (n : ℝ)) * (K : ℝ) := mul_le_mul_of_nonneg_right h_p_bound h_k_pos.le
        _ = (η / 16) * (K : ℝ) * Real.log (n : ℝ) := by ring
        
    have h_LHS_eq : (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) - p * u * (K : ℝ)^2 - p * (p * (n : ℝ)) * (K : ℝ) * (1 - xB) + p * (p * (n : ℝ))^2 + p * ε^3 * (K : ℝ)^2 - p * (K : ℝ) * (1 - xR - xB)
      = (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) - p * u * (K : ℝ)^2 - (p * (p * (n : ℝ)) * (K : ℝ) * (1 - xB)) + p * (p * (n : ℝ))^2 + p * ε^3 * (K : ℝ)^2 - (p * (K : ℝ) * (1 - xR - xB)) := by ring
      
    have h_boundLHS : (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) - p * u * (K : ℝ)^2 - (p * (p * (n : ℝ)) * (K : ℝ) * (1 - xB)) + p * (p * (n : ℝ))^2 + p * ε^3 * (K : ℝ)^2 - (p * (K : ℝ) * (1 - xR - xB))
      ≤ (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) + (- (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ)) - 1 / 4 * (K : ℝ) * Real.log (n : ℝ) * (1 - xB) + (1 / 8 * (1 / (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) + ((1 + ε) / 2 + η / 16) * ε^3 * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ) := by
        linarith [h_bound1, h_bound2, hp3n2, h_bound4, h_bound5]

    have h_C0_subst : (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) + (- (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ)) - 1 / 4 * (K : ℝ) * Real.log (n : ℝ) * (1 - xB) + (1 / 8 * (1 / (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) + ((1 + ε) / 2 + η / 16) * ε^3 * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ)
      = (- ε / (8 * (1 + ε)) - (xR - xB) / 8 + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) := by
      have h_eps_ne_neg_one : 1 + ε ≠ 0 := by positivity
      have h_C0_cond : xB = (1 + u - (xR - xB)) / 2 := by rw [h_u]; ring
      have h_C0 := C0_identity u xB ε (xR - xB) h_eps_ne_neg_one h_C0_cond
      calc
        (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) + (- (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ)) - 1 / 4 * (K : ℝ) * Real.log (n : ℝ) * (1 - xB) + (1 / 8 * (1 / (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) + ((1 + ε) / 2 + η / 16) * ε^3 * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ)
        = (- (ε * u) / 2 - (1 - xB) / 4 + (1 / 8 * (1 / (1 + ε)))) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (1 + ε) / 2 * ε^3 * (K : ℝ) * Real.log (n : ℝ) := by ring
        _ = (- ε / (8 * (1 + ε)) - (xR - xB) / 8 + (1/8 - ε/2) * u) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (1 + ε) / 2 * ε^3 * (K : ℝ) * Real.log (n : ℝ) := by
          rw [h_C0]
        _ = (- ε / (8 * (1 + ε)) - (xR - xB) / 8 + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) := by ring

    have h_bound_d : (- ε / (8 * (1 + ε)) - (xR - xB) / 8 + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ)
      ≤ (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) := by
      calc
        (- ε / (8 * (1 + ε)) - (xR - xB) / 8 + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ)
        = (- ε / (8 * (1 + ε)) - (xR - xB) / 8 + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * ((K : ℝ) * Real.log (n : ℝ)) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * ((K : ℝ) * Real.log (n : ℝ)) := by ring
        _ ≤ (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * ((K : ℝ) * Real.log (n : ℝ)) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * ((K : ℝ) * Real.log (n : ℝ)) := by
          have h_ineq : (- ε / (8 * (1 + ε)) - (xR - xB) / 8 + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) ≤ (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) := by
            have : 0 ≤ (xR - xB) / 8 := by linarith [h_xB_le_xR]
            linarith
          have h_mul := mul_le_mul_of_nonneg_right h_ineq (mul_nonneg h_k_pos.le hlog_pos.le)
          linarith [h_mul]
        _ = (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) := by ring
        
    have h_bound_u : (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ)
      ≤ (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) := by
      calc
        (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ)
        = (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * ((K : ℝ) * Real.log (n : ℝ)) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * ((K : ℝ) * Real.log (n : ℝ)) := by ring
        _ ≤ (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * ((K : ℝ) * Real.log (n : ℝ)) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * ((K : ℝ) * Real.log (n : ℝ)) := by
          have h_ineq : (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) ≤ (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) := by
            have h_mul_u : (1/8 - ε/2) * u ≤ (1/8 - ε/2) * (ε / 2) := mul_le_mul_of_nonneg_left h_u_pos.le (by linarith [h_eps_le])
            linarith
          have h_mul := mul_le_mul_of_nonneg_right h_ineq (mul_nonneg h_k_pos.le hlog_pos.le)
          linarith [h_mul]
        _ = (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) := by ring

    have h_bound_final_A : (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) ≤ (ε * (-1 + ε + 22 * ε^2) / (16 * (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) := by
      calc
        (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ)
        = (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * ((K : ℝ) * Real.log (n : ℝ)) := by ring
        _ ≤ (ε * (-1 + ε + 22 * ε^2) / (16 * (1 + ε))) * ((K : ℝ) * Real.log (n : ℝ)) := by
          have h_ineq : (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) ≤ ε * (-1 + ε + 22 * ε^2) / (16 * (1 + ε)) := by
            have h_denom : 0 < 16 * (1 + ε) := by linarith [h_eps_pos]
            rw [le_div_iff₀ h_denom]
            calc
              (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * (16 * (1 + ε))
              = (- ε / (8 * (1 + ε))) * (16 * (1 + ε)) + ((1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * (16 * (1 + ε)) := by ring
              _ = (- ε / (8 * (1 + ε))) * (8 * (1 + ε)) * 2 + ((1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * (16 * (1 + ε)) := by ring
              _ = (- ε) * 2 + ((1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * (16 * (1 + ε)) := by
                have : 8 * (1 + ε) ≠ 0 := by positivity
                rw [div_mul_cancel₀ _ this]
              _ = -2 * ε + (ε - 4 * ε^2) * (1 + ε) + 8 * (1 + ε)^2 * ε^3 := by ring
              _ = ε * (-1 - 3 * ε + 4 * ε^2 + 16 * ε^3 + 8 * ε^4) := by ring
              _ ≤ ε * (-1 + ε + 22 * ε^2) := by
                apply mul_le_mul_of_nonneg_left
                · have h_eps3 : ε^3 ≤ ε^2 := by
                    calc
                      ε^3 = ε^2 * ε := by ring
                      _ ≤ ε^2 * 1 := mul_le_mul_of_nonneg_left h_eps_lt_one.le (by positivity)
                      _ = ε^2 := mul_one _
                  have h_eps4 : ε^4 ≤ ε^2 := by
                    calc
                      ε^4 = ε^2 * ε^2 := by ring
                      _ ≤ ε^2 * 1 := by
                        apply mul_le_mul_of_nonneg_left
                        · calc
                            ε^2 = ε * ε := by ring
                            _ ≤ 1 * 1 := mul_le_mul h_eps_lt_one.le h_eps_lt_one.le h_eps_pos.le zero_le_one
                            _ = 1 := by ring
                        · positivity
                      _ = ε^2 := mul_one _
                  have h_eps_bound : 6 * ε^2 ≤ 4 * ε := by
                    calc
                      6 * ε^2 = 6 * ε * ε := by ring
                      _ ≤ 6 * (1 / 16) * ε := by
                        apply mul_le_mul_of_nonneg_right
                        · have : ε ≤ 1/16 := h_eps_le
                          linarith
                        · exact h_eps_pos.le
                      _ = (3 / 8) * ε := by ring
                      _ ≤ 4 * ε := by
                        apply mul_le_mul_of_nonneg_right
                        · norm_num
                        · exact h_eps_pos.le
                  linarith [h_eps_pos, h_eps_bound, h_eps3, h_eps4]
                · exact h_eps_pos.le
          exact mul_le_mul_of_nonneg_right h_ineq (mul_nonneg h_k_pos.le hlog_pos.le)
        _ = (ε * (-1 + ε + 22 * ε^2) / (16 * (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) := by ring

    have h_bound_final_B : (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) ≤ (3 * η) * (K : ℝ) * Real.log (n : ℝ) := by
      calc
        (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ)
        = (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * ((K : ℝ) * Real.log (n : ℝ)) := by ring
        _ ≤ (3 * η) * ((K : ℝ) * Real.log (n : ℝ)) := by
          have h_ineq : 2 * η + 2 * (η / 16) + (η / 16) * ε^3 ≤ 3 * η := by
            have h_eps3 : ε^3 ≤ 1 := by
              calc
                ε^3 = ε * ε * ε := by ring
                _ ≤ 1 * 1 * 1 := by
                  apply mul_le_mul
                  · apply mul_le_mul h_eps_lt_one.le h_eps_lt_one.le h_eps_pos.le zero_le_one
                  · exact h_eps_lt_one.le
                  · exact h_eps_pos.le
                  · positivity
                _ = 1 := by ring
            have h_eta16 : 0 ≤ η / 16 := by positivity
            have h_mul_eps3 : (η / 16) * ε^3 ≤ (η / 16) * 1 := mul_le_mul_of_nonneg_left h_eps3 h_eta16
            linarith [h_mul_eps3]
          exact mul_le_mul_of_nonneg_right h_ineq (mul_nonneg h_k_pos.le hlog_pos.le)
        _ = (3 * η) * (K : ℝ) * Real.log (n : ℝ) := by ring

    have h_bound_final : (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ)
      ≤ (ε * (-1 + ε + 22 * ε^2) / (16 * (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) + 3 * η * (K : ℝ) * Real.log (n : ℝ) := by
      apply add_le_add h_bound_final_A h_bound_final_B

    calc
      (η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ) - p * (RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) - RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) - RealChooseTwo (p * (n : ℝ)) - RealChooseTwo ((K : ℝ) - (ℓB : ℝ) - p * (n : ℝ)) - ε ^ 3 * (K : ℝ) ^ 2)
      = (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) - p * u * (K : ℝ)^2 - p * (p * (n : ℝ)) * (K : ℝ) * (1 - xB) + p * (p * (n : ℝ))^2 + p * ε^3 * (K : ℝ)^2 - p * (K : ℝ) * (1 - xR - xB) := h_LHS
      _ = (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) - p * u * (K : ℝ)^2 - (p * (p * (n : ℝ)) * (K : ℝ) * (1 - xB)) + p * (p * (n : ℝ))^2 + p * ε^3 * (K : ℝ)^2 - (p * (K : ℝ) * (1 - xR - xB)) := h_LHS_eq
      _ ≤ (2 * η + u / 2) * (K : ℝ) * Real.log (n : ℝ) + (- (1 + ε) / 2 * u * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ)) - 1 / 4 * (K : ℝ) * Real.log (n : ℝ) * (1 - xB) + (1 / 8 * (1 / (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) + ((1 + ε) / 2 + η / 16) * ε^3 * (K : ℝ) * Real.log (n : ℝ) + (η / 16) * (K : ℝ) * Real.log (n : ℝ) := h_boundLHS
      _ = (- ε / (8 * (1 + ε)) - (xR - xB) / 8 + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) := h_C0_subst
      _ ≤ (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * u + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) := h_bound_d
      _ ≤ (- ε / (8 * (1 + ε)) + (1/8 - ε/2) * (ε / 2) + (1 + ε) / 2 * ε^3) * (K : ℝ) * Real.log (n : ℝ) + (2 * η + 2 * (η / 16) + (η / 16) * ε^3) * (K : ℝ) * Real.log (n : ℝ) := h_bound_u
      _ ≤ (ε * (-1 + ε + 22 * ε^2) / (16 * (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) + 3 * η * (K : ℝ) * Real.log (n : ℝ) := h_bound_final