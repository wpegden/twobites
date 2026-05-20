import Tablet.ParameterHierarchy
import Tablet.FixedSetProjectionBinomialSummationMargins
import Tablet.FixedSetProjectionLowerRegimeExponent
import Tablet.FixedSetProjectionMiddleRegimeExponent
import Tablet.FixedSetProjectionUpperRegimeExponent
import Tablet.ProjectionOpenPairFunction
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

-- [TABLET NODE: FixedSetProjectionCellSummationBound]

theorem FixedSetProjectionCellSummationBound :
    ∀ {ε ε1 ε2 : ℝ} {n0 : ℕ} (δ : ℝ),
      0 < δ →
      ParameterHierarchy ε ε1 ε2 n0 →
        ∃ η : ℝ, 0 < η ∧
          ∃ N : ℕ, n0 ≤ N ∧
            ∀ n : ℕ, N < n →
              let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
              let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
              (Finset.range (K + 1)).sum (fun ℓR =>
                (Finset.range (K + 1)).sum (fun ℓB =>
                  if ℓR * ℓB < K then
                    (0 : ℝ)
                  else
                    Real.exp
                      ((η - (2 - (ℓR : ℝ) / (K : ℝ) -
                          (ℓB : ℝ) / (K : ℝ)) / 2) *
                        (K : ℝ) * Real.log (n : ℝ)) *
                      min (1 : ℝ)
                        (Real.exp
                          (-(p *
                            (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
                              (K : ℝ) p (n : ℝ) -
                              ε ^ 3 * (K : ℝ) ^ 2))))))
                ≤ δ * ((Nat.choose n K : ℝ)⁻¹) := by
-- BODY
  intros ε ε1 ε2 n0 δ hδ h_param
  have exp_min_bound_lower : ∀ {A X Y : ℝ}, A + min 0 X ≤ Y → Real.exp A * min 1 (Real.exp X) ≤ Real.exp Y := by
    intro A X Y h1
    rw [← Real.exp_zero]
    by_cases hX : 0 ≤ X
    · have : min (Real.exp 0) (Real.exp X) = Real.exp 0 := min_eq_left (Real.exp_le_exp.mpr hX)
      rw [this, min_eq_left hX, Real.exp_zero, mul_one, add_zero] at *
      exact Real.exp_le_exp.mpr h1
    · have : X ≤ 0 := le_of_not_ge hX
      have : min (Real.exp 0) (Real.exp X) = Real.exp X := min_eq_right (Real.exp_le_exp.mpr this)
      rw [this, min_eq_right (le_of_not_ge hX), ← Real.exp_add] at *
      exact Real.exp_le_exp.mpr h1

  have exp_min_bound_other : ∀ {A X Y : ℝ}, A + X ≤ Y → Real.exp A * min 1 (Real.exp X) ≤ Real.exp Y := by
    intro A X Y h1
    calc Real.exp A * min 1 (Real.exp X) ≤ Real.exp A * Real.exp X := mul_le_mul_of_nonneg_left (min_le_right 1 (Real.exp X)) (Real.exp_pos A).le
      _ = Real.exp (A + X) := (Real.exp_add A X).symm
      _ ≤ Real.exp Y := Real.exp_le_exp.mpr h1

  have proj_open_pair_bound_mid : ∀ (ℓR ℓB K p n ε : ℝ), 0 ≤ p → -p * (ProjectionOpenPairFunction ℓR ℓB K p n - ε^3 * K^2) ≤ -p * (RealChooseTwo ℓR + RealChooseTwo ℓB - RealChooseTwo (K - ℓR) - RealChooseTwo (p * n) - RealChooseTwo (K - ℓB - p * n) - ε^3 * K^2) := by
    intro ℓR ℓB K p n ε hp
    dsimp [ProjectionOpenPairFunction]
    apply mul_le_mul_of_nonpos_left
    · have h1 : min (RealChooseTwo (K - ℓR)) (RealChooseTwo (p * n) + RealChooseTwo (K - ℓR - p * n)) ≤ RealChooseTwo (K - ℓR) := min_le_left _ _
      have h2 : min (RealChooseTwo (K - ℓB)) (RealChooseTwo (p * n) + RealChooseTwo (K - ℓB - p * n)) ≤ RealChooseTwo (p * n) + RealChooseTwo (K - ℓB - p * n) := min_le_right _ _
      linarith
    · linarith

  have proj_open_pair_bound_up : ∀ (ℓR ℓB K p n ε : ℝ), 0 ≤ p → -p * (ProjectionOpenPairFunction ℓR ℓB K p n - ε^3 * K^2) ≤ -p * (RealChooseTwo ℓR + RealChooseTwo ℓB - RealChooseTwo (K - ℓR) - RealChooseTwo (K - ℓB) - ε^3 * K^2) := by
    intro ℓR ℓB K p n ε hp
    dsimp [ProjectionOpenPairFunction]
    apply mul_le_mul_of_nonpos_left
    · have h1 : min (RealChooseTwo (K - ℓR)) (RealChooseTwo (p * n) + RealChooseTwo (K - ℓR - p * n)) ≤ RealChooseTwo (K - ℓR) := min_le_left _ _
      have h2 : min (RealChooseTwo (K - ℓB)) (RealChooseTwo (p * n) + RealChooseTwo (K - ℓB - p * n)) ≤ RealChooseTwo (K - ℓB) := min_le_left _ _
      linarith
    · linarith

  have middle_regime_bound : ∀ (ε η K log_n : ℝ), 0 ≤ η → 0 < 1 + ε → η ≤ ε * (1 - ε - 22 * ε ^ 2) / (320 * (1 + ε)) → 0 ≤ K * log_n → (ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε))) * K * log_n + 3 * η * K * log_n ≤ -4 * η * K * log_n := by
    intro ε η K log_n h_eta_pos h_eps_pos h_eta_le hKlog_nonneg
    have h_div_eq : ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε)) = - (ε * (1 - ε - 22 * ε ^ 2) / (16 * (1 + ε))) := by
      calc ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε)) = -(ε * (1 - ε - 22 * ε ^ 2)) / (16 * (1 + ε)) := by ring
        _ = - (ε * (1 - ε - 22 * ε ^ 2) / (16 * (1 + ε))) := by ring
    rw [h_div_eq]
    have h1 : 320 * η * (1 + ε) ≤ ε * (1 - ε - 22 * ε ^ 2) := by
      have : η * (320 * (1 + ε)) ≤ ε * (1 - ε - 22 * ε ^ 2) := (le_div_iff₀ (by linarith)).mp h_eta_le
      linarith
    have h2 : 20 * η ≤ ε * (1 - ε - 22 * ε ^ 2) / (16 * (1 + ε)) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have h3_new : - (ε * (1 - ε - 22 * ε ^ 2) / (16 * (1 + ε))) ≤ -(20 * η) := by linarith
    let Y := K * log_n
    have hY : Y = K * log_n := rfl
    have step1 : - (ε * (1 - ε - 22 * ε ^ 2) / (16 * (1 + ε))) * K * log_n + 3 * η * K * log_n = - (ε * (1 - ε - 22 * ε ^ 2) / (16 * (1 + ε))) * Y + 3 * η * Y := by ring
    rw [step1]
    have step2 : -4 * η * K * log_n = -4 * η * Y := by ring
    rw [step2]
    have step0 : - (ε * (1 - ε - 22 * ε ^ 2) / (16 * (1 + ε))) * Y ≤ -(20 * η) * Y := mul_le_mul_of_nonneg_right h3_new (by exact_mod_cast hKlog_nonneg)
    calc - (ε * (1 - ε - 22 * ε ^ 2) / (16 * (1 + ε))) * Y + 3 * η * Y
      ≤ -(20 * η) * Y + 3 * η * Y := by linarith [step0]
      _ = -17 * η * Y := by ring
      _ ≤ -4 * η * Y := mul_le_mul_of_nonneg_right (by linarith) hKlog_nonneg

  have upper_regime_bound : ∀ (ε η xR xB K log_n : ℝ), 0 < ε → ε ≤ 1/16 → 0 ≤ η → η ≤ ε ^ 2 / 320 → 1 + ε / 2 ≤ xR + xB → 0 ≤ K * log_n → -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * K * log_n + 3 * η * K * log_n ≤ -4 * η * K * log_n := by
    intro ε η xR xB K log_n h_eps_pos h_eps_le h_eta_pos h_eta_le h_regime hKlog_nonneg
    have h_x_bnd : ε / 4 ≤ xR + xB - 1 - ε ^ 2 - ε ^ 3 := by
      calc ε / 4 = ε / 2 - ε / 4 := by ring
        _ ≤ (xR + xB - 1) - ε / 4 := by linarith
        _ ≤ (xR + xB - 1) - (ε^2 + ε^3) := by
          apply sub_le_sub_left
          calc ε^2 + ε^3 = ε^2 * (1 + ε) := by ring
            _ ≤ ε * (1/16) * (1 + 1/16) := by
              apply mul_le_mul
              · calc ε^2 = ε * ε := by ring
                  _ ≤ ε * (1/16) := mul_le_mul_of_nonneg_left h_eps_le h_eps_pos.le
              · linarith
              · positivity
              · positivity
            _ = ε * (17/256) := by ring
            _ ≤ ε * (1/4) := mul_le_mul_of_nonneg_left (by norm_num) h_eps_pos.le
            _ = ε / 4 := by ring
        _ = xR + xB - 1 - ε^2 - ε^3 := by ring
    have h_C : 40 * η ≤ ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2 := by
      calc 40 * η ≤ 40 * (ε^2 / 320) := by linarith
        _ = ε^2 / 8 := by ring
        _ = ε * (ε / 4) / 2 := by ring
        _ ≤ ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2 := by
          apply div_le_div_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left h_x_bnd h_eps_pos.le
          · norm_num
    have h3_new : -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) ≤ -(40 * η) := by linarith
    let Y := K * log_n
    have hY : Y = K * log_n := rfl
    have step1 : -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * K * log_n + 3 * η * K * log_n = -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * Y + 3 * η * Y := by ring
    rw [step1]
    have step2 : -4 * η * K * log_n = -4 * η * Y := by ring
    rw [step2]
    have step0 : -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * Y ≤ -(40 * η) * Y := mul_le_mul_of_nonneg_right h3_new (by exact_mod_cast hKlog_nonneg)
    calc -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * Y + 3 * η * Y
      ≤ -(40 * η) * Y + 3 * η * Y := by linarith [step0]
      _ = -37 * η * Y := by ring
      _ ≤ -4 * η * Y := mul_le_mul_of_nonneg_right (by linarith) hKlog_nonneg

  have h_eps_pos : 0 < ε := lt_trans h_param.1 h_param.2.1 |>.trans h_param.2.2.1
  have h_eps_lt1 : ε < 1 := h_param.2.2.2.1
  have h_eps_le : ε ≤ 1/16 := h_param.2.2.2.2.1.le
  let η1 := ε / 80
  let η2 := ε * (1 - ε - 22 * ε ^ 2) / (320 * (1 + ε))
  let η3 := ε ^ 2 / 320
  let η := min η1 (min η2 η3)
  use η
  have h_eps2 : ε^2 ≤ (1/16)^2 := by nlinarith
  have h_pos_1 : 0 < 1 - ε - 22 * ε^2 := by nlinarith
  have h_eta1 : 0 < η1 := by positivity
  have h_eta2 : 0 < η2 := by positivity
  have h_eta3 : 0 < η3 := by positivity
  have hη_pos : 0 < η := lt_min h_eta1 (lt_min h_eta2 h_eta3)
  refine ⟨hη_pos, ?_⟩
  have hη_le1 : η ≤ η1 := min_le_left _ _
  have hη_le2 : η ≤ η2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hη_le3 : η ≤ η3 := le_trans (min_le_right _ _) (min_le_right _ _)

  obtain ⟨N_margin, hN_margin1, hN_margin2⟩ := FixedSetProjectionBinomialSummationMargins h_param hη_pos hδ
  obtain ⟨N_mid, hN_mid1, hN_mid2⟩ := FixedSetProjectionMiddleRegimeExponent h_param hη_pos hη_le2
  obtain ⟨N_up, hN_up1, hN_up2⟩ := FixedSetProjectionUpperRegimeExponent h_param hη_pos hη_le3
  
  let N := max N_margin (max N_mid N_up)
  use N
  have hN_ge : n0 ≤ N := by omega
  refine ⟨hN_ge, ?_⟩
  intros n hn
  have hn_margin : N_margin < n := by omega
  have hn_mid : N_mid < n := by omega
  have hn_up : N_up < n := by omega
  
  let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
  let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
  
  have ⟨hK1, hKn, hlog_choose, h_margin⟩ := hN_margin2 n hn_margin
  have hK_pos_nat : 0 < K := by omega
  have hk_pos : 0 < (K : ℝ) := by exact Nat.cast_pos.mpr hK_pos_nat
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : 0 < (n : ℝ) := by exact Nat.cast_pos.mpr hn_pos_nat
  have hn_ge_1 : 1 ≤ n := by omega
  have hp_pos : 0 ≤ p := by
    dsimp [p, TwoBiteEdgeProbability]
    positivity
  have h_K_nonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hk_ge_1 : 1 ≤ (K : ℝ) := by exact_mod_cast hK1
  have hKlog_nonneg : 0 ≤ (K : ℝ) * Real.log (n : ℝ) := mul_nonneg h_K_nonneg (Real.log_nonneg (by exact_mod_cast hn_ge_1))
  have h_choose_pos : 0 < (Nat.choose n K : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hKn)

  have h_bound : ∀ ℓR ℓB, ℓR ∈ Finset.range (K + 1) → ℓB ∈ Finset.range (K + 1) → K ≤ ℓR * ℓB →
    Real.exp ((η - (2 - (ℓR : ℝ) / (K : ℝ) - (ℓB : ℝ) / (K : ℝ)) / 2) * (K : ℝ) * Real.log (n : ℝ)) *
    min (1 : ℝ) (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2))))
    * (Nat.choose n K : ℝ)
    ≤ Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ)) := by
    intros ℓR ℓB hℓR hℓB _hK_prod
    let xR : ℝ := (ℓR : ℝ) / (K : ℝ)
    let xB : ℝ := (ℓB : ℝ) / (K : ℝ)
    have hlR : ℓR ≤ K := Nat.lt_add_one_iff.mp (Finset.mem_range.mp hℓR)
    have hlB : ℓB ≤ K := Nat.lt_add_one_iff.mp (Finset.mem_range.mp hℓB)
    
    have h_choose_le : (Nat.choose n K : ℝ) ≤ Real.exp (((1 / 2 : ℝ) + η) * (K : ℝ) * Real.log (n : ℝ)) := by
      exact Real.exp_le_exp.mpr hlog_choose |>.trans' (by
        have : Real.exp (Real.log (Nat.choose n K : ℝ)) = (Nat.choose n K : ℝ) := Real.exp_log h_choose_pos
        exact le_of_eq this.symm)
        
    have h_exp_mul : Real.exp ((η - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) * (Nat.choose n K : ℝ)
      ≤ Real.exp (((η - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) + (((1 / 2 : ℝ) + η) * (K : ℝ) * Real.log (n : ℝ))) := by
      calc Real.exp ((η - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) * (Nat.choose n K : ℝ)
        ≤ Real.exp ((η - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) * Real.exp (((1 / 2 : ℝ) + η) * (K : ℝ) * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left h_choose_le (Real.exp_pos _).le
        _ = Real.exp (((η - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) + (((1 / 2 : ℝ) + η) * (K : ℝ) * Real.log (n : ℝ))) := (Real.exp_add _ _).symm
        
    have h_exp_combined : ((η - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) + (((1 / 2 : ℝ) + η) * (K : ℝ) * Real.log (n : ℝ))
      = (η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ) := by ring
      
    have h_summand_le : Real.exp ((η - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) * min 1 (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2)))) * (Nat.choose n K : ℝ)
      ≤ Real.exp ((η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) * min 1 (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2)))) := by
      calc Real.exp ((η - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) * min 1 (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2)))) * (Nat.choose n K : ℝ)
        = (Real.exp ((η - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) * (Nat.choose n K : ℝ)) * min 1 (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2)))) := by ring
        _ ≤ Real.exp (((η - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) + (((1 / 2 : ℝ) + η) * (K : ℝ) * Real.log (n : ℝ))) * min 1 (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2)))) := by
          apply mul_le_mul_of_nonneg_right h_exp_mul
          exact le_min zero_le_one (Real.exp_pos _).le
        _ = Real.exp ((η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)) * min 1 (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2)))) := by rw [h_exp_combined]

    let A := (η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) * (K : ℝ) * Real.log (n : ℝ)
    let X := -(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2))
    
    by_cases h_lower : xR + xB ≤ 1 - ε / 2
    · have h_child := @FixedSetProjectionLowerRegimeExponent ε η p K n ℓR ℓB h_eps_pos hK_pos_nat hKlog_nonneg hη_le1 hlR hlB h_lower
      have h_A : A + min 0 X ≤ -4 * η * (K : ℝ) * Real.log (n : ℝ) := h_child
      exact h_summand_le.trans (exp_min_bound_lower h_A)
      
    · by_cases h_upper : 1 + ε / 2 ≤ xR + xB
      · have h_child := hN_up2 hn_up hlR hlB h_upper
        have h_child2 : A - p * (RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) - RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) - RealChooseTwo ((K : ℝ) - (ℓB : ℝ)) - ε ^ 3 * (K : ℝ) ^ 2) ≤ -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * (K : ℝ) * Real.log (n : ℝ) + 3 * η * (K : ℝ) * Real.log (n : ℝ) := h_child
        have h_proj := proj_open_pair_bound_up ℓR ℓB K p n ε hp_pos
        have h_A : A + X ≤ -(ε * (xR + xB - 1 - ε ^ 2 - ε ^ 3) / 2) * (K : ℝ) * Real.log (n : ℝ) + 3 * η * (K : ℝ) * Real.log (n : ℝ) := by
          have step1 : A + X ≤ A - p * (RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) - RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) - RealChooseTwo ((K : ℝ) - (ℓB : ℝ)) - ε ^ 3 * (K : ℝ) ^ 2) := by linarith [h_proj]
          exact step1.trans h_child2
        have h_up_bound := upper_regime_bound ε η xR xB K (Real.log n) h_eps_pos h_eps_le hη_pos.le hη_le3 h_upper hKlog_nonneg
        have h_A_final : A + X ≤ -4 * η * (K : ℝ) * Real.log (n : ℝ) := h_A.trans h_up_bound
        exact h_summand_le.trans (exp_min_bound_other h_A_final)
        
      · push Not at h_lower h_upper
        have h_mid_cond : xR + xB < 1 + ε / 2 := h_upper
        by_cases h_xB : xB ≤ xR
        · have h_child := (hN_mid2 hn_mid hlR hlB h_lower h_mid_cond h_xB).2
          have h_child2 : A - p * (RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) - RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) - RealChooseTwo (p * (n : ℝ)) - RealChooseTwo ((K : ℝ) - (ℓB : ℝ) - p * (n : ℝ)) - ε ^ 3 * (K : ℝ) ^ 2) ≤ (ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) + 3 * η * (K : ℝ) * Real.log (n : ℝ) := h_child
          have h_proj := proj_open_pair_bound_mid ℓR ℓB K p n ε hp_pos
          have h_A : A + X ≤ (ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) + 3 * η * (K : ℝ) * Real.log (n : ℝ) := by
            have step1 : A + X ≤ A - p * (RealChooseTwo (ℓR : ℝ) + RealChooseTwo (ℓB : ℝ) - RealChooseTwo ((K : ℝ) - (ℓR : ℝ)) - RealChooseTwo (p * (n : ℝ)) - RealChooseTwo ((K : ℝ) - (ℓB : ℝ) - p * (n : ℝ)) - ε ^ 3 * (K : ℝ) ^ 2) := by linarith [h_proj]
            exact step1.trans h_child2
          have h_mid_bound := middle_regime_bound ε η K (Real.log n) hη_pos.le (by linarith) hη_le2 hKlog_nonneg
          have h_A_final : A + X ≤ -4 * η * (K : ℝ) * Real.log (n : ℝ) := h_A.trans h_mid_bound
          exact h_summand_le.trans (exp_min_bound_other h_A_final)
          
        · push Not at h_xB
          have h_symm_proj : ProjectionOpenPairFunction ℓR ℓB K p n = ProjectionOpenPairFunction ℓB ℓR K p n := by
            dsimp [ProjectionOpenPairFunction]
            ring
          have h_xR_le : xR ≤ xB := h_xB.le
          have h_child := (hN_mid2 hn_mid hlB hlR (by rwa [add_comm]) (by rwa [add_comm]) h_xR_le).2
          have h_child2 : (η + (1 / 2 + η) - (2 - xB - xR) / 2) * (K : ℝ) * Real.log (n : ℝ) - p * (RealChooseTwo (ℓB : ℝ) + RealChooseTwo (ℓR : ℝ) - RealChooseTwo ((K : ℝ) - (ℓB : ℝ)) - RealChooseTwo (p * (n : ℝ)) - RealChooseTwo ((K : ℝ) - (ℓR : ℝ) - p * (n : ℝ)) - ε ^ 3 * (K : ℝ) ^ 2) ≤ (ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) + 3 * η * (K : ℝ) * Real.log (n : ℝ) := h_child
          have h_proj := proj_open_pair_bound_mid ℓB ℓR K p n ε hp_pos
          have h_A : A + X ≤ (ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε))) * (K : ℝ) * Real.log (n : ℝ) + 3 * η * (K : ℝ) * Real.log (n : ℝ) := by
            have hX_symm : X = -p * (ProjectionOpenPairFunction ℓB ℓR K p n - ε ^ 3 * K ^ 2) := by
              dsimp [X]
              rw [h_symm_proj]
              ring
            have h_proj_symm : X ≤ -p * (RealChooseTwo (ℓB : ℝ) + RealChooseTwo (ℓR : ℝ) - RealChooseTwo ((K : ℝ) - (ℓB : ℝ)) - RealChooseTwo (p * (n : ℝ)) - RealChooseTwo ((K : ℝ) - (ℓR : ℝ) - p * (n : ℝ)) - ε ^ 3 * (K : ℝ) ^ 2) := hX_symm.trans_le h_proj
            have h_symm_A : A = (η + (1 / 2 + η) - (2 - xB - xR) / 2) * (K : ℝ) * Real.log (n : ℝ) := by
              dsimp [A]
              have : (2 - xR - xB) = (2 - xB - xR) := by ring
              rw [this]
            rw [h_symm_A]
            have step1 : (η + (1 / 2 + η) - (2 - xB - xR) / 2) * (K : ℝ) * Real.log (n : ℝ) + X ≤ (η + (1 / 2 + η) - (2 - xB - xR) / 2) * (K : ℝ) * Real.log (n : ℝ) - p * (RealChooseTwo (ℓB : ℝ) + RealChooseTwo (ℓR : ℝ) - RealChooseTwo ((K : ℝ) - (ℓB : ℝ)) - RealChooseTwo (p * (n : ℝ)) - RealChooseTwo ((K : ℝ) - (ℓR : ℝ) - p * (n : ℝ)) - ε ^ 3 * (K : ℝ) ^ 2) := by linarith [h_proj_symm]
            exact step1.trans h_child2
          have h_mid_bound := middle_regime_bound ε η K (Real.log n) hη_pos.le (by linarith) hη_le2 hKlog_nonneg
          have h_A_final : A + X ≤ -4 * η * (K : ℝ) * Real.log (n : ℝ) := h_A.trans h_mid_bound
          exact h_summand_le.trans (exp_min_bound_other h_A_final)

  have h_sum_le : (Finset.range (K + 1)).sum (fun ℓR => (Finset.range (K + 1)).sum (fun ℓB =>
    if ℓR * ℓB < K then (0 : ℝ)
    else Real.exp ((η - (2 - (ℓR : ℝ) / (K : ℝ) - (ℓB : ℝ) / (K : ℝ)) / 2) * (K : ℝ) * Real.log (n : ℝ)) *
         min (1 : ℝ) (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2))))
    )) * (Nat.choose n K : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ)) := by
    have step_mul : (Finset.range (K + 1)).sum (fun ℓR => (Finset.range (K + 1)).sum (fun ℓB => if ℓR * ℓB < K then (0 : ℝ) else Real.exp ((η - (2 - (ℓR : ℝ) / (K : ℝ) - (ℓB : ℝ) / (K : ℝ)) / 2) * (K : ℝ) * Real.log (n : ℝ)) * min (1 : ℝ) (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2)))))) * (Nat.choose n K : ℝ)
      = (Finset.range (K + 1)).sum (fun ℓR => (Finset.range (K + 1)).sum (fun ℓB => (if ℓR * ℓB < K then (0 : ℝ) else Real.exp ((η - (2 - (ℓR : ℝ) / (K : ℝ) - (ℓB : ℝ) / (K : ℝ)) / 2) * (K : ℝ) * Real.log (n : ℝ)) * min (1 : ℝ) (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2))))) * (Nat.choose n K : ℝ))) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intros x hx
        rw [Finset.sum_mul]
    rw [step_mul]
    have step_le : (Finset.range (K + 1)).sum (fun ℓR => (Finset.range (K + 1)).sum (fun ℓB => (if ℓR * ℓB < K then (0 : ℝ) else Real.exp ((η - (2 - (ℓR : ℝ) / (K : ℝ) - (ℓB : ℝ) / (K : ℝ)) / 2) * (K : ℝ) * Real.log (n : ℝ)) * min (1 : ℝ) (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2))))) * (Nat.choose n K : ℝ)))
      ≤ (Finset.range (K + 1)).sum (fun ℓR => (Finset.range (K + 1)).sum (fun ℓB => Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ)))) := by
        apply Finset.sum_le_sum
        intros ℓR hℓR
        apply Finset.sum_le_sum
        intros ℓB hℓB
        by_cases h_cond : ℓR * ℓB < K
        · rw [if_pos h_cond]
          have : 0 * (Nat.choose n K : ℝ) = 0 := MulZeroClass.zero_mul _
          rw [this]
          exact (Real.exp_pos _).le
        · rw [if_neg h_cond]
          push Not at h_cond
          exact h_bound ℓR ℓB hℓR hℓB h_cond
    have step_eq : (Finset.range (K + 1)).sum (fun ℓR => (Finset.range (K + 1)).sum (fun ℓB => Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ))))
      = ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have h_eq_K : ((K + 1 : ℕ) : ℝ) = ((1 + K : ℕ) : ℝ) := by rw [add_comm]
        rw [h_eq_K]
        have h_ring : ((1 + K : ℕ) : ℝ) * (((1 + K : ℕ) : ℝ) * Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ))) = ((1 + K : ℕ) : ℝ) ^ 2 * Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ)) := by
          calc ((1 + K : ℕ) : ℝ) * (((1 + K : ℕ) : ℝ) * Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ)))
            = (((1 + K : ℕ) : ℝ) * ((1 + K : ℕ) : ℝ)) * Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ)) := (mul_assoc _ _ _).symm
            _ = ((1 + K : ℕ) : ℝ) ^ 2 * Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ)) := by rw [← sq]
        exact h_ring
    exact step_le.trans_eq step_eq

  have h_K1_pos : 0 < ((K + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_K1_sq_exp : ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ)) ≤ δ := by
    have h_log_bound : 2 * Real.log ((K + 1 : ℕ) : ℝ) + Real.log δ⁻¹ ≤ η * (K : ℝ) * Real.log (n : ℝ) := h_margin
    have h_log_K1 : Real.log (((K + 1 : ℕ) : ℝ) ^ 2) = 2 * Real.log ((K + 1 : ℕ) : ℝ) := by
      have : (((K + 1 : ℕ) : ℝ) ^ 2) = ((K + 1 : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ) := by ring
      rw [this, Real.log_mul (ne_of_gt h_K1_pos) (ne_of_gt h_K1_pos)]
      ring
    have h_ineq : Real.log (((K + 1 : ℕ) : ℝ) ^ 2) - η * (K : ℝ) * Real.log (n : ℝ) ≤ - Real.log δ⁻¹ := by linarith
    have h_ineq2 : Real.log (((K + 1 : ℕ) : ℝ) ^ 2) - 4 * η * (K : ℝ) * Real.log (n : ℝ) ≤ Real.log δ := by
      have : Real.log δ⁻¹ = - Real.log δ := Real.log_inv δ
      have : 0 ≤ η * (K : ℝ) * Real.log (n : ℝ) := by positivity
      linarith
    have h_exp_ineq : Real.exp (Real.log (((K + 1 : ℕ) : ℝ) ^ 2) - 4 * η * (K : ℝ) * Real.log (n : ℝ)) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr h_ineq2
    have h_exp_lhs : Real.exp (Real.log (((K + 1 : ℕ) : ℝ) ^ 2) - 4 * η * (K : ℝ) * Real.log (n : ℝ)) = ((K + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-4 * η * (K : ℝ) * Real.log (n : ℝ)) := by
      have : Real.log (((K + 1 : ℕ) : ℝ) ^ 2) - 4 * η * (K : ℝ) * Real.log (n : ℝ) = Real.log (((K + 1 : ℕ) : ℝ) ^ 2) + (- 4 * η * (K : ℝ) * Real.log (n : ℝ)) := by ring
      rw [this, Real.exp_add, Real.exp_log (pow_pos h_K1_pos 2)]
    have h_exp_rhs : Real.exp (Real.log δ) = δ := Real.exp_log hδ
    rwa [h_exp_lhs, h_exp_rhs] at h_exp_ineq

  have step_final1 : (Finset.range (K + 1)).sum (fun ℓR => (Finset.range (K + 1)).sum (fun ℓB => if ℓR * ℓB < K then (0 : ℝ) else Real.exp ((η - (2 - (ℓR : ℝ) / (K : ℝ) - (ℓB : ℝ) / (K : ℝ)) / 2) * (K : ℝ) * Real.log (n : ℝ)) * min (1 : ℝ) (Real.exp (-(p * (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p (n : ℝ) - ε ^ 3 * (K : ℝ) ^ 2)))))) ≤ δ / (Nat.choose n K : ℝ) := (le_div_iff₀ h_choose_pos).mpr (h_sum_le.trans h_K1_sq_exp)
  have step_final2 : δ / (Nat.choose n K : ℝ) = δ * ((Nat.choose n K : ℝ)⁻¹) := div_eq_mul_inv δ (Nat.choose n K : ℝ)
  exact step_final1.trans_eq step_final2
