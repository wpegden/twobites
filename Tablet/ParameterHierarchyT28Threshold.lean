import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT28Threshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT28Threshold :
    ∀ η ε1 : ℝ, 0 < η → 0 < ε1 → η < (1 / 16 : ℝ) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 * (1 + η) * Real.sqrt L * L /
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * η) ≤ (1 / 4 : ℝ) ∧
          4 * (1 + η) * Real.sqrt L * L / Real.rpow (n : ℝ) η ≤
              (1 / 4 : ℝ) ∧
            Real.exp
                (-(1 / 2 : ℝ) *
                  Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * η)) ≤ ε1 := by
-- BODY
  intro η ε1 hη_pos hε1_pos hη_lt_sixteen
  let a : ℝ := (1 / 4 : ℝ) - 2 * η
  let b : ℝ := (3 / 4 : ℝ) - 2 * η
  let c₁ : ℝ := 1 / (8 * (1 + η))
  let c₂ : ℝ := 1 / (16 * (1 + η))
  have h_one_add_pos : 0 < 1 + η := by linarith
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have hb_pos : 0 < b := by
    dsimp [b]
    linarith
  have hhalf_a_pos : 0 < a / 2 := by positivity
  have hhalf_eta_pos : 0 < η / 2 := by positivity
  have hc₁_pos : 0 < c₁ := by
    dsimp [c₁]
    positivity
  have hc₂_pos : 0 < c₂ := by
    dsimp [c₂]
    positivity
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hlog_le_first_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤ c₁ * Real.rpow (n : ℝ) (a / 2) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => Real.rpow x (a / 2)) :=
      isLittleO_log_rpow_atTop hhalf_a_pos
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => Real.rpow (n : ℝ) (a / 2)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def hc₁_pos,
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (a / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    simpa using hbound
  have hlog_le_second_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤ c₂ * Real.rpow (n : ℝ) (η / 2) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => Real.rpow x (η / 2)) :=
      isLittleO_log_rpow_atTop hhalf_eta_pos
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => Real.rpow (n : ℝ) (η / 2)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def hc₂_pos,
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (η / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    simpa using hbound
  have htail_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.exp
            (-(1 / 2 : ℝ) * Real.rpow (n : ℝ) b) ≤ ε1 := by
    have hb_atTop :
        Tendsto (fun n : ℕ => Real.rpow (n : ℝ) b) atTop atTop :=
      (tendsto_rpow_atTop hb_pos).comp hn_atTop
    filter_upwards [hb_atTop.eventually_ge_atTop
      (max (0 : ℝ) (-2 * Real.log ε1))] with n hpow_ge
    let A := Real.rpow (n : ℝ) b
    have hlog_floor : -2 * Real.log ε1 ≤ A := by
      exact le_trans (le_max_right (0 : ℝ) (-2 * Real.log ε1))
        (by simpa [A] using hpow_ge)
    have harg_le_log : -(1 / 2 : ℝ) * A ≤ Real.log ε1 := by
      nlinarith
    exact (Real.le_log_iff_exp_le hε1_pos).1 harg_le_log
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        2 * (1 + η) * Real.sqrt L * L /
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * η) ≤ (1 / 4 : ℝ) ∧
          4 * (1 + η) * Real.sqrt L * L / Real.rpow (n : ℝ) η ≤
              (1 / 4 : ℝ) ∧
            Real.exp
                (-(1 / 2 : ℝ) *
                  Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * η)) ≤ ε1 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_atTop.eventually_ge_atTop (1 : ℝ),
      hlog_le_first_eventually,
      hlog_le_second_eventually,
      htail_eventually] with n hn_ge_one hL_ge_one hfirst_log hsecond_log htail
    let L := Real.log (n : ℝ)
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
    have hL_ge_one_local : (1 : ℝ) ≤ L := by
      simpa [L] using hL_ge_one
    have hL_nonneg : 0 ≤ L := le_trans zero_le_one hL_ge_one_local
    have hsqrtL_le_L : Real.sqrt L ≤ L := by
      have hL_le_sq : L ≤ L ^ 2 := by
        calc
          L = L * 1 := by ring
          _ ≤ L * L := mul_le_mul_of_nonneg_left hL_ge_one_local hL_nonneg
          _ = L ^ 2 := by ring
      calc
        Real.sqrt L ≤ Real.sqrt (L ^ 2) := Real.sqrt_le_sqrt hL_le_sq
        _ = |L| := Real.sqrt_sq_eq_abs L
        _ = L := abs_of_nonneg hL_nonneg
    have hsqrtL_mul_le_sq : Real.sqrt L * L ≤ L ^ 2 := by
      calc
        Real.sqrt L * L ≤ L * L :=
          mul_le_mul_of_nonneg_right hsqrtL_le_L hL_nonneg
        _ = L ^ 2 := by ring
    have hfirst_power_sq :
        (Real.rpow (n : ℝ) (a / 2)) ^ 2 = Real.rpow (n : ℝ) a := by
      calc
        (Real.rpow (n : ℝ) (a / 2)) ^ 2 =
            Real.rpow (n : ℝ) (a / 2) * Real.rpow (n : ℝ) (a / 2) := by ring
        _ = Real.rpow (n : ℝ) ((a / 2) + (a / 2)) := by
          exact (Real.rpow_add hn_pos (a / 2) (a / 2)).symm
        _ = Real.rpow (n : ℝ) a := by
          congr 1
          ring
    have hsecond_power_sq :
        (Real.rpow (n : ℝ) (η / 2)) ^ 2 = Real.rpow (n : ℝ) η := by
      calc
        (Real.rpow (n : ℝ) (η / 2)) ^ 2 =
            Real.rpow (n : ℝ) (η / 2) * Real.rpow (n : ℝ) (η / 2) := by ring
        _ = Real.rpow (n : ℝ) ((η / 2) + (η / 2)) := by
          exact (Real.rpow_add hn_pos (η / 2) (η / 2)).symm
        _ = Real.rpow (n : ℝ) η := by
          congr 1
          ring
    have hL_sq_first :
        L ^ 2 ≤ c₁ ^ 2 * Real.rpow (n : ℝ) a := by
      have hpow := pow_le_pow_left₀ hL_nonneg (by simpa [L] using hfirst_log) 2
      calc
        L ^ 2 ≤ (c₁ * Real.rpow (n : ℝ) (a / 2)) ^ 2 := hpow
        _ = c₁ ^ 2 * (Real.rpow (n : ℝ) (a / 2)) ^ 2 := by ring
        _ = c₁ ^ 2 * Real.rpow (n : ℝ) a := by rw [hfirst_power_sq]
    have hL_sq_second :
        L ^ 2 ≤ c₂ ^ 2 * Real.rpow (n : ℝ) η := by
      have hpow := pow_le_pow_left₀ hL_nonneg (by simpa [L] using hsecond_log) 2
      calc
        L ^ 2 ≤ (c₂ * Real.rpow (n : ℝ) (η / 2)) ^ 2 := hpow
        _ = c₂ ^ 2 * (Real.rpow (n : ℝ) (η / 2)) ^ 2 := by ring
        _ = c₂ ^ 2 * Real.rpow (n : ℝ) η := by rw [hsecond_power_sq]
    have hcoeff₁ :
        2 * (1 + η) * c₁ ^ 2 ≤ (1 / 4 : ℝ) := by
      dsimp [c₁]
      field_simp [ne_of_gt h_one_add_pos]
      nlinarith [sq_nonneg (1 + η), h_one_add_pos]
    have hcoeff₂ :
        4 * (1 + η) * c₂ ^ 2 ≤ (1 / 4 : ℝ) := by
      dsimp [c₂]
      field_simp [ne_of_gt h_one_add_pos]
      nlinarith [sq_nonneg (1 + η), h_one_add_pos]
    have ha_power_pos : 0 < Real.rpow (n : ℝ) a :=
      Real.rpow_pos_of_pos hn_pos _
    have heta_power_pos : 0 < Real.rpow (n : ℝ) η :=
      Real.rpow_pos_of_pos hn_pos _
    have hfirst_num :
        2 * (1 + η) * Real.sqrt L * L ≤
          (1 / 4 : ℝ) * Real.rpow (n : ℝ) a := by
      have hcoeff_nonneg : 0 ≤ 2 * (1 + η) := by positivity
      calc
        2 * (1 + η) * Real.sqrt L * L =
            2 * (1 + η) * (Real.sqrt L * L) := by ring
        _ ≤ 2 * (1 + η) * L ^ 2 :=
          mul_le_mul_of_nonneg_left hsqrtL_mul_le_sq hcoeff_nonneg
        _ ≤ 2 * (1 + η) * (c₁ ^ 2 * Real.rpow (n : ℝ) a) :=
          mul_le_mul_of_nonneg_left hL_sq_first hcoeff_nonneg
        _ = (2 * (1 + η) * c₁ ^ 2) * Real.rpow (n : ℝ) a := by ring
        _ ≤ (1 / 4 : ℝ) * Real.rpow (n : ℝ) a :=
          mul_le_mul_of_nonneg_right hcoeff₁ (le_of_lt ha_power_pos)
    have hsecond_num :
        4 * (1 + η) * Real.sqrt L * L ≤
          (1 / 4 : ℝ) * Real.rpow (n : ℝ) η := by
      have hcoeff_nonneg : 0 ≤ 4 * (1 + η) := by positivity
      calc
        4 * (1 + η) * Real.sqrt L * L =
            4 * (1 + η) * (Real.sqrt L * L) := by ring
        _ ≤ 4 * (1 + η) * L ^ 2 :=
          mul_le_mul_of_nonneg_left hsqrtL_mul_le_sq hcoeff_nonneg
        _ ≤ 4 * (1 + η) * (c₂ ^ 2 * Real.rpow (n : ℝ) η) :=
          mul_le_mul_of_nonneg_left hL_sq_second hcoeff_nonneg
        _ = (4 * (1 + η) * c₂ ^ 2) * Real.rpow (n : ℝ) η := by ring
        _ ≤ (1 / 4 : ℝ) * Real.rpow (n : ℝ) η :=
          mul_le_mul_of_nonneg_right hcoeff₂ (le_of_lt heta_power_pos)
    have hfirst_threshold :
        2 * (1 + η) * Real.sqrt L * L / Real.rpow (n : ℝ) a ≤
          (1 / 4 : ℝ) := by
      rw [div_le_iff₀ ha_power_pos]
      simpa [one_mul] using hfirst_num
    have hsecond_threshold :
        4 * (1 + η) * Real.sqrt L * L / Real.rpow (n : ℝ) η ≤
          (1 / 4 : ℝ) := by
      rw [div_le_iff₀ heta_power_pos]
      simpa [one_mul] using hsecond_num
    exact ⟨by simpa [L, a] using hfirst_threshold,
      by
        refine ⟨by simpa [L] using hsecond_threshold, ?_⟩
        simpa [b] using htail⟩
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
