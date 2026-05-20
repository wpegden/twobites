import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyInitialPowerRatioThreshold]

open Filter
open scoped Topology

theorem ParameterHierarchyInitialPowerRatioThreshold :
    ∀ η ε1 : ℝ,
      0 < η →
      0 < ε1 →
      η < (1 / 16 : ℝ) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        Real.rpow (n : ℝ) (4 * η) ≤ (ε1 / 2) * kReal ∧
          2 * L ^ 2 ≤ (ε1 / 8) * kReal := by
-- BODY
  intro η ε1 hη hε1 hη_lt
  let c1 : ℝ := (ε1 / 2) * (1 + η)
  let c2 : ℝ := (ε1 / 8) * (1 + η)
  have hκpos : 0 < 1 + η := by linarith
  have hc1_pos : 0 < c1 := by
    dsimp [c1]
    positivity
  have hc2_pos : 0 < c2 := by
    dsimp [c2]
    positivity
  let δ : ℝ := Real.sqrt (c2 / 4)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact Real.sqrt_pos.mpr (div_pos hc2_pos (by norm_num))
  have hδ_sq : δ ^ 2 = c2 / 4 := by
    dsimp [δ]
    exact Real.sq_sqrt (le_of_lt (div_pos hc2_pos (by norm_num)))
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hquarter_atTop :
      Tendsto (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (4 : ℝ)⁻¹)).comp hn_atTop
  have hT1_scale_eventually :
      ∀ᶠ n : ℕ in atTop, 1 ≤ c1 * (n : ℝ) ^ ((4 : ℝ)⁻¹) :=
    (hquarter_atTop.const_mul_atTop hc1_pos).eventually_ge_atTop (1 : ℝ)
  have hlog_le_delta_quarter_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤ δ * (n : ℝ) ^ ((4 : ℝ)⁻¹) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => x ^ ((4 : ℝ)⁻¹)) :=
      isLittleO_log_rpow_atTop (by norm_num : 0 < (4 : ℝ)⁻¹)
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ)⁻¹)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def hδ_pos, eventually_ge_atTop (1 : ℕ)]
      with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ (n : ℝ) ^ ((4 : ℝ)⁻¹) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    exact hbound
  have hratio_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        Real.rpow (n : ℝ) (4 * η) ≤ (ε1 / 2) * kReal ∧
          2 * L ^ 2 ≤ (ε1 / 8) * kReal := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_atTop.eventually_ge_atTop (1 : ℝ),
      hT1_scale_eventually,
      hlog_le_delta_quarter_eventually] with n hn_ge_one hL_ge_one hT1_scale
        hlog_le_delta
    let L := Real.log (n : ℝ)
    let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn_ge_one_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
    have hL_nonneg : 0 ≤ L := by
      dsimp [L]
      exact le_trans zero_le_one hL_ge_one
    have hn_le_nL : (n : ℝ) ≤ (n : ℝ) * L := by
      calc
        (n : ℝ) = (n : ℝ) * 1 := by ring
        _ ≤ (n : ℝ) * L :=
          mul_le_mul_of_nonneg_left (by simpa [L] using hL_ge_one) hn_nonneg
    have hsqrt_n_le : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * L) :=
      Real.sqrt_le_sqrt hn_le_nL
    have hquarter_nonneg : 0 ≤ (n : ℝ) ^ ((4 : ℝ)⁻¹) :=
      Real.rpow_nonneg hn_nonneg _
    have hquarter_sq :
        ((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 2 = Real.sqrt (n : ℝ) := by
      calc
        ((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 2 =
            ((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ (2 : ℝ) := by
          exact (Real.rpow_natCast ((n : ℝ) ^ ((4 : ℝ)⁻¹)) 2).symm
        _ = (n : ℝ) ^ (((4 : ℝ)⁻¹) * 2) := by
          rw [← Real.rpow_mul hn_nonneg]
        _ = (n : ℝ) ^ (1 / 2 : ℝ) := by norm_num
        _ = Real.sqrt (n : ℝ) := by rw [← Real.sqrt_eq_rpow]
    have hT1_exponent : 4 * η ≤ ((4 : ℝ)⁻¹) := by
      nlinarith
    have hpow_eta_le_quarter :
        Real.rpow (n : ℝ) (4 * η) ≤ (n : ℝ) ^ ((4 : ℝ)⁻¹) :=
      Real.rpow_le_rpow_of_exponent_le hn_ge_one_real hT1_exponent
    have hquarter_le_c1_sqrt :
        (n : ℝ) ^ ((4 : ℝ)⁻¹) ≤ c1 * Real.sqrt (n : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hT1_scale hquarter_nonneg
      calc
        (n : ℝ) ^ ((4 : ℝ)⁻¹) = 1 * (n : ℝ) ^ ((4 : ℝ)⁻¹) := by ring
        _ ≤ (c1 * (n : ℝ) ^ ((4 : ℝ)⁻¹)) * (n : ℝ) ^ ((4 : ℝ)⁻¹) :=
          hmul
        _ = c1 * (((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 2) := by ring
        _ = c1 * Real.sqrt (n : ℝ) := by rw [hquarter_sq]
    have hT1_final :
        Real.rpow (n : ℝ) (4 * η) ≤ (ε1 / 2) * kReal := by
      calc
        Real.rpow (n : ℝ) (4 * η) ≤ (n : ℝ) ^ ((4 : ℝ)⁻¹) :=
          hpow_eta_le_quarter
        _ ≤ c1 * Real.sqrt (n : ℝ) := hquarter_le_c1_sqrt
        _ ≤ c1 * Real.sqrt ((n : ℝ) * L) :=
          mul_le_mul_of_nonneg_left hsqrt_n_le (le_of_lt hc1_pos)
        _ = (ε1 / 2) * kReal := by
          dsimp [c1, kReal]
          ring
    have hLsq_le_delta :
        L ^ 2 ≤ δ ^ 2 * Real.sqrt (n : ℝ) := by
      have hsquare := pow_le_pow_left₀ hL_nonneg (by simpa [L] using hlog_le_delta) 2
      calc
        L ^ 2 ≤ (δ * (n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 2 := hsquare
        _ = δ ^ 2 * (((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 2) := by ring
        _ = δ ^ 2 * Real.sqrt (n : ℝ) := by rw [hquarter_sq]
    have hcoef : 2 * δ ^ 2 ≤ c2 := by
      nlinarith [hδ_sq, hc2_pos]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have htwo_Lsq_le_c2_sqrt : 2 * L ^ 2 ≤ c2 * Real.sqrt (n : ℝ) := by
      calc
        2 * L ^ 2 ≤ 2 * (δ ^ 2 * Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hLsq_le_delta (by norm_num)
        _ = (2 * δ ^ 2) * Real.sqrt (n : ℝ) := by ring
        _ ≤ c2 * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef hsqrt_nonneg
    have hT2_final : 2 * L ^ 2 ≤ (ε1 / 8) * kReal := by
      calc
        2 * L ^ 2 ≤ c2 * Real.sqrt (n : ℝ) := htwo_Lsq_le_c2_sqrt
        _ ≤ c2 * Real.sqrt ((n : ℝ) * L) :=
          mul_le_mul_of_nonneg_left hsqrt_n_le (le_of_lt hc2_pos)
        _ = (ε1 / 8) * kReal := by
          dsimp [c2, kReal]
          ring
    exact ⟨hT1_final, hT2_final⟩
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hratio_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
