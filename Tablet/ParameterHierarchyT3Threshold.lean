import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT3Threshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT3Threshold :
    ∀ η : ℝ, 0 < η →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        1 < L ∧ 16 * L ^ 2 * Real.sqrt L ≤ kReal := by
-- BODY
  intro η hη
  have hκpos : 0 < 1 + η := by linarith
  have hκ_ge_one : (1 : ℝ) ≤ 1 + η := by linarith
  let δ : ℝ := (1 / 8 : ℝ)
  have hδ_pos : 0 < δ := by dsimp [δ]; norm_num
  have hδ_le_one : δ ≤ 1 := by dsimp [δ]; norm_num
  have hδ_coeff : 16 * δ ^ (5 / 2 : ℝ) ≤ 1 := by
    have hpow_le_sq : δ ^ (5 / 2 : ℝ) ≤ δ ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one
        (by norm_num : (2 : ℝ) ≤ 5 / 2)
    have hδsq : δ ^ 2 = (1 / 64 : ℝ) := by
      dsimp [δ]
      norm_num
    have hsq : δ ^ (2 : ℝ) = δ ^ 2 := Real.rpow_natCast δ 2
    nlinarith
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hlog_le_delta_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤ δ * (n : ℝ) ^ ((5 : ℝ)⁻¹) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => x ^ ((5 : ℝ)⁻¹)) :=
      isLittleO_log_rpow_atTop (by norm_num : 0 < (5 : ℝ)⁻¹)
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => (n : ℝ) ^ ((5 : ℝ)⁻¹)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def hδ_pos, eventually_ge_atTop (1 : ℕ)]
      with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ (n : ℝ) ^ ((5 : ℝ)⁻¹) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    exact hbound
  have hT3_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        1 < L ∧ 16 * L ^ 2 * Real.sqrt L ≤ kReal := by
    filter_upwards [hlog_atTop.eventually_gt_atTop (1 : ℝ),
      hlog_le_delta_eventually] with n hL_gt_one hL_le_delta
    let L := Real.log (n : ℝ)
    let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
    have hL_pos : 0 < L := by dsimp [L]; linarith
    have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hL_rpow_bound :
        L ^ (5 / 2 : ℝ) ≤ δ ^ (5 / 2 : ℝ) * Real.sqrt (n : ℝ) := by
      have hpow := Real.rpow_le_rpow hL_nonneg (by simpa [L] using hL_le_delta)
        (by norm_num : 0 ≤ (5 / 2 : ℝ))
      calc
        L ^ (5 / 2 : ℝ) ≤ (δ * (n : ℝ) ^ ((5 : ℝ)⁻¹)) ^ (5 / 2 : ℝ) :=
          hpow
        _ = δ ^ (5 / 2 : ℝ) * ((n : ℝ) ^ ((5 : ℝ)⁻¹)) ^ (5 / 2 : ℝ) := by
          rw [Real.mul_rpow (le_of_lt hδ_pos) (Real.rpow_nonneg hn_nonneg _)]
        _ = δ ^ (5 / 2 : ℝ) * (n : ℝ) ^ (((5 : ℝ)⁻¹) * (5 / 2 : ℝ)) := by
          rw [← Real.rpow_mul hn_nonneg]
        _ = δ ^ (5 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by norm_num
        _ = δ ^ (5 / 2 : ℝ) * Real.sqrt (n : ℝ) := by rw [← Real.sqrt_eq_rpow]
    have hL_power_eq : L ^ 2 * Real.sqrt L = L ^ (5 / 2 : ℝ) := by
      calc
        L ^ 2 * Real.sqrt L = L ^ (2 : ℝ) * L ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
          exact congrArg (fun x => x * L ^ (1 / 2 : ℝ)) (Real.rpow_natCast L 2).symm
        _ = L ^ ((2 : ℝ) + (1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hL_pos]
        _ = L ^ (5 / 2 : ℝ) := by norm_num
    have hn_le_nL : (n : ℝ) ≤ (n : ℝ) * L := by
      calc
        (n : ℝ) = (n : ℝ) * 1 := by ring
        _ ≤ (n : ℝ) * L :=
          mul_le_mul_of_nonneg_left (le_of_lt hL_gt_one) hn_nonneg
    have hsqrt_n_le : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * L) :=
      Real.sqrt_le_sqrt hn_le_nL
    have hscale_sqrt :
        16 * L ^ 2 * Real.sqrt L ≤ (1 + η) * Real.sqrt (n : ℝ) := by
      calc
        16 * L ^ 2 * Real.sqrt L = 16 * (L ^ 2 * Real.sqrt L) := by ring
        _ = 16 * L ^ (5 / 2 : ℝ) := by rw [hL_power_eq]
        _ ≤ 16 * (δ ^ (5 / 2 : ℝ) * Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hL_rpow_bound (by norm_num)
        _ = (16 * δ ^ (5 / 2 : ℝ)) * Real.sqrt (n : ℝ) := by ring
        _ ≤ 1 * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_right hδ_coeff (Real.sqrt_nonneg _)
        _ ≤ (1 + η) * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_right hκ_ge_one (Real.sqrt_nonneg _)
    have hscale : 16 * L ^ 2 * Real.sqrt L ≤ kReal := by
      calc
        16 * L ^ 2 * Real.sqrt L ≤ (1 + η) * Real.sqrt (n : ℝ) := hscale_sqrt
        _ ≤ (1 + η) * Real.sqrt ((n : ℝ) * L) :=
          mul_le_mul_of_nonneg_left hsqrt_n_le (le_of_lt hκpos)
        _ = kReal := by dsimp [kReal]
    exact ⟨by simpa [L] using hL_gt_one, hscale⟩
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hT3_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
