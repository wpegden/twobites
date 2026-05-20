import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT24Threshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT24Threshold :
    ∀ η : ℝ, 0 < η →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 * (1 + η) * Real.sqrt L / Real.rpow (n : ℝ) η < (1 / 2 : ℝ) := by
-- BODY
  intro η hη_pos
  let c : ℝ := 1 / (8 * (1 + η))
  have h_one_add_pos : 0 < 1 + η := by linarith
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_pos hc_pos
  have htwo_eta_pos : 0 < 2 * η := by positivity
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_le_c_sq_power_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤ c ^ 2 * Real.rpow (n : ℝ) (2 * η) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => Real.rpow x (2 * η)) :=
      isLittleO_log_rpow_atTop htwo_eta_pos
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => Real.rpow (n : ℝ) (2 * η)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def hc_sq_pos,
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (2 * η) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    simpa using hbound
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        2 * (1 + η) * Real.sqrt L / Real.rpow (n : ℝ) η < (1 / 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_le_c_sq_power_eventually] with n hn_ge_one hL_le
    let L := Real.log (n : ℝ)
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hL_nonneg : 0 ≤ L := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have heta_power_pos : 0 < Real.rpow (n : ℝ) η :=
      Real.rpow_pos_of_pos hn_pos _
    have heta_power_nonneg : 0 ≤ Real.rpow (n : ℝ) η :=
      le_of_lt heta_power_pos
    have htwo_eta_power :
        (Real.rpow (n : ℝ) η) ^ 2 = Real.rpow (n : ℝ) (2 * η) := by
      calc
        (Real.rpow (n : ℝ) η) ^ 2 =
            Real.rpow (n : ℝ) η * Real.rpow (n : ℝ) η := by ring
        _ = Real.rpow (n : ℝ) (η + η) := by
          exact (Real.rpow_add hn_pos η η).symm
        _ = Real.rpow (n : ℝ) (2 * η) := by
          congr 1
          ring
    have hright_sq :
        (c * Real.rpow (n : ℝ) η) ^ 2 =
          c ^ 2 * Real.rpow (n : ℝ) (2 * η) := by
      calc
        (c * Real.rpow (n : ℝ) η) ^ 2 =
            c ^ 2 * (Real.rpow (n : ℝ) η) ^ 2 := by ring
        _ = c ^ 2 * Real.rpow (n : ℝ) (2 * η) := by rw [htwo_eta_power]
    have hright_nonneg : 0 ≤ c * Real.rpow (n : ℝ) η :=
      mul_nonneg (le_of_lt hc_pos) heta_power_nonneg
    have hsqrtL_le : Real.sqrt L ≤ c * Real.rpow (n : ℝ) η := by
      calc
        Real.sqrt L ≤ Real.sqrt (c ^ 2 * Real.rpow (n : ℝ) (2 * η)) :=
          Real.sqrt_le_sqrt (by simpa [L] using hL_le)
        _ = Real.sqrt ((c * Real.rpow (n : ℝ) η) ^ 2) := by rw [hright_sq]
        _ = |c * Real.rpow (n : ℝ) η| := Real.sqrt_sq_eq_abs _
        _ = c * Real.rpow (n : ℝ) η := abs_of_nonneg hright_nonneg
    have hcoeff_eq : 2 * (1 + η) * c = (1 / 4 : ℝ) := by
      dsimp [c]
      field_simp [ne_of_gt h_one_add_pos]
      ring_nf
    have hnum_lt :
        2 * (1 + η) * Real.sqrt L <
          (1 / 2 : ℝ) * Real.rpow (n : ℝ) η := by
      have hcoeff_nonneg : 0 ≤ 2 * (1 + η) := by positivity
      calc
        2 * (1 + η) * Real.sqrt L ≤
            2 * (1 + η) * (c * Real.rpow (n : ℝ) η) :=
          mul_le_mul_of_nonneg_left hsqrtL_le hcoeff_nonneg
        _ = (1 / 4 : ℝ) * Real.rpow (n : ℝ) η := by
          calc
            2 * (1 + η) * (c * Real.rpow (n : ℝ) η) =
                (2 * (1 + η) * c) * Real.rpow (n : ℝ) η := by ring
            _ = (1 / 4 : ℝ) * Real.rpow (n : ℝ) η := by rw [hcoeff_eq]
        _ < (1 / 2 : ℝ) * Real.rpow (n : ℝ) η :=
          mul_lt_mul_of_pos_right (by norm_num : (1 / 4 : ℝ) < 1 / 2)
            heta_power_pos
    rw [div_lt_iff₀ heta_power_pos]
    simpa [one_mul] using hnum_lt
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
