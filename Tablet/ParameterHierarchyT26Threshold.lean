import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT26Threshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT26Threshold :
    ∀ η ε1 : ℝ, 0 < η → 0 < ε1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 / L ≤ ε1 / 2 ∧
          1 /
              ((1 + η) * Real.rpow (n : ℝ) (1 / 4 : ℝ) * Real.sqrt L) ≤
            ε1 / 2 := by
-- BODY
  intro η ε1 hη_pos hε1_pos
  have h_one_add_pos : 0 < 1 + η := by linarith
  have h_one_add_ge_one : (1 : ℝ) ≤ 1 + η := by linarith
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hquarter_atTop :
      Tendsto (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (4 : ℝ)⁻¹)).comp hn_atTop
  have hfirst_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        2 / L ≤ ε1 / 2 := by
    filter_upwards [hlog_atTop.eventually_ge_atTop (4 / ε1)] with n hL_ge
    let L := Real.log (n : ℝ)
    have hfour_div_pos : 0 < 4 / ε1 := by positivity
    have hL_pos : 0 < L := by
      exact lt_of_lt_of_le hfour_div_pos (by simpa [L] using hL_ge)
    have hmul :
        (2 : ℝ) ≤ (ε1 / 2) * L := by
      calc
        (2 : ℝ) = (ε1 / 2) * (4 / ε1) := by
          field_simp [hε1_pos.ne']
          ring
        _ ≤ (ε1 / 2) * L :=
          mul_le_mul_of_nonneg_left (by simpa [L] using hL_ge) (by positivity)
    rw [div_le_iff₀ hL_pos]
    simpa [one_mul] using hmul
  have hquarter_eventually :
      ∀ᶠ n : ℕ in atTop,
        2 / ε1 ≤ Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
    filter_upwards [hquarter_atTop.eventually_ge_atTop (2 / ε1)] with n hpow
    simpa [one_div] using hpow
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        2 / L ≤ ε1 / 2 ∧
          1 /
              ((1 + η) * Real.rpow (n : ℝ) (1 / 4 : ℝ) * Real.sqrt L) ≤
            ε1 / 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_atTop.eventually_ge_atTop (1 : ℝ),
      hfirst_eventually,
      hquarter_eventually] with n hn_ge_one hL_ge_one hfirst hquarter
    let L := Real.log (n : ℝ)
    let q := Real.rpow (n : ℝ) (1 / 4 : ℝ)
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
    have hL_ge_one_local : (1 : ℝ) ≤ L := by
      simpa [L] using hL_ge_one
    have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge_one_local
    have hq_pos : 0 < q := by
      dsimp [q]
      exact Real.rpow_pos_of_pos hn_pos _
    have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
    have hsqrtL_ge_one : (1 : ℝ) ≤ Real.sqrt L := by
      simpa using Real.sqrt_le_sqrt hL_ge_one_local
    have hsqrtL_pos : 0 < Real.sqrt L :=
      lt_of_lt_of_le zero_lt_one hsqrtL_ge_one
    have hden_pos :
        0 < (1 + η) * q * Real.sqrt L :=
      mul_pos (mul_pos h_one_add_pos hq_pos) hsqrtL_pos
    have hq_le_den :
        q ≤ (1 + η) * q * Real.sqrt L := by
      have hq_le_scaled : q ≤ (1 + η) * q := by
        calc
          q = 1 * q := by ring
          _ ≤ (1 + η) * q :=
            mul_le_mul_of_nonneg_right h_one_add_ge_one hq_nonneg
      have hscaled_nonneg : 0 ≤ (1 + η) * q :=
        mul_nonneg (le_of_lt h_one_add_pos) hq_nonneg
      calc
        q ≤ (1 + η) * q := hq_le_scaled
        _ = (1 + η) * q * 1 := by ring
        _ ≤ (1 + η) * q * Real.sqrt L :=
          mul_le_mul_of_nonneg_left hsqrtL_ge_one hscaled_nonneg
    have htwo_div_pos : 0 < 2 / ε1 := by positivity
    have hden_ge : 2 / ε1 ≤ (1 + η) * q * Real.sqrt L :=
      le_trans (by simpa [q] using hquarter) hq_le_den
    have h_inv_le :
        ((1 + η) * q * Real.sqrt L)⁻¹ ≤ (2 / ε1)⁻¹ :=
      inv_anti₀ htwo_div_pos hden_ge
    have h_inv_eq : (2 / ε1)⁻¹ = ε1 / 2 := by
      field_simp [hε1_pos.ne']
    exact ⟨by simpa [L] using hfirst,
      by
        simpa [L, q, one_div, h_inv_eq] using h_inv_le⟩
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
