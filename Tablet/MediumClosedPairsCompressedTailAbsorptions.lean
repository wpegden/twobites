import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: MediumClosedPairsCompressedTailAbsorptions]

open Filter
open scoped Topology

theorem MediumClosedPairsCompressedTailAbsorptions
    (ε : ℝ) (hε_pos : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      let L := Real.log (n : ℝ)
      36 * Real.exp 1 * (1 + ε) * L ^ 3 ≤
          Real.rpow (n : ℝ) (2 * ε) ∧
        24 * L ^ 2 ≤ (1 + ε) * Real.sqrt L * Real.rpow (n : ℝ) ε := by
-- BODY
  let C1 : ℝ := 36 * Real.exp 1 * (1 + ε)
  have hC1_pos : 0 < C1 := by
    dsimp [C1]
    positivity
  have h2ε_pos : 0 < 2 * ε := by positivity
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hsmall1_real :
      (fun x : ℝ => (Real.log x) ^ 3) =o[atTop]
        (fun x : ℝ => Real.rpow x (2 * ε)) := by
    simpa [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (3 : ℝ) h2ε_pos)
  have hsmall1_nat :
      (fun n : ℕ => (Real.log (n : ℝ)) ^ 3) =o[atTop]
        (fun n : ℕ => Real.rpow (n : ℝ) (2 * ε)) :=
    hsmall1_real.comp_tendsto hn_atTop
  have hfirst_eventually :
      ∀ᶠ n : ℕ in atTop,
        C1 * (Real.log (n : ℝ)) ^ 3 ≤ Real.rpow (n : ℝ) (2 * ε) := by
    have hc : 0 < C1⁻¹ := inv_pos.mpr hC1_pos
    filter_upwards [hsmall1_nat.def hc, eventually_ge_atTop (1 : ℕ)]
      with n hbound hn_ge_one
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hlog3_nonneg : 0 ≤ (Real.log (n : ℝ)) ^ 3 :=
      pow_nonneg hlog_nonneg _
    have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (2 * ε) :=
      Real.rpow_nonneg hn_nonneg _
    rw [Real.norm_of_nonneg hlog3_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    have hmul := mul_le_mul_of_nonneg_left hbound hC1_pos.le
    calc
      C1 * (Real.log (n : ℝ)) ^ 3
          ≤ C1 * (C1⁻¹ * Real.rpow (n : ℝ) (2 * ε)) := by
        simpa [mul_assoc] using hmul
      _ = Real.rpow (n : ℝ) (2 * ε) := by
        field_simp [hC1_pos.ne']
  let C2 : ℝ := (1 + ε) / 24
  have hC2_pos : 0 < C2 := by
    dsimp [C2]
    positivity
  have hsmall2_real :
      (fun x : ℝ => (Real.log x) ^ 2) =o[atTop]
        (fun x : ℝ => Real.rpow x ε) := by
    simpa [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hε_pos)
  have hsmall2_nat :
      (fun n : ℕ => (Real.log (n : ℝ)) ^ 2) =o[atTop]
        (fun n : ℕ => Real.rpow (n : ℝ) ε) :=
    hsmall2_real.comp_tendsto hn_atTop
  have hsecond_base_eventually :
      ∀ᶠ n : ℕ in atTop,
        24 * (Real.log (n : ℝ)) ^ 2 ≤
          (1 + ε) * Real.rpow (n : ℝ) ε := by
    filter_upwards [hsmall2_nat.def hC2_pos, eventually_ge_atTop (1 : ℕ)]
      with n hbound hn_ge_one
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hlog2_nonneg : 0 ≤ (Real.log (n : ℝ)) ^ 2 :=
      pow_nonneg hlog_nonneg _
    have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) ε :=
      Real.rpow_nonneg hn_nonneg _
    rw [Real.norm_of_nonneg hlog2_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    have hmul := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 24)
    calc
      24 * (Real.log (n : ℝ)) ^ 2
          ≤ 24 * (C2 * Real.rpow (n : ℝ) ε) := by
        simpa [mul_assoc] using hmul
      _ = (1 + ε) * Real.rpow (n : ℝ) ε := by
        dsimp [C2]
        ring
  have hlog_ge_one_eventually :
      ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
    hlog_atTop.eventually_ge_atTop (1 : ℝ)
  filter_upwards [hfirst_eventually, hsecond_base_eventually, hlog_ge_one_eventually,
    eventually_ge_atTop (1 : ℕ)] with n hfirst hsecond_base hlog_ge_one hn_ge_one
  let L := Real.log (n : ℝ)
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hL_ge_one : (1 : ℝ) ≤ L := by simpa [L] using hlog_ge_one
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt L := by
    have h := Real.sqrt_le_sqrt hL_ge_one
    simpa using h
  have hfactor_nonneg : 0 ≤ (1 + ε) * Real.rpow (n : ℝ) ε := by
    have honeps_nonneg : 0 ≤ 1 + ε := by linarith
    exact mul_nonneg honeps_nonneg (Real.rpow_nonneg hn_nonneg _)
  have hsecond :
      24 * L ^ 2 ≤ (1 + ε) * Real.sqrt L * Real.rpow (n : ℝ) ε := by
    calc
      24 * L ^ 2 ≤ (1 + ε) * Real.rpow (n : ℝ) ε := by
        simpa [L] using hsecond_base
      _ = (1 : ℝ) * ((1 + ε) * Real.rpow (n : ℝ) ε) := by ring
      _ ≤ Real.sqrt L * ((1 + ε) * Real.rpow (n : ℝ) ε) :=
        mul_le_mul_of_nonneg_right hsqrt_ge_one hfactor_nonneg
      _ = (1 + ε) * Real.sqrt L * Real.rpow (n : ℝ) ε := by ring
  exact ⟨by simpa [C1, L] using hfirst, hsecond⟩
