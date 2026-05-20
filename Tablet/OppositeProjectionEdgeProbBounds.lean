import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Order.Basic
import Tablet.TwoBiteEdgeProbability

open Filter Topology Set

-- [TABLET NODE: OppositeProjectionEdgeProbBounds]

theorem OppositeProjectionEdgeProbBounds :
    ∀ᶠ n in Filter.atTop,
      0 ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n ∧
        TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ 1 := by
-- BODY
  have h_tendsto : Tendsto (fun (n:ℕ) => Real.log (n:ℝ) / (n:ℝ)) atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simp only [pow_one, one_mul, add_zero] at h
    exact h.comp tendsto_natCast_atTop_atTop

  have h_log_pos : ∀ᶠ n:ℕ in atTop, 0 ≤ Real.log (n:ℝ) := by
    have : ∀ᶠ n:ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    filter_upwards [this] with n hn
    apply Real.log_nonneg
    exact Nat.one_le_cast.mpr hn

  have h_leq_4 : ∀ᶠ n:ℕ in atTop, Real.log (n:ℝ) / (n:ℝ) ≤ 4 := by
    have h_nhds : Iic (4:ℝ) ∈ nhds 0 := Iic_mem_nhds (by norm_num)
    exact h_tendsto h_nhds

  have h_n_pos : ∀ᶠ n:ℕ in atTop, 0 < (n:ℝ) := by
    have : ∀ᶠ n:ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    filter_upwards [this] with n hn
    exact Nat.cast_pos.mpr (by linarith)

  filter_upwards [h_log_pos, h_leq_4, h_n_pos] with n _ hleq4 _
  unfold TwoBiteEdgeProbability
  constructor
  · apply mul_nonneg (by norm_num)
    apply Real.sqrt_nonneg
  · calc (1/2:ℝ) * Real.sqrt (Real.log n / n)
      _ ≤ (1/2:ℝ) * Real.sqrt 4 := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.sqrt_le_sqrt hleq4
        · norm_num
      _ = 1 := by
        have : Real.sqrt 4 = 2 := by
          have : (4:ℝ) = 2^2 := by norm_num
          rw [this, Real.sqrt_sq (by norm_num)]
        rw [this]
        norm_num