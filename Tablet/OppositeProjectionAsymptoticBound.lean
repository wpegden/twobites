import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Complex.ExponentialBounds
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch

open Filter Topology Set

-- [TABLET NODE: OppositeProjectionAsymptoticBound]

theorem OppositeProjectionAsymptoticBound (c : ℝ) (hc : 0 < c)
    (m : ℕ → ℕ) (hm : ∀ n, m n = TwoBiteNaturalReducedVertexCount n) :
    Tendsto (fun (n : ℕ) => (m n : ℝ)^2 * Real.exp (-c * (Real.log (n : ℝ))^3)) atTop (nhds 0) := by
-- BODY
  have tendsto_poly_atBot : Tendsto (fun (y : ℝ) => 2 * y - c * y^3) atTop atBot := by
    have h1 : Tendsto (fun y : ℝ => y^3) atTop atTop := tendsto_pow_atTop (by decide)
    have h2 : Tendsto (fun y : ℝ => 2 * y⁻¹^2 - c) atTop (nhds (2 * 0^2 - c)) := by
      apply Tendsto.sub_const
      apply Tendsto.const_mul
      exact Filter.Tendsto.pow tendsto_inv_atTop_zero 2
    have hc_neg : 2 * 0^2 - c < 0 := by linarith
    have h3 : Tendsto (fun (y : ℝ) => y^3 * (2 * y⁻¹^2 - c)) atTop atBot :=
      Tendsto.atTop_mul_neg hc_neg h1 h2
    apply Tendsto.congr' _ h3
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with y hy
    have hy_ne : y ≠ 0 := ne_of_gt hy
    have h_inv : y * y⁻¹ = 1 := mul_inv_cancel₀ hy_ne
    calc y^3 * (2 * y⁻¹^2 - c)
      _ = 2 * y * (y * y⁻¹) * (y * y⁻¹) - c * y^3 := by ring
      _ = 2 * y * 1 * 1 - c * y^3 := by rw [h_inv]
      _ = 2 * y - c * y^3 := by ring
  have tendsto_exp_poly : Tendsto (fun (y : ℝ) => Real.exp (2 * y - c * y^3)) atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp tendsto_poly_atBot

  have h_bound : ∀ᶠ n : ℕ in atTop, (m n : ℝ)^2 * Real.exp (-c * (Real.log (n : ℝ))^3) ≤ Real.exp (2 * Real.log n - c * (Real.log n)^3) := by
    filter_upwards [Ioi_mem_atTop 3] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by decide) hn
    have hn_cast : (3 : ℝ) < n := by exact_mod_cast hn
    have h_exp : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h_log : (1 : ℝ) ≤ Real.log n := by
      have : (1 : ℝ) = Real.log (Real.exp 1) := Real.log_exp 1 |>.symm
      rw [this]
      apply Real.log_le_log (by positivity)
      exact h_exp.le.trans hn_cast.le
    have h_m : (m n : ℝ) ≤ n := by
      rw [hm]
      have h_nonneg : 0 ≤ TwoBiteReducedVertexCount n := by
        rw [TwoBiteReducedVertexCount, TwoBiteStretch]
        positivity
      have : (TwoBiteNaturalReducedVertexCount n : ℝ) ≤ TwoBiteReducedVertexCount n := Nat.floor_le h_nonneg
      apply le_trans this
      rw [TwoBiteReducedVertexCount, TwoBiteStretch]
      apply div_le_self hn_pos.le
      nlinarith
    calc (m n : ℝ)^2 * Real.exp (-c * (Real.log n)^3)
      _ ≤ (n : ℝ)^2 * Real.exp (-c * (Real.log n)^3) := by
        gcongr
      _ = (Real.exp (Real.log n))^2 * Real.exp (-c * (Real.log n)^3) := by
        rw [Real.exp_log hn_pos]
      _ = Real.exp (2 * Real.log n) * Real.exp (-c * (Real.log n)^3) := by
        rw [← Real.exp_nat_mul]
        congr 1
      _ = Real.exp (2 * Real.log n - c * (Real.log n)^3) := by
        rw [← Real.exp_add]
        ring_nf
  have h_nonneg : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (m n : ℝ)^2 * Real.exp (-c * (Real.log (n : ℝ))^3) := by
    filter_upwards with n
    positivity
  have h_tendsto : Tendsto (fun (n : ℕ) => Real.exp (2 * Real.log n - c * (Real.log n)^3)) atTop (nhds 0) := by
    apply tendsto_exp_poly.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tendsto h_nonneg h_bound
