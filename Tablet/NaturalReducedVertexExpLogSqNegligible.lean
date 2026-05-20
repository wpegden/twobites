import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch

open Filter Topology Set
open scoped Topology

-- [TABLET NODE: NaturalReducedVertexExpLogSqNegligible]

theorem NaturalReducedVertexExpLogSqNegligible (c : ℝ) (hc : 0 < c)
    (m : ℕ → ℕ) (hm : ∀ n, m n = TwoBiteNaturalReducedVertexCount n) :
    Tendsto (fun (n : ℕ) => (m n : ℝ) * Real.exp (-c * (Real.log (n : ℝ))^2))
      atTop (nhds 0) := by
-- BODY
  have tendsto_poly_atBot : Tendsto (fun (y : ℝ) => y - c * y^2) atTop atBot := by
    have h1 : Tendsto (fun y : ℝ => y^2) atTop atTop := tendsto_pow_atTop (by decide)
    have h2 : Tendsto (fun y : ℝ => y⁻¹ - c) atTop (nhds (0 - c)) := by
      exact tendsto_inv_atTop_zero.sub_const c
    have hc_neg : 0 - c < 0 := by linarith
    have h3 : Tendsto (fun (y : ℝ) => y^2 * (y⁻¹ - c)) atTop atBot :=
      Tendsto.atTop_mul_neg hc_neg h1 h2
    apply Tendsto.congr' _ h3
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with y hy
    have hy_ne : y ≠ 0 := ne_of_gt hy
    have h_inv : y * y⁻¹ = 1 := mul_inv_cancel₀ hy_ne
    calc
      y^2 * (y⁻¹ - c) = y * (y * y⁻¹) - c * y^2 := by ring
      _ = y * 1 - c * y^2 := by rw [h_inv]
      _ = y - c * y^2 := by ring
  have tendsto_exp_poly : Tendsto (fun (y : ℝ) => Real.exp (y - c * y^2)) atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp tendsto_poly_atBot
  have h_bound : ∀ᶠ n : ℕ in atTop,
      (m n : ℝ) * Real.exp (-c * (Real.log (n : ℝ))^2) ≤
        Real.exp (Real.log (n : ℝ) - c * (Real.log (n : ℝ))^2) := by
    filter_upwards [Ioi_mem_atTop 3] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by decide) hn
    have hn_cast : (3 : ℝ) < n := by exact_mod_cast hn
    have h_exp : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h_log : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      have : (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      rw [this]
      apply Real.log_le_log (by positivity)
      exact h_exp.le.trans hn_cast.le
    have h_m : (m n : ℝ) ≤ n := by
      rw [hm n]
      have h_nonneg : 0 ≤ TwoBiteReducedVertexCount n := by
        rw [TwoBiteReducedVertexCount, TwoBiteStretch]
        positivity
      have hfloor : (TwoBiteNaturalReducedVertexCount n : ℝ) ≤
          TwoBiteReducedVertexCount n := Nat.floor_le h_nonneg
      apply le_trans hfloor
      rw [TwoBiteReducedVertexCount, TwoBiteStretch]
      apply div_le_self hn_pos.le
      nlinarith [sq_nonneg (Real.log (n : ℝ))]
    calc
      (m n : ℝ) * Real.exp (-c * (Real.log (n : ℝ))^2)
          ≤ (n : ℝ) * Real.exp (-c * (Real.log (n : ℝ))^2) := by
            exact mul_le_mul_of_nonneg_right h_m (Real.exp_pos _).le
      _ = Real.exp (Real.log (n : ℝ)) * Real.exp (-c * (Real.log (n : ℝ))^2) := by
            rw [Real.exp_log hn_pos]
      _ = Real.exp (Real.log (n : ℝ) - c * (Real.log (n : ℝ))^2) := by
            rw [← Real.exp_add]
            ring_nf
  have h_nonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ (m n : ℝ) * Real.exp (-c * (Real.log (n : ℝ))^2) := by
    filter_upwards with n
    positivity
  have h_tendsto :
      Tendsto (fun (n : ℕ) => Real.exp (Real.log (n : ℝ) - c * (Real.log (n : ℝ))^2))
        atTop (nhds 0) := by
    exact tendsto_exp_poly.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_tendsto h_nonneg h_bound
