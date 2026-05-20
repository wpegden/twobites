import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

open Filter Topology

-- [TABLET NODE: ProjectionSizeAnalyticErrorAbsorption]

theorem ProjectionSizeAnalyticErrorAbsorption (δ ε : ℝ) (hδ : 0 < δ) (_hε : 0 < ε) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      let L := Real.log (n : ℝ)
      1 ≤ L ∧ 3 + 2 * ((5/2 : ℝ) * Real.log L + Real.log (4 * (1 + ε))) ≤ δ * L := by
-- BODY
  have t_cast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp t_cast
  have hloglog_atTop : Tendsto (fun L : ℝ => Real.log L) atTop atTop := Real.tendsto_log_atTop
  
  have he1 : ∀ᶠ L : ℝ in atTop, 1 ≤ L := eventually_ge_atTop 1
  have ho : (fun L : ℝ => Real.log L) =o[atTop] (fun L : ℝ => L) := Real.isLittleO_log_id_atTop
  have h_bound1 := ho.bound (by positivity : 0 < δ / 10)
  have h_bound2 : ∀ᶠ L : ℝ in atTop, 3 + 2 * Real.log (4 * (1 + ε)) ≤ (δ / 2) * L := by
    have h_pos : 0 < δ / 2 := by positivity
    have h_tendsto_mul : Tendsto (fun L : ℝ => (δ / 2) * L) atTop atTop :=
      Tendsto.const_mul_atTop h_pos tendsto_id
    exact h_tendsto_mul.eventually (eventually_ge_atTop (3 + 2 * Real.log (4 * (1 + ε))))
    
  have h_all_L : ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 5 * Real.log L ≤ (δ / 2) * L ∧ 3 + 2 * Real.log (4 * (1 + ε)) ≤ (δ / 2) * L := by
    filter_upwards [he1, h_bound1, h_bound2, eventually_gt_atTop (1:ℝ)] with L hL1 hb1 hb2 hL_gt1
    refine ⟨hL1, ?_, hb2⟩
    dsimp at hb1
    have hlog_pos : 0 < Real.log L := Real.log_pos hL_gt1
    have hL_pos : 0 < L := by linarith
    rw [abs_of_pos hlog_pos, abs_of_pos hL_pos] at hb1
    calc 5 * Real.log L ≤ 5 * ((δ / 10) * L) := mul_le_mul_of_nonneg_left hb1 (by norm_num)
      _ = (δ / 2) * L := by ring
  
  have h_all_n : ∀ᶠ n : ℕ in atTop,
    let L := Real.log (n : ℝ)
    1 ≤ L ∧ 5 * Real.log L ≤ (δ / 2) * L ∧ 3 + 2 * Real.log (4 * (1 + ε)) ≤ (δ / 2) * L :=
    hlog_atTop.eventually h_all_L

  obtain ⟨n0, hn0⟩ := eventually_atTop.mp h_all_n
  use n0
  intro n hn
  have hn_props := hn0 n hn
  have h1 := hn_props.1
  have h2 := hn_props.2.1
  have h3 := hn_props.2.2
  refine ⟨h1, ?_⟩
  calc 3 + 2 * ((5 / 2 : ℝ) * Real.log (Real.log ↑n) + Real.log (4 * (1 + ε)))
    _ = 5 * Real.log (Real.log ↑n) + (3 + 2 * Real.log (4 * (1 + ε))) := by ring
    _ ≤ (δ / 2) * Real.log (n : ℝ) + (δ / 2) * Real.log (n : ℝ) := add_le_add h2 h3
    _ = δ * Real.log (n : ℝ) := by ring
