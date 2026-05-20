import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic
import Tablet.NaturalDegreeMassDominatesLogCube
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch

open Filter
open scoped Topology

-- [TABLET NODE: NaturalReducedVertexEdgeMassNegligible]

theorem NaturalReducedVertexEdgeMassNegligible (c : ℝ) (hc : 0 < c)
    (m : ℕ → ℕ) (hm : ∀ n, m n = TwoBiteNaturalReducedVertexCount n) :
    Filter.Tendsto
      (fun n : ℕ =>
        (m n : ℝ) *
          Real.exp (-(c * (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)))))
      Filter.atTop (nhds 0) := by
-- BODY
  have hdom :
      ∀ᶠ n : ℕ in atTop,
        c⁻¹ * (Real.log (n : ℝ)) ^ 3 ≤
          TwoBiteEdgeProbability (1 / 2 : ℝ) n *
            (TwoBiteNaturalReducedVertexCount n : ℝ) :=
    NaturalDegreeMassDominatesLogCube c⁻¹ (inv_pos.mpr hc)
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have htend_poly_atBot :
      Tendsto (fun y : ℝ => y - y ^ 3) atTop atBot := by
    have h1 : Tendsto (fun y : ℝ => y ^ 3) atTop atTop :=
      tendsto_pow_atTop (by decide)
    have h2 : Tendsto (fun y : ℝ => y⁻¹ ^ 2 - 1)
        atTop (nhds (0 ^ 2 - 1)) := by
      exact (Filter.Tendsto.pow tendsto_inv_atTop_zero 2).sub_const 1
    have hneg : 0 ^ 2 - (1 : ℝ) < 0 := by norm_num
    have h3 : Tendsto (fun y : ℝ => y ^ 3 * (y⁻¹ ^ 2 - 1))
        atTop atBot :=
      Tendsto.atTop_mul_neg hneg h1 h2
    apply Tendsto.congr' _ h3
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with y hy
    have hy_ne : y ≠ 0 := ne_of_gt hy
    have h_inv : y * y⁻¹ = 1 := mul_inv_cancel₀ hy_ne
    calc
      y ^ 3 * (y⁻¹ ^ 2 - 1) = y * (y * y⁻¹) ^ 2 - y ^ 3 := by
        ring
      _ = y - y ^ 3 := by
        rw [h_inv]
        ring
  have htend_exp :
      Tendsto (fun y : ℝ => Real.exp (y - y ^ 3)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp htend_poly_atBot
  have htend_bound :
      Tendsto
        (fun n : ℕ =>
          Real.exp (Real.log (n : ℝ) - (Real.log (n : ℝ)) ^ 3))
        atTop (nhds 0) :=
    htend_exp.comp hlog_atTop
  have hnonneg :
      ∀ᶠ n : ℕ in atTop,
        0 ≤
          (m n : ℝ) *
            Real.exp (-(c * (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)))) := by
    filter_upwards with n
    positivity
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        (m n : ℝ) *
            Real.exp (-(c * (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)))) ≤
          Real.exp (Real.log (n : ℝ) - (Real.log (n : ℝ)) ^ 3) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ), hdom] with n hn hdom_n
    let M : ℝ := (m n : ℝ)
    let Mnat : ℝ := (TwoBiteNaturalReducedVertexCount n : ℝ)
    let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
    let L : ℝ := Real.log (n : ℝ)
    have hn_pos : (0 : ℝ) < n := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hn
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hL_ge_one : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      have hn_cast : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have h_exp : Real.exp 1 < 3 := Real.exp_one_lt_three
      have : (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      rw [this]
      exact Real.log_le_log (by positivity) (le_trans h_exp.le hn_cast)
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      positivity
    have hM_le_n : M ≤ (n : ℝ) := by
      dsimp [M]
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
    have hp_nonneg : 0 ≤ p := by
      dsimp [p, TwoBiteEdgeProbability]
      positivity
    have hc_dom_M : L ^ 3 ≤ c * p * Mnat := by
      have hmul := mul_le_mul_of_nonneg_left hdom_n hc.le
      have hcancel : c * (c⁻¹ * L ^ 3) = L ^ 3 := by
        field_simp [hc.ne']
      calc
        L ^ 3 = c * (c⁻¹ * L ^ 3) := hcancel.symm
        _ ≤ c * (p * Mnat) := by simpa [p, Mnat, L, mul_assoc] using hmul
        _ = c * p * Mnat := by ring
    have hc_dom_n : L ^ 3 ≤ c * (p * (n : ℝ)) := by
      have hMnat_le_n : Mnat ≤ (n : ℝ) := by
        dsimp [Mnat]
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
        L ^ 3 ≤ c * p * Mnat := hc_dom_M
        _ = (c * p) * Mnat := by ring
        _ ≤ (c * p) * (n : ℝ) := by
          exact mul_le_mul_of_nonneg_left hMnat_le_n (mul_nonneg hc.le hp_nonneg)
        _ = c * (p * (n : ℝ)) := by ring
    have hexp_le :
        Real.exp (-(c * (p * (n : ℝ)))) ≤ Real.exp (-(L ^ 3)) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have hleft_le :
        M * Real.exp (-(c * (p * (n : ℝ)))) ≤
          (n : ℝ) * Real.exp (-(L ^ 3)) := by
      exact mul_le_mul hM_le_n hexp_le (Real.exp_pos _).le hn_nonneg
    calc
      (m n : ℝ) *
          Real.exp (-(c * (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ))))
          = M * Real.exp (-(c * (p * (n : ℝ)))) := by
            simp [M, p]
      _ ≤ (n : ℝ) * Real.exp (-(L ^ 3)) := hleft_le
      _ = Real.exp (Real.log (n : ℝ) - (Real.log (n : ℝ)) ^ 3) := by
        rw [Real.exp_sub, Real.exp_log hn_pos]
        simp [L]
        rw [Real.exp_neg]
        ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    htend_bound hnonneg hbound
