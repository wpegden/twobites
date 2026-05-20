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

-- [TABLET NODE: NaturalDegreeExponentialEnvelopeNegligible]

theorem NaturalDegreeExponentialEnvelopeNegligible :
    ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto
        (fun n : ℕ =>
          let M : ℝ := (TwoBiteNaturalReducedVertexCount n : ℝ)
          let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
          let c : ℝ := ε ^ 2 / 100
          M * (Real.exp (-(c * p * M)) + Real.exp (-(c * p * M))))
        Filter.atTop (nhds 0) := by
-- BODY
  intro ε hε
  let c : ℝ := ε ^ 2 / 100
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hdom :
      ∀ᶠ n : ℕ in atTop,
        c⁻¹ * (Real.log (n : ℝ)) ^ 3 ≤
          TwoBiteEdgeProbability (1 / 2 : ℝ) n *
            (TwoBiteNaturalReducedVertexCount n : ℝ) :=
    NaturalDegreeMassDominatesLogCube c⁻¹ (inv_pos.mpr hc_pos)
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have htend_poly_atBot :
      Tendsto (fun y : ℝ => Real.log 2 + y - y ^ 3) atTop atBot := by
    have h1 : Tendsto (fun y : ℝ => y ^ 3) atTop atTop :=
      tendsto_pow_atTop (by decide)
    have h2 : Tendsto (fun y : ℝ => (Real.log 2) * y⁻¹ ^ 3 + y⁻¹ ^ 2 - 1)
        atTop (nhds ((Real.log 2) * 0 ^ 3 + 0 ^ 2 - 1)) := by
      apply Tendsto.sub_const
      apply Tendsto.add
      · exact (tendsto_const_nhds.mul (Filter.Tendsto.pow tendsto_inv_atTop_zero 3))
      · exact Filter.Tendsto.pow tendsto_inv_atTop_zero 2
    have hneg : (Real.log 2) * 0 ^ 3 + 0 ^ 2 - 1 < 0 := by norm_num
    have h3 : Tendsto
        (fun y : ℝ => y ^ 3 * ((Real.log 2) * y⁻¹ ^ 3 + y⁻¹ ^ 2 - 1))
        atTop atBot :=
      Tendsto.atTop_mul_neg hneg h1 h2
    apply Tendsto.congr' _ h3
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with y hy
    have hy_ne : y ≠ 0 := ne_of_gt hy
    have h_inv : y * y⁻¹ = 1 := mul_inv_cancel₀ hy_ne
    calc
      y ^ 3 * ((Real.log 2) * y⁻¹ ^ 3 + y⁻¹ ^ 2 - 1)
          = Real.log 2 * (y * y⁻¹) ^ 3 + y * (y * y⁻¹) ^ 2 - y ^ 3 := by
            ring
      _ = Real.log 2 + y - y ^ 3 := by
            rw [h_inv]
            ring
  have htend_exp :
      Tendsto (fun y : ℝ => Real.exp (Real.log 2 + y - y ^ 3)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp htend_poly_atBot
  have htend_bound :
      Tendsto
        (fun n : ℕ =>
          Real.exp (Real.log 2 + Real.log (n : ℝ) -
            (Real.log (n : ℝ)) ^ 3))
        atTop (nhds 0) :=
    htend_exp.comp hlog_atTop
  have hnonneg :
      ∀ᶠ n : ℕ in atTop,
        0 ≤
          (let M : ℝ := (TwoBiteNaturalReducedVertexCount n : ℝ)
           let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
           let c : ℝ := ε ^ 2 / 100
           M * (Real.exp (-(c * p * M)) + Real.exp (-(c * p * M)))) := by
    filter_upwards with n
    positivity
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        (let M : ℝ := (TwoBiteNaturalReducedVertexCount n : ℝ)
         let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
         let c : ℝ := ε ^ 2 / 100
         M * (Real.exp (-(c * p * M)) + Real.exp (-(c * p * M)))) ≤
          Real.exp (Real.log 2 + Real.log (n : ℝ) -
            (Real.log (n : ℝ)) ^ 3) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ), hdom] with n hn hdom_n
    let M : ℝ := (TwoBiteNaturalReducedVertexCount n : ℝ)
    let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
    let L : ℝ := Real.log (n : ℝ)
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hn
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hL_ge_one : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      have hn_cast : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have h_exp : Real.exp 1 < 3 := Real.exp_one_lt_three
      have : (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      rw [this]
      exact Real.log_le_log (by positivity) (le_trans h_exp.le hn_cast)
    have hM_nonneg : 0 ≤ M := Nat.cast_nonneg _
    have hM_le_n : M ≤ (n : ℝ) := by
      dsimp [M]
      have h_nonneg : 0 ≤ TwoBiteReducedVertexCount n := by
        rw [TwoBiteReducedVertexCount, TwoBiteStretch]
        positivity
      have hfloor : (TwoBiteNaturalReducedVertexCount n : ℝ) ≤
          TwoBiteReducedVertexCount n := Nat.floor_le h_nonneg
      apply le_trans hfloor
      rw [TwoBiteReducedVertexCount, TwoBiteStretch]
      apply div_le_self hn_pos.le
      nlinarith
    have hc_dom : L ^ 3 ≤ c * p * M := by
      have hmul := mul_le_mul_of_nonneg_left hdom_n hc_pos.le
      have hcancel : c * (c⁻¹ * L ^ 3) = L ^ 3 := by
        field_simp [hc_pos.ne']
      calc
        L ^ 3 = c * (c⁻¹ * L ^ 3) := hcancel.symm
        _ ≤ c * (p * M) := by simpa [p, M, L, mul_assoc] using hmul
        _ = c * p * M := by ring
    have hexp_le : Real.exp (-(c * p * M)) ≤ Real.exp (-(L ^ 3)) := by
      exact Real.exp_le_exp.mpr (by linarith)
    have htail_nonneg : 0 ≤ Real.exp (-(c * p * M)) := (Real.exp_pos _).le
    have hsum_le :
        Real.exp (-(c * p * M)) + Real.exp (-(c * p * M)) ≤
          2 * Real.exp (-(L ^ 3)) := by
      nlinarith
    have hleft_le :
        M * (Real.exp (-(c * p * M)) + Real.exp (-(c * p * M))) ≤
          (n : ℝ) * (2 * Real.exp (-(L ^ 3))) := by
      exact mul_le_mul hM_le_n hsum_le
        (add_nonneg htail_nonneg htail_nonneg) hn_nonneg
    calc
      (let M : ℝ := (TwoBiteNaturalReducedVertexCount n : ℝ)
       let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
       let c : ℝ := ε ^ 2 / 100
       M * (Real.exp (-(c * p * M)) + Real.exp (-(c * p * M))))
          = M * (Real.exp (-(c * p * M)) + Real.exp (-(c * p * M))) := by
            simp [M, p, c]
      _ ≤ (n : ℝ) * (2 * Real.exp (-(L ^ 3))) := hleft_le
      _ = Real.exp (Real.log 2 + Real.log (n : ℝ) -
            (Real.log (n : ℝ)) ^ 3) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          Real.exp_log hn_pos]
        simp [L]
        rw [Real.exp_neg]
        ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    htend_bound hnonneg hbound
