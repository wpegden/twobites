import Mathlib.Tactic
import Tablet.ChernoffFiberTailExponentsPositive
import Tablet.FiberAndDegreeLiftedSizeImageHypergeometricTail
import Tablet.WithinRelativeError

open Finset Classical Real

-- [TABLET NODE: FiberAndDegreeLiftedSizeFixedVertexTail]

theorem FiberAndDegreeLiftedSizeFixedVertexTail
    (n m q : ℕ) (K : Finset (Fin m × Fin m)) (p δ : ℝ)
    (hK : K.card = q) (h_support : n ≤ m * m)
    (hp0 : 0 ≤ p) (hδ_pos : 0 < δ) (hδ_le : δ ≤ (1 / 2 : ℝ))
    (hmean :
      WithinRelativeError δ (p * (n : ℝ))
        ((n : ℝ) * ((q : ℝ) / (m * m : ℝ)))) :
    let C : ℝ :=
      Real.exp ((-((1 - δ) * Real.log (1 - δ)) + -δ) *
        ((1 - δ) * (p * (n : ℝ)))) +
      Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) *
        ((1 - δ) * (p * (n : ℝ)))))
    ((Finset.univ.filter (fun φ : Fin n ↪ Fin m × Fin m =>
      ¬ WithinRelativeError (3 * δ) (p * (n : ℝ))
        (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ))).card : ℝ)
      ≤ C * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) := by
-- BODY
  classical
  let μ : ℝ := (n : ℝ) * ((q : ℝ) / (m * m : ℝ))
  let lowerExp : ℝ := δ + (1 - δ) * Real.log (1 - δ)
  let upperExp : ℝ := (1 + δ) * Real.log (1 + δ) - δ
  let target : ℝ := p * (n : ℝ)
  let lowerMean : ℝ := (1 - δ) * target
  let C : ℝ :=
    Real.exp ((-((1 - δ) * Real.log (1 - δ)) + -δ) * lowerMean) +
      Real.exp (-(upperExp * lowerMean))
  have htarget_nonneg : 0 ≤ target := by
    dsimp [target]
    positivity
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have h_one_sub_nonneg : 0 ≤ (1 - δ : ℝ) := by linarith
  have hc_pos := ChernoffFiberTailExponentsPositive δ hδ_pos hδ_le
  have hlowerExp_pos : 0 < lowerExp := by simpa [lowerExp] using hc_pos.2
  have hupperExp_pos : 0 < upperExp := by simpa [upperExp] using hc_pos.1
  have hμ_lower : lowerMean ≤ μ := by
    unfold WithinRelativeError at hmean
    have hlo := le_trans (neg_le_abs (μ - target)) (by simpa [μ, target] using hmean)
    dsimp [lowerMean]
    linarith
  let badSet : Finset (Fin n ↪ Fin m × Fin m) :=
    Finset.univ.filter (fun φ : Fin n ↪ Fin m × Fin m =>
      ¬ WithinRelativeError (3 * δ) target
        (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ))
  let tailSet : Finset (Fin n ↪ Fin m × Fin m) :=
    Finset.univ.filter (fun φ : Fin n ↪ Fin m × Fin m =>
      (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ) <
          (1 - δ) * μ ∨
        (1 + δ) * μ <
          (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ))
  have hbad_subset : badSet ⊆ tailSet := by
    intro φ hφ
    simp only [badSet, tailSet, Finset.mem_filter, Finset.mem_univ, true_and] at hφ ⊢
    by_contra hnot_tail
    push Not at hnot_tail
    have hhit_lower :
        (1 - δ) * μ ≤
          (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ) :=
      hnot_tail.1
    have hhit_upper :
          (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ) ≤
        (1 + δ) * μ :=
      hnot_tail.2
    have hμ_upper : μ ≤ (1 + δ) * target := by
      unfold WithinRelativeError at hmean
      have hup := le_trans (le_abs_self (μ - target)) (by simpa [μ, target] using hmean)
      linarith
    have hupper_target :
          (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ) ≤
        (1 + 3 * δ) * target := by
      have hcoef : (1 + δ) * (1 + δ) ≤ 1 + 3 * δ := by
        nlinarith [hδ_nonneg, hδ_le]
      calc
          (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ)
              ≤ (1 + δ) * μ := hhit_upper
          _ ≤ (1 + δ) * ((1 + δ) * target) := by
                exact mul_le_mul_of_nonneg_left hμ_upper (by linarith)
          _ = ((1 + δ) * (1 + δ)) * target := by ring
          _ ≤ (1 + 3 * δ) * target :=
                mul_le_mul_of_nonneg_right hcoef htarget_nonneg
    have hlower_target :
        (1 - 3 * δ) * target ≤
          (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ) := by
      have hcoef : 1 - 3 * δ ≤ (1 - δ) * (1 - δ) := by
        nlinarith [hδ_nonneg]
      calc
        (1 - 3 * δ) * target
            ≤ ((1 - δ) * (1 - δ)) * target :=
              mul_le_mul_of_nonneg_right hcoef htarget_nonneg
        _ = (1 - δ) * ((1 - δ) * target) := by ring
        _ ≤ (1 - δ) * μ :=
              mul_le_mul_of_nonneg_left hμ_lower h_one_sub_nonneg
        _ ≤ (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ) :=
              hhit_lower
    have hwre :
        WithinRelativeError (3 * δ) target
          (((((Finset.univ : Finset (Fin n)).image φ) ∩ K).card : ℕ) : ℝ) := by
      unfold WithinRelativeError
      rw [abs_le]
      constructor <;> linarith
    exact hφ hwre
  have hbad_le_tail : (badSet.card : ℝ) ≤ (tailSet.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hbad_subset
  have htail_count :
      (tailSet.card : ℝ) ≤
        (Real.exp ((-((1 - δ) * Real.log (1 - δ)) + -δ) * μ) +
          Real.exp (-(upperExp * μ))) *
          (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) := by
    have htail :=
      FiberAndDegreeLiftedSizeImageHypergeometricTail
        n m q K hK δ h_support hδ_pos hδ_le
    simpa [tailSet, μ, lowerExp, upperExp] using htail
  have hfactor :
      Real.exp ((-((1 - δ) * Real.log (1 - δ)) + -δ) * μ) +
          Real.exp (-(upperExp * μ)) ≤ C := by
    have hL :
        Real.exp ((-((1 - δ) * Real.log (1 - δ)) + -δ) * μ) ≤
          Real.exp ((-((1 - δ) * Real.log (1 - δ)) + -δ) * lowerMean) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hμ_lower hlowerExp_pos.le
      dsimp [lowerExp] at hmul
      nlinarith
    have hU :
        Real.exp (-(upperExp * μ)) ≤ Real.exp (-(upperExp * lowerMean)) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hμ_lower hupperExp_pos.le
      nlinarith
    exact add_le_add hL hU
  have htail_uniform :
      (tailSet.card : ℝ) ≤ C *
        (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) :=
    le_trans htail_count
      (mul_le_mul_of_nonneg_right hfactor (by positivity))
  simpa [badSet, C, lowerExp, upperExp, lowerMean, target, μ]
    using le_trans hbad_le_tail htail_uniform
