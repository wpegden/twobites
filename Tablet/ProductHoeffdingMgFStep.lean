import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Tablet.Preamble

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Real

-- [TABLET NODE: ProductHoeffdingMgFStep]

theorem ProductHoeffdingMgFStep :
    ∀ {α : Type} [Fintype α] [DecidableEq α]
      (q : α → ℝ) (X : α → ℝ) (a b lam : ℝ),
      (∀ x : α, 0 ≤ q x) →
      Finset.univ.sum (fun x : α => q x) = 1 →
      a ≤ b →
      (∀ x : α, a ≤ X x ∧ X x ≤ b) →
      Finset.univ.sum (fun x : α => q x * X x) = 0 →
      0 ≤ lam →
      Finset.univ.sum (fun x : α => q x * Real.exp (lam * X x))
        ≤ Real.exp (lam ^ 2 * (b - a) ^ 2 / 8) := by
-- BODY
  intro α _ _ q X a b lam hq hq_sum hab hX hmean hlam
  classical
  letI : MeasurableSpace α := ⊤
  have hq_enn : (∑ x : α, ENNReal.ofReal (q x)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · simp [hq_sum]
    · intro x hx
      exact hq x
  let p : PMF α := PMF.ofFintype (fun x : α => ENNReal.ofReal (q x)) hq_enn
  have hp_toReal (x : α) : (p x).toReal = q x := by
    simp [p, ENNReal.toReal_ofReal (hq x)]
  have h_int_zero : (∫ x, X x ∂p.toMeasure) = 0 := by
    rw [PMF.integral_eq_sum]
    calc
      (∑ x : α, (p x).toReal • X x) = ∑ x : α, q x * X x := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simp [hp_toReal x]
      _ = 0 := hmean
  have h_subG :
      HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) p.toMeasure := by
    refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero ?_ ?_ h_int_zero
    · exact (measurable_from_top : Measurable X).aemeasurable
    · exact Filter.Eventually.of_forall fun x => hX x
  have hmgf := h_subG.mgf_le lam
  have hmgf_sum :
      Finset.univ.sum (fun x : α => q x * Real.exp (lam * X x))
        = mgf X p.toMeasure lam := by
    rw [mgf, PMF.integral_eq_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp [hp_toReal x]
  rw [hmgf_sum]
  refine hmgf.trans_eq ?_
  congr 1
  have hnorm : ((‖b - a‖₊ : ℝ) / 2) ^ 2 = (b - a) ^ 2 / 4 := by
    have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    rw [coe_nnnorm, Real.norm_of_nonneg hba]
    ring
  calc
    (↑(((‖b - a‖₊ / 2) ^ 2) : NNReal) : ℝ) * lam ^ 2 / 2
        = ((↑(‖b - a‖₊ : NNReal) : ℝ) / 2) ^ 2 * lam ^ 2 / 2 := by
          norm_num [NNReal.coe_pow, NNReal.coe_div]
    _ = lam ^ 2 * (b - a) ^ 2 / 8 := by
      rw [hnorm]
      ring
