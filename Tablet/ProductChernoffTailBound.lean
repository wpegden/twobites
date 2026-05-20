import Mathlib.Algebra.BigOperators.Ring.Finset
import Tablet.ProductWeightSumOne

open scoped BigOperators
open Real

-- [TABLET NODE: ProductChernoffTailBound]

theorem ProductChernoffTailBound :
    ∀ {α : Type} [Fintype α] [DecidableEq α]
      (r : ℕ) (q : α → ℝ) (c t : ℝ) (Z : (Fin r → α) → ℝ),
      (∀ a : α, 0 ≤ q a) →
      Finset.univ.sum (fun a : α => q a) = 1 →
      0 < c → 0 ≤ t →
      (∀ lam : ℝ, 0 < lam →
        let weight : (Fin r → α) → ℝ :=
          fun ω => Finset.univ.prod (fun i : Fin r => q (ω i))
        let expectation : ℝ :=
          Finset.univ.sum (fun ω : Fin r → α => weight ω * Z ω)
        Finset.univ.sum
            (fun ω : Fin r → α =>
              weight ω * Real.exp (lam * (Z ω - expectation)))
          ≤ Real.exp ((r : ℝ) * lam ^ 2 * c ^ 2 / 8)) →
      let weight : (Fin r → α) → ℝ :=
        fun ω => Finset.univ.prod (fun i : Fin r => q (ω i))
      let expectation : ℝ :=
        Finset.univ.sum (fun ω : Fin r → α => weight ω * Z ω)
      (Finset.univ.filter
          (fun ω : Fin r → α => expectation + t ≤ Z ω)).sum weight
        ≤ Real.exp (-(2 * t ^ 2) / ((r : ℝ) * c ^ 2)) := by
-- BODY
  intro α _ _ r q c t Z hq hq_sum hc ht hmgf
  classical
  let weight : (Fin r → α) → ℝ := fun ω => Finset.univ.prod (fun i : Fin r => q (ω i))
  let expectation : ℝ := Finset.univ.sum (fun ω : Fin r → α => weight ω * Z ω)
  have hweight_nonneg (ω : Fin r → α) : 0 ≤ weight ω := by
    dsimp [weight]
    exact Finset.prod_nonneg fun i hi => hq (ω i)
  have htotal : Finset.univ.sum weight = 1 := by
    dsimp [weight]
    exact ProductWeightSumOne r q hq hq_sum
  have htail_le_one :
      (Finset.univ.filter (fun ω : Fin r → α => expectation + t ≤ Z ω)).sum weight ≤ 1 := by
    rw [← htotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intro x hxuniv hxnot; exact hweight_nonneg x)
  by_cases ht0 : t = 0
  · subst t
    simpa using htail_le_one
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have markov (lam : ℝ) (hlam : 0 < lam) :
      (Finset.univ.filter (fun ω : Fin r → α => expectation + t ≤ Z ω)).sum weight
        ≤ Real.exp (-lam * t + (r : ℝ) * lam ^ 2 * c ^ 2 / 8) := by
    calc
      (Finset.univ.filter (fun ω : Fin r → α => expectation + t ≤ Z ω)).sum weight
          ≤ (Finset.univ.filter (fun ω : Fin r → α => expectation + t ≤ Z ω)).sum
              (fun ω => Real.exp (-lam * t) *
                (weight ω * Real.exp (lam * (Z ω - expectation)))) := by
            refine Finset.sum_le_sum ?_
            intro ω hω
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
            have htail : t ≤ Z ω - expectation := by linarith
            have hexp_ge : 1 ≤ Real.exp (lam * (Z ω - expectation - t)) := by
              rw [one_le_exp_iff]
              nlinarith [mul_nonneg hlam.le (sub_nonneg.mpr htail)]
            have hfactor :
                1 ≤ Real.exp (-lam * t) * Real.exp (lam * (Z ω - expectation)) := by
              calc
                1 ≤ Real.exp (lam * (Z ω - expectation - t)) := hexp_ge
                _ = Real.exp (-lam * t) * Real.exp (lam * (Z ω - expectation)) := by
                  rw [← Real.exp_add]
                  congr 1
                  ring
            calc
              weight ω = weight ω * 1 := by ring
              _ ≤ weight ω *
                    (Real.exp (-lam * t) * Real.exp (lam * (Z ω - expectation))) := by
                    exact mul_le_mul_of_nonneg_left hfactor (hweight_nonneg ω)
              _ = Real.exp (-lam * t) *
                    (weight ω * Real.exp (lam * (Z ω - expectation))) := by ring
      _ ≤ (Finset.univ.sum
              (fun ω : Fin r → α => Real.exp (-lam * t) *
                (weight ω * Real.exp (lam * (Z ω - expectation))))) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro ω hωuniv hωnot
            exact mul_nonneg (Real.exp_pos _).le
              (mul_nonneg (hweight_nonneg ω) (Real.exp_pos _).le)
      _ = Real.exp (-lam * t) *
            Finset.univ.sum
              (fun ω : Fin r → α => weight ω * Real.exp (lam * (Z ω - expectation))) := by
            rw [Finset.mul_sum]
      _ ≤ Real.exp (-lam * t) *
            Real.exp ((r : ℝ) * lam ^ 2 * c ^ 2 / 8) := by
            exact mul_le_mul_of_nonneg_left (hmgf lam hlam) (Real.exp_pos _).le
      _ = Real.exp (-lam * t + (r : ℝ) * lam ^ 2 * c ^ 2 / 8) := by
            rw [Real.exp_add]
  by_cases hr0 : r = 0
  · have hbound := markov 1 (by norm_num)
    calc
      (Finset.univ.filter (fun ω : Fin r → α => expectation + t ≤ Z ω)).sum weight
          ≤ Real.exp (-(1 : ℝ) * t + (r : ℝ) * (1 : ℝ) ^ 2 * c ^ 2 / 8) := hbound
      _ ≤ 1 := by
        rw [hr0]
        simp only [Nat.cast_zero, zero_mul, zero_div, add_zero, one_pow, neg_mul, one_mul]
        exact Real.exp_le_one_iff.mpr (by linarith)
      _ = Real.exp (-(2 * t ^ 2) / ((r : ℝ) * c ^ 2)) := by
        rw [hr0]
        simp
  · have hrpos_nat : 0 < r := Nat.pos_of_ne_zero hr0
    have hden_pos : 0 < (r : ℝ) * c ^ 2 := by
      positivity
    let lam : ℝ := 4 * t / ((r : ℝ) * c ^ 2)
    have hlam : 0 < lam := by
      dsimp [lam]
      positivity
    have hbound := markov lam hlam
    calc
      (Finset.univ.filter (fun ω : Fin r → α => expectation + t ≤ Z ω)).sum weight
          ≤ Real.exp (-lam * t + (r : ℝ) * lam ^ 2 * c ^ 2 / 8) := hbound
      _ = Real.exp (-(2 * t ^ 2) / ((r : ℝ) * c ^ 2)) := by
        congr 1
        dsimp [lam]
        field_simp [hden_pos.ne']
        ring
