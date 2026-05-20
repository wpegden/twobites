import Tablet.ProductChernoffTailBound
import Tablet.ProductMgfBound

-- [TABLET NODE: BoundedDifferencesProduct]

theorem BoundedDifferencesProduct :
    ∀ {α : Type} [Fintype α] [DecidableEq α]
      (r : ℕ) (q : α → ℝ) (c t : ℝ) (Z : (Fin r → α) → ℝ),
      (∀ a : α, 0 ≤ q a) →
      Finset.univ.sum (fun a : α => q a) = 1 →
      0 < c → 0 ≤ t →
      (∀ (i : Fin r) (ω ω' : Fin r → α),
        (∀ j : Fin r, j ≠ i → ω j = ω' j) →
          |Z ω - Z ω'| ≤ c) →
      let weight : (Fin r → α) → ℝ :=
        fun ω => Finset.univ.prod (fun i : Fin r => q (ω i))
      let expectation : ℝ :=
        Finset.univ.sum (fun ω : Fin r → α => weight ω * Z ω)
      (Finset.univ.filter
          (fun ω : Fin r → α => expectation + t ≤ Z ω)).sum weight
        ≤ Real.exp (-(2 * t ^ 2) / ((r : ℝ) * c ^ 2)) := by
-- BODY
  intro α _ _ r q c t Z hq hq_sum hc ht hdiff
  exact ProductChernoffTailBound r q c t Z hq hq_sum hc ht (by
    intro lam hlam
    exact ProductMgfBound r q c Z hq hq_sum hc hdiff lam (le_of_lt hlam))
