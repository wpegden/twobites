import Mathlib.Algebra.BigOperators.Ring.Finset
import Tablet.Preamble

-- [TABLET NODE: ProductWeightSumOne]

theorem ProductWeightSumOne :
    ∀ {α : Type} [Fintype α] [DecidableEq α]
      (r : ℕ) (q : α → ℝ),
      (∀ a : α, 0 ≤ q a) →
      Finset.univ.sum (fun a : α => q a) = 1 →
      Finset.univ.sum
          (fun ω : Fin r → α =>
            Finset.univ.prod (fun i : Fin r => q (ω i))) = 1 := by
-- BODY
  intro α _ _ r q _ hq_sum
  classical
  calc
    Finset.univ.sum
        (fun ω : Fin r → α =>
          Finset.univ.prod (fun i : Fin r => q (ω i)))
        = ∑ ω ∈ Fintype.piFinset (fun _ : Fin r => (Finset.univ : Finset α)),
            ∏ i : Fin r, q (ω i) := by
          rw [Fintype.piFinset_univ]
    _ = ∏ _i : Fin r, ∑ a ∈ (Finset.univ : Finset α), q a := by
          rw [Finset.sum_prod_piFinset]
    _ = 1 := by
          simp [hq_sum]
