import Tablet.Preamble
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Sort

open Finset Equiv Equiv.Perm BigOperators

-- [TABLET NODE: FinVectorHasSortedPermutation]

theorem FinVectorHasSortedPermutation :
    ∀ N : ℕ, ∀ c : Fin N → ℝ,
    ∃ x : Fin N → ℝ,
      (∃ σ : Perm (Fin N), ∀ i, x i = c (σ i)) ∧
      (∀ i j : Fin N, i.val ≤ j.val → x j ≤ x i) := by
-- BODY
  intro N c
  let c_neg := fun i => - c i
  let σ := Tuple.sort c_neg
  use fun i => c (σ i)
  constructor
  · use σ
    intro i
    rfl
  · intro i j hij
    have h_mono : Monotone (c_neg ∘ σ) := Tuple.monotone_sort c_neg
    have h_mono2 : c_neg (σ i) ≤ c_neg (σ j) := h_mono hij
    dsimp [c_neg] at h_mono2
    linarith
