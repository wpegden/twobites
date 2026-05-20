import Tablet.Preamble
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic

open Equiv Equiv.Perm

-- [TABLET NODE: MajorizationNonincreasingPermutationUnique]

theorem MajorizationNonincreasingPermutationUnique (N : ℕ) (u v : Fin N → ℝ)
    (hu : ∀ i j : Fin N, i.val ≤ j.val → u j ≤ u i)
    (hv : ∀ i j : Fin N, i.val ≤ j.val → v j ≤ v i)
    (h_perm : ∃ σ : Perm (Fin N), ∀ i, u i = v (σ i)) :
    ∀ i, u i = v i := by
-- BODY
  rcases h_perm with ⟨σ, h_σ⟩
  have hu_anti : Antitone u := fun i j h => hu i j h
  have hv_anti : Antitone v := fun i j h => hv i j h
  have h_eq : u = v ∘ ⇑σ := funext h_σ
  have hvσ_anti : Antitone (v ∘ ⇑σ) := by
    rw [← h_eq]
    exact hu_anti
  have H := Tuple.unique_antitone hvσ_anti (τ := 1) (by exact hv_anti)
  intro i
  have h_val : (v ∘ ⇑σ) i = (v ∘ ⇑(1 : Perm (Fin N))) i := congr_fun H i
  rw [h_σ i]
  exact h_val
