import Tablet.Preamble
import Mathlib.Data.Fintype.Perm
import Tablet.MajorizationAdjacentInversionSorting
import Tablet.MajorizationNonincreasingPermutationUnique

open Finset Real Equiv Equiv.Perm

-- [TABLET NODE: MajorizationResortingDistance]

theorem MajorizationResortingDistance :
    ∀ N : ℕ, ∀ b y y_down : Fin N → ℝ,
    (∀ i j : Fin N, i.val ≤ j.val → b j ≤ b i) →
    (∀ i j : Fin N, i.val ≤ j.val → y_down j ≤ y_down i) →
    (∃ σ : Perm (Fin N), ∀ i, y_down i = y (σ i)) →
    ∑ i, |y_down i - b i| ≤ ∑ i, |y i - b i| := by
-- BODY
  intro N b y y_down hb hy_down h_perm
  rcases MajorizationAdjacentInversionSorting N b y hb with ⟨u_star, h_perm_u, hu_star, hu_dist⟩
  have h_eq : ∀ i, u_star i = y_down i := by
    apply MajorizationNonincreasingPermutationUnique N u_star y_down hu_star hy_down
    rcases h_perm with ⟨σ, h_σ⟩
    rcases h_perm_u with ⟨τ, h_τ⟩
    use σ⁻¹ * τ
    intro i
    have h1 := h_τ i
    have h2 := h_σ (σ⁻¹ (τ i))
    dsimp at h2
    rw [Equiv.apply_symm_apply] at h2
    rw [h1]
    exact h2.symm

  have h_eq_sum : ∑ i, |y_down i - b i| = ∑ i, |u_star i - b i| := by
    apply sum_congr rfl
    intro x _
    rw [h_eq x]
  rw [h_eq_sum]
  exact hu_dist
