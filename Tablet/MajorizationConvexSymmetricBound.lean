import Tablet.Preamble
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Tablet.MajorizationFiniteDescent

open Finset Real Equiv Equiv.Perm BigOperators

-- [TABLET NODE: MajorizationConvexSymmetricBound]

theorem MajorizationConvexSymmetricBound :
    ∀ N : ℕ, ∀ c b : Fin N → ℝ,
    (∑ i, c i) = (∑ i, b i) →
    (∀ i j : Fin N, i.val ≤ j.val → b j ≤ b i) →
    (∃ x : Fin N → ℝ,
      (∃ σ : Perm (Fin N), ∀ i, x i = c (σ i)) ∧
      (∀ i j : Fin N, i.val ≤ j.val → x j ≤ x i) ∧
      (∀ r : ℕ, r ≤ N →
        ∑ i ∈ univ.filter (·.val < r), b i ≤ ∑ i ∈ univ.filter (·.val < r), x i)) →
    (∀ i : Fin N, ∃ k : ℕ, c i = k) →
    (∀ i : Fin N, ∃ k : ℕ, b i = k) →
    ∀ h : (Fin N → ℝ) → ℝ,
    (∀ y z : Fin N → ℝ, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      h (fun i => (1 - θ) * y i + θ * z i) ≤ (1 - θ) * h y + θ * h z) →
    (∀ y : Fin N → ℝ, ∀ σ : Perm (Fin N), h (fun i => y (σ i)) = h y) →
    h b ≤ h c := by
-- BODY
  intro N c b h_sum h_b_desc ⟨x, ⟨σ, h_x_perm⟩, h_x_desc, h_prefix⟩ h_c_int h_b_int h h_conv h_symm
  have h_x_int : ∀ i, ∃ k : ℕ, x i = k := by
    intro i
    rw [h_x_perm i]
    apply h_c_int
  have h_x_sum : (∑ i, x i) = (∑ i, b i) := by
    rw [← h_sum]
    have h_perm : ∑ i, x i = ∑ i, c (σ i) := sum_congr rfl (fun i _ => h_x_perm i)
    rw [h_perm]
    exact Equiv.sum_comp σ c
  have h_b_le_x := MajorizationFiniteDescent N b x h_b_int h_x_int h_x_sum h_b_desc h_x_desc h_prefix h h_conv h_symm
  have h_x_c : h x = h c := by
    have h_symm_c := h_symm c σ
    have h_x_eq : x = (fun i => c (σ i)) := by
      ext i
      exact h_x_perm i
    rw [h_x_eq, h_symm_c]
  rwa [h_x_c] at h_b_le_x

