import Tablet.Preamble
import Mathlib.Data.Fintype.Perm

open Finset Real Equiv Equiv.Perm

-- [TABLET NODE: MajorizationTransferConvexCombination]

theorem MajorizationTransferConvexCombination :
    ∀ N : ℕ, ∀ b x y : Fin N → ℝ,
    ∀ i j : Fin N, i.val < j.val →
    b j ≤ b i → b i < x i → x j < b j →
    ∀ δ : ℝ, 0 < δ → δ ≤ x i - b i → δ ≤ b j - x j →
    y i = x i - δ → y j = x j + δ → (∀ k : Fin N, k ≠ i → k ≠ j → y k = x k) →
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      ∀ k : Fin N, y k = (1 - θ) * x k + θ * x (swap i j k) := by
-- BODY
  intros N b x y i j _ h_bji h_bix h_xjb
  intros δ h_d_pos h_d_xi h_d_xj h_yi h_yj h_yk
  have h_x_gt : x j < x i := by linarith
  have h_x_diff : 0 < x i - x j := sub_pos.mpr h_x_gt
  use δ / (x i - x j)
  refine ⟨?_, ?_, ?_⟩
  · positivity
  · rw [div_le_one h_x_diff]
    linarith
  · intro k
    by_cases h_ki : k = i
    · rw [h_ki]
      rw [h_yi, swap_apply_left]
      calc x i - δ = x i - (δ / (x i - x j)) * (x i - x j) := by rw [div_mul_cancel₀ _ h_x_diff.ne']
        _ = (1 - δ / (x i - x j)) * x i + (δ / (x i - x j)) * x j := by ring
    · by_cases h_kj : k = j
      · rw [h_kj]
        rw [h_yj, swap_apply_right]
        calc x j + δ = x j + (δ / (x i - x j)) * (x i - x j) := by rw [div_mul_cancel₀ _ h_x_diff.ne']
          _ = (1 - δ / (x i - x j)) * x j + (δ / (x i - x j)) * x i := by ring
      · rw [h_yk k h_ki h_kj, swap_apply_of_ne_of_ne h_ki h_kj]
        ring
