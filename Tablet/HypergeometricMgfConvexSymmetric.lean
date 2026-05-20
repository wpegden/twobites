import Tablet.Preamble
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Finset Real Equiv Equiv.Perm BigOperators

-- [TABLET NODE: HypergeometricMgfConvexSymmetric]

theorem HypergeometricMgfConvexSymmetric :
    ∀ N : ℕ, ∀ v : Fin N → ℝ, ∀ L : ℝ,
    let h : (Fin N → ℝ) → ℝ :=
      fun y => (Nat.factorial N : ℝ)⁻¹ *
        ∑ σ : Perm (Fin N), exp (L * ∑ i : Fin N, y i * v (σ i))
    (∀ y z : Fin N → ℝ, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      h (fun i => (1 - θ) * y i + θ * z i) ≤ (1 - θ) * h y + θ * h z) ∧
    (∀ y : Fin N → ℝ, ∀ σ : Perm (Fin N), h (fun i => y (σ i)) = h y) := by
-- BODY
  intro N v L h
  constructor
  · intro y z θ hθ0 hθ1
    dsimp [h]
    have H1 : ∀ σ : Perm (Fin N), exp (L * ∑ i : Fin N, ((1 - θ) * y i + θ * z i) * v (σ i)) ≤
      (1 - θ) * exp (L * ∑ i : Fin N, y i * v (σ i)) + θ * exp (L * ∑ i : Fin N, z i * v (σ i)) := by
      intro σ
      have E : L * ∑ i : Fin N, ((1 - θ) * y i + θ * z i) * v (σ i) =
        (1 - θ) * (L * ∑ i : Fin N, y i * v (σ i)) + θ * (L * ∑ i : Fin N, z i * v (σ i)) := by
        calc L * ∑ i : Fin N, ((1 - θ) * y i + θ * z i) * v (σ i)
          _ = L * ∑ i : Fin N, ((1 - θ) * (y i * v (σ i)) + θ * (z i * v (σ i))) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = L * ((1 - θ) * ∑ i : Fin N, y i * v (σ i) + θ * ∑ i : Fin N, z i * v (σ i)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = (1 - θ) * (L * ∑ i : Fin N, y i * v (σ i)) + θ * (L * ∑ i : Fin N, z i * v (σ i)) := by
            ring
      rw [E]
      have C := convexOn_exp.2 (x := L * ∑ i : Fin N, y i * v (σ i)) (y := L * ∑ i : Fin N, z i * v (σ i))
        (Set.mem_univ _) (Set.mem_univ _) (sub_nonneg.mpr hθ1) hθ0 (sub_add_cancel 1 θ)
      exact C
    calc (Nat.factorial N : ℝ)⁻¹ * ∑ σ : Perm (Fin N), exp (L * ∑ i : Fin N, ((1 - θ) * y i + θ * z i) * v (σ i))
      _ ≤ (Nat.factorial N : ℝ)⁻¹ * ∑ σ : Perm (Fin N), ((1 - θ) * exp (L * ∑ i : Fin N, y i * v (σ i)) + θ * exp (L * ∑ i : Fin N, z i * v (σ i))) := by
        gcongr (Nat.factorial N : ℝ)⁻¹ * ?_
        apply Finset.sum_le_sum
        intro σ _
        exact H1 σ
      _ = (1 - θ) * ((Nat.factorial N : ℝ)⁻¹ * ∑ σ : Perm (Fin N), exp (L * ∑ i : Fin N, y i * v (σ i))) +
          θ * ((Nat.factorial N : ℝ)⁻¹ * ∑ σ : Perm (Fin N), exp (L * ∑ i : Fin N, z i * v (σ i))) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  · intro y σ
    dsimp [h]
    congr 1
    have E : ∀ τ : Perm (Fin N), ∑ i : Fin N, y (σ i) * v (τ i) = ∑ i : Fin N, y i * v ((τ * σ⁻¹) i) := by
      intro τ
      have H_inner : ∑ i : Fin N, y (σ i) * v (τ i) = ∑ i : Fin N, (fun j => y j * v ((τ * σ⁻¹) j)) (σ i) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp
        rw [Equiv.symm_apply_apply σ i]
      rw [H_inner]
      exact Equiv.sum_comp σ (fun j => y j * v ((τ * σ⁻¹) j))
    have E2 : ∑ τ : Perm (Fin N), exp (L * ∑ i : Fin N, y (σ i) * v (τ i)) =
      ∑ τ : Perm (Fin N), exp (L * ∑ i : Fin N, y i * v ((τ * σ⁻¹) i)) := by
      apply Finset.sum_congr rfl
      intro τ _
      rw [E τ]
    rw [E2]
    have E3 : ∑ τ : Perm (Fin N), exp (L * ∑ i : Fin N, y i * v ((τ * σ⁻¹) i)) =
      ∑ τ : Perm (Fin N), (fun τ' => exp (L * ∑ i : Fin N, y i * v (τ' i))) ((Equiv.mulRight σ⁻¹) τ) := rfl
    rw [E3]
    have E4 := Equiv.sum_comp (Equiv.mulRight σ⁻¹) (fun τ' => exp (L * ∑ i : Fin N, y i * v (τ' i)))
    exact E4
