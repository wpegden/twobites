import Tablet.Preamble
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm

open Finset Real Equiv Equiv.Perm BigOperators

-- [TABLET NODE: BinomialMgfEqSumCountVector]

theorem BinomialMgfEqSumCountVector :
    ∀ N n m : ℕ, 0 < N → n ≤ N → m ≤ N →
    ∀ (M : Finset (Fin N)), M.card = m →
    ∀ L : ℝ,
    let q : ℝ := (m : ℝ) / (N : ℝ)
    let v : Fin N → ℝ := fun i => if i ∈ M then 1 else 0
    let c : (Fin n → Fin N) → Fin N → ℝ :=
      fun X i => (((univ : Finset (Fin n)).filter (fun j => X j = i)).card : ℝ)
    (1 - q + q * exp L) ^ n =
      (N ^ n : ℝ)⁻¹ * ∑ X : Fin n → Fin N,
        (Nat.factorial N : ℝ)⁻¹ *
          ∑ σ : Perm (Fin N), exp (L * ∑ i : Fin N, c X i * v (σ i)) := by
-- BODY
  intro N n m hN hn hm M hM L q v c
  have hc : ∀ (X : Fin n → Fin N) (σ : Perm (Fin N)), ∑ i : Fin N, c X i * v (σ i) = ∑ j : Fin n, v (σ (X j)) := by
    intro X σ
    have h1 : ∀ i, c X i * v (σ i) = ∑ j ∈ univ.filter (fun j => X j = i), v (σ (X j)) := by
      intro i
      have h_eq : ∀ j ∈ univ.filter (fun j => X j = i), v (σ (X j)) = v (σ i) := by
        intro j hj
        rw [mem_filter] at hj
        rw [hj.2]
      rw [sum_congr rfl h_eq]
      simp [c]
    simp_rw [h1]
    exact sum_fiberwise univ X (fun j => v (σ (X j)))
  simp_rw [hc]
  rw [← mul_sum, sum_comm]
  have hexp : ∀ (X : Fin n → Fin N) (σ : Perm (Fin N)), exp (L * ∑ j : Fin n, v (σ (X j))) = ∏ j : Fin n, exp (L * v (σ (X j))) := by
    intro X σ
    rw [mul_sum, Real.exp_sum]
  simp_rw [hexp]
  have hprod : ∀ (σ : Perm (Fin N)), ∑ X : Fin n → Fin N, ∏ j : Fin n, exp (L * v (σ (X j))) = (∑ a : Fin N, exp (L * v (σ a))) ^ n := by
    intro σ
    have h1 := Finset.sum_pow' (univ : Finset (Fin N)) (fun a => exp (L * v (σ a))) n
    rw [Fintype.piFinset_univ] at h1
    exact h1.symm
  simp_rw [hprod]
  have hsum_eq : ∀ σ : Perm (Fin N), ∑ a : Fin N, exp (L * v (σ a)) = ∑ a : Fin N, exp (L * v a) := by
    intro σ
    exact Equiv.sum_comp σ (fun a => exp (L * v a))
  simp_rw [hsum_eq]
  have hsum_sigma : ∑ σ : Perm (Fin N), (∑ a : Fin N, exp (L * v a)) ^ n = (Nat.factorial N : ℝ) * (∑ a : Fin N, exp (L * v a)) ^ n := by
    rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum_sigma, ← mul_assoc (Nat.factorial N : ℝ)⁻¹]
  have h_fac_cancel : (Nat.factorial N : ℝ)⁻¹ * (Nat.factorial N : ℝ) = 1 := by
    apply inv_mul_cancel₀
    exact_mod_cast Nat.factorial_ne_zero N
  rw [h_fac_cancel, one_mul]
  have hp : ((N : ℝ) ^ n)⁻¹ * (∑ a : Fin N, exp (L * v a)) ^ n = ((N : ℝ)⁻¹ * ∑ a : Fin N, exp (L * v a)) ^ n := by
    rw [← inv_pow, ← mul_pow]
  rw [hp]
  congr 1
  have hsum_split : ∑ a : Fin N, exp (L * v a) = ∑ a ∈ M, exp (L * v a) + ∑ a ∈ Mᶜ, exp (L * v a) :=
    (Finset.sum_add_sum_compl M (fun a => exp (L * v a))).symm
  rw [hsum_split]
  have hM_val : ∀ a ∈ M, exp (L * v a) = exp L := by
    intro a ha
    have : v a = 1 := by
      dsimp [v]
      rw [if_pos ha]
    rw [this, mul_one]
  have hn_val : ∀ a ∈ Mᶜ, exp (L * v a) = 1 := by
    intro a ha
    have : v a = 0 := by
      dsimp [v]
      have : a ∉ M := by
        rw [mem_compl] at ha
        exact ha
      rw [if_neg this]
    rw [this, mul_zero, Real.exp_zero]
  rw [sum_congr rfl hM_val, sum_congr rfl hn_val]
  rw [sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  rw [hM]
  have hM_compl : Mᶜ.card = N - m := by
    have hc_card := card_add_card_compl M
    rw [Fintype.card_fin, hM] at hc_card
    omega
  rw [hM_compl]
  have hsub : ((N - m : ℕ) : ℝ) = (N : ℝ) - (m : ℝ) := by
    exact Nat.cast_sub hm
  rw [hsub]
  -- Now goal: 1 - q + q * exp L = (↑N)⁻¹ * (↑m * exp L + (↑N - ↑m) * 1)
  -- where q = ↑m / ↑N
  dsimp [q]
  have hN_inv : (N : ℝ)⁻¹ * (N : ℝ) = 1 := by
    apply inv_mul_cancel₀
    exact_mod_cast ne_of_gt hN
  calc
    1 - (m : ℝ) / (N : ℝ) + (m : ℝ) / (N : ℝ) * exp L = 1 - (m : ℝ) * (N : ℝ)⁻¹ + (m : ℝ) * (N : ℝ)⁻¹ * exp L := by ring
    _ = (N : ℝ)⁻¹ * (N : ℝ) - (N : ℝ)⁻¹ * (m : ℝ) + (N : ℝ)⁻¹ * (m : ℝ) * exp L := by
      rw [hN_inv]
      ring
    _ = (N : ℝ)⁻¹ * ((m : ℝ) * exp L + ((N : ℝ) - (m : ℝ)) * 1) := by ring
