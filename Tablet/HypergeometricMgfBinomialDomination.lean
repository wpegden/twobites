import Tablet.Preamble
import Tablet.HypergeometricSubsetAverageEqPermAverage
import Tablet.BinomialMgfEqSumCountVector
import Tablet.SortedCountVectorPrefixSumBound
import Tablet.MajorizationConvexSymmetricBound
import Tablet.HypergeometricMgfConvexSymmetric
import Tablet.FinVectorHasSortedPermutation

open Finset Real Equiv Equiv.Perm BigOperators

-- [TABLET NODE: HypergeometricMgfBinomialDomination]

theorem HypergeometricMgfBinomialDomination :
    ∀ N n m : ℕ, n ≤ N → m ≤ N →
    ∀ (M : Finset (Fin N)), M.card = m →
    ∀ L : ℝ,
    let q : ℝ := (m : ℝ) / (N : ℝ)
    let Y_mgf : ℝ :=
      (Nat.choose N n : ℝ)⁻¹ *
        ∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)),
          exp (L * (S ∩ M).card)
    Y_mgf ≤ (1 - q + q * exp L) ^ n := by
-- BODY
  intro N n m hn hm M hM L q Y_mgf
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · have hn0 : n = 0 := by omega
    have hm0 : m = 0 := by omega
    subst hn0 hm0
    dsimp [q, Y_mgf]
    simp
  · let v : Fin N → ℝ := fun i => if i ∈ M then 1 else 0
    let b : Fin N → ℝ := fun i => if i.val < n then 1 else 0
    have h_Y_eq : Y_mgf = (Nat.factorial N : ℝ)⁻¹ * ∑ σ : Perm (Fin N), exp (L * ∑ i : Fin N, b i * v (σ i)) :=
      HypergeometricSubsetAverageEqPermAverage N n m hn hm M hM L
    let h_fun : (Fin N → ℝ) → ℝ := fun y => (Nat.factorial N : ℝ)⁻¹ * ∑ σ : Perm (Fin N), exp (L * ∑ i : Fin N, y i * v (σ i))
    have h_Y_eq_hb : Y_mgf = h_fun b := h_Y_eq
    let c : (Fin n → Fin N) → Fin N → ℝ := fun X i => (((univ : Finset (Fin n)).filter (fun j => X j = i)).card : ℝ)
    have h_binom_eq : (1 - q + q * exp L) ^ n = (N ^ n : ℝ)⁻¹ * ∑ X : Fin n → Fin N, h_fun (c X) :=
      BinomialMgfEqSumCountVector N n m hNpos hn hm M hM L
    
    have h_convex_symm := HypergeometricMgfConvexSymmetric N v L
    rcases h_convex_symm with ⟨h_conv, h_symm⟩

    have hb_sum : (∑ i : Fin N, b i) = n := by
      dsimp [b]
      have eq1 : (∑ i : Fin N, ite (i.val < n) (1 : ℝ) 0) = ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < n), (1 : ℝ) := by
        rw [sum_ite]
        simp
      rw [eq1]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      have H1 : (univ.filter (fun i : Fin N => i.val < n)).card = n := by
        have e : (univ.filter (fun (i : Fin N) => i.val < n)) ≃ Fin n :=
          { toFun := fun i => ⟨i.val.val, (mem_filter.1 i.2).2⟩
            invFun := fun i => ⟨⟨i.val, i.2.trans_le hn⟩, mem_filter.2 ⟨mem_univ _, i.2⟩⟩
            left_inv := fun i => Subtype.ext (Fin.ext rfl)
            right_inv := fun i => Fin.ext rfl }
        rw [← Fintype.card_coe]
        exact Eq.trans (Fintype.card_congr e) (Fintype.card_fin n)
      exact_mod_cast H1

    have hb_desc : ∀ i j : Fin N, i.val ≤ j.val → b j ≤ b i := by
      intro i j hij
      dsimp [b]
      by_cases hj : j.val < n
      · have hi : i.val < n := by omega
        rw [if_pos hj, if_pos hi]
      · rw [if_neg hj]
        split_ifs
        · exact zero_le_one
        · exact le_rfl

    have hb_int : ∀ i : Fin N, ∃ k : ℕ, b i = k := by
      intro i
      dsimp [b]
      split_ifs
      · exact ⟨1, by norm_num⟩
      · exact ⟨0, by norm_num⟩

    have hb_pref : ∀ r : ℕ, r ≤ N → ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < r), b i = min r n := by
      intro r hr
      dsimp [b]
      have eq1 : ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < r), (if i.val < n then (1 : ℝ) else 0) =
                 ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < r), if i.val < min r n then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi
        have iff1 : i.val < n ↔ i.val < min r n := by omega
        by_cases h : i.val < n
        · rw [if_pos h, if_pos (iff1.mp h)]
        · rw [if_neg h, if_neg (iff1.not.mp h)]
      rw [eq1]
      have eq2 : ∑ i ∈ univ.filter (fun (i : Fin N) => i.val < r), (if i.val < min r n then (1 : ℝ) else 0) =
                 ∑ i ∈ (univ.filter (fun (i : Fin N) => i.val < r)).filter (fun i => i.val < min r n), (1 : ℝ) := by
        rw [sum_ite]
        simp
      rw [eq2]
      have eq3 : (univ.filter (fun (i : Fin N) => i.val < r)).filter (fun i => i.val < min r n) =
                 univ.filter (fun i : Fin N => i.val < min r n) := by
        ext a
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · intro ⟨h1, h2⟩; exact h2
        · intro h1; exact ⟨lt_of_lt_of_le h1 (Nat.min_le_left r n), h1⟩
      rw [eq3]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      have : (univ.filter (fun (i : Fin N) => i.val < min r n)).card = min r n := by
        have e : (univ.filter (fun (i : Fin N) => i.val < min r n)) ≃ Fin (min r n) :=
          { toFun := fun i => ⟨i.val.val, (mem_filter.1 i.2).2⟩
            invFun := fun i => ⟨⟨i.val, lt_of_lt_of_le i.2 (le_trans (Nat.min_le_right r n) hn)⟩, mem_filter.2 ⟨mem_univ _, i.2⟩⟩
            left_inv := fun i => Subtype.ext (Fin.ext rfl)
            right_inv := fun i => Fin.ext rfl }
        rw [← Fintype.card_coe]
        exact Eq.trans (Fintype.card_congr e) (Fintype.card_fin (min r n))
      exact_mod_cast this

    have h_c_int : ∀ X : Fin n → Fin N, ∀ i : Fin N, ∃ k : ℕ, c X i = k := by
      intro X i
      dsimp [c]
      exact ⟨((univ.filter (fun j => X j = i)).card), by rfl⟩

    have h_c_sum : ∀ X : Fin n → Fin N, (∑ i : Fin N, c X i) = n := by
      intro X
      dsimp [c]
      have : ∑ i : Fin N, (((univ.filter (fun (j : Fin n) => X j = i)).card) : ℝ) =
             ((∑ i : Fin N, (univ.filter (fun (j : Fin n) => X j = i)).card) : ℝ) := by
        rfl
      rw [this]
      have h1 : ∑ i : Fin N, (univ.filter (fun (j : Fin n) => X j = i)).card = n := by
        have eq_sum : ∑ i : Fin N, (univ.filter (fun (j : Fin n) => X j = i)).card = ∑ i : Fin N, ∑ j : Fin n, (ite (X j = i) 1 0 : ℕ) := by
          apply sum_congr rfl
          intro i _
          rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
          rfl
        rw [eq_sum, sum_comm]
        have h_inner : ∀ j : Fin n, ∑ i : Fin N, (ite (X j = i) 1 0 : ℕ) = 1 := by
          intro j
          have eq2 : ∑ i : Fin N, (ite (X j = i) 1 0 : ℕ) = (ite (X j = X j) 1 0 : ℕ) + ∑ i ∈ univ \ {X j}, (ite (X j = i) 1 0 : ℕ) := by
            have H_insert := sum_insert (f := fun i => (ite (X j = i) 1 0 : ℕ)) (a := X j) (s := univ \ {X j}) (by simp)
            have H_eq : insert (X j) (univ \ {X j}) = univ := by
              ext x
              simp
            rw [H_eq] at H_insert
            exact H_insert
          have h_zero : ∑ i ∈ univ \ {X j}, (ite (X j = i) 1 0 : ℕ) = 0 := by
            apply sum_eq_zero
            intro i hi
            have : X j ≠ i := by
              intro h_eq
              simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hi
              exact hi h_eq.symm
            rw [if_neg this]
          rw [eq2, h_zero]
          simp
        rw [sum_congr rfl (fun j _ => h_inner j)]
        simp
      exact_mod_cast h1

    have h_X_bound : ∀ X : Fin n → Fin N, h_fun b ≤ h_fun (c X) := by
      intro X
      have H_exists : ∃ x : Fin N → ℝ,
        (∃ σ : Perm (Fin N), ∀ i, x i = c X (σ i)) ∧
        (∀ i j : Fin N, i.val ≤ j.val → x j ≤ x i) ∧
        (∀ r : ℕ, r ≤ N → ∑ i ∈ univ.filter (fun i => i.val < r), b i ≤ ∑ i ∈ univ.filter (fun i => i.val < r), x i) := by
        have H_sorted := FinVectorHasSortedPermutation N (c X)
        rcases H_sorted with ⟨x, ⟨σ, hx_eq⟩, hx_desc⟩
        use x
        refine ⟨⟨σ, hx_eq⟩, hx_desc, ?_⟩
        intro r hr
        rw [hb_pref r hr]
        have hx_sum : (∑ i, x i) = n := by
          have h_perm : ∑ i, x i = ∑ i, c X (σ i) := sum_congr rfl (fun i _ => hx_eq i)
          rw [h_perm, Equiv.sum_comp σ (c X)]
          exact h_c_sum X
        have hx_int : ∀ i, ∃ k : ℕ, x i = k := by
          intro i
          rw [hx_eq i]
          exact h_c_int X (σ i)
        exact SortedCountVectorPrefixSumBound N n x hx_sum hx_int hx_desc r hr
      have h_sum_c : (∑ i : Fin N, c X i) = ∑ i : Fin N, b i := by
        rw [h_c_sum X, hb_sum]
      exact MajorizationConvexSymmetricBound N (c X) b h_sum_c hb_desc H_exists (h_c_int X) hb_int h_fun h_conv h_symm

    rw [h_Y_eq_hb, h_binom_eq]
    have h_sum_b : ∑ X : Fin n → Fin N, h_fun b ≤ ∑ X : Fin n → Fin N, h_fun (c X) := by
      apply sum_le_sum
      intro X _
      exact h_X_bound X
    have h_sum_b_eval : ∑ X : Fin n → Fin N, h_fun b = (N ^ n : ℝ) * h_fun b := by
      rw [sum_const, nsmul_eq_mul]
      have h_card : (univ : Finset (Fin n → Fin N)).card = N ^ n := by
        rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      rw [h_card]
      push_cast
      rfl
    rw [h_sum_b_eval] at h_sum_b
    have H_inv_pos : 0 ≤ (N ^ n : ℝ)⁻¹ := by
      have hNpos_real : (N : ℝ) > 0 := by exact_mod_cast hNpos
      positivity
    have H_bound := mul_le_mul_of_nonneg_left h_sum_b H_inv_pos
    calc h_fun b
      _ = 1 * h_fun b := by ring
      _ = ((N ^ n : ℝ)⁻¹ * (N ^ n : ℝ)) * h_fun b := by
        congr 1
        symm
        apply inv_mul_cancel₀
        have hNpos_real : (N : ℝ) > 0 := by exact_mod_cast hNpos
        positivity
      _ = (N ^ n : ℝ)⁻¹ * ((N ^ n : ℝ) * h_fun b) := by ring
      _ ≤ (N ^ n : ℝ)⁻¹ * ∑ X : Fin n → Fin N, h_fun (c X) := H_bound
