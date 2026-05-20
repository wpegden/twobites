import Tablet.Preamble
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.Field.Basic

open Finset Real Equiv Equiv.Perm BigOperators

-- [TABLET NODE: HypergeometricSubsetAverageEqPermAverage]

theorem HypergeometricSubsetAverageEqPermAverage :
    ∀ N n m : ℕ, n ≤ N → m ≤ N →
    ∀ (M : Finset (Fin N)), M.card = m →
    ∀ L : ℝ,
    let Y_mgf : ℝ :=
      (Nat.choose N n : ℝ)⁻¹ *
        ∑ S ∈ powersetCard n (univ : Finset (Fin N)),
          exp (L * (S ∩ M).card)
    let v : Fin N → ℝ := fun i => if i ∈ M then 1 else 0
    let b : Fin N → ℝ := fun i => if i.val < n then 1 else 0
    Y_mgf =
      (Nat.factorial N : ℝ)⁻¹ *
        ∑ σ : Perm (Fin N), exp (L * ∑ i : Fin N, b i * v (σ i)) := by
-- BODY
  intros N n m h_n h_m M h_M L Y_mgf v b
  let B : Finset (Fin N) := univ.filter (fun i => i.val < n)
  have hB : B.card = n := by
    have e : (univ.filter (fun (i : Fin N) => i.val < n)) ≃ Fin n :=
      { toFun := fun i => ⟨i.val.val, (mem_filter.1 i.2).2⟩
        invFun := fun i => ⟨⟨i.val, i.2.trans_le h_n⟩, mem_filter.2 ⟨mem_univ _, i.2⟩⟩
        left_inv := fun i => Subtype.ext (Fin.ext rfl)
        right_inv := fun i => Fin.ext rfl }
    rw [← Fintype.card_coe]
    exact Eq.trans (Fintype.card_congr e) (Fintype.card_fin n)
  have h_sum_b_v : ∀ σ : Perm (Fin N), (∑ i : Fin N, b i * v (σ i)) = (B.image σ ∩ M).card := by
    intro σ
    have h_out : ∑ i ∈ univ.filter (fun i : Fin N => ¬ (i.val < n)), b i * v (σ i) = 0 := by
      apply sum_eq_zero
      intro i hi
      have h_notin_B : ¬ (i.val < n) := (mem_filter.1 hi).2
      have hb : b i = 0 := by simp [b, h_notin_B]
      rw [hb, zero_mul]
    have h_univ : ∑ i : Fin N, b i * v (σ i) = (∑ i ∈ B, b i * v (σ i)) + ∑ i ∈ univ.filter (fun i : Fin N => ¬ (i.val < n)), b i * v (σ i) := by
      exact (sum_filter_add_sum_filter_not univ (fun i : Fin N => i.val < n) (fun i => b i * v (σ i))).symm
    rw [h_univ, h_out, add_zero]
    have h1_real : ∑ i ∈ B, b i * v (σ i) = ∑ i ∈ B, v (σ i) := by
      refine sum_congr rfl (fun i hi => ?_)
      have h_in_B : i.val < n := (mem_filter.1 hi).2
      have hb : b i = 1 := by simp [b, h_in_B]
      rw [hb, one_mul]
    rw [h1_real]
    have h2 : ∑ i ∈ B, v (σ i) = ∑ j ∈ B.image σ, v j := by
      rw [sum_image (fun x y hx hy hxy => σ.injective hxy)]
    rw [h2]
    have h3 : ∑ j ∈ B.image σ, v j = (B.image σ ∩ M).card := by
      have h_inter : B.image σ ∩ M = (B.image σ).filter (fun j => j ∈ M) := by
        ext a
        simp
      rw [h_inter]
      have : ∑ j ∈ (B.image σ).filter (fun j => j ∈ M), (1 : ℝ) = ((B.image σ).filter (fun j => j ∈ M)).card := by
        simp only [sum_const, nsmul_eq_mul, mul_one]
      rw [← this]
      have eq_sum : ∑ j ∈ B.image σ, v j = ∑ j ∈ B.image σ, if j ∈ M then (1 : ℝ) else 0 := by
        refine sum_congr rfl (fun j _ => ?_)
        simp [v]
      rw [eq_sum, sum_filter]
    rw [h3]
  
  have image_mul_perm : ∀ (B : Finset (Fin N)) (τ σ : Perm (Fin N)), B.image (τ * σ) = (B.image σ).image τ := by
    intro B τ σ
    ext a
    simp only [mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      use σ b
      refine ⟨?_, by rfl⟩
      use b
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      use c
      refine ⟨hc, by rfl⟩

  have filter_equiv : ∀ (B S : Finset (Fin N)) (τ : Perm (Fin N)),
    {σ : Perm (Fin N) // B.image σ = S} ≃ {σ : Perm (Fin N) // B.image σ = S.image τ} :=
    fun B S τ =>
      { toFun := fun ⟨σ, hσ⟩ => ⟨τ * σ, by rw [image_mul_perm, hσ]⟩
        invFun := fun ⟨σ, hσ⟩ => ⟨τ⁻¹ * σ, by
          rw [image_mul_perm, hσ]
          ext a
          simp only [mem_image]
          constructor
          · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
            have : τ⁻¹ (τ c) = c := by simp
            rw [this]
            exact hc
          · intro ha
            use τ a
            refine ⟨?_, by simp⟩
            use a⟩
        left_inv := fun ⟨σ, hσ⟩ => Subtype.ext (inv_mul_cancel_left τ σ)
        right_inv := fun ⟨σ, hσ⟩ => Subtype.ext (mul_inv_cancel_left τ σ) }

  have C_independent : ∀ (B S1 S2 : Finset (Fin N)), S1.card = S2.card →
    (univ.filter (fun σ : Perm (Fin N) => B.image σ = S1)).card =
    (univ.filter (fun σ : Perm (Fin N) => B.image σ = S2)).card := by
    intro B S1 S2 h_card
    have e_S : S1 ≃ S2 := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, h_card])
    have h_compl_card : Fintype.card {a // a ∉ S1} = Fintype.card {a // a ∉ S2} := by
      have h1 : Fintype.card {a // a ∉ S1} = Fintype.card (Fin N) - Fintype.card S1 :=
        Fintype.card_subtype_compl (fun a => a ∈ S1)
      have h2 : Fintype.card {a // a ∉ S2} = Fintype.card (Fin N) - Fintype.card S2 :=
        Fintype.card_subtype_compl (fun a => a ∈ S2)
      rw [h1, h2, Fintype.card_coe S1, Fintype.card_coe S2, h_card]
    have e_compl : {a // a ∉ S1} ≃ {a // a ∉ S2} := Fintype.equivOfCardEq h_compl_card
    let τ : Perm (Fin N) := (Equiv.sumCompl (· ∈ S1)).symm.trans ((e_S.sumCongr e_compl).trans (Equiv.sumCompl (· ∈ S2)))
    have hτ : S1.image τ = S2 := by
      ext y
      simp only [mem_image, τ]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h_symm : (Equiv.sumCompl (fun a => a ∈ S1)).symm x = Sum.inl ⟨x, hx⟩ :=
          Equiv.sumCompl_symm_apply_of_pos hx
        have eq1 : (Equiv.sumCompl (fun a => a ∈ S1)).symm x = Sum.inl ⟨x, hx⟩ := h_symm
        simp only [Equiv.trans_apply, eq1, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
        exact (e_S ⟨x, hx⟩).2
      · intro hy
        use e_S.symm ⟨y, hy⟩
        have hx : ↑(e_S.symm ⟨y, hy⟩) ∈ S1 := (e_S.symm ⟨y, hy⟩).2
        refine ⟨hx, ?_⟩
        have h_symm : (Equiv.sumCompl (fun a => a ∈ S1)).symm ↑(e_S.symm ⟨y, hy⟩) = Sum.inl ⟨↑(e_S.symm ⟨y, hy⟩), hx⟩ :=
          Equiv.sumCompl_symm_apply_of_pos hx
        have eq1 : (Equiv.sumCompl (fun a => a ∈ S1)).symm ↑(e_S.symm ⟨y, hy⟩) = Sum.inl ⟨↑(e_S.symm ⟨y, hy⟩), hx⟩ := h_symm
        simp only [Equiv.trans_apply, eq1, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
        exact congr_arg Subtype.val (e_S.apply_symm_apply ⟨y, hy⟩)
    have e : {σ : Perm (Fin N) // B.image σ = S1} ≃ {σ : Perm (Fin N) // B.image σ = S2} :=
      (filter_equiv B S1 τ).trans (Equiv.cast (by rw [hτ]))
    have e2 : ↥(univ.filter (fun σ : Perm (Fin N) => B.image σ = S1)) ≃ ↥(univ.filter (fun σ : Perm (Fin N) => B.image σ = S2)) :=
      (Equiv.subtypeEquivRight (by intro x; simp)).trans (e.trans (Equiv.subtypeEquivRight (by intro x; simp)))
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_congr e2

  have h_eq_sum : ∑ σ : Perm (Fin N), exp (L * ∑ i : Fin N, b i * v (σ i)) =
    ∑ S ∈ powersetCard n univ, ((univ.filter (fun σ : Perm (Fin N) => B.image σ = S)).card : ℝ) * exp (L * (S ∩ M).card) := by
    have h_part1 : (∑ σ : Perm (Fin N), exp (L * ∑ i : Fin N, b i * v (σ i))) =
      ∑ σ : Perm (Fin N), exp (L * (B.image σ ∩ M).card) := by
      refine sum_congr rfl (fun σ _ => ?_)
      rw [h_sum_b_v σ]
    rw [h_part1]
    have h_comp := Finset.sum_comp (s := univ) (fun S => exp (L * (S ∩ M).card)) (fun σ : Perm (Fin N) => B.image σ)
    have h_img : univ.image (fun σ : Perm (Fin N) => B.image σ) = powersetCard n univ := by
      ext S
      simp only [mem_image, mem_powersetCard, mem_univ, true_and]
      constructor
      · rintro ⟨σ, rfl⟩
        refine ⟨subset_univ _, ?_⟩
        rw [card_image_of_injective B σ.injective]
        exact hB
      · intro hS
        have hS_card : S.card = n := hS.2
        have e_S : B ≃ S := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hB, hS_card])
        have h_compl_card : Fintype.card {a // a ∉ B} = Fintype.card {a // a ∉ S} := by
          have h1 : Fintype.card {a // a ∉ B} = Fintype.card (Fin N) - Fintype.card B :=
            Fintype.card_subtype_compl (fun a => a ∈ B)
          have h2 : Fintype.card {a // a ∉ S} = Fintype.card (Fin N) - Fintype.card S :=
            Fintype.card_subtype_compl (fun a => a ∈ S)
          rw [h1, h2, Fintype.card_coe B, Fintype.card_coe S, hB, hS_card]
        have e_compl : {a // a ∉ B} ≃ {a // a ∉ S} := Fintype.equivOfCardEq h_compl_card
        let τ : Perm (Fin N) := (Equiv.sumCompl (· ∈ B)).symm.trans ((e_S.sumCongr e_compl).trans (Equiv.sumCompl (· ∈ S)))
        use τ
        ext y
        simp only [mem_image, τ]
        constructor
        · rintro ⟨x, hx, rfl⟩
          have h_symm : (Equiv.sumCompl (fun a => a ∈ B)).symm x = Sum.inl ⟨x, hx⟩ :=
            Equiv.sumCompl_symm_apply_of_pos hx
          have eq1 : (Equiv.sumCompl (fun a => a ∈ B)).symm x = Sum.inl ⟨x, hx⟩ := h_symm
          simp only [Equiv.trans_apply, eq1, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
          exact (e_S ⟨x, hx⟩).2
        · intro hy
          use e_S.symm ⟨y, hy⟩
          have hx : ↑(e_S.symm ⟨y, hy⟩) ∈ B := (e_S.symm ⟨y, hy⟩).2
          refine ⟨hx, ?_⟩
          have h_symm : (Equiv.sumCompl (fun a => a ∈ B)).symm ↑(e_S.symm ⟨y, hy⟩) = Sum.inl ⟨↑(e_S.symm ⟨y, hy⟩), hx⟩ :=
            Equiv.sumCompl_symm_apply_of_pos hx
          have eq1 : (Equiv.sumCompl (fun a => a ∈ B)).symm ↑(e_S.symm ⟨y, hy⟩) = Sum.inl ⟨↑(e_S.symm ⟨y, hy⟩), hx⟩ := h_symm
          simp only [Equiv.trans_apply, eq1, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
          exact congr_arg Subtype.val (e_S.apply_symm_apply ⟨y, hy⟩)
    rw [h_comp, h_img]
    refine sum_congr rfl (fun S _ => ?_)
    rw [nsmul_eq_mul]

  have h_const : ∀ S ∈ powersetCard n (univ : Finset (Fin N)),
    ((univ.filter (fun σ : Perm (Fin N) => B.image σ = S)).card : ℝ) =
    ((univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card : ℝ) := by
    intro S hS
    have hS_card : S.card = n := (mem_powersetCard.1 hS).2
    rw [C_independent B S B (by rw [hS_card, hB])]
  
  have h_pull : ∑ S ∈ powersetCard n univ, ((univ.filter (fun σ : Perm (Fin N) => B.image σ = S)).card : ℝ) * exp (L * ↑(S ∩ M).card) =
    ((univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card : ℝ) * ∑ S ∈ powersetCard n univ, exp (L * ↑(S ∩ M).card) := by
    rw [mul_sum]
    refine sum_congr rfl (fun S hS => ?_)
    have : ((univ.filter (fun σ : Perm (Fin N) => B.image σ = S)).card : ℝ) = ((univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card : ℝ) := h_const S hS
    rw [this]

  let sum_fibers : ℕ := ∑ S ∈ powersetCard n univ, (univ.filter (fun σ : Perm (Fin N) => B.image σ = S)).card
  have h_sum_all_fibers : Fintype.card (Perm (Fin N)) = sum_fibers := by
    have h_img : univ.image (fun σ : Perm (Fin N) => B.image σ) = powersetCard n univ := by
      ext S
      simp only [mem_image, mem_powersetCard, mem_univ, true_and]
      constructor
      · rintro ⟨σ, rfl⟩
        refine ⟨subset_univ _, ?_⟩
        rw [card_image_of_injective B σ.injective]
        exact hB
      · intro hS
        have hS_card : S.card = n := hS.2
        have e_S : B ≃ S := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hB, hS_card])
        have h_compl_card : Fintype.card {a // a ∉ B} = Fintype.card {a // a ∉ S} := by
          have h1 : Fintype.card {a // a ∉ B} = Fintype.card (Fin N) - Fintype.card B :=
            Fintype.card_subtype_compl (fun a => a ∈ B)
          have h2 : Fintype.card {a // a ∉ S} = Fintype.card (Fin N) - Fintype.card S :=
            Fintype.card_subtype_compl (fun a => a ∈ S)
          rw [h1, h2, Fintype.card_coe B, Fintype.card_coe S, hB, hS_card]
        have e_compl : {a // a ∉ B} ≃ {a // a ∉ S} := Fintype.equivOfCardEq h_compl_card
        let τ : Perm (Fin N) := (Equiv.sumCompl (· ∈ B)).symm.trans ((e_S.sumCongr e_compl).trans (Equiv.sumCompl (· ∈ S)))
        use τ
        ext y
        simp only [mem_image, τ]
        constructor
        · rintro ⟨x, hx, rfl⟩
          have h_symm : (Equiv.sumCompl (fun a => a ∈ B)).symm x = Sum.inl ⟨x, hx⟩ :=
            Equiv.sumCompl_symm_apply_of_pos hx
          have eq1 : (Equiv.sumCompl (fun a => a ∈ B)).symm x = Sum.inl ⟨x, hx⟩ := h_symm
          simp only [Equiv.trans_apply, eq1, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
          exact (e_S ⟨x, hx⟩).2
        · intro hy
          use e_S.symm ⟨y, hy⟩
          have hx : ↑(e_S.symm ⟨y, hy⟩) ∈ B := (e_S.symm ⟨y, hy⟩).2
          refine ⟨hx, ?_⟩
          have h_symm : (Equiv.sumCompl (fun a => a ∈ B)).symm ↑(e_S.symm ⟨y, hy⟩) = Sum.inl ⟨↑(e_S.symm ⟨y, hy⟩), hx⟩ :=
            Equiv.sumCompl_symm_apply_of_pos hx
          have eq1 : (Equiv.sumCompl (fun a => a ∈ B)).symm ↑(e_S.symm ⟨y, hy⟩) = Sum.inl ⟨↑(e_S.symm ⟨y, hy⟩), hx⟩ := h_symm
          simp only [Equiv.trans_apply, eq1, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
          exact congr_arg Subtype.val (e_S.apply_symm_apply ⟨y, hy⟩)
    dsimp [sum_fibers]
    rw [← h_img]
    have h_card_univ : Fintype.card (Perm (Fin N)) = (univ : Finset (Perm (Fin N))).card := by rw [card_univ]
    rw [h_card_univ]
    exact card_eq_sum_card_image (fun σ : Perm (Fin N) => B.image σ) univ
  
  have h_sum_const : sum_fibers =
    (powersetCard n (univ : Finset (Fin N))).card * (univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card := by
    have h_rw : sum_fibers =
      ∑ S ∈ powersetCard n (univ : Finset (Fin N)), (univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card := by
      dsimp [sum_fibers]
      have h_eq : ∀ S ∈ powersetCard n (univ : Finset (Fin N)), (univ.filter (fun σ : Perm (Fin N) => B.image σ = S)).card = (univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card := by
        intro S hS
        have hS_card : S.card = n := (mem_powersetCard.1 hS).2
        exact C_independent B S B (by rw [hS_card, hB])
      exact Finset.sum_congr rfl h_eq
    rw [h_rw, sum_const]
    simp

  have h_card_perm : Fintype.card (Perm (Fin N)) = Nat.factorial N := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have h_card_powerset : (powersetCard n (univ : Finset (Fin N))).card = Nat.choose N n := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  
  rw [h_sum_const, h_card_perm, h_card_powerset] at h_sum_all_fibers
  
  have h_eq_C : ((Nat.choose N n : ℝ) * ((univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card : ℝ)) = (Nat.factorial N : ℝ) := by
    exact_mod_cast h_sum_all_fibers.symm
  
  have h_Y : Y_mgf = (Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ powersetCard n univ, exp (L * ↑(S ∩ M).card) := rfl
  by_cases hN0 : Nat.choose N n = 0
  · have h_fac_0 : (Nat.factorial N : ℝ) = 0 := by
      rw [← h_eq_C]
      have : (Nat.choose N n : ℝ) = 0 := by exact_mod_cast hN0
      rw [this, zero_mul]
    have h_fac_neq : (Nat.factorial N : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero N
    exact (h_fac_neq h_fac_0).elim
  · have hN0_R : (Nat.choose N n : ℝ) ≠ 0 := by exact_mod_cast hN0
    have h_C_val : ((univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card : ℝ) = (Nat.factorial N : ℝ) * (Nat.choose N n : ℝ)⁻¹ := by
      calc ((univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card : ℝ)
        _ = 1 * ((univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card : ℝ) := by ring
        _ = ((Nat.choose N n : ℝ)⁻¹ * (Nat.choose N n : ℝ)) * ((univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card : ℝ) := by rw [inv_mul_cancel₀ hN0_R]
        _ = (Nat.choose N n : ℝ)⁻¹ * ((Nat.choose N n : ℝ) * ((univ.filter (fun σ : Perm (Fin N) => B.image σ = B)).card : ℝ)) := by ring
        _ = (Nat.choose N n : ℝ)⁻¹ * (Nat.factorial N : ℝ) := by rw [h_eq_C]
        _ = (Nat.factorial N : ℝ) * (Nat.choose N n : ℝ)⁻¹ := by ring
    rw [h_Y, h_eq_sum, h_pull, h_C_val]
    have h_fac_neq : (Nat.factorial N : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero N
    calc (Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ powersetCard n univ, exp (L * ↑(S ∩ M).card)
      _ = (Nat.choose N n : ℝ)⁻¹ * 1 * ∑ S ∈ powersetCard n univ, exp (L * ↑(S ∩ M).card) := by ring
      _ = (Nat.choose N n : ℝ)⁻¹ * ((Nat.factorial N : ℝ)⁻¹ * (Nat.factorial N : ℝ)) * ∑ S ∈ powersetCard n univ, exp (L * ↑(S ∩ M).card) := by rw [inv_mul_cancel₀ h_fac_neq]
      _ = (Nat.factorial N : ℝ)⁻¹ * ((Nat.factorial N : ℝ) * (Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ powersetCard n univ, exp (L * ↑(S ∩ M).card)) := by ring
