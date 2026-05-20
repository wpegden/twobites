import Tablet.Preamble
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- [TABLET NODE: UniformInjectionImage]

open Finset Classical

theorem UniformInjectionImage {n m k : ℕ}
    (I : Finset (Fin n)) (hI : I.card = k)
    (P : Finset (Fin m × Fin m) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun (pi : Fin n ↪ Fin m × Fin m) => P (I.image pi))).card * Nat.choose (m * m) k =
    (Finset.univ.filter (fun S : Finset (Fin m × Fin m) => S.card = k ∧ P S)).card * Fintype.card (Fin n ↪ Fin m × Fin m) := by
-- BODY
  let U := Fin m × Fin m
  let Omega : Finset (Fin n ↪ U) := univ
  let Subsets : Finset (Finset U) := powersetCard k univ
  let f (pi : Fin n ↪ U) : Finset U := I.image pi

  have hf (pi : Fin n ↪ U) : f pi ∈ Subsets := by
    simp [Subsets, f, mem_powersetCard, card_image_of_injective _ pi.injective, hI]

  have h_subsets_card_ambient : Fintype.card U = m * m := by
    simp [U]

  let r := if h : Subsets.Nonempty then (Omega.filter (fun pi => f pi = choose h)).card else 0

  have hr (S : Finset U) (hS : S ∈ Subsets) : (Omega.filter (fun pi => f pi = S)).card = r := by
    have hne : Subsets.Nonempty := ⟨S, hS⟩
    simp only [r, dif_pos hne]
    let T := choose hne
    have hT : T ∈ Subsets := choose_spec hne
    rw [mem_powersetCard] at hS hT
    let eS := Equiv.sumCompl (fun x => x ∈ S)
    let eT := Equiv.sumCompl (fun x => x ∈ T)
    let e_ST : ↥S ≃ ↥T := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hS.2, hT.2])
    let e_compl_ST : {x // x ∉ S} ≃ {x // x ∉ T} := Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h_subsets_card_ambient, Fintype.card_coe, Fintype.card_coe, hS.2, hT.2])
    let sigma : U ≃ U := eS.symm.trans ((Equiv.sumCongr e_ST e_compl_ST).trans eT)
    let Phi : (Fin n ↪ U) ≃ (Fin n ↪ U) := (Equiv.refl _).embeddingCongr sigma

    have hsigma : ∀ x, sigma x ∈ T ↔ x ∈ S := by
      intro x
      simp only [sigma, Equiv.trans_apply]
      have : eS.symm x = if h : x ∈ S then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, h⟩ := rfl
      rw [this]
      split_ifs with hx
      · simp only [Equiv.sumCongr_apply, Sum.map_inl]
        have : eT (Sum.inl (e_ST ⟨x, hx⟩)) = (e_ST ⟨x, hx⟩).val := rfl
        rw [this]
        simp [hx, (e_ST ⟨x, hx⟩).2]
      · simp only [Equiv.sumCongr_apply, Sum.map_inr]
        have : eT (Sum.inr (e_compl_ST ⟨x, hx⟩)) = (e_compl_ST ⟨x, hx⟩).val := rfl
        rw [this]
        simp [hx, (e_compl_ST ⟨x, hx⟩).2]

    have h_f_Phi (pi : Fin n ↪ U) : f (Phi pi) = (f pi).image sigma := by
      ext y
      simp [f, Phi, Equiv.embeddingCongr_apply, mem_image]

    have h_f_Phi_symm (pi : Fin n ↪ U) : f (Phi.symm pi) = (f pi).image sigma.symm := by
      ext y
      simp [f, Phi, Equiv.embeddingCongr_apply, mem_image]

    have h_image_sigma : S.image sigma = T := by
      ext y; rw [mem_image]
      constructor
      · intro ⟨x, hx, hxy⟩; rw [← hxy, hsigma]; exact hx
      · intro hy; use sigma.symm y; simp [← hsigma, hy]

    apply card_bij (fun pi _ => Phi pi)
    · intro pi h; simp [Omega] at h ⊢; rw [h_f_Phi, h, h_image_sigma]
    · intro pi1 pi2 h1 h2 heq; exact Phi.injective heq
    · intro pi' h'; simp [Omega] at h' ⊢; use Phi.symm pi'
      constructor
      · rw [h_f_Phi_symm, h']
        ext y; constructor
        · intro hy; rw [mem_image] at hy; obtain ⟨x, hx, rfl⟩ := hy
          rw [← hsigma, sigma.apply_symm_apply]; exact hx
        · intro hy; rw [mem_image]
          use sigma y; constructor
          · rw [hsigma]; exact hy
          · rw [sigma.symm_apply_apply]
      · simp

  have h1 : Omega.card = Subsets.card * r := by
    rw [card_eq_sum_card_fiberwise (fun pi _ => hf pi)]
    trans Subsets.sum (fun _ => r)
    · apply sum_congr rfl
      intro S hS; exact hr S hS
    · simp [sum_const]

  have h2 : (Omega.filter (fun pi => P (f pi))).card = (Subsets.filter P).card * r := by
    have h_maps : ∀ pi ∈ Omega.filter (fun pi => P (f pi)), f pi ∈ Subsets.filter P := by
      intro pi hpi; simp only [mem_filter] at hpi ⊢; exact ⟨hf pi, hpi.2⟩
    rw [card_eq_sum_card_fiberwise h_maps]
    trans (Subsets.filter P).sum (fun _ => r)
    · apply sum_congr rfl
      intro S hS; simp only [mem_filter] at hS
      rw [show (Omega.filter (fun pi => P (f pi))).filter (fun pi => f pi = S) = Omega.filter (fun pi => f pi = S) by
        ext pi; simp; intro h_eq h_om; rw [h_eq]; exact hS.2]
      exact hr S hS.1
    · simp [sum_const]

  have h_subsets_card : Subsets.card = Nat.choose (m * m) k := by
    simp [Subsets, card_powersetCard, h_subsets_card_ambient]
  have h_omega_card : Omega.card = Fintype.card (Fin n ↪ U) := card_univ

  calc
    (univ.filter (fun (pi : Fin n ↪ U) => P (I.image pi))).card * Nat.choose (m * m) k
      = (Omega.filter (fun pi => P (f pi))).card * Nat.choose (m * m) k := rfl
    _ = (Subsets.filter P).card * r * Nat.choose (m * m) k := by rw [h2]
    _ = (Subsets.filter P).card * (Nat.choose (m * m) k * r) := by rw [mul_assoc, mul_comm r]
    _ = (Subsets.filter P).card * (Subsets.card * r) := by rw [h_subsets_card]
    _ = (Subsets.filter P).card * Omega.card := by rw [← h1]
    _ = (Subsets.filter P).card * Fintype.card (Fin n ↪ U) := by rw [h_omega_card]
    _ = (univ.filter (fun S => S.card = k ∧ P S)).card * Fintype.card (Fin n ↪ U) := by
      congr 1
      apply congr_arg Finset.card
      ext S
      simp [Subsets, mem_powersetCard, and_comm]
