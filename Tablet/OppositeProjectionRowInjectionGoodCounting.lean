import Tablet.Preamble
import Mathlib.Data.Fintype.CardEmbedding
import Tablet.OppositeProjectionRowRestrictedCounting
import Tablet.OppositeProjectionRowInjectionAllCounting

open scoped Classical BigOperators
open Finset

-- [TABLET NODE: OppositeProjectionRowInjectionGoodCounting]

theorem OppositeProjectionRowInjectionGoodCounting (n m : ℕ) (ρ : Fin n → Fin m)
    (S : Finset (Fin m)) (T : Finset (Fin n)) :
    let X_all := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => ∀ v, (ϕ v).1 = ρ v) Finset.univ;
    let X_good := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => ∀ v ∈ T, (ϕ v).2 ∈ S) X_all;
    let R (i : Fin m) := Finset.filter (fun v => ρ v = i) Finset.univ;
    let q (i : Fin m) := (R i).card;
    let T_i (i : Fin m) := T ∩ R i;
    let h (i : Fin m) := (T_i i).card;
    (X_good.card : ℝ) = ∏ i : Fin m, ((Nat.descFactorial S.card (h i) : ℝ) * (Nat.descFactorial (m - h i) (q i - h i) : ℝ)) := by
-- BODY
  intro X_all X_good R q T_i h
  have h1 : X_good.card = Fintype.card {ϕ : Fin n ↪ Fin m × Fin m // (∀ v, (ϕ v).1 = ρ v) ∧ ∀ v ∈ T, (ϕ v).2 ∈ S} := by
    change X_good.card = _
    have eq1 : X_good = Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => (∀ v, (ϕ v).1 = ρ v) ∧ ∀ v ∈ T, (ϕ v).2 ∈ S) Finset.univ := by
      ext ϕ
      simp [X_good, X_all]
    rw [eq1]
    have eq2 : (Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => (∀ v, (ϕ v).1 = ρ v) ∧ ∀ v ∈ T, (ϕ v).2 ∈ S) Finset.univ).card = Fintype.card {ϕ : Fin n ↪ Fin m × Fin m // (∀ v, (ϕ v).1 = ρ v) ∧ ∀ v ∈ T, (ϕ v).2 ∈ S} := by
      exact (Fintype.card_of_subtype _ (by intro x; simp)).symm
    exact eq2

  let e_all : {ϕ : Fin n ↪ Fin m × Fin m // ∀ v, (ϕ v).1 = ρ v} ≃ (∀ i : Fin m, {v // ρ v = i} ↪ Fin m) := {
    toFun := fun ϕ i =>
      ⟨fun v => (ϕ.1 v.1).2, by
        intro v w h_eq
        have h1 : (ϕ.1 v.1).1 = (ϕ.1 w.1).1 := by
          rw [ϕ.2 v.1, ϕ.2 w.1, v.2, w.2]
        have : ϕ.1 v.1 = ϕ.1 w.1 := Prod.ext h1 h_eq
        exact Subtype.ext (ϕ.1.injective this)⟩
    invFun := fun f =>
      ⟨⟨fun v => (ρ v, (f (ρ v)) ⟨v, rfl⟩), by
        intro v w h_eq
        have h1 : ρ v = ρ w := congrArg Prod.fst h_eq
        have h2 : (f (ρ v)) ⟨v, rfl⟩ = (f (ρ w)) ⟨w, rfl⟩ := congrArg Prod.snd h_eq
        have h3 : (⟨v, h1⟩ : {z // ρ z = ρ w}) = ⟨w, rfl⟩ := by
          apply (f (ρ w)).injective
          have H : f (ρ w) ⟨v, h1⟩ = f (ρ v) ⟨v, rfl⟩ := by
            revert h1
            generalize yw : ρ w = y
            intro h1
            subst h1
            rfl
          rw [H]
          exact h2
        exact congrArg Subtype.val h3⟩, by
          intro v
          rfl⟩
    left_inv := by
      rintro ⟨ϕ, h_prop⟩
      apply Subtype.ext
      apply Function.Embedding.ext
      intro v
      apply Prod.ext
      · exact (h_prop v).symm
      · rfl
    right_inv := by
      intro f
      ext i ⟨v, hv⟩
      dsimp
      subst hv
      rfl
  }

  have e_good : {ϕ : Fin n ↪ Fin m × Fin m // (∀ v, (ϕ v).1 = ρ v) ∧ ∀ v ∈ T, (ϕ v).2 ∈ S} ≃
                {f : ∀ i, {v // ρ v = i} ↪ Fin m // ∀ i, ∀ v : {v // ρ v = i}, ↑v ∈ T → f i v ∈ S} := {
    toFun := fun ⟨ϕ, h_all, h_T⟩ =>
      ⟨e_all ⟨ϕ, h_all⟩, by
        intro i v hv
        have := h_T v.1 hv
        exact this⟩
    invFun := fun ⟨f, h_f⟩ =>
      ⟨(e_all.symm f).1, (e_all.symm f).2, by
        intro v hv
        let i := ρ v
        let v_sub : {z // ρ z = i} := ⟨v, rfl⟩
        have := h_f i v_sub hv
        have H1 : ((e_all.symm f).1 v).2 = f i v_sub := rfl
        rw [H1]
        exact this⟩
    left_inv := by
      rintro ⟨ϕ, h_all, h_T⟩
      apply Subtype.ext
      dsimp
      have := e_all.left_inv ⟨ϕ, h_all⟩
      exact congrArg Subtype.val this
    right_inv := by
      rintro ⟨f, h_f⟩
      apply Subtype.ext
      dsimp
      exact e_all.right_inv f
  }

  let e_pi := @Equiv.subtypePiEquivPi (Fin m) (fun i => {v // ρ v = i} ↪ Fin m) (fun i f_i => ∀ v : {v // ρ v = i}, ↑v ∈ T → f_i v ∈ S)
  let e_tot := e_good.trans e_pi

  have h2 : Fintype.card {ϕ : Fin n ↪ Fin m × Fin m // (∀ v, (ϕ v).1 = ρ v) ∧ ∀ v ∈ T, (ϕ v).2 ∈ S} =
            ∏ i : Fin m, Fintype.card {f : {v // ρ v = i} ↪ Fin m // ∀ v : {v // ρ v = i}, ↑v ∈ T → f v ∈ S} := by
    rw [Fintype.card_congr e_tot, Fintype.card_pi]

  have h3 : ∀ i, (Fintype.card {f : {v // ρ v = i} ↪ Fin m // ∀ v : {v // ρ v = i}, ↑v ∈ T → f v ∈ S} : ℝ) = (Nat.descFactorial S.card (h i) : ℝ) * (Nat.descFactorial (m - h i) (q i - h i) : ℝ) := by
    intro i
    let A := {v // ρ v = i}
    let Y := Fin m
    let B := Finset.filter (fun (v : A) => ↑v ∈ T) Finset.univ
    have h_card_B : B.card = h i := by
      change B.card = (T_i i).card
      have eq3 : Finset.map (Function.Embedding.subtype (fun v => ρ v = i)) B = T_i i := by
        ext x
        simp only [B, mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coe_subtype, T_i, R, mem_inter]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨hy, y.2⟩
        · intro hx
          exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
      rw [← eq3, Finset.card_map]
    
    have h_card_A : Fintype.card A = q i := by
      change Fintype.card {v // ρ v = i} = (R i).card
      have eqA : (R i).card = Fintype.card {v // ρ v = i} := by
        exact (Fintype.card_of_subtype (R i) (by intro x; simp [R])).symm
      exact eqA.symm
      
    have h_card_Y : Fintype.card Y = m := Fintype.card_fin m
    
    have H_inner : Fintype.card {f : A ↪ Y // ∀ v : A, ↑v ∈ T → f v ∈ S} = Fintype.card {f : A ↪ Y // ∀ a ∈ B, f a ∈ S} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro f
      constructor
      · intro hf a ha
        simp only [B, mem_filter, mem_univ, true_and] at ha
        exact hf a ha
      · intro hf a ha
        have ha_B : a ∈ B := by simp [B, ha]
        exact hf a ha_B
        
    have H_cnt : Fintype.card {f : A ↪ Y // ∀ a ∈ B, f a ∈ S} = (Finset.univ.filter (fun (f : A ↪ Y) => ∀ a ∈ B, f a ∈ S)).card := by
      exact Fintype.card_of_subtype _ (by intro x; simp)
    
    have H_rest := OppositeProjectionRowRestrictedCounting B S
    rw [H_cnt] at H_inner
    rw [H_inner]
    rw [H_rest]
    rw [h_card_B, h_card_A, h_card_Y]
    push_cast
    rfl

  rw [h1, h2]
  push_cast
  exact Finset.prod_congr rfl (fun i _ => h3 i)
