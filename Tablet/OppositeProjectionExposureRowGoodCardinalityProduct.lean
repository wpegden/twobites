import Tablet.Preamble

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionExposureRowGoodCardinalityProduct]

theorem OppositeProjectionExposureRowGoodCardinalityProduct (n m : ℕ)
    (U₀ T : Finset (Fin n)) (ρ : Fin n → Fin m) (η : U₀ → Fin m) :
    let S := Finset.univ.image η
    let R := fun i : Fin m => Finset.filter (fun v : Fin n => ρ v = i) Finset.univ
    let X_all_eta :=
      Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
        (∀ v : Fin n, (ϕ v).1 = ρ v) ∧
          (fun u : U₀ => (ϕ u.1).2) = η) Finset.univ
    let X_good_eta :=
      Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
        ∀ v ∈ T, (ϕ v).2 ∈ S) X_all_eta
    let rowGood := fun i : Fin m =>
      (Finset.univ.filter (fun f : ({v : Fin n // v ∈ R i} → Fin m) =>
        Function.Injective f ∧
          (∀ u : U₀, ∀ h : (u.1 : Fin n) ∈ R i, f ⟨u.1, h⟩ = η u) ∧
          ∀ v : {v : Fin n // v ∈ R i}, (v.1 : Fin n) ∈ T → f v ∈ S)).card
    (X_good_eta.card : ℝ) = ∏ i : Fin m, (rowGood i : ℝ) := by
-- BODY
  intro S R X_all_eta X_good_eta rowGood
  let global := {ϕ : Fin n ↪ Fin m × Fin m //
    (∀ v : Fin n, (ϕ v).1 = ρ v) ∧
      (fun u : U₀ => (ϕ u.1).2) = η ∧
        ∀ v : Fin n, v ∈ T → (ϕ v).2 ∈ S}
  let row := fun i : Fin m => {f : ({v : Fin n // v ∈ R i} → Fin m) //
    Function.Injective f ∧
      (∀ u : U₀, ∀ h : (u.1 : Fin n) ∈ R i, f ⟨u.1, h⟩ = η u) ∧
        ∀ v : {v : Fin n // v ∈ R i}, (v.1 : Fin n) ∈ T → f v ∈ S}
  have h_global : (X_good_eta.card : ℝ) = (Fintype.card global : ℝ) := by
    have h_nat : X_good_eta.card = Fintype.card global := by
      dsimp [X_good_eta, X_all_eta, global]
      rw [Fintype.card_subtype]
      simp [Finset.filter_filter, and_assoc]
    exact_mod_cast h_nat
  have h_row : ∀ i : Fin m, (rowGood i : ℝ) = (Fintype.card (row i) : ℝ) := by
    intro i
    have h_nat : rowGood i = Fintype.card (row i) := by
      dsimp [rowGood, row]
      rw [Fintype.card_subtype]
    exact_mod_cast h_nat
  have h_equiv : Nonempty (global ≃ ∀ i : Fin m, row i) := by
    let toRow : global → ∀ i : Fin m, row i := fun ϕ i =>
      ⟨fun v => (ϕ.1 v.1).2, by
        constructor
        · intro v w h
          have hvρ : ρ v.1 = i := by
            have hv : v.1 ∈ Finset.filter (fun z : Fin n => ρ z = i) Finset.univ := by
              simpa [R] using v.2
            exact (Finset.mem_filter.mp hv).2
          have hwρ : ρ w.1 = i := by
            have hw : w.1 ∈ Finset.filter (fun z : Fin n => ρ z = i) Finset.univ := by
              simpa [R] using w.2
            exact (Finset.mem_filter.mp hw).2
          have hfst : (ϕ.1 v.1).1 = (ϕ.1 w.1).1 := by
            rw [ϕ.2.1 v.1, ϕ.2.1 w.1, hvρ, hwρ]
          have hpair : ϕ.1 v.1 = ϕ.1 w.1 := Prod.ext hfst h
          exact Subtype.ext (ϕ.1.injective hpair)
        · constructor
          · intro u _hmem
            exact congrFun ϕ.2.2.1 u
          · intro v hvT
            exact ϕ.2.2.2 v.1 hvT⟩
    let fromRow : (∀ i : Fin m, row i) → global := fun f =>
      ⟨⟨fun v => (ρ v, (f (ρ v)).1 ⟨v, by simp [R]⟩), by
          intro v w h
          have h1 : ρ v = ρ w := congrArg Prod.fst h
          have h2 : (f (ρ v)).1 ⟨v, by simp [R]⟩ =
              (f (ρ w)).1 ⟨w, by simp [R]⟩ := congrArg Prod.snd h
          have h3 :
              (⟨v, by simp [R, h1]⟩ : {z : Fin n // z ∈ R (ρ w)}) =
                ⟨w, by simp [R]⟩ := by
            apply (f (ρ w)).2.1
            have H :
                (f (ρ w)).1 (⟨v, by simp [R, h1]⟩ :
                    {z : Fin n // z ∈ R (ρ w)}) =
                  (f (ρ v)).1 ⟨v, by simp [R]⟩ := by
              revert h1
              generalize yw : ρ w = y
              intro h1
              subst h1
              rfl
            rw [H]
            exact h2
          exact congrArg Subtype.val h3⟩, by
        constructor
        · intro v
          rfl
        · constructor
          · funext u
            exact (f (ρ u.1)).2.2.1 u (by simp [R])
          · intro v hvT
            exact (f (ρ v)).2.2.2 ⟨v, by simp [R]⟩ hvT⟩
    exact ⟨{
      toFun := toRow
      invFun := fromRow
      left_inv := by
        intro ϕ
        apply Subtype.ext
        apply Function.Embedding.ext
        intro v
        dsimp [toRow, fromRow]
        change (ρ v, (ϕ.1 v).2) = ϕ.1 v
        exact Prod.ext (ϕ.2.1 v).symm rfl
      right_inv := by
        intro f
        funext i
        apply Subtype.ext
        funext vsub
        rcases vsub with ⟨v, hv⟩
        dsimp [toRow, fromRow]
        have hvρ : ρ v = i := by
          have hv' : v ∈ Finset.filter (fun z : Fin n => ρ z = i) Finset.univ := by
            simpa [R] using hv
          exact (Finset.mem_filter.mp hv').2
        cases hvρ
        rfl
    }⟩
  calc
    (X_good_eta.card : ℝ) = (Fintype.card global : ℝ) := h_global
    _ = (Fintype.card (∀ i : Fin m, row i) : ℝ) := by
      obtain ⟨e⟩ := h_equiv
      exact_mod_cast Fintype.card_congr e
    _ = ∏ i : Fin m, (Fintype.card (row i) : ℝ) := by
      exact_mod_cast (Fintype.card_pi : Fintype.card (∀ i : Fin m, row i) =
        ∏ i : Fin m, Fintype.card (row i))
    _ = ∏ i : Fin m, (rowGood i : ℝ) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [h_row i]
