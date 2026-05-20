import Tablet.Preamble
import Mathlib.Data.Fintype.CardEmbedding

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionRowInjectionAllCounting]

theorem OppositeProjectionRowInjectionAllCounting (n m : ℕ) (ρ : Fin n → Fin m) :
    let X_all := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => ∀ v, (ϕ v).1 = ρ v) Finset.univ;
    let R (i : Fin m) := Finset.filter (fun v => ρ v = i) Finset.univ;
    let q (i : Fin m) := (R i).card;
    (X_all.card : ℝ) = ∏ i : Fin m, (Nat.descFactorial m (q i) : ℝ) := by
-- BODY
  intro X_all R q
  have h1 : X_all.card = Fintype.card {ϕ : Fin n ↪ Fin m × Fin m // ∀ v, (ϕ v).1 = ρ v} := by
    change X_all.card = _
    exact (Fintype.card_of_subtype X_all (by intro x; simp [X_all])).symm
  let e : {ϕ : Fin n ↪ Fin m × Fin m // ∀ v, (ϕ v).1 = ρ v} ≃ (∀ i : Fin m, {v // ρ v = i} ↪ Fin m) := {
    toFun := fun ϕ i =>
      ⟨fun v => (ϕ.1 v.1).2, by
        intro v w h
        have h1 : (ϕ.1 v.1).1 = (ϕ.1 w.1).1 := by
          rw [ϕ.2 v.1, ϕ.2 w.1, v.2, w.2]
        have : ϕ.1 v.1 = ϕ.1 w.1 := Prod.ext h1 h
        exact Subtype.ext (ϕ.1.injective this)⟩
    invFun := fun f =>
      ⟨⟨fun v => (ρ v, (f (ρ v)) ⟨v, rfl⟩), by
        intro v w h
        have h1 : ρ v = ρ w := congrArg Prod.fst h
        have h2 : (f (ρ v)) ⟨v, rfl⟩ = (f (ρ w)) ⟨w, rfl⟩ := congrArg Prod.snd h
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
  have h2 : Fintype.card {ϕ : Fin n ↪ Fin m × Fin m // ∀ v, (ϕ v).1 = ρ v} = Fintype.card (∀ i : Fin m, {v // ρ v = i} ↪ Fin m) :=
    Fintype.card_congr e
  have h3 : Fintype.card (∀ i : Fin m, {v // ρ v = i} ↪ Fin m) = ∏ i : Fin m, Fintype.card ({v // ρ v = i} ↪ Fin m) :=
    Fintype.card_pi
  have h4 : ∀ i : Fin m, Fintype.card ({v // ρ v = i} ↪ Fin m) = Nat.descFactorial m (q i) := by
    intro i
    have hc : Fintype.card {v // ρ v = i} = q i := by
      change Fintype.card {v // ρ v = i} = (R i).card
      exact Fintype.card_of_subtype (R i) (by intro x; simp [R])
    have := @Fintype.card_embedding_eq {v // ρ v = i} (Fin m) _ _ _
    simp only [Fintype.card_fin] at this
    rw [hc] at this
    exact this
  rw [h1, h2, h3]
  push_cast
  apply prod_congr rfl
  intro i _
  rw [h4]
