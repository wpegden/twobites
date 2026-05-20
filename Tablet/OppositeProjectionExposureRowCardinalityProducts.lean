import Tablet.OppositeProjectionExposureRowAllCardinalityProduct
import Tablet.OppositeProjectionExposureRowGoodCardinalityProduct

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionExposureRowCardinalityProducts]

theorem OppositeProjectionExposureRowCardinalityProducts (n m : ℕ)
    (U₀ V₀ T : Finset (Fin n)) (ρ : Fin n → Fin m) (η : U₀ → Fin m) :
    let S := Finset.univ.image η
    let R := fun i : Fin m => Finset.filter (fun v : Fin n => ρ v = i) Finset.univ
    let X_all_eta :=
      Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
        (∀ v : Fin n, (ϕ v).1 = ρ v) ∧
          (fun u : U₀ => (ϕ u.1).2) = η) Finset.univ
    let X_good_eta :=
      Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
        ∀ v ∈ T, (ϕ v).2 ∈ S) X_all_eta
    let rowAll := fun i : Fin m =>
      (Finset.univ.filter (fun f : ({v : Fin n // v ∈ R i} → Fin m) =>
        Function.Injective f ∧
          ∀ u : U₀, ∀ h : (u.1 : Fin n) ∈ R i, f ⟨u.1, h⟩ = η u)).card
    let rowGood := fun i : Fin m =>
      (Finset.univ.filter (fun f : ({v : Fin n // v ∈ R i} → Fin m) =>
        Function.Injective f ∧
          (∀ u : U₀, ∀ h : (u.1 : Fin n) ∈ R i, f ⟨u.1, h⟩ = η u) ∧
          ∀ v : {v : Fin n // v ∈ R i}, (v.1 : Fin n) ∈ T → f v ∈ S)).card
    (X_all_eta.card : ℝ) = ∏ i : Fin m, (rowAll i : ℝ) ∧
    (X_good_eta.card : ℝ) = ∏ i : Fin m, (rowGood i : ℝ) := by
-- BODY
  intro S R X_all_eta X_good_eta rowAll rowGood
  have h_all :=
    OppositeProjectionExposureRowAllCardinalityProduct n m U₀ ρ η
  have h_good :=
    OppositeProjectionExposureRowGoodCardinalityProduct n m U₀ T ρ η
  exact ⟨h_all, h_good⟩
