import Tablet.OppositeProjectionExposureRowFactorizationIdentities
import Tablet.OppositeProjectionExposureRowQuotientBounds

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionExposureRowRatioWitness]

theorem OppositeProjectionExposureRowRatioWitness (n m : ℕ)
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
    T ⊆ V₀ →
    (∀ u : Fin n, u ∈ U₀ → ∀ v : Fin n, v ∈ V₀ → ρ u ≠ ρ v) →
    (X_all_eta.card : ℝ) ≠ 0 →
    (X_all_eta.card : ℝ) = ∏ i : Fin m, (rowAll i : ℝ) ∧
    (X_good_eta.card : ℝ) = ∏ i : Fin m, (rowGood i : ℝ) ∧
    (∀ i : Fin m, (rowAll i : ℝ) ≠ 0) ∧
    (∀ i : Fin m, 0 ≤ (rowGood i : ℝ) / (rowAll i : ℝ)) ∧
    (∀ i : Fin m,
      (rowGood i : ℝ) / (rowAll i : ℝ) ≤ ((S.card : ℝ) / (m : ℝ)) ^
        ((T ∩ R i).card)) ∧
    (X_good_eta.card : ℝ) / (X_all_eta.card : ℝ) =
      ∏ i : Fin m, (rowGood i : ℝ) / (rowAll i : ℝ) := by
-- BODY
  intro S R X_all_eta X_good_eta rowAll rowGood hT hrows h_all_ne
  obtain ⟨h_all_factor, h_good_factor, h_row_ne, h_ratio⟩ :=
    OppositeProjectionExposureRowFactorizationIdentities n m U₀ V₀ T ρ η h_all_ne
  obtain ⟨h_nonneg, h_bound⟩ :=
    OppositeProjectionExposureRowQuotientBounds n m U₀ V₀ T ρ η hT hrows h_row_ne
  exact ⟨h_all_factor, h_good_factor, h_row_ne, h_nonneg, h_bound, h_ratio⟩
