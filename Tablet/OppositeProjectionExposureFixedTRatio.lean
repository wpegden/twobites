import Tablet.OppositeProjectionRowInjectionCounting
import Tablet.OppositeProjectionExposureFixedTRatioNonzero

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionExposureFixedTRatio]

theorem OppositeProjectionExposureFixedTRatio (n m : ℕ)
    (U₀ V₀ T : Finset (Fin n)) (ρ : Fin n → Fin m) (η : U₀ → Fin m) :
    let S := Finset.univ.image η
    let X_all_eta :=
      Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
        (∀ v : Fin n, (ϕ v).1 = ρ v) ∧
          (fun u : U₀ => (ϕ u.1).2) = η) Finset.univ
    let X_good_eta :=
      Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
        ∀ v ∈ T, (ϕ v).2 ∈ S) X_all_eta
    T ⊆ V₀ →
    (∀ u : Fin n, u ∈ U₀ → ∀ v : Fin n, v ∈ V₀ → ρ u ≠ ρ v) →
    (X_good_eta.card : ℝ) / (X_all_eta.card : ℝ)
      ≤ ((S.card : ℝ) / (m : ℝ)) ^ T.card := by
-- BODY
  intro S X_all_eta X_good_eta hT hrows
  by_cases h_all_zero : X_all_eta.card = 0
  · have h_good_zero : X_good_eta.card = 0 := by
      have h_card_le : X_good_eta.card ≤ X_all_eta.card := by
        apply Finset.card_le_card
        intro ϕ hϕ
        simp [X_good_eta] at hϕ
        exact hϕ.1
      omega
    rw [h_good_zero, h_all_zero]
    simp
    positivity
  · have h_all_ne : (X_all_eta.card : ℝ) ≠ 0 := by
      exact_mod_cast h_all_zero
    exact OppositeProjectionExposureFixedTRatioNonzero n m U₀ V₀ T ρ η hT hrows h_all_ne
