import Tablet.OppositeProjectionRowInjectionCounting
import Tablet.OppositeProjectionExposureRowRatioWitness

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionExposureRowProductBound]

theorem OppositeProjectionExposureRowProductBound (n m : ℕ)
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
    (X_all_eta.card : ℝ) ≠ 0 →
    (X_good_eta.card : ℝ) / (X_all_eta.card : ℝ)
      ≤ ∏ i : Fin m,
          ((S.card : ℝ) / (m : ℝ)) ^
            ((T ∩ Finset.filter (fun v : Fin n => ρ v = i) Finset.univ).card) := by
-- BODY
  intro S X_all_eta X_good_eta hT hrows h_all_ne
  obtain ⟨h_all_factor, h_good_factor, h_row_ne, h_nonneg, h_bound, h_ratio⟩ :=
    OppositeProjectionExposureRowRatioWitness n m U₀ V₀ T ρ η hT hrows h_all_ne
  rw [h_ratio]
  apply Finset.prod_le_prod
  · intro i _
    exact h_nonneg i
  · intro i _
    exact h_bound i
