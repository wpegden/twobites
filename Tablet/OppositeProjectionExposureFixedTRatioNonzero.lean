import Tablet.OppositeProjectionRowInjectionCounting
import Tablet.OppositeProjectionExposureRowProductBound

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionExposureFixedTRatioNonzero]

theorem OppositeProjectionExposureFixedTRatioNonzero (n m : ℕ)
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
      ≤ ((S.card : ℝ) / (m : ℝ)) ^ T.card := by
-- BODY
  intro S X_all_eta X_good_eta hT hrows h_all_ne
  let R (i : Fin m) := Finset.filter (fun v : Fin n => ρ v = i) Finset.univ
  let rowSize (i : Fin m) := (T ∩ R i).card
  have h_product :
      (X_good_eta.card : ℝ) / (X_all_eta.card : ℝ)
        ≤ ∏ i : Fin m, ((S.card : ℝ) / (m : ℝ)) ^ rowSize i := by
    simpa [S, X_all_eta, X_good_eta, R, rowSize] using
      OppositeProjectionExposureRowProductBound n m U₀ V₀ T ρ η hT hrows h_all_ne
  have h_rows_as_filter :
      ∀ i : Fin m, T ∩ R i = Finset.filter (fun v : Fin n => ρ v = i) T := by
    intro i
    dsimp [R]
    ext v
    simp only [mem_inter, mem_filter, mem_univ, true_and]
  have h_row_sum : ∑ i : Fin m, rowSize i = T.card := by
    dsimp [rowSize]
    simp_rw [h_rows_as_filter]
    have h_fiber := Finset.sum_card_fiberwise_eq_card_filter T Finset.univ ρ
    have h_filter_univ :
        Finset.filter (fun v : Fin n => ρ v ∈ (Finset.univ : Finset (Fin m))) T = T := by
      ext v
      simp
    simpa [h_filter_univ] using h_fiber
  have h_pow :
      (∏ i : Fin m, ((S.card : ℝ) / (m : ℝ)) ^ rowSize i)
        = ((S.card : ℝ) / (m : ℝ)) ^ T.card := by
    calc
      (∏ i : Fin m, ((S.card : ℝ) / (m : ℝ)) ^ rowSize i)
          = ((S.card : ℝ) / (m : ℝ)) ^ (∑ i : Fin m, rowSize i) := by
            exact Finset.prod_pow_eq_pow_sum Finset.univ rowSize ((S.card : ℝ) / (m : ℝ))
      _ = ((S.card : ℝ) / (m : ℝ)) ^ T.card := by rw [h_row_sum]
  exact h_product.trans_eq h_pow
