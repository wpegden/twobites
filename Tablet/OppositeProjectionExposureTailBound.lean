import Tablet.TwoBiteConditionalProbability
import Tablet.OppositeProjectionRowInjectionLaw
import Tablet.OppositeProjectionWTailBound
import Tablet.OppositeProjectionExposureInjectionBridge
import Tablet.OppositeProjectionExposureFixedTRatio
import Mathlib.Data.Nat.Choose.Basic

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionExposureTailBound]

theorem OppositeProjectionExposureTailBound (n m : ℕ) (p : ℝ)
    (U₀ V₀ : Finset (Fin n)) (t : ℕ)
    (G_R : SimpleGraph (Fin m)) (ρ : Fin n → Fin m) (η : U₀ → Fin m)
    (hUV : ∀ v : Fin n, v ∈ U₀ → v ∈ V₀ → False)
    (hrows : ∀ u : Fin n, u ∈ U₀ → ∀ v : Fin n, v ∈ V₀ → ρ u ≠ ρ v) :
    TwoBiteConditionalProbability n m p
      (fun ω => (V₀.filter (fun v => (ω.2.2 v).2 ∈ (Finset.univ.image η))).card ≥ t)
      (fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧ (fun (u : U₀) => (ω.2.2 u.1).2) = η)
    ≤ (Nat.choose V₀.card t : ℝ) * (((Finset.univ.image η).card : ℝ) / (m : ℝ)) ^ t := by
-- BODY
  have _ := hUV
  let S := Finset.univ.image η
  let X_all_eta :=
    Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
      (∀ v : Fin n, (ϕ v).1 = ρ v) ∧
        (fun u : U₀ => (ϕ u.1).2) = η) Finset.univ
  let X_good_eta := fun T : Finset (Fin n) =>
    Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
      ∀ v ∈ T, (ϕ v).2 ∈ S) X_all_eta
  have h_bridge :
      TwoBiteConditionalProbability n m p
        (fun ω => (V₀.filter (fun v => (ω.2.2 v).2 ∈ S)).card ≥ t)
        (fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
          (fun u : U₀ => (ω.2.2 u.1).2) = η)
      ≤ ∑ T ∈ Finset.powersetCard t V₀,
          ((X_good_eta T).card : ℝ) / (X_all_eta.card : ℝ) := by
    simpa [S, X_all_eta, X_good_eta] using
      OppositeProjectionExposureInjectionBridge n m p U₀ V₀ t G_R ρ η
  have h_each :
      ∀ T ∈ Finset.powersetCard t V₀,
        ((X_good_eta T).card : ℝ) / (X_all_eta.card : ℝ)
          ≤ ((S.card : ℝ) / (m : ℝ)) ^ t := by
    intro T hT
    have hT_sub : T ⊆ V₀ := (Finset.mem_powersetCard.mp hT).1
    have hT_card : T.card = t := (Finset.mem_powersetCard.mp hT).2
    have h_ratio :=
      OppositeProjectionExposureFixedTRatio n m U₀ V₀ T ρ η hT_sub hrows
    simpa [S, X_all_eta, X_good_eta, hT_card] using h_ratio
  have h_sum_le :
      (∑ T ∈ Finset.powersetCard t V₀,
          ((X_good_eta T).card : ℝ) / (X_all_eta.card : ℝ))
        ≤ ∑ T ∈ Finset.powersetCard t V₀,
          ((S.card : ℝ) / (m : ℝ)) ^ t := by
    apply Finset.sum_le_sum
    intro T hT
    exact h_each T hT
  have h_sum_eq :
      (∑ T ∈ Finset.powersetCard t V₀,
          ((S.card : ℝ) / (m : ℝ)) ^ t)
        = (Nat.choose V₀.card t : ℝ) * ((S.card : ℝ) / (m : ℝ)) ^ t := by
    rw [Finset.sum_const, Finset.card_powersetCard]
    exact nsmul_eq_mul (Nat.choose V₀.card t) (((S.card : ℝ) / (m : ℝ)) ^ t)
  calc
    TwoBiteConditionalProbability n m p
        (fun ω => (V₀.filter (fun v => (ω.2.2 v).2 ∈ (Finset.univ.image η))).card ≥ t)
        (fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
          (fun u : U₀ => (ω.2.2 u.1).2) = η)
        ≤ ∑ T ∈ Finset.powersetCard t V₀,
            ((X_good_eta T).card : ℝ) / (X_all_eta.card : ℝ) := by
          simpa [S] using h_bridge
    _ ≤ ∑ T ∈ Finset.powersetCard t V₀,
          ((S.card : ℝ) / (m : ℝ)) ^ t := h_sum_le
    _ = (Nat.choose V₀.card t : ℝ) * ((S.card : ℝ) / (m : ℝ)) ^ t := h_sum_eq
    _ = (Nat.choose V₀.card t : ℝ) * (((Finset.univ.image η).card : ℝ) / (m : ℝ)) ^ t := by
          rfl
