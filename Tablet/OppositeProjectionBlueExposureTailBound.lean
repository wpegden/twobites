import Tablet.OppositeProjectionExposureTailBound
import Tablet.OppositeProjectionBlueExposureSwap
import Mathlib.Data.Nat.Choose.Basic

-- [TABLET NODE: OppositeProjectionBlueExposureTailBound]

theorem OppositeProjectionBlueExposureTailBound (n m : ℕ) (p : ℝ)
    (U₀ V₀ : Finset (Fin n)) (t : ℕ)
    (G_B : SimpleGraph (Fin m)) (ρ : Fin n → Fin m) (η : U₀ → Fin m)
    (hUV : ∀ v : Fin n, v ∈ U₀ → v ∈ V₀ → False)
    (hrows : ∀ u : Fin n, u ∈ U₀ → ∀ v : Fin n, v ∈ V₀ → ρ u ≠ ρ v) :
    TwoBiteConditionalProbability n m p
      (fun ω => (V₀.filter (fun v => (ω.2.2 v).1 ∈ (Finset.univ.image η))).card ≥ t)
      (fun ω => ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ ∧ (fun (u : U₀) => (ω.2.2 u.1).1) = η)
    ≤ (Nat.choose V₀.card t : ℝ) * (((Finset.univ.image η).card : ℝ) / (m : ℝ)) ^ t := by
-- BODY
  rw [OppositeProjectionBlueExposureSwap n m p U₀ V₀ t G_B ρ η]
  exact OppositeProjectionExposureTailBound n m p U₀ V₀ t G_B ρ η hUV hrows
