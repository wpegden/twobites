import Tablet.TwoBiteConditionalProbability
import Tablet.OppositeProjectionRowInjectionCounting
import Tablet.OppositeProjectionRowInjectionLawBridge

-- [TABLET NODE: OppositeProjectionRowInjectionLaw]

open scoped Classical

theorem OppositeProjectionRowInjectionLaw (n m : ℕ) (p : ℝ)
    (G_R : SimpleGraph (Fin m)) (ρ : Fin n → Fin m)
    (S : Finset (Fin m)) (T : Finset (Fin n)) :
    TwoBiteConditionalProbability n m p
      (fun ω => ∀ v ∈ T, (ω.2.2 v).2 ∈ S)
      (fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ)
    ≤ ((S.card : ℝ) / (m : ℝ)) ^ T.card := by
-- BODY
  unfold TwoBiteConditionalProbability
  split_ifs with h_zero
  · positivity
  · let X_all := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => ∀ v, (ϕ v).1 = ρ v) Finset.univ
    let X_good := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => ∀ v ∈ T, (ϕ v).2 ∈ S) X_all
    have h_bridge := OppositeProjectionRowInjectionLawBridge n m p G_R ρ S T
    have h_count := OppositeProjectionRowInjectionCounting n m ρ S T
    rw [h_bridge.1, h_bridge.2]
    have h_ne_zero : (X_all.card : ℝ) ≠ 0 := by
      intro hc
      have h1 : GnpGraphWeight p G_R * UniformInjectionWeight n m * ↑(X_all.card) = 0 := by
        rw [hc]
        ring
      rw [← h_bridge.1] at h1
      exact h_zero h1
    have h_cancel : (GnpGraphWeight p G_R * UniformInjectionWeight n m * (X_good.card : ℝ)) /
      (GnpGraphWeight p G_R * UniformInjectionWeight n m * (X_all.card : ℝ)) =
      (X_good.card : ℝ) / (X_all.card : ℝ) := by
      have h_w_ne_zero : GnpGraphWeight p G_R * UniformInjectionWeight n m ≠ 0 := by
        intro hc
        have h1 : GnpGraphWeight p G_R * UniformInjectionWeight n m * ↑(X_all.card) = 0 := by
          rw [hc]
          ring
        rw [← h_bridge.1] at h1
        exact h_zero h1
      rw [mul_div_mul_left (X_good.card : ℝ) (X_all.card : ℝ) h_w_ne_zero]
    rw [h_cancel]
    exact h_count h_ne_zero

