import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteSampleWeight
import Tablet.GnpGraphWeightSumOne

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionEtaConditionedInjectionLawBridge]

theorem OppositeProjectionEtaConditionedInjectionLawBridge (n m : ℕ) (p : ℝ)
    (U₀ : Finset (Fin n)) (G_R : SimpleGraph (Fin m))
    (ρ : Fin n → Fin m) (η : U₀ → Fin m)
    (P : (Fin n ↪ Fin m × Fin m) → Prop) :
    TwoBiteEventProbability n m p
      (fun ω => P ω.2.2 ∧
        (ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
          (fun u : U₀ => (ω.2.2 u.1).2) = η)) =
      GnpGraphWeight p G_R * UniformInjectionWeight n m *
        ((Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m => P ϕ)
          (Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
            (∀ v : Fin n, (ϕ v).1 = ρ v) ∧
              (fun u : U₀ => (ϕ u.1).2) = η) Finset.univ)).card : ℝ) := by
-- BODY
  unfold TwoBiteEventProbability
  rw [sum_filter]
  simp_rw [TwoBiteSampleWeight]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [ite_and]
  have h1 : ∀ x : SimpleGraph (Fin m),
      (∑ x_1 : SimpleGraph (Fin m), ∑ x_2 : Fin n ↪ Fin m × Fin m,
        if P x_2 then
          if x = G_R then
            if (fun v => (x_2 v).1) = ρ then
              if (fun u : U₀ => (x_2 u.1).2) = η then
                GnpGraphWeight p x * GnpGraphWeight p x_1 *
                  UniformInjectionWeight n m
              else 0
            else 0
          else 0
        else 0) =
      if x = G_R then
        ∑ x_1 : SimpleGraph (Fin m), ∑ x_2 : Fin n ↪ Fin m × Fin m,
          if P x_2 ∧ (fun v => (x_2 v).1) = ρ ∧
              (fun u : U₀ => (x_2 u.1).2) = η then
            GnpGraphWeight p x * GnpGraphWeight p x_1 *
              UniformInjectionWeight n m
          else 0
      else 0 := by
    intro x
    by_cases hx : x = G_R
    · simp [hx]
      apply Finset.sum_congr rfl
      intro x_1 _
      apply Finset.sum_congr rfl
      intro x_2 _
      by_cases hP : P x_2
      · by_cases hρ : (fun v => (x_2 v).1) = ρ
        · by_cases hη : (fun u : U₀ => (x_2 u.1).2) = η
          · simp [hP, hρ, hη]
          · simp [hP, hρ, hη]
        · simp [hP, hρ]
      · simp [hP]
    · simp [hx]
  simp_rw [h1]
  simp
  have h2 : ∀ (x_1 : SimpleGraph (Fin m)) (x_2 : Fin n ↪ Fin m × Fin m),
      (if P x_2 ∧ (fun v => (x_2 v).1) = ρ ∧
          (fun u : U₀ => (x_2 u.1).2) = η then
        GnpGraphWeight p G_R * GnpGraphWeight p x_1 *
          UniformInjectionWeight n m
      else (0 : ℝ)) =
      (if P x_2 ∧ (fun v => (x_2 v).1) = ρ ∧
          (fun u : U₀ => (x_2 u.1).2) = η then
        UniformInjectionWeight n m
      else 0) * (GnpGraphWeight p G_R * GnpGraphWeight p x_1) := by
    intro x_1 x_2
    split_ifs <;> ring
  simp_rw [h2]
  simp_rw [← Finset.sum_mul]
  have h3 : ∀ x : SimpleGraph (Fin m),
      (∑ i : Fin n ↪ Fin m × Fin m,
          if P i ∧ (fun v => (i v).1) = ρ ∧
              (fun u : U₀ => (i u.1).2) = η then
            UniformInjectionWeight n m
          else (0 : ℝ)) *
        (GnpGraphWeight p G_R * GnpGraphWeight p x) =
      ((∑ i : Fin n ↪ Fin m × Fin m,
          if P i ∧ (fun v => (i v).1) = ρ ∧
              (fun u : U₀ => (i u.1).2) = η then
            UniformInjectionWeight n m
          else (0 : ℝ)) * GnpGraphWeight p G_R) *
        GnpGraphWeight p x := by
    intro x
    ring
  simp_rw [h3]
  rw [← Finset.mul_sum]
  rw [GnpGraphWeightSumOne m p]
  have h4 :
      (∑ i : Fin n ↪ Fin m × Fin m,
          if P i ∧ (fun v => (i v).1) = ρ ∧
              (fun u : U₀ => (i u.1).2) = η then
            UniformInjectionWeight n m
          else (0 : ℝ)) =
        (Finset.filter (fun i : Fin n ↪ Fin m × Fin m => P i)
          (Finset.filter (fun i : Fin n ↪ Fin m × Fin m =>
            (∀ v : Fin n, (i v).1 = ρ v) ∧
              (fun u : U₀ => (i u.1).2) = η) Finset.univ)).card *
          UniformInjectionWeight n m := by
    have h_eq : ∀ i : Fin n ↪ Fin m × Fin m,
        (P i ∧ (fun v => (i v).1) = ρ ∧
            (fun u : U₀ => (i u.1).2) = η) ↔
          ((∀ v : Fin n, (i v).1 = ρ v) ∧
              (fun u : U₀ => (i u.1).2) = η) ∧ P i := by
      intro i
      have h_f : ((fun v => (i v).1) = ρ) ↔
          ∀ v : Fin n, (i v).1 = ρ v := funext_iff
      rw [h_f]
      constructor
      · rintro ⟨hP, hρ, hη⟩
        exact ⟨⟨hρ, hη⟩, hP⟩
      · rintro ⟨⟨hρ, hη⟩, hP⟩
        exact ⟨hP, hρ, hη⟩
    simp_rw [h_eq]
    have h_sum :
        (∑ i : Fin n ↪ Fin m × Fin m,
            if ((∀ v : Fin n, (i v).1 = ρ v) ∧
                (fun u : U₀ => (i u.1).2) = η) ∧ P i then
              UniformInjectionWeight n m
            else (0 : ℝ)) =
          ∑ i ∈ Finset.filter (fun i : Fin n ↪ Fin m × Fin m => P i)
              (Finset.filter (fun i : Fin n ↪ Fin m × Fin m =>
                (∀ v : Fin n, (i v).1 = ρ v) ∧
                  (fun u : U₀ => (i u.1).2) = η) Finset.univ),
            UniformInjectionWeight n m := by
      rw [sum_filter, sum_filter]
      simp_rw [ite_and]
    rw [h_sum]
    simp
  rw [h4]
  ring
