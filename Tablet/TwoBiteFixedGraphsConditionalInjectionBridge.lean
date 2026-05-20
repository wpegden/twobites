import Tablet.TwoBiteEventProbability
import Tablet.GnpGraphWeightSumOne
import Tablet.UniformInjectionWeight
import Tablet.TwoBiteConditionalProbability

open scoped Classical
open Finset

-- [TABLET NODE: TwoBiteFixedGraphsConditionalInjectionBridge]

theorem TwoBiteFixedGraphsConditionalInjectionBridge (n m : ℕ) (p : ℝ)
    (G_R G_B : SimpleGraph (Fin m))
    (P : (Fin n ↪ Fin m × Fin m) → Prop) :
    TwoBiteEventProbability n m p (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) =
      GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) ∧
    TwoBiteEventProbability n m p (fun ω => P ω.2.2 ∧ ω.1 = G_R ∧ ω.2.1 = G_B) =
      GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m * (Finset.univ.filter P).card := by
-- BODY
  have h_P : ∀ (Q : (Fin n ↪ Fin m × Fin m) → Prop),
    TwoBiteEventProbability n m p (fun ω => Q ω.2.2 ∧ ω.1 = G_R ∧ ω.2.1 = G_B) =
      GnpGraphWeight p G_R * GnpGraphWeight p G_B * UniformInjectionWeight n m * (Finset.univ.filter Q).card := by
    intro Q
    unfold TwoBiteEventProbability
    rw [sum_filter]
    simp_rw [TwoBiteSampleWeight]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    simp_rw [ite_and]
    have h1 : ∀ x : SimpleGraph (Fin m),
        (∑ x_1 : SimpleGraph (Fin m), ∑ x_2 : Fin n ↪ Fin m × Fin m,
          if Q x_2 then
            if x = G_R then
              if x_1 = G_B then
                GnpGraphWeight p x * GnpGraphWeight p x_1 * UniformInjectionWeight n m
              else 0
            else 0
          else 0) =
        if x = G_R then
          ∑ x_1 : SimpleGraph (Fin m), ∑ x_2 : Fin n ↪ Fin m × Fin m,
            if Q x_2 ∧ x_1 = G_B then
              GnpGraphWeight p x * GnpGraphWeight p x_1 * UniformInjectionWeight n m
            else 0
        else 0 := by
      intro x
      by_cases hx : x = G_R
      · simp [hx]
        apply Finset.sum_congr rfl
        intro x_1 _
        apply Finset.sum_congr rfl
        intro x_2 _
        by_cases hQ : Q x_2
        · by_cases hB : x_1 = G_B
          · simp [hQ, hB]
          · simp [hQ, hB]
        · simp [hQ]
      · simp [hx]
    simp_rw [h1]
    simp
    have h2 : ∀ x_1 x_2, (if Q x_2 ∧ x_1 = G_B then GnpGraphWeight p G_R * GnpGraphWeight p x_1 * UniformInjectionWeight n m else 0) =
      (if Q x_2 ∧ x_1 = G_B then UniformInjectionWeight n m else 0) * (GnpGraphWeight p G_R * GnpGraphWeight p x_1) := by
      intro x_1 x_2
      split_ifs <;> ring
    simp_rw [h2]
    simp_rw [← Finset.sum_mul]
    have h3 : (∑ x_1 : SimpleGraph (Fin m),
      (∑ x_2 : Fin n ↪ Fin m × Fin m, if Q x_2 ∧ x_1 = G_B then UniformInjectionWeight n m else (0 : ℝ)) *
        (GnpGraphWeight p G_R * GnpGraphWeight p x_1)) =
      ((∑ x_2 : Fin n ↪ Fin m × Fin m, if Q x_2 then UniformInjectionWeight n m else (0 : ℝ)) * GnpGraphWeight p G_B) * GnpGraphWeight p G_R := by
      have h_sum : (∑ x_1 : SimpleGraph (Fin m),
          (∑ x_2 : Fin n ↪ Fin m × Fin m, if Q x_2 ∧ x_1 = G_B then UniformInjectionWeight n m else (0 : ℝ)) *
            (GnpGraphWeight p G_R * GnpGraphWeight p x_1)) =
        ∑ x_1 : SimpleGraph (Fin m), if x_1 = G_B then
          (∑ x_2 : Fin n ↪ Fin m × Fin m, if Q x_2 then UniformInjectionWeight n m else (0 : ℝ)) *
            (GnpGraphWeight p G_R * GnpGraphWeight p x_1)
        else 0 := by
        apply Finset.sum_congr rfl
        intro x_1 _
        split_ifs with hB
        · rw [hB]
          have h_inner : (∑ x_2 : Fin n ↪ Fin m × Fin m, if Q x_2 ∧ G_B = G_B then UniformInjectionWeight n m else (0 : ℝ)) =
            ∑ x_2 : Fin n ↪ Fin m × Fin m, if Q x_2 then UniformInjectionWeight n m else (0 : ℝ) := by
            apply Finset.sum_congr rfl
            intro x_2 _
            simp
          rw [h_inner]
        · have h_inner : (∑ x_2 : Fin n ↪ Fin m × Fin m, if Q x_2 ∧ x_1 = G_B then UniformInjectionWeight n m else (0 : ℝ)) = 0 := by
            have h_eq_zero : ∀ x_2, (if Q x_2 ∧ x_1 = G_B then UniformInjectionWeight n m else (0 : ℝ)) = 0 := by
              intro x_2
              simp [hB]
            rw [Finset.sum_congr rfl (fun x _ => h_eq_zero x), Finset.sum_const_zero]
          rw [h_inner, zero_mul]
      rw [h_sum]
      rw [Finset.sum_eq_single_of_mem G_B (Finset.mem_univ G_B)]
      · simp; ring
      · intro b _ hneq
        simp [hneq]
    rw [h3]
    have h4 : (∑ x_2 : Fin n ↪ Fin m × Fin m, if Q x_2 then UniformInjectionWeight n m else (0 : ℝ)) =
      (Finset.univ.filter Q).card * UniformInjectionWeight n m := by
      have hr : (∑ x_2 : Fin n ↪ Fin m × Fin m, if Q x_2 then UniformInjectionWeight n m else (0 : ℝ)) =
        ∑ x_2 ∈ Finset.univ.filter Q, UniformInjectionWeight n m := by
        rw [sum_filter]
      rw [hr]
      simp
    rw [h4]
    ring
  constructor
  · have hTrue := h_P (fun _ => True)
    have h_eq : (fun ω : TwoBiteSample n m p => True ∧ ω.1 = G_R ∧ ω.2.1 = G_B) = (fun ω => ω.1 = G_R ∧ ω.2.1 = G_B) := by
      ext ω; simp
    rw [h_eq] at hTrue
    rw [hTrue]
    simp
  · exact h_P P
