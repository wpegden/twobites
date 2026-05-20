import Tablet.TwoBiteConditionalProbability
import Tablet.OppositeProjectionRowInjectionCounting
import Tablet.TwoBiteSampleWeight
import Tablet.GnpGraphWeightSumOne

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionRowInjectionLawBridge]

theorem OppositeProjectionRowInjectionLawBridge (n m : ℕ) (p : ℝ)
    (G_R : SimpleGraph (Fin m)) (ρ : Fin n → Fin m)
    (S : Finset (Fin m)) (T : Finset (Fin n)) :
    let X_all := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => ∀ v, (ϕ v).1 = ρ v) Finset.univ;
    let X_good := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => ∀ v ∈ T, (ϕ v).2 ∈ S) X_all;
    TwoBiteEventProbability n m p (fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ) =
      GnpGraphWeight p G_R * UniformInjectionWeight n m * (X_all.card : ℝ) ∧
    TwoBiteEventProbability n m p (fun ω => (∀ v ∈ T, (ω.2.2 v).2 ∈ S) ∧ (ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ)) =
      GnpGraphWeight p G_R * UniformInjectionWeight n m * (X_good.card : ℝ) := by
-- BODY
  intro X_all X_good
  constructor
  · unfold TwoBiteEventProbability
    rw [sum_filter]
    simp_rw [TwoBiteSampleWeight]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    simp_rw [ite_and]
    have h1 : ∀ x, (∑ x_1 : SimpleGraph (Fin m), ∑ x_2 : Fin n ↪ Fin m × Fin m,
      if x = G_R then if (fun v => (x_2 v).1) = ρ then GnpGraphWeight p x * GnpGraphWeight p x_1 * UniformInjectionWeight n m else 0 else 0) =
      if x = G_R then ∑ x_1 : SimpleGraph (Fin m), ∑ x_2 : Fin n ↪ Fin m × Fin m, if (fun v => (x_2 v).1) = ρ then GnpGraphWeight p x * GnpGraphWeight p x_1 * UniformInjectionWeight n m else 0 else 0 := by
      intro x
      split_ifs
      · rfl
      · simp
    simp_rw [h1]
    simp
    have h2 : ∀ (x_1 : SimpleGraph (Fin m)) (x_2 : Fin n ↪ Fin m × Fin m), (if (fun v => (x_2 v).1) = ρ then GnpGraphWeight p G_R * GnpGraphWeight p x_1 * UniformInjectionWeight n m else (0 : ℝ)) =
      (if (fun v => (x_2 v).1) = ρ then UniformInjectionWeight n m else 0) * (GnpGraphWeight p G_R * GnpGraphWeight p x_1) := by
      intro x_1 x_2
      split_ifs
      · ring
      · ring
    simp_rw [h2]
    simp_rw [← Finset.sum_mul]
    have h3 : ∀ x : SimpleGraph (Fin m), (∑ i : Fin n ↪ Fin m × Fin m, if (fun v => (i v).1) = ρ then UniformInjectionWeight n m else (0 : ℝ)) *
      (GnpGraphWeight p G_R * GnpGraphWeight p x) =
      ((∑ i : Fin n ↪ Fin m × Fin m, if (fun v => (i v).1) = ρ then UniformInjectionWeight n m else (0 : ℝ)) * GnpGraphWeight p G_R) * GnpGraphWeight p x := by
      intro x
      ring
    simp_rw [h3]
    rw [← Finset.mul_sum]
    rw [GnpGraphWeightSumOne m p]
    have h4 : (∑ i : Fin n ↪ Fin m × Fin m, if (fun v => (i v).1) = ρ then UniformInjectionWeight n m else (0 : ℝ)) =
      X_all.card * UniformInjectionWeight n m := by
      have h_eq : ∀ i : Fin n ↪ Fin m × Fin m, ((fun v => (i v).1) = ρ) ↔ ∀ v, (i v).1 = ρ v := by
        intro i
        exact funext_iff
      simp_rw [h_eq]
      have h_sum : (∑ i : Fin n ↪ Fin m × Fin m, if ∀ (v : Fin n), (i v).1 = ρ v then UniformInjectionWeight n m else (0 : ℝ)) =
        ∑ i ∈ X_all, UniformInjectionWeight n m := by
        dsimp [X_all]
        rw [sum_filter]
      rw [h_sum]
      simp
    rw [h4]
    ring
  · unfold TwoBiteEventProbability
    rw [sum_filter]
    simp_rw [TwoBiteSampleWeight]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    simp_rw [ite_and]
    have h1 : ∀ x : SimpleGraph (Fin m), (∑ x_1 : SimpleGraph (Fin m), ∑ x_2 : Fin n ↪ Fin m × Fin m,
      if (∀ v ∈ T, (x_2 v).2 ∈ S) then if x = G_R then if (fun v => (x_2 v).1) = ρ then GnpGraphWeight p x * GnpGraphWeight p x_1 * UniformInjectionWeight n m else 0 else 0 else 0) =
      if x = G_R then ∑ x_1 : SimpleGraph (Fin m), ∑ x_2 : Fin n ↪ Fin m × Fin m, if (∀ v ∈ T, (x_2 v).2 ∈ S) ∧ (fun v => (x_2 v).1) = ρ then GnpGraphWeight p x * GnpGraphWeight p x_1 * UniformInjectionWeight n m else 0 else 0 := by
      intro x
      split_ifs
      · apply Finset.sum_congr rfl
        intro x_1 _
        apply Finset.sum_congr rfl
        intro x_2 _
        simp_rw [ite_and]
      · simp
    simp_rw [h1]
    simp
    have h2 : ∀ (x_1 : SimpleGraph (Fin m)) (x_2 : Fin n ↪ Fin m × Fin m), (if (∀ (v : Fin n) (_ : v ∈ T), (x_2 v).2 ∈ S) ∧ (fun v => (x_2 v).1) = ρ then GnpGraphWeight p G_R * GnpGraphWeight p x_1 * UniformInjectionWeight n m else (0 : ℝ)) =
      (if (∀ (v : Fin n) (_ : v ∈ T), (x_2 v).2 ∈ S) ∧ (fun v => (x_2 v).1) = ρ then UniformInjectionWeight n m else 0) * (GnpGraphWeight p G_R * GnpGraphWeight p x_1) := by
      intro x_1 x_2
      split_ifs
      · ring
      · ring
    simp_rw [h2]
    simp_rw [← Finset.sum_mul]
    have h3 : ∀ x : SimpleGraph (Fin m), (∑ i : Fin n ↪ Fin m × Fin m, if (∀ (v : Fin n) (_ : v ∈ T), (i v).2 ∈ S) ∧ (fun v => (i v).1) = ρ then UniformInjectionWeight n m else (0 : ℝ)) *
      (GnpGraphWeight p G_R * GnpGraphWeight p x) =
      ((∑ i : Fin n ↪ Fin m × Fin m, if (∀ (v : Fin n) (_ : v ∈ T), (i v).2 ∈ S) ∧ (fun v => (i v).1) = ρ then UniformInjectionWeight n m else (0 : ℝ)) * GnpGraphWeight p G_R) * GnpGraphWeight p x := by
      intro x
      ring
    simp_rw [h3]
    rw [← Finset.mul_sum]
    rw [GnpGraphWeightSumOne m p]
    have h4 : (∑ i : Fin n ↪ Fin m × Fin m, if (∀ (v : Fin n) (_ : v ∈ T), (i v).2 ∈ S) ∧ (fun v => (i v).1) = ρ then UniformInjectionWeight n m else (0 : ℝ)) =
      X_good.card * UniformInjectionWeight n m := by
      have h_eq : ∀ i : Fin n ↪ Fin m × Fin m, ((∀ (v : Fin n) (_ : v ∈ T), (i v).2 ∈ S) ∧ (fun v => (i v).1) = ρ) ↔ ((∀ (v : Fin n), (i v).1 = ρ v) ∧ ∀ v ∈ T, (i v).2 ∈ S) := by
        intro i
        have h_f : ((fun v => (i v).1) = ρ) ↔ (∀ v, (i v).1 = ρ v) := funext_iff
        rw [h_f, and_comm]
      simp_rw [h_eq]
      have h_sum : (∑ i : Fin n ↪ Fin m × Fin m, if (∀ (v : Fin n), (i v).1 = ρ v) ∧ ∀ (v : Fin n) (_ : v ∈ T), (i v).2 ∈ S then UniformInjectionWeight n m else (0 : ℝ)) =
        ∑ i ∈ X_good, UniformInjectionWeight n m := by
        dsimp [X_good, X_all]
        rw [sum_filter, sum_filter]
        simp_rw [ite_and]
      rw [h_sum]
      simp
    rw [h4]
    ring