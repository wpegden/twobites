import Tablet.TwoBiteConditionalProbability
import Tablet.OppositeProjectionRowInjectionLaw
import Tablet.OppositeProjectionRowInjectionLawBridge
import Tablet.OppositeProjectionRowInjectionCounting
import Tablet.GnpGraphWeightSumOne
import Mathlib.Algebra.BigOperators.Field

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionWTailBound]

theorem OppositeProjectionWTailBound (n m : ℕ) (p : ℝ)
    (G_R : SimpleGraph (Fin m)) (ρ : Fin n → Fin m)
    (S : Finset (Fin m)) (V₀ : Finset (Fin n)) (t : ℕ) :
    TwoBiteConditionalProbability n m p
      (fun ω => (V₀.filter (fun v => (ω.2.2 v).2 ∈ S)).card ≥ t)
      (fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ)
    ≤ (Nat.choose V₀.card t : ℝ) * ((S.card : ℝ) / (m : ℝ)) ^ t := by
-- BODY
  unfold TwoBiteConditionalProbability
  split_ifs with h_zero
  · positivity
  · let X_all := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => ∀ v, (ϕ v).1 = ρ v) Finset.univ
    let X_tail := Finset.filter (fun (ϕ : Fin n ↪ Fin m × Fin m) => (V₀.filter (fun v => (ϕ v).2 ∈ S)).card ≥ t) X_all
    have h_bridge1 := (OppositeProjectionRowInjectionLawBridge n m p G_R ρ S ∅).1
    have h_bridge2 : TwoBiteEventProbability n m p (fun ω => ((V₀.filter (fun v => (ω.2.2 v).2 ∈ S)).card ≥ t) ∧ (ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ)) =
      GnpGraphWeight p G_R * UniformInjectionWeight n m * (X_tail.card : ℝ) := by
      unfold TwoBiteEventProbability
      rw [Finset.sum_filter]
      simp_rw [TwoBiteSampleWeight]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      simp_rw [ite_and]
      have h1 : ∀ x : SimpleGraph (Fin m), (∑ x_1 : SimpleGraph (Fin m), ∑ x_2 : Fin n ↪ Fin m × Fin m,
        if ((V₀.filter (fun v => (x_2 v).2 ∈ S)).card ≥ t) then if x = G_R then if (fun v => (x_2 v).1) = ρ then GnpGraphWeight p x * GnpGraphWeight p x_1 * UniformInjectionWeight n m else 0 else 0 else 0) =
        if x = G_R then ∑ x_1 : SimpleGraph (Fin m), ∑ x_2 : Fin n ↪ Fin m × Fin m, if ((V₀.filter (fun v => (x_2 v).2 ∈ S)).card ≥ t) ∧ (fun v => (x_2 v).1) = ρ then GnpGraphWeight p x * GnpGraphWeight p x_1 * UniformInjectionWeight n m else 0 else 0 := by
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
      have h2 : ∀ (x_1 : SimpleGraph (Fin m)) (x_2 : Fin n ↪ Fin m × Fin m), (if ((V₀.filter (fun v => (x_2 v).2 ∈ S)).card ≥ t) ∧ (fun v => (x_2 v).1) = ρ then GnpGraphWeight p G_R * GnpGraphWeight p x_1 * UniformInjectionWeight n m else (0 : ℝ)) =
        (if ((V₀.filter (fun v => (x_2 v).2 ∈ S)).card ≥ t) ∧ (fun v => (x_2 v).1) = ρ then UniformInjectionWeight n m else 0) * (GnpGraphWeight p G_R * GnpGraphWeight p x_1) := by
        intro x_1 x_2
        split_ifs
        · ring
        · ring
      simp_rw [h2]
      simp_rw [← Finset.sum_mul]
      have h3 : ∀ x : SimpleGraph (Fin m), (∑ i : Fin n ↪ Fin m × Fin m, if ((V₀.filter (fun v => (i v).2 ∈ S)).card ≥ t) ∧ (fun v => (i v).1) = ρ then UniformInjectionWeight n m else (0 : ℝ)) *
        (GnpGraphWeight p G_R * GnpGraphWeight p x) =
        ((∑ i : Fin n ↪ Fin m × Fin m, if ((V₀.filter (fun v => (i v).2 ∈ S)).card ≥ t) ∧ (fun v => (i v).1) = ρ then UniformInjectionWeight n m else (0 : ℝ)) * GnpGraphWeight p G_R) * GnpGraphWeight p x := by
        intro x
        ring
      simp_rw [h3]
      rw [← Finset.mul_sum]
      rw [GnpGraphWeightSumOne m p]
      have h4 : (∑ i : Fin n ↪ Fin m × Fin m, if ((V₀.filter (fun v => (i v).2 ∈ S)).card ≥ t) ∧ (fun v => (i v).1) = ρ then UniformInjectionWeight n m else (0 : ℝ)) =
        X_tail.card * UniformInjectionWeight n m := by
        have h_eq : ∀ i : Fin n ↪ Fin m × Fin m, (((V₀.filter (fun v => (i v).2 ∈ S)).card ≥ t) ∧ (fun v => (i v).1) = ρ) ↔ ((∀ (v : Fin n), (i v).1 = ρ v) ∧ ((V₀.filter (fun v => (i v).2 ∈ S)).card ≥ t)) := by
          intro i
          have h_f : ((fun v => (i v).1) = ρ) ↔ (∀ v, (i v).1 = ρ v) := funext_iff
          rw [h_f, and_comm]
        simp_rw [h_eq]
        have h_sum : (∑ i : Fin n ↪ Fin m × Fin m, if (∀ (v : Fin n), (i v).1 = ρ v) ∧ ((V₀.filter (fun v => (i v).2 ∈ S)).card ≥ t) then UniformInjectionWeight n m else (0 : ℝ)) =
          ∑ i ∈ X_tail, UniformInjectionWeight n m := by
          dsimp [X_tail, X_all]
          rw [Finset.sum_filter, Finset.sum_filter]
          simp_rw [ite_and]
        rw [h_sum]
        simp
      rw [h4]
      ring
    rw [h_bridge1, h_bridge2]
    
    have h_ne_zero : (X_all.card : ℝ) ≠ 0 := by
      intro hc
      have h1 : GnpGraphWeight p G_R * UniformInjectionWeight n m * ↑(X_all.card) = 0 := by
        rw [hc]
        ring
      rw [← h_bridge1] at h1
      exact h_zero h1
      
    have h_cancel : (GnpGraphWeight p G_R * UniformInjectionWeight n m * (X_tail.card : ℝ)) /
      (GnpGraphWeight p G_R * UniformInjectionWeight n m * (X_all.card : ℝ)) =
      (X_tail.card : ℝ) / (X_all.card : ℝ) := by
      have h_w_ne_zero : GnpGraphWeight p G_R * UniformInjectionWeight n m ≠ 0 := by
        intro hc
        have h1 : GnpGraphWeight p G_R * UniformInjectionWeight n m * ↑(X_all.card) = 0 := by
          rw [hc]
          ring
        rw [← h_bridge1] at h1
        exact h_zero h1
      rw [mul_div_mul_left (X_tail.card : ℝ) (X_all.card : ℝ) h_w_ne_zero]
    rw [h_cancel]
    
    let Subsets := Finset.filter (fun T => T.card = t) V₀.powerset
    let X_good (T : Finset (Fin n)) := Finset.filter (fun ϕ => ∀ v ∈ T, (ϕ v).2 ∈ S) X_all
    
    have h_union : X_tail ⊆ Finset.biUnion Subsets X_good := by
      intro ϕ hϕ
      simp only [X_tail, mem_filter] at hϕ
      have h_ge : t ≤ (V₀.filter (fun v => (ϕ v).2 ∈ S)).card := hϕ.2
      obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq h_ge
      simp only [Subsets, mem_biUnion, mem_filter, mem_powerset]
      use T
      refine ⟨⟨?_, hT_card⟩, ?_⟩
      · intro v hv
        have hv_f := hT_sub hv
        simp only [mem_filter] at hv_f
        exact hv_f.1
      · simp only [X_good, mem_filter]
        refine ⟨hϕ.1, ?_⟩
        intro v hv
        have hv_f := hT_sub hv
        simp only [mem_filter] at hv_f
        exact hv_f.2

    have h_card_le : (X_tail.card : ℝ) ≤ ∑ T ∈ Subsets, ((X_good T).card : ℝ) := by
      have h1 := Finset.card_le_card h_union
      have h2 : (Finset.biUnion Subsets X_good).card ≤ ∑ T ∈ Subsets, (X_good T).card := Finset.card_biUnion_le
      have h3 : X_tail.card ≤ ∑ T ∈ Subsets, (X_good T).card := le_trans h1 h2
      have h4 : (X_tail.card : ℝ) ≤ ((∑ T ∈ Subsets, (X_good T).card : ℕ) : ℝ) := Nat.cast_le.mpr h3
      rw [Nat.cast_sum] at h4
      exact h4

    have h_div_le : (X_tail.card : ℝ) / (X_all.card : ℝ) ≤ ∑ T ∈ Subsets, ((X_good T).card : ℝ) / (X_all.card : ℝ) := by
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right h_card_le (by positivity)
      
    have h_count := OppositeProjectionRowInjectionCounting n m ρ S
    
    have h_sum_le : (∑ T ∈ Subsets, ((X_good T).card : ℝ) / (X_all.card : ℝ)) ≤ ∑ T ∈ Subsets, (((S.card : ℝ) / (m : ℝ)) ^ t) := by
      apply Finset.sum_le_sum
      intro T hT
      simp only [Subsets, mem_filter, mem_powerset] at hT
      have hc := h_count T h_ne_zero
      rw [hT.2] at hc
      exact hc

    have h_sum_eq : (∑ T ∈ Subsets, (((S.card : ℝ) / (m : ℝ)) ^ t)) = (Subsets.card : ℝ) * (((S.card : ℝ) / (m : ℝ)) ^ t) := by
      rw [Finset.sum_const]
      have h : (Subsets.card • (((S.card : ℝ) / (m : ℝ)) ^ t)) = (Subsets.card : ℝ) * (((S.card : ℝ) / (m : ℝ)) ^ t) := by
        exact nsmul_eq_mul (Subsets.card) (((S.card : ℝ) / (m : ℝ)) ^ t)
      exact h
      
    have h_subsets_card : Subsets.card = Nat.choose V₀.card t := by
      have h1 : Subsets = Finset.powersetCard t V₀ := by
        exact Finset.powersetCard_eq_filter.symm
      rw [h1]
      exact Finset.card_powersetCard t V₀
      
    rw [h_subsets_card] at h_sum_eq
    
    calc
      (X_tail.card : ℝ) / (X_all.card : ℝ) ≤ ∑ T ∈ Subsets, ((X_good T).card : ℝ) / (X_all.card : ℝ) := h_div_le
      _ ≤ ∑ T ∈ Subsets, (((S.card : ℝ) / (m : ℝ)) ^ t) := h_sum_le
      _ = (Nat.choose V₀.card t : ℝ) * ((S.card : ℝ) / (m : ℝ)) ^ t := h_sum_eq
