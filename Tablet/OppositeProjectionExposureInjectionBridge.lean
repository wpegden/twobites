import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Tablet.OppositeProjectionEtaConditionedInjectionLawBridge

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionExposureInjectionBridge]

theorem OppositeProjectionExposureInjectionBridge (n m : ℕ) (p : ℝ)
    (U₀ V₀ : Finset (Fin n)) (t : ℕ)
    (G_R : SimpleGraph (Fin m)) (ρ : Fin n → Fin m) (η : U₀ → Fin m) :
    let S := Finset.univ.image η
    let X_all_eta :=
      Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
        (∀ v : Fin n, (ϕ v).1 = ρ v) ∧
          (fun u : U₀ => (ϕ u.1).2) = η) Finset.univ
    let X_good_eta := fun T : Finset (Fin n) =>
      Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
        ∀ v ∈ T, (ϕ v).2 ∈ S) X_all_eta
    TwoBiteConditionalProbability n m p
      (fun ω => (V₀.filter (fun v => (ω.2.2 v).2 ∈ S)).card ≥ t)
      (fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
        (fun u : U₀ => (ω.2.2 u.1).2) = η)
      ≤ ∑ T ∈ Finset.powersetCard t V₀,
          ((X_good_eta T).card : ℝ) / (X_all_eta.card : ℝ) := by
-- BODY
  intro S X_all_eta X_good_eta
  let condition : TwoBiteSample n m p → Prop := fun ω =>
    ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
      (fun u : U₀ => (ω.2.2 u.1).2) = η
  let tailP : (Fin n ↪ Fin m × Fin m) → Prop := fun ϕ =>
    (V₀.filter (fun v => (ϕ v).2 ∈ S)).card ≥ t
  let X_tail := Finset.filter tailP X_all_eta
  have hden :
      TwoBiteEventProbability n m p condition =
        GnpGraphWeight p G_R * UniformInjectionWeight n m *
          (X_all_eta.card : ℝ) := by
    simpa [condition, X_all_eta] using
      (OppositeProjectionEtaConditionedInjectionLawBridge
        n m p U₀ G_R ρ η (fun _ : Fin n ↪ Fin m × Fin m => True))
  have hnum :
      TwoBiteEventProbability n m p
          (fun ω => tailP ω.2.2 ∧ condition ω) =
        GnpGraphWeight p G_R * UniformInjectionWeight n m *
          (X_tail.card : ℝ) := by
    let X_tail0 :=
      Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m => tailP ϕ)
        (Finset.filter (fun ϕ : Fin n ↪ Fin m × Fin m =>
          (∀ v : Fin n, (ϕ v).1 = ρ v) ∧
            (fun u : U₀ => (ϕ u.1).2) = η) Finset.univ)
    have hnum0 :
        TwoBiteEventProbability n m p
            (fun ω => tailP ω.2.2 ∧
              (ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
                (fun u : U₀ => (ω.2.2 u.1).2) = η)) =
          GnpGraphWeight p G_R * UniformInjectionWeight n m *
            (X_tail0.card : ℝ) := by
      convert
        (OppositeProjectionEtaConditionedInjectionLawBridge
          n m p U₀ G_R ρ η tailP) using 1
      congr 1
      norm_cast
      apply congrArg Finset.card
      ext ϕ
      simp [tailP, X_tail0, ge_iff_le]
    have hXtail0 : X_tail0 = X_tail := by
      simp [X_tail0, X_tail, X_all_eta]
    simpa [condition, hXtail0] using hnum0
  have hrhs_nonneg :
      0 ≤ ∑ T ∈ Finset.powersetCard t V₀,
          ((X_good_eta T).card : ℝ) / (X_all_eta.card : ℝ) := by
    refine Finset.sum_nonneg ?_
    intro T hT
    by_cases hzero : (X_all_eta.card : ℝ) = 0
    · simp [hzero]
    · exact div_nonneg (by positivity)
        (le_of_lt (lt_of_le_of_ne (by positivity) (Ne.symm hzero)))
  have hcard_ratio :
      0 < (X_all_eta.card : ℝ) →
      ((X_tail.card : ℝ) / (X_all_eta.card : ℝ) ≤
        ∑ T ∈ Finset.powersetCard t V₀,
          ((X_good_eta T).card : ℝ) / (X_all_eta.card : ℝ)) := by
    intro hall_pos
    have hall_nonneg : 0 ≤ (X_all_eta.card : ℝ) := le_of_lt hall_pos
    have htail_subset :
        X_tail ⊆ (Finset.powersetCard t V₀).biUnion X_good_eta := by
      intro ϕ hϕ
      have hϕ_all : ϕ ∈ X_all_eta := (Finset.mem_filter.mp hϕ).1
      have htail : t ≤ (V₀.filter (fun v => (ϕ v).2 ∈ S)).card :=
        (Finset.mem_filter.mp hϕ).2
      obtain ⟨T, hTsub, hTcard⟩ :=
        Finset.exists_subset_card_eq htail
      have hTpow : T ∈ Finset.powersetCard t V₀ := by
        exact Finset.mem_powersetCard.mpr
          ⟨fun v hv => (Finset.mem_filter.mp (hTsub hv)).1, hTcard⟩
      have hϕ_good : ϕ ∈ X_good_eta T := by
        dsimp [X_good_eta]
        refine Finset.mem_filter.mpr ⟨hϕ_all, ?_⟩
        intro v hv
        exact (Finset.mem_filter.mp (hTsub hv)).2
      exact Finset.mem_biUnion.mpr ⟨T, hTpow, hϕ_good⟩
    have htail_card_le_union :
        X_tail.card ≤ ((Finset.powersetCard t V₀).biUnion X_good_eta).card :=
      Finset.card_le_card htail_subset
    have hunion_card_le_sum :
        ((Finset.powersetCard t V₀).biUnion X_good_eta).card ≤
          ∑ T ∈ Finset.powersetCard t V₀, (X_good_eta T).card :=
      Finset.card_biUnion_le
    have htail_card_le_sum :
        X_tail.card ≤
          ∑ T ∈ Finset.powersetCard t V₀, (X_good_eta T).card :=
      le_trans htail_card_le_union hunion_card_le_sum
    have htail_card_le_sum_real :
        (X_tail.card : ℝ) ≤
          ((∑ T ∈ Finset.powersetCard t V₀, (X_good_eta T).card : ℕ) : ℝ) := by
      exact_mod_cast htail_card_le_sum
    have hdiv :
        (X_tail.card : ℝ) / (X_all_eta.card : ℝ) ≤
          ((∑ T ∈ Finset.powersetCard t V₀, (X_good_eta T).card : ℕ) : ℝ) /
            (X_all_eta.card : ℝ) :=
      div_le_div_of_nonneg_right htail_card_le_sum_real hall_nonneg
    have hsum_div :
        ((∑ T ∈ Finset.powersetCard t V₀, (X_good_eta T).card : ℕ) : ℝ) /
            (X_all_eta.card : ℝ) =
          ∑ T ∈ Finset.powersetCard t V₀,
            ((X_good_eta T).card : ℝ) / (X_all_eta.card : ℝ) := by
      rw [Nat.cast_sum, Finset.sum_div]
    exact hdiv.trans_eq hsum_div
  change
    TwoBiteConditionalProbability n m p (fun ω => tailP ω.2.2) condition ≤
      ∑ T ∈ Finset.powersetCard t V₀,
        ((X_good_eta T).card : ℝ) / (X_all_eta.card : ℝ)
  unfold TwoBiteConditionalProbability
  by_cases hzero : TwoBiteEventProbability n m p condition = 0
  · simp [hzero, hrhs_nonneg]
  · simp [hzero]
    let C : ℝ := GnpGraphWeight p G_R * UniformInjectionWeight n m
    have hdenC :
        TwoBiteEventProbability n m p condition =
          C * (X_all_eta.card : ℝ) := by
      simpa [C, mul_assoc] using hden
    have hnumC :
        TwoBiteEventProbability n m p
            (fun ω => tailP ω.2.2 ∧ condition ω) =
          C * (X_tail.card : ℝ) := by
      simpa [C, mul_assoc] using hnum
    have hC_all_ne : C * (X_all_eta.card : ℝ) ≠ 0 := by
      rw [← hdenC]
      exact hzero
    have hC_ne : C ≠ 0 := (mul_ne_zero_iff.mp hC_all_ne).1
    have hall_ne : (X_all_eta.card : ℝ) ≠ 0 :=
      (mul_ne_zero_iff.mp hC_all_ne).2
    have hall_pos : 0 < (X_all_eta.card : ℝ) :=
      lt_of_le_of_ne (by positivity) (Ne.symm hall_ne)
    rw [hnumC, hdenC]
    have hcancel :
        (C * (X_tail.card : ℝ)) / (C * (X_all_eta.card : ℝ)) =
          (X_tail.card : ℝ) / (X_all_eta.card : ℝ) := by
      field_simp [hC_ne, hall_ne]
    rw [hcancel]
    exact hcard_ratio hall_pos
