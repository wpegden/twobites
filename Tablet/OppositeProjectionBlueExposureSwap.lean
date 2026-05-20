import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteSampleWeight

open scoped Classical
open Finset

-- [TABLET NODE: OppositeProjectionBlueExposureSwap]

theorem OppositeProjectionBlueExposureSwap (n m : ℕ) (p : ℝ)
    (U₀ V₀ : Finset (Fin n)) (t : ℕ)
    (G_B : SimpleGraph (Fin m)) (ρ : Fin n → Fin m) (η : U₀ → Fin m) :
    TwoBiteConditionalProbability n m p
      (fun ω => (V₀.filter (fun v => (ω.2.2 v).1 ∈ (Finset.univ.image η))).card ≥ t)
      (fun ω => ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ ∧
        (fun (u : U₀) => (ω.2.2 u.1).1) = η)
    =
    TwoBiteConditionalProbability n m p
      (fun ω => (V₀.filter (fun v => (ω.2.2 v).2 ∈ (Finset.univ.image η))).card ≥ t)
      (fun ω => ω.1 = G_B ∧ (fun v => (ω.2.2 v).1) = ρ ∧
        (fun (u : U₀) => (ω.2.2 u.1).2) = η) := by
-- BODY
  classical
  let swapEmbedding : (Fin n ↪ Fin m × Fin m) ≃ (Fin n ↪ Fin m × Fin m) :=
    { toFun := fun ϕ =>
        { toFun := fun v => ((ϕ v).2, (ϕ v).1)
          inj' := by
            intro a b h
            apply ϕ.injective
            exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h) }
      invFun := fun ϕ =>
        { toFun := fun v => ((ϕ v).2, (ϕ v).1)
          inj' := by
            intro a b h
            apply ϕ.injective
            exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h) }
      left_inv := by
        intro ϕ
        ext v <;> rfl
      right_inv := by
        intro ϕ
        ext v <;> rfl }
  let swapSample : TwoBiteSample n m p ≃ TwoBiteSample n m p :=
    { toFun := fun ω => (ω.2.1, (ω.1, swapEmbedding ω.2.2))
      invFun := fun ω => (ω.2.1, (ω.1, swapEmbedding ω.2.2))
      left_inv := by
        rintro ⟨G_R, G_B, ϕ⟩
        simp [swapEmbedding]
      right_inv := by
        rintro ⟨G_R, G_B, ϕ⟩
        simp [swapEmbedding] }
  have hweight_swap :
      ∀ ω : TwoBiteSample n m p,
        TwoBiteSampleWeight (swapSample ω) = TwoBiteSampleWeight ω := by
    rintro ⟨G_R, G_B, ϕ⟩
    dsimp [swapSample]
    unfold TwoBiteSampleWeight
    ring
  have hevent_swap :
      ∀ E : TwoBiteSample n m p → Prop,
        TwoBiteEventProbability n m p E =
          TwoBiteEventProbability n m p (fun ω => E (swapSample ω)) := by
    intro E
    unfold TwoBiteEventProbability
    rw [sum_filter, sum_filter]
    calc
      (∑ ω : TwoBiteSample n m p,
          if E ω then TwoBiteSampleWeight ω else (0 : ℝ))
          =
        ∑ ω : TwoBiteSample n m p,
          if E (swapSample ω) then TwoBiteSampleWeight (swapSample ω) else (0 : ℝ) := by
            exact (swapSample.sum_comp
              (fun ω : TwoBiteSample n m p =>
                if E ω then TwoBiteSampleWeight ω else (0 : ℝ))).symm
      _ =
        ∑ ω : TwoBiteSample n m p,
          if E (swapSample ω) then TwoBiteSampleWeight ω else (0 : ℝ) := by
            apply Finset.sum_congr rfl
            intro ω _
            by_cases hE : E (swapSample ω) <;> simp [hE, hweight_swap ω]
  let redEvent : TwoBiteSample n m p → Prop := fun ω =>
    (V₀.filter (fun v => (ω.2.2 v).2 ∈ (Finset.univ.image η))).card ≥ t
  let redCondition : TwoBiteSample n m p → Prop := fun ω =>
    ω.1 = G_B ∧ (fun v => (ω.2.2 v).1) = ρ ∧
      (fun (u : U₀) => (ω.2.2 u.1).2) = η
  let blueEvent : TwoBiteSample n m p → Prop := fun ω =>
    (V₀.filter (fun v => (ω.2.2 v).1 ∈ (Finset.univ.image η))).card ≥ t
  let blueCondition : TwoBiteSample n m p → Prop := fun ω =>
    ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ ∧
      (fun (u : U₀) => (ω.2.2 u.1).1) = η
  have hcond :
      TwoBiteEventProbability n m p redCondition =
        TwoBiteEventProbability n m p blueCondition := by
    have h := hevent_swap redCondition
    simpa [redCondition, blueCondition, swapSample, swapEmbedding] using h
  have hboth :
      TwoBiteEventProbability n m p (fun ω => redEvent ω ∧ redCondition ω) =
        TwoBiteEventProbability n m p (fun ω => blueEvent ω ∧ blueCondition ω) := by
    have h := hevent_swap (fun ω => redEvent ω ∧ redCondition ω)
    simpa [redEvent, redCondition, blueEvent, blueCondition, swapSample, swapEmbedding] using h
  change TwoBiteConditionalProbability n m p blueEvent blueCondition =
    TwoBiteConditionalProbability n m p redEvent redCondition
  unfold TwoBiteConditionalProbability
  rw [← hcond, ← hboth]
