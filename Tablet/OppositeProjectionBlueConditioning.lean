import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEventProbabilityTotalMassBound
import Tablet.TwoBiteSampleWeightNonnegative

-- [TABLET NODE: OppositeProjectionBlueConditioning]

theorem OppositeProjectionBlueConditioning (n m : ℕ) (p : ℝ)
    (event : TwoBiteSample n m p → Prop) (C : ℝ)
    (hC : 0 ≤ C) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (bound : ∀ (G_B : SimpleGraph (Fin m)) (ρ : Fin n → Fin m),
      TwoBiteConditionalProbability n m p event
        (fun ω => ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ) ≤ C) :
    TwoBiteEventProbability n m p event ≤ C := by
-- BODY
  classical
  let proj : TwoBiteSample n m p → SimpleGraph (Fin m) × (Fin n → Fin m) :=
    fun ω => (ω.2.1, fun v => (ω.2.2 v).2)
  have hweight : ∀ ω : TwoBiteSample n m p, 0 ≤ TwoBiteSampleWeight ω := by
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hp0 hp1

  have H_event_gen : ∀ E : TwoBiteSample n m p → Prop,
      TwoBiteEventProbability n m p E =
        ∑ val : SimpleGraph (Fin m) × (Fin n → Fin m),
          TwoBiteEventProbability n m p (fun ω => E ω ∧ proj ω = val) := by
    intro E
    unfold TwoBiteEventProbability
    have h_fib :=
      Finset.sum_fiberwise (Finset.filter E Finset.univ) proj
        (fun ω => TwoBiteSampleWeight ω)
    rw [← h_fib]
    refine Finset.sum_congr rfl (fun val _ => ?_)
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

  have H_event := H_event_gen event

  have H_total : TwoBiteEventProbability n m p (fun _ => True) =
      ∑ val : SimpleGraph (Fin m) × (Fin n → Fin m),
        TwoBiteEventProbability n m p (fun ω => proj ω = val) := by
    have h1 := H_event_gen (fun _ => True)
    rw [h1]
    refine Finset.sum_congr rfl (fun val _ => ?_)
    congr 1
    ext ω
    simp only [true_and]

  have H_cell : ∀ val : SimpleGraph (Fin m) × (Fin n → Fin m),
      TwoBiteEventProbability n m p (fun ω => event ω ∧ proj ω = val) ≤
        C * TwoBiteEventProbability n m p (fun ω => proj ω = val) := by
    intro val
    have hb := bound val.1 val.2
    have heq :
        (fun ω : TwoBiteSample n m p =>
          ω.2.1 = val.1 ∧ (fun v => (ω.2.2 v).2) = val.2) =
        (fun ω => proj ω = val) := by
      ext ω
      unfold proj
      rcases val with ⟨val1, val2⟩
      dsimp
      simp only [Prod.mk.injEq]
    rw [heq] at hb
    unfold TwoBiteConditionalProbability at hb
    split_ifs at hb with hzero
    · have h_le_zero :
          TwoBiteEventProbability n m p (fun ω => event ω ∧ proj ω = val) ≤ 0 := by
        have h_sum_le :
            TwoBiteEventProbability n m p (fun ω => event ω ∧ proj ω = val) ≤
              TwoBiteEventProbability n m p (fun ω => proj ω = val) := by
          unfold TwoBiteEventProbability
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ω hω
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
            exact hω.2
          · intro ω _ _
            exact hweight ω
        rw [hzero] at h_sum_le
        exact h_sum_le
      rw [hzero, mul_zero]
      exact h_le_zero
    · have h_pos : 0 < TwoBiteEventProbability n m p (fun ω => proj ω = val) := by
        have h_nonneg : 0 ≤ TwoBiteEventProbability n m p (fun ω => proj ω = val) := by
          unfold TwoBiteEventProbability
          apply Finset.sum_nonneg
          intro ω _
          exact hweight ω
        exact lt_of_le_of_ne h_nonneg (Ne.symm hzero)
      exact (div_le_iff₀ h_pos).mp hb

  rw [H_event]
  calc
    ∑ val : SimpleGraph (Fin m) × (Fin n → Fin m),
        TwoBiteEventProbability n m p (fun ω => event ω ∧ proj ω = val)
        ≤ ∑ val : SimpleGraph (Fin m) × (Fin n → Fin m),
            C * TwoBiteEventProbability n m p (fun ω => proj ω = val) := by
          apply Finset.sum_le_sum
          intro val _
          exact H_cell val
    _ = C * ∑ val : SimpleGraph (Fin m) × (Fin n → Fin m),
          TwoBiteEventProbability n m p (fun ω => proj ω = val) := by
          rw [← Finset.mul_sum]
    _ = C * TwoBiteEventProbability n m p (fun _ => True) := by
          rw [← H_total]
    _ ≤ C * 1 := by
          gcongr
          exact TwoBiteEventProbabilityTotalMassBound n m p
    _ = C := by ring
