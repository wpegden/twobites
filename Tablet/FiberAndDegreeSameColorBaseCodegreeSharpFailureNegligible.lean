import Tablet.NegligibleProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEventProbabilityNonnegative
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.UniformInjectionWeight
import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.TwoBiteNaturalTotalMassOneEventually
import Tablet.OppositeProjectionChooseExponentialBound
import Tablet.TwoBiteEventProbabilityUnionBound
import Tablet.GnpCodegreeBound
import Tablet.TwoBiteRedMarginal
import Tablet.TwoBiteBlueMarginal
import Tablet.SameColorCodegreeLimitBound

open Classical Filter Topology

-- [TABLET NODE: FiberAndDegreeSameColorBaseCodegreeSharpFailureNegligible]

theorem FiberAndDegreeSameColorBaseCodegreeSharpFailureNegligible :
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        NegligibleProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                ¬ (((∀ r s : Fin (m n), r ≠ s →
                      ((Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) ∧
                    (∀ b c : Fin (m n), b ≠ c →
                      ((Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ Real.log (n : ℝ)))))) := by
-- BODY
  intro β hβ m hm
  subst β
  have h_neg_le : ∀ᶠ n in atTop,
    TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability (1/2:ℝ) n)
      (fun ω =>
        ¬ (((∀ r s : Fin (m n), r ≠ s →
              ((Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) ∧
            (∀ b c : Fin (m n), b ≠ c →
              ((Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ Real.log (n : ℝ))))) ≤
    2 * (m n : ℝ)^2 * ((Nat.choose (m n) ⌈Real.log (n : ℝ)⌉₊ : ℝ) *
          ((TwoBiteEdgeProbability (1 / 2 : ℝ) n) ^ 2) ^ ⌈Real.log (n : ℝ)⌉₊) := by
    filter_upwards [TwoBiteNaturalTotalMassOneEventually (1/2:ℝ) rfl m hm, OppositeProjectionEdgeProbBounds] with n hn hp
    let p := TwoBiteEdgeProbability (1/2:ℝ) n
    let T := ⌈Real.log (n : ℝ)⌉₊
    let RedBad := fun ω : TwoBiteSample n (m n) p => ∃ r s : Fin (m n), r ≠ s ∧ Real.log (n:ℝ) < (Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card
    let BlueBad := fun ω : TwoBiteSample n (m n) p => ∃ b c : Fin (m n), b ≠ c ∧ Real.log (n:ℝ) < (Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card
    have heq : (fun ω => ¬ (((∀ r s : Fin (m n), r ≠ s →
                      ((Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) ∧
                    (∀ b c : Fin (m n), b ≠ c →
                      ((Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ Real.log (n : ℝ))))) =
               (fun ω => RedBad ω ∨ BlueBad ω) := by
      funext ω; apply propext
      rw [not_and_or]
      apply or_congr
      · rw [not_forall]; apply exists_congr; intro r
        rw [not_forall]; apply exists_congr; intro s
        rw [Classical.not_imp]; apply and_congr Iff.rfl
        exact not_le
      · rw [not_forall]; apply exists_congr; intro b
        rw [not_forall]; apply exists_congr; intro c
        rw [Classical.not_imp]; apply and_congr Iff.rfl
        exact not_le
    rw [heq]
    
    have h_or_le : TwoBiteEventProbability n (m n) p (fun ω => RedBad ω ∨ BlueBad ω) ≤ TwoBiteEventProbability n (m n) p RedBad + TwoBiteEventProbability n (m n) p BlueBad := by
      let E_or (b : Bool) := cond b RedBad BlueBad
      have h_or : (fun ω => RedBad ω ∨ BlueBad ω) = (fun ω => ∃ b : Bool, E_or b ω) := by
        funext ω; apply propext; constructor
        · rintro (hA | hB)
          · exact ⟨true, hA⟩
          · exact ⟨false, hB⟩
        · rintro ⟨b, h⟩
          · cases b
            · exact Or.inr h
            · exact Or.inl h
      rw [h_or]
      have h_bound := TwoBiteEventProbabilityUnionBound hp.1 hp.2 E_or
      have h_sum : (∑ b : Bool, TwoBiteEventProbability n (m n) p (E_or b)) = 
        TwoBiteEventProbability n (m n) p RedBad + TwoBiteEventProbability n (m n) p BlueBad := by
        exact Fintype.sum_bool _
      rwa [h_sum] at h_bound

    have h_red_le : TwoBiteEventProbability n (m n) p RedBad ≤ (m n : ℝ)^2 * ((Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T) := by
      let E_red (pair : Fin (m n) × Fin (m n)) (ω : TwoBiteSample n (m n) p) := pair.1 ≠ pair.2 ∧ T ≤ (Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj pair.1 t ∧ (TwoBiteRedGraph ω).Adj pair.2 t)).card
      have h_red_le1 : TwoBiteEventProbability n (m n) p RedBad ≤ TwoBiteEventProbability n (m n) p (fun ω => ∃ r s : Fin (m n), E_red (r, s) ω) := by
        unfold TwoBiteEventProbability
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
          rcases hω with ⟨r, s, h_neq, h_lt⟩
          exact ⟨r, s, h_neq, Nat.ceil_le.mpr h_lt.le⟩
        · intro ω _ _
          exact TwoBiteSampleWeightNonnegative ω hp.1 hp.2
      have h_sum_le : TwoBiteEventProbability n (m n) p (fun ω => ∃ r s : Fin (m n), E_red (r, s) ω) ≤ ∑ pair : Fin (m n) × Fin (m n), TwoBiteEventProbability n (m n) p (E_red pair) := by
        have h_eq_red : (fun ω => ∃ r s : Fin (m n), E_red (r, s) ω) = (fun ω => ∃ pair : Fin (m n) × Fin (m n), E_red pair ω) := by
          funext ω; apply propext; simp
        rw [h_eq_red]
        exact TwoBiteEventProbabilityUnionBound hp.1 hp.2 E_red
      have h_bound : ∀ pair : Fin (m n) × Fin (m n), TwoBiteEventProbability n (m n) p (E_red pair) ≤ (Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T := by
        intro pair
        by_cases h_eq : pair.1 = pair.2
        · have h_zero : TwoBiteEventProbability n (m n) p (E_red pair) = 0 := by
            unfold TwoBiteEventProbability
            apply Finset.sum_eq_zero
            intro ω hω
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
            exact False.elim (hω.1 h_eq)
          rw [h_zero]
          exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sq_nonneg p) T)
        · have h_marg := TwoBiteRedMarginal n (m n) p hn.1 (fun G => pair.1 ≠ pair.2 ∧ T ≤ (Finset.univ.filter (fun t => G.Adj pair.1 t ∧ G.Adj pair.2 t)).card)
          have h_marg_simpl : TwoBiteEventProbability n (m n) p (E_red pair) = ∑ G : SimpleGraph (Fin (m n)), if T ≤ (Finset.univ.filter (fun t => G.Adj pair.1 t ∧ G.Adj pair.2 t)).card then GnpGraphWeight p G else 0 := by
            rw [h_marg]
            apply Finset.sum_congr rfl
            intro G _
            by_cases h_if : pair.1 ≠ pair.2 ∧ T ≤ (Finset.univ.filter (fun t => G.Adj pair.1 t ∧ G.Adj pair.2 t)).card
            · rw [if_pos h_if, if_pos h_if.2]
            · by_cases h_if2 : T ≤ (Finset.univ.filter (fun t => G.Adj pair.1 t ∧ G.Adj pair.2 t)).card
              · exact False.elim (h_if ⟨h_eq, h_if2⟩)
              · rw [if_neg h_if, if_neg h_if2]
          rw [h_marg_simpl]
          exact GnpCodegreeBound (m n) p hp.1 hp.2 pair.1 pair.2 h_eq T
      calc
        TwoBiteEventProbability n (m n) p RedBad ≤ TwoBiteEventProbability n (m n) p (fun ω => ∃ r s : Fin (m n), E_red (r, s) ω) := h_red_le1
        _ ≤ ∑ pair : Fin (m n) × Fin (m n), TwoBiteEventProbability n (m n) p (E_red pair) := h_sum_le
        _ ≤ ∑ _pair : Fin (m n) × Fin (m n), (Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T := Finset.sum_le_sum (fun pair _ => h_bound pair)
        _ = (m n : ℝ)^2 * ((Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T) := by simp [Fintype.card_prod, pow_two, mul_assoc]
    have h_blue_le : TwoBiteEventProbability n (m n) p BlueBad ≤ (m n : ℝ)^2 * ((Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T) := by
      let E_blue (pair : Fin (m n) × Fin (m n)) (ω : TwoBiteSample n (m n) p) := pair.1 ≠ pair.2 ∧ T ≤ (Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj pair.1 t ∧ (TwoBiteBlueGraph ω).Adj pair.2 t)).card
      have h_blue_le1 : TwoBiteEventProbability n (m n) p BlueBad ≤ TwoBiteEventProbability n (m n) p (fun ω => ∃ b c : Fin (m n), E_blue (b, c) ω) := by
        unfold TwoBiteEventProbability
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
          rcases hω with ⟨b, c, h_neq, h_lt⟩
          exact ⟨b, c, h_neq, Nat.ceil_le.mpr h_lt.le⟩
        · intro ω _ _
          exact TwoBiteSampleWeightNonnegative ω hp.1 hp.2
      have h_sum_le : TwoBiteEventProbability n (m n) p (fun ω => ∃ b c : Fin (m n), E_blue (b, c) ω) ≤ ∑ pair : Fin (m n) × Fin (m n), TwoBiteEventProbability n (m n) p (E_blue pair) := by
        have h_eq_blue : (fun ω => ∃ b c : Fin (m n), E_blue (b, c) ω) = (fun ω => ∃ pair : Fin (m n) × Fin (m n), E_blue pair ω) := by
          funext ω; apply propext; simp
        rw [h_eq_blue]
        exact TwoBiteEventProbabilityUnionBound hp.1 hp.2 E_blue
      have h_bound : ∀ pair : Fin (m n) × Fin (m n), TwoBiteEventProbability n (m n) p (E_blue pair) ≤ (Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T := by
        intro pair
        by_cases h_eq : pair.1 = pair.2
        · have h_zero : TwoBiteEventProbability n (m n) p (E_blue pair) = 0 := by
            unfold TwoBiteEventProbability
            apply Finset.sum_eq_zero
            intro ω hω
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
            exact False.elim (hω.1 h_eq)
          rw [h_zero]
          exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sq_nonneg p) T)
        · have h_marg := TwoBiteBlueMarginal n (m n) p hn.1 (fun G => pair.1 ≠ pair.2 ∧ T ≤ (Finset.univ.filter (fun t => G.Adj pair.1 t ∧ G.Adj pair.2 t)).card)
          have h_marg_simpl : TwoBiteEventProbability n (m n) p (E_blue pair) = ∑ G : SimpleGraph (Fin (m n)), if T ≤ (Finset.univ.filter (fun t => G.Adj pair.1 t ∧ G.Adj pair.2 t)).card then GnpGraphWeight p G else 0 := by
            rw [h_marg]
            apply Finset.sum_congr rfl
            intro G _
            by_cases h_if : pair.1 ≠ pair.2 ∧ T ≤ (Finset.univ.filter (fun t => G.Adj pair.1 t ∧ G.Adj pair.2 t)).card
            · rw [if_pos h_if, if_pos h_if.2]
            · by_cases h_if2 : T ≤ (Finset.univ.filter (fun t => G.Adj pair.1 t ∧ G.Adj pair.2 t)).card
              · exact False.elim (h_if ⟨h_eq, h_if2⟩)
              · rw [if_neg h_if, if_neg h_if2]
          rw [h_marg_simpl]
          exact GnpCodegreeBound (m n) p hp.1 hp.2 pair.1 pair.2 h_eq T
      calc
        TwoBiteEventProbability n (m n) p BlueBad ≤ TwoBiteEventProbability n (m n) p (fun ω => ∃ b c : Fin (m n), E_blue (b, c) ω) := h_blue_le1
        _ ≤ ∑ pair : Fin (m n) × Fin (m n), TwoBiteEventProbability n (m n) p (E_blue pair) := h_sum_le
        _ ≤ ∑ _pair : Fin (m n) × Fin (m n), (Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T := Finset.sum_le_sum (fun pair _ => h_bound pair)
        _ = (m n : ℝ)^2 * ((Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T) := by simp [Fintype.card_prod, pow_two, mul_assoc]
    calc TwoBiteEventProbability n (m n) p (fun ω => RedBad ω ∨ BlueBad ω) ≤ TwoBiteEventProbability n (m n) p RedBad + TwoBiteEventProbability n (m n) p BlueBad := h_or_le
      _ ≤ (m n : ℝ)^2 * ((Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T) + (m n : ℝ)^2 * ((Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T) := add_le_add h_red_le h_blue_le
      _ = 2 * (m n : ℝ)^2 * ((Nat.choose (m n) T : ℝ) * (p ^ 2) ^ T) := by ring
  
  have h_nonneg : ∀ᶠ n in atTop, 0 ≤ TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability (1/2:ℝ) n)
      (fun ω =>
        ¬ (((∀ r s : Fin (m n), r ≠ s →
              ((Finset.univ.filter (fun t => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ Real.log (n : ℝ)) ∧
            (∀ b c : Fin (m n), b ≠ c →
              ((Finset.univ.filter (fun t => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ Real.log (n : ℝ))))) := by
    filter_upwards [OppositeProjectionEdgeProbBounds] with n hp
    exact TwoBiteEventProbabilityNonnegative hp.1 hp.2 _
  
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (SameColorCodegreeLimitBound m hm) h_nonneg h_neg_le
