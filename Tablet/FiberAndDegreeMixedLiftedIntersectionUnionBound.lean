import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteSample
import Tablet.WithHighProbability
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.GraphDegreeCount
import Tablet.FiberAndDegreeMixedLiftedIntersectionUniformBound
import Tablet.FiberAndDegreeMixedLiftedIntersectionConditioning
import Tablet.TwoBiteSampleWeightNonnegative

-- [TABLET NODE: FiberAndDegreeMixedLiftedIntersectionUnionBound]

theorem FiberAndDegreeMixedLiftedIntersectionUnionBound (n m : ℕ) (p : ℝ)
    (hm : m = TwoBiteNaturalReducedVertexCount n)
    (hp : p = TwoBiteEdgeProbability (1 / 2 : ℝ) n)
    (h_support : n ≤ m * m)
    (h_log : 1 ≤ Real.log (n : ℝ)) :
    TwoBiteEventProbability n m p (fun ω => 
      ¬ (∀ r b : Fin m, ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩ TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) ≤ 100 * (Real.log (n : ℝ)) ^ 3))
    ≤ TwoBiteEventProbability n m p (fun ω => 
        ¬ ((∀ r : Fin m, (GraphDegreeCount ω.1 r : ℝ) ≤ 2 * p * (m : ℝ)) ∧
           (∀ b : Fin m, (GraphDegreeCount ω.2.1 b : ℝ) ≤ 2 * p * (m : ℝ))))
      + (m : ℝ)^2 * Real.exp (- 2 * (Real.log (n : ℝ))^3) := by
-- BODY
  classical
  let BadMixed : TwoBiteSample n m p → Prop := fun ω =>
    ¬ (∀ r b : Fin m,
      ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
        TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) ≤
          100 * (Real.log (n : ℝ)) ^ 3)
  let ExMixed : TwoBiteSample n m p → Prop := fun ω =>
    ∃ r b : Fin m,
      ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
        TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ) >
          100 * (Real.log (n : ℝ)) ^ 3
  let GoodDeg : TwoBiteSample n m p → Prop := fun ω =>
    (∀ r : Fin m, (GraphDegreeCount ω.1 r : ℝ) ≤ 2 * p * (m : ℝ)) ∧
    (∀ b : Fin m, (GraphDegreeCount ω.2.1 b : ℝ) ≤ 2 * p * (m : ℝ))
  let BadDeg : TwoBiteSample n m p → Prop := fun ω => ¬ GoodDeg ω
  let C : ℝ := (m : ℝ)^2 * Real.exp (- 2 * (Real.log (n : ℝ))^3)
  have hn_ne_zero : n ≠ 0 := by
    intro hn
    subst n
    norm_num at h_log
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn_ne_zero
  have hp0 : 0 ≤ p := by
    rw [hp, TwoBiteEdgeProbability]
    positivity
  have hp1 : p ≤ 1 := by
    have hlog_le_n : Real.log (n : ℝ) ≤ (n : ℝ) :=
      Real.log_le_self (Nat.cast_nonneg n)
    have hdiv_le_one : Real.log (n : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn_pos]
      exact hlog_le_n
    have hdiv_le_four : Real.log (n : ℝ) / (n : ℝ) ≤ 4 := by linarith
    rw [hp, TwoBiteEdgeProbability]
    calc
      (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ) / (n : ℝ))
          ≤ (1 / 2 : ℝ) * Real.sqrt 4 := by
            apply mul_le_mul_of_nonneg_left
            · exact Real.sqrt_le_sqrt hdiv_le_four
            · norm_num
      _ = 1 := by
            have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
              have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
              rw [h4, Real.sqrt_sq (by norm_num)]
            rw [hsqrt4]
            norm_num
  have hweight : ∀ ω : TwoBiteSample n m p, 0 ≤ TwoBiteSampleWeight ω := by
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hp0 hp1
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have prob_eq : ∀ E : TwoBiteSample n m p → Prop,
      TwoBiteEventProbability n m p E =
        ∑ ω, if E ω then TwoBiteSampleWeight ω else 0 := by
    intro E
    unfold TwoBiteEventProbability
    exact Finset.sum_filter _ _
  have prob_mono :
      ∀ {E F : TwoBiteSample n m p → Prop},
        (∀ ω, E ω → F ω) →
        TwoBiteEventProbability n m p E ≤ TwoBiteEventProbability n m p F := by
    intro E F hEF
    unfold TwoBiteEventProbability
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        exact hEF ω hω)
      (by
        intro ω _ _
        exact hweight ω)
  have prob_nonneg :
      ∀ E : TwoBiteSample n m p → Prop, 0 ≤ TwoBiteEventProbability n m p E := by
    intro E
    unfold TwoBiteEventProbability
    apply Finset.sum_nonneg
    intro ω _
    exact hweight ω
  have cond_mono :
      ∀ {E F Cond : TwoBiteSample n m p → Prop},
        (∀ ω, E ω → F ω) →
        TwoBiteConditionalProbability n m p E Cond ≤
          TwoBiteConditionalProbability n m p F Cond := by
    intro E F Cond hEF
    unfold TwoBiteConditionalProbability
    split_ifs with hzero
    · exact le_rfl
    · apply div_le_div_of_nonneg_right
      · apply prob_mono
        intro ω hω
        exact ⟨hEF ω hω.1, hω.2⟩
      · exact prob_nonneg Cond
  have bad_to_ex : ∀ ω, BadMixed ω → ExMixed ω := by
    intro ω hω
    dsimp [BadMixed, ExMixed] at hω ⊢
    simpa only [not_forall, not_le] using hω
  have hsplit :
      TwoBiteEventProbability n m p BadMixed ≤
        TwoBiteEventProbability n m p BadDeg +
          TwoBiteEventProbability n m p (fun ω => BadMixed ω ∧ GoodDeg ω) := by
    rw [prob_eq BadMixed, prob_eq BadDeg, prob_eq (fun ω => BadMixed ω ∧ GoodDeg ω),
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    by_cases hA : BadMixed ω <;> by_cases hB : GoodDeg ω
    all_goals simp [BadDeg, hA, hB, hweight ω]
  have hcond :
      TwoBiteEventProbability n m p (fun ω => BadMixed ω ∧ GoodDeg ω) ≤ C := by
    refine FiberAndDegreeMixedLiftedIntersectionConditioning n m p
      (fun ω => BadMixed ω ∧ GoodDeg ω) C hC hweight ?_
    intro G_R G_B
    let Cell : TwoBiteSample n m p → Prop := fun ω => ω.1 = G_R ∧ ω.2.1 = G_B
    by_cases hgoodGB :
        (∀ r : Fin m, (GraphDegreeCount G_R r : ℝ) ≤ 2 * p * (m : ℝ)) ∧
        (∀ b : Fin m, (GraphDegreeCount G_B b : ℝ) ≤ 2 * p * (m : ℝ))
    · have hdeg :
          ∀ r b : Fin m,
            ((Finset.univ.filter (G_R.Adj r)).card : ℝ) ≤ 2 * p * (m : ℝ) ∧
            ((Finset.univ.filter (G_B.Adj b)).card : ℝ) ≤ 2 * p * (m : ℝ) := by
        intro r b
        constructor
        · simpa [GraphDegreeCount] using hgoodGB.1 r
        · simpa [GraphDegreeCount] using hgoodGB.2 b
      have hunif :=
        FiberAndDegreeMixedLiftedIntersectionUniformBound n m p hm hp h_support h_log
          G_R G_B hdeg
      exact le_trans
        (cond_mono (E := fun ω => BadMixed ω ∧ GoodDeg ω) (F := ExMixed)
          (Cond := Cell) (by
            intro ω hω
            exact bad_to_ex ω hω.1))
        (by
          simpa [ExMixed, Cell, C] using hunif)
    · have hempty :
          ∀ ω : TwoBiteSample n m p,
            (BadMixed ω ∧ GoodDeg ω) ∧ Cell ω → False := by
        intro ω hω
        have hfixed : GoodDeg ω := hω.1.2
        have hcell : Cell ω := hω.2
        have hgoodGB' :
            (∀ r : Fin m, (GraphDegreeCount G_R r : ℝ) ≤ 2 * p * (m : ℝ)) ∧
            (∀ b : Fin m, (GraphDegreeCount G_B b : ℝ) ≤ 2 * p * (m : ℝ)) := by
          constructor
          · intro r
            simpa [Cell, hcell.1] using hfixed.1 r
          · intro b
            simpa [Cell, hcell.2] using hfixed.2 b
        exact hgoodGB hgoodGB'
      unfold TwoBiteConditionalProbability
      split_ifs with hzero
      · exact hC
      · have hnum_zero :
            TwoBiteEventProbability n m p
              (fun ω => (BadMixed ω ∧ GoodDeg ω) ∧ Cell ω) = 0 := by
          unfold TwoBiteEventProbability
          apply Finset.sum_eq_zero
          intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
          exact False.elim (hempty ω hω)
        rw [hnum_zero]
        simp [hC]
  dsimp [BadMixed, BadDeg, GoodDeg, C] at hsplit hcond ⊢
  linarith
