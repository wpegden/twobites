import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteSampleWeight

-- [TABLET NODE: TwoBiteConditionalIntersectionBound]

theorem TwoBiteConditionalIntersectionBound :
    ∀ {n m : ℕ} {p cellBound condBound : ℝ}
      {event condition : TwoBiteSample n m p → Prop},
      (∀ ω : TwoBiteSample n m p, 0 ≤ TwoBiteSampleWeight ω) →
      0 ≤ cellBound →
      0 ≤ condBound →
      TwoBiteEventProbability n m p condition ≤ cellBound →
      TwoBiteConditionalProbability n m p event condition ≤ condBound →
      TwoBiteEventProbability n m p (fun ω => event ω ∧ condition ω)
        ≤ cellBound * min (1 : ℝ) condBound := by
-- BODY
  intro n m p cellBound condBound event condition hweight hcell_nonneg hcond_nonneg
    hcellBound hcondBound
  classical
  let prob : (TwoBiteSample n m p → Prop) → ℝ :=
    fun E => TwoBiteEventProbability n m p E
  have prob_nonneg :
      ∀ E : TwoBiteSample n m p → Prop, 0 ≤ prob E := by
    intro E
    unfold prob TwoBiteEventProbability
    exact Finset.sum_nonneg (by
      intro ω hω
      exact hweight ω)
  have prob_mono :
      ∀ {A B : TwoBiteSample n m p → Prop},
        (∀ ω, A ω → B ω) → prob A ≤ prob B := by
    intro A B hAB
    unfold prob TwoBiteEventProbability
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        exact hAB ω hω)
      (by
        intro ω hωB hωnotA
        exact hweight ω)
  have hInterCell : prob (fun ω => event ω ∧ condition ω) ≤ prob condition :=
    prob_mono (by intro ω hω; exact hω.2)
  have hmin_nonneg : 0 ≤ min (1 : ℝ) condBound :=
    le_min zero_le_one hcond_nonneg
  have hInter_le_cell_min :
      prob (fun ω => event ω ∧ condition ω) ≤
        prob condition * min (1 : ℝ) condBound := by
    by_cases hzero : prob condition = 0
    · have hInter_nonneg : 0 ≤ prob (fun ω => event ω ∧ condition ω) :=
        prob_nonneg _
      have hInter_le_zero : prob (fun ω => event ω ∧ condition ω) ≤ 0 := by
        simpa [hzero] using hInterCell
      have hInter_eq_zero :
          prob (fun ω => event ω ∧ condition ω) = 0 :=
        le_antisymm hInter_le_zero hInter_nonneg
      simp [hInter_eq_zero, hzero]
    · have hprob_pos : 0 < prob condition :=
        lt_of_le_of_ne (prob_nonneg condition) (Ne.symm hzero)
      have hdiv :
          prob (fun ω => event ω ∧ condition ω) / prob condition ≤ condBound := by
        simpa [prob, TwoBiteConditionalProbability, hzero] using hcondBound
      have hInter_le_cond :
          prob (fun ω => event ω ∧ condition ω) ≤
            prob condition * condBound := by
        have htmp :
            prob (fun ω => event ω ∧ condition ω) ≤
              condBound * prob condition :=
          (div_le_iff₀ hprob_pos).mp hdiv
        simpa [mul_comm] using htmp
      by_cases hlarge : (1 : ℝ) ≤ condBound
      · have hmin : min (1 : ℝ) condBound = 1 := min_eq_left hlarge
        simpa [hmin] using hInterCell
      · have hcond_le_one : condBound ≤ 1 := le_of_not_ge hlarge
        have hmin : min (1 : ℝ) condBound = condBound := min_eq_right hcond_le_one
        simpa [hmin] using hInter_le_cond
  exact le_trans hInter_le_cell_min
    (mul_le_mul_of_nonneg_right hcellBound hmin_nonneg)
