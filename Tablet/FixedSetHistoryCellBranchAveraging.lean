import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative

-- [TABLET NODE: FixedSetHistoryCellBranchAveraging]

theorem FixedSetHistoryCellBranchAveraging :
    ∀ {n m : ℕ} {p B : ℝ}
      (hist fixedCount target : TwoBiteSample n m p → Prop)
      {Branch : Type} [Fintype Branch]
      (firstBranch : Branch → TwoBiteSample n m p → Prop),
      0 ≤ p →
      p ≤ 1 →
      0 ≤ B →
      (∀ ω : TwoBiteSample n m p, fixedCount ω → hist ω) →
      (∀ b : Branch, ∀ ω : TwoBiteSample n m p,
        firstBranch b ω → hist ω) →
      (∀ ω : TwoBiteSample n m p,
        hist ω → fixedCount ω → ∃ b : Branch, firstBranch b ω) →
      (∀ b c : Branch, b ≠ c →
        ∀ ω : TwoBiteSample n m p,
          ¬ (firstBranch b ω ∧ firstBranch c ω)) →
      (∀ b : Branch,
        TwoBiteEventProbability n m p
            (fun ω => target ω ∧ fixedCount ω ∧ firstBranch b ω)
          ≤ B * TwoBiteEventProbability n m p (firstBranch b)) →
      TwoBiteConditionalProbability n m p
          (fun ω => target ω ∧ fixedCount ω)
          hist
        ≤ B := by
-- BODY
  intro n m p B hist fixedCount target Branch _ firstBranch hp0 hp1 hB
    hFixedHist hBranchHist hCover hDisjoint hBranchBound
  classical
  let Ω := TwoBiteSample n m p
  let w : Ω → ℝ := fun ω => TwoBiteSampleWeight ω
  let prob : (Ω → Prop) → ℝ := fun E => TwoBiteEventProbability n m p E
  have hweight : ∀ ω : Ω, 0 ≤ w ω := by
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hp0 hp1
  have prob_eq_sum_if :
      ∀ E : Ω → Prop,
        prob E = (Finset.univ : Finset Ω).sum (fun ω => if E ω then w ω else 0) := by
    intro E
    unfold prob TwoBiteEventProbability
    rw [Finset.sum_filter]
  have prob_nonneg : ∀ E : Ω → Prop, 0 ≤ prob E := by
    intro E
    rw [prob_eq_sum_if E]
    exact Finset.sum_nonneg (by
      intro ω hω
      by_cases hE : E ω <;> simp [hE, hweight ω])
  have hnum_le_branch :
      prob (fun ω : Ω => (target ω ∧ fixedCount ω) ∧ hist ω) ≤
        (Finset.univ : Finset Branch).sum
          (fun b => prob (fun ω : Ω => target ω ∧ fixedCount ω ∧ firstBranch b ω)) := by
    rw [prob_eq_sum_if]
    calc
      _ ≤ (Finset.univ : Finset Ω).sum
              (fun ω =>
                (Finset.univ : Finset Branch).sum
                  (fun b => if target ω ∧ fixedCount ω ∧ firstBranch b ω then w ω else 0)) := by
            refine Finset.sum_le_sum ?_
            intro ω hω
            by_cases h : (target ω ∧ fixedCount ω) ∧ hist ω
            · rcases h with ⟨⟨htarget, hfixed⟩, hhist⟩
              rcases hCover ω hhist hfixed with ⟨b0, hb0⟩
              have hnonneg :
                  ∀ b ∈ (Finset.univ : Finset Branch),
                    0 ≤ (if target ω ∧ fixedCount ω ∧ firstBranch b ω then w ω else 0) := by
                intro b hb
                by_cases hb' : target ω ∧ fixedCount ω ∧ firstBranch b ω <;>
                  simp [hb', hweight ω]
              have hle :
                  w ω ≤ (Finset.univ : Finset Branch).sum
                    (fun b => if target ω ∧ fixedCount ω ∧ firstBranch b ω then w ω else 0) := by
                simpa [htarget, hfixed, hb0] using
                  (Finset.single_le_sum hnonneg (Finset.mem_univ b0))
              simpa [htarget, hfixed, hhist] using hle
            · have hsum_nonneg :
                  0 ≤ (Finset.univ : Finset Branch).sum
                    (fun b => if target ω ∧ fixedCount ω ∧ firstBranch b ω then w ω else 0) := by
                exact Finset.sum_nonneg (by
                  intro b hb
                  by_cases hb' : target ω ∧ fixedCount ω ∧ firstBranch b ω <;>
                    simp [hb', hweight ω])
              simpa [h] using hsum_nonneg
      _ = (Finset.univ : Finset Branch).sum
            (fun b => (Finset.univ : Finset Ω).sum
              (fun ω => if target ω ∧ fixedCount ω ∧ firstBranch b ω then w ω else 0)) := by
            rw [Finset.sum_comm]
      _ = (Finset.univ : Finset Branch).sum
            (fun b => prob (fun ω : Ω => target ω ∧ fixedCount ω ∧ firstBranch b ω)) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            rw [prob_eq_sum_if]
            refine Finset.sum_congr rfl ?_
            intro ω hω
            by_cases hE : target ω ∧ fixedCount ω ∧ firstBranch b ω <;> simp [hE]
  have hbranch_sum_le_den :
      (Finset.univ : Finset Branch).sum (fun b => prob (firstBranch b)) ≤ prob hist := by
    calc
      (Finset.univ : Finset Branch).sum (fun b => prob (firstBranch b))
          = (Finset.univ : Finset Branch).sum
              (fun b => (Finset.univ : Finset Ω).sum
                (fun ω => if firstBranch b ω then w ω else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            rw [prob_eq_sum_if]
      _ = (Finset.univ : Finset Ω).sum
            (fun ω => (Finset.univ : Finset Branch).sum
              (fun b => if firstBranch b ω then w ω else 0)) := by
            rw [Finset.sum_comm]
      _ ≤ (Finset.univ : Finset Ω).sum (fun ω => if hist ω then w ω else 0) := by
            refine Finset.sum_le_sum ?_
            intro ω hω
            by_cases hhist : hist ω
            · by_cases hex : ∃ b : Branch, firstBranch b ω
              · rcases hex with ⟨b0, hb0⟩
                have hsingle :
                    (Finset.univ : Finset Branch).sum
                      (fun b => if firstBranch b ω then w ω else 0) = w ω := by
                  have hsingle' :
                      (∑ b : Branch, if firstBranch b ω then w ω else 0) =
                        (if firstBranch b0 ω then w ω else 0) := by
                    refine Fintype.sum_eq_single b0 ?_
                    intro b hne
                    have hnot : ¬ firstBranch b ω := by
                      intro hb
                      exact hDisjoint b b0 hne ω ⟨hb, hb0⟩
                    simp [hnot]
                  simpa [hb0] using hsingle'
                simp [hhist, hsingle]
              · have hzero :
                    (Finset.univ : Finset Branch).sum
                      (fun b => if firstBranch b ω then w ω else 0) = 0 := by
                  refine Finset.sum_eq_zero ?_
                  intro b hb
                  have hnot : ¬ firstBranch b ω := by
                    intro hb'
                    exact hex ⟨b, hb'⟩
                  simp [hnot]
                simpa [hhist, hzero] using hweight ω
            · have hzero :
                  (Finset.univ : Finset Branch).sum
                    (fun b => if firstBranch b ω then w ω else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro b hb
                have hnot : ¬ firstBranch b ω := by
                  intro hb'
                  exact hhist (hBranchHist b ω hb')
                simp [hnot]
              simp [hhist, hzero]
      _ = prob hist := by
            rw [prob_eq_sum_if]
  have hnum_le :
      prob (fun ω : Ω => (target ω ∧ fixedCount ω) ∧ hist ω) ≤ B * prob hist := by
    calc
      prob (fun ω : Ω => (target ω ∧ fixedCount ω) ∧ hist ω)
          ≤ (Finset.univ : Finset Branch).sum
              (fun b => prob (fun ω : Ω => target ω ∧ fixedCount ω ∧ firstBranch b ω)) := hnum_le_branch
      _ ≤ (Finset.univ : Finset Branch).sum (fun b => B * prob (firstBranch b)) := by
            refine Finset.sum_le_sum ?_
            intro b hb
            exact hBranchBound b
      _ = B * (Finset.univ : Finset Branch).sum (fun b => prob (firstBranch b)) := by
            rw [Finset.mul_sum]
      _ ≤ B * prob hist := by
            exact mul_le_mul_of_nonneg_left hbranch_sum_le_den hB
  by_cases hden : prob hist = 0
  · simp [TwoBiteConditionalProbability, prob, hden, hB]
  · have hden_pos : 0 < prob hist :=
      lt_of_le_of_ne (prob_nonneg hist) (Ne.symm hden)
    have hquot :
        prob (fun ω : Ω => (target ω ∧ fixedCount ω) ∧ hist ω) / prob hist ≤ B :=
      (div_le_iff₀ hden_pos).2 hnum_le
    simpa [TwoBiteConditionalProbability, prob, hden] using hquot
