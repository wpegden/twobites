import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteSampleWeightNonnegative

-- [TABLET NODE: FixedSetHistoryCellBranchTranscriptSummation]

theorem FixedSetHistoryCellBranchTranscriptSummation :
    ∀ {n m : ℕ} {p M : ℝ}
      (base target : TwoBiteSample n m p → Prop)
      {Branch Support Transcript : Type}
      [Fintype Branch] [Fintype Support] [Fintype Transcript]
      (cellEvent :
        Branch → Support → Transcript → TwoBiteSample n m p → Prop)
      (weight : Branch → Support → Transcript → ℝ),
      0 ≤ p →
      p ≤ 1 →
      0 ≤ M →
      (∀ ω : TwoBiteSample n m p,
        target ω →
          base ω →
            ∃ b s t, cellEvent b s t ω) →
      (∀ b s t, 0 ≤ weight b s t) →
      (∀ b s t,
        TwoBiteEventProbability n m p
            (fun ω => target ω ∧ base ω ∧ cellEvent b s t ω)
          ≤ weight b s t) →
      ((Finset.univ : Finset Branch).sum
          (fun b =>
            (Finset.univ : Finset Support).sum
              (fun s =>
                (Finset.univ : Finset Transcript).sum
                  (fun t => weight b s t)))
        ≤ M) →
      TwoBiteEventProbability n m p (fun ω => target ω ∧ base ω)
        ≤ M := by
-- BODY
  classical
  intro n m p M base target Branch Support Transcript _ _ _ cellEvent weight
    hp0 hp1 _hM hcover hweight_nonneg hcell_bound hweight_sum
  let Ω := TwoBiteSample n m p
  let w : Ω → ℝ := fun ω => TwoBiteSampleWeight ω
  let prob : (Ω → Prop) → ℝ := fun E => TwoBiteEventProbability n m p E
  have hsample_nonneg : ∀ ω : Ω, 0 ≤ w ω := by
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hp0 hp1
  have hpoint :
      ∀ ω : Ω,
        (if target ω ∧ base ω then w ω else 0) ≤
          (Finset.univ : Finset Branch).sum
            (fun b =>
              (Finset.univ : Finset Support).sum
                (fun s =>
                  (Finset.univ : Finset Transcript).sum
                    (fun t =>
                      if target ω ∧ base ω ∧ cellEvent b s t ω then
                        w ω
                      else
                        0))) := by
    intro ω
    by_cases htb : target ω ∧ base ω
    · rcases hcover ω htb.1 htb.2 with ⟨b0, s0, t0, hcell0⟩
      have hcell_pred0 : target ω ∧ base ω ∧ cellEvent b0 s0 t0 ω := by
        exact ⟨htb.1, htb.2, hcell0⟩
      have ht_nonneg :
          ∀ t ∈ (Finset.univ : Finset Transcript),
            0 ≤
              (if target ω ∧ base ω ∧ cellEvent b0 s0 t ω then
                w ω
              else
                0) := by
        intro t ht
        by_cases h : target ω ∧ base ω ∧ cellEvent b0 s0 t ω
        · simp [h, hsample_nonneg ω]
        · simp [h]
      have ht_le :
          w ω ≤
            (Finset.univ : Finset Transcript).sum
              (fun t =>
                if target ω ∧ base ω ∧ cellEvent b0 s0 t ω then
                  w ω
                else
                  0) := by
        simpa [hcell_pred0] using
          Finset.single_le_sum ht_nonneg (Finset.mem_univ t0)
      have hs_nonneg :
          ∀ s ∈ (Finset.univ : Finset Support),
            0 ≤
              (Finset.univ : Finset Transcript).sum
                (fun t =>
                  if target ω ∧ base ω ∧ cellEvent b0 s t ω then
                    w ω
                  else
                    0) := by
        intro s hs
        exact Finset.sum_nonneg (by
          intro t ht
          by_cases h : target ω ∧ base ω ∧ cellEvent b0 s t ω
          · simp [h, hsample_nonneg ω]
          · simp [h])
      have hs_le :
          (Finset.univ : Finset Transcript).sum
              (fun t =>
                if target ω ∧ base ω ∧ cellEvent b0 s0 t ω then
                  w ω
                else
                  0)
            ≤
            (Finset.univ : Finset Support).sum
              (fun s =>
                (Finset.univ : Finset Transcript).sum
                  (fun t =>
                    if target ω ∧ base ω ∧ cellEvent b0 s t ω then
                      w ω
                    else
                      0)) :=
        Finset.single_le_sum hs_nonneg (Finset.mem_univ s0)
      have hb_nonneg :
          ∀ b ∈ (Finset.univ : Finset Branch),
            0 ≤
              (Finset.univ : Finset Support).sum
                (fun s =>
                  (Finset.univ : Finset Transcript).sum
                    (fun t =>
                      if target ω ∧ base ω ∧ cellEvent b s t ω then
                        w ω
                      else
                        0)) := by
        intro b hb
        exact Finset.sum_nonneg (by
          intro s hs
          exact Finset.sum_nonneg (by
            intro t ht
            by_cases h : target ω ∧ base ω ∧ cellEvent b s t ω
            · simp [h, hsample_nonneg ω]
            · simp [h]))
      have hb_le :
          (Finset.univ : Finset Support).sum
              (fun s =>
                (Finset.univ : Finset Transcript).sum
                  (fun t =>
                    if target ω ∧ base ω ∧ cellEvent b0 s t ω then
                      w ω
                    else
                      0))
            ≤
            (Finset.univ : Finset Branch).sum
              (fun b =>
                (Finset.univ : Finset Support).sum
                  (fun s =>
                    (Finset.univ : Finset Transcript).sum
                      (fun t =>
                        if target ω ∧ base ω ∧ cellEvent b s t ω then
                          w ω
                        else
                          0))) :=
        Finset.single_le_sum hb_nonneg (Finset.mem_univ b0)
      simpa [htb] using le_trans ht_le (le_trans hs_le hb_le)
    · have hsum_nonneg :
          0 ≤
            (Finset.univ : Finset Branch).sum
              (fun b =>
                (Finset.univ : Finset Support).sum
                (fun s =>
                  (Finset.univ : Finset Transcript).sum
                    (fun t =>
                      if target ω ∧ base ω ∧ cellEvent b s t ω then
                        w ω
                      else
                        0))) := by
        exact Finset.sum_nonneg (by
          intro b hb
          exact Finset.sum_nonneg (by
            intro s hs
            exact Finset.sum_nonneg (by
              intro t ht
              by_cases h : target ω ∧ base ω ∧ cellEvent b s t ω
              · simp [h, hsample_nonneg ω]
              · simp [h])))
      simpa [htb] using hsum_nonneg
  have hcovered_sum :
      prob (fun ω : Ω => target ω ∧ base ω) ≤
        (Finset.univ : Finset Branch).sum
          (fun b =>
            (Finset.univ : Finset Support).sum
              (fun s =>
                (Finset.univ : Finset Transcript).sum
                  (fun t =>
                    prob
                      (fun ω : Ω =>
                        target ω ∧ base ω ∧ cellEvent b s t ω)))) := by
    calc
      prob (fun ω : Ω => target ω ∧ base ω)
        =
        (Finset.univ : Finset Ω).sum
          (fun ω => if target ω ∧ base ω then w ω else 0)
          := by
            unfold prob TwoBiteEventProbability
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl ?_
            intro ω hω
            by_cases h : target ω ∧ base ω
            · simp [h, w]
            · simp [h, w]
      _ 
        ≤
          (Finset.univ : Finset Ω).sum
            (fun ω =>
              (Finset.univ : Finset Branch).sum
                (fun b =>
                  (Finset.univ : Finset Support).sum
                    (fun s =>
                      (Finset.univ : Finset Transcript).sum
                        (fun t =>
                          if target ω ∧ base ω ∧ cellEvent b s t ω then
                            w ω
                          else
                            0)))) := by
          exact Finset.sum_le_sum (by intro ω hω; exact hpoint ω)
      _ =
          (Finset.univ : Finset Branch).sum
            (fun b =>
              (Finset.univ : Finset Support).sum
                (fun s =>
                  (Finset.univ : Finset Transcript).sum
                    (fun t =>
                      (Finset.univ : Finset Ω).sum
                        (fun ω =>
                          if target ω ∧ base ω ∧ cellEvent b s t ω then
                            w ω
                          else
                            0)))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro b hb
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [Finset.sum_comm]
      _ =
          (Finset.univ : Finset Branch).sum
            (fun b =>
              (Finset.univ : Finset Support).sum
                (fun s =>
                  (Finset.univ : Finset Transcript).sum
                    (fun t =>
                      prob
                        (fun ω : Ω =>
                          target ω ∧ base ω ∧ cellEvent b s t ω)))) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          refine Finset.sum_congr rfl ?_
          intro s hs
          refine Finset.sum_congr rfl ?_
          intro t ht
          unfold prob TwoBiteEventProbability
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro ω hω
          by_cases h : target ω ∧ base ω ∧ cellEvent b s t ω
          · simp [h, w]
          · simp [h, w]
  have hsum_cell_bound :
      (Finset.univ : Finset Branch).sum
          (fun b =>
            (Finset.univ : Finset Support).sum
              (fun s =>
                (Finset.univ : Finset Transcript).sum
                  (fun t =>
                    prob
                      (fun ω : Ω =>
                        target ω ∧ base ω ∧ cellEvent b s t ω))))
        ≤
        (Finset.univ : Finset Branch).sum
          (fun b =>
            (Finset.univ : Finset Support).sum
              (fun s =>
                (Finset.univ : Finset Transcript).sum
                  (fun t => weight b s t))) := by
    refine Finset.sum_le_sum ?_
    intro b hb
    refine Finset.sum_le_sum ?_
    intro s hs
    refine Finset.sum_le_sum ?_
    intro t ht
    exact hcell_bound b s t
  change prob (fun ω : Ω => target ω ∧ base ω) ≤ M
  exact le_trans hcovered_sum (le_trans hsum_cell_bound hweight_sum)
