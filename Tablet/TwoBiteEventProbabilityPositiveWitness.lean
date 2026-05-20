import Tablet.TwoBiteEventProbability

-- [TABLET NODE: TwoBiteEventProbabilityPositiveWitness]

theorem TwoBiteEventProbabilityPositiveWitness :
    ∀ {n m : ℕ} {p : ℝ} {event : TwoBiteSample n m p → Prop},
      0 < TwoBiteEventProbability n m p event →
      ∃ ω : TwoBiteSample n m p, event ω ∧ 0 < TwoBiteSampleWeight ω := by
-- BODY
  intro n m p event hpos
  classical
  unfold TwoBiteEventProbability at hpos
  by_contra hno
  push Not at hno
  have hnonpos :
      (Finset.univ.filter (fun ω : TwoBiteSample n m p => event ω)).sum
          (fun ω => TwoBiteSampleWeight ω) ≤ 0 := by
    exact Finset.sum_nonpos (by
      intro ω hω
      have hEvent : event ω := by
        simpa using hω
      exact hno ω hEvent)
  linarith
