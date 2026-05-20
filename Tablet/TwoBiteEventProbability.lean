import Tablet.TwoBiteSampleWeight

-- [TABLET NODE: TwoBiteEventProbability]

noncomputable def TwoBiteEventProbability (n m : ℕ) (p : ℝ)
    (event : TwoBiteSample n m p → Prop) : ℝ := by
-- BODY
  classical
  exact
    (Finset.univ.filter (fun ω : TwoBiteSample n m p => event ω)).sum
      (fun ω => TwoBiteSampleWeight ω)
