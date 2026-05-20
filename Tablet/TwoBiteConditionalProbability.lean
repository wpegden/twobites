import Tablet.TwoBiteEventProbability

-- [TABLET NODE: TwoBiteConditionalProbability]

noncomputable def TwoBiteConditionalProbability (n m : ℕ) (p : ℝ)
    (event condition : TwoBiteSample n m p → Prop) : ℝ :=
-- BODY
  if TwoBiteEventProbability n m p condition = 0 then
    0
  else
    TwoBiteEventProbability n m p (fun ω => event ω ∧ condition ω) /
      TwoBiteEventProbability n m p condition
