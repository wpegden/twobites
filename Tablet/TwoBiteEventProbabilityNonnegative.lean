import Tablet.Preamble
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.TwoBiteEventProbability

-- [TABLET NODE: TwoBiteEventProbabilityNonnegative]

theorem TwoBiteEventProbabilityNonnegative {n m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : TwoBiteSample n m p → Prop) [DecidablePred S] :
    0 ≤ TwoBiteEventProbability n m p S := by
-- BODY
  classical
  unfold TwoBiteEventProbability
  apply Finset.sum_nonneg
  intro ω _
  apply TwoBiteSampleWeightNonnegative _ hp0 hp1
