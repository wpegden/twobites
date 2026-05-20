import Tablet.TwoBiteTerminalCoordinateUniverse
import Tablet.TwoBiteProjectionContains
import Tablet.TwoBiteStageRevealedVertex
import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteX
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteBaseVertex

-- [TABLET NODE: TwoBitePreTerminalRecordedPairs]

noncomputable def TwoBitePreTerminalRecordedPairs {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε : ℝ) (I : Finset (Fin n)) :
    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := by
-- BODY
  classical
  exact
    (TwoBiteTerminalCoordinateUniverse m).filter
      (fun e =>
        match e with
        | Sum.inl q =>
            (∃ r s : Fin m,
              (q = (r, s) ∨ q = (s, r)) ∧
                ((TwoBiteStageRevealedVertex ω ε I (Sum.inl r) ∧
                    TwoBiteProjectionContains ω I (Sum.inl s)) ∨
                  (TwoBiteStageRevealedVertex ω ε I (Sum.inl s) ∧
                    TwoBiteProjectionContains ω I (Sum.inl r)))) ∨
              ∃ x : TwoBiteBaseVertex m,
                TwoBiteStageRevealedVertex ω ε I x ∧
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ω I x).image (TwoBiteRedProjection ω))
        | Sum.inr q =>
            (∃ b c : Fin m,
              (q = (b, c) ∨ q = (c, b)) ∧
                ((TwoBiteStageRevealedVertex ω ε I (Sum.inr b) ∧
                    TwoBiteProjectionContains ω I (Sum.inr c)) ∨
                  (TwoBiteStageRevealedVertex ω ε I (Sum.inr c) ∧
                    TwoBiteProjectionContains ω I (Sum.inr b)))) ∨
              ∃ x : TwoBiteBaseVertex m,
                TwoBiteStageRevealedVertex ω ε I x ∧
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)))
