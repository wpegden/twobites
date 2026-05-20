import Tablet.ClosedPairsBound
import Tablet.FiberAndDegreeEvent
import Tablet.HugeOppositeColorProjectionBound
import Tablet.HugeSameColorProjectionBound
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.ProjectionOpenPairFunction
import Tablet.TwoBiteProjectedPairSum
import Tablet.TwoBiteHugeClass

-- [TABLET NODE: HugeProjectionClosedPairsBound]

theorem HugeProjectionClosedPairsBound :
    ∀ {n m k : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (ε ε1 ε2 : ℝ) {n0 : ℕ},
      0 ≤ ε1 →
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      I.card = k →
      FiberAndDegreeEvent ω ε2 →
        let hugeRed : TwoBiteBaseVertex m → Prop :=
          fun x => TwoBiteHugeClass ω I x ∧ ∃ r : Fin m, x = Sum.inl r
        let hugeBlue : TwoBiteBaseVertex m → Prop :=
          fun x => TwoBiteHugeClass ω I x ∧ ∃ b : Fin m, x = Sum.inr b
        ClosedPairsBound
            (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω))
            ε1 (k : ℝ) ∧
          ClosedPairsBound
            (TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω))
            ε1 (k : ℝ) ∧
          ClosedPairsBound
            (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
              TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω))
            ε1 (k : ℝ) ∧
          TwoBiteProjectedPairSum ω I hugeRed (TwoBiteBlueProjection ω) ≤
            (1 + ε1) *
              min
                (RealChooseTwo ((k : ℝ) -
                  ((I.image (TwoBiteRedProjection ω)).card : ℝ)))
                (RealChooseTwo (p * (n : ℝ)) +
                  RealChooseTwo
                    ((k : ℝ) -
                      ((I.image (TwoBiteRedProjection ω)).card : ℝ) -
                        p * (n : ℝ))) ∧
          TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteRedProjection ω) ≤
            (1 + ε1) *
              min
                (RealChooseTwo ((k : ℝ) -
                  ((I.image (TwoBiteBlueProjection ω)).card : ℝ)))
                (RealChooseTwo (p * (n : ℝ)) +
                  RealChooseTwo
                    ((k : ℝ) -
                      ((I.image (TwoBiteBlueProjection ω)).card : ℝ) -
                        p * (n : ℝ))) := by
-- BODY
  intro n m k p ω I ε ε1 ε2 n0 hε1 hcomparisons hn hm hp hk hI hfiber
  have hsame :=
    HugeSameColorProjectionBound (n := n) (m := m) (k := k) (p := p)
      ω I ε ε1 ε2 (n0 := n0)
      hε1 hcomparisons hn hm hp hk hI hfiber
  have hopp :=
    HugeOppositeColorProjectionBound (n := n) (m := m) (k := k) (p := p)
      ω I ε ε1 ε2 (n0 := n0)
      hε1 hcomparisons hn hm hp hk hI hfiber
  dsimp at hsame hopp ⊢
  exact ⟨hsame.1, hsame.2.1, hsame.2.2, hopp.1, hopp.2⟩
