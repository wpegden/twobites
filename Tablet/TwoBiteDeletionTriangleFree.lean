import Tablet.TwoBiteFinalGraphNoRedTriangle
import Tablet.TwoBiteFinalGraphNoBlueTriangle
import Tablet.TwoBiteFinalGraphNoRedRedBlueTriangle
import Tablet.TwoBiteFinalGraphNoBlueBlueRedTriangle
import Tablet.TwoBiteFinalGraphShadowTriangleFree

-- [TABLET NODE: TwoBiteDeletionTriangleFree]

theorem TwoBiteDeletionTriangleFree {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) :
    let red := (TwoBiteFinalGraph ω).1
    let blue := (TwoBiteFinalGraph ω).2.1
    let shadow := (TwoBiteFinalGraph ω).2.2
    (¬ ∃ u v w : Fin n, red.Adj u v ∧ red.Adj u w ∧ red.Adj v w) ∧
      (¬ ∃ u v w : Fin n, blue.Adj u v ∧ blue.Adj u w ∧ blue.Adj v w) ∧
      (¬ ∃ u v w : Fin n, red.Adj u v ∧ red.Adj u w ∧ blue.Adj v w) ∧
      (¬ ∃ u v w : Fin n, blue.Adj u v ∧ blue.Adj u w ∧ red.Adj v w) ∧
      (¬ ∃ u v w : Fin n,
        u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
          shadow.Adj u v ∧ shadow.Adj u w ∧ shadow.Adj v w) := by
-- BODY
  exact ⟨TwoBiteFinalGraphNoRedTriangle ω,
    TwoBiteFinalGraphNoBlueTriangle ω,
    TwoBiteFinalGraphNoRedRedBlueTriangle ω,
    TwoBiteFinalGraphNoBlueBlueRedTriangle ω,
    TwoBiteFinalGraphShadowTriangleFree ω⟩
