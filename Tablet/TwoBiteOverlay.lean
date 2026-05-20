import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: TwoBiteOverlay]

def TwoBiteOverlay {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p) :
    SimpleGraph (Fin n) × SimpleGraph (Fin n) :=
-- BODY
  let red : SimpleGraph (Fin n) :=
    { Adj := fun u v =>
        u ≠ v ∧
          (TwoBiteRedGraph ω).Adj
            (TwoBiteRedProjection ω u) (TwoBiteRedProjection ω v)
      symm := by
        intro u v h
        exact ⟨h.1.symm, (TwoBiteRedGraph ω).symm h.2⟩
      loopless := by
        exact ⟨fun _ h => h.1 rfl⟩ }
  let blue : SimpleGraph (Fin n) :=
    { Adj := fun u v =>
        u ≠ v ∧
          (TwoBiteBlueGraph ω).Adj
            (TwoBiteBlueProjection ω u) (TwoBiteBlueProjection ω v)
      symm := by
        intro u v h
        exact ⟨h.1.symm, (TwoBiteBlueGraph ω).symm h.2⟩
      loopless := by
        exact ⟨fun _ h => h.1 rfl⟩ }
  (red, blue)
