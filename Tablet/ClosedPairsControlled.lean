import Mathlib.Tactic.Linarith
import Tablet.ClosedPairsBound
import Tablet.LargeClosedPairsBound
import Tablet.MediumClosedPairsBound
import Tablet.SmallClosedPairsBound
import Tablet.HugeProjectionClosedPairsBound
import Tablet.TwoBiteClosedPairsInClass
import Tablet.TwoBiteLargeClass
import Tablet.TwoBiteMediumClass
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteProjectedPairSum
import Tablet.TwoBiteHugeClass

-- [TABLET NODE: ClosedPairsControlled]

theorem ClosedPairsControlled :
    ∀ {n m k : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (ε ε1 ε2 : ℝ),
      I.card = k →
      FiberAndDegreeEvent ω ε2 →
      TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω →
      TwoBiteSmallClosedPairsEvent (k := k) ε ε1 ω →
      ClosedPairsBound
        ((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ)
        ε1 (k : ℝ) →
      (let hugeRed : TwoBiteBaseVertex m → Prop :=
          fun x => TwoBiteHugeClass ω I x ∧ ∃ r : Fin m, x = Sum.inl r
       let hugeBlue : TwoBiteBaseVertex m → Prop :=
          fun x => TwoBiteHugeClass ω I x ∧ ∃ b : Fin m, x = Sum.inr b
       ClosedPairsBound
        (TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
          TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω))
        ε1 (k : ℝ)) →
      ClosedPairsBound
        (((TwoBiteClosedPairsInClass ω I (TwoBiteLargeClass ω ε I)).card : ℝ) +
          ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) +
          ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ) +
          (let hugeRed : TwoBiteBaseVertex m → Prop :=
            fun x => TwoBiteHugeClass ω I x ∧ ∃ r : Fin m, x = Sum.inl r
           let hugeBlue : TwoBiteBaseVertex m → Prop :=
            fun x => TwoBiteHugeClass ω I x ∧ ∃ b : Fin m, x = Sum.inr b
           TwoBiteProjectedPairSum ω I hugeRed (TwoBiteRedProjection ω) +
            TwoBiteProjectedPairSum ω I hugeBlue (TwoBiteBlueProjection ω)))
        (4 * ε1) (k : ℝ) := by
-- BODY
  intro n m k p ω I ε ε1 ε2 hI _hFiber hMediumEvent hSmallEvent hLarge hHuge
  have hMedium :
      ClosedPairsBound
        ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ)
        ε1 (k : ℝ) :=
    hMediumEvent I hI
  have hSmall :
      ClosedPairsBound
        ((TwoBiteClosedPairsInClass ω I (TwoBiteSmallClass ω ε I)).card : ℝ)
        ε1 (k : ℝ) :=
    hSmallEvent I hI
  unfold ClosedPairsBound at hLarge hMedium hSmall hHuge ⊢
  nlinarith
