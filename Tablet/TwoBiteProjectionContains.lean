import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: TwoBiteProjectionContains]

noncomputable def TwoBiteProjectionContains {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n))
    (x : TwoBiteBaseVertex m) : Prop :=
-- BODY
  match x with
  | Sum.inl r => r ∈ I.image (TwoBiteRedProjection ω)
  | Sum.inr b => b ∈ I.image (TwoBiteBlueProjection ω)
