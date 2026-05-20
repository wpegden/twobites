import Tablet.TwoBiteStageRevealedVertex

-- [TABLET NODE: TwoBiteProjectionPairTouched]

noncomputable def TwoBiteProjectionPairTouched {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε : ℝ) (I : Finset (Fin n))
    (e : Sum (Fin m × Fin m) (Fin m × Fin m)) : Prop :=
-- BODY
  match e with
  | Sum.inl q =>
      TwoBiteStageRevealedVertex ω ε I (Sum.inl q.1) ∨
        TwoBiteStageRevealedVertex ω ε I (Sum.inl q.2)
  | Sum.inr q =>
      TwoBiteStageRevealedVertex ω ε I (Sum.inr q.1) ∨
        TwoBiteStageRevealedVertex ω ε I (Sum.inr q.2)
