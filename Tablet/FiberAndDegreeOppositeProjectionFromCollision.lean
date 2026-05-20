import Tablet.FiberAndDegreeEvent

-- [TABLET NODE: FiberAndDegreeOppositeProjectionFromCollision]

theorem FiberAndDegreeOppositeProjectionFromCollision {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) :
    (∀ x : TwoBiteBaseVertex m,
      ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤ 2 * p * (n : ℝ)) →
    (∀ r s : Fin m, r ≠ s →
      ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
            TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
        ≤ 100 * (Real.log (n : ℝ)) ^ 3) →
    (∀ b c : Fin m, b ≠ c →
      ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
            TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
        ≤ 100 * (Real.log (n : ℝ)) ^ 3) →
    (let sizeBound : Prop :=
        ∀ x : TwoBiteBaseVertex m,
        ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤ 2 * p * (n : ℝ)
      let redBound : Prop :=
        ∀ r s : Fin m, r ≠ s →
        ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
              (TwoBiteBlueProjection ω)) ∩
            ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
              (TwoBiteBlueProjection ω))).card : ℝ)
          ≤
          (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
            100 * (Real.log (n : ℝ)) ^ 3)
      let blueBound : Prop :=
        ∀ b c : Fin m, b ≠ c →
        ((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
              (TwoBiteRedProjection ω)) ∩
            ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
              (TwoBiteRedProjection ω))).card : ℝ)
          ≤
          (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
            100 * (Real.log (n : ℝ)) ^ 3)
      sizeBound → redBound ∧ blueBound) →
    (∀ r s : Fin m, r ≠ s →
      ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
            (TwoBiteBlueProjection ω)) ∩
          ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
            (TwoBiteBlueProjection ω))).card : ℝ)
        ≤ 2 * 100 * (Real.log (n : ℝ)) ^ 3) ∧
    (∀ b c : Fin m, b ≠ c →
      ((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
            (TwoBiteRedProjection ω)) ∩
          ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
            (TwoBiteRedProjection ω))).card : ℝ)
        ≤ 2 * 100 * (Real.log (n : ℝ)) ^ 3) := by
-- BODY
  intro hsize hRedIntersection hBlueIntersection hCollision
  have hCollisionBounds := hCollision hsize
  constructor
  · intro r s hrs
    have hcoll := hCollisionBounds.1 r s hrs
    have hint := hRedIntersection r s hrs
    nlinarith
  · intro b c hbc
    have hcoll := hCollisionBounds.2 b c hbc
    have hint := hBlueIntersection b c hbc
    nlinarith
