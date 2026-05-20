import Tablet.WithinRelativeError
import Tablet.RedFiber
import Tablet.BlueFiber
import Tablet.GraphDegreeCount
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteLiftedNeighborhood

-- [TABLET NODE: FiberAndDegreeEvent]

noncomputable def FiberAndDegreeEvent {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε2 : ℝ) : Prop := by
-- BODY
  classical
  exact
    let C : ℝ := 100
    let oppositeProjection : TwoBiteBaseVertex m → Finset (Fin m) :=
      fun x =>
        match x with
        | Sum.inl r =>
            (TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
              (TwoBiteBlueProjection ω)
        | Sum.inr b =>
            (TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
              (TwoBiteRedProjection ω)
    (∀ r : Fin m,
      WithinRelativeError ε2 ((Real.log (n : ℝ)) ^ 2) ((RedFiber ω r).card : ℝ)) ∧
      (∀ b : Fin m,
        WithinRelativeError ε2 ((Real.log (n : ℝ)) ^ 2) ((BlueFiber ω b).card : ℝ)) ∧
      (∀ r : Fin m,
        WithinRelativeError ε2 (p * (m : ℝ)) (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ)) ∧
      (∀ b : Fin m,
        WithinRelativeError ε2 (p * (m : ℝ)) (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ)) ∧
      (∀ r s : Fin m, r ≠ s →
        ((Finset.univ.filter
          (fun t : Fin m =>
            (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ)
          ≤ C * Real.log (n : ℝ)) ∧
      (∀ b c : Fin m, b ≠ c →
        ((Finset.univ.filter
          (fun t : Fin m =>
            (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ)
          ≤ C * Real.log (n : ℝ)) ∧
      (∀ x : TwoBiteBaseVertex m,
        WithinRelativeError ε2 (p * (n : ℝ))
          ((TwoBiteLiftedNeighborhood ω x).card : ℝ)) ∧
      (∀ r s : Fin m, r ≠ s →
        ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ)
          ≤ C * (Real.log (n : ℝ)) ^ 3) ∧
      (∀ b c : Fin m, b ≠ c →
        ((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ)
          ≤ C * (Real.log (n : ℝ)) ^ 3) ∧
      (∀ r b,
        ((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inr b)).card : ℝ)
          ≤ C * (Real.log (n : ℝ)) ^ 3) ∧
      (∀ r s : Fin m, r ≠ s →
        ((oppositeProjection (Sum.inl r) ∩ oppositeProjection (Sum.inl s)).card : ℝ)
          ≤ 2 * C * (Real.log (n : ℝ)) ^ 3) ∧
      (∀ b c : Fin m, b ≠ c →
        ((oppositeProjection (Sum.inr b) ∩ oppositeProjection (Sum.inr c)).card : ℝ)
          ≤ 2 * C * (Real.log (n : ℝ)) ^ 3)
