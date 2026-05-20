import Tablet.ClosedPairsBound
import Tablet.FixedSetHistoryCellAdaptiveBranchPartition
import Tablet.FixedSetHistoryCellBranchTranscriptSummation
import Tablet.FixedSetHistoryCellCanonicalAbsenceSelection
import Tablet.FixedSetHistoryCellFixedCylinderCharge
import Tablet.FixedSetHistoryCellGlobalBlueExceptionalWitness
import Tablet.FixedSetHistoryCellTerminalProductPartition
import Tablet.ProjectionOpenPairFunction
import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteTerminalCoordinateUniverse

-- [TABLET NODE: FixedSetHistoryCellFixedCountBlueWeightSum]

theorem FixedSetHistoryCellFixedCountBlueWeightSum :
    ∀ {n m k ℓR ℓB : ℕ} {p ε ε1 ε2 : ℝ}
      (I : Finset (Fin n))
      (hist : TwoBiteSample n m p → Prop)
        (recorded terminal :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (rep : TwoBiteSample n m p)
        (uR uB : ℕ)
        [∀ (ω : TwoBiteSample n m p)
          (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
          Decidable (TwoBiteEdgeCoordinateValue ω e)]
        [∀ (ω : TwoBiteSample n m p),
          DecidablePred
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => True
                | Sum.inr _ => False)]
        [∀ (ω : TwoBiteSample n m p),
          DecidablePred
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => False
                | Sum.inr _ => True)],
      0 ≤ ε1 →
      ε1 ≤ 1 →
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      I.card = k →
      hist rep →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
            (ℓB := ℓB) ω I) →
      (∀ ω : TwoBiteSample n m p,
        hist ω ↔
          (∀ x : Fin n, ω.2.2 x = rep.2.2 x) ∧
          (∀ e,
            e ∈ recorded →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue rep e))) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ e,
            e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
              e ∈ recorded) →
      (∀ e,
        e ∈ terminal ↔
          e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded) →
      order.Nodup →
      order.toFinset = terminal →
      (∀ e, e ∈ terminal → e ∉ recorded) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ e,
            e ∈ TwoBiteStagedOpenPairs ω ε I →
              e ∈ terminal) →
      (∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ terminal →
          TwoBiteConditionalProbability n m p
            (fun ω =>
              ∀ e, e ∈ terminal →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A))
            hist =
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ (pre : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
            (e : Sum (Fin m × Fin m) (Fin m × Fin m))
            (suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m))),
            order = pre ++ e :: suffix →
              ∀ ω' : TwoBiteSample n m p,
                (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                (∀ c,
                  c ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                (∀ c,
                  c ∈ pre.toFinset →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                  (e ∈ TwoBiteStagedOpenPairs ω ε I ↔
                    e ∈ TwoBiteStagedOpenPairs ω' ε I) ∧
                  (TwoBiteProjectionPairTouched ω ε I e ↔
                    TwoBiteProjectionPairTouched ω' ε I e) ∧
                  (TwoBiteProjectionPairSameColorClosed ω I e ↔
                    TwoBiteProjectionPairSameColorClosed ω' I e) ∧
                  (e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                    e ∈ TwoBitePreTerminalRecordedPairs ω' ε I)) →
      (∀ ω : TwoBiteSample n m p,
        TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
        TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
          (ℓB := ℓB) ω I →
        ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
            (k : ℝ) p (n : ℝ) - 10 * ε1 * (k : ℝ) ^ 2
          ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ)) →
      (∀ branch : TwoBiteSample n m p,
        hist branch →
          ∃ ER EB : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            ER ⊆ terminal ∧
            EB ⊆ terminal ∧
            (∀ ω : TwoBiteSample n m p,
              hist ω →
              (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
              (∀ e,
                e ∈ recorded →
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue branch e)) →
              (∀ e,
                e ∈ terminal →
                  match e with
                  | Sum.inl _ => True
                  | Sum.inr _ =>
                      (TwoBiteEdgeCoordinateValue ω e ↔
                        TwoBiteEdgeCoordinateValue branch e)) →
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                ClosedPairsBound ((ER.card : ℝ)) (3 * ε1) (k : ℝ) ∧
                (∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                  TwoBiteEdgeCoordinateValue ω e →
                  (match e with
                  | Sum.inl _ => True
                  | Sum.inr _ => False) →
                  (TwoBiteFinalGraph ω).2.2.IsIndepSet
                    (↑I : Set (Fin n)) →
                    e ∈ ER)) ∧
            (∀ ω : TwoBiteSample n m p,
              hist ω →
              (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
              (∀ e,
                e ∈ recorded →
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue branch e)) →
              (∀ e,
                e ∈ terminal →
                  match e with
                  | Sum.inl _ =>
                      (TwoBiteEdgeCoordinateValue ω e ↔
                        TwoBiteEdgeCoordinateValue branch e)
                  | Sum.inr _ => True) →
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                ClosedPairsBound ((EB.card : ℝ)) (3 * ε1) (k : ℝ) ∧
                (∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                  TwoBiteEdgeCoordinateValue ω e →
                  (match e with
                  | Sum.inl _ => False
                  | Sum.inr _ => True) →
                  (TwoBiteFinalGraph ω).2.2.IsIndepSet
                    (↑I : Set (Fin n)) →
                    e ∈ EB))) →
      let a : ℝ :=
        ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
          (k : ℝ) p (n : ℝ) - 10 * ε1 * (k : ℝ) ^ 2
      uR ≤ uB →
        ∃ NR NB : ℕ,
          (NR : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 ∧
          (NB : ℝ) ≤ (k : ℝ) ^ 2 ∧
          TwoBiteConditionalProbability n m p
            (fun ω =>
              ((TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
                TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω) ∧
                (((TwoBiteStagedOpenPairs ω ε I).filter
                  (fun e =>
                    TwoBiteEdgeCoordinateValue ω e ∧
                      match e with
                      | Sum.inl _ => True
                      | Sum.inr _ => False)).card = uR) ∧
                (((TwoBiteStagedOpenPairs ω ε I).filter
                  (fun e =>
                    TwoBiteEdgeCoordinateValue ω e ∧
                      match e with
                      | Sum.inl _ => False
                      | Sum.inr _ => True)).card = uB))
            hist
            ≤
            (Nat.choose NR uB : ℝ) * p ^ uB *
              (Nat.choose NB uR : ℝ) * p ^ uR *
                Real.rpow ((1 : ℝ) - p)
                  (max 0 (a - (uB : ℝ) - (uR : ℝ))) := by
-- BODY
  sorry
