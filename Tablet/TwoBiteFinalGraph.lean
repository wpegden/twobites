import Tablet.TwoBiteOverlay

-- [TABLET NODE: TwoBiteFinalGraph]

def TwoBiteFinalGraph {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p) :
    SimpleGraph (Fin n) × SimpleGraph (Fin n) × SimpleGraph (Fin n) :=
-- BODY
  let pairRank : Fin m → Fin m → ℕ :=
    fun a b => Nat.min a.val b.val * m + Nat.max a.val b.val
  let redLatest : Fin n → Fin n → Fin n → Prop :=
    fun u v w =>
      pairRank (TwoBiteRedProjection ω u) (TwoBiteRedProjection ω w) <
          pairRank (TwoBiteRedProjection ω u) (TwoBiteRedProjection ω v) ∧
        pairRank (TwoBiteRedProjection ω v) (TwoBiteRedProjection ω w) <
          pairRank (TwoBiteRedProjection ω u) (TwoBiteRedProjection ω v)
  let blueLatest : Fin n → Fin n → Fin n → Prop :=
    fun u v w =>
      pairRank (TwoBiteBlueProjection ω u) (TwoBiteBlueProjection ω w) <
          pairRank (TwoBiteBlueProjection ω u) (TwoBiteBlueProjection ω v) ∧
        pairRank (TwoBiteBlueProjection ω v) (TwoBiteBlueProjection ω w) <
          pairRank (TwoBiteBlueProjection ω u) (TwoBiteBlueProjection ω v)
  let redDeletedDirected : Fin n → Fin n → Prop :=
    fun u v =>
      (∃ w : Fin n,
        (TwoBiteOverlay ω).1.Adj u v ∧
          (TwoBiteOverlay ω).1.Adj u w ∧
          (TwoBiteOverlay ω).1.Adj v w ∧
          redLatest u v w) ∨
        (∃ center : Fin n,
          (TwoBiteOverlay ω).2.Adj center u ∧
            (TwoBiteOverlay ω).2.Adj center v ∧
            (TwoBiteOverlay ω).1.Adj u v)
  let blueDeletedDirected : Fin n → Fin n → Prop :=
    fun u v =>
      (∃ w : Fin n,
        (TwoBiteOverlay ω).2.Adj u v ∧
          (TwoBiteOverlay ω).2.Adj u w ∧
          (TwoBiteOverlay ω).2.Adj v w ∧
          blueLatest u v w) ∨
        (∃ center : Fin n,
          (TwoBiteOverlay ω).1.Adj center u ∧
            (TwoBiteOverlay ω).1.Adj center v ∧
            (TwoBiteOverlay ω).2.Adj u v)
  let redDeleted : Fin n → Fin n → Prop :=
    fun u v => redDeletedDirected u v ∨ redDeletedDirected v u
  let blueDeleted : Fin n → Fin n → Prop :=
    fun u v => blueDeletedDirected u v ∨ blueDeletedDirected v u
  let red : SimpleGraph (Fin n) :=
    SimpleGraph.fromRel
      (fun u v => (TwoBiteOverlay ω).1.Adj u v ∧ ¬ redDeleted u v)
  let blue : SimpleGraph (Fin n) :=
    SimpleGraph.fromRel
      (fun u v => (TwoBiteOverlay ω).2.Adj u v ∧ ¬ blueDeleted u v)
  let shadow : SimpleGraph (Fin n) :=
    SimpleGraph.fromRel (fun u v => red.Adj u v ∨ blue.Adj u v)
  (red, blue, shadow)
