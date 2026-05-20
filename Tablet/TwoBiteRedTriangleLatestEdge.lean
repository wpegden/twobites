import Tablet.TwoBiteOverlay
import Tablet.FinPairRankLatestOfDistinct

-- [TABLET NODE: TwoBiteRedTriangleLatestEdge]

theorem TwoBiteRedTriangleLatestEdge {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) {u v w : Fin n}
    (huv : (TwoBiteOverlay ω).1.Adj u v)
    (huw : (TwoBiteOverlay ω).1.Adj u w)
    (hvw : (TwoBiteOverlay ω).1.Adj v w) :
    let pairRank : Fin m → Fin m → ℕ :=
      fun a b => Nat.min a.val b.val * m + Nat.max a.val b.val
    let redLatest : Fin n → Fin n → Fin n → Prop :=
      fun x y z =>
        pairRank (TwoBiteRedProjection ω x) (TwoBiteRedProjection ω z) <
            pairRank (TwoBiteRedProjection ω x) (TwoBiteRedProjection ω y) ∧
          pairRank (TwoBiteRedProjection ω y) (TwoBiteRedProjection ω z) <
            pairRank (TwoBiteRedProjection ω x) (TwoBiteRedProjection ω y)
    redLatest u v w ∨ redLatest u w v ∨ redLatest v w u := by
-- BODY
  dsimp [TwoBiteOverlay] at huv huw hvw
  have hruv : TwoBiteRedProjection ω u ≠ TwoBiteRedProjection ω v := by
    intro h
    have hloop :
        (TwoBiteRedGraph ω).Adj
          (TwoBiteRedProjection ω u) (TwoBiteRedProjection ω u) := by
      simpa [h] using huv.2
    exact (TwoBiteRedGraph ω).loopless.irrefl _ hloop
  have hruw : TwoBiteRedProjection ω u ≠ TwoBiteRedProjection ω w := by
    intro h
    have hloop :
        (TwoBiteRedGraph ω).Adj
          (TwoBiteRedProjection ω u) (TwoBiteRedProjection ω u) := by
      simpa [h] using huw.2
    exact (TwoBiteRedGraph ω).loopless.irrefl _ hloop
  have hrvw : TwoBiteRedProjection ω v ≠ TwoBiteRedProjection ω w := by
    intro h
    have hloop :
        (TwoBiteRedGraph ω).Adj
          (TwoBiteRedProjection ω v) (TwoBiteRedProjection ω v) := by
      simpa [h] using hvw.2
    exact (TwoBiteRedGraph ω).loopless.irrefl _ hloop
  simpa [Nat.min_comm, Nat.max_comm] using
    (FinPairRankLatestOfDistinct
      (a := TwoBiteRedProjection ω u)
      (b := TwoBiteRedProjection ω v)
      (c := TwoBiteRedProjection ω w)
      hruv hruw hrvw)
