import Tablet.TwoBiteFinalGraph
import Tablet.FinPairRankLatestOfDistinct

-- [TABLET NODE: TwoBiteFinalGraphNoBlueTriangle]

theorem TwoBiteFinalGraphNoBlueTriangle {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) :
    let blue := (TwoBiteFinalGraph ω).2.1
    ¬ ∃ u v w : Fin n, blue.Adj u v ∧ blue.Adj u w ∧ blue.Adj v w := by
-- BODY
  dsimp [TwoBiteFinalGraph]
  rintro ⟨u, v, w, huv, huw, hvw⟩
  rw [SimpleGraph.fromRel_adj] at huv
  rw [SimpleGraph.fromRel_adj] at huw
  rw [SimpleGraph.fromRel_adj] at hvw
  have hBlueUV : (TwoBiteOverlay ω).2.Adj u v := by
    rcases huv with ⟨_, huv | huv⟩
    · exact huv.1
    · exact ((TwoBiteOverlay ω).2).symm huv.1
  have hBlueUW : (TwoBiteOverlay ω).2.Adj u w := by
    rcases huw with ⟨_, huw | huw⟩
    · exact huw.1
    · exact ((TwoBiteOverlay ω).2).symm huw.1
  have hBlueVW : (TwoBiteOverlay ω).2.Adj v w := by
    rcases hvw with ⟨_, hvw | hvw⟩
    · exact hvw.1
    · exact ((TwoBiteOverlay ω).2).symm hvw.1
  have hbuv : TwoBiteBlueProjection ω u ≠ TwoBiteBlueProjection ω v := by
    intro h
    have hAdj := hBlueUV
    dsimp [TwoBiteOverlay] at hAdj
    have hloop :
        (TwoBiteBlueGraph ω).Adj
          (TwoBiteBlueProjection ω u) (TwoBiteBlueProjection ω u) := by
      simpa [h] using hAdj.2
    exact (TwoBiteBlueGraph ω).loopless.irrefl _ hloop
  have hbuw : TwoBiteBlueProjection ω u ≠ TwoBiteBlueProjection ω w := by
    intro h
    have hAdj := hBlueUW
    dsimp [TwoBiteOverlay] at hAdj
    have hloop :
        (TwoBiteBlueGraph ω).Adj
          (TwoBiteBlueProjection ω u) (TwoBiteBlueProjection ω u) := by
      simpa [h] using hAdj.2
    exact (TwoBiteBlueGraph ω).loopless.irrefl _ hloop
  have hbvw : TwoBiteBlueProjection ω v ≠ TwoBiteBlueProjection ω w := by
    intro h
    have hAdj := hBlueVW
    dsimp [TwoBiteOverlay] at hAdj
    have hloop :
        (TwoBiteBlueGraph ω).Adj
          (TwoBiteBlueProjection ω v) (TwoBiteBlueProjection ω v) := by
      simpa [h] using hAdj.2
    exact (TwoBiteBlueGraph ω).loopless.irrefl _ hloop
  have hlatest :
      let pairRank : Fin m → Fin m → ℕ :=
        fun a b => Nat.min a.val b.val * m + Nat.max a.val b.val
      let blueLatest : Fin n → Fin n → Fin n → Prop :=
        fun x y z =>
          pairRank (TwoBiteBlueProjection ω x) (TwoBiteBlueProjection ω z) <
              pairRank (TwoBiteBlueProjection ω x) (TwoBiteBlueProjection ω y) ∧
            pairRank (TwoBiteBlueProjection ω y) (TwoBiteBlueProjection ω z) <
              pairRank (TwoBiteBlueProjection ω x) (TwoBiteBlueProjection ω y)
      blueLatest u v w ∨ blueLatest u w v ∨ blueLatest v w u := by
    dsimp
    simpa [Nat.min_comm, Nat.max_comm] using
      (FinPairRankLatestOfDistinct
        (a := TwoBiteBlueProjection ω u)
        (b := TwoBiteBlueProjection ω v)
        (c := TwoBiteBlueProjection ω w)
        hbuv hbuw hbvw)
  dsimp at hlatest
  rcases hlatest with hlatestUV | hlatestUW | hlatestVW
  · rcases huv with ⟨_, huv | huv⟩
    · exact huv.2 (Or.inl (Or.inl ⟨w, hBlueUV, hBlueUW, hBlueVW, hlatestUV⟩))
    · exact huv.2 (Or.inr (Or.inl ⟨w, hBlueUV, hBlueUW, hBlueVW, hlatestUV⟩))
  · rcases huw with ⟨_, huw | huw⟩
    · exact huw.2 (Or.inl (Or.inl
        ⟨v, hBlueUW, hBlueUV, ((TwoBiteOverlay ω).2).symm hBlueVW, hlatestUW⟩))
    · exact huw.2 (Or.inr (Or.inl
        ⟨v, hBlueUW, hBlueUV, ((TwoBiteOverlay ω).2).symm hBlueVW, hlatestUW⟩))
  · rcases hvw with ⟨_, hvw | hvw⟩
    · exact hvw.2 (Or.inl (Or.inl
        ⟨u, hBlueVW, ((TwoBiteOverlay ω).2).symm hBlueUV,
          ((TwoBiteOverlay ω).2).symm hBlueUW, hlatestVW⟩))
    · exact hvw.2 (Or.inr (Or.inl
        ⟨u, hBlueVW, ((TwoBiteOverlay ω).2).symm hBlueUV,
          ((TwoBiteOverlay ω).2).symm hBlueUW, hlatestVW⟩))
