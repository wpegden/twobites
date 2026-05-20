import Tablet.TwoBiteFinalGraph

-- [TABLET NODE: TwoBiteFinalGraphNoBlueBlueRedTriangle]

theorem TwoBiteFinalGraphNoBlueBlueRedTriangle {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) :
    let red := (TwoBiteFinalGraph ω).1
    let blue := (TwoBiteFinalGraph ω).2.1
    ¬ ∃ u v w : Fin n, blue.Adj u v ∧ blue.Adj u w ∧ red.Adj v w := by
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
  rcases hvw with ⟨_, hvw | hvw⟩
  · exact hvw.2 (Or.inl (Or.inr ⟨u, hBlueUV, hBlueUW, hvw.1⟩))
  · exact hvw.2 (Or.inl (Or.inr ⟨u, hBlueUW, hBlueUV, hvw.1⟩))
