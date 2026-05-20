import Tablet.TwoBiteFinalGraph

-- [TABLET NODE: TwoBiteFinalGraphNoRedRedBlueTriangle]

theorem TwoBiteFinalGraphNoRedRedBlueTriangle {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) :
    let red := (TwoBiteFinalGraph ω).1
    let blue := (TwoBiteFinalGraph ω).2.1
    ¬ ∃ u v w : Fin n, red.Adj u v ∧ red.Adj u w ∧ blue.Adj v w := by
-- BODY
  dsimp [TwoBiteFinalGraph]
  rintro ⟨u, v, w, huv, huw, hvw⟩
  rw [SimpleGraph.fromRel_adj] at huv
  rw [SimpleGraph.fromRel_adj] at huw
  rw [SimpleGraph.fromRel_adj] at hvw
  have hRedUV : (TwoBiteOverlay ω).1.Adj u v := by
    rcases huv with ⟨_, huv | huv⟩
    · exact huv.1
    · exact ((TwoBiteOverlay ω).1).symm huv.1
  have hRedUW : (TwoBiteOverlay ω).1.Adj u w := by
    rcases huw with ⟨_, huw | huw⟩
    · exact huw.1
    · exact ((TwoBiteOverlay ω).1).symm huw.1
  rcases hvw with ⟨_, hvw | hvw⟩
  · exact hvw.2 (Or.inl (Or.inr ⟨u, hRedUV, hRedUW, hvw.1⟩))
  · exact hvw.2 (Or.inl (Or.inr ⟨u, hRedUW, hRedUV, hvw.1⟩))
