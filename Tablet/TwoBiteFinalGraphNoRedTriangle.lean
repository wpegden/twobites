import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRedTriangleLatestEdge

-- [TABLET NODE: TwoBiteFinalGraphNoRedTriangle]

theorem TwoBiteFinalGraphNoRedTriangle {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) :
    let red := (TwoBiteFinalGraph ω).1
    ¬ ∃ u v w : Fin n, red.Adj u v ∧ red.Adj u w ∧ red.Adj v w := by
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
  have hRedVW : (TwoBiteOverlay ω).1.Adj v w := by
    rcases hvw with ⟨_, hvw | hvw⟩
    · exact hvw.1
    · exact ((TwoBiteOverlay ω).1).symm hvw.1
  have hlatest := TwoBiteRedTriangleLatestEdge ω hRedUV hRedUW hRedVW
  dsimp at hlatest
  rcases hlatest with hlatestUV | hlatestUW | hlatestVW
  · rcases huv with ⟨_, huv | huv⟩
    · exact huv.2 (Or.inl (Or.inl ⟨w, hRedUV, hRedUW, hRedVW, hlatestUV⟩))
    · exact huv.2 (Or.inr (Or.inl ⟨w, hRedUV, hRedUW, hRedVW, hlatestUV⟩))
  · rcases huw with ⟨_, huw | huw⟩
    · exact huw.2 (Or.inl (Or.inl
        ⟨v, hRedUW, hRedUV, ((TwoBiteOverlay ω).1).symm hRedVW, hlatestUW⟩))
    · exact huw.2 (Or.inr (Or.inl
        ⟨v, hRedUW, hRedUV, ((TwoBiteOverlay ω).1).symm hRedVW, hlatestUW⟩))
  · rcases hvw with ⟨_, hvw | hvw⟩
    · exact hvw.2 (Or.inl (Or.inl
        ⟨u, hRedVW, ((TwoBiteOverlay ω).1).symm hRedUV,
          ((TwoBiteOverlay ω).1).symm hRedUW, hlatestVW⟩))
    · exact hvw.2 (Or.inr (Or.inl
        ⟨u, hRedVW, ((TwoBiteOverlay ω).1).symm hRedUV,
          ((TwoBiteOverlay ω).1).symm hRedUW, hlatestVW⟩))
