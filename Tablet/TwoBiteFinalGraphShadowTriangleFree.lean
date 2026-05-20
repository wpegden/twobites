import Tablet.TwoBiteFinalGraphNoRedTriangle
import Tablet.TwoBiteFinalGraphNoBlueTriangle
import Tablet.TwoBiteFinalGraphNoRedRedBlueTriangle
import Tablet.TwoBiteFinalGraphNoBlueBlueRedTriangle

-- [TABLET NODE: TwoBiteFinalGraphShadowTriangleFree]

theorem TwoBiteFinalGraphShadowTriangleFree {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) :
    let shadow := (TwoBiteFinalGraph ω).2.2
    ¬ ∃ u v w : Fin n,
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
        shadow.Adj u v ∧ shadow.Adj u w ∧ shadow.Adj v w := by
-- BODY
  dsimp
  rintro ⟨u, v, w, huv_ne, huw_ne, hvw_ne, huv, huw, hvw⟩
  have edgeColor :
      ∀ {a b : Fin n}, ((TwoBiteFinalGraph ω).2.2).Adj a b →
        ((TwoBiteFinalGraph ω).1).Adj a b ∨ ((TwoBiteFinalGraph ω).2.1).Adj a b := by
    intro a b h
    dsimp [TwoBiteFinalGraph] at h ⊢
    rw [SimpleGraph.fromRel_adj] at h
    rcases h with ⟨_, h | h⟩
    · exact h
    · rcases h with h | h
      · exact Or.inl ((SimpleGraph.fromRel _).symm h)
      · exact Or.inr ((SimpleGraph.fromRel _).symm h)
  rcases edgeColor huv with huvR | huvB
  · rcases edgeColor huw with huwR | huwB
    · rcases edgeColor hvw with hvwR | hvwB
      · exact TwoBiteFinalGraphNoRedTriangle ω ⟨u, v, w, huvR, huwR, hvwR⟩
      · exact TwoBiteFinalGraphNoRedRedBlueTriangle ω ⟨u, v, w, huvR, huwR, hvwB⟩
    · rcases edgeColor hvw with hvwR | hvwB
      · exact TwoBiteFinalGraphNoRedRedBlueTriangle ω
          ⟨v, u, w, ((TwoBiteFinalGraph ω).1).symm huvR, hvwR, huwB⟩
      · exact TwoBiteFinalGraphNoBlueBlueRedTriangle ω
          ⟨w, u, v, ((TwoBiteFinalGraph ω).2.1).symm huwB,
            ((TwoBiteFinalGraph ω).2.1).symm hvwB, huvR⟩
  · rcases edgeColor huw with huwR | huwB
    · rcases edgeColor hvw with hvwR | hvwB
      · exact TwoBiteFinalGraphNoRedRedBlueTriangle ω
          ⟨w, u, v, ((TwoBiteFinalGraph ω).1).symm huwR,
            ((TwoBiteFinalGraph ω).1).symm hvwR, huvB⟩
      · exact TwoBiteFinalGraphNoBlueBlueRedTriangle ω
          ⟨v, u, w, ((TwoBiteFinalGraph ω).2.1).symm huvB, hvwB, huwR⟩
    · rcases edgeColor hvw with hvwR | hvwB
      · exact TwoBiteFinalGraphNoBlueBlueRedTriangle ω ⟨u, v, w, huvB, huwB, hvwR⟩
      · exact TwoBiteFinalGraphNoBlueTriangle ω ⟨u, v, w, huvB, huwB, hvwB⟩
