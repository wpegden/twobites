import Tablet.Preamble

-- [TABLET NODE: NoDistinctTriangleCliqueFree]

theorem NoDistinctTriangleCliqueFree {α : Type*} (G : SimpleGraph α)
    (h :
      ¬ ∃ u v w : α,
        u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
          G.Adj u v ∧ G.Adj u w ∧ G.Adj v w) :
    G.CliqueFree 3 := by
-- BODY
  rw [SimpleGraph.cliqueFree_iff]
  constructor
  intro f
  have h01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
  have h02 : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
  have h12 : (1 : Fin 3) ≠ (2 : Fin 3) := by decide
  have hf01 : f (0 : Fin 3) ≠ f (1 : Fin 3) := by
    intro hEq
    exact h01 (f.injective hEq)
  have hf02 : f (0 : Fin 3) ≠ f (2 : Fin 3) := by
    intro hEq
    exact h02 (f.injective hEq)
  have hf12 : f (1 : Fin 3) ≠ f (2 : Fin 3) := by
    intro hEq
    exact h12 (f.injective hEq)
  have hadj01 : G.Adj (f (0 : Fin 3)) (f (1 : Fin 3)) := by
    simpa [SimpleGraph.Copy.toHom_apply] using
      f.toHom.map_adj (by simp [SimpleGraph.completeGraph])
  have hadj02 : G.Adj (f (0 : Fin 3)) (f (2 : Fin 3)) := by
    simpa [SimpleGraph.Copy.toHom_apply] using
      f.toHom.map_adj (by simp [SimpleGraph.completeGraph])
  have hadj12 : G.Adj (f (1 : Fin 3)) (f (2 : Fin 3)) := by
    simpa [SimpleGraph.Copy.toHom_apply] using
      f.toHom.map_adj (by simp [SimpleGraph.completeGraph])
  exact h ⟨f (0 : Fin 3), f (1 : Fin 3), f (2 : Fin 3), hf01, hf02, hf12,
    hadj01, hadj02, hadj12⟩
