import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Sqrt

namespace Twobites

open SimpleGraph

noncomputable section

/-- A paper-facing witness for Theorem `main` at a fixed value of `n`. -/
def triangleFreeWithSmallIndepNum (ε : ℝ) (n : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n),
    G.CliqueFree 3 ∧
      (G.indepNum : ℝ) < (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))

/-- A witness that `R(3, k)` is larger than `n`: a graph on `n` vertices with no triangle and no
independent set of size `k`. -/
def triangleFreeRamseyWitness (n k : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.IndepSetFree k

/-- A local off-diagonal Ramsey-number definition, included because mathlib does not appear to
provide one directly. -/
def offDiagonalRamseyNumber (s t : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬ (G.CliqueFree s ∧ G.IndepSetFree t)}

/-- The paper's `R(3, k)` in the local Ramsey-number notation used in this project. -/
def triangleRamseyNumber (k : ℕ) : ℕ :=
  offDiagonalRamseyNumber 3 k

end

end Twobites
