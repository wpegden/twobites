import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Basic

namespace Twobites

open SimpleGraph

/-- Paper Section 2 construction data: two base graphs on `Fin m` together with the injective map
`π : Fin n ↪ Fin m × Fin m` used to lift them to the final vertex set. -/
structure ConstructionData (n m : ℕ) where
  redBase : SimpleGraph (Fin m)
  blueBase : SimpleGraph (Fin m)
  embedding : Fin n ↪ Fin m × Fin m

namespace ConstructionData

variable {n m : ℕ} (C : ConstructionData n m)

/-- The paper's map `π`. -/
def pairEmbedding : Fin n ↪ Fin m × Fin m :=
  C.embedding

/-- The red projection `π_R`. -/
def redProj (v : Fin n) : Fin m :=
  (C.embedding v).1

/-- The blue projection `π_B`. -/
def blueProj (v : Fin n) : Fin m :=
  (C.embedding v).2

/-- The image of a finite vertex set under `π`. -/
def pairImage (s : Finset (Fin n)) : Finset (Fin m × Fin m) :=
  s.image C.embedding

/-- The red projection of a finite vertex set. -/
def redImage (s : Finset (Fin n)) : Finset (Fin m) :=
  s.image C.redProj

/-- The blue projection of a finite vertex set. -/
def blueImage (s : Finset (Fin n)) : Finset (Fin m) :=
  s.image C.blueProj

/-- The fiber `F(r)` over a red-coordinate vertex. -/
def redFiber (r : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun v => C.redProj v = r

/-- The fiber `F(b)` over a blue-coordinate vertex. -/
def blueFiber (b : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun v => C.blueProj v = b

/-- The red lifted graph on `Fin n`, obtained by pulling back `G_R` along `π_R`. -/
def redLift : SimpleGraph (Fin n) :=
  C.redBase.comap C.redProj

/-- The blue lifted graph on `Fin n`, obtained by pulling back `G_B` along `π_B`. -/
def blueLift : SimpleGraph (Fin n) :=
  C.blueBase.comap C.blueProj

/-- The simple graph obtained before the triangle-deletion step by forgetting edge colors and
keeping any edge present in at least one lifted layer. -/
def rawGraph : SimpleGraph (Fin n) :=
  C.redLift ⊔ C.blueLift

@[simp] theorem pairEmbedding_apply (v : Fin n) : C.pairEmbedding v = C.embedding v :=
  rfl

@[simp] theorem redProj_eq_fst (v : Fin n) : C.redProj v = (C.embedding v).1 :=
  rfl

@[simp] theorem blueProj_eq_snd (v : Fin n) : C.blueProj v = (C.embedding v).2 :=
  rfl

@[simp] theorem mem_pairImage {s : Finset (Fin n)} {p : Fin m × Fin m} :
    p ∈ C.pairImage s ↔ ∃ v ∈ s, C.embedding v = p := by
  simp [pairImage]

@[simp] theorem mem_redImage {s : Finset (Fin n)} {r : Fin m} :
    r ∈ C.redImage s ↔ ∃ v ∈ s, C.redProj v = r := by
  simp [redImage]

@[simp] theorem mem_blueImage {s : Finset (Fin n)} {b : Fin m} :
    b ∈ C.blueImage s ↔ ∃ v ∈ s, C.blueProj v = b := by
  simp [blueImage]

@[simp] theorem mem_redFiber {r : Fin m} {v : Fin n} :
    v ∈ C.redFiber r ↔ C.redProj v = r := by
  simp [redFiber]

@[simp] theorem mem_blueFiber {b : Fin m} {v : Fin n} :
    v ∈ C.blueFiber b ↔ C.blueProj v = b := by
  simp [blueFiber]

theorem eq_of_proj_eq_proj {v w : Fin n}
    (hR : C.redProj v = C.redProj w) (hB : C.blueProj v = C.blueProj w) : v = w := by
  apply C.embedding.injective
  exact Prod.ext hR hB

@[simp] theorem redLift_adj_iff {v w : Fin n} :
    C.redLift.Adj v w ↔ C.redBase.Adj (C.redProj v) (C.redProj w) := by
  rfl

@[simp] theorem blueLift_adj_iff {v w : Fin n} :
    C.blueLift.Adj v w ↔ C.blueBase.Adj (C.blueProj v) (C.blueProj w) := by
  rfl

@[simp] theorem rawGraph_adj_iff {v w : Fin n} :
    C.rawGraph.Adj v w ↔
      C.redBase.Adj (C.redProj v) (C.redProj w) ∨
        C.blueBase.Adj (C.blueProj v) (C.blueProj w) := by
  simp [rawGraph, redLift, blueLift]

@[simp] theorem mem_redLift_neighborSet {v w : Fin n} :
    w ∈ C.redLift.neighborSet v ↔ C.redBase.Adj (C.redProj v) (C.redProj w) := by
  simp [SimpleGraph.mem_neighborSet, redLift]

@[simp] theorem mem_blueLift_neighborSet {v w : Fin n} :
    w ∈ C.blueLift.neighborSet v ↔ C.blueBase.Adj (C.blueProj v) (C.blueProj w) := by
  simp [SimpleGraph.mem_neighborSet, blueLift]

theorem redLift_neighborSet_eq_of_redProj_eq {v w : Fin n}
    (h : C.redProj v = C.redProj w) :
    C.redLift.neighborSet v = C.redLift.neighborSet w := by
  ext u
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborSet, C.redLift_adj_iff,
    C.redLift_adj_iff, h]

theorem blueLift_neighborSet_eq_of_blueProj_eq {v w : Fin n}
    (h : C.blueProj v = C.blueProj w) :
    C.blueLift.neighborSet v = C.blueLift.neighborSet w := by
  ext u
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborSet, C.blueLift_adj_iff,
    C.blueLift_adj_iff, h]

end ConstructionData

end Twobites
