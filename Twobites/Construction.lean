import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Basic

namespace Twobites

open SimpleGraph

/-- The ordered representative of an unordered pair in a linearly ordered type. -/
def orderedPair {α : Type*} [LinearOrder α] (a b : α) : α × α :=
  (min a b, max a b)

@[simp] theorem orderedPair_comm {α : Type*} [LinearOrder α] (a b : α) :
    orderedPair a b = orderedPair b a := by
  simp [orderedPair, min_comm, max_comm]

/-- Lexicographic order on ordered pairs. This is the ordering used in the paper for the red and
blue coordinate pairs. -/
def pairLex {α : Type*} [LinearOrder α] (p q : α × α) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

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

/-- The red-coordinate pair attached to an edge of the lifted graph. -/
def redCoordinatePair (v w : Fin n) : Fin m × Fin m :=
  orderedPair (C.redProj v) (C.redProj w)

/-- The blue-coordinate pair attached to an edge of the lifted graph. -/
def blueCoordinatePair (v w : Fin n) : Fin m × Fin m :=
  orderedPair (C.blueProj v) (C.blueProj w)

/-- In a red triangle, the edge `vw` is the one deleted by the paper's lexicographic rule when its
coordinate pair comes later than the two coordinate pairs incident to `u`. -/
def redPairLaterInTriangle (u v w : Fin n) : Prop :=
  pairLex (C.redCoordinatePair u v) (C.redCoordinatePair v w) ∧
    pairLex (C.redCoordinatePair u w) (C.redCoordinatePair v w)

/-- The blue analogue of `redPairLaterInTriangle`. -/
def bluePairLaterInTriangle (u v w : Fin n) : Prop :=
  pairLex (C.blueCoordinatePair u v) (C.blueCoordinatePair v w) ∧
    pairLex (C.blueCoordinatePair u w) (C.blueCoordinatePair v w)

/-- A witness that the red edge `vw` is deleted because it is the last edge of a monochromatic red
triangle, following the paper's lexicographic rule. -/
def redMonochromaticDeletionWitness (u v w : Fin n) : Prop :=
  C.redLift.Adj u v ∧ C.redLift.Adj u w ∧ C.redLift.Adj v w ∧ C.redPairLaterInTriangle u v w

/-- The blue analogue of `redMonochromaticDeletionWitness`. -/
def blueMonochromaticDeletionWitness (u v w : Fin n) : Prop :=
  C.blueLift.Adj u v ∧ C.blueLift.Adj u w ∧ C.blueLift.Adj v w ∧ C.bluePairLaterInTriangle u v w

/-- A witness that the red edge `vw` is deleted because `uvw` is a mixed triangle with two blue
edges from `u` and one red edge between `v` and `w`. -/
def redMixedDeletionWitness (u v w : Fin n) : Prop :=
  C.blueLift.Adj u v ∧ C.blueLift.Adj u w ∧ C.redLift.Adj v w

/-- A witness that the blue edge `vw` is deleted because `uvw` is a mixed triangle with two red
edges from `u` and one blue edge between `v` and `w`. -/
def blueMixedDeletionWitness (u v w : Fin n) : Prop :=
  C.redLift.Adj u v ∧ C.redLift.Adj u w ∧ C.blueLift.Adj v w

/-- The paper's red deletion predicate after aggregating over all possible witnesses `u`. -/
def redDeleted (v w : Fin n) : Prop :=
  ∃ u, C.redMonochromaticDeletionWitness u v w ∨ C.redMixedDeletionWitness u v w

/-- The paper's blue deletion predicate after aggregating over all possible witnesses `u`. -/
def blueDeleted (v w : Fin n) : Prop :=
  ∃ u, C.blueMonochromaticDeletionWitness u v w ∨ C.blueMixedDeletionWitness u v w

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

@[simp] theorem redCoordinatePair_comm (v w : Fin n) :
    C.redCoordinatePair v w = C.redCoordinatePair w v := by
  simp [redCoordinatePair, orderedPair_comm]

@[simp] theorem blueCoordinatePair_comm (v w : Fin n) :
    C.blueCoordinatePair v w = C.blueCoordinatePair w v := by
  simp [blueCoordinatePair, orderedPair_comm]

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

theorem redPairLaterInTriangle_comm {u v w : Fin n} :
    C.redPairLaterInTriangle u v w ↔ C.redPairLaterInTriangle u w v := by
  simp [redPairLaterInTriangle, and_comm]

theorem bluePairLaterInTriangle_comm {u v w : Fin n} :
    C.bluePairLaterInTriangle u v w ↔ C.bluePairLaterInTriangle u w v := by
  simp [bluePairLaterInTriangle, and_comm]

theorem redMonochromaticDeletionWitness_comm {u v w : Fin n} :
    C.redMonochromaticDeletionWitness u v w ↔ C.redMonochromaticDeletionWitness u w v := by
  constructor
  · rintro ⟨huv, huw, hvw, hLater⟩
    exact ⟨huw, huv, hvw.symm, (C.redPairLaterInTriangle_comm).1 hLater⟩
  · rintro ⟨huw, huv, hwv, hLater⟩
    exact ⟨huv, huw, hwv.symm, (C.redPairLaterInTriangle_comm).2 hLater⟩

theorem blueMonochromaticDeletionWitness_comm {u v w : Fin n} :
    C.blueMonochromaticDeletionWitness u v w ↔ C.blueMonochromaticDeletionWitness u w v := by
  constructor
  · rintro ⟨huv, huw, hvw, hLater⟩
    exact ⟨huw, huv, hvw.symm, (C.bluePairLaterInTriangle_comm).1 hLater⟩
  · rintro ⟨huw, huv, hwv, hLater⟩
    exact ⟨huv, huw, hwv.symm, (C.bluePairLaterInTriangle_comm).2 hLater⟩

theorem redMixedDeletionWitness_comm {u v w : Fin n} :
    C.redMixedDeletionWitness u v w ↔ C.redMixedDeletionWitness u w v := by
  constructor
  · rintro ⟨huv, huw, hvw⟩
    exact ⟨huw, huv, hvw.symm⟩
  · rintro ⟨huw, huv, hwv⟩
    exact ⟨huv, huw, hwv.symm⟩

theorem blueMixedDeletionWitness_comm {u v w : Fin n} :
    C.blueMixedDeletionWitness u v w ↔ C.blueMixedDeletionWitness u w v := by
  constructor
  · rintro ⟨huv, huw, hvw⟩
    exact ⟨huw, huv, hvw.symm⟩
  · rintro ⟨huw, huv, hwv⟩
    exact ⟨huv, huw, hwv.symm⟩

theorem redDeleted_comm {v w : Fin n} : C.redDeleted v w ↔ C.redDeleted w v := by
  constructor
  · rintro ⟨u, hmono | hmixed⟩
    · exact ⟨u, Or.inl ((C.redMonochromaticDeletionWitness_comm).1 hmono)⟩
    · exact ⟨u, Or.inr ((C.redMixedDeletionWitness_comm).1 hmixed)⟩
  · rintro ⟨u, hmono | hmixed⟩
    · exact ⟨u, Or.inl ((C.redMonochromaticDeletionWitness_comm).2 hmono)⟩
    · exact ⟨u, Or.inr ((C.redMixedDeletionWitness_comm).2 hmixed)⟩

theorem blueDeleted_comm {v w : Fin n} : C.blueDeleted v w ↔ C.blueDeleted w v := by
  constructor
  · rintro ⟨u, hmono | hmixed⟩
    · exact ⟨u, Or.inl ((C.blueMonochromaticDeletionWitness_comm).1 hmono)⟩
    · exact ⟨u, Or.inr ((C.blueMixedDeletionWitness_comm).1 hmixed)⟩
  · rintro ⟨u, hmono | hmixed⟩
    · exact ⟨u, Or.inl ((C.blueMonochromaticDeletionWitness_comm).2 hmono)⟩
    · exact ⟨u, Or.inr ((C.blueMixedDeletionWitness_comm).2 hmixed)⟩

/-- The retained red layer after the triangle-deletion step. -/
def retainedRed : SimpleGraph (Fin n) where
  Adj v w := C.redLift.Adj v w ∧ ¬ C.redDeleted v w
  symm := by
    intro v w hvw
    refine ⟨hvw.1.symm, ?_⟩
    intro hdel
    exact hvw.2 ((C.redDeleted_comm).2 hdel)
  loopless := ⟨fun v hv => C.redLift.loopless.irrefl v hv.1⟩

/-- The retained blue layer after the triangle-deletion step. -/
def retainedBlue : SimpleGraph (Fin n) where
  Adj v w := C.blueLift.Adj v w ∧ ¬ C.blueDeleted v w
  symm := by
    intro v w hvw
    refine ⟨hvw.1.symm, ?_⟩
    intro hdel
    exact hvw.2 ((C.blueDeleted_comm).2 hdel)
  loopless := ⟨fun v hv => C.blueLift.loopless.irrefl v hv.1⟩

/-- The final simple graph obtained from the retained red and blue layers by forgetting colors and
collapsing any double edge. -/
def finalGraph : SimpleGraph (Fin n) :=
  C.retainedRed ⊔ C.retainedBlue

@[simp] theorem retainedRed_adj_iff {v w : Fin n} :
    C.retainedRed.Adj v w ↔ C.redLift.Adj v w ∧ ¬ C.redDeleted v w := by
  rfl

@[simp] theorem retainedBlue_adj_iff {v w : Fin n} :
    C.retainedBlue.Adj v w ↔ C.blueLift.Adj v w ∧ ¬ C.blueDeleted v w := by
  rfl

@[simp] theorem finalGraph_adj_iff {v w : Fin n} :
    C.finalGraph.Adj v w ↔ C.retainedRed.Adj v w ∨ C.retainedBlue.Adj v w := by
  simp [finalGraph]

theorem retainedRed_le_redLift : C.retainedRed ≤ C.redLift := by
  intro v w hvw
  exact hvw.1

theorem retainedBlue_le_blueLift : C.retainedBlue ≤ C.blueLift := by
  intro v w hvw
  exact hvw.1

theorem finalGraph_le_rawGraph : C.finalGraph ≤ C.rawGraph := by
  intro v w hvw
  rcases (C.finalGraph_adj_iff).1 hvw with hred | hblue
  · exact Or.inl ((C.retainedRed_le_redLift) hred)
  · exact Or.inr ((C.retainedBlue_le_blueLift) hblue)

theorem redDeleted_of_redMonochromaticDeletionWitness {u v w : Fin n}
    (h : C.redMonochromaticDeletionWitness u v w) : C.redDeleted v w :=
  ⟨u, Or.inl h⟩

theorem redDeleted_of_redMixedDeletionWitness {u v w : Fin n}
    (h : C.redMixedDeletionWitness u v w) : C.redDeleted v w :=
  ⟨u, Or.inr h⟩

theorem blueDeleted_of_blueMonochromaticDeletionWitness {u v w : Fin n}
    (h : C.blueMonochromaticDeletionWitness u v w) : C.blueDeleted v w :=
  ⟨u, Or.inl h⟩

theorem blueDeleted_of_blueMixedDeletionWitness {u v w : Fin n}
    (h : C.blueMixedDeletionWitness u v w) : C.blueDeleted v w :=
  ⟨u, Or.inr h⟩

theorem not_retainedRed_adj_of_redDeleted {v w : Fin n} (hdel : C.redDeleted v w) :
    ¬ C.retainedRed.Adj v w := by
  intro hret
  exact hret.2 hdel

theorem not_retainedBlue_adj_of_blueDeleted {v w : Fin n} (hdel : C.blueDeleted v w) :
    ¬ C.retainedBlue.Adj v w := by
  intro hret
  exact hret.2 hdel

theorem not_retainedRed_adj_of_redMonochromaticDeletionWitness {u v w : Fin n}
    (h : C.redMonochromaticDeletionWitness u v w) : ¬ C.retainedRed.Adj v w := by
  exact C.not_retainedRed_adj_of_redDeleted (C.redDeleted_of_redMonochromaticDeletionWitness h)

theorem not_retainedRed_adj_of_redMixedDeletionWitness {u v w : Fin n}
    (h : C.redMixedDeletionWitness u v w) : ¬ C.retainedRed.Adj v w := by
  exact C.not_retainedRed_adj_of_redDeleted (C.redDeleted_of_redMixedDeletionWitness h)

theorem not_retainedBlue_adj_of_blueMonochromaticDeletionWitness {u v w : Fin n}
    (h : C.blueMonochromaticDeletionWitness u v w) : ¬ C.retainedBlue.Adj v w := by
  exact C.not_retainedBlue_adj_of_blueDeleted
    (C.blueDeleted_of_blueMonochromaticDeletionWitness h)

theorem not_retainedBlue_adj_of_blueMixedDeletionWitness {u v w : Fin n}
    (h : C.blueMixedDeletionWitness u v w) : ¬ C.retainedBlue.Adj v w := by
  exact C.not_retainedBlue_adj_of_blueDeleted (C.blueDeleted_of_blueMixedDeletionWitness h)

theorem not_finalGraph_adj_of_redTriangle {u v w : Fin n}
    (huv : C.redLift.Adj u v) (huw : C.redLift.Adj u w) (hvw : C.redLift.Adj v w)
    (hLater : C.redPairLaterInTriangle u v w) : ¬ C.finalGraph.Adj v w := by
  intro hfinal
  rcases (C.finalGraph_adj_iff).1 hfinal with hred | hblue
  · exact hred.2 (C.redDeleted_of_redMonochromaticDeletionWitness ⟨huv, huw, hvw, hLater⟩)
  · exact hblue.2 (C.blueDeleted_of_blueMixedDeletionWitness ⟨huv, huw, hblue.1⟩)

theorem not_finalGraph_adj_of_blueTriangle {u v w : Fin n}
    (huv : C.blueLift.Adj u v) (huw : C.blueLift.Adj u w) (hvw : C.blueLift.Adj v w)
    (hLater : C.bluePairLaterInTriangle u v w) : ¬ C.finalGraph.Adj v w := by
  intro hfinal
  rcases (C.finalGraph_adj_iff).1 hfinal with hred | hblue
  · exact hred.2 (C.redDeleted_of_redMixedDeletionWitness ⟨huv, huw, hred.1⟩)
  · exact hblue.2 (C.blueDeleted_of_blueMonochromaticDeletionWitness ⟨huv, huw, hvw, hLater⟩)

end ConstructionData

end Twobites
