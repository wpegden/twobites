import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Fin.Basic

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

theorem least_of_three {α : Type*} [LinearOrder α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (a < b ∧ a < c) ∨ (b < a ∧ b < c) ∨ (c < a ∧ c < b) := by
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · rcases lt_or_gt_of_ne hac with hac' | hca'
    · exact Or.inl ⟨hab', hac'⟩
    · exact Or.inr (Or.inr ⟨hca', hca'.trans hab'⟩)
  · rcases lt_or_gt_of_ne hbc with hbc' | hcb'
    · exact Or.inr (Or.inl ⟨hba', hbc'⟩)
    · exact Or.inr (Or.inr ⟨hcb'.trans hba', hcb'⟩)

/-- Paper Section 2 construction data: two base graphs on `Fin m` together with the injective map
`π : Fin n ↪ Fin m × Fin m` used to lift them to the final vertex set. -/
structure ConstructionData (n m : ℕ) where
  redBase : SimpleGraph (Fin m)
  blueBase : SimpleGraph (Fin m)
  embedding : Fin n ↪ Fin m × Fin m

noncomputable instance instFintypeConstructionData (n m : ℕ) : Fintype (ConstructionData n m) :=
  Fintype.ofEquiv
    ((SimpleGraph (Fin m) × SimpleGraph (Fin m)) × (Fin n ↪ Fin m × Fin m))
    { toFun := fun t =>
        { redBase := t.1.1
          blueBase := t.1.2
          embedding := t.2 }
      invFun := fun C => ((C.redBase, C.blueBase), C.embedding)
      left_inv := by
        intro t
        cases t
        rfl
      right_inv := by
        intro C
        cases C
        rfl
      }

namespace ConstructionData

variable {n m : ℕ} (C : ConstructionData n m)

/-- The literal finite sample space of all construction outcomes with parameters `(n,m)`. This is
the unweighted ambient space underlying the still-missing global probability layer. -/
noncomputable def sampleSpace (n m : ℕ) : Finset (ConstructionData n m) :=
  Finset.univ

@[simp] theorem mem_sampleSpace (C : ConstructionData n m) :
    C ∈ ConstructionData.sampleSpace n m := by
  simp [ConstructionData.sampleSpace]

/-- The paper's map `π`. -/
def pairEmbedding : Fin n ↪ Fin m × Fin m :=
  C.embedding

/-- A balanced cyclic-band embedding of `Fin n` into `Fin m × Fin m`, available whenever `n`
fits inside a width-`b` band and `b ≤ m`. Each row and each column supports at most `b` points;
this is used later to manufacture explicit finite witnesses for the good event. -/
noncomputable def balancedBandEmbedding {n m b : ℕ} (hn : n ≤ m * b) (hb : b ≤ m) :
    Fin n ↪ Fin m × Fin m := by
  classical
  let e : Fin n ↪ Fin (m * b) := Fin.castLEEmb hn
  refine
    { toFun := fun i =>
        let p : Fin m × Fin b := finProdFinEquiv.symm (e i)
        (p.1, p.1 + Fin.castLE hb p.2)
      inj' := ?_ }
  intro i j hij
  have hfst :
      (finProdFinEquiv.symm (e i)).1 = (finProdFinEquiv.symm (e j)).1 := by
    simpa using congrArg Prod.fst hij
  have hsnd :
      (finProdFinEquiv.symm (e i)).1 + Fin.castLE hb (finProdFinEquiv.symm (e i)).2 =
        (finProdFinEquiv.symm (e j)).1 + Fin.castLE hb (finProdFinEquiv.symm (e j)).2 := by
    simpa using congrArg Prod.snd hij
  rw [hfst] at hsnd
  have hband :
      (finProdFinEquiv.symm (e i)).2 = (finProdFinEquiv.symm (e j)).2 := by
    apply Fin.castLE_injective hb
    exact add_left_cancel hsnd
  have hpair : finProdFinEquiv.symm (e i) = finProdFinEquiv.symm (e j) := by
    exact Prod.ext hfst hband
  have he : e i = e j := by
    simpa only [Equiv.apply_symm_apply] using congrArg finProdFinEquiv hpair
  exact e.injective he

@[simp] theorem balancedBandEmbedding_fst {n m b : ℕ} (hn : n ≤ m * b) (hb : b ≤ m)
    (i : Fin n) :
    (balancedBandEmbedding hn hb i).1 = (finProdFinEquiv.symm ((Fin.castLEEmb hn) i)).1 := rfl

@[simp] theorem balancedBandEmbedding_snd {n m b : ℕ} (hn : n ≤ m * b) (hb : b ≤ m)
    (i : Fin n) :
    (balancedBandEmbedding hn hb i).2 =
      (finProdFinEquiv.symm ((Fin.castLEEmb hn) i)).1 +
        Fin.castLE hb (finProdFinEquiv.symm ((Fin.castLEEmb hn) i)).2 := rfl

/-- The explicit empty-base construction built from the balanced cyclic-band embedding. -/
noncomputable def emptyBalancedConstructionData {n m b : ℕ} (hn : n ≤ m * b) (hb : b ≤ m) :
    ConstructionData n m where
  redBase := ⊥
  blueBase := ⊥
  embedding := balancedBandEmbedding hn hb

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

theorem redPairLaterInTriangle_of_lt_lt {u v w : Fin n}
    (huv : C.redProj u < C.redProj v) (huw : C.redProj u < C.redProj w) :
    C.redPairLaterInTriangle u v w := by
  unfold redPairLaterInTriangle pairLex
  constructor
  · left
    simpa [redCoordinatePair, orderedPair, min_eq_left (le_of_lt huv)] using
      (show C.redProj u < C.redProj v ∧
        (C.redProj u < C.redProj w ∨ C.redProj v < C.redProj w) from ⟨huv, Or.inl huw⟩)
  · left
    simpa [redCoordinatePair, orderedPair, min_eq_left (le_of_lt huw)] using
      (show (C.redProj u < C.redProj v ∨ C.redProj w < C.redProj v) ∧
        C.redProj u < C.redProj w from ⟨Or.inl huv, huw⟩)

theorem bluePairLaterInTriangle_of_lt_lt {u v w : Fin n}
    (huv : C.blueProj u < C.blueProj v) (huw : C.blueProj u < C.blueProj w) :
    C.bluePairLaterInTriangle u v w := by
  unfold bluePairLaterInTriangle pairLex
  constructor
  · left
    simpa [blueCoordinatePair, orderedPair, min_eq_left (le_of_lt huv)] using
      (show C.blueProj u < C.blueProj v ∧
        (C.blueProj u < C.blueProj w ∨ C.blueProj v < C.blueProj w) from ⟨huv, Or.inl huw⟩)
  · left
    simpa [blueCoordinatePair, orderedPair, min_eq_left (le_of_lt huw)] using
      (show (C.blueProj u < C.blueProj v ∨ C.blueProj w < C.blueProj v) ∧
        C.blueProj u < C.blueProj w from ⟨Or.inl huv, huw⟩)

theorem redProj_ne_of_redLift_adj {u v : Fin n} (h : C.redLift.Adj u v) :
    C.redProj u ≠ C.redProj v := by
  intro huv
  change C.redBase.Adj (C.redProj u) (C.redProj v) at h
  rw [huv] at h
  exact C.redBase.loopless.irrefl _ h

theorem blueProj_ne_of_blueLift_adj {u v : Fin n} (h : C.blueLift.Adj u v) :
    C.blueProj u ≠ C.blueProj v := by
  intro huv
  change C.blueBase.Adj (C.blueProj u) (C.blueProj v) at h
  rw [huv] at h
  exact C.blueBase.loopless.irrefl _ h

theorem exists_redPairLaterInTriangle {u v w : Fin n}
    (huv : C.redLift.Adj u v) (huw : C.redLift.Adj u w) (hvw : C.redLift.Adj v w) :
    C.redPairLaterInTriangle u v w ∨
      C.redPairLaterInTriangle v u w ∨ C.redPairLaterInTriangle w u v := by
  have huv_ne := C.redProj_ne_of_redLift_adj huv
  have huw_ne := C.redProj_ne_of_redLift_adj huw
  have hvw_ne := C.redProj_ne_of_redLift_adj hvw
  rcases least_of_three huv_ne huw_ne hvw_ne with hleast | hleast | hleast
  · exact Or.inl (C.redPairLaterInTriangle_of_lt_lt hleast.1 hleast.2)
  · exact Or.inr (Or.inl (C.redPairLaterInTriangle_of_lt_lt hleast.1 hleast.2))
  · exact Or.inr (Or.inr (C.redPairLaterInTriangle_of_lt_lt hleast.1 hleast.2))

theorem exists_bluePairLaterInTriangle {u v w : Fin n}
    (huv : C.blueLift.Adj u v) (huw : C.blueLift.Adj u w) (hvw : C.blueLift.Adj v w) :
    C.bluePairLaterInTriangle u v w ∨
      C.bluePairLaterInTriangle v u w ∨ C.bluePairLaterInTriangle w u v := by
  have huv_ne := C.blueProj_ne_of_blueLift_adj huv
  have huw_ne := C.blueProj_ne_of_blueLift_adj huw
  have hvw_ne := C.blueProj_ne_of_blueLift_adj hvw
  rcases least_of_three huv_ne huw_ne hvw_ne with hleast | hleast | hleast
  · exact Or.inl (C.bluePairLaterInTriangle_of_lt_lt hleast.1 hleast.2)
  · exact Or.inr (Or.inl (C.bluePairLaterInTriangle_of_lt_lt hleast.1 hleast.2))
  · exact Or.inr (Or.inr (C.bluePairLaterInTriangle_of_lt_lt hleast.1 hleast.2))

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

theorem not_retainedRed_triangle {u v w : Fin n}
    (huv : C.retainedRed.Adj u v) (huw : C.retainedRed.Adj u w) (hvw : C.retainedRed.Adj v w) :
    False := by
  rcases C.exists_redPairLaterInTriangle huv.1 huw.1 hvw.1 with h | h | h
  · exact C.not_retainedRed_adj_of_redMonochromaticDeletionWitness ⟨huv.1, huw.1, hvw.1, h⟩ hvw
  · exact C.not_retainedRed_adj_of_redMonochromaticDeletionWitness ⟨huv.1.symm, hvw.1, huw.1, h⟩ huw
  · exact C.not_retainedRed_adj_of_redMonochromaticDeletionWitness
      ⟨huw.1.symm, hvw.1.symm, huv.1, h⟩ huv

theorem not_retainedBlue_triangle {u v w : Fin n}
    (huv : C.retainedBlue.Adj u v) (huw : C.retainedBlue.Adj u w) (hvw : C.retainedBlue.Adj v w) :
    False := by
  rcases C.exists_bluePairLaterInTriangle huv.1 huw.1 hvw.1 with h | h | h
  · exact C.not_retainedBlue_adj_of_blueMonochromaticDeletionWitness ⟨huv.1, huw.1, hvw.1, h⟩ hvw
  · exact C.not_retainedBlue_adj_of_blueMonochromaticDeletionWitness
      ⟨huv.1.symm, hvw.1, huw.1, h⟩ huw
  · exact C.not_retainedBlue_adj_of_blueMonochromaticDeletionWitness
      ⟨huw.1.symm, hvw.1.symm, huv.1, h⟩ huv

theorem retainedRed_cliqueFree : C.retainedRed.CliqueFree 3 := by
  intro s hs
  rcases SimpleGraph.is3Clique_iff.1 hs with ⟨u, v, w, huv, huw, hvw, _⟩
  exact C.not_retainedRed_triangle huv huw hvw

theorem retainedBlue_cliqueFree : C.retainedBlue.CliqueFree 3 := by
  intro s hs
  rcases SimpleGraph.is3Clique_iff.1 hs with ⟨u, v, w, huv, huw, hvw, _⟩
  exact C.not_retainedBlue_triangle huv huw hvw

theorem not_finalGraph_triangle {u v w : Fin n}
    (huv : C.finalGraph.Adj u v) (huw : C.finalGraph.Adj u w) (hvw : C.finalGraph.Adj v w) :
    False := by
  rcases (C.finalGraph_adj_iff).1 huv with huvR | huvB
  · rcases (C.finalGraph_adj_iff).1 huw with huwR | huwB
    · rcases (C.finalGraph_adj_iff).1 hvw with hvwR | hvwB
      · exact C.not_retainedRed_triangle huvR huwR hvwR
      · exact hvwB.2 (C.blueDeleted_of_blueMixedDeletionWitness ⟨huvR.1, huwR.1, hvwB.1⟩)
    · rcases (C.finalGraph_adj_iff).1 hvw with hvwR | hvwB
      · exact huwB.2 (C.blueDeleted_of_blueMixedDeletionWitness ⟨huvR.1.symm, hvwR.1, huwB.1⟩)
      · exact huvR.2 (C.redDeleted_of_redMixedDeletionWitness ⟨huwB.1.symm, hvwB.1.symm, huvR.1⟩)
  · rcases (C.finalGraph_adj_iff).1 huw with huwR | huwB
    · rcases (C.finalGraph_adj_iff).1 hvw with hvwR | hvwB
      · exact huvB.2 (C.blueDeleted_of_blueMixedDeletionWitness ⟨huwR.1.symm, hvwR.1.symm, huvB.1⟩)
      · exact huwR.2 (C.redDeleted_of_redMixedDeletionWitness ⟨huvB.1.symm, hvwB.1, huwR.1⟩)
    · rcases (C.finalGraph_adj_iff).1 hvw with hvwR | hvwB
      · exact hvwR.2 (C.redDeleted_of_redMixedDeletionWitness ⟨huvB.1, huwB.1, hvwR.1⟩)
      · exact C.not_retainedBlue_triangle huvB huwB hvwB

theorem finalGraph_cliqueFree : C.finalGraph.CliqueFree 3 := by
  intro s hs
  rcases SimpleGraph.is3Clique_iff.1 hs with ⟨u, v, w, huv, huw, hvw, _⟩
  exact C.not_finalGraph_triangle huv huw hvw

end ConstructionData

end Twobites
