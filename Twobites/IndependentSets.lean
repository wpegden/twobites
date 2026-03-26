import Twobites.Construction
import Mathlib.Data.Finset.Basic

namespace Twobites

/-- The paper's ambient vertex type `V_R ∪ V_B`, represented as a tagged disjoint union. -/
abbrev BaseVertex (m : ℕ) := Fin m ⊕ Fin m

namespace ConstructionData

variable {n m : ℕ}

noncomputable section

/-- Paper notation `X_v(I)`: vertices of `I` lying in the lifted neighborhood of the base vertex
`v ∈ V_R ∪ V_B`. -/
def X (C : ConstructionData n m) (I : Finset (Fin n)) : BaseVertex m → Finset (Fin n) := by
  classical
  intro x
  cases x with
  | inl r => exact I.filter fun v => C.redBase.Adj r (C.redProj v)
  | inr b => exact I.filter fun v => C.blueBase.Adj b (C.blueProj v)

/-- Paper notation `X_v^+(I)`: the forward-neighborhood analogue of `X_v(I)` used for
monochromatic deletions. -/
def XPlus (C : ConstructionData n m) (I : Finset (Fin n)) : BaseVertex m → Finset (Fin n) := by
  classical
  intro x
  cases x with
  | inl r => exact I.filter fun v => C.redBase.Adj r (C.redProj v) ∧ r < C.redProj v
  | inr b => exact I.filter fun v => C.blueBase.Adj b (C.blueProj v) ∧ b < C.blueProj v

/-- The paper's closed-pair predicate `C(I)`, expressed on ordered pairs of distinct vertices of
`I`. -/
def ClosedPair (C : ConstructionData n m) (I : Finset (Fin n)) (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ∃ x : BaseVertex m, v ∈ C.X I x ∧ w ∈ C.X I x

/-- The paper's `C^+(I)` predicate, built from the forward-neighborhood sets `X_v^+(I)`. -/
def ClosedPairPlus (C : ConstructionData n m) (I : Finset (Fin n)) (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ∃ x : BaseVertex m, v ∈ C.XPlus I x ∧ w ∈ C.XPlus I x

/-- The paper's open-pair predicate `O(I)`. -/
def OpenPair (C : ConstructionData n m) (I : Finset (Fin n)) (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ¬ C.ClosedPair I v w

/-- The paper's `O^+(I)` predicate. -/
def OpenPairPlus (C : ConstructionData n m) (I : Finset (Fin n)) (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ¬ C.ClosedPairPlus I v w

@[simp] theorem mem_X_red (C : ConstructionData n m) {I : Finset (Fin n)} {r : Fin m}
    {v : Fin n} : v ∈ C.X I (Sum.inl r) ↔ v ∈ I ∧ C.redBase.Adj r (C.redProj v) := by
  classical
  simp [X]

@[simp] theorem mem_X_blue (C : ConstructionData n m) {I : Finset (Fin n)} {b : Fin m}
    {v : Fin n} : v ∈ C.X I (Sum.inr b) ↔ v ∈ I ∧ C.blueBase.Adj b (C.blueProj v) := by
  classical
  simp [X]

@[simp] theorem mem_XPlus_red (C : ConstructionData n m) {I : Finset (Fin n)} {r : Fin m}
    {v : Fin n} :
    v ∈ C.XPlus I (Sum.inl r) ↔ v ∈ I ∧ C.redBase.Adj r (C.redProj v) ∧ r < C.redProj v := by
  classical
  simp [XPlus]

@[simp] theorem mem_XPlus_blue (C : ConstructionData n m) {I : Finset (Fin n)} {b : Fin m}
    {v : Fin n} :
    v ∈ C.XPlus I (Sum.inr b) ↔
      v ∈ I ∧ C.blueBase.Adj b (C.blueProj v) ∧ b < C.blueProj v := by
  classical
  simp [XPlus]

theorem mem_X_of_mem_XPlus (C : ConstructionData n m) {I : Finset (Fin n)} {x : BaseVertex m}
    {v : Fin n} (hv : v ∈ C.XPlus I x) : v ∈ C.X I x := by
  cases x with
  | inl r =>
      rcases (C.mem_XPlus_red).1 hv with ⟨hvI, hAdj, _⟩
      exact (C.mem_X_red).2 ⟨hvI, hAdj⟩
  | inr b =>
      rcases (C.mem_XPlus_blue).1 hv with ⟨hvI, hAdj, _⟩
      exact (C.mem_X_blue).2 ⟨hvI, hAdj⟩

theorem closedPair_comm (C : ConstructionData n m) {I : Finset (Fin n)} {v w : Fin n} :
    C.ClosedPair I v w ↔ C.ClosedPair I w v := by
  constructor
  · rintro ⟨hvI, hwI, hvw, x, hvX, hwX⟩
    exact ⟨hwI, hvI, hvw.symm, x, hwX, hvX⟩
  · rintro ⟨hwI, hvI, hwv, x, hwX, hvX⟩
    exact ⟨hvI, hwI, hwv.symm, x, hvX, hwX⟩

theorem closedPairPlus_to_closedPair (C : ConstructionData n m) {I : Finset (Fin n)}
    {v w : Fin n} (h : C.ClosedPairPlus I v w) : C.ClosedPair I v w := by
  rcases h with ⟨hvI, hwI, hvw, x, hvX, hwX⟩
  exact ⟨hvI, hwI, hvw, x, C.mem_X_of_mem_XPlus hvX, C.mem_X_of_mem_XPlus hwX⟩

theorem closedPair_of_redMonochromaticDeletionWitness (C : ConstructionData n m)
    {I : Finset (Fin n)} {u v w : Fin n} (hvI : v ∈ I) (hwI : w ∈ I) (hvw : v ≠ w)
    (h : C.redMonochromaticDeletionWitness u v w) : C.ClosedPair I v w := by
  rcases h with ⟨huv, huw, -, -⟩
  exact ⟨hvI, hwI, hvw, Sum.inl (C.redProj u), (C.mem_X_red).2 ⟨hvI, huv⟩,
    (C.mem_X_red).2 ⟨hwI, huw⟩⟩

theorem closedPair_of_blueMonochromaticDeletionWitness (C : ConstructionData n m)
    {I : Finset (Fin n)} {u v w : Fin n} (hvI : v ∈ I) (hwI : w ∈ I) (hvw : v ≠ w)
    (h : C.blueMonochromaticDeletionWitness u v w) : C.ClosedPair I v w := by
  rcases h with ⟨huv, huw, -, -⟩
  exact ⟨hvI, hwI, hvw, Sum.inr (C.blueProj u), (C.mem_X_blue).2 ⟨hvI, huv⟩,
    (C.mem_X_blue).2 ⟨hwI, huw⟩⟩

theorem closedPair_of_redMixedDeletionWitness (C : ConstructionData n m)
    {I : Finset (Fin n)} {u v w : Fin n} (hvI : v ∈ I) (hwI : w ∈ I) (hvw : v ≠ w)
    (h : C.redMixedDeletionWitness u v w) : C.ClosedPair I v w := by
  rcases h with ⟨huv, huw, -⟩
  exact ⟨hvI, hwI, hvw, Sum.inr (C.blueProj u), (C.mem_X_blue).2 ⟨hvI, huv⟩,
    (C.mem_X_blue).2 ⟨hwI, huw⟩⟩

theorem closedPair_of_blueMixedDeletionWitness (C : ConstructionData n m)
    {I : Finset (Fin n)} {u v w : Fin n} (hvI : v ∈ I) (hwI : w ∈ I) (hvw : v ≠ w)
    (h : C.blueMixedDeletionWitness u v w) : C.ClosedPair I v w := by
  rcases h with ⟨huv, huw, -⟩
  exact ⟨hvI, hwI, hvw, Sum.inl (C.redProj u), (C.mem_X_red).2 ⟨hvI, huv⟩,
    (C.mem_X_red).2 ⟨hwI, huw⟩⟩

end

end ConstructionData

end Twobites
