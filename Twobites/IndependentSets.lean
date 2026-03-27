import Twobites.Construction
import Twobites.ParameterBounds
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

namespace Twobites

open scoped BigOperators

/-- The paper's ambient vertex type `V_R ∪ V_B`, represented as a tagged disjoint union. -/
abbrev BaseVertex (m : ℕ) := Fin m ⊕ Fin m

/-- Predicate selecting the red side `V_R` inside `V_R ∪ V_B`. -/
def IsRedBaseVertex {m : ℕ} : BaseVertex m → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- Predicate selecting the blue side `V_B` inside `V_R ∪ V_B`. -/
def IsBlueBaseVertex {m : ℕ} : BaseVertex m → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

instance {m : ℕ} : DecidablePred (@IsRedBaseVertex m)
  | Sum.inl _ => isTrue trivial
  | Sum.inr _ => isFalse (by simp [IsRedBaseVertex])

instance {m : ℕ} : DecidablePred (@IsBlueBaseVertex m)
  | Sum.inl _ => isFalse (by simp [IsBlueBaseVertex])
  | Sum.inr _ => isTrue trivial

@[simp] theorem isRedBaseVertex_inl {m : ℕ} (r : Fin m) : IsRedBaseVertex (Sum.inl r) := trivial
@[simp] theorem not_isRedBaseVertex_inr {m : ℕ} (b : Fin m) :
    ¬ IsRedBaseVertex (Sum.inr b) := by simp [IsRedBaseVertex]
@[simp] theorem isBlueBaseVertex_inr {m : ℕ} (b : Fin m) : IsBlueBaseVertex (Sum.inr b) := trivial
@[simp] theorem not_isBlueBaseVertex_inl {m : ℕ} (r : Fin m) :
    ¬ IsBlueBaseVertex (Sum.inl r) := by simp [IsBlueBaseVertex]

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

/-- Paper notation `|X_v(I)|`. -/
def xCard (C : ConstructionData n m) (I : Finset (Fin n)) (x : BaseVertex m) : ℕ :=
  (C.X I x).card

/-- Paper notation `|X_v^+(I)|`. -/
def xPlusCard (C : ConstructionData n m) (I : Finset (Fin n)) (x : BaseVertex m) : ℕ :=
  (C.XPlus I x).card

/-- The red-coordinate projection `π_R(X_v(I))` appearing in the huge-case bounds. -/
def redProjectionImage (C : ConstructionData n m) (I : Finset (Fin n))
    (x : BaseVertex m) : Finset (Fin m) :=
  (C.X I x).image C.redProj

/-- The blue-coordinate projection `π_B(X_v(I))` appearing in the huge-case bounds. -/
def blueProjectionImage (C : ConstructionData n m) (I : Finset (Fin n))
    (x : BaseVertex m) : Finset (Fin m) :=
  (C.X I x).image C.blueProj

/-- The deterministic Section 3 event `𝒟`, restricted to the combinatorial bounds that the current
formalization uses directly. It packages fiber bounds, lifted-neighborhood codegrees, same-color
projection bounds, and the projected codegrees that feed the huge-case estimates. -/
structure GoodEventD (C : ConstructionData n m) (fiberBound degreeBound codegreeBound
    projCodegreeBound : ℕ) : Prop where
  redFiberBound : ∀ r : Fin m, (C.redFiber r).card ≤ fiberBound
  blueFiberBound : ∀ b : Fin m, (C.blueFiber b).card ≤ fiberBound
  redProjectionBound : ∀ r : Fin m,
    (C.redProjectionImage Finset.univ (Sum.inl r)).card ≤ degreeBound
  blueProjectionBound : ∀ b : Fin m,
    (C.blueProjectionImage Finset.univ (Sum.inr b)).card ≤ degreeBound
  xInterBound : ∀ x y : BaseVertex m, x ≠ y →
    (C.X Finset.univ x ∩ C.X Finset.univ y).card ≤ codegreeBound
  blueProjectionInterBound : ∀ r r' : Fin m, r ≠ r' →
    (C.blueProjectionImage Finset.univ (Sum.inl r) ∩
      C.blueProjectionImage Finset.univ (Sum.inl r')).card ≤ projCodegreeBound
  redProjectionInterBound : ∀ b b' : Fin m, b ≠ b' →
    (C.redProjectionImage Finset.univ (Sum.inr b) ∩
      C.redProjectionImage Finset.univ (Sum.inr b')).card ≤ projCodegreeBound

/-- Paper Section 3's huge part `H_I`. -/
def HPart (C : ConstructionData n m) (I : Finset (Fin n)) : Finset (BaseVertex m) := by
  classical
  exact Finset.univ.filter fun x =>
    Twobites.paperT1 n < (C.xCard I x : ℝ) ∧ (C.xCard I x : ℝ) ≤ (I.card : ℝ)

/-- Paper Section 3's large part `L_I`. -/
def LPart (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) : Finset (BaseVertex m) := by
  classical
  exact Finset.univ.filter fun x =>
    Twobites.paperT2 ε n < (C.xCard I x : ℝ) ∧ (C.xCard I x : ℝ) ≤ Twobites.paperT1 n

/-- Paper Section 3's medium part `M_I`. -/
def MPart (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) : Finset (BaseVertex m) := by
  classical
  exact Finset.univ.filter fun x =>
    Twobites.paperT3 ε n < (C.xCard I x : ℝ) ∧ (C.xCard I x : ℝ) ≤ Twobites.paperT2 ε n

/-- Paper Section 3's small part `S_I`. -/
def SPart (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) : Finset (BaseVertex m) := by
  classical
  exact Finset.univ.filter fun x =>
    (C.xCard I x : ℝ) ≤ Twobites.paperT3 ε n

/-- The total weight `∑_{v ∈ A} |X_v(I)|` of a selected part `A ⊆ V_R ∪ V_B`. -/
def partWeight (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) : ℕ :=
  ∑ x ∈ A, C.xCard I x

/-- The raw sum `∑_{v ∈ A} (|X_v(I)| choose 2)` that upper-bounds the contribution of closed pairs
from a part before inclusion-exclusion. -/
def partPairCount (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : ℕ :=
  ∑ x ∈ A, (C.xCard I x).choose 2

/-- The total red-projection weight `∑_{v ∈ A} |π_R(X_v(I))|`. -/
def redProjectionWeight (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : ℕ :=
  ∑ x ∈ A, (C.redProjectionImage I x).card

/-- The huge-case red self-contribution `∑_{v ∈ A} (|π_R(X_v(I))| choose 2)`. -/
def redProjectionPairCount (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : ℕ :=
  ∑ x ∈ A, ((C.redProjectionImage I x).card).choose 2

/-- The total blue-projection weight `∑_{v ∈ A} |π_B(X_v(I))|`. -/
def blueProjectionWeight (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : ℕ :=
  ∑ x ∈ A, (C.blueProjectionImage I x).card

/-- The huge-case blue self-contribution `∑_{v ∈ A} (|π_B(X_v(I))| choose 2)`. -/
def blueProjectionPairCount (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : ℕ :=
  ∑ x ∈ A, ((C.blueProjectionImage I x).card).choose 2

/-- The union `⋃_{v ∈ A} π_R(X_v(I))` that appears in the huge-case projection bounds. -/
def redProjectionUnion (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Fin m) :=
  A.biUnion fun x => C.redProjectionImage I x

/-- The union `⋃_{v ∈ A} π_B(X_v(I))` that appears in the huge-case projection bounds. -/
def blueProjectionUnion (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Fin m) :=
  A.biUnion fun x => C.blueProjectionImage I x

/-- The Section 4 base-vertex image `π_R(I) ∪ π_B(I)` inside `V_R ∪ V_B`. -/
def baseImage (C : ConstructionData n m) (I : Finset (Fin n)) : Finset (BaseVertex m) := by
  classical
  exact Finset.univ.filter fun x =>
    match x with
    | Sum.inl r => r ∈ C.redImage I
    | Sum.inr b => b ∈ C.blueImage I

/-- The fiber `F(v)` from Section 4, expressed uniformly on `V_R ∪ V_B`. -/
def baseFiber (C : ConstructionData n m) : BaseVertex m → Finset (Fin n)
  | Sum.inl r => C.redFiber r
  | Sum.inr b => C.blueFiber b

/-- The base-graph neighborhood `N(v)` from Section 4, expressed uniformly on `V_R ∪ V_B`. -/
def baseNeighborSet (C : ConstructionData n m) : BaseVertex m → Finset (BaseVertex m) := by
  classical
  intro x
  cases x with
  | inl r =>
      exact (Finset.univ.filter fun r' : Fin m => C.redBase.Adj r r').image Sum.inl
  | inr b =>
      exact (Finset.univ.filter fun b' : Fin m => C.blueBase.Adj b b').image Sum.inr

/-- Section 4's first revealed set `F_0 = (V_R ∪ V_B) \setminus (π_R(I) ∪ π_B(I))`. -/
def section4F0 (C : ConstructionData n m) (I : Finset (Fin n)) : Finset (BaseVertex m) := by
  classical
  exact Finset.univ \ C.baseImage I

/-- Section 4's second revealed set `F_1 = {v ∈ π_R(I) ∪ π_B(I) : |F(v) ∩ I| > log n}`. -/
def section4F1 (C : ConstructionData n m) (I : Finset (Fin n)) : Finset (BaseVertex m) := by
  classical
  exact (C.baseImage I).filter fun x =>
    Real.log (n : ℝ) < (((C.baseFiber x ∩ I).card : ℕ) : ℝ)

/-- Section 4's third revealed set `F_2 = {v ∈ π_R(I) ∪ π_B(I) : |N(v) ∩ F_1| > t_2 / log n}`. -/
def section4F2 (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) :
    Finset (BaseVertex m) := by
  classical
  exact (C.baseImage I).filter fun x =>
    Twobites.paperT2 ε n / Real.log (n : ℝ) <
      (((C.baseNeighborSet x ∩ C.section4F1 I).card : ℕ) : ℝ)

/-- The total Section 4 revealed base-vertex set `F = F_0 ∪ F_1 ∪ F_2`. -/
def section4F (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) :
    Finset (BaseVertex m) :=
  C.section4F0 I ∪ C.section4F1 I ∪ C.section4F2 I ε

/-- An ordered overcount of the same-color base-image pairs exposed when every vertex of `A` is
queried against `B`. This is the finite counting object used for the Section 4 reveal budget. -/
def revealedBaseArcSet (A B : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact
    (((A.filter IsRedBaseVertex).product (B.filter IsRedBaseVertex)).filter fun p => p.1 ≠ p.2) ∪
      (((A.filter IsBlueBaseVertex).product (B.filter IsBlueBaseVertex)).filter
        fun p => p.1 ≠ p.2)

/-- The Section 4 counting argument only needs an overcount, so we reuse the ordered arc set as the
pair-counting object. -/
def revealedBasePairSet (A B : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) := by
  exact revealedBaseArcSet A B

/-- Canonical red pairs inside `π_R(I)`, counted with the order `r < r'`. -/
def redBasePairSet (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (Fin m × Fin m) := by
  classical
  exact ((C.redImage I).product (C.redImage I)).filter fun p => p.1 < p.2

/-- Canonical blue pairs inside `π_B(I)`, counted with the order `b < b'`. -/
def blueBasePairSet (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (Fin m × Fin m) := by
  classical
  exact ((C.blueImage I).product (C.blueImage I)).filter fun p => p.1 < p.2

/-- The paper's same-color pair object inside `π_R(I) ∪ π_B(I)`, before distinguishing edges from
non-edges. -/
def basePairSet (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact
    ((C.redBasePairSet I).image fun p => (Sum.inl p.1, Sum.inl p.2)) ∪
      ((C.blueBasePairSet I).image fun p => (Sum.inr p.1, Sum.inr p.2))

/-- Section 4's ordered overcount of revealed pairs coming from the queried vertices `A`. -/
def section4RevealArcSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) :=
  revealedBaseArcSet A (C.baseImage I)

/-- Section 4's finite same-color reveal-counting object contributed by the queried vertices `A`.
It is an overcount rather than a deduplicated unordered-pair set, which is enough for the paper's
budget estimate. -/
def section4RevealPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) :=
  revealedBasePairSet A (C.baseImage I)

/-- Canonical red open pairs inside `π_R(I)`, counted with the order `r < r'`. -/
def redBaseOpenPairSet (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (Fin m × Fin m) := by
  classical
  exact ((C.redImage I).product (C.redImage I)).filter fun p =>
    p.1 < p.2 ∧ ¬ C.redBase.Adj p.1 p.2

/-- Canonical blue open pairs inside `π_B(I)`, counted with the order `b < b'`. -/
def blueBaseOpenPairSet (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (Fin m × Fin m) := by
  classical
  exact ((C.blueImage I).product (C.blueImage I)).filter fun p =>
    p.1 < p.2 ∧ ¬ C.blueBase.Adj p.1 p.2

/-- Canonical red closed pairs inside `π_R(I)`, counted with the order `r < r'`. -/
def redBaseClosedPairSet (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (Fin m × Fin m) := by
  classical
  exact (C.redBasePairSet I).filter fun p => C.redBase.Adj p.1 p.2

/-- Canonical blue closed pairs inside `π_B(I)`, counted with the order `b < b'`. -/
def blueBaseClosedPairSet (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (Fin m × Fin m) := by
  classical
  exact (C.blueBasePairSet I).filter fun p => C.blueBase.Adj p.1 p.2

/-- The paper's open pairs inside `π_R(I) ∪ π_B(I)`, represented as canonical same-color base
pairs. -/
def baseOpenPairSet (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact
    ((C.redBaseOpenPairSet I).image fun p => (Sum.inl p.1, Sum.inl p.2)) ∪
      ((C.blueBaseOpenPairSet I).image fun p => (Sum.inr p.1, Sum.inr p.2))

/-- Those base open pairs already revealed by querying vertices of `A`. -/
def revealedBaseOpenPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact (C.baseOpenPairSet I).filter fun p => p.1 ∈ A ∨ p.2 ∈ A

/-- Those base open pairs still unrevealed after querying vertices of `A`. -/
def unrevealedBaseOpenPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact (C.baseOpenPairSet I).filter fun p => p.1 ∉ A ∧ p.2 ∉ A

/-- The paper's unrevealed same-color pair object after querying the vertices of `A`. -/
def unrevealedBasePairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact (C.basePairSet I).filter fun p => p.1 ∉ A ∧ p.2 ∉ A

/-- Canonical unrevealed red pairs after querying `A`, matching the red part of the paper's
`E_I`. -/
def unrevealedRedBasePairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Fin m × Fin m) := by
  classical
  exact (C.redBasePairSet I).filter fun p => Sum.inl p.1 ∉ A ∧ Sum.inl p.2 ∉ A

/-- Canonical unrevealed blue pairs after querying `A`, matching the blue part of the paper's
`E_I`. -/
def unrevealedBlueBasePairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Fin m × Fin m) := by
  classical
  exact (C.blueBasePairSet I).filter fun p => Sum.inr p.1 ∉ A ∧ Sum.inr p.2 ∉ A

/-- The red same-color `ClosedPairPlus` contribution `⋃_i {N^+(r_i) choose 2}` on canonical red
pairs. -/
def redBaseClosedPlusPair (C : ConstructionData n m) (I : Finset (Fin n)) (p : Fin m × Fin m) :
    Prop :=
  ∃ r ∈ C.redImage I,
    C.redBase.Adj r p.1 ∧ C.redBase.Adj r p.2 ∧ r < p.1 ∧ r < p.2

/-- The blue same-color `ClosedPairPlus` contribution `⋃_i {N^+(b_i) choose 2}` on canonical blue
pairs. -/
def blueBaseClosedPlusPair (C : ConstructionData n m) (I : Finset (Fin n)) (p : Fin m × Fin m) :
    Prop :=
  ∃ b ∈ C.blueImage I,
    C.blueBase.Adj b p.1 ∧ C.blueBase.Adj b p.2 ∧ b < p.1 ∧ b < p.2

/-- The paper's `T_R`: unrevealed red pairs after removing the red same-color `ClosedPairPlus`
part. -/
def section4TRedPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Fin m × Fin m) := by
  classical
  exact (C.unrevealedRedBasePairSet I A).filter fun p => ¬ C.redBaseClosedPlusPair I p

/-- The paper's `T_B`: unrevealed blue pairs after removing the blue same-color `ClosedPairPlus`
part. -/
def section4TBluePairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Fin m × Fin m) := by
  classical
  exact (C.unrevealedBlueBasePairSet I A).filter fun p => ¬ C.blueBaseClosedPlusPair I p

/-- The combined same-color `ClosedPairPlus` predicate on canonical base pairs. -/
def sameColorClosedPlusBasePair (C : ConstructionData n m) (I : Finset (Fin n))
    (p : BaseVertex m × BaseVertex m) : Prop :=
  match p.1, p.2 with
  | Sum.inl r, Sum.inl r' => C.redBaseClosedPlusPair I (r, r')
  | Sum.inr b, Sum.inr b' => C.blueBaseClosedPlusPair I (b, b')
  | _, _ => False

/-- The combined `T_I = T_R ∪ T_B` object used in the proof of `lem:RISI`. -/
def section4TPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact (C.unrevealedBasePairSet I A).filter fun p => ¬ C.sameColorClosedPlusBasePair I p

/-- The unrevealed same-color pairs removed from `E_I` by the same-color `ClosedPairPlus`
contribution before defining `T_R ∪ T_B`. -/
def sameColorClosedPlusBasePairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact (C.unrevealedBasePairSet I A).filter fun p => C.sameColorClosedPlusBasePair I p

/-- Canonical red pairs removed by the red same-color `ClosedPairPlus` contribution. -/
def redBaseClosedPlusPairSet (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (Fin m × Fin m) := by
  classical
  exact (C.redBasePairSet I).filter fun p => C.redBaseClosedPlusPair I p

/-- Canonical blue pairs removed by the blue same-color `ClosedPairPlus` contribution. -/
def blueBaseClosedPlusPairSet (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (Fin m × Fin m) := by
  classical
  exact (C.blueBasePairSet I).filter fun p => C.blueBaseClosedPlusPair I p

/-- The paper's `U_R = T_R ∩ E(G_R)` on canonical red base pairs. -/
def section4URedPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Fin m × Fin m) := by
  classical
  exact (C.section4TRedPairSet I A).filter fun p => C.redBase.Adj p.1 p.2

/-- The paper's `U_B = T_B ∩ E(G_B)` on canonical blue base pairs. -/
def section4UBluePairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Fin m × Fin m) := by
  classical
  exact (C.section4TBluePairSet I A).filter fun p => C.blueBase.Adj p.1 p.2

/-- The combined `U_R ∪ U_B` object on base vertices. -/
def section4UPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact
    ((C.section4URedPairSet I A).image fun p => (Sum.inl p.1, Sum.inl p.2)) ∪
      ((C.section4UBluePairSet I A).image fun p => (Sum.inr p.1, Sum.inr p.2))

/-- The opposite-color red witness pool
`⋃_{b ∉ A} π_R({X_b(I) choose 2})`, represented as unordered red pairs. -/
def redOppositeWitnessBiUnion (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Sym2 (Fin m)) :=
  (Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).biUnion fun b =>
    (C.redProjectionImage I (Sum.inr b)).offDiag.image Sym2.mk

/-- The opposite-color blue witness pool
`⋃_{r ∉ A} π_B({X_r(I) choose 2})`, represented as unordered blue pairs. -/
def blueOppositeWitnessBiUnion (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Sym2 (Fin m)) :=
  (Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).biUnion fun r =>
    (C.blueProjectionImage I (Sum.inl r)).offDiag.image Sym2.mk

/-- The monochromatic red witness pool `⋃_{r ∈ V_R} π_R({X_r(I) choose 2})`, represented as
unordered red pairs. -/
def redMonochromaticWitnessBiUnion (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (Sym2 (Fin m)) :=
  (Finset.univ : Finset (Fin m)).biUnion fun r =>
    (C.redProjectionImage I (Sum.inl r)).offDiag.image Sym2.mk

/-- The monochromatic blue witness pool `⋃_{b ∈ V_B} π_B({X_b(I) choose 2})`, represented as
unordered blue pairs. -/
def blueMonochromaticWitnessBiUnion (C : ConstructionData n m) (I : Finset (Fin n)) :
    Finset (Sym2 (Fin m)) :=
  (Finset.univ : Finset (Fin m)).biUnion fun b =>
    (C.blueProjectionImage I (Sum.inr b)).offDiag.image Sym2.mk

/-- The paper's closed-pair predicate `C(I)`, expressed on ordered pairs of distinct vertices of
`I`. -/
def ClosedPair (C : ConstructionData n m) (I : Finset (Fin n)) (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ∃ x : BaseVertex m, v ∈ C.X I x ∧ w ∈ C.X I x

/-- The paper's `C^+(I)` predicate, built from the forward-neighborhood sets `X_v^+(I)`. -/
def ClosedPairPlus (C : ConstructionData n m) (I : Finset (Fin n)) (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ∃ x : BaseVertex m, v ∈ C.XPlus I x ∧ w ∈ C.XPlus I x

/-- The closed-pair predicate restricted to a chosen part of `V_R ∪ V_B`, matching the paper's
unions over `H_I`, `L_I`, `M_I`, and `S_I`. -/
def ClosedPairOn (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m))
    (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ∃ x ∈ A, v ∈ C.X I x ∧ w ∈ C.X I x

/-- The forward-neighborhood version of `ClosedPairOn`. -/
def ClosedPairPlusOn (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m))
    (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ∃ x ∈ A, v ∈ C.XPlus I x ∧ w ∈ C.XPlus I x

/-- The open-pair predicate after only revealing closed pairs witnessed inside `A ⊆ V_R ∪ V_B`. -/
def OpenPairOn (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m))
    (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ¬ C.ClosedPairOn I A v w

/-- The forward-neighborhood analogue of `OpenPairOn`. -/
def OpenPairPlusOn (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m))
    (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ¬ C.ClosedPairPlusOn I A v w

/-- The paper's open-pair predicate `O(I)`. -/
def OpenPair (C : ConstructionData n m) (I : Finset (Fin n)) (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ¬ C.ClosedPair I v w

/-- The paper's `O^+(I)` predicate. -/
def OpenPairPlus (C : ConstructionData n m) (I : Finset (Fin n)) (v w : Fin n) : Prop :=
  v ∈ I ∧ w ∈ I ∧ v ≠ w ∧ ¬ C.ClosedPairPlus I v w

/-- The exact conditioned `U_R` object used in the Section 4 probability estimate: canonical red
base edges whose lifted realizations remain open with respect to `A` and are not
`ClosedPairPlus`. -/
def section4URedCondPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Fin m × Fin m) := by
  classical
  exact (C.section4URedPairSet I A).filter fun p =>
    ∃ v ∈ I, ∃ w ∈ I,
      C.redProj v = p.1 ∧ C.redProj w = p.2 ∧
        v ≠ w ∧ C.OpenPairOn I A v w ∧ C.OpenPairPlus I v w

/-- The exact conditioned `U_B` object used in the Section 4 probability estimate: canonical blue
base edges whose lifted realizations remain open with respect to `A` and are not
`ClosedPairPlus`. -/
def section4UBlueCondPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (Fin m × Fin m) := by
  classical
  exact (C.section4UBluePairSet I A).filter fun p =>
    ∃ v ∈ I, ∃ w ∈ I,
      C.blueProj v = p.1 ∧ C.blueProj w = p.2 ∧
        v ≠ w ∧ C.OpenPairOn I A v w ∧ C.OpenPairPlus I v w

/-- The combined conditioned `U_R ∪ U_B` object used in the exact Section 4 event count. -/
def section4UCondPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact
    ((C.section4URedCondPairSet I A).image fun p => (Sum.inl p.1, Sum.inl p.2)) ∪
      ((C.section4UBlueCondPairSet I A).image fun p => (Sum.inr p.1, Sum.inr p.2))

/-- The residual part of `T_I` after removing the exact conditioned `U_R ∪ U_B` pairs. Under the
independence event, these are the pairs that must be non-edges in the second-stage exposure. -/
def section4TRemainingPairSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : Finset (BaseVertex m × BaseVertex m) := by
  classical
  exact (C.section4TPairSet I A).filter fun p => p ∉ C.section4UCondPairSet I A

/-- Candidate red opposite-color witness choices of size `uR` for the conditioned `U_R`
event-counting layer. -/
def section4URedChoiceSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (uR : ℕ) : Finset (Finset (Sym2 (Fin m))) :=
  (C.redOppositeWitnessBiUnion I A).powersetCard uR

/-- Candidate blue opposite-color witness choices of size `uB` for the conditioned `U_B`
event-counting layer. -/
def section4UBlueChoiceSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (uB : ℕ) : Finset (Finset (Sym2 (Fin m))) :=
  (C.blueOppositeWitnessBiUnion I A).powersetCard uB

/-- The finite family of conditioned `(U_R,U_B)` witness choices of prescribed sizes. -/
def section4UChoiceSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (uR uB : ℕ) :
    Finset (Finset (Sym2 (Fin m)) × Finset (Sym2 (Fin m))) :=
  C.section4URedChoiceSet I A uR ×ˢ C.section4UBlueChoiceSet I A uB

/-- The literal red second-stage sample space of size-`u_R` edge sets inside `T_R`. -/
def section4TRedChoiceSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (uR : ℕ) : Finset (Finset (Sym2 (Fin m))) :=
  ((C.section4TRedPairSet I A).image Sym2.mk).powersetCard uR

/-- The literal blue second-stage sample space of size-`u_B` edge sets inside `T_B`. -/
def section4TBlueChoiceSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (uB : ℕ) : Finset (Finset (Sym2 (Fin m))) :=
  ((C.section4TBluePairSet I A).image Sym2.mk).powersetCard uB

/-- The literal second-stage sample space of size-`(u_R,u_B)` edge outcomes inside `T_R × T_B`. -/
def section4TChoiceSet (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (uR uB : ℕ) :
    Finset (Finset (Sym2 (Fin m)) × Finset (Sym2 (Fin m))) :=
  C.section4TRedChoiceSet I A uR ×ˢ C.section4TBlueChoiceSet I A uB

/-- The Bernoulli mass of a second-stage exposure pattern with `uR + uB` chosen edges and
`remaining` forced non-edges. -/
def section4BernoulliMass (p : ℝ) (uR uB remaining : ℕ) : ℝ :=
  p ^ (uR + uB) * (1 - p) ^ remaining

/-- The finite Bernoulli mass of an explicit second-stage event family. -/
def section4SecondStageEventMass
    (E : Finset (Finset (Sym2 (Fin m)) × Finset (Sym2 (Fin m))))
    (p : ℝ) (remaining : ℕ) : ℝ := by
  exact Finset.sum E fun outcome =>
    section4BernoulliMass p outcome.1.card outcome.2.card remaining

/-- The counted-event upper bound obtained by choosing a red/blue witness pattern and then forcing
all residual `T \ U` pairs to be non-edges. -/
def section4ChoiceMass (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (p : ℝ) (uR uB remaining : ℕ) : ℝ :=
  ((C.section4UChoiceSet I A uR uB).card : ℝ) * section4BernoulliMass p uR uB remaining

/-- The finite counted-event mass of the exact size-`(u_R,u_B)` witness family. -/
def section4ChoiceEventMass (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (p : ℝ) (uR uB remaining : ℕ) : ℝ := by
  exact
    section4SecondStageEventMass (C.section4UChoiceSet I A uR uB) p remaining

/-- The finite index set for the possible `(u_R,u_B)` counts used in the summed `lem:RISI`
estimate. -/
def section4CountIndexSet (uRMax uBMax : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (uRMax + 1) ×ˢ Finset.range (uBMax + 1)

/-- The summed counted-event mass over all admissible `(u_R,u_B)` values. -/
def section4ChoiceEventMassSum (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (p : ℝ) (remaining uRMax uBMax : ℕ) : ℝ := by
  exact
    Finset.sum (section4CountIndexSet uRMax uBMax) fun uv =>
      C.section4ChoiceEventMass I A p uv.1 uv.2 remaining

/-- The corresponding summed upper-bound expression after replacing the actual witness-family
cardinalities by projection-pair counts. -/
def section4ProjectionChoiceMassSum (p : ℝ) (remaining uRMax uBMax : ℕ) : ℝ := by
  exact
    Finset.sum (section4CountIndexSet uRMax uBMax) fun uv =>
      ((((uRMax.choose uv.1 : ℕ) : ℝ) * p ^ uv.1) *
          (((uBMax.choose uv.2 : ℕ) : ℝ) * p ^ uv.2)) *
        (1 - p) ^ remaining

/-- The exact conditioned second-stage witness outcome produced by the current independent-set
configuration. -/
def section4UCondChoiceOutcome (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) :
    Finset (Sym2 (Fin m)) × Finset (Sym2 (Fin m)) :=
  ((C.section4URedCondPairSet I A).image Sym2.mk,
    (C.section4UBlueCondPairSet I A).image Sym2.mk)

/-- The singleton counted-event object corresponding to the actual conditioned second-stage outcome
having prescribed red/blue witness counts. -/
def section4UCondChoiceEvent (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (uR uB : ℕ) :
    Finset (Finset (Sym2 (Fin m)) × Finset (Sym2 (Fin m))) :=
  if (C.section4URedCondPairSet I A).card = uR ∧
      (C.section4UBlueCondPairSet I A).card = uB then
    {C.section4UCondChoiceOutcome I A}
  else
    ∅

/-- The counted mass of the exact conditioned second-stage event with prescribed `(u_R,u_B)`
counts. -/
def section4UCondChoiceEventMass (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (p : ℝ) (uR uB remaining : ℕ) : ℝ := by
  exact
    section4SecondStageEventMass (C.section4UCondChoiceEvent I A uR uB) p remaining

/-- The summed mass of the actual conditioned event over all admissible `(u_R,u_B)` values. -/
def section4UCondChoiceEventMassSum (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) (p : ℝ) (remaining uRMax uBMax : ℕ) : ℝ := by
  exact
    Finset.sum (section4CountIndexSet uRMax uBMax) fun uv =>
      C.section4UCondChoiceEventMass I A p uv.1 uv.2 remaining

/-- The aggregate Section 4 loss term subtracted from a base open-pair lower bound before the
second-stage Bernoulli exposure: reveal budget, same-color `ClosedPairPlus`, and opposite-color
witness-cap contributions. -/
def section4SecondStageLossNat (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) : ℕ :=
  I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
    (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
      C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) +
    C.redProjectionPairCount I
      ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) +
    C.blueProjectionPairCount I
      ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)

/-- The literal finite mass of the actual conditioned second-stage Section 4 event, obtained by
plugging the true `(u_R,u_B)` counts and the aggregate loss term into the explicit Bernoulli event
family. This is the repo-level stand-in for the conditioned probability in `lem:RISI`. -/
def section4ActualConditionedEventMass (C : ConstructionData n m) (I : Finset (Fin n))
    (ε p : ℝ) (N : ℕ) : ℝ :=
  let uRActual := (C.section4URedCondPairSet I (C.section4F I ε)).card
  let uBActual := (C.section4UBlueCondPairSet I (C.section4F I ε)).card
  C.section4UCondChoiceEventMass I (C.section4F I ε) p uRActual uBActual
    (N - C.section4SecondStageLossNat I ε)

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

@[simp] theorem mem_HPart (C : ConstructionData n m) {I : Finset (Fin n)} {x : BaseVertex m} :
    x ∈ C.HPart I ↔
      Twobites.paperT1 n < (C.xCard I x : ℝ) ∧ (C.xCard I x : ℝ) ≤ (I.card : ℝ) := by
  classical
  simp [HPart]

@[simp] theorem mem_LPart (C : ConstructionData n m) {I : Finset (Fin n)} {ε : ℝ}
    {x : BaseVertex m} :
    x ∈ C.LPart I ε ↔
      Twobites.paperT2 ε n < (C.xCard I x : ℝ) ∧
        (C.xCard I x : ℝ) ≤ Twobites.paperT1 n := by
  classical
  simp [LPart]

@[simp] theorem mem_MPart (C : ConstructionData n m) {I : Finset (Fin n)} {ε : ℝ}
    {x : BaseVertex m} :
    x ∈ C.MPart I ε ↔
      Twobites.paperT3 ε n < (C.xCard I x : ℝ) ∧
        (C.xCard I x : ℝ) ≤ Twobites.paperT2 ε n := by
  classical
  simp [MPart]

@[simp] theorem mem_SPart (C : ConstructionData n m) {I : Finset (Fin n)} {ε : ℝ}
    {x : BaseVertex m} :
    x ∈ C.SPart I ε ↔ (C.xCard I x : ℝ) ≤ Twobites.paperT3 ε n := by
  classical
  simp [SPart]

@[simp] theorem mem_baseImage_inl (C : ConstructionData n m) {I : Finset (Fin n)} {r : Fin m} :
    Sum.inl r ∈ C.baseImage I ↔ r ∈ C.redImage I := by
  classical
  simp [baseImage]

@[simp] theorem mem_baseImage_inr (C : ConstructionData n m) {I : Finset (Fin n)} {b : Fin m} :
    Sum.inr b ∈ C.baseImage I ↔ b ∈ C.blueImage I := by
  classical
  simp [baseImage]

@[simp] theorem mem_baseFiber_inl (C : ConstructionData n m) {r : Fin m} {v : Fin n} :
    v ∈ C.baseFiber (Sum.inl r) ↔ C.redProj v = r := by
  simp [baseFiber]

@[simp] theorem mem_baseFiber_inr (C : ConstructionData n m) {b : Fin m} {v : Fin n} :
    v ∈ C.baseFiber (Sum.inr b) ↔ C.blueProj v = b := by
  simp [baseFiber]

@[simp] theorem mem_baseNeighborSet_inl_inl (C : ConstructionData n m) {r r' : Fin m} :
    Sum.inl r' ∈ C.baseNeighborSet (Sum.inl r) ↔ C.redBase.Adj r r' := by
  classical
  simp [baseNeighborSet]

@[simp] theorem not_mem_baseNeighborSet_inl_inr (C : ConstructionData n m) {r b : Fin m} :
    Sum.inr b ∉ C.baseNeighborSet (Sum.inl r) := by
  classical
  simp [baseNeighborSet]

@[simp] theorem mem_baseNeighborSet_inr_inr (C : ConstructionData n m) {b b' : Fin m} :
    Sum.inr b' ∈ C.baseNeighborSet (Sum.inr b) ↔ C.blueBase.Adj b b' := by
  classical
  simp [baseNeighborSet]

@[simp] theorem not_mem_baseNeighborSet_inr_inl (C : ConstructionData n m) {b r : Fin m} :
    Sum.inl r ∉ C.baseNeighborSet (Sum.inr b) := by
  classical
  simp [baseNeighborSet]

@[simp] theorem mem_section4F0 (C : ConstructionData n m) {I : Finset (Fin n)}
    {x : BaseVertex m} :
    x ∈ C.section4F0 I ↔ x ∈ (Finset.univ : Finset (BaseVertex m)) ∧ x ∉ C.baseImage I := by
  classical
  simp [section4F0]

@[simp] theorem mem_section4F1 (C : ConstructionData n m) {I : Finset (Fin n)}
    {x : BaseVertex m} :
    x ∈ C.section4F1 I ↔
      x ∈ C.baseImage I ∧
        Real.log (n : ℝ) < (((C.baseFiber x ∩ I).card : ℕ) : ℝ) := by
  classical
  simp [section4F1]

@[simp] theorem mem_section4F2 (C : ConstructionData n m) {I : Finset (Fin n)} {ε : ℝ}
    {x : BaseVertex m} :
    x ∈ C.section4F2 I ε ↔
      x ∈ C.baseImage I ∧
        Twobites.paperT2 ε n / Real.log (n : ℝ) <
          (((C.baseNeighborSet x ∩ C.section4F1 I).card : ℕ) : ℝ) := by
  classical
  simp [section4F2]

@[simp] theorem mem_section4F (C : ConstructionData n m) {I : Finset (Fin n)} {ε : ℝ}
    {x : BaseVertex m} :
    x ∈ C.section4F I ε ↔ x ∈ C.section4F0 I ∨ x ∈ C.section4F1 I ∨ x ∈ C.section4F2 I ε := by
  classical
  simp [section4F, or_left_comm]

@[simp] theorem mem_redBaseOpenPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {r r' : Fin m} :
    (r, r') ∈ C.redBaseOpenPairSet I ↔
      r ∈ C.redImage I ∧ r' ∈ C.redImage I ∧ r < r' ∧ ¬ C.redBase.Adj r r' := by
  classical
  simp [redBaseOpenPairSet, and_left_comm, and_assoc]

@[simp] theorem mem_redBasePairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {r r' : Fin m} :
    (r, r') ∈ C.redBasePairSet I ↔
      r ∈ C.redImage I ∧ r' ∈ C.redImage I ∧ r < r' := by
  classical
  simp [redBasePairSet, and_assoc]

@[simp] theorem mem_blueBaseOpenPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {b b' : Fin m} :
    (b, b') ∈ C.blueBaseOpenPairSet I ↔
      b ∈ C.blueImage I ∧ b' ∈ C.blueImage I ∧ b < b' ∧ ¬ C.blueBase.Adj b b' := by
  classical
  simp [blueBaseOpenPairSet, and_left_comm, and_assoc]

@[simp] theorem mem_blueBasePairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {b b' : Fin m} :
    (b, b') ∈ C.blueBasePairSet I ↔
      b ∈ C.blueImage I ∧ b' ∈ C.blueImage I ∧ b < b' := by
  classical
  simp [blueBasePairSet, and_assoc]

@[simp] theorem mem_redBaseClosedPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {r r' : Fin m} :
    (r, r') ∈ C.redBaseClosedPairSet I ↔
      r ∈ C.redImage I ∧ r' ∈ C.redImage I ∧ r < r' ∧ C.redBase.Adj r r' := by
  classical
  simp [redBaseClosedPairSet, and_assoc]

@[simp] theorem mem_blueBaseClosedPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {b b' : Fin m} :
    (b, b') ∈ C.blueBaseClosedPairSet I ↔
      b ∈ C.blueImage I ∧ b' ∈ C.blueImage I ∧ b < b' ∧ C.blueBase.Adj b b' := by
  classical
  simp [blueBaseClosedPairSet, and_assoc]

@[simp] theorem mem_revealedBaseOpenPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : BaseVertex m × BaseVertex m} :
    p ∈ C.revealedBaseOpenPairSet I A ↔ p ∈ C.baseOpenPairSet I ∧ (p.1 ∈ A ∨ p.2 ∈ A) := by
  classical
  simp [revealedBaseOpenPairSet]

@[simp] theorem mem_unrevealedBaseOpenPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : BaseVertex m × BaseVertex m} :
    p ∈ C.unrevealedBaseOpenPairSet I A ↔ p ∈ C.baseOpenPairSet I ∧ p.1 ∉ A ∧ p.2 ∉ A := by
  classical
  simp [unrevealedBaseOpenPairSet]

@[simp] theorem mem_unrevealedBasePairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : BaseVertex m × BaseVertex m} :
    p ∈ C.unrevealedBasePairSet I A ↔ p ∈ C.basePairSet I ∧ p.1 ∉ A ∧ p.2 ∉ A := by
  classical
  simp [unrevealedBasePairSet]

@[simp] theorem mem_unrevealedRedBasePairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : Fin m × Fin m} :
    p ∈ C.unrevealedRedBasePairSet I A ↔
      p ∈ C.redBasePairSet I ∧ Sum.inl p.1 ∉ A ∧ Sum.inl p.2 ∉ A := by
  classical
  simp [unrevealedRedBasePairSet]

@[simp] theorem mem_unrevealedBlueBasePairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : Fin m × Fin m} :
    p ∈ C.unrevealedBlueBasePairSet I A ↔
      p ∈ C.blueBasePairSet I ∧ Sum.inr p.1 ∉ A ∧ Sum.inr p.2 ∉ A := by
  classical
  simp [unrevealedBlueBasePairSet]

@[simp] theorem mem_section4TRedPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : Fin m × Fin m} :
    p ∈ C.section4TRedPairSet I A ↔
      p ∈ C.unrevealedRedBasePairSet I A ∧ ¬ C.redBaseClosedPlusPair I p := by
  classical
  simp [section4TRedPairSet]

@[simp] theorem mem_section4TBluePairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : Fin m × Fin m} :
    p ∈ C.section4TBluePairSet I A ↔
      p ∈ C.unrevealedBlueBasePairSet I A ∧ ¬ C.blueBaseClosedPlusPair I p := by
  classical
  simp [section4TBluePairSet]

@[simp] theorem mem_section4TPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : BaseVertex m × BaseVertex m} :
    p ∈ C.section4TPairSet I A ↔
      p ∈ C.unrevealedBasePairSet I A ∧ ¬ C.sameColorClosedPlusBasePair I p := by
  classical
  simp [section4TPairSet]

@[simp] theorem mem_sameColorClosedPlusBasePairSet (C : ConstructionData n m)
    {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {p : BaseVertex m × BaseVertex m} :
    p ∈ C.sameColorClosedPlusBasePairSet I A ↔
      p ∈ C.unrevealedBasePairSet I A ∧ C.sameColorClosedPlusBasePair I p := by
  classical
  simp [sameColorClosedPlusBasePairSet]

@[simp] theorem mem_redBaseClosedPlusPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {p : Fin m × Fin m} :
    p ∈ C.redBaseClosedPlusPairSet I ↔
      p ∈ C.redBasePairSet I ∧ C.redBaseClosedPlusPair I p := by
  classical
  simp [redBaseClosedPlusPairSet]

@[simp] theorem mem_blueBaseClosedPlusPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {p : Fin m × Fin m} :
    p ∈ C.blueBaseClosedPlusPairSet I ↔
      p ∈ C.blueBasePairSet I ∧ C.blueBaseClosedPlusPair I p := by
  classical
  simp [blueBaseClosedPlusPairSet]

@[simp] theorem mem_section4URedPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : Fin m × Fin m} :
    p ∈ C.section4URedPairSet I A ↔
      p ∈ C.section4TRedPairSet I A ∧ C.redBase.Adj p.1 p.2 := by
  classical
  simp [section4URedPairSet]

@[simp] theorem mem_section4UBluePairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : Fin m × Fin m} :
    p ∈ C.section4UBluePairSet I A ↔
      p ∈ C.section4TBluePairSet I A ∧ C.blueBase.Adj p.1 p.2 := by
  classical
  simp [section4UBluePairSet]

@[simp] theorem mem_section4URedCondPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : Fin m × Fin m} :
    p ∈ C.section4URedCondPairSet I A ↔
      p ∈ C.section4URedPairSet I A ∧
        ∃ v ∈ I, ∃ w ∈ I,
          C.redProj v = p.1 ∧ C.redProj w = p.2 ∧
            v ≠ w ∧ C.OpenPairOn I A v w ∧ C.OpenPairPlus I v w := by
  classical
  simp [section4URedCondPairSet, and_left_comm, and_assoc]

@[simp] theorem mem_section4UBlueCondPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : Fin m × Fin m} :
    p ∈ C.section4UBlueCondPairSet I A ↔
      p ∈ C.section4UBluePairSet I A ∧
        ∃ v ∈ I, ∃ w ∈ I,
          C.blueProj v = p.1 ∧ C.blueProj w = p.2 ∧
            v ≠ w ∧ C.OpenPairOn I A v w ∧ C.OpenPairPlus I v w := by
  classical
  simp [section4UBlueCondPairSet, and_left_comm, and_assoc]

@[simp] theorem mem_section4UCondPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : BaseVertex m × BaseVertex m} :
    p ∈ C.section4UCondPairSet I A ↔
      p ∈
          ((C.section4URedCondPairSet I A).image fun q => (Sum.inl q.1, Sum.inl q.2)) ∪
            ((C.section4UBlueCondPairSet I A).image fun q => (Sum.inr q.1, Sum.inr q.2)) := by
  classical
  simp [section4UCondPairSet]

@[simp] theorem mem_section4TRemainingPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {p : BaseVertex m × BaseVertex m} :
    p ∈ C.section4TRemainingPairSet I A ↔
      p ∈ C.section4TPairSet I A ∧ p ∉ C.section4UCondPairSet I A := by
  classical
  simp [section4TRemainingPairSet]

@[simp] theorem mem_baseOpenPairSet_inl_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {r r' : Fin m} :
    (Sum.inl r, Sum.inl r') ∈ C.baseOpenPairSet I ↔ (r, r') ∈ C.redBaseOpenPairSet I := by
  classical
  simp [baseOpenPairSet]

@[simp] theorem mem_basePairSet_inl_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {r r' : Fin m} :
    (Sum.inl r, Sum.inl r') ∈ C.basePairSet I ↔ (r, r') ∈ C.redBasePairSet I := by
  classical
  simp [basePairSet]

@[simp] theorem mem_section4TPairSet_inl_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {r r' : Fin m} :
    (Sum.inl r, Sum.inl r') ∈ C.section4TPairSet I A ↔
      (r, r') ∈ C.section4TRedPairSet I A := by
  classical
  simp [section4TPairSet, section4TRedPairSet, sameColorClosedPlusBasePair]

@[simp] theorem mem_section4UPairSet_inl_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {r r' : Fin m} :
    (Sum.inl r, Sum.inl r') ∈ C.section4UPairSet I A ↔
      (r, r') ∈ C.section4URedPairSet I A := by
  classical
  simp [section4UPairSet]

@[simp] theorem mem_section4UCondPairSet_inl_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {r r' : Fin m} :
    (Sum.inl r, Sum.inl r') ∈ C.section4UCondPairSet I A ↔
      (r, r') ∈ C.section4URedCondPairSet I A := by
  classical
  simp [section4UCondPairSet]

@[simp] theorem mem_section4TRemainingPairSet_inl_inl (C : ConstructionData n m)
    {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {r r' : Fin m} :
    (Sum.inl r, Sum.inl r') ∈ C.section4TRemainingPairSet I A ↔
      (r, r') ∈ C.section4TRedPairSet I A ∧
        (r, r') ∉ C.section4URedCondPairSet I A := by
  classical
  constructor
  · intro h
    rcases C.mem_section4TRemainingPairSet.1 h with ⟨hT, hNotU⟩
    refine ⟨C.mem_section4TPairSet_inl_inl.1 hT, ?_⟩
    intro hU
    exact hNotU (C.mem_section4UCondPairSet_inl_inl.2 hU)
  · rintro ⟨hT, hNotU⟩
    refine C.mem_section4TRemainingPairSet.2 ?_
    refine ⟨C.mem_section4TPairSet_inl_inl.2 hT, ?_⟩
    intro hU
    exact hNotU (C.mem_section4UCondPairSet_inl_inl.1 hU)

@[simp] theorem mem_revealedBaseArcSet_inl_inl {A B : Finset (BaseVertex m)} {r r' : Fin m} :
    (Sum.inl r, Sum.inl r') ∈ revealedBaseArcSet A B ↔
      Sum.inl r ∈ A ∧ Sum.inl r' ∈ B ∧ r ≠ r' := by
  classical
  simp [revealedBaseArcSet, and_assoc]

@[simp] theorem mem_revealedBaseArcSet_inr_inr {A B : Finset (BaseVertex m)} {b b' : Fin m} :
    (Sum.inr b, Sum.inr b') ∈ revealedBaseArcSet A B ↔
      Sum.inr b ∈ A ∧ Sum.inr b' ∈ B ∧ b ≠ b' := by
  classical
  simp [revealedBaseArcSet, and_assoc]

@[simp] theorem not_mem_revealedBaseArcSet_inl_inr {A B : Finset (BaseVertex m)}
    {r : Fin m} {b : Fin m} :
    (Sum.inl r, Sum.inr b) ∉ revealedBaseArcSet A B := by
  classical
  simp [revealedBaseArcSet]

@[simp] theorem not_mem_revealedBaseArcSet_inr_inl {A B : Finset (BaseVertex m)}
    {b : Fin m} {r : Fin m} :
    (Sum.inr b, Sum.inl r) ∉ revealedBaseArcSet A B := by
  classical
  simp [revealedBaseArcSet]

@[simp] theorem mem_baseOpenPairSet_inr_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {b b' : Fin m} :
    (Sum.inr b, Sum.inr b') ∈ C.baseOpenPairSet I ↔ (b, b') ∈ C.blueBaseOpenPairSet I := by
  classical
  simp [baseOpenPairSet]

@[simp] theorem mem_basePairSet_inr_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {b b' : Fin m} :
    (Sum.inr b, Sum.inr b') ∈ C.basePairSet I ↔ (b, b') ∈ C.blueBasePairSet I := by
  classical
  simp [basePairSet]

@[simp] theorem mem_section4TPairSet_inr_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {b b' : Fin m} :
    (Sum.inr b, Sum.inr b') ∈ C.section4TPairSet I A ↔
      (b, b') ∈ C.section4TBluePairSet I A := by
  classical
  simp [section4TPairSet, section4TBluePairSet, sameColorClosedPlusBasePair]

@[simp] theorem mem_section4UPairSet_inr_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {b b' : Fin m} :
    (Sum.inr b, Sum.inr b') ∈ C.section4UPairSet I A ↔
      (b, b') ∈ C.section4UBluePairSet I A := by
  classical
  simp [section4UPairSet]

@[simp] theorem mem_section4UCondPairSet_inr_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {b b' : Fin m} :
    (Sum.inr b, Sum.inr b') ∈ C.section4UCondPairSet I A ↔
      (b, b') ∈ C.section4UBlueCondPairSet I A := by
  classical
  simp [section4UCondPairSet]

@[simp] theorem mem_section4TRemainingPairSet_inr_inr (C : ConstructionData n m)
    {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {b b' : Fin m} :
    (Sum.inr b, Sum.inr b') ∈ C.section4TRemainingPairSet I A ↔
      (b, b') ∈ C.section4TBluePairSet I A ∧
        (b, b') ∉ C.section4UBlueCondPairSet I A := by
  classical
  constructor
  · intro h
    rcases C.mem_section4TRemainingPairSet.1 h with ⟨hT, hNotU⟩
    refine ⟨C.mem_section4TPairSet_inr_inr.1 hT, ?_⟩
    intro hU
    exact hNotU (C.mem_section4UCondPairSet_inr_inr.2 hU)
  · rintro ⟨hT, hNotU⟩
    refine C.mem_section4TRemainingPairSet.2 ?_
    refine ⟨C.mem_section4TPairSet_inr_inr.2 hT, ?_⟩
    intro hU
    exact hNotU (C.mem_section4UCondPairSet_inr_inr.1 hU)

@[simp] theorem not_mem_baseOpenPairSet_inl_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {r : Fin m} {b : Fin m} :
    (Sum.inl r, Sum.inr b) ∉ C.baseOpenPairSet I := by
  classical
  simp [baseOpenPairSet]

@[simp] theorem not_mem_basePairSet_inl_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {r : Fin m} {b : Fin m} :
    (Sum.inl r, Sum.inr b) ∉ C.basePairSet I := by
  classical
  simp [basePairSet]

@[simp] theorem not_mem_section4TPairSet_inl_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {r : Fin m} {b : Fin m} :
    (Sum.inl r, Sum.inr b) ∉ C.section4TPairSet I A := by
  classical
  simp [section4TPairSet, sameColorClosedPlusBasePair]

@[simp] theorem not_mem_section4UPairSet_inl_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {r : Fin m} {b : Fin m} :
    (Sum.inl r, Sum.inr b) ∉ C.section4UPairSet I A := by
  classical
  simp [section4UPairSet]

@[simp] theorem not_mem_section4UCondPairSet_inl_inr (C : ConstructionData n m)
    {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {r : Fin m} {b : Fin m} :
    (Sum.inl r, Sum.inr b) ∉ C.section4UCondPairSet I A := by
  classical
  simp [section4UCondPairSet]

@[simp] theorem not_mem_section4TRemainingPairSet_inl_inr (C : ConstructionData n m)
    {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {r : Fin m} {b : Fin m} :
    (Sum.inl r, Sum.inr b) ∉ C.section4TRemainingPairSet I A := by
  classical
  simp [section4TRemainingPairSet]

@[simp] theorem not_mem_baseOpenPairSet_inr_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {b : Fin m} {r : Fin m} :
    (Sum.inr b, Sum.inl r) ∉ C.baseOpenPairSet I := by
  classical
  simp [baseOpenPairSet]

@[simp] theorem not_mem_basePairSet_inr_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {b : Fin m} {r : Fin m} :
    (Sum.inr b, Sum.inl r) ∉ C.basePairSet I := by
  classical
  simp [basePairSet]

@[simp] theorem not_mem_section4TPairSet_inr_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {b : Fin m} {r : Fin m} :
    (Sum.inr b, Sum.inl r) ∉ C.section4TPairSet I A := by
  classical
  simp [section4TPairSet, sameColorClosedPlusBasePair]

@[simp] theorem not_mem_section4UPairSet_inr_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {b : Fin m} {r : Fin m} :
    (Sum.inr b, Sum.inl r) ∉ C.section4UPairSet I A := by
  classical
  simp [section4UPairSet]

@[simp] theorem not_mem_section4UCondPairSet_inr_inl (C : ConstructionData n m)
    {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {b : Fin m} {r : Fin m} :
    (Sum.inr b, Sum.inl r) ∉ C.section4UCondPairSet I A := by
  classical
  simp [section4UCondPairSet]

@[simp] theorem not_mem_section4TRemainingPairSet_inr_inl (C : ConstructionData n m)
    {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {b : Fin m} {r : Fin m} :
    (Sum.inr b, Sum.inl r) ∉ C.section4TRemainingPairSet I A := by
  classical
  simp [section4TRemainingPairSet]

theorem sym2_mk_injective_of_lt {α : Type*} [LinearOrder α] {a b c d : α}
    (hab : a < b) (hcd : c < d) (h : Sym2.mk (a, b) = Sym2.mk (c, d)) :
    a = c ∧ b = d := by
  rcases Sym2.eq_iff.1 h with hEq | hEq
  · exact hEq
  · rcases hEq with ⟨ha, hb⟩
    subst ha
    subst hb
    exact (lt_asymm hab hcd).elim

theorem lt_of_pairLex_orderedPair_right {α : Type*} [LinearOrder α] {a b c : α}
    (hbc : b < c) (h : pairLex (orderedPair a c) (orderedPair b c)) : a < b := by
  by_cases hac : a ≤ c
  · simpa [pairLex, orderedPair, hac, min_eq_left hac, max_eq_right hac,
      min_eq_left (le_of_lt hbc), max_eq_right (le_of_lt hbc)] using h
  · have hca : c < a := lt_of_not_ge hac
    have h' : c < b ∨ c = b ∧ a < c := by
      simpa [pairLex, orderedPair, min_eq_right (le_of_lt hca), max_eq_left (le_of_lt hca),
        min_eq_left (le_of_lt hbc), max_eq_right (le_of_lt hbc)] using h
    rcases h' with hlt | ⟨-, hlt⟩
    · exact False.elim ((not_lt_of_ge (le_of_lt hbc)) hlt)
    · exact False.elim ((not_lt_of_ge (le_of_lt hca)) hlt)

theorem lt_of_pairLex_orderedPair_left {α : Type*} [LinearOrder α] {a b c : α}
    (hcb : c < b) (h : pairLex (orderedPair a b) (orderedPair b c)) : a < c := by
  by_cases hab : a ≤ b
  · simpa [pairLex, orderedPair, hab, min_eq_left hab, max_eq_right hab,
      min_eq_right (le_of_lt hcb), max_eq_left (le_of_lt hcb)] using h
  · have hba : b < a := lt_of_not_ge hab
    have h' : b < c ∨ b = c ∧ a < b := by
      simpa [pairLex, orderedPair, min_eq_right (le_of_lt hba), max_eq_left (le_of_lt hba),
        min_eq_right (le_of_lt hcb), max_eq_left (le_of_lt hcb)] using h
    rcases h' with hlt | ⟨-, hlt⟩
    · exact False.elim ((not_lt_of_ge (le_of_lt hcb)) hlt)
    · exact False.elim ((not_lt_of_ge (le_of_lt hba)) hlt)

theorem card_image_sym2_mk_of_strictPairSet {α : Type*} [DecidableEq α] [LinearOrder α]
    (s : Finset (α × α)) (hstrict : ∀ p ∈ s, p.1 < p.2) :
    (s.image Sym2.mk).card = s.card := by
  simpa using
    (Finset.card_image_of_injOn (s := s) (f := Sym2.mk)
      (by
        intro p hp q hq hpq
        rcases p with ⟨a, b⟩
        rcases q with ⟨c, d⟩
        rcases sym2_mk_injective_of_lt (hstrict _ hp) (hstrict _ hq) hpq with ⟨hac, hbd⟩
        exact Prod.ext hac hbd))

theorem redBasePairSet_image_sym2_eq_redImage_offDiag_image (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    (C.redBasePairSet I).image Sym2.mk = (C.redImage I).offDiag.image Sym2.mk := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.1 hz with ⟨p, hp, rfl⟩
    rcases p with ⟨r, r'⟩
    rcases (C.mem_redBasePairSet.1 hp) with ⟨hr, hr', hlt⟩
    exact Finset.mem_image.2 ⟨(r, r'), Finset.mem_offDiag.2 ⟨hr, hr', hlt.ne⟩, rfl⟩
  · intro hz
    rcases Finset.mem_image.1 hz with ⟨p, hp, rfl⟩
    rcases p with ⟨r, r'⟩
    rcases Finset.mem_offDiag.1 hp with ⟨hr, hr', hneq⟩
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact Finset.mem_image.2 ⟨(r, r'), (C.mem_redBasePairSet.2 ⟨hr, hr', hlt⟩), rfl⟩
    · exact Finset.mem_image.2
        ⟨(r', r), (C.mem_redBasePairSet.2 ⟨hr', hr, hgt⟩),
          by exact (Sym2.mk_prod_swap_eq (p := (r', r))).symm⟩

theorem blueBasePairSet_image_sym2_eq_blueImage_offDiag_image (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    (C.blueBasePairSet I).image Sym2.mk = (C.blueImage I).offDiag.image Sym2.mk := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.1 hz with ⟨p, hp, rfl⟩
    rcases p with ⟨b, b'⟩
    rcases (C.mem_blueBasePairSet.1 hp) with ⟨hb, hb', hlt⟩
    exact Finset.mem_image.2 ⟨(b, b'), Finset.mem_offDiag.2 ⟨hb, hb', hlt.ne⟩, rfl⟩
  · intro hz
    rcases Finset.mem_image.1 hz with ⟨p, hp, rfl⟩
    rcases p with ⟨b, b'⟩
    rcases Finset.mem_offDiag.1 hp with ⟨hb, hb', hneq⟩
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact Finset.mem_image.2 ⟨(b, b'), (C.mem_blueBasePairSet.2 ⟨hb, hb', hlt⟩), rfl⟩
    · exact Finset.mem_image.2
        ⟨(b', b), (C.mem_blueBasePairSet.2 ⟨hb', hb, hgt⟩),
          by exact (Sym2.mk_prod_swap_eq (p := (b', b))).symm⟩

theorem redBasePairSet_card_eq_choose (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.redBasePairSet I).card = (C.redImage I).card.choose 2 := by
  have hstrict : ∀ p ∈ C.redBasePairSet I, p.1 < p.2 := by
    intro p hp
    exact (C.mem_redBasePairSet.1 hp).2.2
  calc
    (C.redBasePairSet I).card = ((C.redBasePairSet I).image Sym2.mk).card := by
      symm
      exact card_image_sym2_mk_of_strictPairSet _ hstrict
    _ = ((C.redImage I).offDiag.image Sym2.mk).card := by
      rw [C.redBasePairSet_image_sym2_eq_redImage_offDiag_image I]
    _ = (C.redImage I).card.choose 2 := by
      simpa using Sym2.card_image_offDiag (C.redImage I)

theorem blueBasePairSet_card_eq_choose (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.blueBasePairSet I).card = (C.blueImage I).card.choose 2 := by
  have hstrict : ∀ p ∈ C.blueBasePairSet I, p.1 < p.2 := by
    intro p hp
    exact (C.mem_blueBasePairSet.1 hp).2.2
  calc
    (C.blueBasePairSet I).card = ((C.blueBasePairSet I).image Sym2.mk).card := by
      symm
      exact card_image_sym2_mk_of_strictPairSet _ hstrict
    _ = ((C.blueImage I).offDiag.image Sym2.mk).card := by
      rw [C.blueBasePairSet_image_sym2_eq_blueImage_offDiag_image I]
    _ = (C.blueImage I).card.choose 2 := by
      simpa using Sym2.card_image_offDiag (C.blueImage I)

theorem redBaseOpenPairSet_card_add_redBaseClosedPairSet_card (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    (C.redBaseOpenPairSet I).card + (C.redBaseClosedPairSet I).card =
      (C.redBasePairSet I).card := by
  classical
  have hopen :
      C.redBaseOpenPairSet I =
        (C.redBasePairSet I).filter fun p => ¬ C.redBase.Adj p.1 p.2 := by
    ext p
    rcases p with ⟨r, r'⟩
    simp [redBaseOpenPairSet, redBasePairSet, and_left_comm, and_assoc]
  rw [hopen]
  simpa [add_comm, redBaseClosedPairSet] using
    (Finset.card_filter_add_card_filter_not (s := C.redBasePairSet I)
      (p := fun p => C.redBase.Adj p.1 p.2))

theorem blueBaseOpenPairSet_card_add_blueBaseClosedPairSet_card (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    (C.blueBaseOpenPairSet I).card + (C.blueBaseClosedPairSet I).card =
      (C.blueBasePairSet I).card := by
  classical
  have hopen :
      C.blueBaseOpenPairSet I =
        (C.blueBasePairSet I).filter fun p => ¬ C.blueBase.Adj p.1 p.2 := by
    ext p
    rcases p with ⟨b, b'⟩
    simp [blueBaseOpenPairSet, and_left_comm, and_assoc]
  rw [hopen]
  simpa [add_comm, blueBaseClosedPairSet] using
    (Finset.card_filter_add_card_filter_not (s := C.blueBasePairSet I)
      (p := fun p => C.blueBase.Adj p.1 p.2))

theorem swap_not_mem_redBaseOpenPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {r r' : Fin m} (h : (r, r') ∈ C.redBaseOpenPairSet I) :
    (r', r) ∉ C.redBaseOpenPairSet I := by
  intro hswap
  rcases (C.mem_redBaseOpenPairSet.1 h) with ⟨_, _, hlt, _⟩
  rcases (C.mem_redBaseOpenPairSet.1 hswap) with ⟨_, _, hlt', _⟩
  exact (lt_asymm hlt hlt').elim

theorem swap_not_mem_blueBaseOpenPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {b b' : Fin m} (h : (b, b') ∈ C.blueBaseOpenPairSet I) :
    (b', b) ∉ C.blueBaseOpenPairSet I := by
  intro hswap
  rcases (C.mem_blueBaseOpenPairSet.1 h) with ⟨_, _, hlt, _⟩
  rcases (C.mem_blueBaseOpenPairSet.1 hswap) with ⟨_, _, hlt', _⟩
  exact (lt_asymm hlt hlt').elim

theorem swap_not_mem_baseOpenPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {p : BaseVertex m × BaseVertex m} (h : p ∈ C.baseOpenPairSet I) :
    p.swap ∉ C.baseOpenPairSet I := by
  rcases p with ⟨x, y⟩
  cases x <;> cases y
  · intro hswap
    exact
      C.swap_not_mem_redBaseOpenPairSet ((C.mem_baseOpenPairSet_inl_inl).1 h)
        ((C.mem_baseOpenPairSet_inl_inl).1 hswap)
  · exact (C.not_mem_baseOpenPairSet_inl_inr).elim h
  · exact (C.not_mem_baseOpenPairSet_inr_inl).elim h
  · intro hswap
    exact
      C.swap_not_mem_blueBaseOpenPairSet ((C.mem_baseOpenPairSet_inr_inr).1 h)
        ((C.mem_baseOpenPairSet_inr_inr).1 hswap)

theorem baseOpenPairSet_card_eq_redBaseOpenPairSet_card_add_blueBaseOpenPairSet_card
    (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.baseOpenPairSet I).card =
      (C.redBaseOpenPairSet I).card + (C.blueBaseOpenPairSet I).card := by
  classical
  let sR : Finset (BaseVertex m × BaseVertex m) :=
    (C.redBaseOpenPairSet I).image fun p => (Sum.inl p.1, Sum.inl p.2)
  let sB : Finset (BaseVertex m × BaseVertex m) :=
    (C.blueBaseOpenPairSet I).image fun p => (Sum.inr p.1, Sum.inr p.2)
  have hsR :
      sR.card = (C.redBaseOpenPairSet I).card := by
    dsimp [sR]
    simpa using
      (Finset.card_image_of_injective (s := C.redBaseOpenPairSet I)
        (f := fun p => (Sum.inl p.1, Sum.inl p.2))
        (by
          intro a b hab
          cases a
          cases b
          cases hab
          rfl))
  have hsB :
      sB.card = (C.blueBaseOpenPairSet I).card := by
    dsimp [sB]
    simpa using
      (Finset.card_image_of_injective (s := C.blueBaseOpenPairSet I)
        (f := fun p => (Sum.inr p.1, Sum.inr p.2))
        (by
          intro a b hab
          cases a
          cases b
          cases hab
          rfl))
  have hdisj : Disjoint sR sB := by
    refine Finset.disjoint_left.2 ?_
    intro p hpR hpB
    rcases Finset.mem_image.1 hpR with ⟨r, hr, hpR'⟩
    rcases Finset.mem_image.1 hpB with ⟨b, hb, hpB'⟩
    rcases r with ⟨r₁, r₂⟩
    rcases b with ⟨b₁, b₂⟩
    rw [← hpR'] at hpB'
    cases hpB'
  have hcard :
      (C.baseOpenPairSet I).card = sR.card + sB.card := by
    dsimp [sR, sB]
    rw [baseOpenPairSet]
    simpa using (Finset.card_union_eq_card_add_card.2 hdisj)
  rw [hcard, hsR, hsB]

theorem baseOpenPairSet_lower_bound_of_closedBounds (C : ConstructionData n m)
    (I : Finset (Fin n)) {redBound blueBound : ℕ}
    (hred : (C.redBaseClosedPairSet I).card ≤ redBound)
    (hblue : (C.blueBaseClosedPairSet I).card ≤ blueBound) :
    (C.redImage I).card.choose 2 + (C.blueImage I).card.choose 2 - redBound - blueBound ≤
      (C.baseOpenPairSet I).card := by
  have hbase := C.baseOpenPairSet_card_eq_redBaseOpenPairSet_card_add_blueBaseOpenPairSet_card I
  have hredPart := C.redBaseOpenPairSet_card_add_redBaseClosedPairSet_card I
  have hbluePart := C.blueBaseOpenPairSet_card_add_blueBaseClosedPairSet_card I
  have hredTot := C.redBasePairSet_card_eq_choose I
  have hblueTot := C.blueBasePairSet_card_eq_choose I
  omega

theorem fst_mem_baseImage_of_mem_baseOpenPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {p : BaseVertex m × BaseVertex m} (h : p ∈ C.baseOpenPairSet I) : p.1 ∈ C.baseImage I := by
  rcases p with ⟨x, y⟩
  cases x <;> cases y
  · exact
      C.mem_baseImage_inl.2
        ((C.mem_redBaseOpenPairSet.1 ((C.mem_baseOpenPairSet_inl_inl).1 h)).1)
  · exact (C.not_mem_baseOpenPairSet_inl_inr).elim h
  · exact (C.not_mem_baseOpenPairSet_inr_inl).elim h
  · exact
      C.mem_baseImage_inr.2 ((C.mem_blueBaseOpenPairSet.1 ((C.mem_baseOpenPairSet_inr_inr).1 h)).1)

theorem snd_mem_baseImage_of_mem_baseOpenPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {p : BaseVertex m × BaseVertex m} (h : p ∈ C.baseOpenPairSet I) : p.2 ∈ C.baseImage I := by
  rcases p with ⟨x, y⟩
  cases x <;> cases y
  · exact
      C.mem_baseImage_inl.2
        ((C.mem_redBaseOpenPairSet.1 ((C.mem_baseOpenPairSet_inl_inl).1 h)).2.1)
  · exact (C.not_mem_baseOpenPairSet_inl_inr).elim h
  · exact (C.not_mem_baseOpenPairSet_inr_inl).elim h
  · exact
      C.mem_baseImage_inr.2
        ((C.mem_blueBaseOpenPairSet.1 ((C.mem_baseOpenPairSet_inr_inr).1 h)).2.1)

/-- Orient a revealed canonical base open pair toward a queried endpoint. -/
def orientBaseOpenPairToReveal (A : Finset (BaseVertex m))
    (p : BaseVertex m × BaseVertex m) : BaseVertex m × BaseVertex m :=
  if p.1 ∈ A then p else p.swap

theorem orientBaseOpenPairToReveal_mem_section4RevealPairSet (C : ConstructionData n m)
    {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {p : BaseVertex m × BaseVertex m}
    (h : p ∈ C.revealedBaseOpenPairSet I A) :
    orientBaseOpenPairToReveal A p ∈ C.section4RevealPairSet I A := by
  rcases (C.mem_revealedBaseOpenPairSet.1 h) with ⟨hpBase, hpA⟩
  have hpFstBase := C.fst_mem_baseImage_of_mem_baseOpenPairSet hpBase
  have hpSndBase := C.snd_mem_baseImage_of_mem_baseOpenPairSet hpBase
  rcases p with ⟨x, y⟩
  cases x with
  | inl r =>
      cases y with
      | inl r' =>
          by_cases hrA : Sum.inl r ∈ A
          · have hneq : r ≠ r' := by
              exact
                (C.mem_redBaseOpenPairSet.1 ((C.mem_baseOpenPairSet_inl_inl).1 hpBase)).2.2.1.ne
            have hmem :
                (Sum.inl r, Sum.inl r') ∈ revealedBaseArcSet A (C.baseImage I) := by
              exact
                (mem_revealedBaseArcSet_inl_inl
                  (A := A) (B := C.baseImage I) (r := r) (r' := r')).2
                  ⟨hrA, hpSndBase, hneq⟩
            simpa [orientBaseOpenPairToReveal, section4RevealPairSet, revealedBasePairSet, hrA]
              using hmem
          · have hr'A : Sum.inl r' ∈ A := by
              rcases hpA with hrA' | hr'A
              · exact (hrA hrA').elim
              · exact hr'A
            have hneq : r' ≠ r := by
              exact Ne.symm
                ((C.mem_redBaseOpenPairSet.1 ((C.mem_baseOpenPairSet_inl_inl).1 hpBase)).2.2.1.ne)
            have hmem :
                (Sum.inl r', Sum.inl r) ∈ revealedBaseArcSet A (C.baseImage I) := by
              exact
                (mem_revealedBaseArcSet_inl_inl
                  (A := A) (B := C.baseImage I) (r := r') (r' := r)).2
                  ⟨hr'A, hpFstBase, hneq⟩
            simpa [orientBaseOpenPairToReveal, section4RevealPairSet, revealedBasePairSet, hrA]
              using hmem
      | inr b =>
          exact (C.not_mem_baseOpenPairSet_inl_inr).elim hpBase
  | inr b =>
      cases y with
      | inl r =>
          exact (C.not_mem_baseOpenPairSet_inr_inl).elim hpBase
      | inr b' =>
          by_cases hbA : Sum.inr b ∈ A
          · have hneq : b ≠ b' := by
              exact
                (C.mem_blueBaseOpenPairSet.1 ((C.mem_baseOpenPairSet_inr_inr).1 hpBase)).2.2.1.ne
            have hmem :
                (Sum.inr b, Sum.inr b') ∈ revealedBaseArcSet A (C.baseImage I) := by
              exact
                (mem_revealedBaseArcSet_inr_inr
                  (A := A) (B := C.baseImage I) (b := b) (b' := b')).2
                  ⟨hbA, hpSndBase, hneq⟩
            simpa [orientBaseOpenPairToReveal, section4RevealPairSet, revealedBasePairSet, hbA]
              using hmem
          · have hb'A : Sum.inr b' ∈ A := by
              rcases hpA with hbA' | hb'A
              · exact (hbA hbA').elim
              · exact hb'A
            have hneq : b' ≠ b := by
              exact Ne.symm
                ((C.mem_blueBaseOpenPairSet.1 ((C.mem_baseOpenPairSet_inr_inr).1 hpBase)).2.2.1.ne)
            have hmem :
                (Sum.inr b', Sum.inr b) ∈ revealedBaseArcSet A (C.baseImage I) := by
              exact
                (mem_revealedBaseArcSet_inr_inr
                  (A := A) (B := C.baseImage I) (b := b') (b' := b)).2
                  ⟨hb'A, hpFstBase, hneq⟩
            simpa [orientBaseOpenPairToReveal, section4RevealPairSet, revealedBasePairSet, hbA]
              using hmem

theorem orientBaseOpenPairToReveal_injOn (C : ConstructionData n m) {I : Finset (Fin n)}
    (A : Finset (BaseVertex m)) :
    Set.InjOn (orientBaseOpenPairToReveal A) (C.revealedBaseOpenPairSet I A) := by
  intro p hp q hq hpq
  have hpBase := (C.mem_revealedBaseOpenPairSet.1 hp).1
  have hqBase := (C.mem_revealedBaseOpenPairSet.1 hq).1
  by_cases hpA : p.1 ∈ A
  · by_cases hqA : q.1 ∈ A
    · simpa [orientBaseOpenPairToReveal, hpA, hqA] using hpq
    · have hswap : p = q.swap := by
        simpa [orientBaseOpenPairToReveal, hpA, hqA] using hpq
      have hqswap : q.swap ∈ C.baseOpenPairSet I := by simpa [hswap] using hpBase
      exact False.elim ((C.swap_not_mem_baseOpenPairSet hqBase) hqswap)
  · by_cases hqA : q.1 ∈ A
    · have hswap : p.swap = q := by
        simpa [orientBaseOpenPairToReveal, hpA, hqA] using hpq
      have hpswap : p.swap ∈ C.baseOpenPairSet I := by simpa [hswap] using hqBase
      exact False.elim ((C.swap_not_mem_baseOpenPairSet hpBase) hpswap)
    · have hswap : p.swap = q.swap := by
        simpa [orientBaseOpenPairToReveal, hpA, hqA] using hpq
      exact by simpa using congrArg Prod.swap hswap

theorem revealedBaseOpenPairSet_card_le_section4RevealPairSet_card (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.revealedBaseOpenPairSet I A).card ≤ (C.section4RevealPairSet I A).card := by
  apply Finset.card_le_card_of_injOn (f := orientBaseOpenPairToReveal A)
  · intro p hp
    exact C.orientBaseOpenPairToReveal_mem_section4RevealPairSet hp
  · exact C.orientBaseOpenPairToReveal_injOn A

theorem revealedBaseOpenPairSet_card_add_unrevealedBaseOpenPairSet_card
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.revealedBaseOpenPairSet I A).card + (C.unrevealedBaseOpenPairSet I A).card =
      (C.baseOpenPairSet I).card := by
  simpa [revealedBaseOpenPairSet, unrevealedBaseOpenPairSet, not_or] using
    (Finset.card_filter_add_card_filter_not (s := C.baseOpenPairSet I)
      (p := fun p => p.1 ∈ A ∨ p.2 ∈ A))

theorem baseOpenPairSet_card_sub_revealed_le_unrevealed
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.baseOpenPairSet I).card - (C.revealedBaseOpenPairSet I A).card ≤
      (C.unrevealedBaseOpenPairSet I A).card := by
  have hcard := C.revealedBaseOpenPairSet_card_add_unrevealedBaseOpenPairSet_card I A
  omega

theorem openPair_lower_bound_sub_reveal_budget_le_unrevealed
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m))
    {N : ℕ} (hopen : N ≤ (C.baseOpenPairSet I).card) :
    N - (C.revealedBaseOpenPairSet I A).card ≤ (C.unrevealedBaseOpenPairSet I A).card := by
  have hsub := C.baseOpenPairSet_card_sub_revealed_le_unrevealed I A
  omega

theorem mem_basePairSet_of_mem_baseOpenPairSet (C : ConstructionData n m) {I : Finset (Fin n)}
    {p : BaseVertex m × BaseVertex m} (h : p ∈ C.baseOpenPairSet I) : p ∈ C.basePairSet I := by
  rcases p with ⟨x, y⟩
  cases x <;> cases y
  · rcases (C.mem_redBaseOpenPairSet.1 ((C.mem_baseOpenPairSet_inl_inl).1 h)) with
      ⟨hr, hr', hlt, -⟩
    exact (C.mem_basePairSet_inl_inl).2 ((C.mem_redBasePairSet).2 ⟨hr, hr', hlt⟩)
  · exact (C.not_mem_baseOpenPairSet_inl_inr).elim h
  · exact (C.not_mem_baseOpenPairSet_inr_inl).elim h
  · rcases (C.mem_blueBaseOpenPairSet.1 ((C.mem_baseOpenPairSet_inr_inr).1 h)) with
      ⟨hb, hb', hlt, -⟩
    exact (C.mem_basePairSet_inr_inr).2 ((C.mem_blueBasePairSet).2 ⟨hb, hb', hlt⟩)

theorem unrevealedBaseOpenPairSet_subset_unrevealedBasePairSet (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.unrevealedBaseOpenPairSet I A ⊆ C.unrevealedBasePairSet I A := by
  intro p hp
  rcases (C.mem_unrevealedBaseOpenPairSet.1 hp) with ⟨hpOpen, hp1, hp2⟩
  exact (C.mem_unrevealedBasePairSet.2 ⟨C.mem_basePairSet_of_mem_baseOpenPairSet hpOpen, hp1, hp2⟩)

theorem unrevealedBaseOpenPairSet_card_le_unrevealedBasePairSet_card
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.unrevealedBaseOpenPairSet I A).card ≤ (C.unrevealedBasePairSet I A).card := by
  exact Finset.card_le_card (C.unrevealedBaseOpenPairSet_subset_unrevealedBasePairSet I A)

theorem mem_section4F_iff_mem_union_of_mem_baseImage (C : ConstructionData n m)
    {I : Finset (Fin n)} {ε : ℝ} {x : BaseVertex m} (hxBase : x ∈ C.baseImage I) :
    x ∈ C.section4F I ε ↔ x ∈ C.section4F1 I ∪ C.section4F2 I ε := by
  rw [C.mem_section4F]
  constructor
  · intro hx
    rcases hx with hx0 | hx12
    · exact False.elim ((C.mem_section4F0.1 hx0).2 hxBase)
    · simpa [Finset.mem_union] using hx12
  · intro hx
    exact Or.inr (by simpa [Finset.mem_union] using hx)

theorem not_mem_section4F_iff_not_mem_union_of_mem_baseImage (C : ConstructionData n m)
    {I : Finset (Fin n)} {ε : ℝ} {x : BaseVertex m} (hxBase : x ∈ C.baseImage I) :
    x ∉ C.section4F I ε ↔ x ∉ C.section4F1 I ∪ C.section4F2 I ε := by
  exact not_congr (C.mem_section4F_iff_mem_union_of_mem_baseImage hxBase)

theorem revealedBaseOpenPairSet_section4F_eq_union (C : ConstructionData n m)
    (I : Finset (Fin n)) (ε : ℝ) :
    C.revealedBaseOpenPairSet I (C.section4F I ε) =
      C.revealedBaseOpenPairSet I (C.section4F1 I ∪ C.section4F2 I ε) := by
  classical
  ext p
  constructor
  · intro hp
    rcases (C.mem_revealedBaseOpenPairSet.1 hp) with ⟨hpBase, hpA⟩
    have hpFstBase := C.fst_mem_baseImage_of_mem_baseOpenPairSet hpBase
    have hpSndBase := C.snd_mem_baseImage_of_mem_baseOpenPairSet hpBase
    refine (C.mem_revealedBaseOpenPairSet.2 ?_)
    refine ⟨hpBase, ?_⟩
    rcases hpA with hp1 | hp2
    · exact Or.inl ((C.mem_section4F_iff_mem_union_of_mem_baseImage hpFstBase).1 hp1)
    · exact Or.inr ((C.mem_section4F_iff_mem_union_of_mem_baseImage hpSndBase).1 hp2)
  · intro hp
    rcases (C.mem_revealedBaseOpenPairSet.1 hp) with ⟨hpBase, hpA⟩
    refine (C.mem_revealedBaseOpenPairSet.2 ?_)
    refine ⟨hpBase, ?_⟩
    rcases hpA with hp1 | hp2
    · exact Or.inl ((C.mem_section4F_iff_mem_union_of_mem_baseImage
        (C.fst_mem_baseImage_of_mem_baseOpenPairSet hpBase)).2 hp1)
    · exact Or.inr ((C.mem_section4F_iff_mem_union_of_mem_baseImage
        (C.snd_mem_baseImage_of_mem_baseOpenPairSet hpBase)).2 hp2)

theorem unrevealedBaseOpenPairSet_section4F_eq_union (C : ConstructionData n m)
    (I : Finset (Fin n)) (ε : ℝ) :
    C.unrevealedBaseOpenPairSet I (C.section4F I ε) =
      C.unrevealedBaseOpenPairSet I (C.section4F1 I ∪ C.section4F2 I ε) := by
  classical
  ext p
  constructor
  · intro hp
    rcases (C.mem_unrevealedBaseOpenPairSet.1 hp) with ⟨hpBase, hp1, hp2⟩
    have hpFstBase := C.fst_mem_baseImage_of_mem_baseOpenPairSet hpBase
    have hpSndBase := C.snd_mem_baseImage_of_mem_baseOpenPairSet hpBase
    refine (C.mem_unrevealedBaseOpenPairSet.2 ?_)
    refine ⟨hpBase, ?_, ?_⟩
    · exact ((C.not_mem_section4F_iff_not_mem_union_of_mem_baseImage hpFstBase).1 hp1)
    · exact ((C.not_mem_section4F_iff_not_mem_union_of_mem_baseImage hpSndBase).1 hp2)
  · intro hp
    rcases (C.mem_unrevealedBaseOpenPairSet.1 hp) with ⟨hpBase, hp1, hp2⟩
    refine (C.mem_unrevealedBaseOpenPairSet.2 ?_)
    refine ⟨hpBase, ?_, ?_⟩
    · exact ((C.not_mem_section4F_iff_not_mem_union_of_mem_baseImage
        (C.fst_mem_baseImage_of_mem_baseOpenPairSet hpBase)).2 hp1)
    · exact ((C.not_mem_section4F_iff_not_mem_union_of_mem_baseImage
        (C.snd_mem_baseImage_of_mem_baseOpenPairSet hpBase)).2 hp2)

theorem section4F1_subset_baseImage (C : ConstructionData n m) (I : Finset (Fin n)) :
    C.section4F1 I ⊆ C.baseImage I := by
  intro x hx
  exact (C.mem_section4F1).1 hx |>.1

theorem section4F2_subset_baseImage (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) :
    C.section4F2 I ε ⊆ C.baseImage I := by
  intro x hx
  exact (C.mem_section4F2).1 hx |>.1

theorem filter_isRed_union_filter_isBlue (A : Finset (BaseVertex m)) :
    A.filter IsRedBaseVertex ∪ A.filter IsBlueBaseVertex = A := by
  classical
  ext x
  cases x <;> simp [IsRedBaseVertex, IsBlueBaseVertex]

theorem disjoint_filter_isRed_filter_isBlue (A : Finset (BaseVertex m)) :
    Disjoint (A.filter IsRedBaseVertex) (A.filter IsBlueBaseVertex) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro x hxRed hxBlue
  cases x <;> simp [IsRedBaseVertex, IsBlueBaseVertex] at hxRed hxBlue

theorem card_filter_isRed_add_card_filter_isBlue (A : Finset (BaseVertex m)) :
    (A.filter IsRedBaseVertex).card + (A.filter IsBlueBaseVertex).card = A.card := by
  classical
  calc
    (A.filter IsRedBaseVertex).card + (A.filter IsBlueBaseVertex).card =
        (A.filter IsRedBaseVertex ∪ A.filter IsBlueBaseVertex).card := by
      symm
      exact Finset.card_union_of_disjoint (disjoint_filter_isRed_filter_isBlue A)
    _ = A.card := by rw [filter_isRed_union_filter_isBlue]

theorem baseImage_filter_isRed_eq_redImage_image_inl (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    (C.baseImage I).filter IsRedBaseVertex = (C.redImage I).image Sum.inl := by
  classical
  ext x
  cases x with
  | inl r =>
      simp [mem_baseImage_inl]
  | inr b =>
      simp

theorem baseImage_filter_isBlue_eq_blueImage_image_inr (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    (C.baseImage I).filter IsBlueBaseVertex = (C.blueImage I).image Sum.inr := by
  classical
  ext x
  cases x with
  | inl r =>
      simp
  | inr b =>
      simp [mem_baseImage_inr]

theorem univ_filter_isRed_eq_univ_image_inl :
    ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) =
      (Finset.univ : Finset (Fin m)).image Sum.inl := by
  classical
  ext x
  cases x <;> simp [IsRedBaseVertex]

theorem univ_filter_isBlue_eq_univ_image_inr :
    ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) =
      (Finset.univ : Finset (Fin m)).image Sum.inr := by
  classical
  ext x
  cases x <;> simp [IsBlueBaseVertex]

theorem baseImage_filter_isRed_card_eq_redImage_card (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    ((C.baseImage I).filter IsRedBaseVertex).card = (C.redImage I).card := by
  rw [C.baseImage_filter_isRed_eq_redImage_image_inl I]
  simpa using
    (Finset.card_image_of_injective (s := C.redImage I) (f := Sum.inl)
      (by
        intro a b hab
        exact Sum.inl.inj hab))

theorem baseImage_filter_isBlue_card_eq_blueImage_card (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    ((C.baseImage I).filter IsBlueBaseVertex).card = (C.blueImage I).card := by
  rw [C.baseImage_filter_isBlue_eq_blueImage_image_inr I]
  simpa using
    (Finset.card_image_of_injective (s := C.blueImage I) (f := Sum.inr)
      (by
        intro a b hab
        exact Sum.inr.inj hab))

theorem section4F0_disjoint_baseImage (C : ConstructionData n m) (I : Finset (Fin n)) :
    Disjoint (C.section4F0 I) (C.baseImage I) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx0 hxI
  exact (C.mem_section4F0.1 hx0).2 hxI

theorem section4F0_union_baseImage (C : ConstructionData n m) (I : Finset (Fin n)) :
    C.section4F0 I ∪ C.baseImage I = Finset.univ := by
  classical
  ext x
  simp [section4F0]

@[simp] theorem mem_redProjectionImage_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {r r' : Fin m} :
    r' ∈ C.redProjectionImage I (Sum.inl r) ↔ C.redBase.Adj r r' ∧ r' ∈ C.redImage I := by
  constructor
  · intro hr'
    rcases Finset.mem_image.1 hr' with ⟨v, hvX, hrv⟩
    rcases (C.mem_X_red).1 hvX with ⟨hvI, hAdj⟩
    rw [hrv] at hAdj
    refine ⟨hAdj, ?_⟩
    exact (C.mem_redImage).2 ⟨v, hvI, hrv⟩
  · rintro ⟨hAdj, hrI⟩
    rcases (C.mem_redImage).1 hrI with ⟨v, hvI, hrv⟩
    refine Finset.mem_image.2 ⟨v, ?_, hrv⟩
    have hAdj' : C.redBase.Adj r (C.redProj v) := by
      rwa [hrv]
    exact (C.mem_X_red).2 ⟨hvI, hAdj'⟩

@[simp] theorem mem_blueProjectionImage_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {b b' : Fin m} :
    b' ∈ C.blueProjectionImage I (Sum.inr b) ↔
      C.blueBase.Adj b b' ∧ b' ∈ C.blueImage I := by
  constructor
  · intro hb'
    rcases Finset.mem_image.1 hb' with ⟨v, hvX, hbv⟩
    rcases (C.mem_X_blue).1 hvX with ⟨hvI, hAdj⟩
    rw [hbv] at hAdj
    refine ⟨hAdj, ?_⟩
    exact (C.mem_blueImage).2 ⟨v, hvI, hbv⟩
  · rintro ⟨hAdj, hbI⟩
    rcases (C.mem_blueImage).1 hbI with ⟨v, hvI, hbv⟩
    refine Finset.mem_image.2 ⟨v, ?_, hbv⟩
    have hAdj' : C.blueBase.Adj b (C.blueProj v) := by
      rwa [hbv]
    exact (C.mem_X_blue).2 ⟨hvI, hAdj'⟩

@[simp] theorem mem_redProjectionImage_inr (C : ConstructionData n m) {I : Finset (Fin n)}
    {b r : Fin m} :
    r ∈ C.redProjectionImage I (Sum.inr b) ↔
      ∃ v ∈ I, C.blueBase.Adj b (C.blueProj v) ∧ C.redProj v = r := by
  constructor
  · intro hr
    rcases Finset.mem_image.1 hr with ⟨v, hvX, hrv⟩
    rcases (C.mem_X_blue).1 hvX with ⟨hvI, hAdj⟩
    exact ⟨v, hvI, hAdj, hrv⟩
  · rintro ⟨v, hvI, hAdj, hrv⟩
    refine Finset.mem_image.2 ⟨v, ?_, hrv⟩
    exact (C.mem_X_blue).2 ⟨hvI, hAdj⟩

@[simp] theorem mem_blueProjectionImage_inl (C : ConstructionData n m) {I : Finset (Fin n)}
    {r b : Fin m} :
    b ∈ C.blueProjectionImage I (Sum.inl r) ↔
      ∃ v ∈ I, C.redBase.Adj r (C.redProj v) ∧ C.blueProj v = b := by
  constructor
  · intro hb
    rcases Finset.mem_image.1 hb with ⟨v, hvX, hbv⟩
    rcases (C.mem_X_red).1 hvX with ⟨hvI, hAdj⟩
    exact ⟨v, hvI, hAdj, hbv⟩
  · rintro ⟨v, hvI, hAdj, hbv⟩
    refine Finset.mem_image.2 ⟨v, ?_, hbv⟩
    exact (C.mem_X_red).2 ⟨hvI, hAdj⟩

theorem redProjectionImage_image_inl_eq_baseNeighborSet_inter_baseImage
    (C : ConstructionData n m) (I : Finset (Fin n)) (r : Fin m) :
    (C.redProjectionImage I (Sum.inl r)).image Sum.inl =
      C.baseNeighborSet (Sum.inl r) ∩ C.baseImage I := by
  ext x
  cases x with
  | inl r' =>
      simp [C.mem_redProjectionImage_inl, and_assoc]
  | inr b =>
      simp

theorem blueProjectionImage_image_inr_eq_baseNeighborSet_inter_baseImage
    (C : ConstructionData n m) (I : Finset (Fin n)) (b : Fin m) :
    (C.blueProjectionImage I (Sum.inr b)).image Sum.inr =
      C.baseNeighborSet (Sum.inr b) ∩ C.baseImage I := by
  ext x
  cases x with
  | inl r =>
      simp
  | inr b' =>
      simp [C.mem_blueProjectionImage_inr, and_assoc]

theorem
    redProjectionImage_filter_section4F1_image_inl_eq_baseNeighborSet_inter_section4F1
    (C : ConstructionData n m) (I : Finset (Fin n)) (r : Fin m) :
    ((C.redProjectionImage I (Sum.inl r)).filter fun r' => Sum.inl r' ∈ C.section4F1 I).image
        Sum.inl =
      C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I := by
  ext x
  cases x with
  | inl r' =>
      constructor
      · intro hx
        rcases Finset.mem_image.1 hx with ⟨s, hs, hsEq⟩
        rcases Finset.mem_filter.1 hs with ⟨hsProj, hsF1⟩
        have hAdj : C.redBase.Adj r s := (C.mem_redProjectionImage_inl.1 hsProj).1
        exact hsEq ▸ Finset.mem_inter.2 ⟨by simpa using hAdj, hsF1⟩
      · intro hx
        rcases Finset.mem_inter.1 hx with ⟨hAdjMem, hF1⟩
        have hAdj : C.redBase.Adj r r' := (C.mem_baseNeighborSet_inl_inl.1 hAdjMem)
        have hsProj : r' ∈ C.redProjectionImage I (Sum.inl r) := by
          exact (C.mem_redProjectionImage_inl.2
            ⟨hAdj, C.mem_baseImage_inl.1 ((C.mem_section4F1.1 hF1).1)⟩)
        exact Finset.mem_image.2 ⟨r', Finset.mem_filter.2 ⟨hsProj, hF1⟩, rfl⟩
  | inr b =>
      simp

theorem
    blueProjectionImage_filter_section4F1_image_inr_eq_baseNeighborSet_inter_section4F1
    (C : ConstructionData n m) (I : Finset (Fin n)) (b : Fin m) :
    ((C.blueProjectionImage I (Sum.inr b)).filter fun b' => Sum.inr b' ∈ C.section4F1 I).image
        Sum.inr =
      C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I := by
  ext x
  cases x with
  | inl r =>
      simp
  | inr b' =>
      constructor
      · intro hx
        rcases Finset.mem_image.1 hx with ⟨s, hs, hsEq⟩
        rcases Finset.mem_filter.1 hs with ⟨hsProj, hsF1⟩
        have hAdj : C.blueBase.Adj b s := (C.mem_blueProjectionImage_inr.1 hsProj).1
        exact hsEq ▸ Finset.mem_inter.2 ⟨by simpa using hAdj, hsF1⟩
      · intro hx
        rcases Finset.mem_inter.1 hx with ⟨hAdjMem, hF1⟩
        have hAdj : C.blueBase.Adj b b' := (C.mem_baseNeighborSet_inr_inr.1 hAdjMem)
        have hsProj : b' ∈ C.blueProjectionImage I (Sum.inr b) := by
          exact (C.mem_blueProjectionImage_inr.2
            ⟨hAdj, C.mem_baseImage_inr.1 ((C.mem_section4F1.1 hF1).1)⟩)
        exact Finset.mem_image.2 ⟨b', Finset.mem_filter.2 ⟨hsProj, hF1⟩, rfl⟩

theorem disjoint_redFiber_inter (C : ConstructionData n m) (I : Finset (Fin n))
    {r r' : Fin m} (hrr' : r ≠ r') :
    Disjoint (C.redFiber r ∩ I) (C.redFiber r' ∩ I) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rcases Finset.mem_inter.1 hv with ⟨hvFiber, _⟩
  rcases Finset.mem_inter.1 hv' with ⟨hvFiber', _⟩
  have h1 : C.redProj v = r := C.mem_redFiber.1 hvFiber
  have h2 : C.redProj v = r' := C.mem_redFiber.1 hvFiber'
  exact hrr' (h1.symm.trans h2)

theorem disjoint_blueFiber_inter (C : ConstructionData n m) (I : Finset (Fin n))
    {b b' : Fin m} (hbb' : b ≠ b') :
    Disjoint (C.blueFiber b ∩ I) (C.blueFiber b' ∩ I) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rcases Finset.mem_inter.1 hv with ⟨hvFiber, _⟩
  rcases Finset.mem_inter.1 hv' with ⟨hvFiber', _⟩
  have h1 : C.blueProj v = b := C.mem_blueFiber.1 hvFiber
  have h2 : C.blueProj v = b' := C.mem_blueFiber.1 hvFiber'
  exact hbb' (h1.symm.trans h2)

theorem X_red_eq_biUnion_redFiber_inter (C : ConstructionData n m) (I : Finset (Fin n))
    (r : Fin m) :
    C.X I (Sum.inl r) =
      (C.redProjectionImage I (Sum.inl r)).biUnion fun r' => C.redFiber r' ∩ I := by
  ext v
  constructor
  · intro hv
    refine Finset.mem_biUnion.2 ⟨C.redProj v, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨v, hv, rfl⟩
    · rcases (C.mem_X_red).1 hv with ⟨hvI, _⟩
      simp [hvI]
  · intro hv
    rcases Finset.mem_biUnion.1 hv with ⟨r', hr', hv'⟩
    rcases Finset.mem_inter.1 hv' with ⟨hvFiber, hvI⟩
    have hAdj : C.redBase.Adj r r' := (C.mem_redProjectionImage_inl.1 hr').1
    have hAdj' : C.redBase.Adj r (C.redProj v) := by
      rwa [C.mem_redFiber.1 hvFiber]
    exact (C.mem_X_red).2 ⟨hvI, hAdj'⟩

theorem X_blue_eq_biUnion_blueFiber_inter (C : ConstructionData n m) (I : Finset (Fin n))
    (b : Fin m) :
    C.X I (Sum.inr b) =
      (C.blueProjectionImage I (Sum.inr b)).biUnion fun b' => C.blueFiber b' ∩ I := by
  ext v
  constructor
  · intro hv
    refine Finset.mem_biUnion.2 ⟨C.blueProj v, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨v, hv, rfl⟩
    · rcases (C.mem_X_blue).1 hv with ⟨hvI, _⟩
      simp [hvI]
  · intro hv
    rcases Finset.mem_biUnion.1 hv with ⟨b', hb', hv'⟩
    rcases Finset.mem_inter.1 hv' with ⟨hvFiber, hvI⟩
    have hAdj : C.blueBase.Adj b b' := (C.mem_blueProjectionImage_inr.1 hb').1
    have hAdj' : C.blueBase.Adj b (C.blueProj v) := by
      rwa [C.mem_blueFiber.1 hvFiber]
    exact (C.mem_X_blue).2 ⟨hvI, hAdj'⟩

theorem xCard_red_eq_sum_card_redFiber_inter (C : ConstructionData n m) (I : Finset (Fin n))
    (r : Fin m) :
    C.xCard I (Sum.inl r) =
      ∑ r' ∈ C.redProjectionImage I (Sum.inl r), (C.redFiber r' ∩ I).card := by
  rw [xCard, C.X_red_eq_biUnion_redFiber_inter I r]
  exact Finset.card_biUnion (by
    intro r' hr' s hs hrs
    exact C.disjoint_redFiber_inter I hrs)

theorem xCard_blue_eq_sum_card_blueFiber_inter (C : ConstructionData n m) (I : Finset (Fin n))
    (b : Fin m) :
    C.xCard I (Sum.inr b) =
      ∑ b' ∈ C.blueProjectionImage I (Sum.inr b), (C.blueFiber b' ∩ I).card := by
  rw [xCard, C.X_blue_eq_biUnion_blueFiber_inter I b]
  exact Finset.card_biUnion (by
    intro b' hb' c hc hbc
    exact C.disjoint_blueFiber_inter I hbc)

theorem section4F1_filter_isRed_card_mul_log_le_card (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    Real.log (n : ℝ) * (((C.section4F1 I).filter IsRedBaseVertex).card : ℝ) ≤ (I.card : ℝ) := by
  classical
  let A : Finset (Fin m) := (C.redImage I).filter fun r => Sum.inl r ∈ C.section4F1 I
  have hcard :
      (((C.section4F1 I).filter IsRedBaseVertex).card : ℝ) = (A.card : ℝ) := by
    have hAcard :
        A.card = ((C.section4F1 I).filter IsRedBaseVertex).card := by
      calc
        A.card = ((A.image fun r : Fin m => (Sum.inl r : BaseVertex m)).card) := by
          symm
          exact Finset.card_image_of_injective _ (by
            intro a b hab
            exact Sum.inl.inj hab)
        _ = ((C.section4F1 I).filter IsRedBaseVertex).card := by
          rw [show A.image (fun r : Fin m => (Sum.inl r : BaseVertex m)) =
              (C.section4F1 I).filter IsRedBaseVertex by
            ext x
            cases x with
            | inl r =>
                simp [A]
            | inr b =>
                simp [A]]
    exact_mod_cast hAcard.symm
  have hsum :
      Real.log (n : ℝ) * (A.card : ℝ) ≤
        ∑ r ∈ A, (((C.redFiber r ∩ I).card : ℕ) : ℝ) := by
    calc
      Real.log (n : ℝ) * (A.card : ℝ) = ∑ _r ∈ A, Real.log (n : ℝ) := by
        simp [mul_comm]
      _ ≤ ∑ r ∈ A, (((C.redFiber r ∩ I).card : ℕ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro r hr
        have hrF1 : Sum.inl r ∈ C.section4F1 I := (Finset.mem_filter.1 hr).2
        exact le_of_lt ((C.mem_section4F1.1 hrF1).2)
  have hdisj :
      (A : Set (Fin m)).PairwiseDisjoint fun r => C.redFiber r ∩ I := by
    intro r hr s hs hrs
    exact C.disjoint_redFiber_inter I hrs
  have hUnionNat :
      (A.biUnion fun r => C.redFiber r ∩ I).card =
        ∑ r ∈ A, (C.redFiber r ∩ I).card :=
    Finset.card_biUnion hdisj
  have hUnion :
      ((((A.biUnion fun r => C.redFiber r ∩ I).card : ℕ) : ℝ)) =
        ∑ r ∈ A, (((C.redFiber r ∩ I).card : ℕ) : ℝ) := by
    exact_mod_cast hUnionNat
  have hSubset : A.biUnion (fun r => C.redFiber r ∩ I) ⊆ I := by
    intro v hv
    rcases Finset.mem_biUnion.1 hv with ⟨r, -, hv'⟩
    exact (Finset.mem_inter.1 hv').2
  calc
    Real.log (n : ℝ) * (((C.section4F1 I).filter IsRedBaseVertex).card : ℝ)
        = Real.log (n : ℝ) * (A.card : ℝ) := by rw [hcard]
    _ ≤ ∑ r ∈ A, (((C.redFiber r ∩ I).card : ℕ) : ℝ) := hsum
    _ = (((A.biUnion fun r => C.redFiber r ∩ I).card : ℕ) : ℝ) := hUnion.symm
    _ ≤ (I.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSubset

theorem section4F1_filter_isBlue_card_mul_log_le_card (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    Real.log (n : ℝ) * (((C.section4F1 I).filter IsBlueBaseVertex).card : ℝ) ≤ (I.card : ℝ) := by
  classical
  let A : Finset (Fin m) := (C.blueImage I).filter fun b => Sum.inr b ∈ C.section4F1 I
  have hcard :
      (((C.section4F1 I).filter IsBlueBaseVertex).card : ℝ) = (A.card : ℝ) := by
    have hAcard :
        A.card = ((C.section4F1 I).filter IsBlueBaseVertex).card := by
      calc
        A.card = ((A.image fun b : Fin m => (Sum.inr b : BaseVertex m)).card) := by
          symm
          exact Finset.card_image_of_injective _ (by
            intro a b hab
            exact Sum.inr.inj hab)
        _ = ((C.section4F1 I).filter IsBlueBaseVertex).card := by
          rw [show A.image (fun b : Fin m => (Sum.inr b : BaseVertex m)) =
              (C.section4F1 I).filter IsBlueBaseVertex by
            ext x
            cases x with
            | inl r =>
                simp [A]
            | inr b =>
                simp [A]]
    exact_mod_cast hAcard.symm
  have hsum :
      Real.log (n : ℝ) * (A.card : ℝ) ≤
        ∑ b ∈ A, (((C.blueFiber b ∩ I).card : ℕ) : ℝ) := by
    calc
      Real.log (n : ℝ) * (A.card : ℝ) = ∑ _b ∈ A, Real.log (n : ℝ) := by
        simp [mul_comm]
      _ ≤ ∑ b ∈ A, (((C.blueFiber b ∩ I).card : ℕ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro b hb
        have hbF1 : Sum.inr b ∈ C.section4F1 I := (Finset.mem_filter.1 hb).2
        exact le_of_lt ((C.mem_section4F1.1 hbF1).2)
  have hdisj :
      (A : Set (Fin m)).PairwiseDisjoint fun b => C.blueFiber b ∩ I := by
    intro b hb c hc hbc
    exact C.disjoint_blueFiber_inter I hbc
  have hUnionNat :
      (A.biUnion fun b => C.blueFiber b ∩ I).card =
        ∑ b ∈ A, (C.blueFiber b ∩ I).card :=
    Finset.card_biUnion hdisj
  have hUnion :
      ((((A.biUnion fun b => C.blueFiber b ∩ I).card : ℕ) : ℝ)) =
        ∑ b ∈ A, (((C.blueFiber b ∩ I).card : ℕ) : ℝ) := by
    exact_mod_cast hUnionNat
  have hSubset : A.biUnion (fun b => C.blueFiber b ∩ I) ⊆ I := by
    intro v hv
    rcases Finset.mem_biUnion.1 hv with ⟨b, -, hv'⟩
    exact (Finset.mem_inter.1 hv').2
  calc
    Real.log (n : ℝ) * (((C.section4F1 I).filter IsBlueBaseVertex).card : ℝ)
        = Real.log (n : ℝ) * (A.card : ℝ) := by rw [hcard]
    _ ≤ ∑ b ∈ A, (((C.blueFiber b ∩ I).card : ℕ) : ℝ) := hsum
    _ = (((A.biUnion fun b => C.blueFiber b ∩ I).card : ℕ) : ℝ) := hUnion.symm
    _ ≤ (I.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSubset

theorem section4F1_eq_filter_isRed_union_filter_isBlue (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    C.section4F1 I =
      (C.section4F1 I).filter IsRedBaseVertex ∪ (C.section4F1 I).filter IsBlueBaseVertex := by
  ext x
  cases x with
  | inl r =>
      simp
  | inr b =>
      simp

theorem disjoint_section4F1_filter_isRed_filter_isBlue (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    Disjoint ((C.section4F1 I).filter IsRedBaseVertex)
      ((C.section4F1 I).filter IsBlueBaseVertex) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxR hxB
  cases x with
  | inl r =>
      simp at hxB
  | inr b =>
      simp at hxR

theorem section4F1_card_mul_log_le_two_mul_card (C : ConstructionData n m)
    (I : Finset (Fin n)) :
    Real.log (n : ℝ) * ((C.section4F1 I).card : ℝ) ≤ 2 * (I.card : ℝ) := by
  have hred := C.section4F1_filter_isRed_card_mul_log_le_card I
  have hblue := C.section4F1_filter_isBlue_card_mul_log_le_card I
  have hcard :
      (C.section4F1 I).card =
        ((C.section4F1 I).filter IsRedBaseVertex).card +
          ((C.section4F1 I).filter IsBlueBaseVertex).card := by
    calc
      (C.section4F1 I).card =
          (((C.section4F1 I).filter IsRedBaseVertex ∪
              (C.section4F1 I).filter IsBlueBaseVertex).card) := by
            rw [← C.section4F1_eq_filter_isRed_union_filter_isBlue I]
      _ =
          ((C.section4F1 I).filter IsRedBaseVertex).card +
            ((C.section4F1 I).filter IsBlueBaseVertex).card := by
          exact Finset.card_union_of_disjoint (C.disjoint_section4F1_filter_isRed_filter_isBlue I)
  calc
    Real.log (n : ℝ) * ((C.section4F1 I).card : ℝ)
        = Real.log (n : ℝ) *
            ((((C.section4F1 I).filter IsRedBaseVertex).card +
                ((C.section4F1 I).filter IsBlueBaseVertex).card : ℕ) : ℝ) := by
          rw [hcard]
    _ = Real.log (n : ℝ) * (((C.section4F1 I).filter IsRedBaseVertex).card : ℝ) +
          Real.log (n : ℝ) * (((C.section4F1 I).filter IsBlueBaseVertex).card : ℝ) := by
          simp [mul_add]
    _ ≤ (I.card : ℝ) + (I.card : ℝ) := by
      linarith
    _ = 2 * (I.card : ℝ) := by ring

theorem xCard_red_ge_log_mul_section4F1_neighbor_card (C : ConstructionData n m)
    (I : Finset (Fin n)) (r : Fin m) :
    Real.log (n : ℝ) * (((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ) ≤
      (C.xCard I (Sum.inl r) : ℝ) := by
  classical
  let A : Finset (Fin m) :=
    (C.redProjectionImage I (Sum.inl r)).filter fun r' => Sum.inl r' ∈ C.section4F1 I
  have hcard :
      (((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ) = (A.card : ℝ) := by
    have hAcard : A.card = (C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card := by
      calc
        A.card = ((A.image fun r' : Fin m => (Sum.inl r' : BaseVertex m)).card) := by
          symm
          exact Finset.card_image_of_injective _ (by
            intro a b hab
            exact Sum.inl.inj hab)
        _ = (C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card := by
          rw [C.redProjectionImage_filter_section4F1_image_inl_eq_baseNeighborSet_inter_section4F1
            I r]
    exact_mod_cast hAcard.symm
  have hsumA :
      Real.log (n : ℝ) * (A.card : ℝ) ≤
        ∑ r' ∈ A, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) := by
    calc
      Real.log (n : ℝ) * (A.card : ℝ) = ∑ _r' ∈ A, Real.log (n : ℝ) := by
        simp [mul_comm]
      _ ≤ ∑ r' ∈ A, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro r' hr'
        have hr'F1 : Sum.inl r' ∈ C.section4F1 I := (Finset.mem_filter.1 hr').2
        exact le_of_lt ((C.mem_section4F1.1 hr'F1).2)
  have hsumSubset :
      ∑ r' ∈ A, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) ≤
        ∑ r' ∈ C.redProjectionImage I (Sum.inl r), (((C.redFiber r' ∩ I).card : ℕ) : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
      intro r' hr' hnot
      positivity)
  have hwhole :
      (C.xCard I (Sum.inl r) : ℝ) =
        ∑ r' ∈ C.redProjectionImage I (Sum.inl r), (((C.redFiber r' ∩ I).card : ℕ) : ℝ) := by
    exact_mod_cast C.xCard_red_eq_sum_card_redFiber_inter I r
  calc
    Real.log (n : ℝ) * (((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ)
        = Real.log (n : ℝ) * (A.card : ℝ) := by rw [hcard]
    _ ≤ ∑ r' ∈ A, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) := hsumA
    _ ≤ ∑ r' ∈ C.redProjectionImage I (Sum.inl r), (((C.redFiber r' ∩ I).card : ℕ) : ℝ) :=
      hsumSubset
    _ = (C.xCard I (Sum.inl r) : ℝ) := hwhole.symm

theorem xCard_blue_ge_log_mul_section4F1_neighbor_card (C : ConstructionData n m)
    (I : Finset (Fin n)) (b : Fin m) :
    Real.log (n : ℝ) * (((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ) ≤
      (C.xCard I (Sum.inr b) : ℝ) := by
  classical
  let A : Finset (Fin m) :=
    (C.blueProjectionImage I (Sum.inr b)).filter fun b' => Sum.inr b' ∈ C.section4F1 I
  have hcard :
      (((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ) = (A.card : ℝ) := by
    have hAcard : A.card = (C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card := by
      calc
        A.card = ((A.image fun b' : Fin m => (Sum.inr b' : BaseVertex m)).card) := by
          symm
          exact Finset.card_image_of_injective _ (by
            intro a c hac
            exact Sum.inr.inj hac)
        _ = (C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card := by
          rw [C.blueProjectionImage_filter_section4F1_image_inr_eq_baseNeighborSet_inter_section4F1
            I b]
    exact_mod_cast hAcard.symm
  have hsumA :
      Real.log (n : ℝ) * (A.card : ℝ) ≤
        ∑ b' ∈ A, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) := by
    calc
      Real.log (n : ℝ) * (A.card : ℝ) = ∑ _b' ∈ A, Real.log (n : ℝ) := by
        simp [mul_comm]
      _ ≤ ∑ b' ∈ A, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro b' hb'
        have hb'F1 : Sum.inr b' ∈ C.section4F1 I := (Finset.mem_filter.1 hb').2
        exact le_of_lt ((C.mem_section4F1.1 hb'F1).2)
  have hsumSubset :
      ∑ b' ∈ A, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) ≤
        ∑ b' ∈ C.blueProjectionImage I (Sum.inr b), (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
      intro b' hb' hnot
      positivity)
  have hwhole :
      (C.xCard I (Sum.inr b) : ℝ) =
        ∑ b' ∈ C.blueProjectionImage I (Sum.inr b), (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) := by
    exact_mod_cast C.xCard_blue_eq_sum_card_blueFiber_inter I b
  calc
    Real.log (n : ℝ) * (((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ)
        = Real.log (n : ℝ) * (A.card : ℝ) := by rw [hcard]
    _ ≤ ∑ b' ∈ A, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) := hsumA
    _ ≤ ∑ b' ∈ C.blueProjectionImage I (Sum.inr b), (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) :=
      hsumSubset
    _ = (C.xCard I (Sum.inr b) : ℝ) := hwhole.symm


theorem mem_I_of_mem_X (C : ConstructionData n m) {I : Finset (Fin n)} {x : BaseVertex m}
    {v : Fin n} (hv : v ∈ C.X I x) : v ∈ I := by
  cases x with
  | inl r =>
      exact (C.mem_X_red).1 hv |>.1
  | inr b =>
      exact (C.mem_X_blue).1 hv |>.1

theorem mem_X_of_mem_XPlus (C : ConstructionData n m) {I : Finset (Fin n)} {x : BaseVertex m}
    {v : Fin n} (hv : v ∈ C.XPlus I x) : v ∈ C.X I x := by
  cases x with
  | inl r =>
      rcases (C.mem_XPlus_red).1 hv with ⟨hvI, hAdj, _⟩
      exact (C.mem_X_red).2 ⟨hvI, hAdj⟩
  | inr b =>
      rcases (C.mem_XPlus_blue).1 hv with ⟨hvI, hAdj, _⟩
      exact (C.mem_X_blue).2 ⟨hvI, hAdj⟩

theorem mem_I_of_mem_XPlus (C : ConstructionData n m) {I : Finset (Fin n)} {x : BaseVertex m}
    {v : Fin n} (hv : v ∈ C.XPlus I x) : v ∈ I :=
  C.mem_I_of_mem_X (C.mem_X_of_mem_XPlus hv)

theorem xCard_le_card_I (C : ConstructionData n m) (I : Finset (Fin n)) (x : BaseVertex m) :
    C.xCard I x ≤ I.card := by
  unfold xCard
  exact Finset.card_le_card (by
    intro v hv
    exact C.mem_I_of_mem_X hv)

theorem xPlusCard_le_xCard (C : ConstructionData n m) (I : Finset (Fin n)) (x : BaseVertex m) :
    C.xPlusCard I x ≤ C.xCard I x := by
  unfold xPlusCard xCard
  exact Finset.card_le_card (by
    intro v hv
    exact C.mem_X_of_mem_XPlus hv)

theorem xPlusCard_le_card_I (C : ConstructionData n m) (I : Finset (Fin n)) (x : BaseVertex m) :
    C.xPlusCard I x ≤ I.card :=
  (C.xPlusCard_le_xCard I x).trans (C.xCard_le_card_I I x)

theorem card_redProjectionImage_le_xCard (C : ConstructionData n m) (I : Finset (Fin n))
    (x : BaseVertex m) : (C.redProjectionImage I x).card ≤ C.xCard I x := by
  unfold redProjectionImage xCard
  exact Finset.card_image_le

theorem card_blueProjectionImage_le_xCard (C : ConstructionData n m) (I : Finset (Fin n))
    (x : BaseVertex m) : (C.blueProjectionImage I x).card ≤ C.xCard I x := by
  unfold blueProjectionImage xCard
  exact Finset.card_image_le

theorem redProjectionImage_card_le_card_I (C : ConstructionData n m) (I : Finset (Fin n))
    (x : BaseVertex m) : (C.redProjectionImage I x).card ≤ I.card :=
  (C.card_redProjectionImage_le_xCard I x).trans (C.xCard_le_card_I I x)

theorem blueProjectionImage_card_le_card_I (C : ConstructionData n m) (I : Finset (Fin n))
    (x : BaseVertex m) : (C.blueProjectionImage I x).card ≤ I.card :=
  (C.card_blueProjectionImage_le_xCard I x).trans (C.xCard_le_card_I I x)

theorem X_subset_univ (C : ConstructionData n m) {I : Finset (Fin n)} (x : BaseVertex m) :
    C.X I x ⊆ C.X Finset.univ x := by
  intro v hv
  cases x with
  | inl r =>
      rcases (C.mem_X_red).1 hv with ⟨-, hadj⟩
      exact (C.mem_X_red).2 ⟨by simp, hadj⟩
  | inr b =>
      rcases (C.mem_X_blue).1 hv with ⟨-, hadj⟩
      exact (C.mem_X_blue).2 ⟨by simp, hadj⟩

theorem redProjectionImage_subset_univ (C : ConstructionData n m) {I : Finset (Fin n)}
    (x : BaseVertex m) : C.redProjectionImage I x ⊆ C.redProjectionImage Finset.univ x := by
  intro r hr
  rcases Finset.mem_image.1 hr with ⟨v, hvX, rfl⟩
  exact Finset.mem_image.2 ⟨v, C.X_subset_univ x hvX, rfl⟩

theorem blueProjectionImage_subset_univ (C : ConstructionData n m) {I : Finset (Fin n)}
    (x : BaseVertex m) : C.blueProjectionImage I x ⊆ C.blueProjectionImage Finset.univ x := by
  intro b hb
  rcases Finset.mem_image.1 hb with ⟨v, hvX, rfl⟩
  exact Finset.mem_image.2 ⟨v, C.X_subset_univ x hvX, rfl⟩

theorem card_redProjectionImage_le_univ (C : ConstructionData n m) (I : Finset (Fin n))
    (x : BaseVertex m) :
    (C.redProjectionImage I x).card ≤ (C.redProjectionImage Finset.univ x).card :=
  Finset.card_le_card (C.redProjectionImage_subset_univ x)

theorem card_blueProjectionImage_le_univ (C : ConstructionData n m) (I : Finset (Fin n))
    (x : BaseVertex m) :
    (C.blueProjectionImage I x).card ≤ (C.blueProjectionImage Finset.univ x).card :=
  Finset.card_le_card (C.blueProjectionImage_subset_univ x)

theorem sum_card_le_card_biUnion_add_choose_mul_of_inter_bound {ι α : Type*}
    [DecidableEq α] (s : Finset ι) (F : ι → Finset α) {D : ℕ}
    (hinter : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (F a ∩ F b).card ≤ D) :
    ∑ a ∈ s, (F a).card ≤ (s.biUnion F).card + s.card.choose 2 * D := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hs : ∀ b ∈ s, ∀ c ∈ s, b ≠ c → (F b ∩ F c).card ≤ D := by
        intro b hb c hc hbc
        exact hinter b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hbc
      have ih' := ih hs
      have hInterSum : (F a ∩ s.biUnion F).card ≤ ∑ x ∈ s, (F a ∩ F x).card := by
        rw [Finset.inter_biUnion]
        exact Finset.card_biUnion_le
      have hInterBound : (F a ∩ s.biUnion F).card ≤ s.card * D := by
        refine hInterSum.trans ?_
        calc
          ∑ x ∈ s, (F a ∩ F x).card ≤ ∑ _x ∈ s, D := by
            refine Finset.sum_le_sum ?_
            intro x hx
            exact hinter a (by simp) x (Finset.mem_insert_of_mem hx) (by
              intro hax
              subst hax
              exact ha hx)
          _ = s.card * D := by
            simp
      have hCard :
          (F a).card + (s.biUnion F).card ≤
            ((insert a s).biUnion F).card + s.card * D := by
        rw [Finset.biUnion_insert, ← Finset.card_union_add_card_inter]
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hInterBound ((F a ∪ s.biUnion F).card)
      have hStep : (F a).card + ∑ x ∈ s, (F x).card ≤
          ((insert a s).biUnion F).card + s.card * D + s.card.choose 2 * D := by
        calc
          (F a).card + ∑ x ∈ s, (F x).card ≤
              (F a).card + ((s.biUnion F).card + s.card.choose 2 * D) := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left ih' ((F a).card)
          _ = ((F a).card + (s.biUnion F).card) + s.card.choose 2 * D := by
            ac_rfl
          _ ≤ (((insert a s).biUnion F).card + s.card * D) + s.card.choose 2 * D := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hCard (s.card.choose 2 * D)
          _ = ((insert a s).biUnion F).card + s.card * D + s.card.choose 2 * D := by
            ac_rfl
      have hchoose : (insert a s).card.choose 2 = s.card.choose 2 + s.card := by
        simp [ha, Nat.choose_succ_succ', Nat.add_comm]
      calc
        ∑ x ∈ insert a s, (F x).card = (F a).card + ∑ x ∈ s, (F x).card := by
          simp [ha]
        _ ≤ ((insert a s).biUnion F).card + s.card * D + s.card.choose 2 * D := hStep
        _ = ((insert a s).biUnion F).card + (s.card * D + s.card.choose 2 * D) := by
          ac_rfl
        _ = ((insert a s).biUnion F).card + (s.card + s.card.choose 2) * D := by
          rw [Nat.add_mul]
        _ = ((insert a s).biUnion F).card + (insert a s).card.choose 2 * D := by
          rw [Nat.add_comm s.card (s.card.choose 2), hchoose]

theorem card_biUnion_X_le_card_I (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : (A.biUnion fun x => C.X I x).card ≤ I.card := by
  refine Finset.card_le_card ?_
  intro v hv
  rcases Finset.mem_biUnion.1 hv with ⟨x, -, hvX⟩
  exact C.mem_I_of_mem_X hvX

theorem redProjectionUnion_eq_redImage_biUnion_X (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) :
    C.redProjectionUnion I A = C.redImage (A.biUnion fun x => C.X I x) := by
  ext r
  constructor
  · intro hr
    rcases Finset.mem_biUnion.1 hr with ⟨x, hxA, hrx⟩
    rcases Finset.mem_image.1 hrx with ⟨v, hvX, hvr⟩
    exact (C.mem_redImage).2 ⟨v, Finset.mem_biUnion.2 ⟨x, hxA, hvX⟩, hvr⟩
  · intro hr
    rcases (C.mem_redImage).1 hr with ⟨v, hvUnion, hvr⟩
    rcases Finset.mem_biUnion.1 hvUnion with ⟨x, hxA, hvX⟩
    exact Finset.mem_biUnion.2 ⟨x, hxA, Finset.mem_image.2 ⟨v, hvX, hvr⟩⟩

theorem blueProjectionUnion_eq_blueImage_biUnion_X (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.blueProjectionUnion I A = C.blueImage (A.biUnion fun x => C.X I x) := by
  ext b
  constructor
  · intro hb
    rcases Finset.mem_biUnion.1 hb with ⟨x, hxA, hbx⟩
    rcases Finset.mem_image.1 hbx with ⟨v, hvX, hvb⟩
    exact (C.mem_blueImage).2 ⟨v, Finset.mem_biUnion.2 ⟨x, hxA, hvX⟩, hvb⟩
  · intro hb
    rcases (C.mem_blueImage).1 hb with ⟨v, hvUnion, hvb⟩
    rcases Finset.mem_biUnion.1 hvUnion with ⟨x, hxA, hvX⟩
    exact Finset.mem_biUnion.2 ⟨x, hxA, Finset.mem_image.2 ⟨v, hvX, hvb⟩⟩

theorem card_redProjectionUnion_le_card_biUnion_X (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.redProjectionUnion I A).card ≤ (A.biUnion fun x => C.X I x).card := by
  rw [C.redProjectionUnion_eq_redImage_biUnion_X I A]
  simpa [ConstructionData.redImage] using
    (Finset.card_image_le (s := A.biUnion fun x => C.X I x) (f := C.redProj))

theorem card_blueProjectionUnion_le_card_biUnion_X (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.blueProjectionUnion I A).card ≤ (A.biUnion fun x => C.X I x).card := by
  rw [C.blueProjectionUnion_eq_blueImage_biUnion_X I A]
  simpa [ConstructionData.blueImage] using
    (Finset.card_image_le (s := A.biUnion fun x => C.X I x) (f := C.blueProj))

theorem card_redImage_le_card_redImage_of_subset_add_card_sdiff (C : ConstructionData n m)
    {I U : Finset (Fin n)} (hU : U ⊆ I) :
    (C.redImage I).card ≤ (C.redImage U).card + (I \ U).card := by
  calc
    (C.redImage I).card = (C.redImage (U ∪ (I \ U))).card := by
      rw [Finset.union_sdiff_of_subset hU]
    _ ≤ (C.redImage U).card + (C.redImage (I \ U)).card := by
      rw [ConstructionData.redImage, Finset.image_union]
      exact Finset.card_union_le _ _
    _ ≤ (C.redImage U).card + (I \ U).card := by
      gcongr
      exact Finset.card_image_le

theorem card_blueImage_le_card_blueImage_of_subset_add_card_sdiff (C : ConstructionData n m)
    {I U : Finset (Fin n)} (hU : U ⊆ I) :
    (C.blueImage I).card ≤ (C.blueImage U).card + (I \ U).card := by
  calc
    (C.blueImage I).card = (C.blueImage (U ∪ (I \ U))).card := by
      rw [Finset.union_sdiff_of_subset hU]
    _ ≤ (C.blueImage U).card + (C.blueImage (I \ U)).card := by
      rw [ConstructionData.blueImage, Finset.image_union]
      exact Finset.card_union_le _ _
    _ ≤ (C.blueImage U).card + (I \ U).card := by
      gcongr
      exact Finset.card_image_le

theorem card_subset_le_card_sub_card_redImage_add_card_redImage (C : ConstructionData n m)
    {I U : Finset (Fin n)} (hU : U ⊆ I) :
    U.card ≤ I.card - (C.redImage I).card + (C.redImage U).card := by
  have hImage := C.card_redImage_le_card_redImage_of_subset_add_card_sdiff hU
  have hCard : (I \ U).card + U.card = I.card := Finset.card_sdiff_add_card_eq_card hU
  omega

theorem card_subset_le_card_sub_card_blueImage_add_card_blueImage (C : ConstructionData n m)
    {I U : Finset (Fin n)} (hU : U ⊆ I) :
    U.card ≤ I.card - (C.blueImage I).card + (C.blueImage U).card := by
  have hImage := C.card_blueImage_le_card_blueImage_of_subset_add_card_sdiff hU
  have hCard : (I \ U).card + U.card = I.card := Finset.card_sdiff_add_card_eq_card hU
  omega

theorem card_biUnion_X_le_card_I_sub_card_redImage_add_redProjectionUnion
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (A.biUnion fun x => C.X I x).card ≤
      I.card - (C.redImage I).card + (C.redProjectionUnion I A).card := by
  have hSubset : (A.biUnion fun x => C.X I x) ⊆ I := by
    intro v hv
    rcases Finset.mem_biUnion.1 hv with ⟨x, -, hvX⟩
    exact C.mem_I_of_mem_X hvX
  simpa [C.redProjectionUnion_eq_redImage_biUnion_X I A] using
    (C.card_subset_le_card_sub_card_redImage_add_card_redImage hSubset)

theorem card_biUnion_X_le_card_I_sub_card_blueImage_add_blueProjectionUnion
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (A.biUnion fun x => C.X I x).card ≤
      I.card - (C.blueImage I).card + (C.blueProjectionUnion I A).card := by
  have hSubset : (A.biUnion fun x => C.X I x) ⊆ I := by
    intro v hv
    rcases Finset.mem_biUnion.1 hv with ⟨x, -, hvX⟩
    exact C.mem_I_of_mem_X hvX
  simpa [C.blueProjectionUnion_eq_blueImage_biUnion_X I A] using
    (C.card_subset_le_card_sub_card_blueImage_add_card_blueImage hSubset)

theorem card_blueProjectionUnion_le_card_I_sub_card_redImage_add_redProjectionUnion
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.blueProjectionUnion I A).card ≤
      I.card - (C.redImage I).card + (C.redProjectionUnion I A).card := by
  calc
    (C.blueProjectionUnion I A).card ≤ (A.biUnion fun x => C.X I x).card :=
      C.card_blueProjectionUnion_le_card_biUnion_X I A
    _ ≤ I.card - (C.redImage I).card + (C.redProjectionUnion I A).card :=
      C.card_biUnion_X_le_card_I_sub_card_redImage_add_redProjectionUnion I A

theorem card_redProjectionUnion_le_card_I_sub_card_blueImage_add_blueProjectionUnion
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.redProjectionUnion I A).card ≤
      I.card - (C.blueImage I).card + (C.blueProjectionUnion I A).card := by
  calc
    (C.redProjectionUnion I A).card ≤ (A.biUnion fun x => C.X I x).card :=
      C.card_redProjectionUnion_le_card_biUnion_X I A
    _ ≤ I.card - (C.blueImage I).card + (C.blueProjectionUnion I A).card :=
      C.card_biUnion_X_le_card_I_sub_card_blueImage_add_blueProjectionUnion I A

theorem partWeight_le_card_I_add_choose_mul_of_pairwise_inter_bound (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {D : ℕ}
    (hinter : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → (C.X I x ∩ C.X I y).card ≤ D) :
    C.partWeight I A ≤ I.card + A.card.choose 2 * D := by
  unfold partWeight
  exact (sum_card_le_card_biUnion_add_choose_mul_of_inter_bound A (fun x => C.X I x) hinter).trans
    (Nat.add_le_add_right (C.card_biUnion_X_le_card_I I A) _)

theorem xInter_card_le_of_goodEventD (C : ConstructionData n m) {fiberBound degreeBound
    codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {x y : BaseVertex m} (hxy : x ≠ y) :
    (C.X I x ∩ C.X I y).card ≤ codegreeBound := by
  refine (Finset.card_le_card ?_).trans (hD.xInterBound x y hxy)
  intro v hv
  simp only [Finset.mem_inter] at hv ⊢
  exact ⟨C.X_subset_univ x hv.1, C.X_subset_univ y hv.2⟩

theorem blueProjectionInter_card_le_of_goodEventD (C : ConstructionData n m) {fiberBound
    degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {r r' : Fin m} (hrr' : r ≠ r') :
    (C.blueProjectionImage I (Sum.inl r) ∩ C.blueProjectionImage I (Sum.inl r')).card ≤
      projCodegreeBound := by
  refine (Finset.card_le_card ?_).trans (hD.blueProjectionInterBound r r' hrr')
  intro b hb
  simp only [Finset.mem_inter] at hb ⊢
  exact ⟨C.blueProjectionImage_subset_univ (Sum.inl r) hb.1,
    C.blueProjectionImage_subset_univ (Sum.inl r') hb.2⟩

theorem redProjectionInter_card_le_of_goodEventD (C : ConstructionData n m) {fiberBound
    degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {b b' : Fin m} (hbb' : b ≠ b') :
    (C.redProjectionImage I (Sum.inr b) ∩ C.redProjectionImage I (Sum.inr b')).card ≤
      projCodegreeBound := by
  refine (Finset.card_le_card ?_).trans (hD.redProjectionInterBound b b' hbb')
  intro r hr
  simp only [Finset.mem_inter] at hr ⊢
  exact ⟨C.redProjectionImage_subset_univ (Sum.inr b) hr.1,
    C.redProjectionImage_subset_univ (Sum.inr b') hr.2⟩

theorem partWeight_le_card_I_add_choose_mul_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.partWeight I A ≤ I.card + A.card.choose 2 * codegreeBound := by
  apply C.partWeight_le_card_I_add_choose_mul_of_pairwise_inter_bound I A
  intro x hx y hy hxy
  exact C.xInter_card_le_of_goodEventD hD I hxy

theorem card_redProjectionUnion_le_redProjectionWeight (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.redProjectionUnion I A).card ≤ C.redProjectionWeight I A := by
  unfold redProjectionUnion redProjectionWeight
  exact Finset.card_biUnion_le

theorem card_blueProjectionUnion_le_blueProjectionWeight (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.blueProjectionUnion I A).card ≤ C.blueProjectionWeight I A := by
  unfold blueProjectionUnion blueProjectionWeight
  exact Finset.card_biUnion_le

theorem redProjectionWeight_le_card_redProjectionUnion_add_choose_mul_of_pairwise_inter_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {D : ℕ}
    (hinter :
      ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        (C.redProjectionImage I x ∩ C.redProjectionImage I y).card ≤ D) :
    C.redProjectionWeight I A ≤
      (C.redProjectionUnion I A).card + A.card.choose 2 * D := by
  unfold redProjectionWeight redProjectionUnion
  exact sum_card_le_card_biUnion_add_choose_mul_of_inter_bound A
    (fun x => C.redProjectionImage I x) hinter

theorem blueProjectionWeight_le_card_blueProjectionUnion_add_choose_mul_of_pairwise_inter_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {D : ℕ}
    (hinter :
      ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        (C.blueProjectionImage I x ∩ C.blueProjectionImage I y).card ≤ D) :
    C.blueProjectionWeight I A ≤
      (C.blueProjectionUnion I A).card + A.card.choose 2 * D := by
  unfold blueProjectionWeight blueProjectionUnion
  exact sum_card_le_card_biUnion_add_choose_mul_of_inter_bound A
    (fun x => C.blueProjectionImage I x) hinter

theorem lowerNat_mul_card_le_partWeight_of_le_xCard (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {lower : ℕ}
    (hlower : ∀ x ∈ A, lower ≤ C.xCard I x) :
    A.card * lower ≤ C.partWeight I A := by
  unfold partWeight
  calc
    A.card * lower = ∑ _x ∈ A, lower := by
      simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ A, C.xCard I x := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact hlower x hx

theorem card_lt_of_card_lt_mul_sub_choose_mul_of_pairwise_inter_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m))
    {lower codegreeBound witnessSize : ℕ}
    (hlower : ∀ x ∈ A, lower ≤ C.xCard I x)
    (hinter : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → (C.X I x ∩ C.X I y).card ≤ codegreeBound)
    (hwitness :
      I.card < witnessSize * lower - witnessSize.choose 2 * codegreeBound) :
    A.card < witnessSize := by
  by_contra hA
  have hge : witnessSize ≤ A.card := Nat.not_lt.1 hA
  rcases Finset.exists_subset_card_eq hge with ⟨B, hBA, hBcard⟩
  have hLowerB : ∀ x ∈ B, lower ≤ C.xCard I x := by
    intro x hx
    exact hlower x (hBA hx)
  have hInterB : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → (C.X I x ∩ C.X I y).card ≤ codegreeBound := by
    intro x hx y hy hxy
    exact hinter x (hBA hx) y (hBA hy) hxy
  have hWeightLower : witnessSize * lower ≤ C.partWeight I B := by
    simpa [hBcard] using C.lowerNat_mul_card_le_partWeight_of_le_xCard I B hLowerB
  have hWeightUpper :
      C.partWeight I B ≤ I.card + witnessSize.choose 2 * codegreeBound := by
    simpa [hBcard] using
      C.partWeight_le_card_I_add_choose_mul_of_pairwise_inter_bound I B hInterB
  have hmul : witnessSize * lower ≤ I.card + witnessSize.choose 2 * codegreeBound :=
    hWeightLower.trans hWeightUpper
  have hbound : witnessSize * lower - witnessSize.choose 2 * codegreeBound ≤ I.card := by
    omega
  exact not_lt_of_ge hbound hwitness

theorem card_lt_of_card_lt_mul_sub_choose_mul_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {lower witnessSize : ℕ}
    (hlower : ∀ x ∈ A, lower ≤ C.xCard I x)
    (hwitness :
      I.card < witnessSize * lower - witnessSize.choose 2 * codegreeBound) :
    A.card < witnessSize := by
  apply C.card_lt_of_card_lt_mul_sub_choose_mul_of_pairwise_inter_bound I A hlower
  · intro x hx y hy hxy
    exact C.xInter_card_le_of_goodEventD hD I hxy
  · exact hwitness

theorem partWeight_le_card_I_add_choose_mul_of_goodEventD_of_card_le (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {bound : ℕ} (hA : A.card ≤ bound) :
    C.partWeight I A ≤ I.card + bound.choose 2 * codegreeBound := by
  have hchoose : A.card.choose 2 * codegreeBound ≤ bound.choose 2 * codegreeBound := by
    exact Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hA)
  exact (C.partWeight_le_card_I_add_choose_mul_of_goodEventD hD I A).trans
    (Nat.add_le_add_left hchoose _)

theorem LPart_card_lt_of_goodEventD_of_lt (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ} {witnessSize : ℕ}
    (hwitness :
      I.card < witnessSize * ⌈Twobites.paperT2 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    (C.LPart I ε).card < witnessSize := by
  apply C.card_lt_of_card_lt_mul_sub_choose_mul_of_goodEventD hD I (C.LPart I ε)
  · intro x hx
    exact (Nat.ceil_le).2 (le_of_lt ((C.mem_LPart.1 hx).1))
  · exact hwitness

theorem LPart_card_le_of_goodEventD_of_paperWitness (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT2 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    (C.LPart I ε).card ≤ witnessSize := by
  exact Nat.le_of_lt (C.LPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hwitness))

theorem cast_LPart_card_le_of_goodEventD_of_paperWitness (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT2 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    ((C.LPart I ε).card : ℝ) ≤ (witnessSize : ℝ) := by
  exact_mod_cast C.LPart_card_le_of_goodEventD_of_paperWitness hD I hI hwitness

theorem LPart_card_le_paperLargeWitnessNat_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT2 : 2 < Twobites.paperT2 ε n)
    (hchoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n) :
    (C.LPart I ε).card ≤ Twobites.paperLargeWitnessNat κ ε n := by
  have hwitness :
      Twobites.paperKNat κ n <
        Twobites.paperLargeWitnessNat κ ε n * ⌈Twobites.paperT2 ε n⌉₊ -
          (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound := by
    exact
      Twobites.paperKNat_lt_mul_ceil_paperT2_sub_choose_mul_of_two_mul_lt
        (Twobites.two_mul_paperKNat_lt_paperLargeWitnessNat_mul_ceil_paperT2 hκ hT2)
        hchoose
  exact C.LPart_card_le_of_goodEventD_of_paperWitness hD I hI hwitness

theorem cast_LPart_card_le_paperLargeWitnessNat_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT2 : 2 < Twobites.paperT2 ε n)
    (hchoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n) :
    ((C.LPart I ε).card : ℝ) ≤ (Twobites.paperLargeWitnessNat κ ε n : ℝ) := by
  exact_mod_cast C.LPart_card_le_paperLargeWitnessNat_of_goodEventD hD I hI hκ hT2 hchoose

theorem MPart_card_lt_of_goodEventD_of_lt (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ} {witnessSize : ℕ}
    (hwitness :
      I.card < witnessSize * ⌈Twobites.paperT3 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    (C.MPart I ε).card < witnessSize := by
  apply C.card_lt_of_card_lt_mul_sub_choose_mul_of_goodEventD hD I (C.MPart I ε)
  · intro x hx
    exact (Nat.ceil_le).2 (le_of_lt ((C.mem_MPart.1 hx).1))
  · exact hwitness

theorem HPart_card_lt_of_goodEventD_of_lt (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {witnessSize : ℕ}
    (hwitness :
      I.card < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    (C.HPart I).card < witnessSize := by
  apply C.card_lt_of_card_lt_mul_sub_choose_mul_of_goodEventD hD I (C.HPart I)
  · intro x hx
    exact (Nat.ceil_le).2 (le_of_lt ((C.mem_HPart.1 hx).1))
  · exact hwitness

theorem HPart_card_lt_mul_paperK_div_paperT1_of_goodEventD_of_lt_of_le
    (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ B : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hbound :
      (witnessSize : ℝ) ≤ B * (Twobites.paperK κ n / Twobites.paperT1 n)) :
    ((C.HPart I).card : ℝ) < B * (Twobites.paperK κ n / Twobites.paperT1 n) := by
  have hcard : (C.HPart I).card < witnessSize :=
    C.HPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hwitness)
  have hcard' : ((C.HPart I).card : ℝ) < witnessSize := by
    exact_mod_cast hcard
  exact hcard'.trans_le hbound

theorem HPart_card_lt_mul_mul_loglog_of_goodEventD_of_lt_of_le
    (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ B : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hbound :
      (witnessSize : ℝ) ≤ B * (Twobites.paperK κ n / Twobites.paperT1 n))
    (hn : 1 < n) (hloglog : 0 < Real.log (Real.log (n : ℝ))) :
    ((C.HPart I).card : ℝ) < B * κ * Real.log (Real.log (n : ℝ)) := by
  have hcard :
      ((C.HPart I).card : ℝ) < B * (Twobites.paperK κ n / Twobites.paperT1 n) :=
    C.HPart_card_lt_mul_paperK_div_paperT1_of_goodEventD_of_lt_of_le hD I hI hwitness hbound
  rw [Twobites.paperK_div_paperT1_eq_mul_loglog hn hloglog] at hcard
  simpa [mul_assoc] using hcard

theorem HPart_card_lt_mul_paperK_div_paperT1_of_goodEventD_of_two_mul_lt_of_choose_le
    (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ B : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (htwo : 2 * Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊)
    (hchoose : witnessSize.choose 2 * codegreeBound ≤ Twobites.paperKNat κ n)
    (hbound :
      (witnessSize : ℝ) ≤ B * (Twobites.paperK κ n / Twobites.paperT1 n)) :
    ((C.HPart I).card : ℝ) < B * (Twobites.paperK κ n / Twobites.paperT1 n) := by
  have hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound :=
    Twobites.paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_of_two_mul_lt htwo hchoose
  exact C.HPart_card_lt_mul_paperK_div_paperT1_of_goodEventD_of_lt_of_le hD I hI hwitness hbound

theorem HPart_card_lt_mul_mul_loglog_of_goodEventD_of_two_mul_lt_of_choose_le
    (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ B : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (htwo : 2 * Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊)
    (hchoose : witnessSize.choose 2 * codegreeBound ≤ Twobites.paperKNat κ n)
    (hbound :
      (witnessSize : ℝ) ≤ B * (Twobites.paperK κ n / Twobites.paperT1 n))
    (hn : 1 < n) (hloglog : 0 < Real.log (Real.log (n : ℝ))) :
    ((C.HPart I).card : ℝ) < B * κ * Real.log (Real.log (n : ℝ)) := by
  have hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound :=
    Twobites.paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_of_two_mul_lt htwo hchoose
  exact
    C.HPart_card_lt_mul_mul_loglog_of_goodEventD_of_lt_of_le hD I hI hwitness hbound hn
      hloglog

theorem HPart_card_lt_two_mul_paperK_div_paperT1_add_two_of_goodEventD_of_paperHugeWitness
    (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT1 : 2 < Twobites.paperT1 n)
    (hchoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n) :
    ((C.HPart I).card : ℝ) < 2 * (Twobites.paperK κ n / Twobites.paperT1 n) + 2 := by
  have htwo :
      2 * Twobites.paperKNat κ n <
        Twobites.paperHugeWitnessNat κ n * ⌈Twobites.paperT1 n⌉₊ :=
    Twobites.two_mul_paperKNat_lt_paperHugeWitnessNat_mul_ceil_paperT1 hκ hT1
  have hbound :
      (Twobites.paperHugeWitnessNat κ n : ℝ) ≤
        2 * (Twobites.paperK κ n / Twobites.paperT1 n) + 2 := by
    exact Twobites.paperHugeWitnessNat_le_two_mul_paperK_div_paperT1_add_two hκ (by linarith)
  have hcard :
      ((C.HPart I).card : ℝ) < (Twobites.paperHugeWitnessNat κ n : ℝ) :=
    by
      have hwitness :
          Twobites.paperKNat κ n <
            Twobites.paperHugeWitnessNat κ n * ⌈Twobites.paperT1 n⌉₊ -
              (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound :=
        Twobites.paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_of_two_mul_lt htwo hchoose
      have hnat :
          (C.HPart I).card < Twobites.paperHugeWitnessNat κ n :=
        C.HPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hwitness)
      exact_mod_cast hnat
  exact hcard.trans_le hbound

theorem paperT1_lt_xCard_of_mem_HPart (C : ConstructionData n m) {I : Finset (Fin n)}
    {x : BaseVertex m} (hx : x ∈ C.HPart I) : Twobites.paperT1 n < (C.xCard I x : ℝ) :=
  (C.mem_HPart.1 hx).1

theorem xCard_le_card_I_of_mem_HPart (C : ConstructionData n m) {I : Finset (Fin n)}
    {x : BaseVertex m} (hx : x ∈ C.HPart I) : (C.xCard I x : ℝ) ≤ (I.card : ℝ) :=
  (C.mem_HPart.1 hx).2

theorem paperT2_lt_xCard_of_mem_LPart (C : ConstructionData n m) {I : Finset (Fin n)}
    {ε : ℝ} {x : BaseVertex m} (hx : x ∈ C.LPart I ε) :
    Twobites.paperT2 ε n < (C.xCard I x : ℝ) :=
  (C.mem_LPart.1 hx).1

theorem xCard_le_paperT1_of_mem_LPart (C : ConstructionData n m) {I : Finset (Fin n)}
    {ε : ℝ} {x : BaseVertex m} (hx : x ∈ C.LPart I ε) :
    (C.xCard I x : ℝ) ≤ Twobites.paperT1 n :=
  (C.mem_LPart.1 hx).2

theorem paperT3_lt_xCard_of_mem_MPart (C : ConstructionData n m) {I : Finset (Fin n)}
    {ε : ℝ} {x : BaseVertex m} (hx : x ∈ C.MPart I ε) :
    Twobites.paperT3 ε n < (C.xCard I x : ℝ) :=
  (C.mem_MPart.1 hx).1

theorem xCard_le_paperT2_of_mem_MPart (C : ConstructionData n m) {I : Finset (Fin n)}
    {ε : ℝ} {x : BaseVertex m} (hx : x ∈ C.MPart I ε) :
    (C.xCard I x : ℝ) ≤ Twobites.paperT2 ε n :=
  (C.mem_MPart.1 hx).2

theorem xCard_le_paperT3_of_mem_SPart (C : ConstructionData n m) {I : Finset (Fin n)}
    {ε : ℝ} {x : BaseVertex m} (hx : x ∈ C.SPart I ε) :
    (C.xCard I x : ℝ) ≤ Twobites.paperT3 ε n :=
  (C.mem_SPart.1 hx)

theorem ceil_paperT1_le_xCard_of_mem_HPart (C : ConstructionData n m) {I : Finset (Fin n)}
    {x : BaseVertex m} (hx : x ∈ C.HPart I) : ⌈Twobites.paperT1 n⌉₊ ≤ C.xCard I x := by
  exact (Nat.ceil_le).2 (le_of_lt (C.paperT1_lt_xCard_of_mem_HPart hx))

theorem ceil_paperT2_le_xCard_of_mem_LPart (C : ConstructionData n m) {I : Finset (Fin n)}
    {ε : ℝ} {x : BaseVertex m} (hx : x ∈ C.LPart I ε) :
    ⌈Twobites.paperT2 ε n⌉₊ ≤ C.xCard I x := by
  exact (Nat.ceil_le).2 (le_of_lt (C.paperT2_lt_xCard_of_mem_LPart hx))

theorem ceil_paperT3_le_xCard_of_mem_MPart (C : ConstructionData n m) {I : Finset (Fin n)}
    {ε : ℝ} {x : BaseVertex m} (hx : x ∈ C.MPart I ε) :
    ⌈Twobites.paperT3 ε n⌉₊ ≤ C.xCard I x := by
  exact (Nat.ceil_le).2 (le_of_lt (C.paperT3_lt_xCard_of_mem_MPart hx))

theorem mem_HPart_or_mem_LPart_or_mem_MPart_or_mem_SPart (C : ConstructionData n m)
    (I : Finset (Fin n)) (ε : ℝ) (x : BaseVertex m) :
    x ∈ C.HPart I ∨ x ∈ C.LPart I ε ∨ x ∈ C.MPart I ε ∨ x ∈ C.SPart I ε := by
  by_cases hs : (C.xCard I x : ℝ) ≤ Twobites.paperT3 ε n
  · exact Or.inr <| Or.inr <| Or.inr <| (C.mem_SPart).2 hs
  · have hs' : Twobites.paperT3 ε n < (C.xCard I x : ℝ) := lt_of_not_ge hs
    by_cases hm : (C.xCard I x : ℝ) ≤ Twobites.paperT2 ε n
    · exact Or.inr <| Or.inr <| Or.inl <| (C.mem_MPart).2 ⟨hs', hm⟩
    · have hm' : Twobites.paperT2 ε n < (C.xCard I x : ℝ) := lt_of_not_ge hm
      by_cases hl : (C.xCard I x : ℝ) ≤ Twobites.paperT1 n
      · exact Or.inr <| Or.inl <| (C.mem_LPart).2 ⟨hm', hl⟩
      · have hl' : Twobites.paperT1 n < (C.xCard I x : ℝ) := lt_of_not_ge hl
        exact Or.inl <| (C.mem_HPart).2 ⟨hl', by exact_mod_cast C.xCard_le_card_I I x⟩

theorem disjoint_HPart_LPart (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) :
    Disjoint (C.HPart I) (C.LPart I ε) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxH hxL
  have hH := C.paperT1_lt_xCard_of_mem_HPart hxH
  have hL := C.xCard_le_paperT1_of_mem_LPart hxL
  linarith

theorem disjoint_LPart_MPart (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) :
    Disjoint (C.LPart I ε) (C.MPart I ε) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxL hxM
  have hL := C.paperT2_lt_xCard_of_mem_LPart hxL
  have hM := C.xCard_le_paperT2_of_mem_MPart hxM
  linarith

theorem disjoint_MPart_SPart (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) :
    Disjoint (C.MPart I ε) (C.SPart I ε) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxM hxS
  have hM := C.paperT3_lt_xCard_of_mem_MPart hxM
  have hS := C.xCard_le_paperT3_of_mem_SPart hxS
  linarith

theorem disjoint_HPart_MPart (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n) :
    Disjoint (C.HPart I) (C.MPart I ε) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxH hxM
  have hH := C.paperT1_lt_xCard_of_mem_HPart hxH
  have hM := C.xCard_le_paperT2_of_mem_MPart hxM
  linarith

theorem disjoint_LPart_SPart (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    Disjoint (C.LPart I ε) (C.SPart I ε) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxL hxS
  have hL := C.paperT2_lt_xCard_of_mem_LPart hxL
  have hS := C.xCard_le_paperT3_of_mem_SPart hxS
  linarith

theorem disjoint_HPart_SPart (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht31 : Twobites.paperT3 ε n ≤ Twobites.paperT1 n) :
    Disjoint (C.HPart I) (C.SPart I ε) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxH hxS
  have hH := C.paperT1_lt_xCard_of_mem_HPart hxH
  have hS := C.xCard_le_paperT3_of_mem_SPart hxS
  linarith

theorem section4F2_subset_LPart_union_HPart_of_log_pos_of_paperT3_le_paperT2
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hlog : 0 < Real.log (n : ℝ)) (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    C.section4F2 I ε ⊆ C.LPart I ε ∪ C.HPart I := by
  intro x hx
  have hxgt : Twobites.paperT2 ε n < (C.xCard I x : ℝ) := by
    cases x with
    | inl r =>
        have hcount : Twobites.paperT2 ε n / Real.log (n : ℝ) <
            (((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ) :=
          (C.mem_section4F2.1 hx).2
        have hmul' :
            Twobites.paperT2 ε n <
              (((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ) *
                Real.log (n : ℝ) := (div_lt_iff₀ hlog).1 hcount
        have hmul :
            Twobites.paperT2 ε n <
              Real.log (n : ℝ) *
                (((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ) := by
          simpa [mul_comm] using hmul'
        exact lt_of_lt_of_le hmul (C.xCard_red_ge_log_mul_section4F1_neighbor_card I r)
    | inr b =>
        have hcount : Twobites.paperT2 ε n / Real.log (n : ℝ) <
            (((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ) :=
          (C.mem_section4F2.1 hx).2
        have hmul' :
            Twobites.paperT2 ε n <
              (((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ) *
                Real.log (n : ℝ) := (div_lt_iff₀ hlog).1 hcount
        have hmul :
            Twobites.paperT2 ε n <
              Real.log (n : ℝ) *
                (((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ) := by
          simpa [mul_comm] using hmul'
        exact lt_of_lt_of_le hmul (C.xCard_blue_ge_log_mul_section4F1_neighbor_card I b)
  rcases C.mem_HPart_or_mem_LPart_or_mem_MPart_or_mem_SPart I ε x with hH | hL | hM | hS
  · exact Finset.mem_union.2 (Or.inr hH)
  · exact Finset.mem_union.2 (Or.inl hL)
  · exfalso
    have hMle := C.xCard_le_paperT2_of_mem_MPart hM
    linarith
  · exfalso
    have hSle := C.xCard_le_paperT3_of_mem_SPart hS
    linarith

theorem section4F2_card_le_card_LPart_union_HPart_of_log_pos_of_paperT3_le_paperT2
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hlog : 0 < Real.log (n : ℝ)) (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    (C.section4F2 I ε).card ≤ (C.LPart I ε ∪ C.HPart I).card := by
  exact Finset.card_le_card
    (C.section4F2_subset_LPart_union_HPart_of_log_pos_of_paperT3_le_paperT2 I hlog ht32)

theorem baseFiber_card_le_log_of_mem_baseImage_of_not_mem_section4F1
    (C : ConstructionData n m) {I : Finset (Fin n)} {x : BaseVertex m}
    (hxBase : x ∈ C.baseImage I) (hxF1 : x ∉ C.section4F1 I) :
    (((C.baseFiber x ∩ I).card : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
  by_contra hgt
  exact hxF1 ((C.mem_section4F1.2 ⟨hxBase, lt_of_not_ge hgt⟩))

theorem section4F1_neighbor_card_le_paperT2_div_log_of_mem_baseImage_of_not_mem_section4F2
    (C : ConstructionData n m) {I : Finset (Fin n)} {x : BaseVertex m} {ε : ℝ}
    (hxBase : x ∈ C.baseImage I) (hxF2 : x ∉ C.section4F2 I ε) :
    ((((C.baseNeighborSet x ∩ C.section4F1 I).card : ℕ) : ℝ)) ≤
      Twobites.paperT2 ε n / Real.log (n : ℝ) := by
  by_contra hgt
  exact hxF2 ((C.mem_section4F2.2 ⟨hxBase, lt_of_not_ge hgt⟩))

theorem xCard_red_le_fiberBound_mul_section4F1_neighbor_card_add_log_mul_degreeBound_of_goodEventD
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (r : Fin m) :
    (C.xCard I (Sum.inl r) : ℝ) ≤
      (fiberBound : ℝ) *
          ((((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ)) +
        Real.log (n : ℝ) * degreeBound := by
  classical
  let A : Finset (Fin m) := C.redProjectionImage I (Sum.inl r)
  let A₁ : Finset (Fin m) := A.filter fun r' => Sum.inl r' ∈ C.section4F1 I
  let A₂ : Finset (Fin m) := A.filter fun r' => Sum.inl r' ∉ C.section4F1 I
  have hsplit :
      ∑ r' ∈ A, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) =
        ∑ r' ∈ A₁, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) +
          ∑ r' ∈ A₂, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) := by
    simpa [A₁, A₂, A] using
      (Finset.sum_filter_add_sum_filter_not A
        (fun r' => Sum.inl r' ∈ C.section4F1 I)
        (fun r' => (((C.redFiber r' ∩ I).card : ℕ) : ℝ))).symm
  have hA₁card :
      ((A₁.card : ℕ) : ℝ) =
        ((((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ)) := by
    have hA₁cardNat : A₁.card = (C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card := by
      calc
        A₁.card = (A₁.image fun r' : Fin m => (Sum.inl r' : BaseVertex m)).card := by
          symm
          exact Finset.card_image_of_injective _ (by
            intro a b hab
            exact Sum.inl.inj hab)
        _ = (C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card := by
          rw [C.redProjectionImage_filter_section4F1_image_inl_eq_baseNeighborSet_inter_section4F1
            I r]
    exact_mod_cast hA₁cardNat
  have hsumA₁ :
      ∑ r' ∈ A₁, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) ≤
        (fiberBound : ℝ) * (A₁.card : ℝ) := by
    calc
      ∑ r' ∈ A₁, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) ≤
          ∑ _r' ∈ A₁, (fiberBound : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro r' hr'
        have hcard : (C.redFiber r' ∩ I).card ≤ fiberBound := by
          exact (Finset.card_le_card (by
            intro v hv
            exact (Finset.mem_inter.1 hv).1)).trans (hD.redFiberBound r')
        exact_mod_cast hcard
      _ = (fiberBound : ℝ) * (A₁.card : ℝ) := by
        simp [mul_comm]
  have hsumA₂ :
      ∑ r' ∈ A₂, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) ≤
        Real.log (n : ℝ) * (A₂.card : ℝ) := by
    calc
      ∑ r' ∈ A₂, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) ≤
          ∑ _r' ∈ A₂, Real.log (n : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro r' hr'
        rcases Finset.mem_filter.1 hr' with ⟨hrA, hrNotF1⟩
        have hrBase : Sum.inl r' ∈ C.baseImage I := by
          exact C.mem_baseImage_inl.2 ((C.mem_redProjectionImage_inl.1 hrA).2)
        exact C.baseFiber_card_le_log_of_mem_baseImage_of_not_mem_section4F1 hrBase hrNotF1
      _ = Real.log (n : ℝ) * (A₂.card : ℝ) := by
        simp [mul_comm]
  have hA₂card :
      (A₂.card : ℝ) ≤ degreeBound := by
    have hA₂cardNat : A₂.card ≤ degreeBound := by
      have hfilter : A₂.card ≤ A.card := by
        simpa [A₂] using (A.card_filter_le fun r' => Sum.inl r' ∉ C.section4F1 I)
      exact hfilter.trans
        ((C.card_redProjectionImage_le_univ I (Sum.inl r)).trans (hD.redProjectionBound r))
    exact_mod_cast hA₂cardNat
  have hwhole :
      (C.xCard I (Sum.inl r) : ℝ) =
        ∑ r' ∈ A, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) := by
    exact_mod_cast C.xCard_red_eq_sum_card_redFiber_inter I r
  calc
    (C.xCard I (Sum.inl r) : ℝ) =
        ∑ r' ∈ A, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) := hwhole
    _ =
        ∑ r' ∈ A₁, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) +
          ∑ r' ∈ A₂, (((C.redFiber r' ∩ I).card : ℕ) : ℝ) := hsplit
    _ ≤ (fiberBound : ℝ) * (A₁.card : ℝ) + Real.log (n : ℝ) * (A₂.card : ℝ) := by
      exact add_le_add hsumA₁ hsumA₂
    _ =
        (fiberBound : ℝ) *
            ((((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ)) +
          Real.log (n : ℝ) * (A₂.card : ℝ) := by
      rw [hA₁card]
    _ ≤
        (fiberBound : ℝ) *
            ((((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ)) +
          Real.log (n : ℝ) * degreeBound := by
      gcongr

theorem xCard_blue_le_fiberBound_mul_section4F1_neighbor_card_add_log_mul_degreeBound_of_goodEventD
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (b : Fin m) :
    (C.xCard I (Sum.inr b) : ℝ) ≤
      (fiberBound : ℝ) *
          ((((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ)) +
        Real.log (n : ℝ) * degreeBound := by
  classical
  let A : Finset (Fin m) := C.blueProjectionImage I (Sum.inr b)
  let A₁ : Finset (Fin m) := A.filter fun b' => Sum.inr b' ∈ C.section4F1 I
  let A₂ : Finset (Fin m) := A.filter fun b' => Sum.inr b' ∉ C.section4F1 I
  have hsplit :
      ∑ b' ∈ A, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) =
        ∑ b' ∈ A₁, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) +
          ∑ b' ∈ A₂, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) := by
    simpa [A₁, A₂, A] using
      (Finset.sum_filter_add_sum_filter_not A
        (fun b' => Sum.inr b' ∈ C.section4F1 I)
        (fun b' => (((C.blueFiber b' ∩ I).card : ℕ) : ℝ))).symm
  have hA₁card :
      ((A₁.card : ℕ) : ℝ) =
        ((((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ)) := by
    have hA₁cardNat : A₁.card = (C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card := by
      calc
        A₁.card = (A₁.image fun b' : Fin m => (Sum.inr b' : BaseVertex m)).card := by
          symm
          exact Finset.card_image_of_injective _ (by
            intro a c hac
            exact Sum.inr.inj hac)
        _ = (C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card := by
          rw [C.blueProjectionImage_filter_section4F1_image_inr_eq_baseNeighborSet_inter_section4F1
            I b]
    exact_mod_cast hA₁cardNat
  have hsumA₁ :
      ∑ b' ∈ A₁, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) ≤
        (fiberBound : ℝ) * (A₁.card : ℝ) := by
    calc
      ∑ b' ∈ A₁, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) ≤
          ∑ _b' ∈ A₁, (fiberBound : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro b' hb'
        have hcard : (C.blueFiber b' ∩ I).card ≤ fiberBound := by
          exact (Finset.card_le_card (by
            intro v hv
            exact (Finset.mem_inter.1 hv).1)).trans (hD.blueFiberBound b')
        exact_mod_cast hcard
      _ = (fiberBound : ℝ) * (A₁.card : ℝ) := by
        simp [mul_comm]
  have hsumA₂ :
      ∑ b' ∈ A₂, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) ≤
        Real.log (n : ℝ) * (A₂.card : ℝ) := by
    calc
      ∑ b' ∈ A₂, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) ≤
          ∑ _b' ∈ A₂, Real.log (n : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro b' hb'
        rcases Finset.mem_filter.1 hb' with ⟨hbA, hbNotF1⟩
        have hbBase : Sum.inr b' ∈ C.baseImage I := by
          exact C.mem_baseImage_inr.2 ((C.mem_blueProjectionImage_inr.1 hbA).2)
        exact C.baseFiber_card_le_log_of_mem_baseImage_of_not_mem_section4F1 hbBase hbNotF1
      _ = Real.log (n : ℝ) * (A₂.card : ℝ) := by
        simp [mul_comm]
  have hA₂card :
      (A₂.card : ℝ) ≤ degreeBound := by
    have hA₂cardNat : A₂.card ≤ degreeBound := by
      have hfilter : A₂.card ≤ A.card := by
        simpa [A₂] using (A.card_filter_le fun b' => Sum.inr b' ∉ C.section4F1 I)
      exact hfilter.trans
        ((C.card_blueProjectionImage_le_univ I (Sum.inr b)).trans (hD.blueProjectionBound b))
    exact_mod_cast hA₂cardNat
  have hwhole :
      (C.xCard I (Sum.inr b) : ℝ) =
        ∑ b' ∈ A, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) := by
    exact_mod_cast C.xCard_blue_eq_sum_card_blueFiber_inter I b
  calc
    (C.xCard I (Sum.inr b) : ℝ) =
        ∑ b' ∈ A, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) := hwhole
    _ =
        ∑ b' ∈ A₁, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) +
          ∑ b' ∈ A₂, (((C.blueFiber b' ∩ I).card : ℕ) : ℝ) := hsplit
    _ ≤ (fiberBound : ℝ) * (A₁.card : ℝ) + Real.log (n : ℝ) * (A₂.card : ℝ) := by
      exact add_le_add hsumA₁ hsumA₂
    _ =
        (fiberBound : ℝ) *
            ((((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ)) +
          Real.log (n : ℝ) * (A₂.card : ℝ) := by
      rw [hA₁card]
    _ ≤
        (fiberBound : ℝ) *
            ((((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ)) +
          Real.log (n : ℝ) * degreeBound := by
      gcongr

set_option linter.style.longLine false in
theorem
    xCard_le_fiberBound_mul_paperT2_div_log_add_log_mul_degreeBound_of_goodEventD_of_mem_baseImage_of_not_mem_section4F2
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {x : BaseVertex m} {ε : ℝ}
    (hxBase : x ∈ C.baseImage I) (hxF2 : x ∉ C.section4F2 I ε) :
    (C.xCard I x : ℝ) ≤
      (fiberBound : ℝ) * (Twobites.paperT2 ε n / Real.log (n : ℝ)) +
        Real.log (n : ℝ) * degreeBound := by
  have hcount :
      ((((C.baseNeighborSet x ∩ C.section4F1 I).card : ℕ) : ℝ)) ≤
        Twobites.paperT2 ε n / Real.log (n : ℝ) :=
    C.section4F1_neighbor_card_le_paperT2_div_log_of_mem_baseImage_of_not_mem_section4F2
      hxBase hxF2
  cases x with
  | inl r =>
      calc
        (C.xCard I (Sum.inl r) : ℝ) ≤
            (fiberBound : ℝ) *
                ((((C.baseNeighborSet (Sum.inl r) ∩ C.section4F1 I).card : ℕ) : ℝ)) +
              Real.log (n : ℝ) * degreeBound := by
            exact
              C.xCard_red_le_fiberBound_mul_section4F1_neighbor_card_add_log_mul_degreeBound_of_goodEventD
                hD I r
        _ ≤
            (fiberBound : ℝ) * (Twobites.paperT2 ε n / Real.log (n : ℝ)) +
              Real.log (n : ℝ) * degreeBound := by
            gcongr
  | inr b =>
      calc
        (C.xCard I (Sum.inr b) : ℝ) ≤
            (fiberBound : ℝ) *
                ((((C.baseNeighborSet (Sum.inr b) ∩ C.section4F1 I).card : ℕ) : ℝ)) +
              Real.log (n : ℝ) * degreeBound := by
            exact
              C.xCard_blue_le_fiberBound_mul_section4F1_neighbor_card_add_log_mul_degreeBound_of_goodEventD
                hD I b
        _ ≤
            (fiberBound : ℝ) * (Twobites.paperT2 ε n / Real.log (n : ℝ)) +
              Real.log (n : ℝ) * degreeBound := by
            gcongr

set_option linter.style.longLine false in
theorem
    baseImage_inter_HPart_subset_section4F2_of_goodEventD_of_section4_bound
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ}
    (hbound :
      (fiberBound : ℝ) * (Twobites.paperT2 ε n / Real.log (n : ℝ)) +
          Real.log (n : ℝ) * degreeBound ≤
        Twobites.paperT1 n) :
    C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε := by
  intro x hx
  rcases Finset.mem_inter.1 hx with ⟨hxBase, hxH⟩
  by_contra hxF2
  have hxle :=
    C.xCard_le_fiberBound_mul_paperT2_div_log_add_log_mul_degreeBound_of_goodEventD_of_mem_baseImage_of_not_mem_section4F2
      hD I hxBase hxF2
  have hxgt := C.paperT1_lt_xCard_of_mem_HPart hxH
  linarith

theorem
    baseImage_inter_HPart_subset_section4F2_of_goodEventD_of_paperSection4Bound
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {β ε2 : ℝ}
    (hfiberBound : (fiberBound : ℝ) ≤ (1 + ε2) * Twobites.paperS n)
    (hdegreeBound : (degreeBound : ℝ) ≤ (1 + ε2) * Twobites.paperP β n * Twobites.paperM n)
    (hn : 1 < n) (hβ0 : 0 ≤ β) (hβ : β ≤ (1 / 2 : ℝ)) (hε2low : -1 ≤ ε2)
    (hε2 : ε2 ≤ (1 / 8 : ℝ)) (hloglog : 2 ≤ Real.log (Real.log (n : ℝ)))
    (hfiberScale :
      (1 + ε2) * Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 / 8 : ℝ) - ε2) / 2) :
    C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε2 := by
  have hlogpos : 0 < Real.log (n : ℝ) := Twobites.paperLog_pos hn
  have htermNonneg : 0 ≤ Twobites.paperT2 ε2 n / Real.log (n : ℝ) := by
    exact div_nonneg (Twobites.paperT2_nonneg ε2 n) hlogpos.le
  have hfiberTerm :
      (fiberBound : ℝ) * (Twobites.paperT2 ε2 n / Real.log (n : ℝ)) ≤
        ((1 + ε2) * Twobites.paperS n) * (Twobites.paperT2 ε2 n / Real.log (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hfiberBound htermNonneg
  have hdegreeTerm :
      Real.log (n : ℝ) * degreeBound ≤
        Real.log (n : ℝ) * ((1 + ε2) * Twobites.paperP β n * Twobites.paperM n) := by
    exact mul_le_mul_of_nonneg_left hdegreeBound hlogpos.le
  have hpaper :
      ((1 + ε2) * Twobites.paperS n) * (Twobites.paperT2 ε2 n / Real.log (n : ℝ)) +
          Real.log (n : ℝ) * ((1 + ε2) * Twobites.paperP β n * Twobites.paperM n) ≤
        Twobites.paperT1 n := by
    exact Twobites.paperSection4Bound_le_paperT1_of_two_le_loglog_of_fiberScale
      hn hβ0 hβ hε2low hε2 hloglog hfiberScale
  have hbound :
      (fiberBound : ℝ) * (Twobites.paperT2 ε2 n / Real.log (n : ℝ)) +
          Real.log (n : ℝ) * degreeBound ≤
        Twobites.paperT1 n := by
    linarith
  exact C.baseImage_inter_HPart_subset_section4F2_of_goodEventD_of_section4_bound hD I hbound

theorem section4F1_card_le_two_mul_card_div_log
    (C : ConstructionData n m) (I : Finset (Fin n)) (hn : 1 < n) :
    ((C.section4F1 I).card : ℝ) ≤ 2 * (I.card : ℝ) / Real.log (n : ℝ) := by
  have hlogpos : 0 < Real.log (n : ℝ) := Twobites.paperLog_pos hn
  have hbase := C.section4F1_card_mul_log_le_two_mul_card I
  exact (le_div_iff₀ hlogpos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hbase)

theorem section4F2_card_le_card_LPart_union_HPart_of_paper
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ)) :
    (C.section4F2 I ε).card ≤ (C.LPart I ε ∪ C.HPart I).card := by
  exact C.section4F2_card_le_card_LPart_union_HPart_of_log_pos_of_paperT3_le_paperT2 I
    (Twobites.paperLog_pos hn) (Twobites.paperT3_le_paperT2 (Nat.le_of_lt hn) hε)

theorem section4F2_card_le_card_LPart_add_card_HPart_of_paper
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ)) :
    (C.section4F2 I ε).card ≤ (C.LPart I ε).card + (C.HPart I).card := by
  exact (C.section4F2_card_le_card_LPart_union_HPart_of_paper I hn hε).trans
    (Finset.card_union_le _ _)

theorem section4F1_union_section4F2_card_le_two_mul_card_div_log_add_card_LPart_add_card_HPart
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ)) :
    ((C.section4F1 I ∪ C.section4F2 I ε).card : ℝ) ≤
      2 * (I.card : ℝ) / Real.log (n : ℝ) +
        ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ) := by
  have hunion :
      ((C.section4F1 I ∪ C.section4F2 I ε).card : ℝ) ≤
        ((C.section4F1 I).card : ℝ) + ((C.section4F2 I ε).card : ℝ) := by
    exact_mod_cast (Finset.card_union_le (C.section4F1 I) (C.section4F2 I ε))
  have hF1 : ((C.section4F1 I).card : ℝ) ≤ 2 * (I.card : ℝ) / Real.log (n : ℝ) :=
    C.section4F1_card_le_two_mul_card_div_log I hn
  have hF2 : ((C.section4F2 I ε).card : ℝ) ≤
      ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ) := by
    exact_mod_cast C.section4F2_card_le_card_LPart_add_card_HPart_of_paper I hn hε
  linarith

theorem card_mul_section4F1_union_section4F2_card_le_two_mul_card_sq_div_log_add_card_mul_parts
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ)) :
    (I.card : ℝ) * ((C.section4F1 I ∪ C.section4F2 I ε).card : ℝ) ≤
      (I.card : ℝ) *
        (2 * (I.card : ℝ) / Real.log (n : ℝ) +
          ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ)) := by
  have hcard :=
    C.section4F1_union_section4F2_card_le_two_mul_card_div_log_add_card_LPart_add_card_HPart
      I hn hε
  exact mul_le_mul_of_nonneg_left hcard (by positivity)

theorem cast_section4RevealBudget_le_eps_mul_paperKSq_of_cardBounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε ε1 lBound hBound : ℝ}
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hL : ((C.LPart I ε).card : ℝ) ≤ lBound)
    (hH : ((C.HPart I).card : ℝ) ≤ hBound)
    (harith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + lBound + hBound) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) ≤
      ε1 * Twobites.paperK κ n ^ 2 := by
  have hinner :
      2 * (I.card : ℝ) / Real.log (n : ℝ) +
          ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ) ≤
        2 * (I.card : ℝ) / Real.log (n : ℝ) + lBound + hBound := by
    linarith
  have hparts :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
            ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ)) ≤
        (I.card : ℝ) * (2 * (I.card : ℝ) / Real.log (n : ℝ) + lBound + hBound) := by
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  calc
    (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) =
        (I.card : ℝ) * ((C.section4F1 I ∪ C.section4F2 I ε).card : ℝ) := by
      norm_num
    _ ≤
        (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
            ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ)) :=
      C.card_mul_section4F1_union_section4F2_card_le_two_mul_card_sq_div_log_add_card_mul_parts
        I hn hε
    _ ≤ (I.card : ℝ) * (2 * (I.card : ℝ) / Real.log (n : ℝ) + lBound + hBound) := hparts
    _ ≤ ε1 * Twobites.paperK κ n ^ 2 := harith

theorem HPart_card_le_paperHugeWitnessNat_of_goodEventD
    (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT1 : 2 < Twobites.paperT1 n)
    (hchoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n) :
    ((C.HPart I).card : ℝ) ≤ (Twobites.paperHugeWitnessNat κ n : ℝ) := by
  have htwo :
      2 * Twobites.paperKNat κ n <
        Twobites.paperHugeWitnessNat κ n * ⌈Twobites.paperT1 n⌉₊ :=
    Twobites.two_mul_paperKNat_lt_paperHugeWitnessNat_mul_ceil_paperT1 hκ hT1
  have hwitness :
      Twobites.paperKNat κ n <
        Twobites.paperHugeWitnessNat κ n * ⌈Twobites.paperT1 n⌉₊ -
          (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound :=
    Twobites.paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_of_two_mul_lt htwo hchoose
  exact_mod_cast
    Nat.le_of_lt (C.HPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hwitness))

set_option linter.style.longLine false in
theorem
    cast_section4RevealBudget_le_eps_mul_paperKSq_of_LBound_of_paperHugeWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε ε1 lBound : ℝ}
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT1 : 2 < Twobites.paperT1 n)
    (hchoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hL : ((C.LPart I ε).card : ℝ) ≤ lBound)
    (harith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + lBound +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) ≤
      ε1 * Twobites.paperK κ n ^ 2 := by
  have hH :
      ((C.HPart I).card : ℝ) ≤ (Twobites.paperHugeWitnessNat κ n : ℝ) :=
    C.HPart_card_le_paperHugeWitnessNat_of_goodEventD hD I hI hκ hT1 hchoose
  exact
    C.cast_section4RevealBudget_le_eps_mul_paperKSq_of_cardBounds I hn hε hL hH harith

set_option linter.style.longLine false in
theorem
    cast_section4RevealBudget_le_eps_mul_paperKSq_of_LWitness_of_paperHugeWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε ε1 : ℝ} {lWitness : ℕ}
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT1 : 2 < Twobites.paperT1 n)
    (hLWitness :
      Twobites.paperKNat κ n < lWitness * ⌈Twobites.paperT2 ε n⌉₊ -
        lWitness.choose 2 * codegreeBound)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (harith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + (lWitness : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) ≤
      ε1 * Twobites.paperK κ n ^ 2 := by
  have hL :
      ((C.LPart I ε).card : ℝ) ≤ (lWitness : ℝ) :=
    C.cast_LPart_card_le_of_goodEventD_of_paperWitness hD I hI hLWitness
  exact
    C.cast_section4RevealBudget_le_eps_mul_paperKSq_of_LBound_of_paperHugeWitness
      hD I hn hε hI hκ hT1 hHChoose hL harith

set_option linter.style.longLine false in
theorem
    cast_section4RevealBudget_le_eps_mul_paperKSq_of_paperLargeWitness_of_paperHugeWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε ε1 : ℝ}
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT2 : 2 < Twobites.paperT2 ε n) (hT1 : 2 < Twobites.paperT1 n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (harith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
              (Twobites.paperLargeWitnessNat κ ε n : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) ≤
      ε1 * Twobites.paperK κ n ^ 2 := by
  have hLWitness :
      Twobites.paperKNat κ n <
        Twobites.paperLargeWitnessNat κ ε n * ⌈Twobites.paperT2 ε n⌉₊ -
          (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound := by
    exact
      Twobites.paperKNat_lt_mul_ceil_paperT2_sub_choose_mul_of_two_mul_lt
        (Twobites.two_mul_paperKNat_lt_paperLargeWitnessNat_mul_ceil_paperT2 hκ hT2)
        hLChoose
  exact
    C.cast_section4RevealBudget_le_eps_mul_paperKSq_of_LWitness_of_paperHugeWitness
      hD I hn hε hI hκ hT1 hLWitness hHChoose harith

set_option linter.style.longLine false in
theorem
    cast_section4RevealBudget_le_eps_mul_paperKSq_of_goodEventD_of_witnessBounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε ε1 : ℝ} {lWitness hWitness : ℕ}
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hLWitness :
      Twobites.paperKNat κ n < lWitness * ⌈Twobites.paperT2 ε n⌉₊ -
        lWitness.choose 2 * codegreeBound)
    (hHWitness :
      Twobites.paperKNat κ n < hWitness * ⌈Twobites.paperT1 n⌉₊ -
        hWitness.choose 2 * codegreeBound)
    (harith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + (lWitness : ℝ) + (hWitness : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) ≤
      ε1 * Twobites.paperK κ n ^ 2 := by
  have hL :
      ((C.LPart I ε).card : ℝ) ≤ (lWitness : ℝ) := by
    exact_mod_cast Nat.le_of_lt (C.LPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hLWitness))
  have hH :
      ((C.HPart I).card : ℝ) ≤ (hWitness : ℝ) := by
    exact_mod_cast Nat.le_of_lt (C.HPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hHWitness))
  have hinner :
      2 * (I.card : ℝ) / Real.log (n : ℝ) +
          ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ) ≤
        2 * (I.card : ℝ) / Real.log (n : ℝ) + (lWitness : ℝ) + (hWitness : ℝ) := by
    linarith
  have hparts :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
            ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ)) ≤
        (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + (lWitness : ℝ) + (hWitness : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  calc
    (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) =
        (I.card : ℝ) * ((C.section4F1 I ∪ C.section4F2 I ε).card : ℝ) := by
      norm_num
    _ ≤
        (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
            ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ)) :=
      C.card_mul_section4F1_union_section4F2_card_le_two_mul_card_sq_div_log_add_card_mul_parts
        I hn hε
    _ ≤
        (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + (lWitness : ℝ) + (hWitness : ℝ)) :=
      hparts
    _ ≤ ε1 * Twobites.paperK κ n ^ 2 := harith

/-- The ordered reveal-counting object is bounded by the obvious color-separated rectangle count. -/
theorem revealedBaseArcSet_card_le (A B : Finset (BaseVertex m)) :
    (revealedBaseArcSet A B).card ≤
      (A.filter IsRedBaseVertex).card * (B.filter IsRedBaseVertex).card +
        (A.filter IsBlueBaseVertex).card * (B.filter IsBlueBaseVertex).card := by
  classical
  calc
    (revealedBaseArcSet A B).card ≤
        ((((A.filter IsRedBaseVertex).product (B.filter IsRedBaseVertex)).filter
            fun p => p.1 ≠ p.2).card) +
          ((((A.filter IsBlueBaseVertex).product (B.filter IsBlueBaseVertex)).filter
              fun p => p.1 ≠ p.2).card) := by
      simpa [revealedBaseArcSet] using
        (Finset.card_union_le
          (((A.filter IsRedBaseVertex).product (B.filter IsRedBaseVertex)).filter
            fun p => p.1 ≠ p.2)
          (((A.filter IsBlueBaseVertex).product (B.filter IsBlueBaseVertex)).filter
            fun p => p.1 ≠ p.2))
    _ ≤ ((A.filter IsRedBaseVertex).product (B.filter IsRedBaseVertex)).card +
          ((A.filter IsBlueBaseVertex).product (B.filter IsBlueBaseVertex)).card := by
      exact add_le_add (Finset.card_filter_le _ _) (Finset.card_filter_le _ _)
    _ = (A.filter IsRedBaseVertex).card * (B.filter IsRedBaseVertex).card +
          (A.filter IsBlueBaseVertex).card * (B.filter IsBlueBaseVertex).card := by
      simp

theorem revealedBasePairSet_card_le_revealedBaseArcSet_card (A B : Finset (BaseVertex m)) :
    (revealedBasePairSet A B).card ≤ (revealedBaseArcSet A B).card := by
  rfl

theorem section4RevealArcSet_card_le_card_mul (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.section4RevealArcSet I A).card ≤ I.card * A.card := by
  have hbase := revealedBaseArcSet_card_le A (C.baseImage I)
  have hred :
      (A.filter IsRedBaseVertex).card * ((C.baseImage I).filter IsRedBaseVertex).card ≤
        (A.filter IsRedBaseVertex).card * I.card := by
    have hredImage :
        ((C.baseImage I).filter IsRedBaseVertex).card ≤ I.card := by
      rw [C.baseImage_filter_isRed_card_eq_redImage_card I]
      simpa [ConstructionData.redImage] using
        (Finset.card_image_le (s := I) (f := C.redProj))
    exact Nat.mul_le_mul_left _ hredImage
  have hblue :
      (A.filter IsBlueBaseVertex).card * ((C.baseImage I).filter IsBlueBaseVertex).card ≤
        (A.filter IsBlueBaseVertex).card * I.card := by
    have hblueImage :
        ((C.baseImage I).filter IsBlueBaseVertex).card ≤ I.card := by
      rw [C.baseImage_filter_isBlue_card_eq_blueImage_card I]
      simpa [ConstructionData.blueImage] using
        (Finset.card_image_le (s := I) (f := C.blueProj))
    exact Nat.mul_le_mul_left _ hblueImage
  calc
    (C.section4RevealArcSet I A).card =
        (revealedBaseArcSet A (C.baseImage I)).card := rfl
    _ ≤ (A.filter IsRedBaseVertex).card * ((C.baseImage I).filter IsRedBaseVertex).card +
          (A.filter IsBlueBaseVertex).card * ((C.baseImage I).filter IsBlueBaseVertex).card :=
        hbase
    _ ≤ (A.filter IsRedBaseVertex).card * I.card +
          (A.filter IsBlueBaseVertex).card * I.card := Nat.add_le_add hred hblue
    _ = ((A.filter IsRedBaseVertex).card + (A.filter IsBlueBaseVertex).card) * I.card := by
      rw [Nat.add_mul]
    _ = A.card * I.card := by rw [card_filter_isRed_add_card_filter_isBlue A]
    _ = I.card * A.card := by rw [Nat.mul_comm]

theorem section4RevealPairSet_card_le_card_mul (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.section4RevealPairSet I A).card ≤ I.card * A.card := by
  exact
    (revealedBasePairSet_card_le_revealedBaseArcSet_card A (C.baseImage I)).trans
      (C.section4RevealArcSet_card_le_card_mul I A)

theorem revealedBaseOpenPairSet_card_le_section4_budget (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.revealedBaseOpenPairSet I A).card ≤ I.card * A.card := by
  exact
    (C.revealedBaseOpenPairSet_card_le_section4RevealPairSet_card I A).trans
      (C.section4RevealPairSet_card_le_card_mul I A)

theorem revealedBaseOpenPairSet_card_le_section4_budget_of_section4F
    (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) :
    (C.revealedBaseOpenPairSet I (C.section4F I ε)).card ≤
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card := by
  rw [C.revealedBaseOpenPairSet_section4F_eq_union I ε]
  exact C.revealedBaseOpenPairSet_card_le_section4_budget I (C.section4F1 I ∪ C.section4F2 I ε)

theorem openPair_lower_bound_sub_section4_budget_le_unrevealed_section4F
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ} {N : ℕ}
    (hopen : N ≤ (C.baseOpenPairSet I).card) :
    N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card ≤
      (C.unrevealedBaseOpenPairSet I (C.section4F I ε)).card := by
  have hbase :
      N - (C.revealedBaseOpenPairSet I (C.section4F I ε)).card ≤
        (C.unrevealedBaseOpenPairSet I (C.section4F I ε)).card :=
    C.openPair_lower_bound_sub_reveal_budget_le_unrevealed I (C.section4F I ε) hopen
  have hbudget :
      (C.revealedBaseOpenPairSet I (C.section4F I ε)).card ≤
        I.card * (C.section4F1 I ∪ C.section4F2 I ε).card :=
    C.revealedBaseOpenPairSet_card_le_section4_budget_of_section4F I ε
  omega

theorem openPair_lower_bound_sub_section4_budget_le_unrevealedBasePairSet_section4F
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ} {N : ℕ}
    (hopen : N ≤ (C.baseOpenPairSet I).card) :
    N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card ≤
      (C.unrevealedBasePairSet I (C.section4F I ε)).card := by
  exact
    (C.openPair_lower_bound_sub_section4_budget_le_unrevealed_section4F I hopen).trans
      (C.unrevealedBaseOpenPairSet_card_le_unrevealedBasePairSet_card I (C.section4F I ε))

theorem unrevealedBasePair_lower_bound_sub_sameColorClosedPlus_le_section4TPairSet
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m))
    {N M : ℕ}
    (hN : N ≤ (C.unrevealedBasePairSet I A).card)
    (hM : (C.sameColorClosedPlusBasePairSet I A).card ≤ M) :
    N - M ≤ (C.section4TPairSet I A).card := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := C.unrevealedBasePairSet I A) (p := fun p => C.sameColorClosedPlusBasePair I p)
  have hPlus :
      ((C.unrevealedBasePairSet I A).filter fun p => C.sameColorClosedPlusBasePair I p).card =
        (C.sameColorClosedPlusBasePairSet I A).card := by
    unfold sameColorClosedPlusBasePairSet
    rfl
  have hT :
      ((C.unrevealedBasePairSet I A).filter fun p => ¬ C.sameColorClosedPlusBasePair I p).card =
        (C.section4TPairSet I A).card := by
    unfold section4TPairSet
    rfl
  rw [hPlus, hT] at hpart
  omega

theorem openPair_lower_bound_sub_section4_budget_sub_sameColorClosedPlus_le_section4TPairSet
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ} {N M : ℕ}
    (hopen : N ≤ (C.baseOpenPairSet I).card)
    (hM : (C.sameColorClosedPlusBasePairSet I (C.section4F I ε)).card ≤ M) :
    N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card - M ≤
      (C.section4TPairSet I (C.section4F I ε)).card := by
  classical
  have hbase :
      N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card ≤
        (C.unrevealedBasePairSet I (C.section4F I ε)).card :=
    C.openPair_lower_bound_sub_section4_budget_le_unrevealedBasePairSet_section4F I hopen
  have hT :
      N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card - M ≤
        (C.section4TPairSet I (C.section4F I ε)).card :=
    C.unrevealedBasePair_lower_bound_sub_sameColorClosedPlus_le_section4TPairSet
      I (C.section4F I ε) hbase hM
  exact hT

theorem redBaseClosedPlusPairSet_image_sym2_subset_redWitnessBiUnion
    (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.redBaseClosedPlusPairSet I).image Sym2.mk ⊆
      (C.redImage I).biUnion
        (fun r => (C.redProjectionImage I (Sum.inl r)).offDiag.image Sym2.mk) := by
  intro z hz
  rcases Finset.mem_image.1 hz with ⟨p, hp, rfl⟩
  rcases (C.mem_redBaseClosedPlusPairSet.1 hp) with ⟨hpPair, hpClosed⟩
  rcases (C.mem_redBasePairSet.1 hpPair) with ⟨hp₁, hp₂, hpLt⟩
  rcases hpClosed with ⟨r, hrI, hrAdj₁, hrAdj₂, -, -⟩
  refine Finset.mem_biUnion.2 ⟨r, hrI, ?_⟩
  refine Finset.mem_image.2 ⟨p, ?_, rfl⟩
  exact Finset.mem_offDiag.2
    ⟨(C.mem_redProjectionImage_inl.2 ⟨hrAdj₁, hp₁⟩),
      (C.mem_redProjectionImage_inl.2 ⟨hrAdj₂, hp₂⟩), hpLt.ne⟩

theorem blueBaseClosedPlusPairSet_image_sym2_subset_blueWitnessBiUnion
    (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.blueBaseClosedPlusPairSet I).image Sym2.mk ⊆
      (C.blueImage I).biUnion
        (fun b => (C.blueProjectionImage I (Sum.inr b)).offDiag.image Sym2.mk) := by
  intro z hz
  rcases Finset.mem_image.1 hz with ⟨p, hp, rfl⟩
  rcases (C.mem_blueBaseClosedPlusPairSet.1 hp) with ⟨hpPair, hpClosed⟩
  rcases (C.mem_blueBasePairSet.1 hpPair) with ⟨hp₁, hp₂, hpLt⟩
  rcases hpClosed with ⟨b, hbI, hbAdj₁, hbAdj₂, -, -⟩
  refine Finset.mem_biUnion.2 ⟨b, hbI, ?_⟩
  refine Finset.mem_image.2 ⟨p, ?_, rfl⟩
  exact Finset.mem_offDiag.2
    ⟨(C.mem_blueProjectionImage_inr.2 ⟨hbAdj₁, hp₁⟩),
      (C.mem_blueProjectionImage_inr.2 ⟨hbAdj₂, hp₂⟩), hpLt.ne⟩

theorem redBaseClosedPlusPairSet_card_le_redProjectionPairCount
    (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.redBaseClosedPlusPairSet I).card ≤
      C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) := by
  have hstrict :
      ∀ p ∈ C.redBaseClosedPlusPairSet I, p.1 < p.2 := by
    intro p hp
    exact (C.mem_redBasePairSet.1 ((C.mem_redBaseClosedPlusPairSet.1 hp).1)).2.2
  have himage :
      (C.redBaseClosedPlusPairSet I).card =
        ((C.redBaseClosedPlusPairSet I).image Sym2.mk).card := by
    symm
    exact card_image_sym2_mk_of_strictPairSet _ hstrict
  calc
    (C.redBaseClosedPlusPairSet I).card =
        ((C.redBaseClosedPlusPairSet I).image Sym2.mk).card :=
      himage
    _ ≤
        ∑ r ∈ C.redImage I,
          ((C.redProjectionImage I (Sum.inl r)).offDiag.image Sym2.mk).card := by
      exact
        (Finset.card_le_card
          (C.redBaseClosedPlusPairSet_image_sym2_subset_redWitnessBiUnion I)).trans
          Finset.card_biUnion_le
    _ = ∑ r ∈ C.redImage I, ((C.redProjectionImage I (Sum.inl r)).card).choose 2 := by
      simp [Sym2.card_image_offDiag]
    _ = C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) := by
      rw [C.baseImage_filter_isRed_eq_redImage_image_inl I, redProjectionPairCount]
      simp

theorem blueBaseClosedPlusPairSet_card_le_blueProjectionPairCount
    (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.blueBaseClosedPlusPairSet I).card ≤
      C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex) := by
  have hstrict :
      ∀ p ∈ C.blueBaseClosedPlusPairSet I, p.1 < p.2 := by
    intro p hp
    exact (C.mem_blueBasePairSet.1 ((C.mem_blueBaseClosedPlusPairSet.1 hp).1)).2.2
  have himage :
      (C.blueBaseClosedPlusPairSet I).card =
        ((C.blueBaseClosedPlusPairSet I).image Sym2.mk).card := by
    symm
    exact card_image_sym2_mk_of_strictPairSet _ hstrict
  calc
    (C.blueBaseClosedPlusPairSet I).card =
        ((C.blueBaseClosedPlusPairSet I).image Sym2.mk).card :=
      himage
    _ ≤
        ∑ b ∈ C.blueImage I,
          ((C.blueProjectionImage I (Sum.inr b)).offDiag.image Sym2.mk).card := by
      exact
        (Finset.card_le_card
          (C.blueBaseClosedPlusPairSet_image_sym2_subset_blueWitnessBiUnion I)).trans
          Finset.card_biUnion_le
    _ = ∑ b ∈ C.blueImage I, ((C.blueProjectionImage I (Sum.inr b)).card).choose 2 := by
      simp [Sym2.card_image_offDiag]
    _ = C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex) := by
      rw [C.baseImage_filter_isBlue_eq_blueImage_image_inr I, blueProjectionPairCount]
      simp

theorem sameColorClosedPlusBasePairSet_card_le_projectionPairCount_sum
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.sameColorClosedPlusBasePairSet I A).card ≤
      C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex) := by
  classical
  let sR : Finset (BaseVertex m × BaseVertex m) :=
    (C.redBaseClosedPlusPairSet I).image fun p => (Sum.inl p.1, Sum.inl p.2)
  let sB : Finset (BaseVertex m × BaseVertex m) :=
    (C.blueBaseClosedPlusPairSet I).image fun p => (Sum.inr p.1, Sum.inr p.2)
  have hsubset : C.sameColorClosedPlusBasePairSet I A ⊆ sR ∪ sB := by
    intro p hp
    rcases p with ⟨x, y⟩
    cases x <;> cases y
    · rcases (C.mem_sameColorClosedPlusBasePairSet.1 hp) with ⟨hpBase, hpClosed⟩
      have hpBase' := (C.mem_unrevealedBasePairSet.1 hpBase).1
      exact Finset.mem_union.2 <| Or.inl <| Finset.mem_image.2 ⟨_, by
        exact (C.mem_redBaseClosedPlusPairSet.2
          ⟨(C.mem_basePairSet_inl_inl.1 hpBase'), hpClosed⟩), rfl⟩
    · exact (C.not_mem_basePairSet_inl_inr).elim ((C.mem_unrevealedBasePairSet.1
        ((C.mem_sameColorClosedPlusBasePairSet.1 hp).1)).1)
    · exact (C.not_mem_basePairSet_inr_inl).elim ((C.mem_unrevealedBasePairSet.1
        ((C.mem_sameColorClosedPlusBasePairSet.1 hp).1)).1)
    · rcases (C.mem_sameColorClosedPlusBasePairSet.1 hp) with ⟨hpBase, hpClosed⟩
      have hpBase' := (C.mem_unrevealedBasePairSet.1 hpBase).1
      exact Finset.mem_union.2 <| Or.inr <| Finset.mem_image.2 ⟨_, by
        exact (C.mem_blueBaseClosedPlusPairSet.2
          ⟨(C.mem_basePairSet_inr_inr.1 hpBase'), hpClosed⟩), rfl⟩
  have hcardUnion :
      (C.sameColorClosedPlusBasePairSet I A).card ≤ sR.card + sB.card := by
    exact (Finset.card_le_card hsubset).trans (Finset.card_union_le sR sB)
  have hsR :
      sR.card = (C.redBaseClosedPlusPairSet I).card := by
    dsimp [sR]
    simpa using
      (Finset.card_image_of_injective (s := C.redBaseClosedPlusPairSet I)
        (f := fun p => (Sum.inl p.1, Sum.inl p.2))
        (by
          intro a b hab
          cases a
          cases b
          cases hab
          rfl))
  have hsB :
      sB.card = (C.blueBaseClosedPlusPairSet I).card := by
    dsimp [sB]
    simpa using
      (Finset.card_image_of_injective (s := C.blueBaseClosedPlusPairSet I)
        (f := fun p => (Sum.inr p.1, Sum.inr p.2))
        (by
          intro a b hab
          cases a
          cases b
          cases hab
          rfl))
  rw [hsR, hsB] at hcardUnion
  exact hcardUnion.trans <|
    add_le_add (C.redBaseClosedPlusPairSet_card_le_redProjectionPairCount I)
      (C.blueBaseClosedPlusPairSet_card_le_blueProjectionPairCount I)

theorem openPair_lower_bound_sub_section4_budget_sub_projectionPairCount_sum_le_section4TPairSet
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ} {N : ℕ}
    (hopen : N ≤ (C.baseOpenPairSet I).card) :
    N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
        (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) ≤
      (C.section4TPairSet I (C.section4F I ε)).card := by
  exact
    C.openPair_lower_bound_sub_section4_budget_sub_sameColorClosedPlus_le_section4TPairSet I
      hopen (C.sameColorClosedPlusBasePairSet_card_le_projectionPairCount_sum I (C.section4F I ε))

theorem section4UCondPairSet_card_eq (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) :
    (C.section4UCondPairSet I A).card =
      (C.section4URedCondPairSet I A).card + (C.section4UBlueCondPairSet I A).card := by
  classical
  let sR : Finset (BaseVertex m × BaseVertex m) :=
    (C.section4URedCondPairSet I A).image fun p => (Sum.inl p.1, Sum.inl p.2)
  let sB : Finset (BaseVertex m × BaseVertex m) :=
    (C.section4UBlueCondPairSet I A).image fun p => (Sum.inr p.1, Sum.inr p.2)
  have hsR :
      sR.card = (C.section4URedCondPairSet I A).card := by
    dsimp [sR]
    simpa using
      (Finset.card_image_of_injective (s := C.section4URedCondPairSet I A)
        (f := fun p => (Sum.inl p.1, Sum.inl p.2))
        (by
          intro a b hab
          cases a
          cases b
          cases hab
          rfl))
  have hsB :
      sB.card = (C.section4UBlueCondPairSet I A).card := by
    dsimp [sB]
    simpa using
      (Finset.card_image_of_injective (s := C.section4UBlueCondPairSet I A)
        (f := fun p => (Sum.inr p.1, Sum.inr p.2))
        (by
          intro a b hab
          cases a
          cases b
          cases hab
          rfl))
  have hdisj : Disjoint sR sB := by
    refine Finset.disjoint_left.2 ?_
    intro p hpR hpB
    rcases Finset.mem_image.1 hpR with ⟨qR, _, hqR⟩
    rcases Finset.mem_image.1 hpB with ⟨qB, _, hqB⟩
    rcases qR with ⟨r, r'⟩
    rcases qB with ⟨b, b'⟩
    have hfst : (Sum.inl r : BaseVertex m) = Sum.inr b := by
      simpa [hqR, hqB] using congrArg Prod.fst (hqR.trans hqB.symm)
    cases hfst
  calc
    (C.section4UCondPairSet I A).card = (sR ∪ sB).card := by
      rfl
    _ = sR.card + sB.card := Finset.card_union_of_disjoint hdisj
    _ = (C.section4URedCondPairSet I A).card + (C.section4UBlueCondPairSet I A).card := by
      rw [hsR, hsB]

theorem section4UCondPairSet_subset_section4TPairSet (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.section4UCondPairSet I A ⊆ C.section4TPairSet I A := by
  intro p hp
  rw [section4UCondPairSet] at hp
  rcases Finset.mem_union.1 hp with hR | hB
  · rcases Finset.mem_image.1 hR with ⟨q, hq, rfl⟩
    exact
      (C.mem_section4TPairSet_inl_inl.2 <|
        (C.mem_section4URedPairSet.1 (C.mem_section4URedCondPairSet.1 hq).1).1)
  · rcases Finset.mem_image.1 hB with ⟨q, hq, rfl⟩
    exact
      (C.mem_section4TPairSet_inr_inr.2 <|
        (C.mem_section4UBluePairSet.1 (C.mem_section4UBlueCondPairSet.1 hq).1).1)

theorem section4TRemainingPairSet_card_eq (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) :
    (C.section4TRemainingPairSet I A).card =
      (C.section4TPairSet I A).card -
        (C.section4URedCondPairSet I A).card -
          (C.section4UBlueCondPairSet I A).card := by
  classical
  have hpart :=
    Finset.card_filter_add_card_filter_not (s := C.section4TPairSet I A)
      (p := fun p => p ∈ C.section4UCondPairSet I A)
  have hfilter :
      (C.section4TPairSet I A).filter (fun p => p ∈ C.section4UCondPairSet I A) =
        C.section4UCondPairSet I A := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      exact (Finset.mem_filter.1 hp).2
    · intro hp
      exact Finset.mem_filter.2 ⟨C.section4UCondPairSet_subset_section4TPairSet I A hp, hp⟩
  rw [show (C.section4TPairSet I A).filter
      (fun p => p ∉ C.section4UCondPairSet I A) = C.section4TRemainingPairSet I A by
      rfl] at hpart
  rw [hfilter, C.section4UCondPairSet_card_eq] at hpart
  omega

theorem section4TRemainingPairSet_card_eq_of_card_eq_condCounts
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m))
    {uR uB : ℕ}
    (huR : (C.section4URedCondPairSet I A).card = uR)
    (huB : (C.section4UBlueCondPairSet I A).card = uB) :
    (C.section4TRemainingPairSet I A).card = (C.section4TPairSet I A).card - uR - uB := by
  rw [C.section4TRemainingPairSet_card_eq I A, huR, huB]

theorem section4TPairSet_lower_bound_sub_condCounts_le_section4TRemainingPairSet
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m))
    {N R B : ℕ}
    (hT : N ≤ (C.section4TPairSet I A).card)
    (hR : (C.section4URedCondPairSet I A).card ≤ R)
    (hB : (C.section4UBlueCondPairSet I A).card ≤ B) :
    N - R - B ≤ (C.section4TRemainingPairSet I A).card := by
  rw [C.section4TRemainingPairSet_card_eq I A]
  omega

theorem section4RevealPairSet_card_le_section4_budget (C : ConstructionData n m)
    (I : Finset (Fin n)) {ε : ℝ} :
    (C.section4RevealPairSet I (C.section4F1 I ∪ C.section4F2 I ε)).card ≤
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card := by
  exact C.section4RevealPairSet_card_le_card_mul I (C.section4F1 I ∪ C.section4F2 I ε)

theorem cast_section4RevealPairSet_card_le_two_mul_card_sq_div_log_add_card_mul_parts
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ)) :
    (((C.section4RevealPairSet I (C.section4F1 I ∪ C.section4F2 I ε)).card : ℕ) : ℝ) ≤
      (I.card : ℝ) *
        (2 * (I.card : ℝ) / Real.log (n : ℝ) +
          ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ)) := by
  calc
    (((C.section4RevealPairSet I (C.section4F1 I ∪ C.section4F2 I ε)).card : ℕ) : ℝ) ≤
        (I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) := by
      exact_mod_cast C.section4RevealPairSet_card_le_section4_budget I (ε := ε)
    _ = (I.card : ℝ) * ((C.section4F1 I ∪ C.section4F2 I ε).card : ℝ) := by norm_num
    _ ≤ (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
            ((C.LPart I ε).card : ℝ) + ((C.HPart I).card : ℝ)) :=
      C.card_mul_section4F1_union_section4F2_card_le_two_mul_card_sq_div_log_add_card_mul_parts
        I hn hε

theorem cast_choose_two_le_half_mul_of_le {a : ℕ} {T : ℝ} (hT : (a : ℝ) ≤ T) :
    ((a.choose 2 : ℕ) : ℝ) ≤ (a : ℝ) * T / 2 := by
  have ha : 0 ≤ (a : ℝ) := by
    positivity
  have hminus : (a : ℝ) - 1 ≤ T := by
    linarith
  calc
    ((a.choose 2 : ℕ) : ℝ) = (a : ℝ) * ((a : ℝ) - 1) / 2 := by
      simpa using (Nat.cast_choose_two ℝ a)
    _ ≤ (a : ℝ) * T / 2 := by
      have hmul : (a : ℝ) * ((a : ℝ) - 1) ≤ (a : ℝ) * T := by
        exact mul_le_mul_of_nonneg_left hminus ha
      nlinarith

theorem cast_sum_choose_two_card_le_half_threshold_mul_sum_card {α : Type*}
    (F : BaseVertex m → Finset α) (A : Finset (BaseVertex m)) {T : ℝ}
    (hA : ∀ x ∈ A, ((F x).card : ℝ) ≤ T) :
    ((∑ x ∈ A, ((F x).card).choose 2 : ℕ) : ℝ) ≤
      (T / 2) * ∑ x ∈ A, ((F x).card : ℝ) := by
  calc
    ((∑ x ∈ A, ((F x).card).choose 2 : ℕ) : ℝ)
        = ∑ x ∈ A, ((((F x).card).choose 2 : ℕ) : ℝ) := by
            simp
    _ ≤ ∑ x ∈ A, ((F x).card : ℝ) * T / 2 := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact cast_choose_two_le_half_mul_of_le (hA x hx)
    _ = (T / 2) * ∑ x ∈ A, ((F x).card : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring

theorem choose_two_add_le_choose_two_sum (a b : ℕ) :
    a.choose 2 + b.choose 2 ≤ (a + b).choose 2 := by
  have hdiff :
      (((a + b).choose 2 : ℕ) : ℚ) - ((a.choose 2 + b.choose 2 : ℕ) : ℚ) = a * b := by
    rw [Nat.cast_add]
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
    rw [Nat.cast_add]
    ring_nf
  have hab : (0 : ℚ) ≤ a * b := by
    positivity
  have hq : ((a.choose 2 + b.choose 2 : ℕ) : ℚ) ≤ ((a + b).choose 2 : ℕ) := by
    linarith
  exact_mod_cast hq

theorem cast_choose_two_add_eq (a b : ℕ) :
    (((a + b).choose 2 : ℕ) : ℝ) =
      ((a.choose 2 : ℕ) : ℝ) + (a : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) := by
  rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_add]
  ring

theorem cast_choose_two_add_le_one_add_mul_choose_two {a b : ℕ} {ε : ℝ}
    (herr :
      (a : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) ≤ ε * (((a.choose 2 : ℕ) : ℝ))) :
    (((a + b).choose 2 : ℕ) : ℝ) ≤ (1 + ε) * (((a.choose 2 : ℕ) : ℝ)) := by
  calc
    (((a + b).choose 2 : ℕ) : ℝ)
        = ((a.choose 2 : ℕ) : ℝ) + ((a : ℝ) * b + ((b.choose 2 : ℕ) : ℝ)) := by
            simpa [add_assoc, add_left_comm, add_comm] using cast_choose_two_add_eq a b
    _ ≤ ((a.choose 2 : ℕ) : ℝ) + ε * (((a.choose 2 : ℕ) : ℝ)) := by
      gcongr
    _ = (1 + ε) * (((a.choose 2 : ℕ) : ℝ)) := by
      ring

theorem sum_choose_two_le_choose_two_sum {α : Type*} (A : Finset α) (f : α → ℕ) :
    ∑ x ∈ A, (f x).choose 2 ≤ (∑ x ∈ A, f x).choose 2 := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      calc
        ∑ x ∈ insert a s, (f x).choose 2 = (f a).choose 2 + ∑ x ∈ s, (f x).choose 2 := by
          simp [ha]
        _ ≤ (f a).choose 2 + (∑ x ∈ s, f x).choose 2 := by
          gcongr
        _ ≤ ((f a) + ∑ x ∈ s, f x).choose 2 := choose_two_add_le_choose_two_sum _ _
        _ = (∑ x ∈ insert a s, f x).choose 2 := by
          simp [ha]

theorem choose_two_add_le_choose_two_cap_add_choose_two_sub {a b cap : ℕ}
    (ha : a ≤ cap) (hb : b ≤ cap) (hcap : cap ≤ a + b) :
    a.choose 2 + b.choose 2 ≤ cap.choose 2 + (a + b - cap).choose 2 := by
  have hdiff :
      ((cap.choose 2 + (a + b - cap).choose 2 : ℕ) : ℚ) -
        ((a.choose 2 + b.choose 2 : ℕ) : ℚ) = ((cap : ℚ) - a) * ((cap : ℚ) - b) := by
    rw [Nat.cast_add, Nat.cast_add]
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
    rw [Nat.cast_sub hcap]
    repeat rw [Nat.cast_add]
    ring_nf
  have hnonneg : (0 : ℚ) ≤ ((cap : ℚ) - a) * ((cap : ℚ) - b) := by
    apply mul_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast ha)
    · exact sub_nonneg.mpr (by exact_mod_cast hb)
  have hq :
      ((a.choose 2 + b.choose 2 : ℕ) : ℚ) ≤
        ((cap.choose 2 + (a + b - cap).choose 2 : ℕ) : ℚ) := by
    linarith
  exact_mod_cast hq

theorem cast_choose_two_cap_add_choose_two_sub_add_eq {a b cap : ℕ} (hcap : cap ≤ a) :
    ((cap.choose 2 + (a + b - cap).choose 2 : ℕ) : ℝ) =
      ((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ) +
        ((a - cap : ℕ) : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) := by
  have hsub : a + b - cap = (a - cap) + b := by
    omega
  rw [hsub, Nat.cast_add]
  rw [cast_choose_two_add_eq (a - cap) b]
  simp [Nat.cast_add, add_left_comm, add_comm]

theorem cast_choose_two_cap_add_choose_two_sub_add_le_one_add_mul {a b cap : ℕ} {ε : ℝ}
    (hcap : cap ≤ a)
    (herr :
      ((a - cap : ℕ) : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) ≤
        ε * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))) :
    ((cap.choose 2 + (a + b - cap).choose 2 : ℕ) : ℝ) ≤
      (1 + ε) * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
  calc
    ((cap.choose 2 + (a + b - cap).choose 2 : ℕ) : ℝ)
        = ((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ) +
            (((a - cap : ℕ) : ℝ) * b + ((b.choose 2 : ℕ) : ℝ)) := by
              simpa [add_assoc, add_left_comm, add_comm] using
                cast_choose_two_cap_add_choose_two_sub_add_eq (a := a) (b := b) (cap := cap) hcap
    _ ≤ ((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ) +
        ε * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
          gcongr
    _ = (1 + ε) * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
      ring

theorem cast_min_choose_two_add_le_one_add_mul_min {a b cap : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (hcap : cap ≤ a)
    (hleft :
      (a : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) ≤ ε * (((a.choose 2 : ℕ) : ℝ)))
    (hright :
      ((a - cap : ℕ) : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) ≤
        ε * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))) :
    ((min ((a + b).choose 2) (cap.choose 2 + (a + b - cap).choose 2) : ℕ) : ℝ) ≤
      (1 + ε) * ((min (a.choose 2) (cap.choose 2 + (a - cap).choose 2) : ℕ) : ℝ) := by
  have hfac : 0 ≤ 1 + ε := by linarith
  rw [Nat.cast_min, Nat.cast_min]
  calc
    min (((a + b).choose 2 : ℕ) : ℝ) (((cap.choose 2 + (a + b - cap).choose 2 : ℕ) : ℝ))
        ≤ min
            ((1 + ε) * (((a.choose 2 : ℕ) : ℝ)))
            ((1 + ε) * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))) := by
              apply min_le_min
              · exact cast_choose_two_add_le_one_add_mul_choose_two hleft
              · exact cast_choose_two_cap_add_choose_two_sub_add_le_one_add_mul hcap hright
    _ = (1 + ε) *
        min (((a.choose 2 : ℕ) : ℝ)) (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
          symm
          simpa using
            (mul_min_of_nonneg
              (((a.choose 2 : ℕ) : ℝ))
              (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))
              hfac : (1 + ε) *
                  min (((a.choose 2 : ℕ) : ℝ))
                    (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) =
                min
                  ((1 + ε) * (((a.choose 2 : ℕ) : ℝ)))
                  ((1 + ε) * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))))

theorem cast_choose_two_cap_add_choose_two_sub_add_le_one_add_mul_split {a u o cap : ℕ} {ε : ℝ}
    (hcap : cap ≤ a) (hu : u ≤ a - cap)
    (herr :
      ((3 : ℝ) / 2) * (((a - cap : ℕ) : ℝ) * u) +
          (((a - cap + u : ℕ) : ℝ) * o + ((o.choose 2 : ℕ) : ℝ)) ≤
        ε * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))) :
    ((cap.choose 2 + (a + u + o - cap).choose 2 : ℕ) : ℝ) ≤
      (1 + ε) * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
  let base : ℝ := (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))
  have hcap' : cap ≤ a + u := by omega
  have hsub : a + u - cap = a - cap + u := by omega
  have hsplitO :
      ((cap.choose 2 + (a + u + o - cap).choose 2 : ℕ) : ℝ) =
        ((cap.choose 2 + (a + u - cap).choose 2 : ℕ) : ℝ) +
          ((a - cap + u : ℕ) : ℝ) * o + ((o.choose 2 : ℕ) : ℝ) := by
    simpa [hsub, add_assoc, add_left_comm, add_comm] using
      cast_choose_two_cap_add_choose_two_sub_add_eq (a := a + u) (b := o) (cap := cap) hcap'
  have hsplitU :
      ((cap.choose 2 + (a + u - cap).choose 2 : ℕ) : ℝ) =
        base + (((a - cap : ℕ) : ℝ) * u + ((u.choose 2 : ℕ) : ℝ)) := by
    simpa [base, add_assoc, add_left_comm, add_comm] using
      cast_choose_two_cap_add_choose_two_sub_add_eq (a := a) (b := u) (cap := cap) hcap
  have hu' : ((u : ℕ) : ℝ) ≤ ((a - cap : ℕ) : ℝ) := by
    exact_mod_cast hu
  have hchooseU :
      ((u.choose 2 : ℕ) : ℝ) ≤ (u : ℝ) * ((a - cap : ℕ) : ℝ) / 2 := by
    simpa [mul_comm] using
      (cast_choose_two_le_half_mul_of_le (a := u) (T := ((a - cap : ℕ) : ℝ)) hu')
  have hlinearU :
      (((a - cap : ℕ) : ℝ) * u + ((u.choose 2 : ℕ) : ℝ)) ≤
        ((3 : ℝ) / 2) * (((a - cap : ℕ) : ℝ) * u) := by
    nlinarith
  calc
    ((cap.choose 2 + (a + u + o - cap).choose 2 : ℕ) : ℝ)
        = base + (((a - cap : ℕ) : ℝ) * u + ((u.choose 2 : ℕ) : ℝ)) +
            (((a - cap + u : ℕ) : ℝ) * o + ((o.choose 2 : ℕ) : ℝ)) := by
              rw [hsplitO, hsplitU]
              ring
    _ ≤ base + (((3 : ℝ) / 2) * (((a - cap : ℕ) : ℝ) * u)) +
          (((a - cap + u : ℕ) : ℝ) * o + ((o.choose 2 : ℕ) : ℝ)) := by
            nlinarith [hlinearU]
    _ ≤ base + ε * base := by
          nlinarith [herr]
    _ = (1 + ε) * base := by
      ring

theorem cast_min_choose_two_add_le_one_add_mul_min_of_split_right {a u o cap : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (hcap : cap ≤ a) (hu : u ≤ a - cap)
    (hleft :
      (a : ℝ) * (u + o) + (((u + o).choose 2 : ℕ) : ℝ) ≤ ε * (((a.choose 2 : ℕ) : ℝ)))
    (hright :
      ((3 : ℝ) / 2) * (((a - cap : ℕ) : ℝ) * u) +
          (((a - cap + u : ℕ) : ℝ) * o + ((o.choose 2 : ℕ) : ℝ)) ≤
        ε * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))) :
    ((min ((a + u + o).choose 2) (cap.choose 2 + (a + u + o - cap).choose 2) : ℕ) : ℝ) ≤
      (1 + ε) * ((min (a.choose 2) (cap.choose 2 + (a - cap).choose 2) : ℕ) : ℝ) := by
  have hfac : 0 ≤ 1 + ε := by linarith
  rw [Nat.cast_min, Nat.cast_min]
  calc
    min (((a + u + o).choose 2 : ℕ) : ℝ)
          (((cap.choose 2 + (a + u + o - cap).choose 2 : ℕ) : ℝ))
        ≤
          min
            ((1 + ε) * (((a.choose 2 : ℕ) : ℝ)))
            ((1 + ε) * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))) := by
              have hleft' :
                  (a : ℝ) * (((u + o : ℕ) : ℝ)) + (((u + o).choose 2 : ℕ) : ℝ) ≤
                    ε * (((a.choose 2 : ℕ) : ℝ)) := by
                simpa [Nat.cast_add] using hleft
              apply min_le_min
              · simpa [Nat.add_assoc] using
                  cast_choose_two_add_le_one_add_mul_choose_two (a := a) (b := u + o)
                    (ε := ε) hleft'
              · exact
                  cast_choose_two_cap_add_choose_two_sub_add_le_one_add_mul_split
                    (a := a) (u := u) (o := o) (cap := cap) hcap hu hright
    _ = (1 + ε) *
          min (((a.choose 2 : ℕ) : ℝ))
            (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
              symm
              simpa using
                (mul_min_of_nonneg
                  (((a.choose 2 : ℕ) : ℝ))
                  (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))
                  hfac : (1 + ε) *
                      min (((a.choose 2 : ℕ) : ℝ))
                        (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) =
                    min
                      ((1 + ε) * (((a.choose 2 : ℕ) : ℝ)))
                      ((1 + ε) * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ))))

theorem cast_choose_two_le_of_le {a b : ℕ} (h : a ≤ b) :
    ((a.choose 2 : ℕ) : ℝ) ≤ ((b.choose 2 : ℕ) : ℝ) := by
  exact_mod_cast Nat.choose_le_choose 2 h

theorem cast_mul_add_choose_two_le_of_le {a b B : ℕ} (hb : b ≤ B) :
    (a : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) ≤ (a : ℝ) * B + ((B.choose 2 : ℕ) : ℝ) := by
  have hb' : (b : ℝ) ≤ B := by
    exact_mod_cast hb
  have hchoose := cast_choose_two_le_of_le hb
  nlinarith

theorem cast_mul_add_choose_two_le_of_le_of_sq_bound {a b : ℕ} {W : ℝ}
    (hb : (b : ℝ) ≤ W) :
    (a : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) ≤ (a : ℝ) * W + W ^ 2 / 2 := by
  have hW : 0 ≤ W := le_trans (by positivity : (0 : ℝ) ≤ (b : ℝ)) hb
  have hmul : (a : ℝ) * b ≤ (a : ℝ) * W := by
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hchoose : ((b.choose 2 : ℕ) : ℝ) ≤ W ^ 2 / 2 := by
    calc
      ((b.choose 2 : ℕ) : ℝ) ≤ (b : ℝ) ^ 2 / 2 := by
        exact Twobites.cast_choose_two_le_sq_div_two b
      _ ≤ W ^ 2 / 2 := by
        have hsquare : (b : ℝ) ^ 2 ≤ W ^ 2 := by nlinarith
        nlinarith
  nlinarith

theorem cast_mul_add_choose_two_le_eps_mul_choose_two_of_le_of_three_mul_le
    {a b : ℕ} {ε : ℝ} (hb : b ≤ a)
    (hsmall : (3 : ℝ) * (b : ℝ) ≤ ε * ((a : ℝ) - 1)) :
    (a : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) ≤ ε * (((a.choose 2 : ℕ) : ℝ)) := by
  have hchoose : ((b.choose 2 : ℕ) : ℝ) ≤ (b : ℝ) * (a : ℝ) / 2 := by
    exact cast_choose_two_le_half_mul_of_le (by exact_mod_cast hb)
  have hbase : (a : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) ≤ ((3 : ℝ) / 2) * (a : ℝ) * b := by
    nlinarith
  have hfinal : ((3 : ℝ) / 2) * (a : ℝ) * b ≤ ε * ((a : ℝ) * ((a : ℝ) - 1) / 2) := by
    nlinarith
  calc
    (a : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) ≤ ((3 : ℝ) / 2) * (a : ℝ) * b := hbase
    _ ≤ ε * ((a : ℝ) * ((a : ℝ) - 1) / 2) := hfinal
    _ = ε * (((a.choose 2 : ℕ) : ℝ)) := by rw [Nat.cast_choose_two]

theorem cast_mul_add_choose_two_le_eps_mul_choose_two_cap_add_choose_two_sub_of_le_of_three_mul_le
    {a b cap : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hb : b ≤ a - cap)
    (hsmall : (3 : ℝ) * (b : ℝ) ≤ ε * (((a - cap : ℕ) : ℝ) - 1)) :
    ((a - cap : ℕ) : ℝ) * b + ((b.choose 2 : ℕ) : ℝ) ≤
      ε * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
  have hbase :
      (((a - cap : ℕ) : ℝ) * b + ((b.choose 2 : ℕ) : ℝ)) ≤
        ε * ((((a - cap).choose 2 : ℕ) : ℝ)) := by
    exact cast_mul_add_choose_two_le_eps_mul_choose_two_of_le_of_three_mul_le hb hsmall
  have hmono :
      ε * ((((a - cap).choose 2 : ℕ) : ℝ)) ≤
        ε * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
    have hnat : (a - cap).choose 2 ≤ cap.choose 2 + (a - cap).choose 2 := by
      exact Nat.le_add_left _ _
    have hcast :
        ((((a - cap).choose 2 : ℕ) : ℝ)) ≤
          (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_left hcast hε
  exact hbase.trans hmono

theorem real_mul_add_sq_half_le_eps_mul_choose_two_of_le_of_three_mul_le
    {a : ℕ} {W ε : ℝ} (hW : 0 ≤ W) (hbound : W ≤ (a : ℝ))
    (hsmall : (3 : ℝ) * W ≤ ε * ((a : ℝ) - 1)) :
    (a : ℝ) * W + W ^ 2 / 2 ≤ ε * (((a.choose 2 : ℕ) : ℝ)) := by
  have hbase : (a : ℝ) * W + W ^ 2 / 2 ≤ ((3 : ℝ) / 2) * (a : ℝ) * W := by
    nlinarith
  have hfinal : ((3 : ℝ) / 2) * (a : ℝ) * W ≤ ε * ((a : ℝ) * ((a : ℝ) - 1) / 2) := by
    nlinarith
  calc
    (a : ℝ) * W + W ^ 2 / 2 ≤ ((3 : ℝ) / 2) * (a : ℝ) * W := hbase
    _ ≤ ε * ((a : ℝ) * ((a : ℝ) - 1) / 2) := hfinal
    _ = ε * (((a.choose 2 : ℕ) : ℝ)) := by rw [Nat.cast_choose_two]

theorem real_mul_add_sq_half_le_eps_mul_choose_two_cap_add_choose_two_sub_of_le_of_three_mul_le
    {a cap : ℕ} {W ε : ℝ} (hε : 0 ≤ ε) (hW : 0 ≤ W)
    (hbound : W ≤ (((a - cap : ℕ) : ℝ)))
    (hsmall : (3 : ℝ) * W ≤ ε * ((((a - cap : ℕ) : ℝ) - 1))) :
    (((a - cap : ℕ) : ℝ) * W + W ^ 2 / 2) ≤
      ε * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
  have hbase :
      (((a - cap : ℕ) : ℝ) * W + W ^ 2 / 2) ≤
        ε * ((((a - cap).choose 2 : ℕ) : ℝ)) := by
    exact
      real_mul_add_sq_half_le_eps_mul_choose_two_of_le_of_three_mul_le
        hW hbound hsmall
  have hmono :
      ε * ((((a - cap).choose 2 : ℕ) : ℝ)) ≤
        ε * (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
    have hnat : (a - cap).choose 2 ≤ cap.choose 2 + (a - cap).choose 2 := by
      exact Nat.le_add_left _ _
    have hcast :
        ((((a - cap).choose 2 : ℕ) : ℝ)) ≤
          (((cap.choose 2 + (a - cap).choose 2 : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_left hcast hε
  exact hbase.trans hmono

theorem sum_choose_two_le_choose_two_cap_add_choose_two_sub_of_le {α : Type*} (A : Finset α)
    (f : α → ℕ) {cap : ℕ} (hcap : ∀ x ∈ A, f x ≤ cap) (hsum : cap ≤ ∑ x ∈ A, f x) :
    ∑ x ∈ A, (f x).choose 2 ≤ cap.choose 2 + ((∑ x ∈ A, f x) - cap).choose 2 := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      have hcap_le : cap ≤ 0 := by
        simpa using hsum
      have hcap0 : cap = 0 := Nat.eq_zero_of_le_zero hcap_le
      simp [hcap0]
  | @insert a s ha ih =>
      have haCap : f a ≤ cap := hcap a (by simp [ha])
      by_cases hs : cap ≤ ∑ x ∈ s, f x
      · have hsCap : ∀ x ∈ s, f x ≤ cap := by
          intro x hx
          exact hcap x (Finset.mem_insert_of_mem hx)
        calc
          ∑ x ∈ insert a s, (f x).choose 2 = (f a).choose 2 + ∑ x ∈ s, (f x).choose 2 := by
            simp [ha]
          _ ≤ (f a).choose 2 + (cap.choose 2 + ((∑ x ∈ s, f x) - cap).choose 2) := by
            gcongr
            exact ih hsCap hs
          _ = cap.choose 2 + ((f a).choose 2 + ((∑ x ∈ s, f x) - cap).choose 2) := by
            ac_rfl
          _ ≤ cap.choose 2 + (f a + ((∑ x ∈ s, f x) - cap)).choose 2 := by
            gcongr
            exact choose_two_add_le_choose_two_sum _ _
          _ = cap.choose 2 + ((∑ x ∈ insert a s, f x) - cap).choose 2 := by
            rw [Finset.sum_insert ha]
            rw [Nat.add_sub_assoc hs]
      · have hslt : ∑ x ∈ s, f x < cap := Nat.lt_of_not_ge hs
        have hs' : ∑ x ∈ s, f x ≤ cap := le_of_lt hslt
        have hsumInsert : cap ≤ f a + ∑ x ∈ s, f x := by
          simpa [Finset.sum_insert, ha] using hsum
        calc
          ∑ x ∈ insert a s, (f x).choose 2 = (f a).choose 2 + ∑ x ∈ s, (f x).choose 2 := by
            simp [ha]
          _ ≤ (f a).choose 2 + (∑ x ∈ s, f x).choose 2 := by
            gcongr
            exact sum_choose_two_le_choose_two_sum s f
          _ ≤ cap.choose 2 + (f a + ∑ x ∈ s, f x - cap).choose 2 := by
            exact choose_two_add_le_choose_two_cap_add_choose_two_sub haCap hs' hsumInsert
          _ = cap.choose 2 + ((∑ x ∈ insert a s, f x) - cap).choose 2 := by
            rw [Finset.sum_insert ha]

theorem partPairCount_le_partWeight_choose_two (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : C.partPairCount I A ≤ (C.partWeight I A).choose 2 := by
  unfold partPairCount partWeight
  simpa using sum_choose_two_le_choose_two_sum A (fun x => C.xCard I x)

theorem redProjectionPairCount_le_redProjectionWeight_choose_two (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.redProjectionPairCount I A ≤ (C.redProjectionWeight I A).choose 2 := by
  unfold redProjectionPairCount redProjectionWeight
  simpa using sum_choose_two_le_choose_two_sum A
    (fun x => (C.redProjectionImage I x).card)

theorem blueProjectionPairCount_le_blueProjectionWeight_choose_two (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.blueProjectionPairCount I A ≤ (C.blueProjectionWeight I A).choose 2 := by
  unfold blueProjectionPairCount blueProjectionWeight
  simpa using sum_choose_two_le_choose_two_sum A
    (fun x => (C.blueProjectionImage I x).card)

theorem redProjectionPairCount_le_choose_of_weight_le (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {W : ℕ}
    (hW : C.redProjectionWeight I A ≤ W) :
    C.redProjectionPairCount I A ≤ W.choose 2 := by
  exact (C.redProjectionPairCount_le_redProjectionWeight_choose_two I A).trans
    (Nat.choose_le_choose 2 hW)

theorem blueProjectionPairCount_le_choose_of_weight_le (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {W : ℕ}
    (hW : C.blueProjectionWeight I A ≤ W) :
    C.blueProjectionPairCount I A ≤ W.choose 2 := by
  exact (C.blueProjectionPairCount_le_blueProjectionWeight_choose_two I A).trans
    (Nat.choose_le_choose 2 hW)

theorem redProjectionPairCount_le_choose_two_cap_add_choose_two_sub_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {cap : ℕ}
    (hcap : ∀ x ∈ A, (C.redProjectionImage I x).card ≤ cap)
    (hsum : cap ≤ C.redProjectionWeight I A) :
    C.redProjectionPairCount I A ≤ cap.choose 2 + (C.redProjectionWeight I A - cap).choose 2 := by
  unfold redProjectionPairCount redProjectionWeight
  exact sum_choose_two_le_choose_two_cap_add_choose_two_sub_of_le A
    (fun x => (C.redProjectionImage I x).card) hcap hsum

theorem blueProjectionPairCount_le_choose_two_cap_add_choose_two_sub_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {cap : ℕ}
    (hcap : ∀ x ∈ A, (C.blueProjectionImage I x).card ≤ cap)
    (hsum : cap ≤ C.blueProjectionWeight I A) :
    C.blueProjectionPairCount I A ≤ cap.choose 2 + (C.blueProjectionWeight I A - cap).choose 2 := by
  unfold blueProjectionPairCount blueProjectionWeight
  exact sum_choose_two_le_choose_two_cap_add_choose_two_sub_of_le A
    (fun x => (C.blueProjectionImage I x).card) hcap hsum

theorem redProjectionPairCount_le_min_choose_of_weight_bounds (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {cap W : ℕ}
    (hcap : ∀ x ∈ A, (C.redProjectionImage I x).card ≤ cap)
    (hcapWeight : cap ≤ C.redProjectionWeight I A) (hweight : C.redProjectionWeight I A ≤ W) :
    C.redProjectionPairCount I A ≤ min (W.choose 2) (cap.choose 2 + (W - cap).choose 2) := by
  refine le_min ?_ ?_
  · exact C.redProjectionPairCount_le_choose_of_weight_le I A hweight
  · have hbase := C.redProjectionPairCount_le_choose_two_cap_add_choose_two_sub_of_le
      I A hcap hcapWeight
    have hsub : C.redProjectionWeight I A - cap ≤ W - cap := Nat.sub_le_sub_right hweight _
    exact hbase.trans (Nat.add_le_add_left (Nat.choose_le_choose 2 hsub) _)

theorem blueProjectionPairCount_le_min_choose_of_weight_bounds (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {cap W : ℕ}
    (hcap : ∀ x ∈ A, (C.blueProjectionImage I x).card ≤ cap)
    (hcapWeight : cap ≤ C.blueProjectionWeight I A) (hweight : C.blueProjectionWeight I A ≤ W) :
    C.blueProjectionPairCount I A ≤ min (W.choose 2) (cap.choose 2 + (W - cap).choose 2) := by
  refine le_min ?_ ?_
  · exact C.blueProjectionPairCount_le_choose_of_weight_le I A hweight
  · have hbase := C.blueProjectionPairCount_le_choose_two_cap_add_choose_two_sub_of_le
      I A hcap hcapWeight
    have hsub : C.blueProjectionWeight I A - cap ≤ W - cap := Nat.sub_le_sub_right hweight _
    exact hbase.trans (Nat.add_le_add_left (Nat.choose_le_choose 2 hsub) _)

theorem redProjectionWeight_le_partWeight (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : C.redProjectionWeight I A ≤ C.partWeight I A := by
  unfold redProjectionWeight partWeight
  simpa using (Finset.sum_le_sum fun x _ => C.card_redProjectionImage_le_xCard I x)

theorem blueProjectionWeight_le_partWeight (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : C.blueProjectionWeight I A ≤ C.partWeight I A := by
  unfold blueProjectionWeight partWeight
  simpa using (Finset.sum_le_sum fun x _ => C.card_blueProjectionImage_le_xCard I x)

theorem partPairCount_mono (C : ConstructionData n m) (I : Finset (Fin n))
    {A B : Finset (BaseVertex m)} (hAB : A ⊆ B) :
    C.partPairCount I A ≤ C.partPairCount I B := by
  unfold partPairCount
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB (by
    intro x hxA hxB
    positivity)

theorem redProjectionPairCount_mono (C : ConstructionData n m) (I : Finset (Fin n))
    {A B : Finset (BaseVertex m)} (hAB : A ⊆ B) :
    C.redProjectionPairCount I A ≤ C.redProjectionPairCount I B := by
  unfold redProjectionPairCount
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB (by
    intro x hxA hxB
    positivity)

theorem blueProjectionPairCount_mono (C : ConstructionData n m) (I : Finset (Fin n))
    {A B : Finset (BaseVertex m)} (hAB : A ⊆ B) :
    C.blueProjectionPairCount I A ≤ C.blueProjectionPairCount I B := by
  unfold blueProjectionPairCount
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB (by
    intro x hxA hxB
    positivity)

theorem partPairCount_union_of_disjoint (C : ConstructionData n m) (I : Finset (Fin n))
    {A B : Finset (BaseVertex m)} (hAB : Disjoint A B) :
    C.partPairCount I (A ∪ B) = C.partPairCount I A + C.partPairCount I B := by
  unfold partPairCount
  rw [Finset.sum_union hAB]

theorem redProjectionPairCount_union_of_disjoint (C : ConstructionData n m) (I : Finset (Fin n))
    {A B : Finset (BaseVertex m)} (hAB : Disjoint A B) :
    C.redProjectionPairCount I (A ∪ B) =
      C.redProjectionPairCount I A + C.redProjectionPairCount I B := by
  unfold redProjectionPairCount
  rw [Finset.sum_union hAB]

theorem blueProjectionPairCount_union_of_disjoint (C : ConstructionData n m)
    (I : Finset (Fin n)) {A B : Finset (BaseVertex m)} (hAB : Disjoint A B) :
    C.blueProjectionPairCount I (A ∪ B) =
      C.blueProjectionPairCount I A + C.blueProjectionPairCount I B := by
  unfold blueProjectionPairCount
  rw [Finset.sum_union hAB]

theorem redProjectionPairCount_le_partPairCount (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) :
    C.redProjectionPairCount I A ≤ C.partPairCount I A := by
  unfold redProjectionPairCount partPairCount
  refine Finset.sum_le_sum ?_
  intro x hx
  exact Nat.choose_le_choose 2 (C.card_redProjectionImage_le_xCard I x)

theorem blueProjectionPairCount_le_partPairCount (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) :
    C.blueProjectionPairCount I A ≤ C.partPairCount I A := by
  unfold blueProjectionPairCount partPairCount
  refine Finset.sum_le_sum ?_
  intro x hx
  exact Nat.choose_le_choose 2 (C.card_blueProjectionImage_le_xCard I x)

theorem partPairCount_filter_isRed_add_partPairCount_filter_isBlue
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.partPairCount I (A.filter IsRedBaseVertex) +
        C.partPairCount I (A.filter IsBlueBaseVertex) =
      C.partPairCount I A := by
  calc
    C.partPairCount I (A.filter IsRedBaseVertex) + C.partPairCount I (A.filter IsBlueBaseVertex) =
        C.partPairCount I ((A.filter IsRedBaseVertex) ∪ (A.filter IsBlueBaseVertex)) := by
          symm
          exact C.partPairCount_union_of_disjoint I (disjoint_filter_isRed_filter_isBlue A)
    _ = C.partPairCount I A := by
      rw [filter_isRed_union_filter_isBlue]

theorem disjoint_HPart_LPart_union_MPart_union_SPart_of_thresholds
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    Disjoint (C.HPart I) (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) := by
  refine Finset.disjoint_left.2 ?_
  intro x hxH hxA
  rcases Finset.mem_union.1 hxA with hxLM | hxS
  · rcases Finset.mem_union.1 hxLM with hxL | hxM
    · exact (Finset.disjoint_left.1 (C.disjoint_HPart_LPart I ε)) hxH hxL
    · exact (Finset.disjoint_left.1 (C.disjoint_HPart_MPart I ht21)) hxH hxM
  · have ht31 : Twobites.paperT3 ε n ≤ Twobites.paperT1 n := le_trans ht32 ht21
    exact (Finset.disjoint_left.1 (C.disjoint_HPart_SPart I ht31)) hxH hxS

theorem outside_section4F_subset_LPart_union_MPart_union_SPart_of_HPart_subset_section4F2
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε) :
    (Finset.univ.filter fun x : BaseVertex m => x ∉ C.section4F I ε) ⊆
      C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε := by
  intro x hx
  have hxNotF : x ∉ C.section4F I ε := (Finset.mem_filter.1 hx).2
  have hxBase : x ∈ C.baseImage I := by
    by_contra hxBase
    exact hxNotF <| C.mem_section4F.2 <| Or.inl <| C.mem_section4F0.2 ⟨by simp, hxBase⟩
  have hxNotH : x ∉ C.HPart I := by
    intro hxH
    have hxF2 : x ∈ C.section4F2 I ε := hHsubset (by simp [hxBase, hxH])
    exact hxNotF <| C.mem_section4F.2 <| Or.inr <| Or.inr hxF2
  rcases C.mem_HPart_or_mem_LPart_or_mem_MPart_or_mem_SPart I ε x with hxH | hxL | hxM | hxS
  · exact False.elim (hxNotH hxH)
  · simpa [Finset.mem_union] using
      (Or.inl hxL : x ∈ C.LPart I ε ∨ x ∈ C.MPart I ε ∨ x ∈ C.SPart I ε)
  · simpa [Finset.mem_union] using
      (Or.inr (Or.inl hxM) : x ∈ C.LPart I ε ∨ x ∈ C.MPart I ε ∨ x ∈ C.SPart I ε)
  · simpa [Finset.mem_union] using
      (Or.inr (Or.inr hxS) : x ∈ C.LPart I ε ∨ x ∈ C.MPart I ε ∨ x ∈ C.SPart I ε)

theorem outside_section4F_blue_subset_LMS_filter_isBlue_of_HPart_subset_section4F2
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε) :
    ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) ⊆
      ((C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε).filter IsBlueBaseVertex) := by
  intro x hx
  rcases Finset.mem_image.1 hx with ⟨b, hb, rfl⟩
  refine Finset.mem_filter.2 ?_
  refine ⟨?_, by simp [IsBlueBaseVertex]⟩
  exact
    C.outside_section4F_subset_LPart_union_MPart_union_SPart_of_HPart_subset_section4F2 I
      hHsubset (by simpa using hb)

theorem outside_section4F_red_subset_LMS_filter_isRed_of_HPart_subset_section4F2
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε) :
    ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ⊆
      ((C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε).filter IsRedBaseVertex) := by
  intro x hx
  rcases Finset.mem_image.1 hx with ⟨r, hr, rfl⟩
  refine Finset.mem_filter.2 ?_
  refine ⟨?_, by simp [IsRedBaseVertex]⟩
  exact
    C.outside_section4F_subset_LPart_union_MPart_union_SPart_of_HPart_subset_section4F2 I
      hHsubset (by simpa using hr)

set_option linter.style.longLine false in
theorem oppositeProjectionPairCount_sum_outside_section4F_le_partPairCount_LMS_of_HPart_subset_section4F2
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε) :
    C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) +
      C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
      C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) := by
  let A := C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε
  have hBlue :
      ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) ⊆
        A.filter IsBlueBaseVertex := by
    simpa [A] using
      C.outside_section4F_blue_subset_LMS_filter_isBlue_of_HPart_subset_section4F2 I hHsubset
  have hRed :
      ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ⊆
        A.filter IsRedBaseVertex := by
    simpa [A] using
      C.outside_section4F_red_subset_LMS_filter_isRed_of_HPart_subset_section4F2 I hHsubset
  calc
    C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) +
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
      C.redProjectionPairCount I (A.filter IsBlueBaseVertex) +
        C.blueProjectionPairCount I (A.filter IsRedBaseVertex) := by
          exact Nat.add_le_add (C.redProjectionPairCount_mono I hBlue)
            (C.blueProjectionPairCount_mono I hRed)
    _ ≤ C.partPairCount I (A.filter IsBlueBaseVertex) +
          C.partPairCount I (A.filter IsRedBaseVertex) := by
        exact Nat.add_le_add
          (C.redProjectionPairCount_le_partPairCount I (A.filter IsBlueBaseVertex))
          (C.blueProjectionPairCount_le_partPairCount I (A.filter IsRedBaseVertex))
    _ = C.partPairCount I A := by
        rw [add_comm, C.partPairCount_filter_isRed_add_partPairCount_filter_isBlue]

theorem redProjectionPairCount_baseImage_filter_isRed_le_partPairCount_LMS_filter_isRed_add_huge
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) ≤
      C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
        C.partPairCount I ((C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε).filter IsRedBaseVertex) := by
  let A := C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε
  have hsubset :
      (C.baseImage I).filter IsRedBaseVertex ⊆
        (C.HPart I).filter IsRedBaseVertex ∪ A.filter IsRedBaseVertex := by
    intro x hx
    have hxRed : IsRedBaseVertex x := (Finset.mem_filter.1 hx).2
    rcases C.mem_HPart_or_mem_LPart_or_mem_MPart_or_mem_SPart I ε x with hxH | hxL | hxM | hxS
    · exact Finset.mem_union.2 <| Or.inl <| by simp [hxH, hxRed]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxL, hxRed, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxM, hxRed, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxS, hxRed, Finset.mem_union]
  have hdisjHA :
      Disjoint (C.HPart I) A :=
    C.disjoint_HPart_LPart_union_MPart_union_SPart_of_thresholds I ht21 ht32
  have hdisj :
      Disjoint ((C.HPart I).filter IsRedBaseVertex) (A.filter IsRedBaseVertex) := by
    refine Finset.disjoint_left.2 ?_
    intro x hxH hxA
    exact (Finset.disjoint_left.1 hdisjHA) (Finset.mem_filter.1 hxH).1 (Finset.mem_filter.1 hxA).1
  calc
    C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) ≤
      C.redProjectionPairCount I
        (((C.HPart I).filter IsRedBaseVertex) ∪ (A.filter IsRedBaseVertex)) := by
          exact C.redProjectionPairCount_mono I hsubset
    _ = C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.redProjectionPairCount I (A.filter IsRedBaseVertex) := by
        rw [C.redProjectionPairCount_union_of_disjoint I hdisj]
    _ ≤ C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.partPairCount I (A.filter IsRedBaseVertex) := by
        exact Nat.add_le_add_left
          (C.redProjectionPairCount_le_partPairCount I (A.filter IsRedBaseVertex)) _

theorem blueProjectionPairCount_baseImage_filter_isBlue_le_partPairCount_LMS_filter_isBlue_add_huge
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex) ≤
      C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
        C.partPairCount I ((C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε).filter IsBlueBaseVertex) := by
  let A := C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε
  have hsubset :
      (C.baseImage I).filter IsBlueBaseVertex ⊆
        (C.HPart I).filter IsBlueBaseVertex ∪ A.filter IsBlueBaseVertex := by
    intro x hx
    have hxBlue : IsBlueBaseVertex x := (Finset.mem_filter.1 hx).2
    rcases C.mem_HPart_or_mem_LPart_or_mem_MPart_or_mem_SPart I ε x with hxH | hxL | hxM | hxS
    · exact Finset.mem_union.2 <| Or.inl <| by simp [hxH, hxBlue]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxL, hxBlue, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxM, hxBlue, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxS, hxBlue, Finset.mem_union]
  have hdisjHA :
      Disjoint (C.HPart I) A :=
    C.disjoint_HPart_LPart_union_MPart_union_SPart_of_thresholds I ht21 ht32
  have hdisj :
      Disjoint ((C.HPart I).filter IsBlueBaseVertex) (A.filter IsBlueBaseVertex) := by
    refine Finset.disjoint_left.2 ?_
    intro x hxH hxA
    exact (Finset.disjoint_left.1 hdisjHA) (Finset.mem_filter.1 hxH).1 (Finset.mem_filter.1 hxA).1
  calc
    C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex) ≤
      C.blueProjectionPairCount I
        (((C.HPart I).filter IsBlueBaseVertex) ∪ (A.filter IsBlueBaseVertex)) := by
          exact C.blueProjectionPairCount_mono I hsubset
    _ = C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
          C.blueProjectionPairCount I (A.filter IsBlueBaseVertex) := by
        rw [C.blueProjectionPairCount_union_of_disjoint I hdisj]
    _ ≤ C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
          C.partPairCount I (A.filter IsBlueBaseVertex) := by
        exact Nat.add_le_add_left
          (C.blueProjectionPairCount_le_partPairCount I (A.filter IsBlueBaseVertex)) _

theorem redProjectionPairCount_filter_isRed_le_partPairCount_LMS_filter_isRed_add_huge
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) ≤
      C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
        C.partPairCount I ((C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε).filter IsRedBaseVertex) := by
  let A := C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε
  have hsubset :
      ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) ⊆
        (C.HPart I).filter IsRedBaseVertex ∪ A.filter IsRedBaseVertex := by
    intro x hx
    have hxRed : IsRedBaseVertex x := (Finset.mem_filter.1 hx).2
    rcases C.mem_HPart_or_mem_LPart_or_mem_MPart_or_mem_SPart I ε x with hxH | hxL | hxM | hxS
    · exact Finset.mem_union.2 <| Or.inl <| by simp [hxH, hxRed]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxL, hxRed, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxM, hxRed, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxS, hxRed, Finset.mem_union]
  have hdisjHA :
      Disjoint (C.HPart I) A :=
    C.disjoint_HPart_LPart_union_MPart_union_SPart_of_thresholds I ht21 ht32
  have hdisj :
      Disjoint ((C.HPart I).filter IsRedBaseVertex) (A.filter IsRedBaseVertex) := by
    refine Finset.disjoint_left.2 ?_
    intro x hxH hxA
    exact (Finset.disjoint_left.1 hdisjHA) (Finset.mem_filter.1 hxH).1 (Finset.mem_filter.1 hxA).1
  calc
    C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) ≤
      C.redProjectionPairCount I
        (((C.HPart I).filter IsRedBaseVertex) ∪ (A.filter IsRedBaseVertex)) := by
          exact C.redProjectionPairCount_mono I hsubset
    _ = C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.redProjectionPairCount I (A.filter IsRedBaseVertex) := by
        rw [C.redProjectionPairCount_union_of_disjoint I hdisj]
    _ ≤ C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.partPairCount I (A.filter IsRedBaseVertex) := by
        exact Nat.add_le_add_left
          (C.redProjectionPairCount_le_partPairCount I (A.filter IsRedBaseVertex)) _

theorem redProjectionPairCount_filter_isBlue_le_partPairCount_LMS_filter_isBlue_add_huge
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) ≤
      C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
        C.partPairCount I ((C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε).filter IsBlueBaseVertex) := by
  let A := C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε
  have hsubset :
      ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) ⊆
        (C.HPart I).filter IsBlueBaseVertex ∪ A.filter IsBlueBaseVertex := by
    intro x hx
    have hxBlue : IsBlueBaseVertex x := (Finset.mem_filter.1 hx).2
    rcases C.mem_HPart_or_mem_LPart_or_mem_MPart_or_mem_SPart I ε x with hxH | hxL | hxM | hxS
    · exact Finset.mem_union.2 <| Or.inl <| by simp [hxH, hxBlue]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxL, hxBlue, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxM, hxBlue, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxS, hxBlue, Finset.mem_union]
  have hdisjHA :
      Disjoint (C.HPart I) A :=
    C.disjoint_HPart_LPart_union_MPart_union_SPart_of_thresholds I ht21 ht32
  have hdisj :
      Disjoint ((C.HPart I).filter IsBlueBaseVertex) (A.filter IsBlueBaseVertex) := by
    refine Finset.disjoint_left.2 ?_
    intro x hxH hxA
    exact (Finset.disjoint_left.1 hdisjHA) (Finset.mem_filter.1 hxH).1 (Finset.mem_filter.1 hxA).1
  calc
    C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) ≤
      C.redProjectionPairCount I
        (((C.HPart I).filter IsBlueBaseVertex) ∪ (A.filter IsBlueBaseVertex)) := by
          exact C.redProjectionPairCount_mono I hsubset
    _ = C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
          C.redProjectionPairCount I (A.filter IsBlueBaseVertex) := by
        rw [C.redProjectionPairCount_union_of_disjoint I hdisj]
    _ ≤ C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
          C.partPairCount I (A.filter IsBlueBaseVertex) := by
        exact Nat.add_le_add_left
          (C.redProjectionPairCount_le_partPairCount I (A.filter IsBlueBaseVertex)) _

theorem blueProjectionPairCount_filter_isRed_le_partPairCount_LMS_filter_isRed_add_huge
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) ≤
      C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
        C.partPairCount I ((C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε).filter IsRedBaseVertex) := by
  let A := C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε
  have hsubset :
      ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) ⊆
        (C.HPart I).filter IsRedBaseVertex ∪ A.filter IsRedBaseVertex := by
    intro x hx
    have hxRed : IsRedBaseVertex x := (Finset.mem_filter.1 hx).2
    rcases C.mem_HPart_or_mem_LPart_or_mem_MPart_or_mem_SPart I ε x with hxH | hxL | hxM | hxS
    · exact Finset.mem_union.2 <| Or.inl <| by simp [hxH, hxRed]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxL, hxRed, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxM, hxRed, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxS, hxRed, Finset.mem_union]
  have hdisjHA :
      Disjoint (C.HPart I) A :=
    C.disjoint_HPart_LPart_union_MPart_union_SPart_of_thresholds I ht21 ht32
  have hdisj :
      Disjoint ((C.HPart I).filter IsRedBaseVertex) (A.filter IsRedBaseVertex) := by
    refine Finset.disjoint_left.2 ?_
    intro x hxH hxA
    exact (Finset.disjoint_left.1 hdisjHA) (Finset.mem_filter.1 hxH).1 (Finset.mem_filter.1 hxA).1
  calc
    C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) ≤
      C.blueProjectionPairCount I
        (((C.HPart I).filter IsRedBaseVertex) ∪ (A.filter IsRedBaseVertex)) := by
          exact C.blueProjectionPairCount_mono I hsubset
    _ = C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I (A.filter IsRedBaseVertex) := by
        rw [C.blueProjectionPairCount_union_of_disjoint I hdisj]
    _ ≤ C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.partPairCount I (A.filter IsRedBaseVertex) := by
        exact Nat.add_le_add_left
          (C.blueProjectionPairCount_le_partPairCount I (A.filter IsRedBaseVertex)) _

theorem blueProjectionPairCount_filter_isBlue_le_partPairCount_LMS_filter_isBlue_add_huge
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) ≤
      C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
        C.partPairCount I ((C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε).filter IsBlueBaseVertex) := by
  let A := C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε
  have hsubset :
      ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) ⊆
        (C.HPart I).filter IsBlueBaseVertex ∪ A.filter IsBlueBaseVertex := by
    intro x hx
    have hxBlue : IsBlueBaseVertex x := (Finset.mem_filter.1 hx).2
    rcases C.mem_HPart_or_mem_LPart_or_mem_MPart_or_mem_SPart I ε x with hxH | hxL | hxM | hxS
    · exact Finset.mem_union.2 <| Or.inl <| by simp [hxH, hxBlue]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxL, hxBlue, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxM, hxBlue, Finset.mem_union]
    · exact Finset.mem_union.2 <| Or.inr <| by simp [A, hxS, hxBlue, Finset.mem_union]
  have hdisjHA :
      Disjoint (C.HPart I) A :=
    C.disjoint_HPart_LPart_union_MPart_union_SPart_of_thresholds I ht21 ht32
  have hdisj :
      Disjoint ((C.HPart I).filter IsBlueBaseVertex) (A.filter IsBlueBaseVertex) := by
    refine Finset.disjoint_left.2 ?_
    intro x hxH hxA
    exact (Finset.disjoint_left.1 hdisjHA) (Finset.mem_filter.1 hxH).1 (Finset.mem_filter.1 hxA).1
  calc
    C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) ≤
      C.blueProjectionPairCount I
        (((C.HPart I).filter IsBlueBaseVertex) ∪ (A.filter IsBlueBaseVertex)) := by
          exact C.blueProjectionPairCount_mono I hsubset
    _ = C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
          C.blueProjectionPairCount I (A.filter IsBlueBaseVertex) := by
        rw [C.blueProjectionPairCount_union_of_disjoint I hdisj]
    _ ≤ C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
          C.partPairCount I (A.filter IsBlueBaseVertex) := by
        exact Nat.add_le_add_left
          (C.blueProjectionPairCount_le_partPairCount I (A.filter IsBlueBaseVertex)) _

theorem projectionPairCount_sum_baseImage_le_partPairCount_LMS_add_huge_of_thresholds
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
      C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex) ≤
      C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
        C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) := by
  let A := C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε
  have hred :=
    C.redProjectionPairCount_baseImage_filter_isRed_le_partPairCount_LMS_filter_isRed_add_huge
      I ht21 ht32
  have hblue :=
    C.blueProjectionPairCount_baseImage_filter_isBlue_le_partPairCount_LMS_filter_isBlue_add_huge
      I ht21 ht32
  calc
    C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex) ≤
      (C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.partPairCount I (A.filter IsRedBaseVertex)) +
        (C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
          C.partPairCount I (A.filter IsBlueBaseVertex)) := by
            exact Nat.add_le_add hred hblue
    _ = C.partPairCount I (A.filter IsRedBaseVertex) +
          C.partPairCount I (A.filter IsBlueBaseVertex) +
            C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
              C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) := by
        omega
    _ = C.partPairCount I A +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) := by
        rw [C.partPairCount_filter_isRed_add_partPairCount_filter_isBlue]

theorem cast_partPairCount_LMS_le_sum_of_thresholds
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ} {L M S : ℝ}
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hL : ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤ L)
    (hM : ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤ M)
    (hS : ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤ S) :
    ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) ≤
      L + M + S := by
  have hMS :
      C.partPairCount I (C.MPart I ε ∪ C.SPart I ε) =
        C.partPairCount I (C.MPart I ε) + C.partPairCount I (C.SPart I ε) := by
    exact C.partPairCount_union_of_disjoint I (C.disjoint_MPart_SPart I ε)
  have hLMSDisj :
      Disjoint (C.LPart I ε) (C.MPart I ε ∪ C.SPart I ε) := by
    refine Finset.disjoint_left.2 ?_
    intro x hxL hxMS
    rcases Finset.mem_union.1 hxMS with hxM | hxS
    · exact (Finset.disjoint_left.1 (C.disjoint_LPart_MPart I ε)) hxL hxM
    · exact (Finset.disjoint_left.1 (C.disjoint_LPart_SPart I ht32)) hxL hxS
  have hUnion :
      C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) =
        C.partPairCount I (C.LPart I ε) + C.partPairCount I (C.MPart I ε) +
          C.partPairCount I (C.SPart I ε) := by
    calc
      C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) =
          C.partPairCount I (C.LPart I ε ∪ (C.MPart I ε ∪ C.SPart I ε)) := by
            rw [Finset.union_assoc]
      _ = C.partPairCount I (C.LPart I ε) + C.partPairCount I (C.MPart I ε ∪ C.SPart I ε) := by
            exact C.partPairCount_union_of_disjoint I hLMSDisj
      _ = C.partPairCount I (C.LPart I ε) +
            (C.partPairCount I (C.MPart I ε) + C.partPairCount I (C.SPart I ε)) := by
            rw [hMS]
      _ = C.partPairCount I (C.LPart I ε) + C.partPairCount I (C.MPart I ε) +
            C.partPairCount I (C.SPart I ε) := by
            omega
  have hUnionCast :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) =
        ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) +
          ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) +
          ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) := by
    exact_mod_cast hUnion
  rw [hUnionCast]
  linarith

set_option linter.style.longLine false in
theorem section4SecondStageLossNat_le_revealBudget_add_two_mul_partPairCount_LMS_add_huge
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    C.section4SecondStageLossNat I ε ≤
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
        2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
        C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) := by
  unfold section4SecondStageLossNat
  have hsame :=
    C.projectionPairCount_sum_baseImage_le_partPairCount_LMS_add_huge_of_thresholds I ht21 ht32
  have hopp :=
    C.oppositeProjectionPairCount_sum_outside_section4F_le_partPairCount_LMS_of_HPart_subset_section4F2
      I hHsubset
  omega

set_option linter.style.longLine false in
theorem section4SecondStageLossNat_add_witnessCaps_le_revealBudget_add_three_mul_partPairCount_LMS_add_huge
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    C.section4SecondStageLossNat I ε +
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) +
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
        3 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
        C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) := by
  have hloss :=
    C.section4SecondStageLossNat_le_revealBudget_add_two_mul_partPairCount_LMS_add_huge
      I hHsubset ht21 ht32
  have hopp :=
    C.oppositeProjectionPairCount_sum_outside_section4F_le_partPairCount_LMS_of_HPart_subset_section4F2
      I hHsubset
  omega

theorem redProjectionWeight_filter_isLeft_le_card_mul_of_univ_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {D : ℕ}
    (hD : ∀ r : Fin m, (C.redProjectionImage Finset.univ (Sum.inl r)).card ≤ D) :
    C.redProjectionWeight I (A.filter IsRedBaseVertex) ≤ (A.filter IsRedBaseVertex).card * D := by
  unfold redProjectionWeight
  calc
    ∑ x ∈ A.filter IsRedBaseVertex, (C.redProjectionImage I x).card ≤
        ∑ _x ∈ A.filter IsRedBaseVertex, D := by
      refine Finset.sum_le_sum ?_
      intro x hx
      rcases x with r | b
      · exact (C.card_redProjectionImage_le_univ I (Sum.inl r)).trans (hD r)
      · exfalso
        simpa using (Finset.mem_filter.1 hx).2
    _ = (A.filter IsRedBaseVertex).card * D := by
      simp

theorem blueProjectionWeight_filter_isRight_le_card_mul_of_univ_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {D : ℕ}
    (hD : ∀ b : Fin m, (C.blueProjectionImage Finset.univ (Sum.inr b)).card ≤ D) :
    C.blueProjectionWeight I (A.filter IsBlueBaseVertex) ≤
      (A.filter IsBlueBaseVertex).card * D := by
  unfold blueProjectionWeight
  calc
    ∑ x ∈ A.filter IsBlueBaseVertex, (C.blueProjectionImage I x).card ≤
        ∑ _x ∈ A.filter IsBlueBaseVertex, D := by
      refine Finset.sum_le_sum ?_
      intro x hx
      rcases x with r | b
      · exfalso
        simpa using (Finset.mem_filter.1 hx).2
      · exact (C.card_blueProjectionImage_le_univ I (Sum.inr b)).trans (hD b)
    _ = (A.filter IsBlueBaseVertex).card * D := by
      simp

theorem redProjectionWeight_filter_isLeft_le_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.redProjectionWeight I (A.filter IsRedBaseVertex) ≤
      (A.filter IsRedBaseVertex).card * degreeBound :=
  C.redProjectionWeight_filter_isLeft_le_card_mul_of_univ_bound I A hD.redProjectionBound

theorem blueProjectionWeight_filter_isRight_le_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.blueProjectionWeight I (A.filter IsBlueBaseVertex) ≤
      (A.filter IsBlueBaseVertex).card * degreeBound :=
  C.blueProjectionWeight_filter_isRight_le_card_mul_of_univ_bound I A hD.blueProjectionBound

theorem redProjectionWeight_filter_isLeft_le_of_goodEventD_of_card_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {bound : ℕ}
    (hA : (A.filter IsRedBaseVertex).card ≤ bound) :
    C.redProjectionWeight I (A.filter IsRedBaseVertex) ≤ bound * degreeBound :=
  (C.redProjectionWeight_filter_isLeft_le_of_goodEventD hD I A).trans
    (Nat.mul_le_mul_right _ hA)

theorem blueProjectionWeight_filter_isRight_le_of_goodEventD_of_card_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {bound : ℕ}
    (hA : (A.filter IsBlueBaseVertex).card ≤ bound) :
    C.blueProjectionWeight I (A.filter IsBlueBaseVertex) ≤ bound * degreeBound :=
  (C.blueProjectionWeight_filter_isRight_le_of_goodEventD hD I A).trans
    (Nat.mul_le_mul_right _ hA)

theorem blueProjectionWeight_filter_isLeft_le_card_blueProjectionUnion_add_choose_mul_of_goodEventD
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.blueProjectionWeight I (A.filter IsRedBaseVertex) ≤
      (C.blueProjectionUnion I (A.filter IsRedBaseVertex)).card +
        (A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound := by
  apply C.blueProjectionWeight_le_card_blueProjectionUnion_add_choose_mul_of_pairwise_inter_bound I
  intro x hx y hy hxy
  rcases x with r | b
  · rcases y with r' | b'
    · exact C.blueProjectionInter_card_le_of_goodEventD hD I (by
        intro hrr'
        apply hxy
        simp [hrr'])
    · exfalso
      simpa using (Finset.mem_filter.1 hy).2
  · exfalso
    simpa using (Finset.mem_filter.1 hx).2

theorem redProjectionWeight_filter_isRight_le_card_redProjectionUnion_add_choose_mul_of_goodEventD
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.redProjectionWeight I (A.filter IsBlueBaseVertex) ≤
      (C.redProjectionUnion I (A.filter IsBlueBaseVertex)).card +
        (A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound := by
  apply C.redProjectionWeight_le_card_redProjectionUnion_add_choose_mul_of_pairwise_inter_bound I
  intro x hx y hy hxy
  rcases x with r | b
  · exfalso
    simpa using (Finset.mem_filter.1 hx).2
  · rcases y with r' | b'
    · exfalso
      simpa using (Finset.mem_filter.1 hy).2
    · exact C.redProjectionInter_card_le_of_goodEventD hD I (by
        intro hbb'
        apply hxy
        simp [hbb'])

theorem blueProjectionPairCount_filter_isLeft_le_choose_of_goodEventD
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.blueProjectionPairCount I (A.filter IsRedBaseVertex) ≤
      ((C.blueProjectionUnion I (A.filter IsRedBaseVertex)).card +
        (A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound).choose 2 := by
  apply C.blueProjectionPairCount_le_choose_of_weight_le I
  exact blueProjectionWeight_filter_isLeft_le_card_blueProjectionUnion_add_choose_mul_of_goodEventD
    C hD I A

theorem redProjectionPairCount_filter_isRight_le_choose_of_goodEventD
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    C.redProjectionPairCount I (A.filter IsBlueBaseVertex) ≤
      ((C.redProjectionUnion I (A.filter IsBlueBaseVertex)).card +
        (A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound).choose 2 := by
  apply C.redProjectionPairCount_le_choose_of_weight_le I
  exact redProjectionWeight_filter_isRight_le_card_redProjectionUnion_add_choose_mul_of_goodEventD
    C hD I A

theorem blueProjectionPairCount_filter_isLeft_le_min_choose_union_error_of_goodEventD
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {cap : ℕ}
    (hcap : ∀ x ∈ A.filter IsRedBaseVertex, (C.blueProjectionImage I x).card ≤ cap)
    (hcapWeight : cap ≤ C.blueProjectionWeight I (A.filter IsRedBaseVertex)) :
    C.blueProjectionPairCount I (A.filter IsRedBaseVertex) ≤
      min
        (((C.blueProjectionUnion I (A.filter IsRedBaseVertex)).card +
          (A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound).choose 2)
        (cap.choose 2 +
          (((C.blueProjectionUnion I (A.filter IsRedBaseVertex)).card +
            (A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound) - cap).choose 2) := by
  apply C.blueProjectionPairCount_le_min_choose_of_weight_bounds I
    (A.filter IsRedBaseVertex) hcap hcapWeight
  exact blueProjectionWeight_filter_isLeft_le_card_blueProjectionUnion_add_choose_mul_of_goodEventD
    C hD I A

theorem redProjectionPairCount_filter_isRight_le_min_choose_union_error_of_goodEventD
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {cap : ℕ}
    (hcap : ∀ x ∈ A.filter IsBlueBaseVertex, (C.redProjectionImage I x).card ≤ cap)
    (hcapWeight : cap ≤ C.redProjectionWeight I (A.filter IsBlueBaseVertex)) :
    C.redProjectionPairCount I (A.filter IsBlueBaseVertex) ≤
      min
        (((C.redProjectionUnion I (A.filter IsBlueBaseVertex)).card +
          (A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound).choose 2)
        (cap.choose 2 +
          (((C.redProjectionUnion I (A.filter IsBlueBaseVertex)).card +
            (A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound) - cap).choose 2) := by
  apply C.redProjectionPairCount_le_min_choose_of_weight_bounds I
    (A.filter IsBlueBaseVertex) hcap hcapWeight
  exact redProjectionWeight_filter_isRight_le_card_redProjectionUnion_add_choose_mul_of_goodEventD
    C hD I A

theorem
    blueProjectionWeight_filter_isLeft_le_concrete_of_goodEventD_of_card_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {bound : ℕ}
    (hA : (A.filter IsRedBaseVertex).card ≤ bound) :
    C.blueProjectionWeight I (A.filter IsRedBaseVertex) ≤
      I.card - (C.redImage I).card + bound * degreeBound +
        (A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound := by
  have hUnion :
      (C.blueProjectionUnion I (A.filter IsRedBaseVertex)).card ≤
        I.card - (C.redImage I).card + bound * degreeBound := by
    calc
      (C.blueProjectionUnion I (A.filter IsRedBaseVertex)).card ≤
          I.card - (C.redImage I).card +
            (C.redProjectionUnion I (A.filter IsRedBaseVertex)).card := by
        exact C.card_blueProjectionUnion_le_card_I_sub_card_redImage_add_redProjectionUnion I
          (A.filter IsRedBaseVertex)
      _ ≤ I.card - (C.redImage I).card + bound * degreeBound := by
        gcongr
        calc
          (C.redProjectionUnion I (A.filter IsRedBaseVertex)).card ≤
              C.redProjectionWeight I (A.filter IsRedBaseVertex) := by
            exact C.card_redProjectionUnion_le_redProjectionWeight I (A.filter IsRedBaseVertex)
          _ ≤ bound * degreeBound := by
            exact C.redProjectionWeight_filter_isLeft_le_of_goodEventD_of_card_le hD I A hA
  have hbase :=
    C.blueProjectionWeight_filter_isLeft_le_card_blueProjectionUnion_add_choose_mul_of_goodEventD
      hD I A
  exact hbase.trans <| by
    simpa [add_assoc, add_left_comm, add_comm] using Nat.add_le_add_right hUnion
      ((A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound)

theorem
    redProjectionWeight_filter_isRight_le_concrete_of_goodEventD_of_card_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {bound : ℕ}
    (hA : (A.filter IsBlueBaseVertex).card ≤ bound) :
    C.redProjectionWeight I (A.filter IsBlueBaseVertex) ≤
      I.card - (C.blueImage I).card + bound * degreeBound +
        (A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound := by
  have hUnion :
      (C.redProjectionUnion I (A.filter IsBlueBaseVertex)).card ≤
        I.card - (C.blueImage I).card + bound * degreeBound := by
    calc
      (C.redProjectionUnion I (A.filter IsBlueBaseVertex)).card ≤
          I.card - (C.blueImage I).card +
            (C.blueProjectionUnion I (A.filter IsBlueBaseVertex)).card := by
        exact C.card_redProjectionUnion_le_card_I_sub_card_blueImage_add_blueProjectionUnion I
          (A.filter IsBlueBaseVertex)
      _ ≤ I.card - (C.blueImage I).card + bound * degreeBound := by
        gcongr
        calc
          (C.blueProjectionUnion I (A.filter IsBlueBaseVertex)).card ≤
              C.blueProjectionWeight I (A.filter IsBlueBaseVertex) := by
            exact C.card_blueProjectionUnion_le_blueProjectionWeight I (A.filter IsBlueBaseVertex)
          _ ≤ bound * degreeBound := by
            exact C.blueProjectionWeight_filter_isRight_le_of_goodEventD_of_card_le hD I A hA
  have hbase :=
    C.redProjectionWeight_filter_isRight_le_card_redProjectionUnion_add_choose_mul_of_goodEventD
      hD I A
  exact hbase.trans <| by
    simpa [add_assoc, add_left_comm, add_comm] using Nat.add_le_add_right hUnion
      ((A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound)

theorem
    blueProjectionPairCount_filter_isLeft_le_min_choose_concrete_of_goodEventD_of_card_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {bound cap : ℕ}
    (hA : (A.filter IsRedBaseVertex).card ≤ bound)
    (hcap : ∀ x ∈ A.filter IsRedBaseVertex, (C.blueProjectionImage I x).card ≤ cap)
    (hcapWeight : cap ≤ C.blueProjectionWeight I (A.filter IsRedBaseVertex)) :
    C.blueProjectionPairCount I (A.filter IsRedBaseVertex) ≤
      min
        ((I.card - (C.redImage I).card + bound * degreeBound +
          (A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound).choose 2)
        (cap.choose 2 +
          ((I.card - (C.redImage I).card + bound * degreeBound +
            (A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound) - cap).choose 2) := by
  apply C.blueProjectionPairCount_le_min_choose_of_weight_bounds I
    (A.filter IsRedBaseVertex) hcap hcapWeight
  exact
    C.blueProjectionWeight_filter_isLeft_le_concrete_of_goodEventD_of_card_le
      hD I A hA

theorem
    redProjectionPairCount_filter_isRight_le_min_choose_concrete_of_goodEventD_of_card_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {bound cap : ℕ}
    (hA : (A.filter IsBlueBaseVertex).card ≤ bound)
    (hcap : ∀ x ∈ A.filter IsBlueBaseVertex, (C.redProjectionImage I x).card ≤ cap)
    (hcapWeight : cap ≤ C.redProjectionWeight I (A.filter IsBlueBaseVertex)) :
    C.redProjectionPairCount I (A.filter IsBlueBaseVertex) ≤
      min
        ((I.card - (C.blueImage I).card + bound * degreeBound +
          (A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound).choose 2)
        (cap.choose 2 +
          ((I.card - (C.blueImage I).card + bound * degreeBound +
            (A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound) - cap).choose 2) := by
  apply C.redProjectionPairCount_le_min_choose_of_weight_bounds I
    (A.filter IsBlueBaseVertex) hcap hcapWeight
  exact
    C.redProjectionWeight_filter_isRight_le_concrete_of_goodEventD_of_card_le
      hD I A hA

theorem blueProjectionWeight_filter_isLeft_le_concrete_of_goodEventD_of_paperBound
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {κ : ℝ} {bound : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hA : (A.filter IsRedBaseVertex).card ≤ bound) :
    C.blueProjectionWeight I (A.filter IsRedBaseVertex) ≤
      Twobites.paperKNat κ n - (C.redImage I).card + bound * degreeBound +
        (A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound := by
  have hbase :=
    C.blueProjectionWeight_filter_isLeft_le_concrete_of_goodEventD_of_card_le hD I A hA
  have hsub :
      I.card - (C.redImage I).card ≤
        Twobites.paperKNat κ n - (C.redImage I).card := by
    exact Nat.sub_le_sub_right hI _
  exact hbase.trans <| by
    gcongr

theorem redProjectionWeight_filter_isRight_le_concrete_of_goodEventD_of_paperBound
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {κ : ℝ} {bound : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hA : (A.filter IsBlueBaseVertex).card ≤ bound) :
    C.redProjectionWeight I (A.filter IsBlueBaseVertex) ≤
      Twobites.paperKNat κ n - (C.blueImage I).card + bound * degreeBound +
        (A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound := by
  have hbase :=
    C.redProjectionWeight_filter_isRight_le_concrete_of_goodEventD_of_card_le hD I A hA
  have hsub :
      I.card - (C.blueImage I).card ≤
        Twobites.paperKNat κ n - (C.blueImage I).card := by
    exact Nat.sub_le_sub_right hI _
  exact hbase.trans <| by
    gcongr

theorem blueProjectionPairCount_filter_isLeft_le_min_choose_concrete_of_goodEventD_of_paperBound
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {κ : ℝ} {bound cap : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hA : (A.filter IsRedBaseVertex).card ≤ bound)
    (hcap : ∀ x ∈ A.filter IsRedBaseVertex, (C.blueProjectionImage I x).card ≤ cap)
    (hcapWeight : cap ≤ C.blueProjectionWeight I (A.filter IsRedBaseVertex)) :
    C.blueProjectionPairCount I (A.filter IsRedBaseVertex) ≤
      min
        ((Twobites.paperKNat κ n - (C.redImage I).card + bound * degreeBound +
          (A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound).choose 2)
        (cap.choose 2 +
          ((Twobites.paperKNat κ n - (C.redImage I).card + bound * degreeBound +
            (A.filter IsRedBaseVertex).card.choose 2 * projCodegreeBound) - cap).choose 2) := by
  apply C.blueProjectionPairCount_le_min_choose_of_weight_bounds I
    (A.filter IsRedBaseVertex) hcap hcapWeight
  exact C.blueProjectionWeight_filter_isLeft_le_concrete_of_goodEventD_of_paperBound
    hD I A hI hA

theorem redProjectionPairCount_filter_isRight_le_min_choose_concrete_of_goodEventD_of_paperBound
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {κ : ℝ} {bound cap : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hA : (A.filter IsBlueBaseVertex).card ≤ bound)
    (hcap : ∀ x ∈ A.filter IsBlueBaseVertex, (C.redProjectionImage I x).card ≤ cap)
    (hcapWeight : cap ≤ C.redProjectionWeight I (A.filter IsBlueBaseVertex)) :
    C.redProjectionPairCount I (A.filter IsBlueBaseVertex) ≤
      min
        ((Twobites.paperKNat κ n - (C.blueImage I).card + bound * degreeBound +
          (A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound).choose 2)
        (cap.choose 2 +
          ((Twobites.paperKNat κ n - (C.blueImage I).card + bound * degreeBound +
            (A.filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound) - cap).choose 2) := by
  apply C.redProjectionPairCount_le_min_choose_of_weight_bounds I
    (A.filter IsBlueBaseVertex) hcap hcapWeight
  exact C.redProjectionWeight_filter_isRight_le_concrete_of_goodEventD_of_paperBound
    hD I A hI hA

theorem card_filter_IsRedBaseVertex_le (A : Finset (BaseVertex m)) :
    (A.filter IsRedBaseVertex).card ≤ A.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem card_filter_IsBlueBaseVertex_le (A : Finset (BaseVertex m)) :
    (A.filter IsBlueBaseVertex).card ≤ A.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem cast_partPairCount_le_half_threshold_mul_partWeight (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {T : ℝ}
    (hA : ∀ x ∈ A, (C.xCard I x : ℝ) ≤ T) :
    ((C.partPairCount I A : ℕ) : ℝ) ≤ (T / 2) * (C.partWeight I A : ℕ) := by
  unfold partPairCount partWeight
  calc
    ((∑ x ∈ A, (C.xCard I x).choose 2 : ℕ) : ℝ)
        = ∑ x ∈ A, (((C.xCard I x).choose 2 : ℕ) : ℝ) := by
            simp
    _ ≤ ∑ x ∈ A, (C.xCard I x : ℝ) * T / 2 := by
      refine Finset.sum_le_sum ?_
      intro x hx
      exact cast_choose_two_le_half_mul_of_le (hA x hx)
    _ = (T / 2) * ∑ x ∈ A, (C.xCard I x : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring
    _ = (T / 2) * (C.partWeight I A : ℕ) := by
      simp [partWeight]

theorem cast_partPairCount_HPart_le (C : ConstructionData n m) (I : Finset (Fin n)) :
    ((C.partPairCount I (C.HPart I) : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (C.partWeight I (C.HPart I) : ℕ) := by
  apply C.cast_partPairCount_le_half_threshold_mul_partWeight
  intro x hx
  exact C.xCard_le_card_I_of_mem_HPart hx

theorem cast_partPairCount_LPart_le (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) :
    ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT1 n / 2) * (C.partWeight I (C.LPart I ε) : ℕ) := by
  apply C.cast_partPairCount_le_half_threshold_mul_partWeight
  intro x hx
  exact C.xCard_le_paperT1_of_mem_LPart hx

theorem cast_partPairCount_MPart_le (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) :
    ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT2 ε n / 2) * (C.partWeight I (C.MPart I ε) : ℕ) := by
  apply C.cast_partPairCount_le_half_threshold_mul_partWeight
  intro x hx
  exact C.xCard_le_paperT2_of_mem_MPart hx

theorem cast_partPairCount_SPart_le (C : ConstructionData n m) (I : Finset (Fin n)) (ε : ℝ) :
    ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT3 ε n / 2) * (C.partWeight I (C.SPart I ε) : ℕ) := by
  apply C.cast_partPairCount_le_half_threshold_mul_partWeight
  intro x hx
  exact C.xCard_le_paperT3_of_mem_SPart hx

theorem cast_largeContribution_le_of_partWeight_le (C : ConstructionData n m)
    (I : Finset (Fin n)) {ε W : ℝ} (hT1 : 0 ≤ Twobites.paperT1 n)
    (hW : (C.partWeight I (C.LPart I ε) : ℕ) ≤ W) :
    ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤ (Twobites.paperT1 n / 2) * W := by
  have hfac : 0 ≤ Twobites.paperT1 n / 2 := by
    linarith
  have hbase := C.cast_partPairCount_LPart_le I ε
  have hmul : (Twobites.paperT1 n / 2) * (C.partWeight I (C.LPart I ε) : ℕ) ≤
      (Twobites.paperT1 n / 2) * W := by
    exact mul_le_mul_of_nonneg_left hW hfac
  exact hbase.trans hmul

theorem cast_mediumContribution_le_of_partWeight_le (C : ConstructionData n m)
    (I : Finset (Fin n)) {ε W : ℝ}
    (hW : (C.partWeight I (C.MPart I ε) : ℕ) ≤ W) :
    ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤ (Twobites.paperT2 ε n / 2) * W := by
  have hfac : 0 ≤ Twobites.paperT2 ε n / 2 := by
    nlinarith [Twobites.paperT2_nonneg ε n]
  have hbase := C.cast_partPairCount_MPart_le I ε
  have hmul : (Twobites.paperT2 ε n / 2) * (C.partWeight I (C.MPart I ε) : ℕ) ≤
      (Twobites.paperT2 ε n / 2) * W := by
    exact mul_le_mul_of_nonneg_left hW hfac
  exact hbase.trans hmul

theorem cast_smallContribution_le_of_partWeight_le (C : ConstructionData n m)
    (I : Finset (Fin n)) {ε W : ℝ}
    (hW : (C.partWeight I (C.SPart I ε) : ℕ) ≤ W) :
    ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤ (Twobites.paperT3 ε n / 2) * W := by
  have hfac : 0 ≤ Twobites.paperT3 ε n / 2 := by
    nlinarith [Twobites.paperT3_nonneg ε n]
  have hbase := C.cast_partPairCount_SPart_le I ε
  have hmul : (Twobites.paperT3 ε n / 2) * (C.partWeight I (C.SPart I ε) : ℕ) ≤
      (Twobites.paperT3 ε n / 2) * W := by
    exact mul_le_mul_of_nonneg_left hW hfac
  exact hbase.trans hmul

theorem cast_largeContribution_le_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ} (hT1 : 0 ≤ Twobites.paperT1 n) :
    ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT1 n / 2) *
        (I.card + (C.LPart I ε).card.choose 2 * codegreeBound : ℕ) := by
  apply C.cast_largeContribution_le_of_partWeight_le I hT1
  exact_mod_cast C.partWeight_le_card_I_add_choose_mul_of_goodEventD hD I (C.LPart I ε)

theorem cast_mediumContribution_le_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ} :
    ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT2 ε n / 2) *
        (I.card + (C.MPart I ε).card.choose 2 * codegreeBound : ℕ) := by
  apply C.cast_mediumContribution_le_of_partWeight_le I
  exact_mod_cast C.partWeight_le_card_I_add_choose_mul_of_goodEventD hD I (C.MPart I ε)

theorem cast_smallContribution_le_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ} :
    ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT3 ε n / 2) *
        (I.card + (C.SPart I ε).card.choose 2 * codegreeBound : ℕ) := by
  apply C.cast_smallContribution_le_of_partWeight_le I
  exact_mod_cast C.partWeight_le_card_I_add_choose_mul_of_goodEventD hD I (C.SPart I ε)

theorem cast_largeContribution_le_of_goodEventD_of_card_le (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ} {bound : ℕ} (hT1 : 0 ≤ Twobites.paperT1 n)
    (hA : (C.LPart I ε).card ≤ bound) :
    ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT1 n / 2) * (I.card + bound.choose 2 * codegreeBound : ℕ) := by
  apply C.cast_largeContribution_le_of_partWeight_le I hT1
  exact_mod_cast C.partWeight_le_card_I_add_choose_mul_of_goodEventD_of_card_le hD I
    (C.LPart I ε) hA

theorem cast_mediumContribution_le_of_goodEventD_of_card_le (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ} {bound : ℕ} (hA : (C.MPart I ε).card ≤ bound) :
    ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT2 ε n / 2) * (I.card + bound.choose 2 * codegreeBound : ℕ) := by
  apply C.cast_mediumContribution_le_of_partWeight_le I
  exact_mod_cast C.partWeight_le_card_I_add_choose_mul_of_goodEventD_of_card_le hD I
    (C.MPart I ε) hA

theorem cast_smallContribution_le_of_goodEventD_of_card_le (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ} {bound : ℕ} (hA : (C.SPart I ε).card ≤ bound) :
    ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT3 ε n / 2) * (I.card + bound.choose 2 * codegreeBound : ℕ) := by
  apply C.cast_smallContribution_le_of_partWeight_le I
  exact_mod_cast C.partWeight_le_card_I_add_choose_mul_of_goodEventD_of_card_le hD I
    (C.SPart I ε) hA

theorem cast_largeContribution_le_of_goodEventD_of_witness (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ} {witnessSize : ℕ} (hT1 : 0 ≤ Twobites.paperT1 n)
    (hwitness :
      I.card < witnessSize * ⌈Twobites.paperT2 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT1 n / 2) * (I.card + witnessSize.choose 2 * codegreeBound : ℕ) := by
  apply C.cast_largeContribution_le_of_goodEventD_of_card_le hD I hT1
  exact Nat.le_of_lt (C.LPart_card_lt_of_goodEventD_of_lt hD I hwitness)

theorem cast_largeContribution_le_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε : ℝ} {witnessSize : ℕ} (hT1 : 0 ≤ Twobites.paperT1 n)
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT2 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT1 n / 2) *
        (Twobites.paperKNat κ n + witnessSize.choose 2 * codegreeBound : ℕ) := by
  have hbase := C.cast_largeContribution_le_of_goodEventD_of_witness hD I hT1
    (lt_of_le_of_lt hI hwitness)
  have hfac : 0 ≤ Twobites.paperT1 n / 2 := by
    linarith
  have hnat :
      I.card + witnessSize.choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n + witnessSize.choose 2 * codegreeBound :=
    Nat.add_le_add_right hI _
  have hmul :
      (Twobites.paperT1 n / 2) * (I.card + witnessSize.choose 2 * codegreeBound : ℕ) ≤
        (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n + witnessSize.choose 2 * codegreeBound : ℕ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnat) hfac
  exact hbase.trans hmul

theorem cast_mediumContribution_le_of_goodEventD_of_witness (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ε : ℝ} {witnessSize : ℕ}
    (hwitness :
      I.card < witnessSize * ⌈Twobites.paperT3 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT2 ε n / 2) * (I.card + witnessSize.choose 2 * codegreeBound : ℕ) := by
  apply C.cast_mediumContribution_le_of_goodEventD_of_card_le hD I
  exact Nat.le_of_lt (C.MPart_card_lt_of_goodEventD_of_lt hD I hwitness)

theorem cast_mediumContribution_le_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT3 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
      (Twobites.paperT2 ε n / 2) *
        (Twobites.paperKNat κ n + witnessSize.choose 2 * codegreeBound : ℕ) := by
  have hbase := C.cast_mediumContribution_le_of_goodEventD_of_witness hD I
    (lt_of_le_of_lt hI hwitness)
  have hfac : 0 ≤ Twobites.paperT2 ε n / 2 := by
    nlinarith [Twobites.paperT2_nonneg ε n]
  have hnat :
      I.card + witnessSize.choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n + witnessSize.choose 2 * codegreeBound :=
    Nat.add_le_add_right hI _
  have hmul :
      (Twobites.paperT2 ε n / 2) * (I.card + witnessSize.choose 2 * codegreeBound : ℕ) ≤
        (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + witnessSize.choose 2 * codegreeBound : ℕ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnat) hfac
  exact hbase.trans hmul

theorem cast_largeContribution_le_eps_mul_paperKSq_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε ε1 : ℝ} {witnessSize : ℕ}
    (hT1 : 0 ≤ Twobites.paperT1 n) (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT2 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hbound :
      (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n + witnessSize.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤ ε1 * Twobites.paperK κ n ^ 2 :=
  (C.cast_largeContribution_le_of_goodEventD_of_paperWitness hD I hT1 hI hwitness).trans hbound

theorem cast_mediumContribution_le_eps_mul_paperKSq_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε ε1 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT3 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hbound :
      (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + witnessSize.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤ ε1 * Twobites.paperK κ n ^ 2 :=
  (C.cast_mediumContribution_le_of_goodEventD_of_paperWitness hD I hI hwitness).trans hbound

/-- Paper Lemma `lem:large`, reduced to the remaining Section 3 witness arithmetic. -/
theorem paper_large_deterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε ε1 : ℝ} {witnessSize : ℕ}
    (hT1 : 0 ≤ Twobites.paperT1 n) (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT2 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hbound :
      (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n + witnessSize.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤ ε1 * Twobites.paperK κ n ^ 2 :=
  C.cast_largeContribution_le_eps_mul_paperKSq_of_goodEventD_of_paperWitness
    hD I hT1 hI hwitness hbound

/-- Paper Lemma `lem:med`, reduced to the remaining witness arithmetic coming from the medium
event analysis. -/
theorem paper_medium_deterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε ε1 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT3 ε n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hbound :
      (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + witnessSize.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤ ε1 * Twobites.paperK κ n ^ 2 :=
  C.cast_mediumContribution_le_eps_mul_paperKSq_of_goodEventD_of_paperWitness
    hD I hI hwitness hbound

/-- Paper Lemma `lem:small`, reduced to the remaining Section 3 small-event arithmetic. -/
theorem paper_small_deterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε ε1 : ℝ} {bound : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hS : (C.SPart I ε).card ≤ bound)
    (hbound :
      (Twobites.paperT3 ε n / 2) *
          (Twobites.paperKNat κ n + bound.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤ ε1 * Twobites.paperK κ n ^ 2 := by
  have hbase := C.cast_smallContribution_le_of_goodEventD_of_card_le hD I hS
  have hfac : 0 ≤ Twobites.paperT3 ε n / 2 := by
    nlinarith [Twobites.paperT3_nonneg ε n]
  have hnat :
      I.card + bound.choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n + bound.choose 2 * codegreeBound :=
    Nat.add_le_add_right hI _
  have hmul :
      (Twobites.paperT3 ε n / 2) * (I.card + bound.choose 2 * codegreeBound : ℕ) ≤
        (Twobites.paperT3 ε n / 2) *
          (Twobites.paperKNat κ n + bound.choose 2 * codegreeBound : ℕ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnat) hfac
  exact hbase.trans (hmul.trans hbound)

theorem cast_redProjectionPairCount_le_half_card_mul_redProjectionWeight
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    ((C.redProjectionPairCount I A : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (C.redProjectionWeight I A : ℕ) := by
  simpa [redProjectionPairCount, redProjectionWeight] using
    (cast_sum_choose_two_card_le_half_threshold_mul_sum_card
      (m := m) (F := fun x => C.redProjectionImage I x) A
      (fun x hx => by exact_mod_cast C.redProjectionImage_card_le_card_I I x))

theorem cast_blueProjectionPairCount_le_half_card_mul_blueProjectionWeight
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    ((C.blueProjectionPairCount I A : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (C.blueProjectionWeight I A : ℕ) := by
  simpa [blueProjectionPairCount, blueProjectionWeight] using
    (cast_sum_choose_two_card_le_half_threshold_mul_sum_card
      (m := m) (F := fun x => C.blueProjectionImage I x) A
      (fun x hx => by exact_mod_cast C.blueProjectionImage_card_le_card_I I x))

theorem cast_redProjectionPairCount_HPart_le (C : ConstructionData n m) (I : Finset (Fin n)) :
    ((C.redProjectionPairCount I (C.HPart I) : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (C.redProjectionWeight I (C.HPart I) : ℕ) :=
  C.cast_redProjectionPairCount_le_half_card_mul_redProjectionWeight I (C.HPart I)

theorem cast_blueProjectionPairCount_HPart_le (C : ConstructionData n m) (I : Finset (Fin n)) :
    ((C.blueProjectionPairCount I (C.HPart I) : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (C.blueProjectionWeight I (C.HPart I) : ℕ) :=
  C.cast_blueProjectionPairCount_le_half_card_mul_blueProjectionWeight I (C.HPart I)

theorem cast_redProjectionContribution_le_of_weight_le (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {W : ℝ}
    (hW : (C.redProjectionWeight I A : ℕ) ≤ W) :
    ((C.redProjectionPairCount I A : ℕ) : ℝ) ≤ ((I.card : ℝ) / 2) * W := by
  have hfac : 0 ≤ (I.card : ℝ) / 2 := by
    positivity
  have hbase := C.cast_redProjectionPairCount_le_half_card_mul_redProjectionWeight I A
  have hmul :
      ((I.card : ℝ) / 2) * (C.redProjectionWeight I A : ℕ) ≤ ((I.card : ℝ) / 2) * W := by
    exact mul_le_mul_of_nonneg_left hW hfac
  exact hbase.trans hmul

theorem cast_blueProjectionContribution_le_of_weight_le (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) {W : ℝ}
    (hW : (C.blueProjectionWeight I A : ℕ) ≤ W) :
    ((C.blueProjectionPairCount I A : ℕ) : ℝ) ≤ ((I.card : ℝ) / 2) * W := by
  have hfac : 0 ≤ (I.card : ℝ) / 2 := by
    positivity
  have hbase := C.cast_blueProjectionPairCount_le_half_card_mul_blueProjectionWeight I A
  have hmul :
      ((I.card : ℝ) / 2) * (C.blueProjectionWeight I A : ℕ) ≤ ((I.card : ℝ) / 2) * W := by
    exact mul_le_mul_of_nonneg_left hW hfac
  exact hbase.trans hmul

theorem cast_hugeRedContribution_le_of_weight_le (C : ConstructionData n m) (I : Finset (Fin n))
    {W : ℝ} (hW : (C.redProjectionWeight I (C.HPart I) : ℕ) ≤ W) :
    ((C.redProjectionPairCount I (C.HPart I) : ℕ) : ℝ) ≤ ((I.card : ℝ) / 2) * W :=
  C.cast_redProjectionContribution_le_of_weight_le I (C.HPart I) hW

theorem cast_hugeBlueContribution_le_of_weight_le (C : ConstructionData n m) (I : Finset (Fin n))
    {W : ℝ} (hW : (C.blueProjectionWeight I (C.HPart I) : ℕ) ≤ W) :
    ((C.blueProjectionPairCount I (C.HPart I) : ℕ) : ℝ) ≤ ((I.card : ℝ) / 2) * W :=
  C.cast_blueProjectionContribution_le_of_weight_le I (C.HPart I) hW

theorem cast_hugeRedContribution_filter_isLeft_le_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (((C.HPart I).filter IsRedBaseVertex).card * degreeBound : ℕ) := by
  apply C.cast_redProjectionContribution_le_of_weight_le I ((C.HPart I).filter IsRedBaseVertex)
  exact_mod_cast C.redProjectionWeight_filter_isLeft_le_of_goodEventD hD I (C.HPart I)

theorem cast_hugeBlueContribution_filter_isRight_le_of_goodEventD (C : ConstructionData n m)
    {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (((C.HPart I).filter IsBlueBaseVertex).card * degreeBound : ℕ) := by
  apply C.cast_blueProjectionContribution_le_of_weight_le I ((C.HPart I).filter IsBlueBaseVertex)
  exact_mod_cast C.blueProjectionWeight_filter_isRight_le_of_goodEventD hD I (C.HPart I)

theorem cast_hugeRedContribution_filter_isLeft_le_of_goodEventD_of_card_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {bound : ℕ}
    (hA : ((C.HPart I).filter IsRedBaseVertex).card ≤ bound) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (bound * degreeBound : ℕ) := by
  apply C.cast_redProjectionContribution_le_of_weight_le I ((C.HPart I).filter IsRedBaseVertex)
  exact_mod_cast C.redProjectionWeight_filter_isLeft_le_of_goodEventD_of_card_le hD I
    (C.HPart I) hA

theorem cast_hugeBlueContribution_filter_isRight_le_of_goodEventD_of_card_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {bound : ℕ}
    (hA : ((C.HPart I).filter IsBlueBaseVertex).card ≤ bound) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (bound * degreeBound : ℕ) := by
  apply C.cast_blueProjectionContribution_le_of_weight_le I ((C.HPart I).filter IsBlueBaseVertex)
  exact_mod_cast C.blueProjectionWeight_filter_isRight_le_of_goodEventD_of_card_le hD I
    (C.HPart I) hA

theorem cast_hugeRedContribution_filter_isLeft_le_of_goodEventD_of_HPart_witness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {witnessSize : ℕ}
    (hwitness :
      I.card < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (witnessSize * degreeBound : ℕ) := by
  apply C.cast_hugeRedContribution_filter_isLeft_le_of_goodEventD_of_card_le hD I
  exact (card_filter_IsRedBaseVertex_le (C.HPart I)).trans
    (Nat.le_of_lt (C.HPart_card_lt_of_goodEventD_of_lt hD I hwitness))

theorem cast_hugeRedContribution_filter_isLeft_le_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) := by
  have hbase := C.cast_hugeRedContribution_filter_isLeft_le_of_goodEventD_of_HPart_witness hD I
    (lt_of_le_of_lt hI hwitness)
  have hfac : 0 ≤ (witnessSize * degreeBound : ℕ) := by
    positivity
  have hI' : (I.card : ℝ) ≤ Twobites.paperKNat κ n := by
    exact_mod_cast hI
  have hmul :
      ((I.card : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) := by
    nlinarith
  exact hbase.trans hmul

theorem cast_hugeBlueContribution_filter_isRight_le_of_goodEventD_of_HPart_witness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {witnessSize : ℕ}
    (hwitness :
      I.card < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      ((I.card : ℝ) / 2) * (witnessSize * degreeBound : ℕ) := by
  apply C.cast_hugeBlueContribution_filter_isRight_le_of_goodEventD_of_card_le hD I
  exact (card_filter_IsBlueBaseVertex_le (C.HPart I)).trans
    (Nat.le_of_lt (C.HPart_card_lt_of_goodEventD_of_lt hD I hwitness))

theorem cast_hugeBlueContribution_filter_isRight_le_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) := by
  have hbase := C.cast_hugeBlueContribution_filter_isRight_le_of_goodEventD_of_HPart_witness hD I
    (lt_of_le_of_lt hI hwitness)
  have hfac : 0 ≤ (witnessSize * degreeBound : ℕ) := by
    positivity
  have hI' : (I.card : ℝ) ≤ Twobites.paperKNat κ n := by
    exact_mod_cast hI
  have hmul :
      ((I.card : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) := by
    nlinarith
  exact hbase.trans hmul

theorem cast_hugeRedContribution_filter_isLeft_le_eps_mul_paperKSq_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε1 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hbound :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      ε1 * Twobites.paperK κ n ^ 2 :=
  (C.cast_hugeRedContribution_filter_isLeft_le_of_goodEventD_of_paperWitness hD I hI hwitness).trans
    hbound

theorem cast_hugeBlueContribution_filter_isRight_le_eps_mul_paperKSq_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε1 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hbound :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      ε1 * Twobites.paperK κ n ^ 2 :=
  (C.cast_hugeBlueContribution_filter_isRight_le_of_goodEventD_of_paperWitness
    hD I hI hwitness).trans hbound

/-- The union-size slack in the `H_I ∩ V_R` cross-projection term coming from the
`|π_R (⋃ X_v(I))|` contribution in the paper proof. -/
def paperHugeBlueCrossUnionSlackNat (_C : ConstructionData n m) (_I : Finset (Fin n))
    (witnessSize degreeBound : ℕ) : ℕ :=
  witnessSize * degreeBound

/-- The projected-overlap slack in the `H_I ∩ V_R` cross-projection term coming from pairwise
intersections of the projected neighborhoods. -/
def paperHugeBlueCrossOverlapErrorNat (C : ConstructionData n m) (I : Finset (Fin n))
    (projCodegreeBound : ℕ) : ℕ :=
  ((C.HPart I).filter IsRedBaseVertex).card.choose 2 * projCodegreeBound

/-- The current natural-number upper bound for the `H_I ∩ V_R` cross-projection term, before the
final paper asymptotic simplifications are applied. It is the sum of the union-size slack and the
projected-overlap slack. -/
def paperHugeBlueCrossErrorNat (C : ConstructionData n m) (I : Finset (Fin n))
    (witnessSize degreeBound projCodegreeBound : ℕ) : ℕ :=
  C.paperHugeBlueCrossUnionSlackNat I witnessSize degreeBound +
    C.paperHugeBlueCrossOverlapErrorNat I projCodegreeBound

/-- The paper's capped right-hand branch for the `H_I ∩ V_R` cross-projection term. -/
def paperHugeBlueCrossRightTargetNat (C : ConstructionData n m) (I : Finset (Fin n)) (κ : ℝ)
    (cap : ℕ) : ℕ :=
  cap.choose 2 + ((Twobites.paperKNat κ n - (C.redImage I).card) - cap).choose 2

/-- The real-valued coercion of the capped right-hand branch for the `H_I ∩ V_R` cross term. -/
def paperHugeBlueCrossRightTarget (C : ConstructionData n m) (I : Finset (Fin n)) (κ : ℝ)
    (cap : ℕ) : ℝ :=
  (C.paperHugeBlueCrossRightTargetNat I κ cap : ℕ)

/-- The witness-size right-branch error condition for the `H_I ∩ V_R` cross term. -/
def paperHugeBlueCrossWitnessRightErrorProp (C : ConstructionData n m) (I : Finset (Fin n))
    (κ ε1 : ℝ) (witnessSize degreeBound projCodegreeBound cap : ℕ) : Prop :=
  (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) *
      (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
    (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
      ℕ) : ℝ) ≤
    ε1 * C.paperHugeBlueCrossRightTarget I κ cap)

/-- The split right-branch witness-error condition for the `H_I ∩ V_R` cross term, keeping the
union-size slack linear while only the projected-overlap slack pays a quadratic loss. -/
def paperHugeBlueCrossWitnessRightSplitErrorProp (C : ConstructionData n m) (I : Finset (Fin n))
    (κ ε1 : ℝ) (unionSlack overlapError cap : ℕ) : Prop :=
  (((3 : ℝ) / 2) *
        (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) *
          (unionSlack : ℝ)) +
      ((((Twobites.paperKNat κ n - (C.redImage I).card - cap + unionSlack : ℕ) : ℝ) *
          (overlapError : ℝ)) +
        (((overlapError.choose 2 : ℕ) : ℝ)))) ≤
    ε1 * C.paperHugeBlueCrossRightTarget I κ cap

/-- The current natural-number upper bound for the `H_I ∩ V_R` cross-projection term, before the
final paper asymptotic simplifications are applied. -/
def paperHugeBlueCrossConcreteBoundNat (C : ConstructionData n m) (I : Finset (Fin n)) (κ : ℝ)
    (witnessSize degreeBound projCodegreeBound cap : ℕ) : ℕ :=
  min
    ((Twobites.paperKNat κ n - (C.redImage I).card +
      C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2)
    (cap.choose 2 +
      ((Twobites.paperKNat κ n - (C.redImage I).card +
        C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound) - cap).choose 2)

/-- The paper's target natural-number expression for the `H_I ∩ V_R` cross-projection term. -/
def paperHugeBlueCrossTargetNat (C : ConstructionData n m) (I : Finset (Fin n)) (κ : ℝ)
    (cap : ℕ) : ℕ :=
  min
    ((Twobites.paperKNat κ n - (C.redImage I).card).choose 2)
    (C.paperHugeBlueCrossRightTargetNat I κ cap)

/-- The union-size slack in the `H_I ∩ V_B` cross-projection term coming from the
`|π_B (⋃ X_v(I))|` contribution in the paper proof. -/
def paperHugeRedCrossUnionSlackNat (_C : ConstructionData n m) (_I : Finset (Fin n))
    (witnessSize degreeBound : ℕ) : ℕ :=
  witnessSize * degreeBound

/-- The projected-overlap slack in the `H_I ∩ V_B` cross-projection term coming from pairwise
intersections of the projected neighborhoods. -/
def paperHugeRedCrossOverlapErrorNat (C : ConstructionData n m) (I : Finset (Fin n))
    (projCodegreeBound : ℕ) : ℕ :=
  ((C.HPart I).filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound

/-- The current natural-number upper bound for the `H_I ∩ V_B` cross-projection term, before the
final paper asymptotic simplifications are applied. It is the sum of the union-size slack and the
projected-overlap slack. -/
def paperHugeRedCrossErrorNat (C : ConstructionData n m) (I : Finset (Fin n))
    (witnessSize degreeBound projCodegreeBound : ℕ) : ℕ :=
  C.paperHugeRedCrossUnionSlackNat I witnessSize degreeBound +
    C.paperHugeRedCrossOverlapErrorNat I projCodegreeBound

/-- The paper's capped right-hand branch for the `H_I ∩ V_B` cross-projection term. -/
def paperHugeRedCrossRightTargetNat (C : ConstructionData n m) (I : Finset (Fin n)) (κ : ℝ)
    (cap : ℕ) : ℕ :=
  cap.choose 2 + ((Twobites.paperKNat κ n - (C.blueImage I).card) - cap).choose 2

/-- The real-valued coercion of the capped right-hand branch for the `H_I ∩ V_B` cross term. -/
def paperHugeRedCrossRightTarget (C : ConstructionData n m) (I : Finset (Fin n)) (κ : ℝ)
    (cap : ℕ) : ℝ :=
  (C.paperHugeRedCrossRightTargetNat I κ cap : ℕ)

/-- The witness-size right-branch error condition for the `H_I ∩ V_B` cross term. -/
def paperHugeRedCrossWitnessRightErrorProp (C : ConstructionData n m) (I : Finset (Fin n))
    (κ ε1 : ℝ) (witnessSize degreeBound projCodegreeBound cap : ℕ) : Prop :=
  (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) *
      (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
    (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
      ℕ) : ℝ) ≤
    ε1 * C.paperHugeRedCrossRightTarget I κ cap)

/-- The split right-branch witness-error condition for the `H_I ∩ V_B` cross term, keeping the
union-size slack linear while only the projected-overlap slack pays a quadratic loss. -/
def paperHugeRedCrossWitnessRightSplitErrorProp (C : ConstructionData n m) (I : Finset (Fin n))
    (κ ε1 : ℝ) (unionSlack overlapError cap : ℕ) : Prop :=
  (((3 : ℝ) / 2) *
        (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) *
          (unionSlack : ℝ)) +
      ((((Twobites.paperKNat κ n - (C.blueImage I).card - cap + unionSlack : ℕ) : ℝ) *
          (overlapError : ℝ)) +
        (((overlapError.choose 2 : ℕ) : ℝ)))) ≤
    ε1 * C.paperHugeRedCrossRightTarget I κ cap

/-- The current natural-number upper bound for the `H_I ∩ V_B` cross-projection term, before the
final paper asymptotic simplifications are applied. -/
def paperHugeRedCrossConcreteBoundNat (C : ConstructionData n m) (I : Finset (Fin n)) (κ : ℝ)
    (witnessSize degreeBound projCodegreeBound cap : ℕ) : ℕ :=
  min
    ((Twobites.paperKNat κ n - (C.blueImage I).card +
      C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2)
    (cap.choose 2 +
      ((Twobites.paperKNat κ n - (C.blueImage I).card +
        C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound) - cap).choose 2)

/-- The paper's target natural-number expression for the `H_I ∩ V_B` cross-projection term. -/
def paperHugeRedCrossTargetNat (C : ConstructionData n m) (I : Finset (Fin n)) (κ : ℝ)
    (cap : ℕ) : ℕ :=
  min
    ((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2)
    (C.paperHugeRedCrossRightTargetNat I κ cap)

/-- The paper's Section 4 target
`f(ℓ_R, ℓ_B) = choose(ℓ_R) + choose(ℓ_B) - target_R - target_B`,
expressed in the repo's natural-number bookkeeping with `ℓ_R = |π_R(I)|`,
`ℓ_B = |π_B(I)|`, and a generic huge-case cap parameter. -/
def paperSection4OpenPairTargetNat (C : ConstructionData n m) (I : Finset (Fin n)) (κ : ℝ)
    (cap : ℕ) : ℕ :=
  (C.redImage I).card.choose 2 + (C.blueImage I).card.choose 2 -
    C.paperHugeBlueCrossTargetNat I κ cap - C.paperHugeRedCrossTargetNat I κ cap

/-- The real-valued coercion of the paper's Section 4 target `f(ℓ_R,ℓ_B)`. -/
def paperSection4OpenPairTarget (C : ConstructionData n m) (I : Finset (Fin n)) (κ : ℝ)
    (cap : ℕ) : ℝ :=
  (C.paperSection4OpenPairTargetNat I κ cap : ℕ)

theorem paperSection4OpenPairTarget_lower_bound_of_targetBounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap blueBound redBound : ℕ}
    (hblue : C.paperHugeBlueCrossTargetNat I κ cap ≤ blueBound)
    (hred : C.paperHugeRedCrossTargetNat I κ cap ≤ redBound) :
    (((C.redImage I).card.choose 2 : ℕ) : ℝ) + (((C.blueImage I).card.choose 2 : ℕ) : ℝ) -
        (blueBound : ℝ) - (redBound : ℝ) ≤
      C.paperSection4OpenPairTarget I κ cap := by
  let totalChoose := (C.redImage I).card.choose 2 + (C.blueImage I).card.choose 2
  let totalTarget := C.paperHugeBlueCrossTargetNat I κ cap + C.paperHugeRedCrossTargetNat I κ cap
  let totalBound := blueBound + redBound
  have htargetLeBound : totalTarget ≤ totalBound := by
    dsimp [totalTarget, totalBound]
    exact Nat.add_le_add hblue hred
  have hsplit :
      (((C.redImage I).card.choose 2 : ℕ) : ℝ) + (((C.blueImage I).card.choose 2 : ℕ) : ℝ) -
          (blueBound : ℝ) - (redBound : ℝ) =
        (totalChoose : ℝ) - (totalBound : ℝ) := by
    dsimp [totalChoose, totalBound]
    rw [Nat.cast_add, Nat.cast_add]
    ring
  by_cases hle : totalTarget ≤ totalChoose
  · have hle' :
        C.paperHugeBlueCrossTargetNat I κ cap + C.paperHugeRedCrossTargetNat I κ cap ≤
          (C.redImage I).card.choose 2 + (C.blueImage I).card.choose 2 := by
      simpa [totalChoose, totalTarget] using hle
    have htarget :
        C.paperSection4OpenPairTarget I κ cap = (totalChoose : ℝ) - (totalTarget : ℝ) := by
      unfold paperSection4OpenPairTarget paperSection4OpenPairTargetNat totalChoose totalTarget
      rw [Nat.sub_sub, Nat.cast_sub hle', Nat.cast_add]
    have htargetLeBoundR : (totalTarget : ℝ) ≤ (totalBound : ℝ) := by
      exact_mod_cast htargetLeBound
    rw [hsplit]
    calc
      (totalChoose : ℝ) - (totalBound : ℝ) ≤ (totalChoose : ℝ) - (totalTarget : ℝ) := by
        linarith
      _ = C.paperSection4OpenPairTarget I κ cap := htarget.symm
  · have hzero : C.paperSection4OpenPairTarget I κ cap = 0 := by
      have hlt : totalChoose < totalTarget := Nat.lt_of_not_ge hle
      have hle' :
          (C.redImage I).card.choose 2 + (C.blueImage I).card.choose 2 ≤
            C.paperHugeBlueCrossTargetNat I κ cap + C.paperHugeRedCrossTargetNat I κ cap := by
        simpa [totalChoose, totalTarget] using hlt.le
      unfold paperSection4OpenPairTarget paperSection4OpenPairTargetNat
      rw [Nat.sub_sub, Nat.sub_eq_zero_of_le hle', Nat.cast_zero]
    have hnonpos :
        (((C.redImage I).card.choose 2 : ℕ) : ℝ) + (((C.blueImage I).card.choose 2 : ℕ) : ℝ) -
            (blueBound : ℝ) - (redBound : ℝ) ≤
          0 := by
      have hlt : totalChoose < totalTarget := Nat.lt_of_not_ge hle
      have hlt' : (totalChoose : ℝ) < (totalBound : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le hlt htargetLeBound)
      rw [hsplit]
      linarith
    nlinarith [hzero]

theorem paperSection4OpenPairTarget_lower_bound_of_blueLeft_of_redLeft
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap : ℕ} :
    (((C.redImage I).card.choose 2 : ℕ) : ℝ) + (((C.blueImage I).card.choose 2 : ℕ) : ℝ) -
        ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)) -
        ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)) ≤
      C.paperSection4OpenPairTarget I κ cap := by
  exact
    C.paperSection4OpenPairTarget_lower_bound_of_targetBounds (I := I)
      (blueBound := (Twobites.paperKNat κ n - (C.redImage I).card).choose 2)
      (redBound := (Twobites.paperKNat κ n - (C.blueImage I).card).choose 2)
      (by simp [paperHugeBlueCrossTargetNat])
      (by simp [paperHugeRedCrossTargetNat])

theorem paperSection4OpenPairTarget_lower_bound_of_blueLeft_of_redRight
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap : ℕ} :
    (((C.redImage I).card.choose 2 : ℕ) : ℝ) + (((C.blueImage I).card.choose 2 : ℕ) : ℝ) -
        ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)) -
        C.paperHugeRedCrossRightTarget I κ cap ≤
      C.paperSection4OpenPairTarget I κ cap := by
  exact
    C.paperSection4OpenPairTarget_lower_bound_of_targetBounds (I := I)
      (blueBound := (Twobites.paperKNat κ n - (C.redImage I).card).choose 2)
      (redBound := C.paperHugeRedCrossRightTargetNat I κ cap)
      (by simp [paperHugeBlueCrossTargetNat])
      (by simp [paperHugeRedCrossTargetNat])

theorem paperSection4OpenPairTarget_lower_bound_of_blueRight_of_redLeft
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap : ℕ} :
    (((C.redImage I).card.choose 2 : ℕ) : ℝ) + (((C.blueImage I).card.choose 2 : ℕ) : ℝ) -
        C.paperHugeBlueCrossRightTarget I κ cap -
        ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)) ≤
      C.paperSection4OpenPairTarget I κ cap := by
  exact
    C.paperSection4OpenPairTarget_lower_bound_of_targetBounds (I := I)
      (blueBound := C.paperHugeBlueCrossRightTargetNat I κ cap)
      (redBound := (Twobites.paperKNat κ n - (C.blueImage I).card).choose 2)
      (by simp [paperHugeBlueCrossTargetNat])
      (by simp [paperHugeRedCrossTargetNat])

theorem nat_le_paperSection4OpenPairTargetNat_of_blueLeft_of_redLeft
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap lossNat : ℕ}
    (hLoss :
      (lossNat : ℝ) ≤
        (((C.redImage I).card.choose 2 : ℕ) : ℝ) + (((C.blueImage I).card.choose 2 : ℕ) : ℝ) -
          ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)) -
          ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ))) :
    lossNat ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  have htarget :
      (lossNat : ℝ) ≤ C.paperSection4OpenPairTarget I κ cap := by
    exact hLoss.trans (C.paperSection4OpenPairTarget_lower_bound_of_blueLeft_of_redLeft I)
  have htarget' :
      (lossNat : ℝ) ≤ (C.paperSection4OpenPairTargetNat I κ cap : ℝ) := by
    simpa [paperSection4OpenPairTarget] using htarget
  exact_mod_cast htarget'

theorem nat_le_paperSection4OpenPairTargetNat_of_blueLeft_of_redRight
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap lossNat : ℕ}
    (hLoss :
      (lossNat : ℝ) ≤
        (((C.redImage I).card.choose 2 : ℕ) : ℝ) + (((C.blueImage I).card.choose 2 : ℕ) : ℝ) -
          ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)) -
          C.paperHugeRedCrossRightTarget I κ cap) :
    lossNat ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  have htarget :
      (lossNat : ℝ) ≤ C.paperSection4OpenPairTarget I κ cap := by
    exact hLoss.trans (C.paperSection4OpenPairTarget_lower_bound_of_blueLeft_of_redRight I)
  have htarget' :
      (lossNat : ℝ) ≤ (C.paperSection4OpenPairTargetNat I κ cap : ℝ) := by
    simpa [paperSection4OpenPairTarget] using htarget
  exact_mod_cast htarget'

theorem nat_le_paperSection4OpenPairTargetNat_of_blueRight_of_redLeft
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap lossNat : ℕ}
    (hLoss :
      (lossNat : ℝ) ≤
        (((C.redImage I).card.choose 2 : ℕ) : ℝ) + (((C.blueImage I).card.choose 2 : ℕ) : ℝ) -
          C.paperHugeBlueCrossRightTarget I κ cap -
          ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ))) :
    lossNat ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  have htarget :
      (lossNat : ℝ) ≤ C.paperSection4OpenPairTarget I κ cap := by
    exact hLoss.trans (C.paperSection4OpenPairTarget_lower_bound_of_blueRight_of_redLeft I)
  have htarget' :
      (lossNat : ℝ) ≤ (C.paperSection4OpenPairTargetNat I κ cap : ℝ) := by
    simpa [paperSection4OpenPairTarget] using htarget
  exact_mod_cast htarget'

/-- The combined manuscript-scale deterministic loss term that remains to be dominated by the
Section 4 target in `lem:RISI`. -/
def paperRISILossNat (κ ε1 : ℝ) (n : ℕ) : ℕ :=
  ⌈9 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ + ⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊

theorem paperRISILossNat_le_natCeil_nineteen_mul_eps_mul_paperKSq_add_one
    {κ ε1 : ℝ} (n : ℕ) (hε1 : 0 ≤ ε1) :
    paperRISILossNat κ ε1 n ≤ ⌈19 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ + 1 := by
  have h9 :
      0 ≤ 9 * (ε1 * Twobites.paperK κ n ^ 2) := by
    nlinarith [sq_nonneg (Twobites.paperK κ n)]
  have h10 :
      0 ≤ 10 * (ε1 * Twobites.paperK κ n ^ 2) := by
    nlinarith [sq_nonneg (Twobites.paperK κ n)]
  calc
    paperRISILossNat κ ε1 n =
        ⌈9 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ +
          ⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ := rfl
    _ ≤ ⌈9 * (ε1 * Twobites.paperK κ n ^ 2) +
          10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ + 1 := by
      exact Twobites.natCeil_add_natCeil_le_natCeil_add_one h9 h10
    _ = ⌈19 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ + 1 := by ring_nf

theorem paperSection4Branch_blueLeft_redLeft_eq
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat κ n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat κ n) :
    ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
          Twobites.paperKNat κ n) *
        ((Twobites.paperKNat κ n : ℝ) - 1) =
      ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
        (((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ) -
        (((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ) := by
  rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
  rw [Nat.cast_add, Nat.cast_sub hred, Nat.cast_sub hblue]
  ring

theorem paperSection4Branch_blueLeft_redRight_eq
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap : ℕ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat κ n)
    (hblueCap : (C.blueImage I).card + cap ≤ Twobites.paperKNat κ n) :
    ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
          Twobites.paperKNat κ n) *
        ((Twobites.paperKNat κ n : ℝ) - 1) +
      (cap : ℝ) * ((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) =
      ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
        (((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ) -
        C.paperHugeRedCrossRightTarget I κ cap := by
  have hredCast :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) =
        Twobites.paperKNat κ n - (C.redImage I).card := by
    exact Nat.cast_sub hred
  have hblueCapNat :
      (Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) =
        Twobites.paperKNat κ n - ((C.blueImage I).card + cap) := by
    omega
  have hblueCapCast :
      ((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) =
        Twobites.paperKNat κ n - (C.blueImage I).card - cap := by
    rw [hblueCapNat, Nat.cast_sub hblueCap, Nat.cast_add]
    ring
  unfold ConstructionData.paperHugeRedCrossRightTarget
  unfold ConstructionData.paperHugeRedCrossRightTargetNat
  repeat rw [Nat.cast_add]
  repeat rw [Nat.cast_choose_two]
  rw [hredCast, hblueCapCast]
  ring_nf

theorem paperSection4Branch_blueRight_redLeft_eq
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap : ℕ}
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat κ n)
    (hredCap : (C.redImage I).card + cap ≤ Twobites.paperKNat κ n) :
    ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
          Twobites.paperKNat κ n) *
        ((Twobites.paperKNat κ n : ℝ) - 1) +
      (cap : ℝ) * ((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) =
      ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
        C.paperHugeBlueCrossRightTarget I κ cap -
        (((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ) := by
  have hblueCast :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) =
        Twobites.paperKNat κ n - (C.blueImage I).card := by
    exact Nat.cast_sub hblue
  have hredCapNat :
      (Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) =
        Twobites.paperKNat κ n - ((C.redImage I).card + cap) := by
    omega
  have hredCapCast :
      ((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) =
        Twobites.paperKNat κ n - (C.redImage I).card - cap := by
    rw [hredCapNat, Nat.cast_sub hredCap, Nat.cast_add]
    ring
  unfold ConstructionData.paperHugeBlueCrossRightTarget
  unfold ConstructionData.paperHugeBlueCrossRightTargetNat
  repeat rw [Nat.cast_add]
  repeat rw [Nat.cast_choose_two]
  rw [hblueCast, hredCapCast]
  ring_nf

theorem paper_risi_hLossGap_of_blueLeft_of_redLeft
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap : ℕ}
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
          (((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ) -
          (((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)) :
    paperRISILossNat κ ε1 n ≤
      C.paperSection4OpenPairTargetNat I κ cap := by
  exact
    C.nat_le_paperSection4OpenPairTargetNat_of_blueLeft_of_redLeft (I := I) (cap := cap)
      (lossNat := paperRISILossNat κ ε1 n) hLoss

theorem paper_risi_hLossGap_of_blueLeft_of_redRight
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap : ℕ}
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
          (((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ) -
          C.paperHugeRedCrossRightTarget I κ cap) :
    paperRISILossNat κ ε1 n ≤
      C.paperSection4OpenPairTargetNat I κ cap := by
  exact
    C.nat_le_paperSection4OpenPairTargetNat_of_blueLeft_of_redRight (I := I) (cap := cap)
      (lossNat := paperRISILossNat κ ε1 n) hLoss

theorem paper_risi_hLossGap_of_blueRight_of_redLeft
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap : ℕ}
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
          C.paperHugeBlueCrossRightTarget I κ cap -
          (((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)) :
    paperRISILossNat κ ε1 n ≤
      C.paperSection4OpenPairTargetNat I κ cap := by
  exact
    C.nat_le_paperSection4OpenPairTargetNat_of_blueRight_of_redLeft (I := I) (cap := cap)
      (lossNat := paperRISILossNat κ ε1 n) hLoss

theorem paper_risi_hLossGap_of_blueLeft_of_redLeft_sumGap
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap : ℕ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat κ n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat κ n)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
            Twobites.paperKNat κ n) *
          ((Twobites.paperKNat κ n : ℝ) - 1)) :
    paperRISILossNat κ ε1 n ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  have hBranch :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
          (((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ) -
          (((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ) := by
    calc
      (paperRISILossNat κ ε1 n : ℝ) ≤
          ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
              Twobites.paperKNat κ n) *
            ((Twobites.paperKNat κ n : ℝ) - 1) := hLoss
      _ =
          ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
            (((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ) -
            (((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ) :=
          C.paperSection4Branch_blueLeft_redLeft_eq I hred hblue
  exact C.paper_risi_hLossGap_of_blueLeft_of_redLeft I (cap := cap) hBranch

theorem paper_risi_hLossGap_of_blueLeft_of_redLeft_natGap
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap gap : ℕ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat κ n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat κ n)
    (hgap :
      Twobites.paperKNat κ n + gap ≤ (C.redImage I).card + (C.blueImage I).card)
    (hLoss : paperRISILossNat κ ε1 n ≤ gap * (Twobites.paperKNat κ n - 1)) :
    paperRISILossNat κ ε1 n ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  have hsumNat :
      gap ≤ (C.redImage I).card + (C.blueImage I).card - Twobites.paperKNat κ n := by
    omega
  have hsumLe :
      Twobites.paperKNat κ n ≤ (C.redImage I).card + (C.blueImage I).card := by
    omega
  by_cases hknat : 1 ≤ Twobites.paperKNat κ n
  · have hLossReal :
        (paperRISILossNat κ ε1 n : ℝ) ≤
          ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
              Twobites.paperKNat κ n) *
            ((Twobites.paperKNat κ n : ℝ) - 1) := by
      have hmulNat :
          gap * (Twobites.paperKNat κ n - 1) ≤
            ((C.redImage I).card + (C.blueImage I).card - Twobites.paperKNat κ n) *
              (Twobites.paperKNat κ n - 1) := by
        exact Nat.mul_le_mul_right (Twobites.paperKNat κ n - 1) hsumNat
      calc
        (paperRISILossNat κ ε1 n : ℝ) ≤
            (gap * (Twobites.paperKNat κ n - 1) : ℕ) := by
          exact_mod_cast hLoss
        _ ≤
            (((C.redImage I).card + (C.blueImage I).card - Twobites.paperKNat κ n) *
                (Twobites.paperKNat κ n - 1) : ℕ) := by
          exact_mod_cast hmulNat
        _ =
            ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
                Twobites.paperKNat κ n) *
              ((Twobites.paperKNat κ n : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub hsumLe, Nat.cast_sub hknat]
          ring
    exact C.paper_risi_hLossGap_of_blueLeft_of_redLeft_sumGap I hred hblue hLossReal
  · have hk0 : Twobites.paperKNat κ n = 0 := by omega
    have hred0 : (C.redImage I).card = 0 := by omega
    have hblue0 : (C.blueImage I).card = 0 := by omega
    have hgap0 : gap = 0 := by omega
    have hLoss0 : paperRISILossNat κ ε1 n = 0 := by
      have : paperRISILossNat κ ε1 n ≤ 0 := by simpa [hk0, hgap0] using hLoss
      omega
    simp [hLoss0]

theorem paper_risi_hLossGap_of_blueLeft_of_redRight_sumGap
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap : ℕ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat κ n)
    (hblueCap : (C.blueImage I).card + cap ≤ Twobites.paperKNat κ n)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
            Twobites.paperKNat κ n) *
          ((Twobites.paperKNat κ n : ℝ) - 1) +
        (cap : ℝ) * ((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ)) :
    paperRISILossNat κ ε1 n ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  have hBranch :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
          (((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ) -
          C.paperHugeRedCrossRightTarget I κ cap := by
    calc
      (paperRISILossNat κ ε1 n : ℝ) ≤
          ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
              Twobites.paperKNat κ n) *
            ((Twobites.paperKNat κ n : ℝ) - 1) +
          (cap : ℝ) * ((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) := hLoss
      _ =
          ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
            (((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ) -
            C.paperHugeRedCrossRightTarget I κ cap :=
          C.paperSection4Branch_blueLeft_redRight_eq I hred hblueCap
  exact C.paper_risi_hLossGap_of_blueLeft_of_redRight I (cap := cap) hBranch

theorem paper_risi_hLossGap_of_blueLeft_of_redRight_natDeficit
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap deficit gap : ℕ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat κ n)
    (hblueCap : (C.blueImage I).card + cap ≤ Twobites.paperKNat κ n)
    (hsumDef :
      (C.redImage I).card + (C.blueImage I).card + deficit = Twobites.paperKNat κ n)
    (hblueGap :
      (C.blueImage I).card + cap + gap = Twobites.paperKNat κ n)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) +
          (deficit : ℝ) * ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (cap : ℝ) * (gap : ℝ)) :
    paperRISILossNat κ ε1 n ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  have hsumEq :
      (C.redImage I).card + (C.blueImage I).card =
        Twobites.paperKNat κ n - deficit := by
    omega
  have hgapEq :
      Twobites.paperKNat κ n - (C.blueImage I).card - cap = gap := by
    omega
  have hLossReal :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
            Twobites.paperKNat κ n) *
          ((Twobites.paperKNat κ n : ℝ) - 1) +
        (cap : ℝ) * ((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) := by
    have hdefLe : deficit ≤ Twobites.paperKNat κ n := by
      omega
    calc
      (paperRISILossNat κ ε1 n : ℝ) ≤
          (cap : ℝ) * (gap : ℝ) -
            (deficit : ℝ) * ((Twobites.paperKNat κ n : ℝ) - 1) := by
        linarith
      _ =
          ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
              Twobites.paperKNat κ n) *
            ((Twobites.paperKNat κ n : ℝ) - 1) +
          (cap : ℝ) * ((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) := by
        rw [hgapEq, hsumEq, Nat.cast_sub hdefLe]
        ring
  exact C.paper_risi_hLossGap_of_blueLeft_of_redRight_sumGap I hred hblueCap hLossReal

theorem paper_risi_hLossGap_of_blueLeft_of_redRight_subGap
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap : ℕ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat κ n)
    (hblueCap : (C.blueImage I).card + cap ≤ Twobites.paperKNat κ n)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (cap : ℝ) *
          ((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ)) :
    paperRISILossNat κ ε1 n ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  by_cases hknat : 1 ≤ Twobites.paperKNat κ n
  · have hfactor : 0 ≤ (Twobites.paperKNat κ n : ℝ) - 1 := by
      have hknat' : (1 : ℝ) ≤ Twobites.paperKNat κ n := by
        exact_mod_cast hknat
      linarith
    have hfirst :
        -((((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ)) *
              ((Twobites.paperKNat κ n : ℝ) - 1) ≤
          ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
                Twobites.paperKNat κ n) *
              ((Twobites.paperKNat κ n : ℝ) - 1) := by
      have hbase :
          -((((Twobites.paperKNat κ n -
                  ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ)) ≤
            (((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
              Twobites.paperKNat κ n := by
        by_cases hsum :
            (C.redImage I).card + (C.blueImage I).card ≤ Twobites.paperKNat κ n
        · rw [Nat.cast_sub hsum]
          linarith
        · have hsub0 :
            (Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) = 0 := by
            omega
          rw [hsub0]
          have hnonneg :
              0 ≤ (((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
                  Twobites.paperKNat κ n := by
            have hsum' :
                Twobites.paperKNat κ n ≤ (C.redImage I).card + (C.blueImage I).card := by
              exact Nat.le_of_not_ge hsum
            have hsum'' :
                (Twobites.paperKNat κ n : ℝ) ≤
                  (((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) := by
              exact_mod_cast hsum'
            linarith
          linarith
      exact mul_le_mul_of_nonneg_right hbase hfactor
    have hLossReal :
        (paperRISILossNat κ ε1 n : ℝ) ≤
          ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
              Twobites.paperKNat κ n) *
            ((Twobites.paperKNat κ n : ℝ) - 1) +
          (cap : ℝ) * ((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) := by
      linarith
    exact C.paper_risi_hLossGap_of_blueLeft_of_redRight_sumGap I hred hblueCap hLossReal
  · have hk0 : Twobites.paperKNat κ n = 0 := by omega
    have hred0 : (C.redImage I).card = 0 := by omega
    have hblue0 : (C.blueImage I).card = 0 := by omega
    have hcap0 : cap = 0 := by omega
    have hLoss0 : paperRISILossNat κ ε1 n = 0 := by
      have : (paperRISILossNat κ ε1 n : ℝ) ≤ 0 := by simpa [hk0, hblue0, hcap0] using hLoss
      have hLossNatLe : paperRISILossNat κ ε1 n ≤ 0 := by
        exact_mod_cast this
      omega
    simp [hLoss0]

theorem paper_risi_hLossGap_of_blueRight_of_redLeft_sumGap
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap : ℕ}
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat κ n)
    (hredCap : (C.redImage I).card + cap ≤ Twobites.paperKNat κ n)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
            Twobites.paperKNat κ n) *
          ((Twobites.paperKNat κ n : ℝ) - 1) +
        (cap : ℝ) * ((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ)) :
    paperRISILossNat κ ε1 n ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  have hBranch :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
          C.paperHugeBlueCrossRightTarget I κ cap -
          (((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ) := by
    calc
      (paperRISILossNat κ ε1 n : ℝ) ≤
          ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
              Twobites.paperKNat κ n) *
            ((Twobites.paperKNat κ n : ℝ) - 1) +
          (cap : ℝ) * ((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) := hLoss
      _ =
          ((C.redImage I).card.choose 2 : ℝ) + ((C.blueImage I).card.choose 2 : ℝ) -
            C.paperHugeBlueCrossRightTarget I κ cap -
            (((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ) :=
          C.paperSection4Branch_blueRight_redLeft_eq I hblue hredCap
  exact C.paper_risi_hLossGap_of_blueRight_of_redLeft I (cap := cap) hBranch

theorem paper_risi_hLossGap_of_blueRight_of_redLeft_natDeficit
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap deficit gap : ℕ}
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat κ n)
    (hredCap : (C.redImage I).card + cap ≤ Twobites.paperKNat κ n)
    (hsumDef :
      (C.redImage I).card + (C.blueImage I).card + deficit = Twobites.paperKNat κ n)
    (hredGap :
      (C.redImage I).card + cap + gap = Twobites.paperKNat κ n)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) +
          (deficit : ℝ) * ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (cap : ℝ) * (gap : ℝ)) :
    paperRISILossNat κ ε1 n ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  have hsumEq :
      (C.redImage I).card + (C.blueImage I).card =
        Twobites.paperKNat κ n - deficit := by
    omega
  have hgapEq :
      Twobites.paperKNat κ n - (C.redImage I).card - cap = gap := by
    omega
  have hLossReal :
      (paperRISILossNat κ ε1 n : ℝ) ≤
        ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
            Twobites.paperKNat κ n) *
          ((Twobites.paperKNat κ n : ℝ) - 1) +
        (cap : ℝ) * ((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) := by
    have hdefLe : deficit ≤ Twobites.paperKNat κ n := by
      omega
    calc
      (paperRISILossNat κ ε1 n : ℝ) ≤
          (cap : ℝ) * (gap : ℝ) -
            (deficit : ℝ) * ((Twobites.paperKNat κ n : ℝ) - 1) := by
        linarith
      _ =
          ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
              Twobites.paperKNat κ n) *
            ((Twobites.paperKNat κ n : ℝ) - 1) +
          (cap : ℝ) * ((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) := by
        rw [hgapEq, hsumEq, Nat.cast_sub hdefLe]
        ring
  exact C.paper_risi_hLossGap_of_blueRight_of_redLeft_sumGap I hblue hredCap hLossReal

theorem paper_risi_hLossGap_of_blueRight_of_redLeft_subGap
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ} {cap : ℕ}
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat κ n)
    (hredCap : (C.redImage I).card + cap ≤ Twobites.paperKNat κ n)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (cap : ℝ) *
          ((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ)) :
    paperRISILossNat κ ε1 n ≤ C.paperSection4OpenPairTargetNat I κ cap := by
  by_cases hknat : 1 ≤ Twobites.paperKNat κ n
  · have hfactor : 0 ≤ (Twobites.paperKNat κ n : ℝ) - 1 := by
      have hknat' : (1 : ℝ) ≤ Twobites.paperKNat κ n := by
        exact_mod_cast hknat
      linarith
    have hfirst :
        -((((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ)) *
              ((Twobites.paperKNat κ n : ℝ) - 1) ≤
          ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
                Twobites.paperKNat κ n) *
              ((Twobites.paperKNat κ n : ℝ) - 1) := by
      have hbase :
          -((((Twobites.paperKNat κ n -
                  ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ)) ≤
            (((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
              Twobites.paperKNat κ n := by
        by_cases hsum :
            (C.redImage I).card + (C.blueImage I).card ≤ Twobites.paperKNat κ n
        · rw [Nat.cast_sub hsum]
          linarith
        · have hsub0 :
            (Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) = 0 := by
            omega
          rw [hsub0]
          have hnonneg :
              0 ≤ (((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
                  Twobites.paperKNat κ n := by
            have hsum' :
                Twobites.paperKNat κ n ≤ (C.redImage I).card + (C.blueImage I).card := by
              exact Nat.le_of_not_ge hsum
            have hsum'' :
                (Twobites.paperKNat κ n : ℝ) ≤
                  (((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) := by
              exact_mod_cast hsum'
            linarith
          linarith
      exact mul_le_mul_of_nonneg_right hbase hfactor
    have hLossReal :
        (paperRISILossNat κ ε1 n : ℝ) ≤
          ((((C.redImage I).card + (C.blueImage I).card : ℕ) : ℝ) -
              Twobites.paperKNat κ n) *
            ((Twobites.paperKNat κ n : ℝ) - 1) +
          (cap : ℝ) * ((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) := by
      linarith
    exact C.paper_risi_hLossGap_of_blueRight_of_redLeft_sumGap I hblue hredCap hLossReal
  · have hk0 : Twobites.paperKNat κ n = 0 := by omega
    have hred0 : (C.redImage I).card = 0 := by omega
    have hblue0 : (C.blueImage I).card = 0 := by omega
    have hcap0 : cap = 0 := by omega
    have hLoss0 : paperRISILossNat κ ε1 n = 0 := by
      have : (paperRISILossNat κ ε1 n : ℝ) ≤ 0 := by simpa [hk0, hred0, hcap0] using hLoss
      have hLossNatLe : paperRISILossNat κ ε1 n ≤ 0 := by
        exact_mod_cast this
      omega
    simp [hLoss0]

theorem paperHugeBlueCrossTargetNat_cast_le_paperKSq
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap : ℕ}
    (hκ : 0 ≤ κ) (hk : 1 ≤ Twobites.paperK κ n) :
    ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) ≤ Twobites.paperK κ n ^ 2 := by
  have hsub :
      Twobites.paperKNat κ n - (C.redImage I).card ≤ Twobites.paperKNat κ n := by
    exact Nat.sub_le _ _
  have htargetNat :
      C.paperHugeBlueCrossTargetNat I κ cap ≤ (Twobites.paperKNat κ n).choose 2 := by
    unfold paperHugeBlueCrossTargetNat
    exact (Nat.min_le_left _ _).trans (Nat.choose_le_choose 2 hsub)
  have htargetCast :
      ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        (((Twobites.paperKNat κ n).choose 2 : ℕ) : ℝ) := by
    exact_mod_cast htargetNat
  have hceil : (Twobites.paperKNat κ n : ℝ) ≤ Twobites.paperK κ n + 1 :=
    Twobites.paperKNat_le_paperK_add_one hκ n
  have hknat_ge_one : 1 ≤ (Twobites.paperKNat κ n : ℝ) := by
    exact hk.trans (Twobites.paperK_le_paperKNat κ n)
  have hsub_le : (Twobites.paperKNat κ n : ℝ) - 1 ≤ Twobites.paperK κ n := by
    linarith
  have hmul :
      (Twobites.paperKNat κ n : ℝ) * ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (Twobites.paperK κ n + 1) * Twobites.paperK κ n := by
    have hsub_nonneg : 0 ≤ (Twobites.paperKNat κ n : ℝ) - 1 := by
      linarith
    have hk1_nonneg : 0 ≤ Twobites.paperK κ n + 1 := by
      linarith
    exact mul_le_mul hceil hsub_le hsub_nonneg hk1_nonneg
  have hchoose :
      (((Twobites.paperKNat κ n).choose 2 : ℕ) : ℝ) ≤ Twobites.paperK κ n ^ 2 := by
    rw [Nat.cast_choose_two]
    have hdiv :
        ((Twobites.paperKNat κ n : ℝ) * ((Twobites.paperKNat κ n : ℝ) - 1)) / 2 ≤
          ((Twobites.paperK κ n + 1) * Twobites.paperK κ n) / 2 := by
      exact div_le_div_of_nonneg_right hmul (by norm_num)
    have hhalf :
        ((Twobites.paperK κ n + 1) * Twobites.paperK κ n) / 2 ≤
          Twobites.paperK κ n ^ 2 := by
      nlinarith
    exact hdiv.trans hhalf
  exact htargetCast.trans hchoose

theorem paperHugeRedCrossTargetNat_cast_le_paperKSq
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap : ℕ}
    (hκ : 0 ≤ κ) (hk : 1 ≤ Twobites.paperK κ n) :
    ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) ≤ Twobites.paperK κ n ^ 2 := by
  have hsub :
      Twobites.paperKNat κ n - (C.blueImage I).card ≤ Twobites.paperKNat κ n := by
    exact Nat.sub_le _ _
  have htargetNat :
      C.paperHugeRedCrossTargetNat I κ cap ≤ (Twobites.paperKNat κ n).choose 2 := by
    unfold paperHugeRedCrossTargetNat
    exact (Nat.min_le_left _ _).trans (Nat.choose_le_choose 2 hsub)
  have htargetCast :
      ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        (((Twobites.paperKNat κ n).choose 2 : ℕ) : ℝ) := by
    exact_mod_cast htargetNat
  have hceil : (Twobites.paperKNat κ n : ℝ) ≤ Twobites.paperK κ n + 1 :=
    Twobites.paperKNat_le_paperK_add_one hκ n
  have hknat_ge_one : 1 ≤ (Twobites.paperKNat κ n : ℝ) := by
    exact hk.trans (Twobites.paperK_le_paperKNat κ n)
  have hsub_le : (Twobites.paperKNat κ n : ℝ) - 1 ≤ Twobites.paperK κ n := by
    linarith
  have hmul :
      (Twobites.paperKNat κ n : ℝ) * ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (Twobites.paperK κ n + 1) * Twobites.paperK κ n := by
    have hsub_nonneg : 0 ≤ (Twobites.paperKNat κ n : ℝ) - 1 := by
      linarith
    have hk1_nonneg : 0 ≤ Twobites.paperK κ n + 1 := by
      linarith
    exact mul_le_mul hceil hsub_le hsub_nonneg hk1_nonneg
  have hchoose :
      (((Twobites.paperKNat κ n).choose 2 : ℕ) : ℝ) ≤ Twobites.paperK κ n ^ 2 := by
    rw [Nat.cast_choose_two]
    have hdiv :
        ((Twobites.paperKNat κ n : ℝ) * ((Twobites.paperKNat κ n : ℝ) - 1)) / 2 ≤
          ((Twobites.paperK κ n + 1) * Twobites.paperK κ n) / 2 := by
      exact div_le_div_of_nonneg_right hmul (by norm_num)
    have hhalf :
        ((Twobites.paperK κ n + 1) * Twobites.paperK κ n) / 2 ≤
          Twobites.paperK κ n ^ 2 := by
      nlinarith
    exact hdiv.trans hhalf
  exact htargetCast.trans hchoose

theorem four_mul_eps_mul_paperKSq_add_eps_mul_natTarget_le_ceil_five_mul_eps_mul_paperKSq
    {κ ε1 : ℝ} {target : ℕ}
    (hε1 : 0 ≤ ε1)
    (htarget : ((target : ℕ) : ℝ) ≤ Twobites.paperK κ n ^ 2) :
    4 * (ε1 * Twobites.paperK κ n ^ 2) + ε1 * ((target : ℕ) : ℝ) ≤
      (⌈5 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ : ℝ) := by
  have hbound :
      4 * (ε1 * Twobites.paperK κ n ^ 2) + ε1 * ((target : ℕ) : ℝ) ≤
        5 * (ε1 * Twobites.paperK κ n ^ 2) := by
    nlinarith
  exact hbound.trans (Nat.le_ceil _)

theorem paperSection4OpenPairTargetNat_le_baseOpenPairSet_card_of_closedBounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap : ℕ}
    (hred :
      (C.redBaseClosedPairSet I).card ≤ C.paperHugeBlueCrossTargetNat I κ cap)
    (hblue :
      (C.blueBaseClosedPairSet I).card ≤ C.paperHugeRedCrossTargetNat I κ cap) :
    C.paperSection4OpenPairTargetNat I κ cap ≤ (C.baseOpenPairSet I).card := by
  simpa [paperSection4OpenPairTargetNat] using
    C.baseOpenPairSet_lower_bound_of_closedBounds I hred hblue

theorem paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_closedBounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap openError : ℕ}
    (hred :
      (C.redBaseClosedPairSet I).card ≤ C.paperHugeBlueCrossTargetNat I κ cap)
    (hblue :
      (C.blueBaseClosedPairSet I).card ≤ C.paperHugeRedCrossTargetNat I κ cap) :
    C.paperSection4OpenPairTargetNat I κ cap - openError ≤ (C.baseOpenPairSet I).card := by
  exact
    (Nat.sub_le _ _).trans
      (C.paperSection4OpenPairTargetNat_le_baseOpenPairSet_card_of_closedBounds I hred hblue)

theorem paperSection4OpenPairTargetNat_sub_errorSum_le_baseOpenPairSet_card_of_closedErrorBounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap redError blueError : ℕ}
    (hred :
      (C.redBaseClosedPairSet I).card ≤ C.paperHugeBlueCrossTargetNat I κ cap + redError)
    (hblue :
      (C.blueBaseClosedPairSet I).card ≤ C.paperHugeRedCrossTargetNat I κ cap + blueError) :
    C.paperSection4OpenPairTargetNat I κ cap - (redError + blueError) ≤
      (C.baseOpenPairSet I).card := by
  have hbase :=
    C.baseOpenPairSet_lower_bound_of_closedBounds I hred hblue
  simpa [paperSection4OpenPairTargetNat, Nat.sub_sub, add_assoc, add_left_comm, add_comm] using
    hbase

theorem paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_closedErrorBounds
    (C : ConstructionData n m) (I : Finset (Fin n))
    {κ : ℝ} {cap redError blueError openError : ℕ}
    (hred :
      (C.redBaseClosedPairSet I).card ≤ C.paperHugeBlueCrossTargetNat I κ cap + redError)
    (hblue :
      (C.blueBaseClosedPairSet I).card ≤ C.paperHugeRedCrossTargetNat I κ cap + blueError)
    (herror : redError + blueError ≤ openError) :
    C.paperSection4OpenPairTargetNat I κ cap - openError ≤ (C.baseOpenPairSet I).card := by
  have hsum :=
    C.paperSection4OpenPairTargetNat_sub_errorSum_le_baseOpenPairSet_card_of_closedErrorBounds
      I hred hblue
  exact (Nat.sub_le_sub_left herror _).trans hsum

set_option linter.style.longLine false in
theorem paperSection4OpenPairTargetNat_sub_errorSum_le_baseOpenPairSet_card_of_swappedClosedErrorBounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ} {cap redError blueError : ℕ}
    (hred :
      (C.redBaseClosedPairSet I).card ≤ C.paperHugeRedCrossTargetNat I κ cap + redError)
    (hblue :
      (C.blueBaseClosedPairSet I).card ≤ C.paperHugeBlueCrossTargetNat I κ cap + blueError) :
    C.paperSection4OpenPairTargetNat I κ cap - (redError + blueError) ≤
      (C.baseOpenPairSet I).card := by
  have hbase :=
    C.baseOpenPairSet_lower_bound_of_closedBounds I hred hblue
  simpa [paperSection4OpenPairTargetNat, Nat.sub_sub, add_assoc, add_left_comm, add_comm] using
    hbase

set_option linter.style.longLine false in
theorem paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_swappedClosedErrorBounds
    (C : ConstructionData n m) (I : Finset (Fin n))
    {κ : ℝ} {cap redError blueError openError : ℕ}
    (hred :
      (C.redBaseClosedPairSet I).card ≤ C.paperHugeRedCrossTargetNat I κ cap + redError)
    (hblue :
      (C.blueBaseClosedPairSet I).card ≤ C.paperHugeBlueCrossTargetNat I κ cap + blueError)
    (herror : redError + blueError ≤ openError) :
    C.paperSection4OpenPairTargetNat I κ cap - openError ≤ (C.baseOpenPairSet I).card := by
  have hsum :=
    C.paperSection4OpenPairTargetNat_sub_errorSum_le_baseOpenPairSet_card_of_swappedClosedErrorBounds
      I hred hblue
  exact (Nat.sub_le_sub_left herror _).trans hsum

theorem
    baseOpenPairSet_card_add_redBaseClosedPairSet_card_add_blueBaseClosedPairSet_card_eq_choose_sum
    (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.baseOpenPairSet I).card + (C.redBaseClosedPairSet I).card +
        (C.blueBaseClosedPairSet I).card =
      (C.redImage I).card.choose 2 + (C.blueImage I).card.choose 2 := by
  have hbase := C.baseOpenPairSet_card_eq_redBaseOpenPairSet_card_add_blueBaseOpenPairSet_card I
  have hredPart := C.redBaseOpenPairSet_card_add_redBaseClosedPairSet_card I
  have hbluePart := C.blueBaseOpenPairSet_card_add_blueBaseClosedPairSet_card I
  have hredTot := C.redBasePairSet_card_eq_choose I
  have hblueTot := C.blueBasePairSet_card_eq_choose I
  omega

set_option linter.style.longLine false in
theorem paperSection4OpenPairTarget_sub_openError_le_baseOpenPairSet_card_of_swappedClosedRealErrorBounds
    (C : ConstructionData n m) (I : Finset (Fin n))
    {κ : ℝ} {cap : ℕ} {redError blueError openError : ℝ}
    (hred :
      ((C.redBaseClosedPairSet I).card : ℝ) ≤
        ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) + redError)
    (hblue :
      ((C.blueBaseClosedPairSet I).card : ℝ) ≤
        ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) + blueError)
    (herror : redError + blueError ≤ openError)
    (hopenError : 0 ≤ openError) :
    C.paperSection4OpenPairTarget I κ cap - openError ≤ ((C.baseOpenPairSet I).card : ℝ) := by
  let totalChoose := (C.redImage I).card.choose 2 + (C.blueImage I).card.choose 2
  let totalTarget := C.paperHugeBlueCrossTargetNat I κ cap + C.paperHugeRedCrossTargetNat I κ cap
  have hsum :
      ((C.baseOpenPairSet I).card : ℝ) + ((C.redBaseClosedPairSet I).card : ℝ) +
          ((C.blueBaseClosedPairSet I).card : ℝ) =
        (totalChoose : ℝ) := by
    exact_mod_cast
      C.baseOpenPairSet_card_add_redBaseClosedPairSet_card_add_blueBaseClosedPairSet_card_eq_choose_sum
        I
  by_cases hle : totalTarget ≤ totalChoose
  · have htarget :
        C.paperSection4OpenPairTarget I κ cap =
          (totalChoose : ℝ) - (totalTarget : ℝ) := by
      unfold paperSection4OpenPairTarget paperSection4OpenPairTargetNat totalChoose totalTarget
      rw [Nat.sub_sub, Nat.cast_sub hle, Nat.cast_add]
    have hbase :
        (totalChoose : ℝ) -
            ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) -
            ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) -
            (redError + blueError) ≤
          ((C.baseOpenPairSet I).card : ℝ) := by
      nlinarith [hsum, hred, hblue]
    have htarget' :
        C.paperSection4OpenPairTarget I κ cap =
          (totalChoose : ℝ) -
            ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) -
            ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) := by
      have hcastTarget :
          (totalTarget : ℝ) =
            ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) +
              ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) := by
        dsimp [totalTarget]
        norm_num
      calc
        C.paperSection4OpenPairTarget I κ cap = (totalChoose : ℝ) - (totalTarget : ℝ) := htarget
        _ = (totalChoose : ℝ) -
              (((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) +
                ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ)) := by
            rw [hcastTarget]
        _ = (totalChoose : ℝ) -
              ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) -
              ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) := by
            ring
    nlinarith [hbase, htarget', herror]
  · have hzero :
        C.paperSection4OpenPairTarget I κ cap = 0 := by
      unfold paperSection4OpenPairTarget paperSection4OpenPairTargetNat
      rw [Nat.sub_sub, Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hle)), Nat.cast_zero]
    have hnonneg : 0 ≤ ((C.baseOpenPairSet I).card : ℝ) := by positivity
    nlinarith

/-- The `H_I ∩ V_R` cross-projection term from Paper Lemma `lem:huge`, reduced to the remaining
paper-witness arithmetic and cap/min-expression estimates. -/
theorem paper_huge_blue_cross_concrete_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ : ℝ} {witnessSize cap : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex, (C.blueProjectionImage I x).card ≤ cap)
    (hcapWeight :
      cap ≤ C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex)) :
    C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) ≤
      C.paperHugeBlueCrossConcreteBoundNat I κ witnessSize degreeBound projCodegreeBound cap := by
  have hA : ((C.HPart I).filter IsRedBaseVertex).card ≤ witnessSize := by
    exact (card_filter_IsRedBaseVertex_le (C.HPart I)).trans <|
      Nat.le_of_lt <| C.HPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hwitness)
  simpa [paperHugeBlueCrossConcreteBoundNat, paperHugeBlueCrossErrorNat, add_assoc] using
    (C.blueProjectionPairCount_filter_isLeft_le_min_choose_concrete_of_goodEventD_of_paperBound
      hD I (C.HPart I) hI hA hcap hcapWeight)

/-- The `H_I ∩ V_B` cross-projection term from Paper Lemma `lem:huge`, reduced to the remaining
paper-witness arithmetic and cap/min-expression estimates. -/
theorem paper_huge_red_cross_concrete_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ : ℝ} {witnessSize cap : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex, (C.redProjectionImage I x).card ≤ cap)
    (hcapWeight :
      cap ≤ C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex)) :
    C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
      C.paperHugeRedCrossConcreteBoundNat I κ witnessSize degreeBound projCodegreeBound cap := by
  have hA : ((C.HPart I).filter IsBlueBaseVertex).card ≤ witnessSize := by
    exact (card_filter_IsBlueBaseVertex_le (C.HPart I)).trans <|
      Nat.le_of_lt <| C.HPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hwitness)
  simpa [paperHugeRedCrossConcreteBoundNat, paperHugeRedCrossErrorNat, add_assoc] using
    (C.redProjectionPairCount_filter_isRight_le_min_choose_concrete_of_goodEventD_of_paperBound
      hD I (C.HPart I) hI hA hcap hcapWeight)

theorem paperHugeBlueCrossErrorNat_le_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound ≤
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound := by
  unfold paperHugeBlueCrossErrorNat
  have hcard : ((C.HPart I).filter IsRedBaseVertex).card ≤ witnessSize := by
    exact (card_filter_IsRedBaseVertex_le (C.HPart I)).trans <|
      Nat.le_of_lt <| C.HPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hwitness)
  unfold paperHugeBlueCrossUnionSlackNat paperHugeBlueCrossOverlapErrorNat
  gcongr

theorem paperHugeBlueCrossOverlapErrorNat_le_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    C.paperHugeBlueCrossOverlapErrorNat I projCodegreeBound ≤
      witnessSize.choose 2 * projCodegreeBound := by
  unfold paperHugeBlueCrossOverlapErrorNat
  have hcard : ((C.HPart I).filter IsRedBaseVertex).card ≤ witnessSize := by
    exact (card_filter_IsRedBaseVertex_le (C.HPart I)).trans <|
      Nat.le_of_lt <| C.HPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hwitness)
  gcongr

theorem paperHugeRedCrossErrorNat_le_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound ≤
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound := by
  unfold paperHugeRedCrossErrorNat
  have hcard : ((C.HPart I).filter IsBlueBaseVertex).card ≤ witnessSize := by
    exact (card_filter_IsBlueBaseVertex_le (C.HPart I)).trans <|
      Nat.le_of_lt <| C.HPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hwitness)
  unfold paperHugeRedCrossUnionSlackNat paperHugeRedCrossOverlapErrorNat
  gcongr

theorem paperHugeRedCrossOverlapErrorNat_le_of_goodEventD_of_paperWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound) :
    C.paperHugeRedCrossOverlapErrorNat I projCodegreeBound ≤
      witnessSize.choose 2 * projCodegreeBound := by
  unfold paperHugeRedCrossOverlapErrorNat
  have hcard : ((C.HPart I).filter IsBlueBaseVertex).card ≤ witnessSize := by
    exact (card_filter_IsBlueBaseVertex_le (C.HPart I)).trans <|
      Nat.le_of_lt <| C.HPart_card_lt_of_goodEventD_of_lt hD I (lt_of_le_of_lt hI hwitness)
  gcongr

theorem paperHugeBlueCrossLeftError_of_le_of_three_mul_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ}
    {witnessSize degreeBound projCodegreeBound : ℕ}
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - (C.redImage I).card)
    (hsmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 * (((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) - 1)) :
    ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
      ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)) := by
  simpa using
    (cast_mul_add_choose_two_le_eps_mul_choose_two_of_le_of_three_mul_le
      (a := Twobites.paperKNat κ n - (C.redImage I).card)
      (b := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound)
      hB hsmall)

theorem paperHugeBlueCrossLeftError_of_le_of_sq_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 W : ℝ}
    {witnessSize degreeBound projCodegreeBound : ℕ}
    (herror :
      (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤ W)
    (hcoeff :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) * W + W ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ))) :
    ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
      ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)) := by
  have hbase :=
    cast_mul_add_choose_two_le_of_le_of_sq_bound
      (a := Twobites.paperKNat κ n - (C.redImage I).card)
      (b := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound)
      (W := W) herror
  have hbase' :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
            ((witnessSize : ℝ) * degreeBound + (witnessSize.choose 2 : ℝ) * projCodegreeBound) +
          ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
            ℕ) : ℝ)) ≤
        ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) * W + W ^ 2 / 2 := by
    simpa [Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm] using hbase
  exact hbase'.trans hcoeff

theorem paperHugeBlueCrossWitnessRightErrorProp_of_le_of_three_mul_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ}
    {witnessSize degreeBound projCodegreeBound cap : ℕ} (hε1 : 0 ≤ ε1)
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - (C.redImage I).card - cap)
    (hsmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 * (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) - 1)) :
    C.paperHugeBlueCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound projCodegreeBound
      cap := by
  unfold paperHugeBlueCrossWitnessRightErrorProp paperHugeBlueCrossRightTarget
  simpa [paperHugeBlueCrossRightTargetNat] using
    (cast_mul_add_choose_two_le_eps_mul_choose_two_cap_add_choose_two_sub_of_le_of_three_mul_le
      (a := Twobites.paperKNat κ n - (C.redImage I).card)
      (b := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound)
      (cap := cap) hε1 hB hsmall)

theorem paperHugeBlueCrossWitnessRightErrorProp_of_le_of_sq_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 W : ℝ}
    {witnessSize degreeBound projCodegreeBound cap : ℕ}
    (herror :
      (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤ W)
    (hcoeff :
      (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) * W + W ^ 2 / 2) ≤
        ε1 * C.paperHugeBlueCrossRightTarget I κ cap) :
    C.paperHugeBlueCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound projCodegreeBound
      cap := by
  unfold paperHugeBlueCrossWitnessRightErrorProp
  have hbase :=
    cast_mul_add_choose_two_le_of_le_of_sq_bound
      (a := Twobites.paperKNat κ n - (C.redImage I).card - cap)
      (b := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound)
      (W := W) herror
  have hbase' :
      (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) *
            ((witnessSize : ℝ) * degreeBound + (witnessSize.choose 2 : ℝ) * projCodegreeBound) +
          (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
            ℕ) : ℝ)) ≤
        ((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) * W + W ^ 2 / 2 := by
    simpa [Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm] using hbase
  exact hbase'.trans hcoeff

theorem paperHugeBlueCrossWitnessRightSplitErrorProp_mono
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ}
    {union₁ union₂ overlap₁ overlap₂ cap : ℕ}
    (hunion : union₁ ≤ union₂) (hoverlap : overlap₁ ≤ overlap₂)
    (hprop : C.paperHugeBlueCrossWitnessRightSplitErrorProp I κ ε1 union₂ overlap₂ cap) :
    C.paperHugeBlueCrossWitnessRightSplitErrorProp I κ ε1 union₁ overlap₁ cap := by
  unfold paperHugeBlueCrossWitnessRightSplitErrorProp at hprop ⊢
  have hunion' : (union₁ : ℝ) ≤ union₂ := by exact_mod_cast hunion
  have hoverlap' : (overlap₁ : ℝ) ≤ overlap₂ := by exact_mod_cast hoverlap
  have hsum :
      (((Twobites.paperKNat κ n - (C.redImage I).card - cap + union₁ : ℕ) : ℝ)) ≤
        ((Twobites.paperKNat κ n - (C.redImage I).card - cap + union₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_left hunion _
  have hchoose := cast_choose_two_le_of_le hoverlap
  have hmono :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) * union₁) +
          ((((Twobites.paperKNat κ n - (C.redImage I).card - cap + union₁ : ℕ) : ℝ) *
              overlap₁) +
            (((overlap₁.choose 2 : ℕ) : ℝ))) ≤
        ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) * union₂) +
          ((((Twobites.paperKNat κ n - (C.redImage I).card - cap + union₂ : ℕ) : ℝ) *
              overlap₂) +
            (((overlap₂.choose 2 : ℕ) : ℝ))) := by
    have hbase1 :
        (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) * union₁) ≤
          (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) * union₂) := by
      exact mul_le_mul_of_nonneg_left hunion' (by positivity)
    have hterm1 :
        ((3 : ℝ) / 2) *
              (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) * union₁) ≤
          ((3 : ℝ) / 2) *
              (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) * union₂) := by
      exact mul_le_mul_of_nonneg_left hbase1 (by positivity)
    have hterm2 :
        (((Twobites.paperKNat κ n - (C.redImage I).card - cap + union₁ : ℕ) : ℝ) * overlap₁) ≤
          (((Twobites.paperKNat κ n - (C.redImage I).card - cap + union₂ : ℕ) : ℝ) * overlap₂) := by
      exact mul_le_mul hsum hoverlap' (by positivity) (by positivity)
    nlinarith
  exact hmono.trans hprop

theorem paperHugeBlueCrossWitnessRightSplitErrorProp_of_le_of_sq_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 U O : ℝ}
    {witnessSize degreeBound projCodegreeBound cap : ℕ}
    (hunion :
      (((witnessSize * degreeBound : ℕ) : ℝ)) ≤ U)
    (hoverlap :
      (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤ O)
    (hcoeff :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) * U) +
          ((((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) + U) * O +
            O ^ 2 / 2) ≤
        ε1 * C.paperHugeBlueCrossRightTarget I κ cap) :
    C.paperHugeBlueCrossWitnessRightSplitErrorProp I κ ε1
      (witnessSize * degreeBound) (witnessSize.choose 2 * projCodegreeBound) cap := by
  unfold paperHugeBlueCrossWitnessRightSplitErrorProp
  have hsum :
      (((Twobites.paperKNat κ n - (C.redImage I).card - cap + witnessSize * degreeBound : ℕ) :
        ℝ)) ≤
        (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) + U) := by
    calc
      (((Twobites.paperKNat κ n - (C.redImage I).card - cap + witnessSize * degreeBound : ℕ) :
        ℝ)) =
          (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ)) +
            (((witnessSize * degreeBound : ℕ) : ℝ)) := by
              norm_num
      _ ≤ (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) + U) := by
            gcongr
  have hchoose :
      (((witnessSize.choose 2 * projCodegreeBound).choose 2 : ℕ) : ℝ) ≤ O ^ 2 / 2 := by
    have hO : 0 ≤ O := le_trans (by positivity : (0 : ℝ) ≤
      (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ))) hoverlap
    calc
      (((witnessSize.choose 2 * projCodegreeBound).choose 2 : ℕ) : ℝ) ≤
          (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ^ 2 / 2 := by
            exact Twobites.cast_choose_two_le_sq_div_two (witnessSize.choose 2 * projCodegreeBound)
      _ ≤ O ^ 2 / 2 := by
            nlinarith
  have hterm1 :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) *
              (((witnessSize * degreeBound : ℕ) : ℝ))) ≤
        ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) * U) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hunion (by positivity)) (by positivity)
  have hterm2 :
      (((Twobites.paperKNat κ n - (C.redImage I).card - cap + witnessSize * degreeBound : ℕ) :
        ℝ) * (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ))) ≤
        ((((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) + U) * O) := by
    have hU : 0 ≤ U := le_trans (by positivity : (0 : ℝ) ≤
      (((witnessSize * degreeBound : ℕ) : ℝ))) hunion
    have hA : 0 ≤ (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) + U) := by
      positivity
    exact mul_le_mul hsum hoverlap (by positivity) hA
  nlinarith [hterm1, hterm2, hchoose, hcoeff]

theorem paperHugeRedCrossLeftError_of_le_of_three_mul_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ}
    {witnessSize degreeBound projCodegreeBound : ℕ}
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - (C.blueImage I).card)
    (hsmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 * (((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) - 1)) :
    ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
      ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)) := by
  simpa using
    (cast_mul_add_choose_two_le_eps_mul_choose_two_of_le_of_three_mul_le
      (a := Twobites.paperKNat κ n - (C.blueImage I).card)
      (b := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound)
      hB hsmall)

theorem paperHugeRedCrossLeftError_of_le_of_sq_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 W : ℝ}
    {witnessSize degreeBound projCodegreeBound : ℕ}
    (herror :
      (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤ W)
    (hcoeff :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) * W + W ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ))) :
    ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
      ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)) := by
  have hbase :=
    cast_mul_add_choose_two_le_of_le_of_sq_bound
      (a := Twobites.paperKNat κ n - (C.blueImage I).card)
      (b := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound)
      (W := W) herror
  have hbase' :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
            ((witnessSize : ℝ) * degreeBound + (witnessSize.choose 2 : ℝ) * projCodegreeBound) +
          ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
            ℕ) : ℝ)) ≤
        ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) * W + W ^ 2 / 2 := by
    simpa [Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm] using hbase
  exact hbase'.trans hcoeff

theorem paperHugeRedCrossWitnessRightErrorProp_of_le_of_three_mul_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ}
    {witnessSize degreeBound projCodegreeBound cap : ℕ} (hε1 : 0 ≤ ε1)
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - cap)
    (hsmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 * (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) - 1)) :
    C.paperHugeRedCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound projCodegreeBound
      cap := by
  unfold paperHugeRedCrossWitnessRightErrorProp paperHugeRedCrossRightTarget
  simpa [paperHugeRedCrossRightTargetNat] using
    (cast_mul_add_choose_two_le_eps_mul_choose_two_cap_add_choose_two_sub_of_le_of_three_mul_le
      (a := Twobites.paperKNat κ n - (C.blueImage I).card)
      (b := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound)
      (cap := cap) hε1 hB hsmall)

theorem paperHugeRedCrossWitnessRightErrorProp_of_le_of_sq_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 W : ℝ}
    {witnessSize degreeBound projCodegreeBound cap : ℕ}
    (herror :
      (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤ W)
    (hcoeff :
      (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) * W + W ^ 2 / 2) ≤
        ε1 * C.paperHugeRedCrossRightTarget I κ cap) :
    C.paperHugeRedCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound projCodegreeBound
      cap := by
  unfold paperHugeRedCrossWitnessRightErrorProp
  have hbase :=
    cast_mul_add_choose_two_le_of_le_of_sq_bound
      (a := Twobites.paperKNat κ n - (C.blueImage I).card - cap)
      (b := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound)
      (W := W) herror
  have hbase' :
      (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) *
            ((witnessSize : ℝ) * degreeBound + (witnessSize.choose 2 : ℝ) * projCodegreeBound) +
          (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
            ℕ) : ℝ)) ≤
        ((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) * W + W ^ 2 / 2 := by
    simpa [Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm] using hbase
  exact hbase'.trans hcoeff

theorem paperHugeRedCrossWitnessRightSplitErrorProp_mono
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ}
    {union₁ union₂ overlap₁ overlap₂ cap : ℕ}
    (hunion : union₁ ≤ union₂) (hoverlap : overlap₁ ≤ overlap₂)
    (hprop : C.paperHugeRedCrossWitnessRightSplitErrorProp I κ ε1 union₂ overlap₂ cap) :
    C.paperHugeRedCrossWitnessRightSplitErrorProp I κ ε1 union₁ overlap₁ cap := by
  unfold paperHugeRedCrossWitnessRightSplitErrorProp at hprop ⊢
  have hunion' : (union₁ : ℝ) ≤ union₂ := by exact_mod_cast hunion
  have hoverlap' : (overlap₁ : ℝ) ≤ overlap₂ := by exact_mod_cast hoverlap
  have hsum :
      (((Twobites.paperKNat κ n - (C.blueImage I).card - cap + union₁ : ℕ) : ℝ)) ≤
        ((Twobites.paperKNat κ n - (C.blueImage I).card - cap + union₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_left hunion _
  have hchoose := cast_choose_two_le_of_le hoverlap
  have hmono :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) * union₁) +
          ((((Twobites.paperKNat κ n - (C.blueImage I).card - cap + union₁ : ℕ) : ℝ) *
              overlap₁) +
            (((overlap₁.choose 2 : ℕ) : ℝ))) ≤
        ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) * union₂) +
          ((((Twobites.paperKNat κ n - (C.blueImage I).card - cap + union₂ : ℕ) : ℝ) *
              overlap₂) +
            (((overlap₂.choose 2 : ℕ) : ℝ))) := by
    have hbase1 :
        (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) * union₁) ≤
          (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) * union₂) := by
      exact mul_le_mul_of_nonneg_left hunion' (by positivity)
    have hterm1 :
        ((3 : ℝ) / 2) *
              (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) * union₁) ≤
          ((3 : ℝ) / 2) *
              (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) * union₂) := by
      exact mul_le_mul_of_nonneg_left hbase1 (by positivity)
    have hterm2 :
        (((Twobites.paperKNat κ n - (C.blueImage I).card - cap + union₁ : ℕ) : ℝ) * overlap₁) ≤
          (((Twobites.paperKNat κ n - (C.blueImage I).card - cap + union₂ : ℕ) : ℝ) *
            overlap₂) := by
      exact mul_le_mul hsum hoverlap' (by positivity) (by positivity)
    nlinarith
  exact hmono.trans hprop

theorem paperHugeRedCrossWitnessRightSplitErrorProp_of_le_of_sq_bound
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 U O : ℝ}
    {witnessSize degreeBound projCodegreeBound cap : ℕ}
    (hunion :
      (((witnessSize * degreeBound : ℕ) : ℝ)) ≤ U)
    (hoverlap :
      (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤ O)
    (hcoeff :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) * U) +
          ((((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) + U) * O +
            O ^ 2 / 2) ≤
        ε1 * C.paperHugeRedCrossRightTarget I κ cap) :
    C.paperHugeRedCrossWitnessRightSplitErrorProp I κ ε1
      (witnessSize * degreeBound) (witnessSize.choose 2 * projCodegreeBound) cap := by
  unfold paperHugeRedCrossWitnessRightSplitErrorProp
  have hsum :
      (((Twobites.paperKNat κ n - (C.blueImage I).card - cap + witnessSize * degreeBound : ℕ) :
        ℝ)) ≤
        (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) + U) := by
    calc
      (((Twobites.paperKNat κ n - (C.blueImage I).card - cap + witnessSize * degreeBound : ℕ) :
        ℝ)) =
          (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ)) +
            (((witnessSize * degreeBound : ℕ) : ℝ)) := by
              norm_num
      _ ≤ (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) + U) := by
            gcongr
  have hchoose :
      (((witnessSize.choose 2 * projCodegreeBound).choose 2 : ℕ) : ℝ) ≤ O ^ 2 / 2 := by
    have hO : 0 ≤ O := le_trans (by positivity : (0 : ℝ) ≤
      (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ))) hoverlap
    calc
      (((witnessSize.choose 2 * projCodegreeBound).choose 2 : ℕ) : ℝ) ≤
          (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ^ 2 / 2 := by
            exact Twobites.cast_choose_two_le_sq_div_two (witnessSize.choose 2 * projCodegreeBound)
      _ ≤ O ^ 2 / 2 := by
            nlinarith
  have hterm1 :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) *
              (((witnessSize * degreeBound : ℕ) : ℝ))) ≤
        ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) * U) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hunion (by positivity)) (by positivity)
  have hterm2 :
      (((Twobites.paperKNat κ n - (C.blueImage I).card - cap + witnessSize * degreeBound : ℕ) :
        ℝ) * (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ))) ≤
        ((((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) + U) * O) := by
    have hU : 0 ≤ U := le_trans (by positivity : (0 : ℝ) ≤
      (((witnessSize * degreeBound : ℕ) : ℝ))) hunion
    have hA : 0 ≤ (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) + U) := by
      positivity
    exact mul_le_mul hsum hoverlap (by positivity) hA
  nlinarith [hterm1, hterm2, hchoose, hcoeff]

/-- The `H_I ∩ V_R` cross-projection term from Paper Lemma `lem:huge`, reduced to a final
comparison between the current concrete bound and the paper's target min-expression. -/
theorem paper_huge_blue_cross_deterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε1 : ℝ} {witnessSize cap : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex, (C.blueProjectionImage I x).card ≤ cap)
    (hcapWeight :
      cap ≤ C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hbound :
      ((C.paperHugeBlueCrossConcreteBoundNat I κ witnessSize degreeBound projCodegreeBound cap :
        ℕ) : ℝ) ≤
        (1 + ε1) * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) := by
  have hnat := C.paper_huge_blue_cross_concrete_of_paperWitness hD I hI hwitness hcap hcapWeight
  have hcast :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ((C.paperHugeBlueCrossConcreteBoundNat I κ witnessSize degreeBound projCodegreeBound cap :
          ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans hbound

theorem paperHugeBlueCrossConcreteBoundNat_le_target_of_error_bounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ}
    {witnessSize degreeBound projCodegreeBound cap : ℕ} (hε1 : 0 ≤ ε1)
    (hcap : cap ≤ Twobites.paperKNat κ n - (C.redImage I).card)
    (hleft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound +
        (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) *
          C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound) +
        (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((C.paperHugeBlueCrossRightTargetNat I κ cap : ℕ) : ℝ)) :
    ((C.paperHugeBlueCrossConcreteBoundNat I κ witnessSize degreeBound projCodegreeBound cap :
      ℕ) : ℝ) ≤
      (1 + ε1) * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) := by
  let a := Twobites.paperKNat κ n - (C.redImage I).card
  let b := C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound
  have hbase :
      ((min ((a + b).choose 2) (cap.choose 2 + (a + b - cap).choose 2) : ℕ) : ℝ) ≤
        (1 + ε1) * ((min (a.choose 2) (cap.choose 2 + (a - cap).choose 2) : ℕ) : ℝ) := by
    apply cast_min_choose_two_add_le_one_add_mul_min (ε := ε1) hε1
    · simpa [a] using hcap
    · simpa [a, b, mul_comm, mul_left_comm, mul_assoc] using hleft
    · simpa [a, b, paperHugeBlueCrossRightTargetNat, mul_comm, mul_left_comm, mul_assoc] using
        hright
  simpa [paperHugeBlueCrossConcreteBoundNat, paperHugeBlueCrossTargetNat,
    paperHugeBlueCrossRightTargetNat, paperHugeBlueCrossErrorNat, a, b] using hbase

theorem paperHugeBlueCrossConcreteBoundNat_le_target_of_split_right_error_bounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ}
    {witnessSize degreeBound projCodegreeBound cap : ℕ} (hε1 : 0 ≤ ε1)
    (hcap : cap ≤ Twobites.paperKNat κ n - (C.redImage I).card)
    (hunionBase :
      C.paperHugeBlueCrossUnionSlackNat I witnessSize degreeBound ≤
        Twobites.paperKNat κ n - (C.redImage I).card - cap)
    (hleft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound +
        (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      C.paperHugeBlueCrossWitnessRightSplitErrorProp I κ ε1
        (C.paperHugeBlueCrossUnionSlackNat I witnessSize degreeBound)
        (C.paperHugeBlueCrossOverlapErrorNat I projCodegreeBound) cap) :
    ((C.paperHugeBlueCrossConcreteBoundNat I κ witnessSize degreeBound projCodegreeBound cap :
      ℕ) : ℝ) ≤
      (1 + ε1) * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) := by
  let a := Twobites.paperKNat κ n - (C.redImage I).card
  let u := C.paperHugeBlueCrossUnionSlackNat I witnessSize degreeBound
  let o := C.paperHugeBlueCrossOverlapErrorNat I projCodegreeBound
  have hbase :
      ((min ((a + u + o).choose 2) (cap.choose 2 + (a + u + o - cap).choose 2) : ℕ) : ℝ) ≤
        (1 + ε1) * ((min (a.choose 2) (cap.choose 2 + (a - cap).choose 2) : ℕ) : ℝ) := by
    apply cast_min_choose_two_add_le_one_add_mul_min_of_split_right (ε := ε1) hε1
    · simpa [a] using hcap
    · simpa [a, u] using hunionBase
    · simpa [a, u, o, paperHugeBlueCrossErrorNat, paperHugeBlueCrossUnionSlackNat,
        paperHugeBlueCrossOverlapErrorNat, add_assoc, add_left_comm, add_comm, mul_comm,
        mul_left_comm, mul_assoc] using hleft
    · simpa [a, u, o, paperHugeBlueCrossWitnessRightSplitErrorProp,
        paperHugeBlueCrossRightTarget, paperHugeBlueCrossRightTargetNat, add_assoc,
        add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using hright
  simpa [paperHugeBlueCrossConcreteBoundNat, paperHugeBlueCrossTargetNat,
    paperHugeBlueCrossRightTargetNat, paperHugeBlueCrossErrorNat, paperHugeBlueCrossUnionSlackNat,
    paperHugeBlueCrossOverlapErrorNat, a, u, o, add_assoc, add_left_comm, add_comm] using hbase

theorem paper_huge_blue_cross_deterministic_of_error_bounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε1 : ℝ} {witnessSize cap : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex, (C.blueProjectionImage I x).card ≤ cap)
    (hcapWeight :
      cap ≤ C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hε1 : 0 ≤ ε1)
    (hcapBase : cap ≤ Twobites.paperKNat κ n - (C.redImage I).card)
    (hleft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound +
        (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      (((Twobites.paperKNat κ n - (C.redImage I).card - cap : ℕ) : ℝ) *
          C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound) +
        (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((C.paperHugeBlueCrossRightTargetNat I κ cap : ℕ) : ℝ)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) := by
  apply C.paper_huge_blue_cross_deterministic hD I hI hwitness hcap hcapWeight
  exact C.paperHugeBlueCrossConcreteBoundNat_le_target_of_error_bounds I hε1 hcapBase hleft hright

/-- The `H_I ∩ V_B` cross-projection term from Paper Lemma `lem:huge`, reduced to a final
comparison between the current concrete bound and the paper's target min-expression. -/
theorem paper_huge_red_cross_deterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε1 : ℝ} {witnessSize cap : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex, (C.redProjectionImage I x).card ≤ cap)
    (hcapWeight :
      cap ≤ C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hbound :
      ((C.paperHugeRedCrossConcreteBoundNat I κ witnessSize degreeBound projCodegreeBound cap :
        ℕ) : ℝ) ≤
        (1 + ε1) * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) := by
  have hnat := C.paper_huge_red_cross_concrete_of_paperWitness hD I hI hwitness hcap hcapWeight
  have hcast :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ((C.paperHugeRedCrossConcreteBoundNat I κ witnessSize degreeBound projCodegreeBound cap :
          ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans hbound

theorem paperHugeRedCrossConcreteBoundNat_le_target_of_error_bounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ}
    {witnessSize degreeBound projCodegreeBound cap : ℕ} (hε1 : 0 ≤ ε1)
    (hcap : cap ≤ Twobites.paperKNat κ n - (C.blueImage I).card)
    (hleft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound +
        (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) *
          C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound) +
        (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((C.paperHugeRedCrossRightTargetNat I κ cap : ℕ) : ℝ)) :
    ((C.paperHugeRedCrossConcreteBoundNat I κ witnessSize degreeBound projCodegreeBound cap :
      ℕ) : ℝ) ≤
      (1 + ε1) * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) := by
  let a := Twobites.paperKNat κ n - (C.blueImage I).card
  let b := C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound
  have hbase :
      ((min ((a + b).choose 2) (cap.choose 2 + (a + b - cap).choose 2) : ℕ) : ℝ) ≤
        (1 + ε1) * ((min (a.choose 2) (cap.choose 2 + (a - cap).choose 2) : ℕ) : ℝ) := by
    apply cast_min_choose_two_add_le_one_add_mul_min (ε := ε1) hε1
    · simpa [a] using hcap
    · simpa [a, b, mul_comm, mul_left_comm, mul_assoc] using hleft
    · simpa [a, b, paperHugeRedCrossRightTargetNat, mul_comm, mul_left_comm, mul_assoc] using
        hright
  simpa [paperHugeRedCrossConcreteBoundNat, paperHugeRedCrossTargetNat,
    paperHugeRedCrossRightTargetNat, paperHugeRedCrossErrorNat, a, b] using hbase

theorem paperHugeRedCrossConcreteBoundNat_le_target_of_split_right_error_bounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε1 : ℝ}
    {witnessSize degreeBound projCodegreeBound cap : ℕ} (hε1 : 0 ≤ ε1)
    (hcap : cap ≤ Twobites.paperKNat κ n - (C.blueImage I).card)
    (hunionBase :
      C.paperHugeRedCrossUnionSlackNat I witnessSize degreeBound ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - cap)
    (hleft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound +
        (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      C.paperHugeRedCrossWitnessRightSplitErrorProp I κ ε1
        (C.paperHugeRedCrossUnionSlackNat I witnessSize degreeBound)
        (C.paperHugeRedCrossOverlapErrorNat I projCodegreeBound) cap) :
    ((C.paperHugeRedCrossConcreteBoundNat I κ witnessSize degreeBound projCodegreeBound cap :
      ℕ) : ℝ) ≤
      (1 + ε1) * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) := by
  let a := Twobites.paperKNat κ n - (C.blueImage I).card
  let u := C.paperHugeRedCrossUnionSlackNat I witnessSize degreeBound
  let o := C.paperHugeRedCrossOverlapErrorNat I projCodegreeBound
  have hbase :
      ((min ((a + u + o).choose 2) (cap.choose 2 + (a + u + o - cap).choose 2) : ℕ) : ℝ) ≤
        (1 + ε1) * ((min (a.choose 2) (cap.choose 2 + (a - cap).choose 2) : ℕ) : ℝ) := by
    apply cast_min_choose_two_add_le_one_add_mul_min_of_split_right (ε := ε1) hε1
    · simpa [a] using hcap
    · simpa [a, u] using hunionBase
    · simpa [a, u, o, paperHugeRedCrossErrorNat, paperHugeRedCrossUnionSlackNat,
        paperHugeRedCrossOverlapErrorNat, add_assoc, add_left_comm, add_comm, mul_comm,
        mul_left_comm, mul_assoc] using hleft
    · simpa [a, u, o, paperHugeRedCrossWitnessRightSplitErrorProp,
        paperHugeRedCrossRightTarget, paperHugeRedCrossRightTargetNat, add_assoc,
        add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using hright
  simpa [paperHugeRedCrossConcreteBoundNat, paperHugeRedCrossTargetNat,
    paperHugeRedCrossRightTargetNat, paperHugeRedCrossErrorNat, paperHugeRedCrossUnionSlackNat,
    paperHugeRedCrossOverlapErrorNat, a, u, o, add_assoc, add_left_comm, add_comm] using hbase

theorem paper_huge_red_cross_deterministic_of_error_bounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε1 : ℝ} {witnessSize cap : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex, (C.redProjectionImage I x).card ≤ cap)
    (hcapWeight :
      cap ≤ C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hε1 : 0 ≤ ε1)
    (hcapBase : cap ≤ Twobites.paperKNat κ n - (C.blueImage I).card)
    (hleft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound +
        (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      (((Twobites.paperKNat κ n - (C.blueImage I).card - cap : ℕ) : ℝ) *
          C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound) +
        (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((C.paperHugeRedCrossRightTargetNat I κ cap : ℕ) : ℝ)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) := by
  apply C.paper_huge_red_cross_deterministic hD I hI hwitness hcap hcapWeight
  exact C.paperHugeRedCrossConcreteBoundNat_le_target_of_error_bounds I hε1 hcapBase hleft
    hright

theorem paper_huge_blue_cross_deterministic_of_paperCapNat_of_witnessSplitRightErrorBounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {β κ ε1 ε2 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hε1 : 0 ≤ ε1)
    (hcapBase :
      Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n - (C.redImage I).card)
    (hunionBase :
      witnessSize * degreeBound ≤
        Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n)
    (hleft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      C.paperHugeBlueCrossWitnessRightSplitErrorProp I κ ε1
        (witnessSize * degreeBound) (witnessSize.choose 2 * projCodegreeBound)
        (Twobites.paperCapNat β ε2 n)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  have hright' :
      C.paperHugeBlueCrossWitnessRightSplitErrorProp I κ ε1
        (C.paperHugeBlueCrossUnionSlackNat I witnessSize degreeBound)
        (C.paperHugeBlueCrossOverlapErrorNat I projCodegreeBound)
        (Twobites.paperCapNat β ε2 n) := by
    refine C.paperHugeBlueCrossWitnessRightSplitErrorProp_mono
      (I := I)
      (union₂ := witnessSize * degreeBound)
      (overlap₂ := witnessSize.choose 2 * projCodegreeBound)
      ?_ ?_ hright
    · simp [paperHugeBlueCrossUnionSlackNat]
    · exact C.paperHugeBlueCrossOverlapErrorNat_le_of_goodEventD_of_paperWitness hD I hI hwitness
  have hleft' :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound +
        (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)) := by
    let B : ℕ := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound
    have herror :
        C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound ≤ B :=
      C.paperHugeBlueCrossErrorNat_le_of_goodEventD_of_paperWitness hD I hI hwitness
    have hmono :
        ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
            C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound +
          (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
            ℕ) : ℝ) ≤
        ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) * B +
          (((B.choose 2 : ℕ) : ℝ)) := by
      simpa [B] using
        (cast_mul_add_choose_two_le_of_le
          (a := Twobites.paperKNat κ n - (C.redImage I).card) herror)
    exact hmono.trans <| by simpa [B] using hleft
  apply C.paper_huge_blue_cross_deterministic hD I hI hwitness hcap hcapWeight
  exact
    C.paperHugeBlueCrossConcreteBoundNat_le_target_of_split_right_error_bounds I hε1 hcapBase
      (by simpa [paperHugeBlueCrossUnionSlackNat] using hunionBase) hleft' hright'

theorem paper_huge_red_cross_deterministic_of_paperCapNat_of_witnessSplitRightErrorBounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {β κ ε1 ε2 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hε1 : 0 ≤ ε1)
    (hcapBase :
      Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n - (C.blueImage I).card)
    (hunionBase :
      witnessSize * degreeBound ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n)
    (hleft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      C.paperHugeRedCrossWitnessRightSplitErrorProp I κ ε1
        (witnessSize * degreeBound) (witnessSize.choose 2 * projCodegreeBound)
        (Twobites.paperCapNat β ε2 n)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  have hright' :
      C.paperHugeRedCrossWitnessRightSplitErrorProp I κ ε1
        (C.paperHugeRedCrossUnionSlackNat I witnessSize degreeBound)
        (C.paperHugeRedCrossOverlapErrorNat I projCodegreeBound)
        (Twobites.paperCapNat β ε2 n) := by
    refine C.paperHugeRedCrossWitnessRightSplitErrorProp_mono
      (I := I)
      (union₂ := witnessSize * degreeBound)
      (overlap₂ := witnessSize.choose 2 * projCodegreeBound)
      ?_ ?_ hright
    · simp [paperHugeRedCrossUnionSlackNat]
    · exact C.paperHugeRedCrossOverlapErrorNat_le_of_goodEventD_of_paperWitness hD I hI hwitness
  have hleft' :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound +
        (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)) := by
    let B : ℕ := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound
    have herror :
        C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound ≤ B :=
      C.paperHugeRedCrossErrorNat_le_of_goodEventD_of_paperWitness hD I hI hwitness
    have hmono :
        ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
            C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound +
          (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
            ℕ) : ℝ) ≤
        ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) * B +
          (((B.choose 2 : ℕ) : ℝ)) := by
      simpa [B] using
        (cast_mul_add_choose_two_le_of_le
          (a := Twobites.paperKNat κ n - (C.blueImage I).card) herror)
    exact hmono.trans <| by simpa [B] using hleft
  apply C.paper_huge_red_cross_deterministic hD I hI hwitness hcap hcapWeight
  exact
    C.paperHugeRedCrossConcreteBoundNat_le_target_of_split_right_error_bounds I hε1 hcapBase
      (by simpa [paperHugeRedCrossUnionSlackNat] using hunionBase) hleft' hright'

theorem paper_huge_blue_cross_deterministic_of_paperCapNat_of_witnessErrorBounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {β κ ε1 ε2 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hε1 : 0 ≤ ε1)
    (hcapBase :
      Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n - (C.redImage I).card)
    (hleft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      C.paperHugeBlueCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound
        projCodegreeBound (Twobites.paperCapNat β ε2 n)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  let B : ℕ := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound
  have herror :
      C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound ≤ B :=
    C.paperHugeBlueCrossErrorNat_le_of_goodEventD_of_paperWitness hD I hI hwitness
  have hleft' :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound +
        (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)) := by
    have hmono :
        ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
            C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound +
          (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
            ℕ) : ℝ) ≤
        ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) * B +
          (((B.choose 2 : ℕ) : ℝ)) := by
      simpa [B] using
        (cast_mul_add_choose_two_le_of_le
          (a := Twobites.paperKNat κ n - (C.redImage I).card) herror)
    exact hmono.trans <| by simpa [B] using hleft
  have hright' :
      (((Twobites.paperKNat κ n - (C.redImage I).card -
          Twobites.paperCapNat β ε2 n : ℕ) : ℝ) *
          C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound) +
        (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 *
          ((C.paperHugeBlueCrossRightTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
    have hmono :
        (((Twobites.paperKNat κ n - (C.redImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) *
            C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound) +
          (((C.paperHugeBlueCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
            ℕ) : ℝ) ≤
        (((Twobites.paperKNat κ n - (C.redImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * B) +
          (((B.choose 2 : ℕ) : ℝ)) := by
      simpa [B] using
        (cast_mul_add_choose_two_le_of_le
          (a := Twobites.paperKNat κ n - (C.redImage I).card -
            Twobites.paperCapNat β ε2 n) herror)
    exact hmono.trans <| by
      simpa [paperHugeBlueCrossWitnessRightErrorProp, paperHugeBlueCrossRightTarget, B] using
        hright
  exact C.paper_huge_blue_cross_deterministic_of_error_bounds hD I hI hwitness hcap
    hcapWeight hε1 hcapBase hleft' hright'

theorem paper_huge_red_cross_deterministic_of_paperCapNat_of_witnessErrorBounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {β κ ε1 ε2 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hε1 : 0 ≤ ε1)
    (hcapBase :
      Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n - (C.blueImage I).card)
    (hleft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      C.paperHugeRedCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound
        projCodegreeBound (Twobites.paperCapNat β ε2 n)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  let B : ℕ := witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound
  have herror :
      C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound ≤ B :=
    C.paperHugeRedCrossErrorNat_le_of_goodEventD_of_paperWitness hD I hI hwitness
  have hleft' :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound +
        (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)) := by
    have hmono :
        ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
            C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound +
          (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
            ℕ) : ℝ) ≤
        ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) * B +
          (((B.choose 2 : ℕ) : ℝ)) := by
      simpa [B] using
        (cast_mul_add_choose_two_le_of_le
          (a := Twobites.paperKNat κ n - (C.blueImage I).card) herror)
    exact hmono.trans <| by simpa [B] using hleft
  have hright' :
      (((Twobites.paperKNat κ n - (C.blueImage I).card -
          Twobites.paperCapNat β ε2 n : ℕ) : ℝ) *
          C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound) +
        (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
          ℕ) : ℝ) ≤
        ε1 *
          ((C.paperHugeRedCrossRightTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
    have hmono :
        (((Twobites.paperKNat κ n - (C.blueImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) *
            C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound) +
          (((C.paperHugeRedCrossErrorNat I witnessSize degreeBound projCodegreeBound).choose 2 :
            ℕ) : ℝ) ≤
        (((Twobites.paperKNat κ n - (C.blueImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * B) +
          (((B.choose 2 : ℕ) : ℝ)) := by
      simpa [B] using
        (cast_mul_add_choose_two_le_of_le
          (a := Twobites.paperKNat κ n - (C.blueImage I).card -
            Twobites.paperCapNat β ε2 n) herror)
    exact hmono.trans <| by
      simpa [paperHugeRedCrossWitnessRightErrorProp, paperHugeRedCrossRightTarget, B] using
        hright
  exact C.paper_huge_red_cross_deterministic_of_error_bounds hD I hI hwitness hcap
    hcapWeight hε1 hcapBase hleft' hright'

theorem redImage_card_add_paperCapNat_le_paperKNat_add_one_of_card_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρ β ε2 : ℝ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) :
    (C.redImage I).card + Twobites.paperCapNat β ε2 n ≤
      Twobites.paperKNat (ρ + (1 + ε2) * β) n + 1 := by
  calc
    (C.redImage I).card + Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n := by
      exact Nat.add_le_add_right hred _
    _ ≤ Twobites.paperKNat (ρ + (1 + ε2) * β) n + 1 := by
      exact Twobites.paperKNat_add_paperCapNat_le_paperKNat_add_one hn hρ hβ hε2

theorem blueImage_card_add_paperCapNat_le_paperKNat_add_one_of_card_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρ β ε2 : ℝ}
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) :
    (C.blueImage I).card + Twobites.paperCapNat β ε2 n ≤
      Twobites.paperKNat (ρ + (1 + ε2) * β) n + 1 := by
  calc
    (C.blueImage I).card + Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n := by
      exact Nat.add_le_add_right hblue _
    _ ≤ Twobites.paperKNat (ρ + (1 + ε2) * β) n + 1 := by
      exact Twobites.paperKNat_add_paperCapNat_le_paperKNat_add_one hn hρ hβ hε2

theorem redImage_card_add_paperCapNat_le_paperKNat_of_card_le_of_one_le_gap
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρ β ε2 δ : ℝ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) :
    (C.redImage I).card + Twobites.paperCapNat β ε2 n ≤
      Twobites.paperKNat (ρ + (1 + ε2) * β + δ) n := by
  calc
    (C.redImage I).card + Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat (ρ + (1 + ε2) * β) n + 1 := by
      exact C.redImage_card_add_paperCapNat_le_paperKNat_add_one_of_card_le I hred hn hρ hβ hε2
    _ ≤ Twobites.paperKNat (ρ + (1 + ε2) * β + δ) n := by
      exact Twobites.paperKNat_add_one_le_paperKNat_of_one_le_gap
        (by
          have hfac : 0 ≤ 1 + ε2 := by linarith
          have hcap : 0 ≤ (1 + ε2) * β := by exact mul_nonneg hfac hβ
          linarith)
        hgap

theorem blueImage_card_add_paperCapNat_le_paperKNat_of_card_le_of_one_le_gap
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρ β ε2 δ : ℝ}
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) :
    (C.blueImage I).card + Twobites.paperCapNat β ε2 n ≤
      Twobites.paperKNat (ρ + (1 + ε2) * β + δ) n := by
  calc
    (C.blueImage I).card + Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat (ρ + (1 + ε2) * β) n + 1 := by
      exact C.blueImage_card_add_paperCapNat_le_paperKNat_add_one_of_card_le I hblue hn hρ hβ hε2
    _ ≤ Twobites.paperKNat (ρ + (1 + ε2) * β + δ) n := by
      exact Twobites.paperKNat_add_one_le_paperKNat_of_one_le_gap
        (by
          have hfac : 0 ≤ 1 + ε2 := by linarith
          have hcap : 0 ≤ (1 + ε2) * β := by exact mul_nonneg hfac hβ
          linarith)
        hgap

theorem redImage_card_add_paperCapNat_le_paperKNat_of_card_le_of_one_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρ β ε2 δ κ : ℝ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ) :
    (C.redImage I).card + Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n := by
  calc
    (C.redImage I).card + Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n := by
      exact Nat.add_le_add_right hred _
    _ ≤ Twobites.paperKNat κ n := by
      exact Twobites.paperKNat_add_paperCapNat_le_paperKNat_of_one_le_gap_of_le
        hn hρ hβ hε2 hgap hκ

theorem redImage_card_add_paperCapNat_add_paperKNat_le_paperKNat_of_card_le_of_two_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρ β ε2 δ η κ : ℝ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ)
    (hgap : 2 ≤ Twobites.paperK η n) (hκ : ρ + (1 + ε2) * β + δ + η ≤ κ) :
    (C.redImage I).card + Twobites.paperCapNat β ε2 n + Twobites.paperKNat δ n ≤
      Twobites.paperKNat κ n := by
  calc
    (C.redImage I).card + Twobites.paperCapNat β ε2 n + Twobites.paperKNat δ n ≤
        Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n + Twobites.paperKNat δ n := by
      omega
    _ ≤ Twobites.paperKNat κ n := by
      exact Twobites.paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_of_two_le_gap_of_le
        hn hρ hβ hε2 hδ hgap hκ

theorem blueImage_card_add_paperCapNat_le_paperKNat_of_card_le_of_one_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρ β ε2 δ κ : ℝ}
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ) :
    (C.blueImage I).card + Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n := by
  calc
    (C.blueImage I).card + Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n := by
      exact Nat.add_le_add_right hblue _
    _ ≤ Twobites.paperKNat κ n := by
      exact Twobites.paperKNat_add_paperCapNat_le_paperKNat_of_one_le_gap_of_le
        hn hρ hβ hε2 hgap hκ

theorem blueImage_card_add_paperCapNat_add_paperKNat_le_paperKNat_of_card_le_of_two_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρ β ε2 δ η κ : ℝ}
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ)
    (hgap : 2 ≤ Twobites.paperK η n) (hκ : ρ + (1 + ε2) * β + δ + η ≤ κ) :
    (C.blueImage I).card + Twobites.paperCapNat β ε2 n + Twobites.paperKNat δ n ≤
      Twobites.paperKNat κ n := by
  calc
    (C.blueImage I).card + Twobites.paperCapNat β ε2 n + Twobites.paperKNat δ n ≤
        Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n + Twobites.paperKNat δ n := by
      omega
    _ ≤ Twobites.paperKNat κ n := by
      exact Twobites.paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_of_two_le_gap_of_le
        hn hρ hβ hε2 hδ hgap hκ

theorem redImage_card_le_card (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.redImage I).card ≤ I.card := by
  simpa [ConstructionData.redImage] using
    (Finset.card_image_le (s := I) (f := C.redProj))

theorem blueImage_card_le_card (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.blueImage I).card ≤ I.card := by
  simpa [ConstructionData.blueImage] using
    (Finset.card_image_le (s := I) (f := C.blueProj))

theorem blueImage_card_le_paperKNat_half_of_sum_le_of_blue_le_red
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ}
    (hsum : (C.redImage I).card + (C.blueImage I).card ≤ Twobites.paperKNat κ n)
    (hblue : (C.blueImage I).card ≤ (C.redImage I).card) (hκ : 0 ≤ κ) :
    (C.blueImage I).card ≤ Twobites.paperKNat (κ / 2) n := by
  have htwo : 2 * (C.blueImage I).card ≤ (C.redImage I).card + (C.blueImage I).card := by
    omega
  exact Twobites.le_paperKNat_half_of_two_mul_le_paperKNat hκ (htwo.trans hsum)

theorem redImage_card_le_paperKNat_half_of_sum_le_of_red_le_blue
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ : ℝ}
    (hsum : (C.redImage I).card + (C.blueImage I).card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ (C.blueImage I).card) (hκ : 0 ≤ κ) :
    (C.redImage I).card ≤ Twobites.paperKNat (κ / 2) n := by
  have htwo : 2 * (C.redImage I).card ≤ (C.redImage I).card + (C.blueImage I).card := by
    omega
  exact Twobites.le_paperKNat_half_of_two_mul_le_paperKNat hκ (htwo.trans hsum)

theorem paperKNat_le_paperKNat_sub_redImage_card_sub_paperCapNat_of_card_le_of_two_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρ β ε2 δ η κ : ℝ}
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ)
    (hgap : 2 ≤ Twobites.paperK η n) (hκ : ρ + (1 + ε2) * β + δ + η ≤ κ) :
    Twobites.paperKNat δ n ≤
      Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n := by
  have hsum :=
    C.redImage_card_add_paperCapNat_add_paperKNat_le_paperKNat_of_card_le_of_two_le_gap_of_le
      I hred hn hρ hβ hε2 hδ hgap hκ
  omega

theorem paperKNat_le_paperKNat_sub_blueImage_card_sub_paperCapNat_of_card_le_of_two_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρ β ε2 δ η κ : ℝ}
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ)
    (hgap : 2 ≤ Twobites.paperK η n) (hκ : ρ + (1 + ε2) * β + δ + η ≤ κ) :
    Twobites.paperKNat δ n ≤
      Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n := by
  have hsum :=
    C.blueImage_card_add_paperCapNat_add_paperKNat_le_paperKNat_of_card_le_of_two_le_gap_of_le
      I hblue hn hρ hβ hε2 hδ hgap hκ
  omega

theorem paper_risi_hLossGap_of_blueLeft_of_redRight_subGap_of_card_le_of_one_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρB β ε2 δ κ ε1 : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hn : 0 < n) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρB + (1 + ε2) * β + δ ≤ κ)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (Twobites.paperCapNat β ε2 n : ℝ) *
          ((Twobites.paperKNat κ n - (C.blueImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) :
    paperRISILossNat κ ε1 n ≤
      C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) := by
  have hredκ : (C.redImage I).card ≤ Twobites.paperKNat κ n := by
    exact (redImage_card_le_card C I).trans hI
  have hblueCap :
      (C.blueImage I).card + Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat κ n := by
    exact
      blueImage_card_add_paperCapNat_le_paperKNat_of_card_le_of_one_le_gap_of_le
        C I hblue hn hρB hβ hε2 hgap hκ
  exact
    C.paper_risi_hLossGap_of_blueLeft_of_redRight_subGap
      I (κ := κ) (ε1 := ε1) (cap := Twobites.paperCapNat β ε2 n) hredκ hblueCap hLoss

theorem paper_risi_hLossGap_of_blueRight_of_redLeft_subGap_of_card_le_of_one_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρR β ε2 δ κ ε1 : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρR + (1 + ε2) * β + δ ≤ κ)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (Twobites.paperCapNat β ε2 n : ℝ) *
          ((Twobites.paperKNat κ n - (C.redImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) :
    paperRISILossNat κ ε1 n ≤
      C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) := by
  have hblueκ : (C.blueImage I).card ≤ Twobites.paperKNat κ n := by
    exact (blueImage_card_le_card C I).trans hI
  have hredCap :
      (C.redImage I).card + Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat κ n := by
    exact
      redImage_card_add_paperCapNat_le_paperKNat_of_card_le_of_one_le_gap_of_le
        C I hred hn hρR hβ hε2 hgap hκ
  exact
    C.paper_risi_hLossGap_of_blueRight_of_redLeft_subGap
      I (κ := κ) (ε1 := ε1) (cap := Twobites.paperCapNat β ε2 n) hblueκ hredCap hLoss

theorem paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_card_le_of_one_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρB β ε2 δ κ ε1 : ℝ} {gap : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hn : 0 < n) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapCap : 1 ≤ Twobites.paperK δ n) (hκ : ρB + (1 + ε2) * β + δ ≤ κ)
    (hgap :
      gap ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (Twobites.paperCapNat β ε2 n : ℝ) * (gap : ℝ)) :
    paperRISILossNat κ ε1 n ≤
      C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) := by
  have hLoss' :
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (Twobites.paperCapNat β ε2 n : ℝ) *
          ((Twobites.paperKNat κ n - (C.blueImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) := by
    calc
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
          (Twobites.paperCapNat β ε2 n : ℝ) * (gap : ℝ) := hLoss
      _ ≤
          (Twobites.paperCapNat β ε2 n : ℝ) *
            ((Twobites.paperKNat κ n - (C.blueImage I).card -
                  Twobites.paperCapNat β ε2 n : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hgap) (Nat.cast_nonneg _)
  exact
    C.paper_risi_hLossGap_of_blueLeft_of_redRight_subGap_of_card_le_of_one_le_gap_of_le
      I hI hblue hn hρB hβ hε2 hgapCap hκ hLoss'

theorem paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_card_le_of_one_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρR β ε2 δ κ ε1 : ℝ} {gap : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapCap : 1 ≤ Twobites.paperK δ n) (hκ : ρR + (1 + ε2) * β + δ ≤ κ)
    (hgap :
      gap ≤
        Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (Twobites.paperCapNat β ε2 n : ℝ) * (gap : ℝ)) :
    paperRISILossNat κ ε1 n ≤
      C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) := by
  have hLoss' :
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (Twobites.paperCapNat β ε2 n : ℝ) *
          ((Twobites.paperKNat κ n - (C.redImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) := by
    calc
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
          (Twobites.paperCapNat β ε2 n : ℝ) * (gap : ℝ) := hLoss
      _ ≤
          (Twobites.paperCapNat β ε2 n : ℝ) *
            ((Twobites.paperKNat κ n - (C.redImage I).card -
                  Twobites.paperCapNat β ε2 n : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hgap) (Nat.cast_nonneg _)
  exact
    C.paper_risi_hLossGap_of_blueRight_of_redLeft_subGap_of_card_le_of_one_le_gap_of_le
      I hI hred hn hρR hβ hε2 hgapCap hκ hLoss'

theorem paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_card_le_of_two_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρB β ε2 δ η κ ε1 : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hn : 0 < n) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ)
    (hgap2 : 2 ≤ Twobites.paperK η n) (hκ : ρB + (1 + ε2) * β + δ + η ≤ κ)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (Twobites.paperCapNat β ε2 n : ℝ) * (Twobites.paperKNat δ n : ℝ)) :
    paperRISILossNat κ ε1 n ≤
      C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) := by
  have hgapCap :
      1 ≤ Twobites.paperK (δ + η) n := by
    rw [← Twobites.paperK_add (κ₁ := δ) (κ₂ := η) n]
    have hδK : 0 ≤ Twobites.paperK δ n := Twobites.paperK_nonneg hδ n
    linarith
  have hκCap : ρB + (1 + ε2) * β + (δ + η) ≤ κ := by
    linarith
  have hgap :
      Twobites.paperKNat δ n ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n := by
    exact
      C.paperKNat_le_paperKNat_sub_blueImage_card_sub_paperCapNat_of_card_le_of_two_le_gap_of_le
        I hblue hn hρB hβ hε2 hδ hgap2 hκ
  exact
    C.paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_card_le_of_one_le_gap_of_le
      I (ρB := ρB) (β := β) (ε2 := ε2) (δ := δ + η) (κ := κ) (ε1 := ε1)
      (gap := Twobites.paperKNat δ n) hI hblue hn hρB hβ hε2 hgapCap hκCap hgap hLoss

theorem paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_card_le_of_two_le_gap_of_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ρR β ε2 δ η κ ε1 : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ)
    (hgap2 : 2 ≤ Twobites.paperK η n) (hκ : ρR + (1 + ε2) * β + δ + η ≤ κ)
    (hLoss :
      (paperRISILossNat κ ε1 n : ℝ) +
          (((Twobites.paperKNat κ n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat κ n : ℝ) - 1) ≤
        (Twobites.paperCapNat β ε2 n : ℝ) * (Twobites.paperKNat δ n : ℝ)) :
    paperRISILossNat κ ε1 n ≤
      C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) := by
  have hgapCap :
      1 ≤ Twobites.paperK (δ + η) n := by
    rw [← Twobites.paperK_add (κ₁ := δ) (κ₂ := η) n]
    have hδK : 0 ≤ Twobites.paperK δ n := Twobites.paperK_nonneg hδ n
    linarith
  have hκCap : ρR + (1 + ε2) * β + (δ + η) ≤ κ := by
    linarith
  have hgap :
      Twobites.paperKNat δ n ≤
        Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n := by
    exact
      C.paperKNat_le_paperKNat_sub_redImage_card_sub_paperCapNat_of_card_le_of_two_le_gap_of_le
        I hred hn hρR hβ hε2 hδ hgap2 hκ
  exact
    C.paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_card_le_of_one_le_gap_of_le
      I (ρR := ρR) (β := β) (ε2 := ε2) (δ := δ + η) (κ := κ) (ε1 := ε1)
      (gap := Twobites.paperKNat δ n) hI hred hn hρR hβ hε2 hgapCap hκCap hgap hLoss

theorem paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_paperNearOne
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε ε1 : ℝ}
    (hI : I.card ≤ Twobites.paperKNat (1 + ε) n)
    (hblue :
      (C.blueImage I).card ≤ Twobites.paperKNat (((1 + ε) * (2 + ε)) / 4) n)
    (hn : 0 < n) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hgap2 : 2 ≤ Twobites.paperK (ε * (1 - ε) / 8) n)
    (hLoss :
      (paperRISILossNat (1 + ε) ε1 n : ℝ) +
          (((Twobites.paperKNat (1 + ε) n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat (1 + ε) n : ℝ) - 1) ≤
        (Twobites.paperCapNat (1 / 2) 0 n : ℝ) *
          (Twobites.paperKNat (ε * (1 - ε) / 8) n : ℝ)) :
    paperRISILossNat (1 + ε) ε1 n ≤
      C.paperSection4OpenPairTargetNat I (1 + ε) (Twobites.paperCapNat (1 / 2) 0 n) := by
  have hρB : 0 ≤ (((1 + ε) * (2 + ε)) / 4 : ℝ) := by
    nlinarith
  have hδ : 0 ≤ ε * (1 - ε) / 8 := by
    nlinarith
  have hκ :
      (((1 + ε) * (2 + ε)) / 4 : ℝ) +
          (1 + (0 : ℝ)) * (1 / 2 : ℝ) +
          ε * (1 - ε) / 8 + ε * (1 - ε) / 8 ≤
        1 + ε := by
    nlinarith
  exact
    C.paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_card_le_of_two_le_gap_of_le
      I (ρB := ((1 + ε) * (2 + ε)) / 4) (β := (1 / 2 : ℝ)) (ε2 := 0)
      (δ := ε * (1 - ε) / 8) (η := ε * (1 - ε) / 8) (κ := 1 + ε) (ε1 := ε1)
      hI hblue hn hρB (by norm_num) (by norm_num) hδ hgap2 hκ hLoss

theorem paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_paperNearOne
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε ε1 : ℝ}
    (hI : I.card ≤ Twobites.paperKNat (1 + ε) n)
    (hred :
      (C.redImage I).card ≤ Twobites.paperKNat (((1 + ε) * (2 + ε)) / 4) n)
    (hn : 0 < n) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hgap2 : 2 ≤ Twobites.paperK (ε * (1 - ε) / 8) n)
    (hLoss :
      (paperRISILossNat (1 + ε) ε1 n : ℝ) +
          (((Twobites.paperKNat (1 + ε) n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat (1 + ε) n : ℝ) - 1) ≤
        (Twobites.paperCapNat (1 / 2) 0 n : ℝ) *
          (Twobites.paperKNat (ε * (1 - ε) / 8) n : ℝ)) :
    paperRISILossNat (1 + ε) ε1 n ≤
      C.paperSection4OpenPairTargetNat I (1 + ε) (Twobites.paperCapNat (1 / 2) 0 n) := by
  have hρR : 0 ≤ (((1 + ε) * (2 + ε)) / 4 : ℝ) := by
    nlinarith
  have hδ : 0 ≤ ε * (1 - ε) / 8 := by
    nlinarith
  have hκ :
      (((1 + ε) * (2 + ε)) / 4 : ℝ) +
          (1 + (0 : ℝ)) * (1 / 2 : ℝ) +
          ε * (1 - ε) / 8 + ε * (1 - ε) / 8 ≤
        1 + ε := by
    nlinarith
  exact
    C.paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_card_le_of_two_le_gap_of_le
      I (ρR := ((1 + ε) * (2 + ε)) / 4) (β := (1 / 2 : ℝ)) (ε2 := 0)
      (δ := ε * (1 - ε) / 8) (η := ε * (1 - ε) / 8) (κ := 1 + ε) (ε1 := ε1)
      hI hred hn hρR (by norm_num) (by norm_num) hδ hgap2 hκ hLoss

theorem paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_paperNearOne_of_two_div_le_loglog
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε ε1 : ℝ}
    (hI : I.card ≤ Twobites.paperKNat (1 + ε) n)
    (hblue :
      (C.blueImage I).card ≤ Twobites.paperKNat (((1 + ε) * (2 + ε)) / 4) n)
    (hn : 1 < n) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hloglog : 2 / (ε * (1 - ε) / 8) ≤ Real.log (Real.log (n : ℝ)))
    (hLoss :
      (paperRISILossNat (1 + ε) ε1 n : ℝ) +
          (((Twobites.paperKNat (1 + ε) n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat (1 + ε) n : ℝ) - 1) ≤
        (Twobites.paperCapNat (1 / 2) 0 n : ℝ) *
          (Twobites.paperKNat (ε * (1 - ε) / 8) n : ℝ)) :
    paperRISILossNat (1 + ε) ε1 n ≤
      C.paperSection4OpenPairTargetNat I (1 + ε) (Twobites.paperCapNat (1 / 2) 0 n) := by
  have hηpos : 0 < ε * (1 - ε) / 8 := by
    nlinarith
  have hηle : ε * (1 - ε) / 8 ≤ 1 := by
    nlinarith
  have hgap2 : 2 ≤ Twobites.paperK (ε * (1 - ε) / 8) n :=
    Twobites.two_le_paperK_of_two_div_le_of_le_one hn hηpos hηle hloglog
  exact
    C.paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_paperNearOne
      I hI hblue (show 0 < n by exact Nat.lt_trans Nat.zero_lt_one hn) hε0.le hε1.le hgap2
      hLoss

theorem paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_paperNearOne_of_two_div_le_loglog
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε ε1 : ℝ}
    (hI : I.card ≤ Twobites.paperKNat (1 + ε) n)
    (hred :
      (C.redImage I).card ≤ Twobites.paperKNat (((1 + ε) * (2 + ε)) / 4) n)
    (hn : 1 < n) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hloglog : 2 / (ε * (1 - ε) / 8) ≤ Real.log (Real.log (n : ℝ)))
    (hLoss :
      (paperRISILossNat (1 + ε) ε1 n : ℝ) +
          (((Twobites.paperKNat (1 + ε) n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat (1 + ε) n : ℝ) - 1) ≤
        (Twobites.paperCapNat (1 / 2) 0 n : ℝ) *
          (Twobites.paperKNat (ε * (1 - ε) / 8) n : ℝ)) :
    paperRISILossNat (1 + ε) ε1 n ≤
      C.paperSection4OpenPairTargetNat I (1 + ε) (Twobites.paperCapNat (1 / 2) 0 n) := by
  have hηpos : 0 < ε * (1 - ε) / 8 := by
    nlinarith
  have hηle : ε * (1 - ε) / 8 ≤ 1 := by
    nlinarith
  have hgap2 : 2 ≤ Twobites.paperK (ε * (1 - ε) / 8) n :=
    Twobites.two_le_paperK_of_two_div_le_of_le_one hn hηpos hηle hloglog
  exact
    C.paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_paperNearOne
      I hI hred (show 0 < n by exact Nat.lt_trans Nat.zero_lt_one hn) hε0.le hε1.le hgap2
      hLoss

theorem blueImage_card_le_paperKNat_of_paperNearOneSum_of_blue_le_red
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hsum :
      (C.redImage I).card + (C.blueImage I).card ≤
        Twobites.paperKNat (((1 + ε) * (2 + ε)) / 2) n)
    (hblue : (C.blueImage I).card ≤ (C.redImage I).card) (hε : 0 ≤ ε) :
    (C.blueImage I).card ≤ Twobites.paperKNat (((1 + ε) * (2 + ε)) / 4) n := by
  have hκ : 0 ≤ (((1 + ε) * (2 + ε)) / 2 : ℝ) := by
    nlinarith
  have hhalf :
      (C.blueImage I).card ≤
        Twobites.paperKNat ((((1 + ε) * (2 + ε)) / 2) / 2) n :=
    C.blueImage_card_le_paperKNat_half_of_sum_le_of_blue_le_red I hsum hblue hκ
  have hcoeff : ((((1 + ε) * (2 + ε)) / 2) / 2 : ℝ) = (((1 + ε) * (2 + ε)) / 4 : ℝ) := by
    ring
  simpa [hcoeff] using hhalf

theorem redImage_card_le_paperKNat_of_paperNearOneSum_of_red_le_blue
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hsum :
      (C.redImage I).card + (C.blueImage I).card ≤
        Twobites.paperKNat (((1 + ε) * (2 + ε)) / 2) n)
    (hred : (C.redImage I).card ≤ (C.blueImage I).card) (hε : 0 ≤ ε) :
    (C.redImage I).card ≤ Twobites.paperKNat (((1 + ε) * (2 + ε)) / 4) n := by
  have hκ : 0 ≤ (((1 + ε) * (2 + ε)) / 2 : ℝ) := by
    nlinarith
  have hhalf :
      (C.redImage I).card ≤
        Twobites.paperKNat ((((1 + ε) * (2 + ε)) / 2) / 2) n :=
    C.redImage_card_le_paperKNat_half_of_sum_le_of_red_le_blue I hsum hred hκ
  have hcoeff : ((((1 + ε) * (2 + ε)) / 2) / 2 : ℝ) = (((1 + ε) * (2 + ε)) / 4 : ℝ) := by
    ring
  simpa [hcoeff] using hhalf

set_option linter.style.longLine false in
theorem
    paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_paperNearOneSum_of_blue_le_red_of_two_div_le_loglog
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε ε1 : ℝ}
    (hI : I.card ≤ Twobites.paperKNat (1 + ε) n)
    (hsum :
      (C.redImage I).card + (C.blueImage I).card ≤
        Twobites.paperKNat (((1 + ε) * (2 + ε)) / 2) n)
    (hblueLeRed : (C.blueImage I).card ≤ (C.redImage I).card)
    (hn : 1 < n) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hloglog : 2 / (ε * (1 - ε) / 8) ≤ Real.log (Real.log (n : ℝ)))
    (hLoss :
      (paperRISILossNat (1 + ε) ε1 n : ℝ) +
          (((Twobites.paperKNat (1 + ε) n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat (1 + ε) n : ℝ) - 1) ≤
        (Twobites.paperCapNat (1 / 2) 0 n : ℝ) *
          (Twobites.paperKNat (ε * (1 - ε) / 8) n : ℝ)) :
    paperRISILossNat (1 + ε) ε1 n ≤
      C.paperSection4OpenPairTargetNat I (1 + ε) (Twobites.paperCapNat (1 / 2) 0 n) := by
  have hblue :
      (C.blueImage I).card ≤ Twobites.paperKNat (((1 + ε) * (2 + ε)) / 4) n :=
    C.blueImage_card_le_paperKNat_of_paperNearOneSum_of_blue_le_red I hsum hblueLeRed hε0.le
  exact
    C.paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_paperNearOne_of_two_div_le_loglog
      I hI hblue hn hε0 hε1 hloglog hLoss

set_option linter.style.longLine false in
theorem
    paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_paperNearOneSum_of_red_le_blue_of_two_div_le_loglog
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε ε1 : ℝ}
    (hI : I.card ≤ Twobites.paperKNat (1 + ε) n)
    (hsum :
      (C.redImage I).card + (C.blueImage I).card ≤
        Twobites.paperKNat (((1 + ε) * (2 + ε)) / 2) n)
    (hredLeBlue : (C.redImage I).card ≤ (C.blueImage I).card)
    (hn : 1 < n) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hloglog : 2 / (ε * (1 - ε) / 8) ≤ Real.log (Real.log (n : ℝ)))
    (hLoss :
      (paperRISILossNat (1 + ε) ε1 n : ℝ) +
          (((Twobites.paperKNat (1 + ε) n -
                ((C.redImage I).card + (C.blueImage I).card) : ℕ) : ℕ) : ℝ) *
            ((Twobites.paperKNat (1 + ε) n : ℝ) - 1) ≤
        (Twobites.paperCapNat (1 / 2) 0 n : ℝ) *
          (Twobites.paperKNat (ε * (1 - ε) / 8) n : ℝ)) :
    paperRISILossNat (1 + ε) ε1 n ≤
      C.paperSection4OpenPairTargetNat I (1 + ε) (Twobites.paperCapNat (1 / 2) 0 n) := by
  have hred :
      (C.redImage I).card ≤ Twobites.paperKNat (((1 + ε) * (2 + ε)) / 4) n :=
    C.redImage_card_le_paperKNat_of_paperNearOneSum_of_red_le_blue I hsum hredLeBlue hε0.le
  exact
    C.paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_paperNearOne_of_two_div_le_loglog
      I hI hred hn hε0 hε1 hloglog hLoss

theorem paper_huge_blue_cross_deterministic_of_paperCapNat_of_witnessErrorBounds_of_additiveCapBase
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {β κ ε1 ε2 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hε1 : 0 ≤ ε1)
    (hcapBase :
      (C.redImage I).card + Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n)
    (hleft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      C.paperHugeBlueCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound
        projCodegreeBound (Twobites.paperCapNat β ε2 n)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  apply C.paper_huge_blue_cross_deterministic_of_paperCapNat_of_witnessErrorBounds hD I
    hI hwitness hcap hcapWeight hε1
  · have hred : (C.redImage I).card ≤ Twobites.paperKNat κ n := (C.redImage_card_le_card I).trans hI
    exact (Nat.le_sub_iff_add_le hred).2 <| by simpa [Nat.add_comm] using hcapBase
  · exact hleft
  · exact hright

theorem paper_huge_red_cross_deterministic_of_paperCapNat_of_witnessErrorBounds_of_additiveCapBase
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {β κ ε1 ε2 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hε1 : 0 ≤ ε1)
    (hcapBase :
      (C.blueImage I).card + Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n)
    (hleft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      C.paperHugeRedCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound
        projCodegreeBound (Twobites.paperCapNat β ε2 n)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  apply C.paper_huge_red_cross_deterministic_of_paperCapNat_of_witnessErrorBounds hD I
    hI hwitness hcap hcapWeight hε1
  · have hblue : (C.blueImage I).card ≤ Twobites.paperKNat κ n :=
      (C.blueImage_card_le_card I).trans hI
    exact (Nat.le_sub_iff_add_le hblue).2 <| by simpa [Nat.add_comm] using hcapBase
  · exact hleft
  · exact hright

theorem paper_huge_blue_cross_deterministic_of_card_le_of_one_le_gap_of_witnessErrorBounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hleft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      C.paperHugeBlueCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound
        projCodegreeBound (Twobites.paperCapNat β ε2 n)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  apply
    C.paper_huge_blue_cross_deterministic_of_paperCapNat_of_witnessErrorBounds_of_additiveCapBase
      hD I hI hwitness hcap hcapWeight hε1
  · exact C.redImage_card_add_paperCapNat_le_paperKNat_of_card_le_of_one_le_gap_of_le I
      hred hn hρ hβ hε2 hgap hκ
  · exact hleft
  · exact hright

theorem paper_huge_red_cross_deterministic_of_card_le_of_one_le_gap_of_witnessErrorBounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hleft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hright :
      C.paperHugeRedCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound
        projCodegreeBound (Twobites.paperCapNat β ε2 n)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  apply
    C.paper_huge_red_cross_deterministic_of_paperCapNat_of_witnessErrorBounds_of_additiveCapBase
      hD I hI hwitness hcap hcapWeight hε1
  · exact C.blueImage_card_add_paperCapNat_le_paperKNat_of_card_le_of_one_le_gap_of_le I
      hblue hn hρ hβ hε2 hgap hκ
  · exact hleft
  · exact hright

theorem paper_huge_blue_cross_deterministic_of_card_le_of_one_le_gap_of_three_mul_error_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n)
    (hleftSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 * (((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) - 1))
    (hrightSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - (C.redImage I).card -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  apply C.paper_huge_blue_cross_deterministic_of_card_le_of_one_le_gap_of_witnessErrorBounds
    hD I hI hwitness hred hcap hcapWeight hn hρ hβ hε2 hgap hκ hε1
  · exact C.paperHugeBlueCrossLeftError_of_le_of_three_mul_le I
      (Nat.le_trans hB (Nat.sub_le _ _)) hleftSmall
  · exact C.paperHugeBlueCrossWitnessRightErrorProp_of_le_of_three_mul_le I hε1 hB hrightSmall

theorem paper_huge_red_cross_deterministic_of_card_le_of_one_le_gap_of_three_mul_error_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n)
    (hleftSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 * (((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) - 1))
    (hrightSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - (C.blueImage I).card -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  apply C.paper_huge_red_cross_deterministic_of_card_le_of_one_le_gap_of_witnessErrorBounds
    hD I hI hwitness hblue hcap hcapWeight hn hρ hβ hε2 hgap hκ hε1
  · exact C.paperHugeRedCrossLeftError_of_le_of_three_mul_le I
      (Nat.le_trans hB (Nat.sub_le _ _)) hleftSmall
  · exact C.paperHugeRedCrossWitnessRightErrorProp_of_le_of_three_mul_le I hε1 hB hrightSmall

theorem paper_huge_blue_cross_deterministic_of_card_le_of_one_le_gap_of_right_three_mul_error_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n)
    (hrightSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - (C.redImage I).card -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  have hleftSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 * (((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) - 1) := by
    have hmono :
        ε1 *
            (((Twobites.paperKNat κ n - (C.redImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) ≤
          ε1 * (((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) - 1) := by
      have hsub :
          (((Twobites.paperKNat κ n - (C.redImage I).card -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) ≤
            (((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) - 1) := by
        exact sub_le_sub_right (by exact_mod_cast (Nat.sub_le _ _)) 1
      exact mul_le_mul_of_nonneg_left hsub hε1
    exact hrightSmall.trans hmono
  exact C.paper_huge_blue_cross_deterministic_of_card_le_of_one_le_gap_of_three_mul_error_le
    hD I hI hwitness hred hcap hcapWeight hn hρ hβ hε2 hgap hκ hε1 hB hleftSmall
    hrightSmall

theorem paper_huge_red_cross_deterministic_of_card_le_of_one_le_gap_of_right_three_mul_error_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n)
    (hrightSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - (C.blueImage I).card -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  have hleftSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 * (((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) - 1) := by
    have hmono :
        ε1 *
            (((Twobites.paperKNat κ n - (C.blueImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) ≤
          ε1 * (((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) - 1) := by
      have hsub :
          (((Twobites.paperKNat κ n - (C.blueImage I).card -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) ≤
            (((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) - 1) := by
        exact sub_le_sub_right (by exact_mod_cast (Nat.sub_le _ _)) 1
      exact mul_le_mul_of_nonneg_left hsub hε1
    exact hrightSmall.trans hmono
  exact C.paper_huge_red_cross_deterministic_of_card_le_of_one_le_gap_of_three_mul_error_le
    hD I hI hwitness hblue hcap hcapWeight hn hρ hβ hε2 hgap hκ hε1 hB hleftSmall
    hrightSmall

theorem three_mul_le_mul_sub_one_mono {b d₁ d₂ : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hd : d₁ ≤ d₂)
    (hsmall : (3 : ℝ) * (b : ℝ) ≤ ε * (((d₁ : ℕ) : ℝ) - 1)) :
    (3 : ℝ) * (b : ℝ) ≤ ε * (((d₂ : ℕ) : ℝ) - 1) := by
  have hmono : ε * (((d₁ : ℕ) : ℝ) - 1) ≤ ε * (((d₂ : ℕ) : ℝ) - 1) := by
    have hsub : (((d₁ : ℕ) : ℝ) - 1) ≤ (((d₂ : ℕ) : ℝ) - 1) := by
      exact sub_le_sub_right (by exact_mod_cast hd) 1
    exact mul_le_mul_of_nonneg_left hsub hε
  exact hsmall.trans hmono

theorem three_mul_le_mul_sub_one_mono_real {W : ℝ} {d₁ d₂ : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hd : d₁ ≤ d₂)
    (hsmall : (3 : ℝ) * W ≤ ε * (((d₁ : ℕ) : ℝ) - 1)) :
    (3 : ℝ) * W ≤ ε * (((d₂ : ℕ) : ℝ) - 1) := by
  have hmono : ε * (((d₁ : ℕ) : ℝ) - 1) ≤ ε * (((d₂ : ℕ) : ℝ) - 1) := by
    have hsub : (((d₁ : ℕ) : ℝ) - 1) ≤ (((d₂ : ℕ) : ℝ) - 1) := by
      exact sub_le_sub_right (by exact_mod_cast hd) 1
    exact mul_le_mul_of_nonneg_left hsub hε
  exact hsmall.trans hmono

theorem paper_huge_blue_cross_deterministic_of_card_le_of_paramDeficit_of_right_three_mul_error_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρ n - Twobites.paperCapNat β ε2 n)
    (hrightSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρ n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  have hdeficit :
      Twobites.paperKNat κ n - Twobites.paperKNat ρ n - Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n := by
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_left hred _) _
  have hB' :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n :=
    hB.trans hdeficit
  have hrightSmall' :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - (C.redImage I).card -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    exact three_mul_le_mul_sub_one_mono hε1 hdeficit hrightSmall
  exact C.paper_huge_blue_cross_deterministic_of_card_le_of_one_le_gap_of_right_three_mul_error_le
    hD I hI hwitness hred hcap hcapWeight hn hρ hβ hε2 hgap hκ hε1 hB' hrightSmall'

theorem paper_huge_red_cross_deterministic_of_card_le_of_paramDeficit_of_right_three_mul_error_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρ n - Twobites.paperCapNat β ε2 n)
    (hrightSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρ n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  have hdeficit :
      Twobites.paperKNat κ n - Twobites.paperKNat ρ n - Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n := by
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_left hblue _) _
  have hB' :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n :=
    hB.trans hdeficit
  have hrightSmall' :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - (C.blueImage I).card -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    exact three_mul_le_mul_sub_one_mono hε1 hdeficit hrightSmall
  exact C.paper_huge_red_cross_deterministic_of_card_le_of_one_le_gap_of_right_three_mul_error_le
    hD I hI hwitness hblue hcap hcapWeight hn hρ hβ hε2 hgap hκ hε1 hB' hrightSmall'

theorem
    paper_huge_blue_cross_deterministic_of_additiveParamDeficit_of_right_three_mul_error_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hB :
      Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n +
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) ≤
        Twobites.paperKNat κ n)
    (hrightSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρ n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  have hk :
      Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n := by
    exact le_trans (Nat.le_add_right _ _) hB
  have hB' :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρ n - Twobites.paperCapNat β ε2 n := by
    have hbase :
        witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
          Twobites.paperKNat κ n - (Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n) := by
      exact (Nat.le_sub_iff_add_le hk).2 <| by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hB
    simpa [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbase
  exact
    C.paper_huge_blue_cross_deterministic_of_card_le_of_paramDeficit_of_right_three_mul_error_le
      hD I hI hwitness hred hcap hcapWeight hn hρ hβ hε2 hgap hκ hε1 hB' hrightSmall

theorem
    paper_huge_red_cross_deterministic_of_additiveParamDeficit_of_right_three_mul_error_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hB :
      Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n +
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) ≤
        Twobites.paperKNat κ n)
    (hrightSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρ n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  have hk :
      Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n := by
    exact le_trans (Nat.le_add_right _ _) hB
  have hB' :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρ n - Twobites.paperCapNat β ε2 n := by
    have hbase :
        witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
          Twobites.paperKNat κ n - (Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n) := by
      exact (Nat.le_sub_iff_add_le hk).2 <| by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hB
    simpa [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbase
  exact
    C.paper_huge_red_cross_deterministic_of_card_le_of_paramDeficit_of_right_three_mul_error_le
      hD I hI hwitness hblue hcap hcapWeight hn hρ hβ hε2 hgap hκ hε1 hB' hrightSmall

theorem paper_huge_blue_cross_deterministic_of_error_le_paperKNat_of_right_three_mul_error_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ δerr δgap : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1) (hδerr : 0 ≤ δerr) (hgap2 : 2 ≤ Twobites.paperK δgap n)
    (hκ2 : ρ + (1 + ε2) * β + δerr + δgap ≤ κ)
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat δerr n)
    (hrightSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρ n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  have hB' :
      Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n +
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) ≤
        Twobites.paperKNat κ n := by
    calc
      Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n +
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) ≤
          Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n + Twobites.paperKNat δerr n := by
        simpa [Nat.add_assoc] using
          Nat.add_le_add_left hB (Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n)
      _ ≤ Twobites.paperKNat κ n := by
        exact Twobites.paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_of_two_le_gap_of_le
          hn hρ hβ hε2 hδerr hgap2 hκ2
  exact
    C.paper_huge_blue_cross_deterministic_of_additiveParamDeficit_of_right_three_mul_error_le
      hD I hI hwitness hred hcap hcapWeight hn hρ hβ hε2 hgap hκ hε1 hB' hrightSmall

theorem paper_huge_red_cross_deterministic_of_error_le_paperKNat_of_right_three_mul_error_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρ β κ ε1 ε2 δ δerr δgap : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρ n)
    (hcap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hcapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ Twobites.paperK δ n) (hκ : ρ + (1 + ε2) * β + δ ≤ κ)
    (hε1 : 0 ≤ ε1) (hδerr : 0 ≤ δerr) (hgap2 : 2 ≤ Twobites.paperK δgap n)
    (hκ2 : ρ + (1 + ε2) * β + δerr + δgap ≤ κ)
    (hB :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat δerr n)
    (hrightSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρ n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      (1 + ε1) *
        ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) := by
  have hB' :
      Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n +
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) ≤
        Twobites.paperKNat κ n := by
    calc
      Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n +
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) ≤
          Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n + Twobites.paperKNat δerr n := by
        simpa [Nat.add_assoc] using
          Nat.add_le_add_left hB (Twobites.paperKNat ρ n + Twobites.paperCapNat β ε2 n)
      _ ≤ Twobites.paperKNat κ n := by
        exact Twobites.paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_of_two_le_gap_of_le
          hn hρ hβ hε2 hδerr hgap2 hκ2
  exact
    C.paper_huge_red_cross_deterministic_of_additiveParamDeficit_of_right_three_mul_error_le
      hD I hI hwitness hblue hcap hcapWeight hn hρ hβ hε2 hgap hκ hε1 hB' hrightSmall

/-- The diagonal red part of Paper Lemma `lem:huge`, reduced to the remaining Section 3 witness
arithmetic. -/
theorem paper_huge_red_diagonal_deterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε1 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hbound :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
      ε1 * Twobites.paperK κ n ^ 2 :=
  C.cast_hugeRedContribution_filter_isLeft_le_eps_mul_paperKSq_of_goodEventD_of_paperWitness
    hD I hI hwitness hbound

/-- The diagonal blue part of Paper Lemma `lem:huge`, reduced to the remaining Section 3 witness
arithmetic. -/
theorem paper_huge_blue_diagonal_deterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε1 : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hbound :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
      ε1 * Twobites.paperK κ n ^ 2 :=
  C.cast_hugeBlueContribution_filter_isRight_le_eps_mul_paperKSq_of_goodEventD_of_paperWitness
    hD I hI hwitness hbound

/-- Paper Lemma `lem:huge`, with the cross terms driven directly by the paper-style witness error
bounds rather than the later `three_mul_error` specialization. -/
theorem paper_huge_deterministic_of_witnessErrorBounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρR ρB β κ ε1 ε2 δR δB : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1)
    (hblueCrossLeft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hblueCrossRight :
      C.paperHugeBlueCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound
        projCodegreeBound (Twobites.paperCapNat β ε2 n))
    (hredCrossLeft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hredCrossRight :
      C.paperHugeRedCrossWitnessRightErrorProp I κ ε1 witnessSize degreeBound
        projCodegreeBound (Twobites.paperCapNat β ε2 n)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact C.paper_huge_red_diagonal_deterministic hD I hI hwitness hdiagRed
  · exact C.paper_huge_blue_diagonal_deterministic hD I hI hwitness hdiagBlue
  · exact
      C.paper_huge_blue_cross_deterministic_of_card_le_of_one_le_gap_of_witnessErrorBounds
        hD I hI hwitness hred hblueCap hblueCapWeight hn hρR hβ hε2 hgapR hκR hε1
        hblueCrossLeft hblueCrossRight
  · exact
      C.paper_huge_red_cross_deterministic_of_card_le_of_one_le_gap_of_witnessErrorBounds
        hD I hI hwitness hblue hredCap hredCapWeight hn hρB hβ hε2 hgapB hκB hε1
        hredCrossLeft hredCrossRight

theorem paper_huge_deterministic_of_witnessSplitRightErrorBounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρR ρB β κ ε1 ε2 δR δB : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1)
    (hblueCrossUnionBase :
      witnessSize * degreeBound ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρR n - Twobites.paperCapNat β ε2 n)
    (hblueCrossLeft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hblueCrossRight :
      C.paperHugeBlueCrossWitnessRightSplitErrorProp I κ ε1
        (witnessSize * degreeBound) (witnessSize.choose 2 * projCodegreeBound)
        (Twobites.paperCapNat β ε2 n))
    (hredCrossUnionBase :
      witnessSize * degreeBound ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρB n - Twobites.paperCapNat β ε2 n)
    (hredCrossLeft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) *
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) +
        ((((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound).choose 2 :
          ℕ) : ℝ)) ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hredCrossRight :
      C.paperHugeRedCrossWitnessRightSplitErrorProp I κ ε1
        (witnessSize * degreeBound) (witnessSize.choose 2 * projCodegreeBound)
        (Twobites.paperCapNat β ε2 n)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hblueCapBase :
      Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n - (C.redImage I).card := by
    have hsum :
        (C.redImage I).card + Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n := by
      exact
        (C.redImage_card_add_paperCapNat_le_paperKNat_of_card_le_of_one_le_gap I
          hred hn hρR hβ hε2 hgapR).trans
          (Twobites.paperKNat_le_paperKNat_of_le hκR)
    omega
  have hredCapBase :
      Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n - (C.blueImage I).card := by
    have hsum :
        (C.blueImage I).card + Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n := by
      exact
        (C.blueImage_card_add_paperCapNat_le_paperKNat_of_card_le_of_one_le_gap I
          hblue hn hρB hβ hε2 hgapB).trans
          (Twobites.paperKNat_le_paperKNat_of_le hκB)
    omega
  have hblueUnionBase' :
      witnessSize * degreeBound ≤
        Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n := by
    have hdeficit :
        Twobites.paperKNat κ n - Twobites.paperKNat ρR n - Twobites.paperCapNat β ε2 n ≤
          Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n := by
      omega
    exact hblueCrossUnionBase.trans hdeficit
  have hredUnionBase' :
      witnessSize * degreeBound ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n := by
    have hdeficit :
        Twobites.paperKNat κ n - Twobites.paperKNat ρB n - Twobites.paperCapNat β ε2 n ≤
          Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n := by
      omega
    exact hredCrossUnionBase.trans hdeficit
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact C.paper_huge_red_diagonal_deterministic hD I hI hwitness hdiagRed
  · exact C.paper_huge_blue_diagonal_deterministic hD I hI hwitness hdiagBlue
  · exact
      C.paper_huge_blue_cross_deterministic_of_paperCapNat_of_witnessSplitRightErrorBounds
        hD I hI hwitness hblueCap hblueCapWeight hε1 hblueCapBase hblueUnionBase'
        hblueCrossLeft hblueCrossRight
  · exact
      C.paper_huge_red_cross_deterministic_of_paperCapNat_of_witnessSplitRightErrorBounds
        hD I hI hwitness hredCap hredCapWeight hε1 hredCapBase hredUnionBase'
        hredCrossLeft hredCrossRight

/-- Paper Lemma `lem:huge`, with the cross-term witness errors supplied through a single real
upper bound `W = o(k)` on the left branch and split real bounds `U`, `O` on the capped right
branch. -/
theorem paper_huge_deterministic_of_witnessErrorBounds_of_realErrorBound
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρR ρB β κ ε1 ε2 δR δB U O W : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1)
    (hunion :
      (((witnessSize * degreeBound : ℕ) : ℝ)) ≤ U)
    (hoverlap :
      (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤ O)
    (hsum : U + O ≤ W)
    (hblueCrossUnion :
      U ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)))
    (hblueCrossLeft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) * W + W ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hblueCrossRight :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.redImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * U) +
          ((((Twobites.paperKNat κ n - (C.redImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) + U) * O +
            O ^ 2 / 2) ≤
        ε1 *
          C.paperHugeBlueCrossRightTarget I κ (Twobites.paperCapNat β ε2 n))
    (hredCrossUnion :
      U ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)))
    (hredCrossLeft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) * W + W ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hredCrossRight :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.blueImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * U) +
          ((((Twobites.paperKNat κ n - (C.blueImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) + U) * O +
            O ^ 2 / 2) ≤
        ε1 *
          C.paperHugeRedCrossRightTarget I κ (Twobites.paperCapNat β ε2 n)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have herror :
      (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤ W := by
    calc
      (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) =
          (((witnessSize * degreeBound : ℕ) : ℝ)) +
            (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) := by
              norm_num
      _ ≤ U + O := by linarith
      _ ≤ W := hsum
  have hblueCrossUnionNat :
      witnessSize * degreeBound ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρR n - Twobites.paperCapNat β ε2 n := by
    have hblueCrossUnion' :
        (((witnessSize * degreeBound : ℕ) : ℝ)) ≤
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) := hunion.trans hblueCrossUnion
    exact_mod_cast hblueCrossUnion'
  have hredCrossUnionNat :
      witnessSize * degreeBound ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρB n - Twobites.paperCapNat β ε2 n := by
    have hredCrossUnion' :
        (((witnessSize * degreeBound : ℕ) : ℝ)) ≤
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) := hunion.trans hredCrossUnion
    exact_mod_cast hredCrossUnion'
  exact
    C.paper_huge_deterministic_of_witnessSplitRightErrorBounds hD I hI hwitness hred hblue
      hblueCap hblueCapWeight hredCap hredCapWeight hn hρR hρB hβ hε2 hgapR hgapB hκR hκB
      hdiagRed hdiagBlue hε1 hblueCrossUnionNat
      (C.paperHugeBlueCrossLeftError_of_le_of_sq_bound I herror hblueCrossLeft)
      (C.paperHugeBlueCrossWitnessRightSplitErrorProp_of_le_of_sq_bound I hunion hoverlap
        hblueCrossRight)
      hredCrossUnionNat
      (C.paperHugeRedCrossLeftError_of_le_of_sq_bound I herror hredCrossLeft)
      (C.paperHugeRedCrossWitnessRightSplitErrorProp_of_le_of_sq_bound I hunion hoverlap
        hredCrossRight)

/-- Paper Lemma `lem:huge`, with the Section 3 witness error packaged through a witness-size scale
`B` and a combined coefficient `δ`, so the remaining cross-term work is stated as two left
`paperK δ` inequalities and two split right-branch coefficient inequalities. -/
theorem paper_huge_deterministic_of_witnessErrorBounds_of_coeffBound
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB B βdeg qcodeg δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1)
    (hbound : (witnessSize : ℝ) ≤ B)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δ)
    (hblueCrossUnion :
      Twobites.paperK ((B * βdeg) / Twobites.paperS n) n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)))
    (hblueCrossLeft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) * Twobites.paperK δ n +
        (Twobites.paperK δ n) ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hblueCrossRight :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.redImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) *
              Twobites.paperK ((B * βdeg) / Twobites.paperS n) n) +
          ((((Twobites.paperKNat κ n - (C.redImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) +
                Twobites.paperK ((B * βdeg) / Twobites.paperS n) n) *
              Twobites.paperK
                (((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n +
            (Twobites.paperK
                (((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n) ^
              2 / 2) ≤
        ε1 *
          C.paperHugeBlueCrossRightTarget I κ (Twobites.paperCapNat β ε2 n))
    (hredCrossUnion :
      Twobites.paperK ((B * βdeg) / Twobites.paperS n) n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)))
    (hredCrossLeft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) * Twobites.paperK δ n +
        (Twobites.paperK δ n) ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hredCrossRight :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.blueImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) *
              Twobites.paperK ((B * βdeg) / Twobites.paperS n) n) +
          ((((Twobites.paperKNat κ n - (C.blueImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) +
                Twobites.paperK ((B * βdeg) / Twobites.paperS n) n) *
              Twobites.paperK
                (((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n +
            (Twobites.paperK
                (((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n) ^
              2 / 2) ≤
        ε1 *
          C.paperHugeRedCrossRightTarget I κ (Twobites.paperCapNat β ε2 n)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hβdeg : 0 ≤ βdeg := Twobites.nonneg_of_le_paperP_mul_paperM hn hdegBound
  let δdeg : ℝ := (B * βdeg) / Twobites.paperS n
  let δcodeg : ℝ := ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  have hunion :
      (((witnessSize * degreeBound : ℕ) : ℝ)) ≤ Twobites.paperK δdeg n := by
    have hdegreePart :
        (((witnessSize * degreeBound : ℕ) : ℝ)) ≤
          Twobites.paperK (((witnessSize : ℝ) * βdeg) / Twobites.paperS n) n := by
      simpa using
        (Twobites.cast_mul_le_paperK_of_le_of_le_paperP_mul_paperM
          (w := witnessSize) (bound := witnessSize) (degreeBound := degreeBound)
          (β := βdeg) (n := n) (le_rfl : witnessSize ≤ witnessSize) hβdeg hn hdegBound)
    have hdegreeCoeff :
        ((witnessSize : ℝ) * βdeg) / Twobites.paperS n ≤ δdeg := by
      dsimp [δdeg]
      exact
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hbound hβdeg)
          (Twobites.paperS_nonneg n)
    exact hdegreePart.trans <| by
      unfold Twobites.paperK
      exact mul_le_mul_of_nonneg_right hdegreeCoeff (Real.sqrt_nonneg _)
  have hoverlap :
      (((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤
        Twobites.paperK δcodeg n := by
    simpa [δcodeg] using
      Twobites.cast_choose_mul_le_paperK_of_real_bound hbound hn hcodegBound
  have hsum :
      Twobites.paperK δdeg n + Twobites.paperK δcodeg n ≤ Twobites.paperK δ n := by
    calc
      Twobites.paperK δdeg n + Twobites.paperK δcodeg n =
          Twobites.paperK (δdeg + δcodeg) n := by
            simp [Twobites.paperK, δdeg, δcodeg]
            ring
      _ ≤ Twobites.paperK δ n := by
            apply Twobites.paperK_le_paperK_of_le
            simpa [δdeg, δcodeg] using hsplit
  exact
    C.paper_huge_deterministic_of_witnessErrorBounds_of_realErrorBound
      (U := Twobites.paperK δdeg n) (O := Twobites.paperK δcodeg n) (W := Twobites.paperK δ n)
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight
      (lt_trans Nat.zero_lt_one hn) hρR hρB hβ hε2 hgapR hgapB hκR hκB hdiagRed hdiagBlue
      hε1 hunion hoverlap hsum
      (by simpa [δdeg] using hblueCrossUnion) hblueCrossLeft
      (by simpa [δdeg, δcodeg] using hblueCrossRight)
      (by simpa [δdeg] using hredCrossUnion) hredCrossLeft
      (by simpa [δdeg, δcodeg] using hredCrossRight)

theorem paper_huge_deterministic_of_witnessErrorBounds_of_coeffBound_of_rightSmall
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB B βdeg qcodeg δ : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1) (hε1le : ε1 ≤ 1)
    (hbound : (witnessSize : ℝ) ≤ B)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δ)
    (hblueBound :
      Twobites.paperK δ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)))
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δ n ≤
        ε1 *
          ((((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)))
    (hredBound :
      Twobites.paperK δ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)))
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δ n ≤
        ε1 *
          ((((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hβdeg : 0 ≤ βdeg := Twobites.nonneg_of_le_paperP_mul_paperM hn hdegBound
  have hqcodeg : 0 ≤ qcodeg := Twobites.nonneg_of_natCast_le hcodegBound
  have hB0 : 0 ≤ B := Twobites.nonneg_of_natCast_le hbound
  have hδ0 : 0 ≤ δ := by
    have hsplit0 :
        0 ≤ (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      refine add_nonneg ?_ ?_
      · exact div_nonneg (mul_nonneg hB0 hβdeg) (Twobites.paperS_nonneg n)
      · exact div_nonneg (mul_nonneg (by nlinarith) hqcodeg) (Real.sqrt_nonneg _)
    linarith
  let δdeg : ℝ := (B * βdeg) / Twobites.paperS n
  let δcodeg : ℝ := ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  have hδcodeg0 : 0 ≤ δcodeg := by
    dsimp [δcodeg]
    exact div_nonneg (mul_nonneg (by nlinarith) hqcodeg) (Real.sqrt_nonneg _)
  have hδdeg0 : 0 ≤ δdeg := by
    dsimp [δdeg]
    exact div_nonneg (mul_nonneg hB0 hβdeg) (Twobites.paperS_nonneg n)
  have hδdeg_le : δdeg ≤ δ := by
    have hsplit' : δdeg + δcodeg ≤ δ := by
      simpa [δdeg, δcodeg] using hsplit
    linarith
  have hW : 0 ≤ Twobites.paperK δ n := Twobites.paperK_nonneg hδ0 n
  have hU0 : 0 ≤ Twobites.paperK δdeg n := Twobites.paperK_nonneg hδdeg0 n
  have hO0 : 0 ≤ Twobites.paperK δcodeg n := Twobites.paperK_nonneg hδcodeg0 n
  have hsumCoeff :
      Twobites.paperK δdeg n + Twobites.paperK δcodeg n ≤ Twobites.paperK δ n := by
    calc
      Twobites.paperK δdeg n + Twobites.paperK δcodeg n =
          Twobites.paperK (δdeg + δcodeg) n := by
            simp [Twobites.paperK, δdeg, δcodeg]
            ring
      _ ≤ Twobites.paperK δ n := by
            apply Twobites.paperK_le_paperK_of_le
            simpa [δdeg, δcodeg] using hsplit
  have hblueUnionBound :
      Twobites.paperK δdeg n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) := by
    exact (Twobites.paperK_le_paperK_of_le hδdeg_le).trans hblueBound
  have hblueDeficit :
      Twobites.paperKNat κ n - Twobites.paperKNat ρR n - Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n := by
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_left hred _) _
  have hblueBound' :
      Twobites.paperK δ n ≤
        (((Twobites.paperKNat κ n - (C.redImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) := by
    exact hblueBound.trans <| by exact_mod_cast hblueDeficit
  have hblueLeftBound :
      Twobites.paperK δ n ≤
        (((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ)) := by
    exact hblueBound'.trans <| by exact_mod_cast (Nat.sub_le _ _)
  have hblueCrossSmall' :
      (3 : ℝ) * Twobites.paperK δ n ≤
        ε1 *
          ((((Twobites.paperKNat κ n - (C.redImage I).card -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) := by
    exact three_mul_le_mul_sub_one_mono_real hε1 hblueDeficit hblueCrossSmall
  have hblueLeftSmall :
      (3 : ℝ) * Twobites.paperK δ n ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) - 1)) := by
    exact three_mul_le_mul_sub_one_mono_real hε1 (Nat.sub_le _ _) hblueCrossSmall'
  have hredDeficit :
      Twobites.paperKNat κ n - Twobites.paperKNat ρB n - Twobites.paperCapNat β ε2 n ≤
        Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n := by
    exact Nat.sub_le_sub_right (Nat.sub_le_sub_left hblue _) _
  have hredBound' :
      Twobites.paperK δ n ≤
        (((Twobites.paperKNat κ n - (C.blueImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) := by
    exact hredBound.trans <| by exact_mod_cast hredDeficit
  have hredLeftBound :
      Twobites.paperK δ n ≤
        (((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ)) := by
    exact hredBound'.trans <| by exact_mod_cast (Nat.sub_le _ _)
  have hredCrossSmall' :
      (3 : ℝ) * Twobites.paperK δ n ≤
        ε1 *
          ((((Twobites.paperKNat κ n - (C.blueImage I).card -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) := by
    exact three_mul_le_mul_sub_one_mono_real hε1 hredDeficit hredCrossSmall
  have hredLeftSmall :
      (3 : ℝ) * Twobites.paperK δ n ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) - 1)) := by
    exact three_mul_le_mul_sub_one_mono_real hε1 (Nat.sub_le _ _) hredCrossSmall'
  have hredUnionBound :
      Twobites.paperK δdeg n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) := by
    exact (Twobites.paperK_le_paperK_of_le hδdeg_le).trans hredBound
  have hblueCrossLeftCoeff :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) * Twobites.paperK δ n +
        (Twobites.paperK δ n) ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)) := by
    exact
      real_mul_add_sq_half_le_eps_mul_choose_two_of_le_of_three_mul_le
        hW hblueLeftBound hblueLeftSmall
  have hredCrossLeftCoeff :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) * Twobites.paperK δ n +
        (Twobites.paperK δ n) ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)) := by
    exact
      real_mul_add_sq_half_le_eps_mul_choose_two_of_le_of_three_mul_le
        hW hredLeftBound hredLeftSmall
  have hblueCrossRightCoeff :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.redImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * Twobites.paperK δdeg n) +
          ((((Twobites.paperKNat κ n - (C.redImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) +
                Twobites.paperK δdeg n) * Twobites.paperK δcodeg n +
            (Twobites.paperK δcodeg n) ^ 2 / 2) ≤
        ε1 *
          C.paperHugeBlueCrossRightTarget I κ (Twobites.paperCapNat β ε2 n) := by
    let a : ℕ :=
      Twobites.paperKNat κ n - (C.redImage I).card - Twobites.paperCapNat β ε2 n
    unfold ConstructionData.paperHugeBlueCrossRightTarget
    simpa [ConstructionData.paperHugeBlueCrossRightTargetNat, a, add_assoc, add_left_comm,
      add_comm, mul_comm, mul_left_comm, mul_assoc] using
      (Twobites.splitRightCoeff_le_eps_mul_cap_choose_two_add_choose_two_of_sum_le_of_three_mul_le
        (a := a) (cap := Twobites.paperCapNat β ε2 n) hε1 hε1le hU0 hO0 hsumCoeff
        hblueCrossSmall')
  have hredCrossRightCoeff :
      ((3 : ℝ) / 2) *
            (((Twobites.paperKNat κ n - (C.blueImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * Twobites.paperK δdeg n) +
          ((((Twobites.paperKNat κ n - (C.blueImage I).card -
                Twobites.paperCapNat β ε2 n : ℕ) : ℝ) +
                Twobites.paperK δdeg n) * Twobites.paperK δcodeg n +
            (Twobites.paperK δcodeg n) ^ 2 / 2) ≤
        ε1 *
          C.paperHugeRedCrossRightTarget I κ (Twobites.paperCapNat β ε2 n) := by
    let a : ℕ :=
      Twobites.paperKNat κ n - (C.blueImage I).card - Twobites.paperCapNat β ε2 n
    unfold ConstructionData.paperHugeRedCrossRightTarget
    simpa [ConstructionData.paperHugeRedCrossRightTargetNat, a, add_assoc, add_left_comm,
      add_comm, mul_comm, mul_left_comm, mul_assoc] using
      (Twobites.splitRightCoeff_le_eps_mul_cap_choose_two_add_choose_two_of_sum_le_of_three_mul_le
        (a := a) (cap := Twobites.paperCapNat β ε2 n) hε1 hε1le hU0 hO0 hsumCoeff
        hredCrossSmall')
  exact
    C.paper_huge_deterministic_of_witnessErrorBounds_of_coeffBound
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR
      hρB hβ hε2 hgapR hgapB hκR hκB hdiagRed hdiagBlue hε1 hbound hdegBound
      hcodegBound hsplit (by simpa [δdeg] using hblueUnionBound) hblueCrossLeftCoeff
      (by simpa [δdeg, δcodeg] using hblueCrossRightCoeff)
      (by simpa [δdeg] using hredUnionBound) hredCrossLeftCoeff
      (by simpa [δdeg, δcodeg] using hredCrossRightCoeff)

theorem paper_huge_deterministic_of_witnessErrorBounds_of_coeffBound_of_paramDeficit
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB B βdeg qcodeg δ δgapR δgapB : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1) (hε1le : ε1 ≤ 1)
    (hbound : (witnessSize : ℝ) ≤ B)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δ)
    (hδgapR : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δ + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δ n ≤
        ε1 *
          ((((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)))
    (hδgapB : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δ + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δ n ≤
        ε1 *
          ((((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hβdeg0 : 0 ≤ βdeg := Twobites.nonneg_of_le_paperP_mul_paperM hn hdegBound
  have hqcodeg0 : 0 ≤ qcodeg := Twobites.nonneg_of_natCast_le hcodegBound
  have hB0 : 0 ≤ B := Twobites.nonneg_of_natCast_le hbound
  have hδ0 : 0 ≤ δ := by
    have hsplit0 :
        0 ≤ (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      refine add_nonneg ?_ ?_
      · exact div_nonneg (mul_nonneg hB0 hβdeg0) (Twobites.paperS_nonneg n)
      · exact div_nonneg (mul_nonneg (by nlinarith) hqcodeg0) (Real.sqrt_nonneg _)
    linarith
  have hblueNat :
      Twobites.paperKNat ρR n + Twobites.paperCapNat β ε2 n + Twobites.paperKNat δ n ≤
        Twobites.paperKNat κ n := by
    exact
      Twobites.paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_of_two_le_gap_of_le
        (lt_trans Nat.zero_lt_one hn) hρR hβ hε2 hδ0 hδgapR hκ2R
  have hblueNatDef :
      Twobites.paperKNat δ n ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρR n - Twobites.paperCapNat β ε2 n := by
    have hk :
        Twobites.paperKNat ρR n + Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n := by
      exact le_trans (Nat.le_add_right _ _) hblueNat
    have hbase :
        Twobites.paperKNat δ n ≤
          Twobites.paperKNat κ n -
            (Twobites.paperKNat ρR n + Twobites.paperCapNat β ε2 n) := by
      exact (Nat.le_sub_iff_add_le hk).2 <| by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hblueNat
    simpa [Nat.sub_sub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbase
  have hblueBound :
      Twobites.paperK δ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) := by
    calc
      Twobites.paperK δ n ≤ Twobites.paperKNat δ n := Nat.le_ceil _
      _ ≤ (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) := by
        exact_mod_cast hblueNatDef
  have hredNat :
      Twobites.paperKNat ρB n + Twobites.paperCapNat β ε2 n + Twobites.paperKNat δ n ≤
        Twobites.paperKNat κ n := by
    exact
      Twobites.paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_of_two_le_gap_of_le
        (lt_trans Nat.zero_lt_one hn) hρB hβ hε2 hδ0 hδgapB hκ2B
  have hredNatDef :
      Twobites.paperKNat δ n ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρB n - Twobites.paperCapNat β ε2 n := by
    have hk :
        Twobites.paperKNat ρB n + Twobites.paperCapNat β ε2 n ≤ Twobites.paperKNat κ n := by
      exact le_trans (Nat.le_add_right _ _) hredNat
    have hbase :
        Twobites.paperKNat δ n ≤
          Twobites.paperKNat κ n -
            (Twobites.paperKNat ρB n + Twobites.paperCapNat β ε2 n) := by
      exact (Nat.le_sub_iff_add_le hk).2 <| by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hredNat
    simpa [Nat.sub_sub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbase
  have hredBound :
      Twobites.paperK δ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) := by
    calc
      Twobites.paperK δ n ≤ Twobites.paperKNat δ n := Nat.le_ceil _
      _ ≤ (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ)) := by
        exact_mod_cast hredNatDef
  exact
    C.paper_huge_deterministic_of_witnessErrorBounds_of_coeffBound_of_rightSmall
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR
      hρB hβ hε2 hgapR hgapB hκR hκB hdiagRed hdiagBlue hε1 hε1le hbound hdegBound
      hcodegBound hsplit hblueBound hblueCrossSmall hredBound hredCrossSmall

theorem paper_huge_deterministic_of_witnessErrorBounds_of_coeffBound_of_paramDeficit_of_split
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB B βdeg qcodeg δcodeg δgapR δgapB : ℝ}
    {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1) (hε1le : ε1 ≤ 1)
    (hbound : (witnessSize : ℝ) ≤ B)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hsplitFirst : (B * βdeg) / Twobites.paperS n ≤ ε1 * κ)
    (hcodegCoeff :
      ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ δcodeg)
    (hδgapR : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + (ε1 * κ + δcodeg) + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK (ε1 * κ + δcodeg) n ≤
        ε1 *
          ((((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)))
    (hδgapB : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + (ε1 * κ + δcodeg) + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK (ε1 * κ + δcodeg) n ≤
        ε1 *
          ((((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        ε1 * κ + δcodeg := by
    linarith
  simpa [add_assoc, add_left_comm, add_comm] using
    C.paper_huge_deterministic_of_witnessErrorBounds_of_coeffBound_of_paramDeficit
      (δ := ε1 * κ + δcodeg) hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap
      hredCapWeight hn hρR hρB hβ hε2 hgapR hgapB hκR hκB hdiagRed hdiagBlue hε1
      hε1le hbound hdegBound hcodegBound hsplit hδgapR hκ2R hblueCrossSmall
      hδgapB hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_witnessErrorBounds_of_coeffBound_of_paramDeficit_of_three
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg qcodeg δcodeg δgapR δgapB : ℝ}
    {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1) (hε1le : ε1 ≤ 1)
    (hbound :
      (witnessSize : ℝ) ≤ 3 * κ * Real.log (Real.log (n : ℝ)))
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δcodeg)
    (hδgapR : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + (ε1 * κ + δcodeg) + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK (ε1 * κ + δcodeg) n ≤
        ε1 *
          ((((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)))
    (hδgapB : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + (ε1 * κ + δcodeg) + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK (ε1 * κ + δcodeg) n ≤
        ε1 *
          ((((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hsplitFirst :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * βdeg) / Twobites.paperS n ≤ ε1 * κ := by
    exact Twobites.three_loglog_split_first_le hn hκ0 hdiagScale
  have hcodegCoeff :
      (((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * qcodeg) /
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δcodeg := by
    convert hcodegScale using 1
    ring_nf
  exact
    C.paper_huge_deterministic_of_witnessErrorBounds_of_coeffBound_of_paramDeficit_of_split
      (B := 3 * κ * Real.log (Real.log (n : ℝ))) hD I hI hwitness hred hblue hblueCap
      hblueCapWeight hredCap hredCapWeight hn hρR hρB hβ hε2 hgapR hgapB hκR hκB
      hdiagRed hdiagBlue hε1 hε1le hbound hdegBound hcodegBound hsplitFirst hcodegCoeff
      hδgapR hκ2R hblueCrossSmall hδgapB hκ2B hredCrossSmall

/-- Paper Lemma `lem:huge`, reduced to the remaining Section 3 parameter inequalities for the
diagonal and cross terms. -/
theorem paper_huge_deterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρR ρB β κ ε1 ε2 δR δB : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1)
    (hblueCrossDeficit :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρR n - Twobites.paperCapNat β ε2 n)
    (hblueCrossSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hredCrossDeficit :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat κ n - Twobites.paperKNat ρB n - Twobites.paperCapNat β ε2 n)
    (hredCrossSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact C.paper_huge_red_diagonal_deterministic hD I hI hwitness hdiagRed
  · exact C.paper_huge_blue_diagonal_deterministic hD I hI hwitness hdiagBlue
  · exact
      C.paper_huge_blue_cross_deterministic_of_card_le_of_paramDeficit_of_right_three_mul_error_le
        hD I hI hwitness hred hblueCap hblueCapWeight hn hρR hβ hε2 hgapR hκR hε1
        hblueCrossDeficit hblueCrossSmall
  · exact
      C.paper_huge_red_cross_deterministic_of_card_le_of_paramDeficit_of_right_three_mul_error_le
        hD I hI hwitness hblue hredCap hredCapWeight hn hρB hβ hε2 hgapB hκB hε1
        hredCrossDeficit hredCrossSmall

theorem paper_huge_deterministic_of_additiveParamDeficit
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρR ρB β κ ε1 ε2 δR δB : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1)
    (hblueCrossDeficit :
      Twobites.paperKNat ρR n + Twobites.paperCapNat β ε2 n +
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) ≤
        Twobites.paperKNat κ n)
    (hblueCrossSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hredCrossDeficit :
      Twobites.paperKNat ρB n + Twobites.paperCapNat β ε2 n +
          (witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound) ≤
        Twobites.paperKNat κ n)
    (hredCrossSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact C.paper_huge_red_diagonal_deterministic hD I hI hwitness hdiagRed
  · exact C.paper_huge_blue_diagonal_deterministic hD I hI hwitness hdiagBlue
  · exact
      C.paper_huge_blue_cross_deterministic_of_additiveParamDeficit_of_right_three_mul_error_le
        hD I hI hwitness hred hblueCap hblueCapWeight hn hρR hβ hε2 hgapR hκR hε1
        hblueCrossDeficit hblueCrossSmall
  · exact
      C.paper_huge_red_cross_deterministic_of_additiveParamDeficit_of_right_three_mul_error_le
        hD I hI hwitness hblue hredCap hredCapWeight hn hρB hβ hε2 hgapB hκB hε1
        hredCrossDeficit hredCrossSmall

theorem paper_huge_deterministic_of_error_le_paperKNat
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB δerrR δgapR δerrB δgapB : ℝ} {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1)
    (hδerrR : 0 ≤ δerrR) (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δerrR + δgapR ≤ κ)
    (hblueCrossError :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat δerrR n)
    (hblueCrossSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hδerrB : 0 ≤ δerrB) (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δerrB + δgapB ≤ κ)
    (hredCrossError :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat δerrB n)
    (hredCrossSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact C.paper_huge_red_diagonal_deterministic hD I hI hwitness hdiagRed
  · exact C.paper_huge_blue_diagonal_deterministic hD I hI hwitness hdiagBlue
  · exact
      C.paper_huge_blue_cross_deterministic_of_error_le_paperKNat_of_right_three_mul_error_le
        hD I hI hwitness hred hblueCap hblueCapWeight hn hρR hβ hε2 hgapR hκR hε1
        hδerrR hgap2R hκ2R hblueCrossError hblueCrossSmall
  · exact
      C.paper_huge_red_cross_deterministic_of_error_le_paperKNat_of_right_three_mul_error_le
        hD I hI hwitness hblue hredCap hredCapWeight hn hρB hβ hε2 hgapB hκB hε1
        hδerrB hgap2B hκ2B hredCrossError hredCrossSmall

theorem paper_huge_deterministic_of_split_error_le_paperKNat
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB δdeg δcodeg δsumGap δerr δgapR δgapB : ℝ}
    {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1)
    (hδdeg : 0 ≤ δdeg) (hδcodeg : 0 ≤ δcodeg) (hδerr : 0 ≤ δerr)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hsumκ : δdeg + δcodeg + δsumGap ≤ δerr)
    (hdegBound : witnessSize * degreeBound ≤ Twobites.paperKNat δdeg n)
    (hcodegBound : witnessSize.choose 2 * projCodegreeBound ≤ Twobites.paperKNat δcodeg n)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δerr + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δerr + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have herror :
      witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound ≤
        Twobites.paperKNat δerr n := by
    exact
      Twobites.add_le_paperKNat_of_le_paperKNat_of_le_paperKNat_of_one_le_gap_of_le
        hdegBound hcodegBound hδdeg hδcodeg hsumGap hsumκ
  exact
    C.paper_huge_deterministic_of_error_le_paperKNat hD I hI hwitness hred hblue hblueCap
      hblueCapWeight hredCap hredCapWeight hn hρR hρB hβ hε2 hgapR hgapB hκR hκB hdiagRed
      hdiagBlue hε1 hδerr hgap2R hκ2R herror hblueCrossSmall hδerr hgap2B hκ2B herror
      hredCrossSmall

theorem paper_huge_deterministic_of_split_error_le_paperK
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB δdeg δcodeg δsumGap δerr δgapR δgapB : ℝ}
    {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1)
    (hδdeg : 0 ≤ δdeg) (hδcodeg : 0 ≤ δcodeg) (hδerr : 0 ≤ δerr)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hsumκ : δdeg + δcodeg + δsumGap ≤ δerr)
    (hdegBound : ((witnessSize * degreeBound : ℕ) : ℝ) ≤ Twobites.paperK δdeg n)
    (hcodegBound :
      ((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤ Twobites.paperK δcodeg n)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δerr + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δerr + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hdegBoundNat : witnessSize * degreeBound ≤ Twobites.paperKNat δdeg n := by
    exact Twobites.nat_le_paperKNat_of_le_paperK hdegBound
  have hcodegBoundNat :
      witnessSize.choose 2 * projCodegreeBound ≤ Twobites.paperKNat δcodeg n := by
    exact Twobites.nat_le_paperKNat_of_le_paperK hcodegBound
  exact
    C.paper_huge_deterministic_of_split_error_le_paperKNat hD I hI hwitness hred hblue hblueCap
      hblueCapWeight hredCap hredCapWeight hn hρR hρB hβ hε2 hgapR hgapB hκR hκB
      hdiagRed hdiagBlue hε1 hδdeg hδcodeg hδerr hsumGap hsumκ hdegBoundNat hcodegBoundNat
      hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem cast_add_le_paperK_add_of_le_paperK {a b : ℕ} {α β : ℝ} {n : ℕ}
    (ha : (a : ℝ) ≤ Twobites.paperK α n) (hb : (b : ℝ) ≤ Twobites.paperK β n) :
    (((a + b : ℕ) : ℝ)) ≤ Twobites.paperK α n + Twobites.paperK β n := by
  calc
    (((a + b : ℕ) : ℝ)) = (a : ℝ) + (b : ℝ) := by norm_num
    _ ≤ Twobites.paperK α n + Twobites.paperK β n := by linarith

theorem paper_huge_deterministic_of_split_error_le_paperK_of_split_small
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB δdeg δcodeg δsumGap δerr δgapR δgapB : ℝ}
    {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 0 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1)
    (hδdeg : 0 ≤ δdeg) (hδcodeg : 0 ≤ δcodeg) (hδerr : 0 ≤ δerr)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hsumκ : δdeg + δcodeg + δsumGap ≤ δerr)
    (hdegBound : ((witnessSize * degreeBound : ℕ) : ℝ) ≤ Twobites.paperK δdeg n)
    (hcodegBound :
      ((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤ Twobites.paperK δcodeg n)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δerr + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * (Twobites.paperK δdeg n + Twobites.paperK δcodeg n) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δerr + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * (Twobites.paperK δdeg n + Twobites.paperK δcodeg n) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have herrorBound :
      (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤
        Twobites.paperK δdeg n + Twobites.paperK δcodeg n := by
    exact cast_add_le_paperK_add_of_le_paperK hdegBound hcodegBound
  have hblueCrossSmall' :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    nlinarith
  have hredCrossSmall' :
      (3 : ℝ) *
          ((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    nlinarith
  exact
    C.paper_huge_deterministic_of_split_error_le_paperK hD I hI hwitness hred hblue hblueCap
      hblueCapWeight hredCap hredCapWeight hn hρR hρB hβ hε2 hgapR hgapB hκR hκB
      hdiagRed hdiagBlue hε1 hδdeg hδcodeg hδerr hsumGap hsumκ hdegBound hcodegBound
      hgap2R hκ2R hblueCrossSmall' hgap2B hκ2B hredCrossSmall'

theorem paper_huge_deterministic_of_split_degree_le_paperPM_of_split_small
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg δcodeg δsumGap δerr δgapR δgapB : ℝ}
    {bound witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1) (hw : witnessSize ≤ bound) (hβdeg : 0 ≤ βdeg)
    (hδcodeg : 0 ≤ δcodeg) (hδerr : 0 ≤ δerr)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hsumκ : (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n + δcodeg + δsumGap ≤ δerr)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound :
      ((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤ Twobites.paperK δcodeg n)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δerr + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) *
          (Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n +
            Twobites.paperK δcodeg n) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δerr + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) *
          (Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n +
            Twobites.paperK δcodeg n) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  let δdeg : ℝ := (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have hδdeg : 0 ≤ δdeg := by
    dsimp [δdeg]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg bound) hβdeg) (Twobites.paperS_nonneg n)
  have hdegBound' : ((witnessSize * degreeBound : ℕ) : ℝ) ≤ Twobites.paperK δdeg n := by
    simpa [δdeg] using
      Twobites.cast_mul_le_paperK_of_le_of_le_paperP_mul_paperM hw hβdeg hn hdegBound
  exact
    C.paper_huge_deterministic_of_split_error_le_paperK_of_split_small hD I hI hwitness hred
      hblue hblueCap hblueCapWeight hredCap hredCapWeight hn0 hρR hρB hβ hε2 hgapR hgapB
      hκR hκB hdiagRed hdiagBlue hε1 hδdeg hδcodeg hδerr hsumGap (by simpa [δdeg] using hsumκ)
      hdegBound' hcodegBound hgap2R hκ2R (by simpa [δdeg] using hblueCrossSmall) hgap2B
      hκ2B (by simpa [δdeg] using hredCrossSmall)

theorem paper_huge_deterministic_of_split_degree_le_paperPM_of_codegree_le_of_split_small
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg qcodeg δsumGap δerr δgapR δgapB : ℝ}
    {bound witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1) (hw : witnessSize ≤ bound) (hβdeg : 0 ≤ βdeg)
    (hqcodeg : 0 ≤ qcodeg) (hδerr : 0 ≤ δerr)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hsumκ :
      (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n +
          ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) +
          δsumGap ≤
        δerr)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δerr + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) *
          (Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n +
            Twobites.paperK
              ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
                Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δerr + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) *
          (Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n +
            Twobites.paperK
              ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
                Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  let δcodeg : ℝ :=
    ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
  have hδcodeg : 0 ≤ δcodeg := by
    dsimp [δcodeg]
    exact div_nonneg (mul_nonneg (by positivity) hqcodeg) (Real.sqrt_nonneg _)
  have hcodegBound' :
      ((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤ Twobites.paperK δcodeg n := by
    simpa [δcodeg] using
      Twobites.cast_choose_mul_le_paperK_of_le_of_le hw hn hcodegBound
  exact
    C.paper_huge_deterministic_of_split_degree_le_paperPM_of_split_small hD I hI hwitness
      hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR hρB hβ hε2 hgapR
      hgapB hκR hκB hdiagRed hdiagBlue hε1 hw hβdeg hδcodeg hδerr hsumGap
      (by simpa [δcodeg, add_assoc, add_left_comm, add_comm] using hsumκ) hdegBound
      hcodegBound' hgap2R hκ2R (by simpa [δcodeg] using hblueCrossSmall) hgap2B hκ2B
      (by simpa [δcodeg] using hredCrossSmall)

theorem paper_huge_deterministic_of_split_degree_le_paperPM_of_codegree_le_of_small_coeff
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg qcodeg δsplit δsumGap δerr δgapR δgapB : ℝ}
    {bound witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1) (hw : witnessSize ≤ bound) (hβdeg : 0 ≤ βdeg)
    (hqcodeg : 0 ≤ qcodeg) (hδerr : 0 ≤ δerr)
    (hsplit :
      (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n +
          ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hsumκ : δsplit + δsumGap ≤ δerr)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δerr + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δerr + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  let δdeg : ℝ := (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n
  let δcodeg : ℝ :=
    ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
  have hδcodeg : 0 ≤ δcodeg := by
    dsimp [δcodeg]
    exact div_nonneg (mul_nonneg (by positivity) hqcodeg) (Real.sqrt_nonneg _)
  have hsmallCoeff :
      Twobites.paperK δdeg n + Twobites.paperK δcodeg n ≤ Twobites.paperK δsplit n := by
    calc
      Twobites.paperK δdeg n + Twobites.paperK δcodeg n =
          Twobites.paperK (δdeg + δcodeg) n := by
            rw [Twobites.paperK_add]
      _ ≤ Twobites.paperK δsplit n := by
        apply Twobites.paperK_le_paperK_of_le
        simpa [δdeg, δcodeg] using hsplit
  have hblueCrossSmall' :
      (3 : ℝ) *
          (Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n +
            Twobites.paperK
              ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
                Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    have hmono : (3 : ℝ) * (Twobites.paperK δdeg n + Twobites.paperK δcodeg n) ≤
        (3 : ℝ) * Twobites.paperK δsplit n := by
      nlinarith
    exact (hmono.trans hblueCrossSmall)
  have hredCrossSmall' :
      (3 : ℝ) *
          (Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n +
            Twobites.paperK
              ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
                Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n) ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    have hmono : (3 : ℝ) * (Twobites.paperK δdeg n + Twobites.paperK δcodeg n) ≤
        (3 : ℝ) * Twobites.paperK δsplit n := by
      nlinarith
    exact (hmono.trans hredCrossSmall)
  exact
    C.paper_huge_deterministic_of_split_degree_le_paperPM_of_codegree_le_of_split_small hD I
      hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR hρB
      hβ hε2 hgapR hgapB hκR hκB hdiagRed hdiagBlue hε1 hw hβdeg hqcodeg hδerr hsumGap
      (by
        have : δdeg + δcodeg + δsumGap ≤ δerr := by
          linarith
        simpa [δdeg, δcodeg, add_assoc, add_left_comm, add_comm] using this)
      hdegBound hcodegBound hgap2R hκ2R hblueCrossSmall' hgap2B hκ2B hredCrossSmall'

theorem paper_huge_deterministic_of_split_degree_le_paperPM_of_codegree_le_of_small_coeff_of_gap
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg qcodeg δsplit δsumGap δgapR δgapB : ℝ}
    {bound witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hdiagBlue :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hε1 : 0 ≤ ε1) (hw : witnessSize ≤ bound) (hβdeg : 0 ≤ βdeg)
    (hqcodeg : 0 ≤ qcodeg)
    (hsplit :
      (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n +
          ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hcoeffNonneg :
      0 ≤ (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n +
        ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
    exact Twobites.splitCoeff_nonneg (n := n) hβdeg hqcodeg
  have hδsplit : 0 ≤ δsplit := by
    linarith
  have hδsumGap : 0 ≤ δsumGap := by
    exact Twobites.nonneg_of_one_le_paperK hn hsumGap
  exact
    C.paper_huge_deterministic_of_split_degree_le_paperPM_of_codegree_le_of_small_coeff hD I
      hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR hρB
      hβ hε2 hgapR hgapB hκR hκB hdiagRed hdiagBlue hε1 hw hβdeg hqcodeg
      (add_nonneg hδsplit hδsumGap) hsplit hsumGap (by simp) hdegBound hcodegBound hgap2R
      (by simpa [add_assoc, add_left_comm, add_comm] using hκ2R)
      hblueCrossSmall hgap2B (by simpa [add_assoc, add_left_comm, add_comm] using hκ2B)
      hredCrossSmall

theorem paper_huge_deterministic_of_small_coeff_gap_diag
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg qcodeg δsplit δsumGap δgapR δgapB : ℝ}
    {bound witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hε1 : 0 ≤ ε1) (hw : witnessSize ≤ bound) (hβdeg : 0 ≤ βdeg)
    (hqcodeg : 0 ≤ qcodeg)
    (hdiag :
      ((Twobites.paperKNat κ n : ℝ) / 2) *
          Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hsplit :
      (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n +
          ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hdegTerm :
      ((witnessSize * degreeBound : ℕ) : ℝ) ≤
        Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n := by
    exact Twobites.cast_mul_le_paperK_of_le_of_le_paperP_mul_paperM hw hβdeg hn hdegBound
  have hdiagRed :
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2 := by
    calc
      ((Twobites.paperKNat κ n : ℝ) / 2) * (witnessSize * degreeBound : ℕ) ≤
          ((Twobites.paperKNat κ n : ℝ) / 2) *
            Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n := by
              gcongr
      _ ≤ ε1 * Twobites.paperK κ n ^ 2 := hdiag
  exact
    C.paper_huge_deterministic_of_split_degree_le_paperPM_of_codegree_le_of_small_coeff_of_gap
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR
      hρB hβ hε2 hgapR hgapB hκR hκB hdiagRed hdiagRed hε1 hw hβdeg hqcodeg hsplit
      hsumGap hdegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B
      hredCrossSmall

theorem paper_huge_deterministic_of_small_coeff_gap_diag_paperK
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg qcodeg δsplit δsumGap δgapR δgapB : ℝ}
    {bound witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hε1 : 0 ≤ ε1) (hw : witnessSize ≤ bound) (hβdeg : 0 ≤ βdeg)
    (hqcodeg : 0 ≤ qcodeg)
    (hdiag :
      ((Twobites.paperK κ n + 1) / 2) *
          Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hsplit :
      (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n +
          ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hδR : 0 ≤ δR := Twobites.nonneg_of_one_le_paperK hn hgapR
  have hfac : 0 ≤ 1 + ε2 := by linarith
  have hκ : 0 ≤ κ := by
    have hbase : 0 ≤ ρR + (1 + ε2) * β + δR := by
      nlinarith
    linarith
  have hcoeffNonneg :
      0 ≤ Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n := by
    apply Twobites.paperK_nonneg
    exact div_nonneg (mul_nonneg (by positivity) hβdeg) (Twobites.paperS_nonneg n)
  have hdiag' :
      ((Twobites.paperKNat κ n : ℝ) / 2) *
          Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n ≤
        ε1 * Twobites.paperK κ n ^ 2 := by
    have hceil : (Twobites.paperKNat κ n : ℝ) ≤ Twobites.paperK κ n + 1 := by
      exact Twobites.paperKNat_le_paperK_add_one hκ n
    calc
      ((Twobites.paperKNat κ n : ℝ) / 2) *
          Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n ≤
          ((Twobites.paperK κ n + 1) / 2) *
            Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n := by
              apply mul_le_mul_of_nonneg_right
              · linarith
              · exact hcoeffNonneg
      _ ≤ ε1 * Twobites.paperK κ n ^ 2 := hdiag
  exact
    C.paper_huge_deterministic_of_small_coeff_gap_diag
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR
      hρB hβ hε2 hgapR hgapB hκR hκB hε1 hw hβdeg hqcodeg hdiag' hsplit hsumGap
      hdegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_small_coeff_gap_diag_paperK_of_bound_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg qcodeg δsplit δsumGap δgapR δgapB B : ℝ}
    {bound witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hε1 : 0 ≤ ε1) (hw : witnessSize ≤ bound) (hbound : (bound : ℝ) ≤ B)
    (hβdeg : 0 ≤ βdeg) (hqcodeg : 0 ≤ qcodeg)
    (hdiag :
      ((Twobites.paperK κ n + 1) / 2) * Twobites.paperK (B * βdeg / Twobites.paperS n) n ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hδR : 0 ≤ δR := Twobites.nonneg_of_one_le_paperK hn hgapR
  have hκ : 0 ≤ κ := by
    have hfac : 0 ≤ 1 + ε2 := by linarith
    have hbase : 0 ≤ ρR + (1 + ε2) * β + δR := by
      nlinarith
    linarith
  have hcoeff :
      (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n ≤ (B * βdeg) / Twobites.paperS n := by
    have hs : 0 < Twobites.paperS n := Twobites.paperS_pos hn
    apply (div_le_div_iff₀ hs hs).2
    nlinarith [mul_le_mul_of_nonneg_right hbound hβdeg]
  have hdiag' :
      ((Twobites.paperK κ n + 1) / 2) *
          Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n ≤
        ε1 * Twobites.paperK κ n ^ 2 := by
    have hfac : 0 ≤ (Twobites.paperK κ n + 1) / 2 := by
      have hk : 0 ≤ Twobites.paperK κ n := Twobites.paperK_nonneg hκ n
      nlinarith
    calc
      ((Twobites.paperK κ n + 1) / 2) *
          Twobites.paperK ((((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n) n ≤
          ((Twobites.paperK κ n + 1) / 2) * Twobites.paperK (B * βdeg / Twobites.paperS n) n := by
            gcongr
            exact Twobites.paperK_le_paperK_of_le hcoeff
      _ ≤ ε1 * Twobites.paperK κ n ^ 2 := hdiag
  have hsplit' :
      (((bound : ℕ) : ℝ) * βdeg) / Twobites.paperS n +
          ((((bound.choose 2 : ℕ) : ℝ) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit := by
    exact (Twobites.splitCoeff_le_of_bound_le hn hbound hβdeg hqcodeg).trans hsplit
  exact
    C.paper_huge_deterministic_of_small_coeff_gap_diag_paperK hD I hI hwitness hred hblue
      hblueCap hblueCapWeight hredCap hredCapWeight hn hρR hρB hβ hε2 hgapR hgapB hκR hκB
      hε1 hw hβdeg hqcodeg hdiag' hsplit' hsumGap hdegBound hcodegBound hgap2R hκ2R
      hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_small_coeff_gap_diag_paperK_of_witness_bound_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg qcodeg δsplit δsumGap δgapR δgapB B : ℝ}
    {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hε1 : 0 ≤ ε1) (hbound : (witnessSize : ℝ) ≤ B) (hβdeg : 0 ≤ βdeg)
    (hqcodeg : 0 ≤ qcodeg)
    (hdiag :
      ((Twobites.paperK κ n + 1) / 2) * Twobites.paperK (B * βdeg / Twobites.paperS n) n ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  exact
    C.paper_huge_deterministic_of_small_coeff_gap_diag_paperK_of_bound_le
      (bound := witnessSize) hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap
      hredCapWeight hn hρR hρB hβ hε2 hgapR hgapB hκR hκB hε1 (le_rfl : witnessSize ≤ witnessSize)
      hbound hβdeg hqcodeg hdiag hsplit hsumGap hdegBound hcodegBound hgap2R hκ2R
      hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_small_coeff_gap_diag_paperK_of_witness_bound_le_of_diagCoeff
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg qcodeg δsplit δsumGap δgapR δgapB B : ℝ}
    {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hε1 : 0 ≤ ε1) (hbound : (witnessSize : ℝ) ≤ B) (hβdeg : 0 ≤ βdeg)
    (hqcodeg : 0 ≤ qcodeg)
    (hdiagCoeff :
      (B * βdeg / Twobites.paperS n) * (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hdiag :
      ((Twobites.paperK κ n + 1) / 2) * Twobites.paperK (B * βdeg / Twobites.paperS n) n ≤
        ε1 * Twobites.paperK κ n ^ 2 := by
    exact Twobites.half_add_one_mul_paperK_le_eps_mul_paperKSq_of_le hn hdiagCoeff
  exact
    C.paper_huge_deterministic_of_small_coeff_gap_diag_paperK_of_witness_bound_le
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR
      hρB hβ hε2 hgapR hgapB hκR hκB hε1 hbound hβdeg hqcodeg hdiag hsplit hsumGap
      hdegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_witness_bound_of_diagCoeff_of_bounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 δR δB βdeg qcodeg δsplit δsumGap δgapR δgapB B : ℝ}
    {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgapR : 1 ≤ Twobites.paperK δR n) (hgapB : 1 ≤ Twobites.paperK δB n)
    (hκR : ρR + (1 + ε2) * β + δR ≤ κ)
    (hκB : ρB + (1 + ε2) * β + δB ≤ κ)
    (hε1 : 0 ≤ ε1) (hbound : (witnessSize : ℝ) ≤ B)
    (hdiagCoeff :
      (B * βdeg / Twobites.paperS n) * (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hβdeg : 0 ≤ βdeg := Twobites.nonneg_of_le_paperP_mul_paperM hn hdegBound
  have hqcodeg : 0 ≤ qcodeg := Twobites.nonneg_of_natCast_le hcodegBound
  exact
    C.paper_huge_deterministic_of_small_coeff_gap_diag_paperK_of_witness_bound_le_of_diagCoeff
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR
      hρB hβ hε2 hgapR hgapB hκR hκB hε1 hbound hβdeg hqcodeg hdiagCoeff hsplit hsumGap
      hdegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_witness_bound_of_diagCoeff_of_bounds_of_gaps
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB B : ℝ}
    {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1 : 0 ≤ ε1) (hbound : (witnessSize : ℝ) ≤ B)
    (hdiagCoeff :
      (B * βdeg / Twobites.paperS n) * (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R : ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B : ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hβdeg : 0 ≤ βdeg := Twobites.nonneg_of_le_paperP_mul_paperM hn hdegBound
  have hqcodeg : 0 ≤ qcodeg := Twobites.nonneg_of_natCast_le hcodegBound
  have hB : 0 ≤ B := by
    have hw0 : 0 ≤ (witnessSize : ℝ) := by positivity
    linarith
  have hsplitNonneg :
      0 ≤ (B * βdeg) / Twobites.paperS n +
        ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    refine add_nonneg ?_ ?_
    · exact div_nonneg (mul_nonneg hB hβdeg) (Twobites.paperS_nonneg n)
    · have hBsq : 0 ≤ B ^ 2 / 2 := by
        nlinarith [sq_nonneg B]
      exact div_nonneg (mul_nonneg hBsq hqcodeg) (Real.sqrt_nonneg _)
  have hδsplit : 0 ≤ δsplit := by
    linarith
  have hδsumGap : 0 ≤ δsumGap := Twobites.nonneg_of_one_le_paperK hn hsumGap
  have hδgapR : 0 ≤ δgapR := Twobites.nonneg_of_one_le_paperK hn (by linarith [hgap2R])
  have hδgapB : 0 ≤ δgapB := Twobites.nonneg_of_one_le_paperK hn (by linarith [hgap2B])
  have hgapR :
      1 ≤ Twobites.paperK (δsplit + δsumGap + δgapR) n := by
    have hmono :
        Twobites.paperK δgapR n ≤ Twobites.paperK (δsplit + δsumGap + δgapR) n := by
      apply Twobites.paperK_le_paperK_of_le
      nlinarith
    linarith
  have hgapB :
      1 ≤ Twobites.paperK (δsplit + δsumGap + δgapB) n := by
    have hmono :
        Twobites.paperK δgapB n ≤ Twobites.paperK (δsplit + δsumGap + δgapB) n := by
      apply Twobites.paperK_le_paperK_of_le
      nlinarith
    linarith
  have hκR :
      ρR + (1 + ε2) * β + (δsplit + δsumGap + δgapR) ≤ κ := by
    simpa [add_assoc, add_left_comm, add_comm] using hκ2R
  have hκB :
      ρB + (1 + ε2) * β + (δsplit + δsumGap + δgapB) ≤ κ := by
    simpa [add_assoc, add_left_comm, add_comm] using hκ2B
  exact
    C.paper_huge_deterministic_of_witness_bound_of_diagCoeff_of_bounds
      (δR := δsplit + δsumGap + δgapR) (δB := δsplit + δsumGap + δgapB)
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR
      hρB hβ hε2 hgapR hgapB hκR hκB hε1 hbound hdiagCoeff hsplit hsumGap hdegBound
      hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_ratio_witness_bound_of_diagCoeff_of_bounds_of_gaps
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB B : ℝ}
    {witnessSize : ℕ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hwitness :
      Twobites.paperKNat κ n < witnessSize * ⌈Twobites.paperT1 n⌉₊ -
        witnessSize.choose 2 * codegreeBound)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hloglog : 0 < Real.log (Real.log (n : ℝ)))
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1 : 0 ≤ ε1)
    (hbound :
      (witnessSize : ℝ) ≤ B * (Twobites.paperK κ n / Twobites.paperT1 n))
    (hdiagCoeff :
      ((B * κ * Real.log (Real.log (n : ℝ))) * βdeg / Twobites.paperS n) *
          (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      ((B * κ * Real.log (Real.log (n : ℝ))) * βdeg) / Twobites.paperS n +
          ((((B * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hbound' :
      (witnessSize : ℝ) ≤ B * κ * Real.log (Real.log (n : ℝ)) := by
    exact Twobites.le_mul_mul_loglog_of_le_mul_paperK_div_paperT1 hbound hn hloglog
  exact
    C.paper_huge_deterministic_of_witness_bound_of_diagCoeff_of_bounds_of_gaps
      (B := B * κ * Real.log (Real.log (n : ℝ))) hD I hI hwitness hred hblue hblueCap
      hblueCapWeight hredCap hredCapWeight hn hρR hρB hβ hε2 hε1 hbound' hdiagCoeff
      hsplit hsumGap hdegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B
      hredCrossSmall

theorem paper_huge_deterministic_of_paperHugeWitness_of_diagCoeff_of_bounds_of_gaps
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hloglog : 0 < Real.log (Real.log (n : ℝ))) (hκ : 0 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hT1 : 2 < Twobites.paperT1 n)
    (hchoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hε1 : 0 ≤ ε1)
    (hdiagCoeff :
      ((2 * κ * Real.log (Real.log (n : ℝ)) + 2) * βdeg / Twobites.paperS n) *
          (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      ((2 * κ * Real.log (Real.log (n : ℝ)) + 2) * βdeg) / Twobites.paperS n +
          ((((2 * κ * Real.log (Real.log (n : ℝ)) + 2) ^ 2 / 2) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have htwo :
      2 * Twobites.paperKNat κ n <
        Twobites.paperHugeWitnessNat κ n * ⌈Twobites.paperT1 n⌉₊ :=
    Twobites.two_mul_paperKNat_lt_paperHugeWitnessNat_mul_ceil_paperT1 hκ hT1
  have hwitness :
      Twobites.paperKNat κ n <
        Twobites.paperHugeWitnessNat κ n * ⌈Twobites.paperT1 n⌉₊ -
          (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound :=
    Twobites.paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_of_two_mul_lt htwo hchoose
  have hbound :
      (Twobites.paperHugeWitnessNat κ n : ℝ) ≤
        2 * κ * Real.log (Real.log (n : ℝ)) + 2 :=
    Twobites.paperHugeWitnessNat_le_two_mul_mul_loglog_add_two hκ hn hloglog
  exact
    C.paper_huge_deterministic_of_witness_bound_of_diagCoeff_of_bounds_of_gaps
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR
      hρB hβ hε2 hε1 hbound hdiagCoeff hsplit hsumGap hdegBound hcodegBound hgap2R
      hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_paperHugeWitness_of_ratioGap_of_diagCoeff_of_bounds_of_gaps
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB η : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hloglog : 0 < Real.log (Real.log (n : ℝ))) (hκ : 0 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hT1 : 2 < Twobites.paperT1 n)
    (hgapWitness : 2 ≤ η * (κ * Real.log (Real.log (n : ℝ))))
    (hchoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hε1 : 0 ≤ ε1)
    (hdiagCoeff :
      (((2 + η) * κ * Real.log (Real.log (n : ℝ))) * βdeg / Twobites.paperS n) *
          (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      (((2 + η) * κ * Real.log (Real.log (n : ℝ))) * βdeg) / Twobites.paperS n +
          ((((((2 + η) * κ * Real.log (Real.log (n : ℝ))) ^ 2) / 2) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have htwo :
      2 * Twobites.paperKNat κ n <
        Twobites.paperHugeWitnessNat κ n * ⌈Twobites.paperT1 n⌉₊ :=
    Twobites.two_mul_paperKNat_lt_paperHugeWitnessNat_mul_ceil_paperT1 hκ hT1
  have hwitness :
      Twobites.paperKNat κ n <
        Twobites.paperHugeWitnessNat κ n * ⌈Twobites.paperT1 n⌉₊ -
          (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound :=
    Twobites.paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_of_two_mul_lt htwo hchoose
  have hbound :
      (Twobites.paperHugeWitnessNat κ n : ℝ) ≤
        (2 + η) * (Twobites.paperK κ n / Twobites.paperT1 n) := by
    have hT1pos : 0 < Twobites.paperT1 n := by linarith
    exact
      Twobites.paperHugeWitnessNat_le_two_add_eta_mul_paperK_div_paperT1 hκ hT1pos
        (by rwa [Twobites.paperK_div_paperT1_eq_mul_loglog hn hloglog])
  exact
    C.paper_huge_deterministic_of_ratio_witness_bound_of_diagCoeff_of_bounds_of_gaps
      (B := 2 + η) hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap
      hredCapWeight hn hloglog hρR hρB hβ hε2 hε1 hbound hdiagCoeff hsplit hsumGap
      hdegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_paperHugeWitness_of_loglogSlack_of_diagCoeff_of_bounds_of_gaps
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB η : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hT1 : 2 < Twobites.paperT1 n) (hη : 0 < η)
    (hloglogGap : 2 / η ≤ Real.log (Real.log (n : ℝ)))
    (hchoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hε1 : 0 ≤ ε1)
    (hdiagCoeff :
      (((2 + η) * κ * Real.log (Real.log (n : ℝ))) * βdeg / Twobites.paperS n) *
          (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      (((2 + η) * κ * Real.log (Real.log (n : ℝ))) * βdeg) / Twobites.paperS n +
          ((((((2 + η) * κ * Real.log (Real.log (n : ℝ))) ^ 2) / 2) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hloglog : 0 < Real.log (Real.log (n : ℝ)) := by
    exact Twobites.loglog_pos_of_two_div_le hη hloglogGap
  have hgapWitness : 2 ≤ η * (κ * Real.log (Real.log (n : ℝ))) :=
    Twobites.two_le_eta_mul_mul_loglog_of_two_div_loglog_le hκ hη hloglogGap
  exact
    C.paper_huge_deterministic_of_paperHugeWitness_of_ratioGap_of_diagCoeff_of_bounds_of_gaps
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hloglog hκ0
      hρR hρB hβ hε2 hT1 hgapWitness hchoose hε1 hdiagCoeff hsplit hsumGap hdegBound
      hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_diagCoeff_of_bounds_of_gaps
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hchoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hε1 : 0 ≤ ε1)
    (hdiagCoeff :
      (((2 + ε1) * κ * Real.log (Real.log (n : ℝ))) * βdeg / Twobites.paperS n) *
          (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      (((2 + ε1) * κ * Real.log (Real.log (n : ℝ))) * βdeg) / Twobites.paperS n +
          ((((((2 + ε1) * κ * Real.log (Real.log (n : ℝ))) ^ 2) / 2) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  exact
    C.paper_huge_deterministic_of_paperHugeWitness_of_loglogSlack_of_diagCoeff_of_bounds_of_gaps
      (η := ε1) hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ
      hρR hρB hβ hε2 hT1 hε1pos hloglogGap hchoose hε1 hdiagCoeff hsplit hsumGap
      hdegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem
    paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_diagCoeff_of_bounds_of_gaps_of_le
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB B : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hchoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hε1 : 0 ≤ ε1) (hB :
      (2 + ε1) * κ * Real.log (Real.log (n : ℝ)) ≤ B)
    (hdiagCoeff :
      (B * βdeg / Twobites.paperS n) * (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hloglog : 0 < Real.log (Real.log (n : ℝ)) := by
    exact Twobites.loglog_pos_of_two_div_le hε1pos hloglogGap
  have hβdeg : 0 ≤ βdeg := Twobites.nonneg_of_le_paperP_mul_paperM hn hdegBound
  have hqcodeg : 0 ≤ qcodeg := Twobites.nonneg_of_natCast_le hcodegBound
  have hB0 :
      0 ≤ (2 + ε1) * κ * Real.log (Real.log (n : ℝ)) := by
    have hfac : 0 ≤ 2 + ε1 := by linarith
    exact mul_nonneg (mul_nonneg hfac hκ0) hloglog.le
  have hdiagCoeff' :
      (((2 + ε1) * κ * Real.log (Real.log (n : ℝ))) * βdeg / Twobites.paperS n) *
          (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n := by
    exact (Twobites.diagCoeffTerm_le_of_le hκ0 hβdeg hB).trans hdiagCoeff
  have hsplit' :
      (((2 + ε1) * κ * Real.log (Real.log (n : ℝ))) * βdeg) / Twobites.paperS n +
          ((((((2 + ε1) * κ * Real.log (Real.log (n : ℝ))) ^ 2) / 2) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit := by
    exact (Twobites.splitCoeffReal_le_of_le hB0 hB hβdeg hqcodeg).trans hsplit
  exact
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_diagCoeff_of_bounds_of_gaps
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ hρR hρB
      hβ hε2 hT1 hε1pos hloglogGap hchoose hε1 hdiagCoeff' hsplit' hsumGap hdegBound
      hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_le_of_codegCoeff
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB B : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hε1 : 0 ≤ ε1) (hB :
      (2 + ε1) * κ * Real.log (Real.log (n : ℝ)) ≤ B)
    (hdiagCoeff :
      (B * βdeg / Twobites.paperS n) * (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hchooseCoeff :
      ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ κ)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hloglog : 0 < Real.log (Real.log (n : ℝ)) := by
    exact Twobites.loglog_pos_of_two_div_le hε1pos hloglogGap
  have hgapWitness : 2 ≤ ε1 * (κ * Real.log (Real.log (n : ℝ))) :=
    Twobites.two_le_eta_mul_mul_loglog_of_two_div_loglog_le hκ hε1pos hloglogGap
  have hwitnessBoundBase :
      (Twobites.paperHugeWitnessNat κ n : ℝ) ≤
        (2 + ε1) * κ * Real.log (Real.log (n : ℝ)) := by
    exact
      Twobites.paperHugeWitnessNat_le_two_add_eta_mul_mul_loglog hκ0 hn hloglog
        hgapWitness
  have hwitnessBound : (Twobites.paperHugeWitnessNat κ n : ℝ) ≤ B :=
    hwitnessBoundBase.trans hB
  have hchooseReal :
      (((Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound : ℕ) : ℝ) ≤
        Twobites.paperK
          (((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n := by
    exact
      Twobites.cast_choose_mul_le_paperK_of_real_bound hwitnessBound hn hchooseCodegBound
  have hchooseReal' :
      (((Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound : ℕ) : ℝ) ≤
        Twobites.paperK κ n := by
    exact hchooseReal.trans <| Twobites.paperK_le_paperK_of_le hchooseCoeff
  have hchoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n := by
    exact Twobites.nat_le_paperKNat_of_le_paperK hchooseReal'
  exact
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_diagCoeff_of_bounds_of_gaps_of_le
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ hρR hρB
      hβ hε2 hT1 hε1pos hloglogGap hchoose hε1 hB hdiagCoeff hsplit hsumGap hdegBound
      hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_le_of_splitCoeff
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB B : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hε1 : 0 ≤ ε1) (hB :
      (2 + ε1) * κ * Real.log (Real.log (n : ℝ)) ≤ B)
    (hdiagCoeff :
      (B * βdeg / Twobites.paperS n) * (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      (B * βdeg) / Twobites.paperS n +
          ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hloglog : 0 < Real.log (Real.log (n : ℝ)) := by
    exact Twobites.loglog_pos_of_two_div_le hε1pos hloglogGap
  have hB0 : 0 ≤ B := by
    have hfac : 0 ≤ 2 + ε1 := by linarith
    have hbase :
        0 ≤ (2 + ε1) * κ * Real.log (Real.log (n : ℝ)) := by
      exact mul_nonneg (mul_nonneg hfac hκ0) hloglog.le
    linarith
  have hβdeg : 0 ≤ βdeg := Twobites.nonneg_of_le_paperP_mul_paperM hn hdegBound
  have hsplitFirstNonneg : 0 ≤ (B * βdeg) / Twobites.paperS n := by
    exact div_nonneg (mul_nonneg hB0 hβdeg) (Twobites.paperS_nonneg n)
  have hgap1R : 1 ≤ Twobites.paperK δgapR n := by linarith
  have hδsumGap : 0 ≤ δsumGap := Twobites.nonneg_of_one_le_paperK hn hsumGap
  have hδgapR : 0 ≤ δgapR := Twobites.nonneg_of_one_le_paperK hn hgap1R
  have hδsplit_le_κ : δsplit ≤ κ := by
    have hfac : 0 ≤ 1 + ε2 := by linarith
    have hbase : 0 ≤ ρR + (1 + ε2) * β + δsumGap + δgapR := by
      nlinarith
    linarith
  have hchooseCoeff :
      ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ κ := by
    have hqterm_le_dsplit :
        ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ δsplit := by
      linarith
    exact hqterm_le_dsplit.trans hδsplit_le_κ
  exact
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_le_of_codegCoeff
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ hρR hρB
      hβ hε2 hT1 hε1pos hloglogGap hε1 hB hdiagCoeff hsplit hsumGap hdegBound
      hchooseCodegBound hcodegBound hchooseCoeff hgap2R hκ2R hblueCrossSmall hgap2B
      hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hε1 : 0 ≤ ε1)
    (hdiagCoeff :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * βdeg / Twobites.paperS n) *
          (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n)
    (hsplit :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * βdeg) / Twobites.paperS n +
          ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hloglog : 0 < Real.log (Real.log (n : ℝ)) := by
    exact Twobites.loglog_pos_of_two_div_le hε1pos hloglogGap
  have hκloglog : 0 ≤ κ * Real.log (Real.log (n : ℝ)) := by
    exact mul_nonneg hκ0 hloglog.le
  have hB :
      (2 + ε1) * κ * Real.log (Real.log (n : ℝ)) ≤
        3 * κ * Real.log (Real.log (n : ℝ)) := by
    have hconst : 2 + ε1 ≤ 3 := by linarith
    nlinarith
  have hT1 : 2 < Twobites.paperT1 n := by
    exact
      Twobites.two_lt_paperT1_of_two_div_le_of_le_one
        hn hε1pos hε1le hloglogGap
  exact
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_le_of_splitCoeff
      (B := 3 * κ * Real.log (Real.log (n : ℝ))) hD I hI hred hblue hblueCap
      hblueCapWeight hredCap hredCapWeight hn hκ hρR hρB hβ hε2 hT1 hε1pos hloglogGap
      hε1 hB hdiagCoeff hsplit hsumGap hdegBound hchooseCodegBound hcodegBound hgap2R
      hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

theorem paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hε1 : 0 ≤ ε1)
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hsplit :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * βdeg) / Twobites.paperS n +
          ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hloglogOne : 1 ≤ Real.log (Real.log (n : ℝ)) := by
    exact Twobites.one_le_loglog_of_two_div_le_of_le_one hε1pos hε1le hloglogGap
  have hT1 : 2 < Twobites.paperT1 n := by
    exact
      Twobites.two_lt_paperT1_of_two_div_le_of_le_one
        hn hε1pos hε1le hloglogGap
  have hk : 1 ≤ Twobites.paperK κ n := by
    have hT1leK : Twobites.paperT1 n ≤ Twobites.paperK κ n :=
      Twobites.paperT1_le_paperK hloglogOne hκ
    linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hdiagCoeff :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * βdeg / Twobites.paperS n) *
          (Twobites.paperK κ n + 1) ≤
        2 * ε1 * κ * Twobites.paperK κ n := by
    exact Twobites.three_loglog_diagCoeff_le hn hκ0 hε1 hk hdiagScale
  exact
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ hρR
      hρB hβ hε2 hε1pos hε1le hloglogGap hε1 hdiagCoeff hsplit hsumGap
      hdegBound hchooseCodegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B
      hκ2B hredCrossSmall

theorem
    paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegCoeff
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB δcodeg : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hε1 : 0 ≤ ε1)
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegCoeff :
      ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      δcodeg)
    (hsplitGap : ε1 * κ + δcodeg ≤ δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hsplit :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * βdeg) / Twobites.paperS n +
          ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * qcodeg) /
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        δsplit := by
    have hfirst :
        ((3 * κ * Real.log (Real.log (n : ℝ))) * βdeg) / Twobites.paperS n ≤ ε1 * κ := by
      exact Twobites.three_loglog_split_first_le hn hκ0 hdiagScale
    linarith
  exact
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ hρR
      hρB hβ hε2 hε1pos hε1le hloglogGap hε1 hdiagScale hsplit hsumGap
      hdegBound hchooseCodegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B
      hκ2B hredCrossSmall

theorem
    paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsplit δsumGap δgapR δgapB δcodeg : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hε1 : 0 ≤ ε1)
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      δcodeg)
    (hsplitGap : ε1 * κ + δcodeg ≤ δsplit)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + δsplit + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + δsplit + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK δsplit n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hcodegCoeff :
      ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      δcodeg := by
    convert hcodegScale using 1
    ring_nf
  exact
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegCoeff
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ hρR
      hρB hβ hε2 hε1pos hε1le hloglogGap hε1 hdiagScale hcodegCoeff
      hsplitGap hsumGap hdegBound hchooseCodegBound hcodegBound hgap2R hκ2R
      hblueCrossSmall hgap2B hκ2B hredCrossSmall

set_option linter.style.longLine false in
theorem
    paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale_of_split
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB δcodeg : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hε1 : 0 ≤ ε1)
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      δcodeg)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + (ε1 * κ + δcodeg) + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK (ε1 * κ + δcodeg) n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + (ε1 * κ + δcodeg) + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK (ε1 * κ + δcodeg) n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  simpa [add_assoc, add_left_comm, add_comm] using
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale
      (δsplit := ε1 * κ + δcodeg) hD I hI hred hblue hblueCap hblueCapWeight hredCap
      hredCapWeight hn hκ hρR hρB hβ hε2 hε1pos hε1le hloglogGap hε1 hdiagScale
      hcodegScale (le_rfl : ε1 * κ + δcodeg ≤ ε1 * κ + δcodeg) hsumGap hdegBound
      hchooseCodegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B
      hredCrossSmall

set_option linter.style.longLine false in
theorem
    paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale_of_doubleEps
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hε1 : 0 ≤ ε1)
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      (3 : ℝ) * Twobites.paperK (2 * ε1 * κ) n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      (3 : ℝ) * Twobites.paperK (2 * ε1 * κ) n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hsplitEq : 2 * ε1 * κ = ε1 * κ + ε1 * κ := by ring
  have hκ2R' :
      ρR + (1 + ε2) * β + (ε1 * κ + ε1 * κ) + δsumGap + δgapR ≤ κ := by
    simpa [hsplitEq, add_assoc, add_left_comm, add_comm] using hκ2R
  have hκ2B' :
      ρB + (1 + ε2) * β + (ε1 * κ + ε1 * κ) + δsumGap + δgapB ≤ κ := by
    simpa [hsplitEq, add_assoc, add_left_comm, add_comm] using hκ2B
  have hblueCrossSmall' :
      (3 : ℝ) * Twobites.paperK (ε1 * κ + ε1 * κ) n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    simpa [hsplitEq] using hblueCrossSmall
  have hredCrossSmall' :
      (3 : ℝ) * Twobites.paperK (ε1 * κ + ε1 * κ) n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    simpa [hsplitEq] using hredCrossSmall
  simpa [hsplitEq, add_assoc, add_left_comm, add_comm] using
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale_of_split
      (δcodeg := ε1 * κ) hD I hI hred hblue hblueCap hblueCapWeight hredCap
      hredCapWeight hn hκ hρR hρB hβ hε2 hε1pos hε1le hloglogGap hε1 hdiagScale
      hcodegScale hsumGap hdegBound hchooseCodegBound hcodegBound hgap2R hκ2R'
      hblueCrossSmall' hgap2B hκ2B' hredCrossSmall'

set_option linter.style.longLine false in
theorem
    paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale_of_doubleEps_of_kSmall
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB : ℝ}
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hn : 1 < n) (hκ : 1 ≤ κ)
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hε1 : 0 ≤ ε1)
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) ∧
      (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
            (1 + ε1) *
              ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) ∧
          (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ)) := by
  have hblueCrossSmall' :
      (3 : ℝ) * Twobites.paperK (2 * ε1 * κ) n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    rw [Twobites.three_mul_paperK_two_mul_eq]
    exact mul_le_mul_of_nonneg_left hblueCrossSmall hε1
  have hredCrossSmall' :
      (3 : ℝ) * Twobites.paperK (2 * ε1 * κ) n ≤
        ε1 *
          (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
              Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    rw [Twobites.three_mul_paperK_two_mul_eq]
    exact mul_le_mul_of_nonneg_left hredCrossSmall hε1
  exact
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale_of_doubleEps
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ hρR hρB
      hβ hε2 hε1pos hε1le hloglogGap hε1 hdiagScale hcodegScale hsumGap hdegBound
      hchooseCodegBound hcodegBound hgap2R hκ2R hblueCrossSmall' hgap2B hκ2B
      hredCrossSmall'

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

theorem closedPairOn_of_mem (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {x : BaseVertex m} {v w : Fin n} (hx : x ∈ A)
    (hvX : v ∈ C.X I x) (hwX : w ∈ C.X I x) (hvw : v ≠ w) : C.ClosedPairOn I A v w := by
  exact ⟨C.mem_I_of_mem_X hvX, C.mem_I_of_mem_X hwX, hvw, x, hx, hvX, hwX⟩

theorem closedPairPlusOn_of_mem (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {x : BaseVertex m} {v w : Fin n} (hx : x ∈ A)
    (hvX : v ∈ C.XPlus I x) (hwX : w ∈ C.XPlus I x) (hvw : v ≠ w) :
    C.ClosedPairPlusOn I A v w := by
  exact ⟨C.mem_I_of_mem_XPlus hvX, C.mem_I_of_mem_XPlus hwX, hvw, x, hx, hvX, hwX⟩

theorem closedPairOn_mono (C : ConstructionData n m) {I : Finset (Fin n)}
    {A B : Finset (BaseVertex m)} (hAB : A ⊆ B) {v w : Fin n} :
    C.ClosedPairOn I A v w → C.ClosedPairOn I B v w := by
  rintro ⟨hvI, hwI, hvw, x, hxA, hvX, hwX⟩
  exact ⟨hvI, hwI, hvw, x, hAB hxA, hvX, hwX⟩

theorem closedPairPlusOn_mono (C : ConstructionData n m) {I : Finset (Fin n)}
    {A B : Finset (BaseVertex m)} (hAB : A ⊆ B) {v w : Fin n} :
    C.ClosedPairPlusOn I A v w → C.ClosedPairPlusOn I B v w := by
  rintro ⟨hvI, hwI, hvw, x, hxA, hvX, hwX⟩
  exact ⟨hvI, hwI, hvw, x, hAB hxA, hvX, hwX⟩

theorem closedPairOn_to_closedPair (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {v w : Fin n} (h : C.ClosedPairOn I A v w) :
    C.ClosedPair I v w := by
  rcases h with ⟨hvI, hwI, hvw, x, -, hvX, hwX⟩
  exact ⟨hvI, hwI, hvw, x, hvX, hwX⟩

theorem closedPairPlusOn_to_closedPairPlus (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {v w : Fin n} (h : C.ClosedPairPlusOn I A v w) :
    C.ClosedPairPlus I v w := by
  rcases h with ⟨hvI, hwI, hvw, x, -, hvX, hwX⟩
  exact ⟨hvI, hwI, hvw, x, hvX, hwX⟩

theorem closedPairPlusOn_to_closedPairOn (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {v w : Fin n} (h : C.ClosedPairPlusOn I A v w) :
    C.ClosedPairOn I A v w := by
  rcases h with ⟨hvI, hwI, hvw, x, hxA, hvX, hwX⟩
  exact ⟨hvI, hwI, hvw, x, hxA, C.mem_X_of_mem_XPlus hvX, C.mem_X_of_mem_XPlus hwX⟩

theorem openPairOn_mono (C : ConstructionData n m) {I : Finset (Fin n)}
    {A B : Finset (BaseVertex m)} (hAB : A ⊆ B) {v w : Fin n} :
    C.OpenPairOn I B v w → C.OpenPairOn I A v w := by
  rintro ⟨hvI, hwI, hvw, hopen⟩
  refine ⟨hvI, hwI, hvw, ?_⟩
  intro hclosed
  exact hopen (C.closedPairOn_mono hAB hclosed)

theorem openPairPlusOn_mono (C : ConstructionData n m) {I : Finset (Fin n)}
    {A B : Finset (BaseVertex m)} (hAB : A ⊆ B) {v w : Fin n} :
    C.OpenPairPlusOn I B v w → C.OpenPairPlusOn I A v w := by
  rintro ⟨hvI, hwI, hvw, hopen⟩
  refine ⟨hvI, hwI, hvw, ?_⟩
  intro hclosed
  exact hopen (C.closedPairPlusOn_mono hAB hclosed)

theorem openPairOn_of_openPair (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {v w : Fin n} (h : C.OpenPair I v w) :
    C.OpenPairOn I A v w := by
  rcases h with ⟨hvI, hwI, hvw, hopen⟩
  refine ⟨hvI, hwI, hvw, ?_⟩
  intro hclosed
  exact hopen (C.closedPairOn_to_closedPair hclosed)

theorem openPairPlusOn_of_openPairPlus (C : ConstructionData n m) {I : Finset (Fin n)}
    {A : Finset (BaseVertex m)} {v w : Fin n} (h : C.OpenPairPlus I v w) :
    C.OpenPairPlusOn I A v w := by
  rcases h with ⟨hvI, hwI, hvw, hopen⟩
  refine ⟨hvI, hwI, hvw, ?_⟩
  intro hclosed
  exact hopen (C.closedPairPlusOn_to_closedPairPlus hclosed)

theorem closedPairOn_univ_iff_closedPair (C : ConstructionData n m) {I : Finset (Fin n)}
    {v w : Fin n} : C.ClosedPairOn I Finset.univ v w ↔ C.ClosedPair I v w := by
  constructor
  · exact C.closedPairOn_to_closedPair
  · rintro ⟨hvI, hwI, hvw, x, hvX, hwX⟩
    exact ⟨hvI, hwI, hvw, x, by simp, hvX, hwX⟩

theorem closedPairPlusOn_univ_iff_closedPairPlus (C : ConstructionData n m) {I : Finset (Fin n)}
    {v w : Fin n} : C.ClosedPairPlusOn I Finset.univ v w ↔ C.ClosedPairPlus I v w := by
  constructor
  · exact C.closedPairPlusOn_to_closedPairPlus
  · rintro ⟨hvI, hwI, hvw, x, hvX, hwX⟩
    exact ⟨hvI, hwI, hvw, x, by simp, hvX, hwX⟩

theorem openPairOn_univ_iff_openPair (C : ConstructionData n m) {I : Finset (Fin n)}
    {v w : Fin n} : C.OpenPairOn I Finset.univ v w ↔ C.OpenPair I v w := by
  constructor
  · rintro ⟨hvI, hwI, hvw, hopen⟩
    refine ⟨hvI, hwI, hvw, ?_⟩
    intro hclosed
    exact hopen ((C.closedPairOn_univ_iff_closedPair).2 hclosed)
  · exact C.openPairOn_of_openPair

theorem openPairPlusOn_univ_iff_openPairPlus (C : ConstructionData n m) {I : Finset (Fin n)}
    {v w : Fin n} : C.OpenPairPlusOn I Finset.univ v w ↔ C.OpenPairPlus I v w := by
  constructor
  · rintro ⟨hvI, hwI, hvw, hopen⟩
    refine ⟨hvI, hwI, hvw, ?_⟩
    intro hclosed
    exact hopen ((C.closedPairPlusOn_univ_iff_closedPairPlus).2 hclosed)
  · exact C.openPairPlusOn_of_openPairPlus

theorem closedPair_of_redMonochromaticDeletionWitness (C : ConstructionData n m)
    {I : Finset (Fin n)} {u v w : Fin n} (hvI : v ∈ I) (hwI : w ∈ I) (hvw : v ≠ w)
    (h : C.redMonochromaticDeletionWitness u v w) : C.ClosedPair I v w := by
  rcases h with ⟨huv, huw, -, -⟩
  exact ⟨hvI, hwI, hvw, Sum.inl (C.redProj u), (C.mem_X_red).2 ⟨hvI, huv⟩,
    (C.mem_X_red).2 ⟨hwI, huw⟩⟩

theorem redProj_lt_lt_of_redMonochromaticDeletionWitness (C : ConstructionData n m)
    {u v w : Fin n} (h : C.redMonochromaticDeletionWitness u v w) :
    C.redProj u < C.redProj v ∧ C.redProj u < C.redProj w := by
  rcases h with ⟨-, -, hvw, hLater⟩
  have hvwNe : C.redProj v ≠ C.redProj w := C.redProj_ne_of_redLift_adj hvw
  rcases lt_or_gt_of_ne hvwNe with hvwLt | hwvLt
  · have huvLt : C.redProj u < C.redProj v :=
      lt_of_pairLex_orderedPair_right hvwLt hLater.2
    exact ⟨huvLt, huvLt.trans hvwLt⟩
  · have huwLt : C.redProj u < C.redProj w :=
      lt_of_pairLex_orderedPair_left hwvLt hLater.1
    exact ⟨huwLt.trans hwvLt, huwLt⟩

theorem closedPairPlus_of_redMonochromaticDeletionWitness (C : ConstructionData n m)
    {I : Finset (Fin n)} {u v w : Fin n} (hvI : v ∈ I) (hwI : w ∈ I) (hvw : v ≠ w)
    (h : C.redMonochromaticDeletionWitness u v w) : C.ClosedPairPlus I v w := by
  have hlt := C.redProj_lt_lt_of_redMonochromaticDeletionWitness h
  rcases h with ⟨huv, huw, -, -⟩
  exact
    ⟨hvI, hwI, hvw, Sum.inl (C.redProj u),
      (C.mem_XPlus_red).2 ⟨hvI, huv, hlt.1⟩,
      (C.mem_XPlus_red).2 ⟨hwI, huw, hlt.2⟩⟩

theorem closedPair_of_blueMonochromaticDeletionWitness (C : ConstructionData n m)
    {I : Finset (Fin n)} {u v w : Fin n} (hvI : v ∈ I) (hwI : w ∈ I) (hvw : v ≠ w)
    (h : C.blueMonochromaticDeletionWitness u v w) : C.ClosedPair I v w := by
  rcases h with ⟨huv, huw, -, -⟩
  exact ⟨hvI, hwI, hvw, Sum.inr (C.blueProj u), (C.mem_X_blue).2 ⟨hvI, huv⟩,
    (C.mem_X_blue).2 ⟨hwI, huw⟩⟩

theorem blueProj_lt_lt_of_blueMonochromaticDeletionWitness (C : ConstructionData n m)
    {u v w : Fin n} (h : C.blueMonochromaticDeletionWitness u v w) :
    C.blueProj u < C.blueProj v ∧ C.blueProj u < C.blueProj w := by
  rcases h with ⟨-, -, hvw, hLater⟩
  have hvwNe : C.blueProj v ≠ C.blueProj w := C.blueProj_ne_of_blueLift_adj hvw
  rcases lt_or_gt_of_ne hvwNe with hvwLt | hwvLt
  · have huvLt : C.blueProj u < C.blueProj v :=
      lt_of_pairLex_orderedPair_right hvwLt hLater.2
    exact ⟨huvLt, huvLt.trans hvwLt⟩
  · have huwLt : C.blueProj u < C.blueProj w :=
      lt_of_pairLex_orderedPair_left hwvLt hLater.1
    exact ⟨huwLt.trans hwvLt, huwLt⟩

theorem closedPairPlus_of_blueMonochromaticDeletionWitness (C : ConstructionData n m)
    {I : Finset (Fin n)} {u v w : Fin n} (hvI : v ∈ I) (hwI : w ∈ I) (hvw : v ≠ w)
    (h : C.blueMonochromaticDeletionWitness u v w) : C.ClosedPairPlus I v w := by
  have hlt := C.blueProj_lt_lt_of_blueMonochromaticDeletionWitness h
  rcases h with ⟨huv, huw, -, -⟩
  exact
    ⟨hvI, hwI, hvw, Sum.inr (C.blueProj u),
      (C.mem_XPlus_blue).2 ⟨hvI, huv, hlt.1⟩,
      (C.mem_XPlus_blue).2 ⟨hwI, huw, hlt.2⟩⟩

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

set_option linter.style.longLine false in
theorem redMonochromaticWitnessBiUnion_card_le_redProjectionPairCount_filter_isRed
    (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.redMonochromaticWitnessBiUnion I).card ≤
      C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) := by
  calc
    (C.redMonochromaticWitnessBiUnion I).card ≤
        ∑ r ∈ (Finset.univ : Finset (Fin m)),
          (((C.redProjectionImage I (Sum.inl r)).offDiag.image Sym2.mk).card) := by
      simpa [redMonochromaticWitnessBiUnion] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin m)))
          (t := fun r => (C.redProjectionImage I (Sum.inl r)).offDiag.image Sym2.mk))
    _ = ∑ r ∈ (Finset.univ : Finset (Fin m)),
          ((C.redProjectionImage I (Sum.inl r)).card).choose 2 := by
      simp [Sym2.card_image_offDiag]
    _ = C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) := by
      rw [redProjectionPairCount, univ_filter_isRed_eq_univ_image_inl]
      refine Finset.sum_bij (i := fun r _ => (Sum.inl r : BaseVertex m)) ?_ ?_ ?_ ?_
      · intro r _
        simp
      · intro r₁ _ r₂ _ h
        cases h
        rfl
      · intro x hx
        rcases Finset.mem_image.1 hx with ⟨r, hr, rfl⟩
        exact ⟨r, hr, rfl⟩
      · intro r _
        rfl

set_option linter.style.longLine false in
theorem blueMonochromaticWitnessBiUnion_card_le_blueProjectionPairCount_filter_isBlue
    (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.blueMonochromaticWitnessBiUnion I).card ≤
      C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) := by
  calc
    (C.blueMonochromaticWitnessBiUnion I).card ≤
        ∑ b ∈ (Finset.univ : Finset (Fin m)),
          (((C.blueProjectionImage I (Sum.inr b)).offDiag.image Sym2.mk).card) := by
      simpa [blueMonochromaticWitnessBiUnion] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin m)))
          (t := fun b => (C.blueProjectionImage I (Sum.inr b)).offDiag.image Sym2.mk))
    _ = ∑ b ∈ (Finset.univ : Finset (Fin m)),
          ((C.blueProjectionImage I (Sum.inr b)).card).choose 2 := by
      simp [Sym2.card_image_offDiag]
    _ = C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) := by
      rw [blueProjectionPairCount, univ_filter_isBlue_eq_univ_image_inr]
      refine Finset.sum_bij (i := fun b _ => (Sum.inr b : BaseVertex m)) ?_ ?_ ?_ ?_
      · intro b _
        simp
      · intro b₁ _ b₂ _ h
        cases h
        rfl
      · intro x hx
        rcases Finset.mem_image.1 hx with ⟨b, hb, rfl⟩
        exact ⟨b, hb, rfl⟩
      · intro b _
        rfl

set_option linter.style.longLine false in
theorem redBaseClosedPairSet_image_sym2_subset_redMonochromaticWitnessBiUnion_union_redOppositeWitnessBiUnion_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w) :
    (C.redBaseClosedPairSet I).image Sym2.mk ⊆
      C.redMonochromaticWitnessBiUnion I ∪ C.redOppositeWitnessBiUnion I ∅ := by
  intro z hz
  rcases Finset.mem_image.1 hz with ⟨p, hp, rfl⟩
  rcases p with ⟨r, r'⟩
  rcases (C.mem_redBaseClosedPairSet.1 hp) with ⟨hr, hr', hrr', hAdj⟩
  rcases C.mem_redImage.1 hr with ⟨v, hvI, hv⟩
  rcases C.mem_redImage.1 hr' with ⟨w, hwI, hw⟩
  have hvw : v ≠ w := by
    intro hvwEq
    have hprojEq : C.redProj v = C.redProj w := congrArg C.redProj hvwEq
    have hrrEq : r = r' := by
      rw [← hv, ← hw]
      exact hprojEq
    exact hrr'.ne hrrEq
  have hred : C.redLift.Adj v w := by
    rw [C.redLift_adj_iff, hv, hw]
    exact hAdj
  have hdel : C.redDeleted v w := by
    by_contra hnotDel
    exact (hindep hvI hwI hvw) <|
      (C.finalGraph_adj_iff.2 <| Or.inl <| (C.retainedRed_adj_iff.2 ⟨hred, hnotDel⟩))
  rcases hdel with ⟨u, hmono | hmixed⟩
  · refine Finset.mem_union.2 <| Or.inl ?_
    refine Finset.mem_biUnion.2 ⟨C.redProj u, by simp, ?_⟩
    refine Finset.mem_image.2 ⟨(r, r'), ?_, rfl⟩
    refine Finset.mem_offDiag.2 ⟨?_, ?_, hrr'.ne⟩
    · refine C.mem_redProjectionImage_inl.2 ?_
      refine ⟨?_, hr⟩
      rw [← hv]
      exact C.redLift_adj_iff.1 hmono.1
    · refine C.mem_redProjectionImage_inl.2 ?_
      refine ⟨?_, hr'⟩
      rw [← hw]
      exact C.redLift_adj_iff.1 hmono.2.1
  · refine Finset.mem_union.2 <| Or.inr ?_
    refine Finset.mem_biUnion.2 ⟨C.blueProj u, by simp, ?_⟩
    refine Finset.mem_image.2 ⟨(r, r'), ?_, rfl⟩
    refine Finset.mem_offDiag.2 ⟨?_, ?_, hrr'.ne⟩
    · refine C.mem_redProjectionImage_inr.2 ?_
      refine ⟨v, hvI, ?_, hv⟩
      simpa [C.blueLift_adj_iff] using hmixed.1
    · refine C.mem_redProjectionImage_inr.2 ?_
      refine ⟨w, hwI, ?_, hw⟩
      simpa [C.blueLift_adj_iff] using hmixed.2.1

set_option linter.style.longLine false in
theorem blueBaseClosedPairSet_image_sym2_subset_blueMonochromaticWitnessBiUnion_union_blueOppositeWitnessBiUnion_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w) :
    (C.blueBaseClosedPairSet I).image Sym2.mk ⊆
      C.blueMonochromaticWitnessBiUnion I ∪ C.blueOppositeWitnessBiUnion I ∅ := by
  intro z hz
  rcases Finset.mem_image.1 hz with ⟨p, hp, rfl⟩
  rcases p with ⟨b, b'⟩
  rcases (C.mem_blueBaseClosedPairSet.1 hp) with ⟨hb, hb', hbb', hAdj⟩
  rcases C.mem_blueImage.1 hb with ⟨v, hvI, hv⟩
  rcases C.mem_blueImage.1 hb' with ⟨w, hwI, hw⟩
  have hvw : v ≠ w := by
    intro hvwEq
    have hprojEq : C.blueProj v = C.blueProj w := congrArg C.blueProj hvwEq
    have hbbEq : b = b' := by
      rw [← hv, ← hw]
      exact hprojEq
    exact hbb'.ne hbbEq
  have hblue : C.blueLift.Adj v w := by
    rw [C.blueLift_adj_iff, hv, hw]
    exact hAdj
  have hdel : C.blueDeleted v w := by
    by_contra hnotDel
    exact (hindep hvI hwI hvw) <|
      (C.finalGraph_adj_iff.2 <| Or.inr <| (C.retainedBlue_adj_iff.2 ⟨hblue, hnotDel⟩))
  rcases hdel with ⟨u, hmono | hmixed⟩
  · refine Finset.mem_union.2 <| Or.inl ?_
    refine Finset.mem_biUnion.2 ⟨C.blueProj u, by simp, ?_⟩
    refine Finset.mem_image.2 ⟨(b, b'), ?_, rfl⟩
    refine Finset.mem_offDiag.2 ⟨?_, ?_, hbb'.ne⟩
    · refine C.mem_blueProjectionImage_inr.2 ?_
      refine ⟨?_, hb⟩
      rw [← hv]
      exact C.blueLift_adj_iff.1 hmono.1
    · refine C.mem_blueProjectionImage_inr.2 ?_
      refine ⟨?_, hb'⟩
      rw [← hw]
      exact C.blueLift_adj_iff.1 hmono.2.1
  · refine Finset.mem_union.2 <| Or.inr ?_
    refine Finset.mem_biUnion.2 ⟨C.redProj u, by simp, ?_⟩
    refine Finset.mem_image.2 ⟨(b, b'), ?_, rfl⟩
    refine Finset.mem_offDiag.2 ⟨?_, ?_, hbb'.ne⟩
    · refine C.mem_blueProjectionImage_inl.2 ?_
      refine ⟨v, hvI, ?_, hv⟩
      simpa [C.redLift_adj_iff] using hmixed.1
    · refine C.mem_blueProjectionImage_inl.2 ?_
      refine ⟨w, hwI, ?_, hw⟩
      simpa [C.redLift_adj_iff] using hmixed.2.1

set_option linter.style.longLine false in
theorem redBaseClosedPairSet_card_le_redProjectionPairCount_filter_isRed_add_filter_isBlue_of_indep
    (C : ConstructionData n m) (I : Finset (Fin n))
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w) :
    (C.redBaseClosedPairSet I).card ≤
      C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) +
        C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) := by
  have hstrict :
      ∀ p ∈ C.redBaseClosedPairSet I, p.1 < p.2 := by
    intro p hp
    exact (C.mem_redBaseClosedPairSet.1 hp).2.2.1
  have himage :
      (C.redBaseClosedPairSet I).card = ((C.redBaseClosedPairSet I).image Sym2.mk).card := by
    symm
    exact card_image_sym2_mk_of_strictPairSet _ hstrict
  have hmono :=
    C.redMonochromaticWitnessBiUnion_card_le_redProjectionPairCount_filter_isRed I
  have hopp :
      (C.redOppositeWitnessBiUnion I (∅ : Finset (BaseVertex m))).card ≤
        C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) := by
    calc
      (C.redOppositeWitnessBiUnion I (∅ : Finset (BaseVertex m))).card ≤
          ∑ b ∈ (Finset.univ : Finset (Fin m)),
            (((C.redProjectionImage I (Sum.inr b)).offDiag.image Sym2.mk).card) := by
        simpa [redOppositeWitnessBiUnion] using
          (Finset.card_biUnion_le
            (s := (Finset.univ : Finset (Fin m)))
            (t := fun b => (C.redProjectionImage I (Sum.inr b)).offDiag.image Sym2.mk))
      _ = ∑ b ∈ (Finset.univ : Finset (Fin m)),
            ((C.redProjectionImage I (Sum.inr b)).card).choose 2 := by
        simp [Sym2.card_image_offDiag]
      _ = C.redProjectionPairCount I
            ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) := by
        rw [redProjectionPairCount, univ_filter_isBlue_eq_univ_image_inr]
        refine Finset.sum_bij (i := fun b _ => (Sum.inr b : BaseVertex m)) ?_ ?_ ?_ ?_
        · intro b _
          simp
        · intro b₁ _ b₂ _ h
          cases h
          rfl
        · intro x hx
          rcases Finset.mem_image.1 hx with ⟨b, hb, rfl⟩
          exact ⟨b, hb, rfl⟩
        · intro b _
          rfl
  calc
    (C.redBaseClosedPairSet I).card = ((C.redBaseClosedPairSet I).image Sym2.mk).card := himage
    _ ≤
        (C.redMonochromaticWitnessBiUnion I).card +
          (C.redOppositeWitnessBiUnion I (∅ : Finset (BaseVertex m))).card := by
      exact
        (Finset.card_le_card
          (C.redBaseClosedPairSet_image_sym2_subset_redMonochromaticWitnessBiUnion_union_redOppositeWitnessBiUnion_of_indep
            hindep)).trans (Finset.card_union_le _ _)
    _ ≤
        C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) +
          C.redProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) := by
      exact Nat.add_le_add hmono hopp

set_option linter.style.longLine false in
theorem blueBaseClosedPairSet_card_le_blueProjectionPairCount_filter_isBlue_add_filter_isRed_of_indep
    (C : ConstructionData n m) (I : Finset (Fin n))
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w) :
    (C.blueBaseClosedPairSet I).card ≤
      C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) +
        C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) := by
  have hstrict :
      ∀ p ∈ C.blueBaseClosedPairSet I, p.1 < p.2 := by
    intro p hp
    exact (C.mem_blueBaseClosedPairSet.1 hp).2.2.1
  have himage :
      (C.blueBaseClosedPairSet I).card = ((C.blueBaseClosedPairSet I).image Sym2.mk).card := by
    symm
    exact card_image_sym2_mk_of_strictPairSet _ hstrict
  have hmono :=
    C.blueMonochromaticWitnessBiUnion_card_le_blueProjectionPairCount_filter_isBlue I
  have hopp :
      (C.blueOppositeWitnessBiUnion I (∅ : Finset (BaseVertex m))).card ≤
        C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) := by
    calc
      (C.blueOppositeWitnessBiUnion I (∅ : Finset (BaseVertex m))).card ≤
          ∑ r ∈ (Finset.univ : Finset (Fin m)),
            (((C.blueProjectionImage I (Sum.inl r)).offDiag.image Sym2.mk).card) := by
        simpa [blueOppositeWitnessBiUnion] using
          (Finset.card_biUnion_le
            (s := (Finset.univ : Finset (Fin m)))
            (t := fun r => (C.blueProjectionImage I (Sum.inl r)).offDiag.image Sym2.mk))
      _ = ∑ r ∈ (Finset.univ : Finset (Fin m)),
            ((C.blueProjectionImage I (Sum.inl r)).card).choose 2 := by
        simp [Sym2.card_image_offDiag]
      _ = C.blueProjectionPairCount I
            ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) := by
        rw [blueProjectionPairCount, univ_filter_isRed_eq_univ_image_inl]
        refine Finset.sum_bij (i := fun r _ => (Sum.inl r : BaseVertex m)) ?_ ?_ ?_ ?_
        · intro r _
          simp
        · intro r₁ _ r₂ _ h
          cases h
          rfl
        · intro x hx
          rcases Finset.mem_image.1 hx with ⟨r, hr, rfl⟩
          exact ⟨r, hr, rfl⟩
        · intro r _
          rfl
  calc
    (C.blueBaseClosedPairSet I).card = ((C.blueBaseClosedPairSet I).image Sym2.mk).card := himage
    _ ≤
        (C.blueMonochromaticWitnessBiUnion I).card +
          (C.blueOppositeWitnessBiUnion I (∅ : Finset (BaseVertex m))).card := by
      exact
        (Finset.card_le_card
          (C.blueBaseClosedPairSet_image_sym2_subset_blueMonochromaticWitnessBiUnion_union_blueOppositeWitnessBiUnion_of_indep
            hindep)).trans (Finset.card_union_le _ _)
    _ ≤
        C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsBlueBaseVertex) +
          C.blueProjectionPairCount I ((Finset.univ : Finset (BaseVertex m)).filter IsRedBaseVertex) := by
      exact Nat.add_le_add hmono hopp

set_option linter.style.longLine false in
theorem redBaseClosedPairSet_card_le_partPairCount_LMS_add_huge_diag_add_huge_cross_of_indep
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    (C.redBaseClosedPairSet I).card ≤
      C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
        C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
        C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) := by
  let A := C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε
  have hbase :=
    C.redBaseClosedPairSet_card_le_redProjectionPairCount_filter_isRed_add_filter_isBlue_of_indep
      I hindep
  have hred :=
    C.redProjectionPairCount_filter_isRed_le_partPairCount_LMS_filter_isRed_add_huge
      I ht21 ht32
  have hblue :=
    C.redProjectionPairCount_filter_isBlue_le_partPairCount_LMS_filter_isBlue_add_huge
      I ht21 ht32
  calc
    (C.redBaseClosedPairSet I).card ≤
      (C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.partPairCount I (A.filter IsRedBaseVertex)) +
        (C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
          C.partPairCount I (A.filter IsBlueBaseVertex)) := by
            exact hbase.trans (Nat.add_le_add hred hblue)
    _ = C.partPairCount I (A.filter IsRedBaseVertex) +
          C.partPairCount I (A.filter IsBlueBaseVertex) +
            C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
              C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) := by
        omega
    _ = C.partPairCount I A +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
            C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) := by
        rw [C.partPairCount_filter_isRed_add_partPairCount_filter_isBlue]

set_option linter.style.longLine false in
theorem blueBaseClosedPairSet_card_le_partPairCount_LMS_add_huge_diag_add_huge_cross_of_indep
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n) :
    (C.blueBaseClosedPairSet I).card ≤
      C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
        C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
        C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) := by
  let A := C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε
  have hbase :=
    C.blueBaseClosedPairSet_card_le_blueProjectionPairCount_filter_isBlue_add_filter_isRed_of_indep
      I hindep
  have hblue :=
    C.blueProjectionPairCount_filter_isBlue_le_partPairCount_LMS_filter_isBlue_add_huge
      I ht21 ht32
  have hred :=
    C.blueProjectionPairCount_filter_isRed_le_partPairCount_LMS_filter_isRed_add_huge
      I ht21 ht32
  calc
    (C.blueBaseClosedPairSet I).card ≤
      (C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
          C.partPairCount I (A.filter IsBlueBaseVertex)) +
        (C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.partPairCount I (A.filter IsRedBaseVertex)) := by
            exact hbase.trans (Nat.add_le_add hblue hred)
    _ = C.partPairCount I (A.filter IsRedBaseVertex) +
          C.partPairCount I (A.filter IsBlueBaseVertex) +
            C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
              C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) := by
        omega
    _ = C.partPairCount I A +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) +
            C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) := by
        rw [C.partPairCount_filter_isRed_add_partPairCount_filter_isBlue]

theorem redBaseClosedPairSet_card_le_paperHugeRedCrossTargetNat_add_of_indep_of_LMSHugeBounds
    (C : ConstructionData n m) (I : Finset (Fin n))
    {κ ε ε1 lmsError diagError : ℝ} {cap redError : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLMS :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) ≤
        lmsError)
    (hHugeDiag :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        diagError)
    (hHugeCross :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        (1 + ε1) * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ))
    (hError :
      lmsError + diagError +
          ε1 * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        (redError : ℝ)) :
    (C.redBaseClosedPairSet I).card ≤ C.paperHugeRedCrossTargetNat I κ cap + redError := by
  have hbase :=
    C.redBaseClosedPairSet_card_le_partPairCount_LMS_add_huge_diag_add_huge_cross_of_indep
      I hindep ht21 ht32
  have hbaseR :
      ((C.redBaseClosedPairSet I).card : ℝ) ≤
        ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) +
          ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) +
          ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) := by
    exact_mod_cast hbase
  have hsum :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) +
          ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) +
          ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) + (redError : ℝ) := by
    nlinarith [hLMS, hHugeDiag, hHugeCross, hError]
  have hfinalR :
      ((C.redBaseClosedPairSet I).card : ℝ) ≤
        ((C.paperHugeRedCrossTargetNat I κ cap + redError : ℕ) : ℝ) := by
    simpa [Nat.cast_add] using hbaseR.trans hsum
  exact_mod_cast hfinalR

theorem blueBaseClosedPairSet_card_le_paperHugeBlueCrossTargetNat_add_of_indep_of_LMSHugeBounds
    (C : ConstructionData n m) (I : Finset (Fin n))
    {κ ε ε1 lmsError diagError : ℝ} {cap blueError : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLMS :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) ≤
        lmsError)
    (hHugeDiag :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        diagError)
    (hHugeCross :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        (1 + ε1) * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ))
    (hError :
      lmsError + diagError +
          ε1 * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        (blueError : ℝ)) :
    (C.blueBaseClosedPairSet I).card ≤ C.paperHugeBlueCrossTargetNat I κ cap + blueError := by
  have hbase :=
    C.blueBaseClosedPairSet_card_le_partPairCount_LMS_add_huge_diag_add_huge_cross_of_indep
      I hindep ht21 ht32
  have hbaseR :
      ((C.blueBaseClosedPairSet I).card : ℝ) ≤
        ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) +
          ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) +
          ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) := by
    exact_mod_cast hbase
  have hsum :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) +
          ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) +
          ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) + (blueError : ℝ) := by
    nlinarith [hLMS, hHugeDiag, hHugeCross, hError]
  have hfinalR :
      ((C.blueBaseClosedPairSet I).card : ℝ) ≤
        ((C.paperHugeBlueCrossTargetNat I κ cap + blueError : ℕ) : ℝ) := by
    simpa [Nat.cast_add] using hbaseR.trans hsum
  exact_mod_cast hfinalR

set_option linter.style.longLine false in
theorem paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_splitClosedErrorBounds
    (C : ConstructionData n m) (I : Finset (Fin n))
    {κ ε ε1 largeError mediumError smallError redDiagError blueDiagError : ℝ}
    {cap redError blueError openError : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤ largeError)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤ mediumError)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤ smallError)
    (hHugeRedDiag :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        redDiagError)
    (hHugeBlueDiag :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        blueDiagError)
    (hHugeRedCross :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        (1 + ε1) * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ))
    (hHugeBlueCross :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        (1 + ε1) * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ))
    (hRedError :
      largeError + mediumError + smallError + redDiagError +
          ε1 * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        (redError : ℝ))
    (hBlueError :
      largeError + mediumError + smallError + blueDiagError +
          ε1 * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        (blueError : ℝ))
    (hOpenError : redError + blueError ≤ openError) :
    C.paperSection4OpenPairTargetNat I κ cap - openError ≤ (C.baseOpenPairSet I).card := by
  have hLMS :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) ≤
        largeError + mediumError + smallError := by
    exact C.cast_partPairCount_LMS_le_sum_of_thresholds I ht32 hLarge hMedium hSmall
  have hredClosed :
      (C.redBaseClosedPairSet I).card ≤ C.paperHugeRedCrossTargetNat I κ cap + redError := by
    have hRedError' :
        largeError + mediumError + smallError + redDiagError +
            ε1 * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) ≤
          (redError : ℝ) := hRedError
    exact
      C.redBaseClosedPairSet_card_le_paperHugeRedCrossTargetNat_add_of_indep_of_LMSHugeBounds
        I hindep ht21 ht32 hLMS hHugeRedDiag hHugeRedCross hRedError'
  have hblueClosed :
      (C.blueBaseClosedPairSet I).card ≤ C.paperHugeBlueCrossTargetNat I κ cap + blueError := by
    have hBlueError' :
        largeError + mediumError + smallError + blueDiagError +
            ε1 * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) ≤
          (blueError : ℝ) := hBlueError
    exact
      C.blueBaseClosedPairSet_card_le_paperHugeBlueCrossTargetNat_add_of_indep_of_LMSHugeBounds
        I hindep ht21 ht32 hLMS hHugeBlueDiag hHugeBlueCross hBlueError'
  exact
    C.paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_swappedClosedErrorBounds
      I hredClosed hblueClosed hOpenError

set_option linter.style.longLine false in
theorem paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_uniformPaperErrorBounds
    (C : ConstructionData n m) (I : Finset (Fin n))
    {κ ε ε1 : ℝ} {cap redError blueError openError : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHuge :
      (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
            ε1 * Twobites.paperK κ n ^ 2) ∧
          (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ)) ∧
            (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
                (1 + ε1) * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ)))
    (hRedError :
      4 * (ε1 * Twobites.paperK κ n ^ 2) +
          ε1 * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        (redError : ℝ))
    (hBlueError :
      4 * (ε1 * Twobites.paperK κ n ^ 2) +
          ε1 * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        (blueError : ℝ))
    (hOpenError : redError + blueError ≤ openError) :
    C.paperSection4OpenPairTargetNat I κ cap - openError ≤ (C.baseOpenPairSet I).card := by
  rcases hHuge with ⟨hHugeRedDiag, hHugeBlueDiag, hHugeBlueCross, hHugeRedCross⟩
  have hRedError' :
      ε1 * Twobites.paperK κ n ^ 2 + ε1 * Twobites.paperK κ n ^ 2 +
          ε1 * Twobites.paperK κ n ^ 2 + ε1 * Twobites.paperK κ n ^ 2 +
          ε1 * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        (redError : ℝ) := by
    nlinarith
  have hBlueError' :
      ε1 * Twobites.paperK κ n ^ 2 + ε1 * Twobites.paperK κ n ^ 2 +
          ε1 * Twobites.paperK κ n ^ 2 + ε1 * Twobites.paperK κ n ^ 2 +
          ε1 * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        (blueError : ℝ) := by
    nlinarith
  exact
    C.paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_splitClosedErrorBounds
      I hindep ht21 ht32 hLarge hMedium hSmall hHugeRedDiag hHugeBlueDiag hHugeRedCross
      hHugeBlueCross hRedError' hBlueError' hOpenError

set_option linter.style.longLine false in
theorem paperSection4OpenPairTarget_sub_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_uniformPaperErrorBounds
    (C : ConstructionData n m) (I : Finset (Fin n))
    {κ ε ε1 : ℝ} {cap : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHuge :
      (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
            ε1 * Twobites.paperK κ n ^ 2) ∧
          (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ)) ∧
            (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
                (1 + ε1) * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ)))
    (hκ : 1 ≤ κ)
    (hε1 : 0 ≤ ε1)
    (hk : 1 ≤ Twobites.paperK κ n) :
    C.paperSection4OpenPairTarget I κ cap - 10 * (ε1 * Twobites.paperK κ n ^ 2) ≤
      ((C.baseOpenPairSet I).card : ℝ) := by
  rcases hHuge with ⟨hHugeRedDiag, hHugeBlueDiag, hHugeBlueCross, hHugeRedCross⟩
  have hκ0 : 0 ≤ κ := by linarith
  have hLMS :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) ≤
        3 * (ε1 * Twobites.paperK κ n ^ 2) := by
    have hLMS' :=
      C.cast_partPairCount_LMS_le_sum_of_thresholds I ht32 hLarge hMedium hSmall
    nlinarith
  have hredBase :
      ((C.redBaseClosedPairSet I).card : ℝ) ≤
        ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) +
          ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) +
          ((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) := by
    exact_mod_cast
      C.redBaseClosedPairSet_card_le_partPairCount_LMS_add_huge_diag_add_huge_cross_of_indep
        I hindep ht21 ht32
  have hblueBase :
      ((C.blueBaseClosedPairSet I).card : ℝ) ≤
        ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) +
          ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) +
          ((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) := by
    exact_mod_cast
      C.blueBaseClosedPairSet_card_le_partPairCount_LMS_add_huge_diag_add_huge_cross_of_indep
        I hindep ht21 ht32
  have hredErrorCore :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) +
          ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        4 * (ε1 * Twobites.paperK κ n ^ 2) := by
    nlinarith [hLMS, hHugeRedDiag]
  have hblueErrorCore :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) +
          ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        4 * (ε1 * Twobites.paperK κ n ^ 2) := by
    nlinarith [hLMS, hHugeBlueDiag]
  have hredClosed :
      ((C.redBaseClosedPairSet I).card : ℝ) ≤
        ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) +
          (4 * (ε1 * Twobites.paperK κ n ^ 2) +
            ε1 * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ)) := by
    nlinarith [hredBase, hredErrorCore, hHugeRedCross]
  have hblueClosed :
      ((C.blueBaseClosedPairSet I).card : ℝ) ≤
        ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) +
          (4 * (ε1 * Twobites.paperK κ n ^ 2) +
            ε1 * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ)) := by
    nlinarith [hblueBase, hblueErrorCore, hHugeBlueCross]
  have hredTarget :
      ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        Twobites.paperK κ n ^ 2 := by
    exact C.paperHugeRedCrossTargetNat_cast_le_paperKSq (I := I) hκ0 hk
  have hblueTarget :
      ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ) ≤
        Twobites.paperK κ n ^ 2 := by
    exact C.paperHugeBlueCrossTargetNat_cast_le_paperKSq (I := I) hκ0 hk
  have hopenError :
      (4 * (ε1 * Twobites.paperK κ n ^ 2) +
            ε1 * ((C.paperHugeRedCrossTargetNat I κ cap : ℕ) : ℝ)) +
          (4 * (ε1 * Twobites.paperK κ n ^ 2) +
            ε1 * ((C.paperHugeBlueCrossTargetNat I κ cap : ℕ) : ℝ)) ≤
        10 * (ε1 * Twobites.paperK κ n ^ 2) := by
    nlinarith
  have htenNonneg : 0 ≤ 10 * (ε1 * Twobites.paperK κ n ^ 2) := by positivity
  exact
    C.paperSection4OpenPairTarget_sub_openError_le_baseOpenPairSet_card_of_swappedClosedRealErrorBounds
      I hredClosed hblueClosed hopenError htenNonneg

set_option linter.style.longLine false in
theorem paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_paperDeterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB : ℝ}
    {mediumWitness smallBound redError blueError openError : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hT1 : 0 ≤ Twobites.paperT1 n)
    (hn : 1 < n)
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 1 ≤ κ)
    (hT2 : 2 < Twobites.paperT2 ε n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hLargeBound :
      (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n +
            (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMediumWitness :
      Twobites.paperKNat κ n < mediumWitness * ⌈Twobites.paperT3 ε n⌉₊ -
        mediumWitness.choose 2 * codegreeBound)
    (hMediumBound :
      (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + mediumWitness.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmallCard : (C.SPart I ε).card ≤ smallBound)
    (hSmallBound :
      (Twobites.paperT3 ε n / 2) *
          (Twobites.paperKNat κ n + smallBound.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hRedError :
      4 * (ε1 * Twobites.paperK κ n ^ 2) +
          ε1 *
            ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) ≤
        (redError : ℝ))
    (hBlueError :
      4 * (ε1 * Twobites.paperK κ n ^ 2) +
          ε1 *
            ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) ≤
        (blueError : ℝ))
    (hOpenError : redError + blueError ≤ openError) :
    C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) - openError ≤
      (C.baseOpenPairSet I).card := by
  have hκ0 : 0 ≤ κ := by linarith
  have hε1 : 0 ≤ ε1 := le_of_lt hε1pos
  have hLargeWitness :
      Twobites.paperKNat κ n <
        Twobites.paperLargeWitnessNat κ ε n * ⌈Twobites.paperT2 ε n⌉₊ -
          (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound := by
    exact
      Twobites.paperKNat_lt_mul_ceil_paperT2_sub_choose_mul_of_two_mul_lt
        (Twobites.two_mul_paperKNat_lt_paperLargeWitnessNat_mul_ceil_paperT2 hκ0 hT2)
        hLChoose
  have hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2 :=
    C.paper_large_deterministic hD I hT1 hI hLargeWitness hLargeBound
  have hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2 :=
    C.paper_medium_deterministic hD I hI hMediumWitness hMediumBound
  have hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2 :=
    C.paper_small_deterministic hD I hI hSmallCard hSmallBound
  have hHuge :
      (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
            ε1 * Twobites.paperK κ n ^ 2) ∧
          (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) :
                  ℝ)) ∧
            (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
                (1 + ε1) *
                  ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) :
                    ℝ)) :=
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale_of_doubleEps_of_kSmall
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ hρR hρB
      hβ hε2 hε1pos hε1le hloglogGap hε1 hdiagScale hcodegScale hsumGap hdegBound
      hchooseCodegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B
      hredCrossSmall
  exact
    C.paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_uniformPaperErrorBounds
      I hindep ht21 ht32 hLarge hMedium hSmall hHuge hRedError hBlueError hOpenError

set_option linter.style.longLine false in
theorem
    paperSection4OpenPairTargetNat_sub_double_ceil_five_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB : ℝ}
    {mediumWitness smallBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hT1 : 0 ≤ Twobites.paperT1 n)
    (hn : 1 < n)
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 1 ≤ κ)
    (hT2 : 2 < Twobites.paperT2 ε n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hLargeBound :
      (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n +
            (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMediumWitness :
      Twobites.paperKNat κ n < mediumWitness * ⌈Twobites.paperT3 ε n⌉₊ -
        mediumWitness.choose 2 * codegreeBound)
    (hMediumBound :
      (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + mediumWitness.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmallCard : (C.SPart I ε).card ≤ smallBound)
    (hSmallBound :
      (Twobites.paperT3 ε n / 2) *
          (Twobites.paperKNat κ n + smallBound.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) -
        2 * ⌈5 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ ≤
      (C.baseOpenPairSet I).card := by
  have hκ0 : 0 ≤ κ := by linarith
  have hloglogOne : 1 ≤ Real.log (Real.log (n : ℝ)) := by
    exact Twobites.one_le_loglog_of_two_div_le_of_le_one hε1pos hε1le hloglogGap
  have hk : 1 ≤ Twobites.paperK κ n := by
    have hT1leK : Twobites.paperT1 n ≤ Twobites.paperK κ n :=
      Twobites.paperT1_le_paperK hloglogOne hκ
    linarith
  have hε1 : 0 ≤ ε1 := le_of_lt hε1pos
  have hRedError :
      4 * (ε1 * Twobites.paperK κ n ^ 2) +
          ε1 *
            ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) ≤
        (⌈5 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ : ℝ) := by
    exact
      four_mul_eps_mul_paperKSq_add_eps_mul_natTarget_le_ceil_five_mul_eps_mul_paperKSq
        hε1 (C.paperHugeRedCrossTargetNat_cast_le_paperKSq (I := I) hκ0 hk)
  have hBlueError :
      4 * (ε1 * Twobites.paperK κ n ^ 2) +
          ε1 *
            ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) : ℝ) ≤
        (⌈5 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ : ℝ) := by
    exact
      four_mul_eps_mul_paperKSq_add_eps_mul_natTarget_le_ceil_five_mul_eps_mul_paperKSq
        hε1 (C.paperHugeBlueCrossTargetNat_cast_le_paperKSq (I := I) hκ0 hk)
  have hOpenError :
      (⌈5 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ : ℕ) +
          ⌈5 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ ≤
        2 * ⌈5 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ := by
    omega
  exact
    C.paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_paperDeterministic
      hD I hindep ht21 ht32 hT1 hn hI hκ hT2 hLChoose hLargeBound hMediumWitness
      hMediumBound hSmallCard hSmallBound hred hblue hblueCap hblueCapWeight hredCap
      hredCapWeight hρR hρB hβ hε2 hε1pos hε1le hloglogGap hdiagScale hcodegScale
      hsumGap hdegBound hchooseCodegBound hcodegBound hgap2R hκ2R hblueCrossSmall
      hgap2B hκ2B hredCrossSmall hRedError hBlueError hOpenError

set_option linter.style.longLine false in
/-- Paper Lemma `lem:RISI`: the deterministic Section 3/4 open-pair target gap in the
manuscript-scale `10 * ε₁ * k²` form, assuming the current paper deterministic bounds for the
large, medium, small, and huge regimes. -/
theorem paperSection4OpenPairTarget_sub_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB : ℝ}
    {mediumWitness smallBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hT1 : 0 ≤ Twobites.paperT1 n)
    (hn : 1 < n)
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 1 ≤ κ)
    (hT2 : 2 < Twobites.paperT2 ε n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hLargeBound :
      (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n +
            (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMediumWitness :
      Twobites.paperKNat κ n < mediumWitness * ⌈Twobites.paperT3 ε n⌉₊ -
        mediumWitness.choose 2 * codegreeBound)
    (hMediumBound :
      (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + mediumWitness.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmallCard : (C.SPart I ε).card ≤ smallBound)
    (hSmallBound :
      (Twobites.paperT3 ε n / 2) *
          (Twobites.paperKNat κ n + smallBound.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    C.paperSection4OpenPairTarget I κ (Twobites.paperCapNat β ε2 n) -
        10 * (ε1 * Twobites.paperK κ n ^ 2) ≤
      ((C.baseOpenPairSet I).card : ℝ) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hloglogOne : 1 ≤ Real.log (Real.log (n : ℝ)) := by
    exact Twobites.one_le_loglog_of_two_div_le_of_le_one hε1pos hε1le hloglogGap
  have hk : 1 ≤ Twobites.paperK κ n := by
    have hT1leK : Twobites.paperT1 n ≤ Twobites.paperK κ n :=
      Twobites.paperT1_le_paperK hloglogOne hκ
    linarith
  have hε1 : 0 ≤ ε1 := le_of_lt hε1pos
  have hLargeWitness :
      Twobites.paperKNat κ n <
        Twobites.paperLargeWitnessNat κ ε n * ⌈Twobites.paperT2 ε n⌉₊ -
          (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound := by
    exact
      Twobites.paperKNat_lt_mul_ceil_paperT2_sub_choose_mul_of_two_mul_lt
        (Twobites.two_mul_paperKNat_lt_paperLargeWitnessNat_mul_ceil_paperT2 hκ0 hT2)
        hLChoose
  have hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2 :=
    C.paper_large_deterministic hD I hT1 hI hLargeWitness hLargeBound
  have hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2 :=
    C.paper_medium_deterministic hD I hI hMediumWitness hMediumBound
  have hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2 :=
    C.paper_small_deterministic hD I hI hSmallCard hSmallBound
  have hHuge :
      (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
            ε1 * Twobites.paperK κ n ^ 2) ∧
          (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) :
                  ℝ)) ∧
            (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
                (1 + ε1) *
                  ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) :
                    ℝ)) :=
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale_of_doubleEps_of_kSmall
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ hρR hρB
      hβ hε2 hε1pos hε1le hloglogGap hε1 hdiagScale hcodegScale hsumGap hdegBound
      hchooseCodegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B
      hredCrossSmall
  exact
    C.paperSection4OpenPairTarget_sub_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_uniformPaperErrorBounds
      I hindep ht21 ht32 hLarge hMedium hSmall hHuge hκ hε1 hk

set_option linter.style.longLine false in
theorem paperSection4OpenPairTargetNat_sub_ceil_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB : ℝ}
    {mediumWitness smallBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hT1 : 0 ≤ Twobites.paperT1 n)
    (hn : 1 < n)
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 1 ≤ κ)
    (hT2 : 2 < Twobites.paperT2 ε n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hLargeBound :
      (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n +
            (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMediumWitness :
      Twobites.paperKNat κ n < mediumWitness * ⌈Twobites.paperT3 ε n⌉₊ -
        mediumWitness.choose 2 * codegreeBound)
    (hMediumBound :
      (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + mediumWitness.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmallCard : (C.SPart I ε).card ≤ smallBound)
    (hSmallBound :
      (Twobites.paperT3 ε n / 2) *
          (Twobites.paperKNat κ n + smallBound.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) -
        ⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ ≤
      (C.baseOpenPairSet I).card := by
  have hreal :=
    C.paperSection4OpenPairTarget_sub_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministic
      hD I hindep ht21 ht32 hT1 hn hI hκ hT2 hLChoose hLargeBound hMediumWitness
      hMediumBound hSmallCard hSmallBound hred hblue hblueCap hblueCapWeight hredCap
      hredCapWeight hρR hρB hβ hε2 hε1pos hε1le hloglogGap hdiagScale hcodegScale
      hsumGap hdegBound hchooseCodegBound hcodegBound hgap2R hκ2R hblueCrossSmall
      hgap2B hκ2B hredCrossSmall
  by_cases
      hle :
        ⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ ≤
          C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n)
  · have hcast :
        (((C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) -
              ⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ : ℕ) : ℝ)) ≤
          ((C.baseOpenPairSet I).card : ℝ) := by
      rw [Nat.cast_sub hle]
      unfold paperSection4OpenPairTarget at hreal
      have hceil :
          10 * (ε1 * Twobites.paperK κ n ^ 2) ≤
            (⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ : ℝ) := by
        exact Nat.le_ceil _
      nlinarith
    exact_mod_cast hcast
  · have hzero :
        C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) -
            ⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ = 0 := by
      exact Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hle))
    simp [hzero]

set_option linter.style.longLine false in
/-- The deterministic Section 4 loss term before the final target-gap subtraction is bounded by
`9 * ε₁ * k²` once the reveal, large, medium, small, and huge diagonal terms are each bounded by
`ε₁ * k²`. This is the manuscript-scale loss package underlying `lem:RISI`. -/
theorem cast_section4LossTarget_le_nine_mul_eps_mul_paperKSq_of_uniformBounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {κ ε ε1 : ℝ}
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hReveal :
      (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
            2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
            C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ)) ≤
      9 * (ε1 * Twobites.paperK κ n ^ 2) := by
  have hLMS :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2 + ε1 * Twobites.paperK κ n ^ 2 +
          ε1 * Twobites.paperK κ n ^ 2 := by
    have hLMS' :=
      C.cast_partPairCount_LMS_le_sum_of_thresholds I ht32 hLarge hMedium hSmall
    nlinarith
  have hCast :
      (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
              2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
              C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
              C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ)) =
        (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) +
          2 * ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) +
          ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) +
          ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) := by
    norm_num
  rw [hCast]
  nlinarith

set_option linter.style.longLine false in
/-- The natural-number version of the `9 * ε₁ * k²` Section 4 loss bound, instantiated from the
current paper deterministic large/medium/small/huge wrappers. -/
theorem section4LossTargetNat_le_ceil_nine_mul_eps_mul_paperKSq_of_paperDeterministic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB : ℝ}
    {mediumWitness smallBound : ℕ}
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hn : 1 < n)
    (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 1 ≤ κ)
    (hT2 : 2 < Twobites.paperT2 ε n)
    (hT1 : 2 < Twobites.paperT1 n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hLargeBound :
      (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n +
            (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMediumWitness :
      Twobites.paperKNat κ n < mediumWitness * ⌈Twobites.paperT3 ε n⌉₊ -
        mediumWitness.choose 2 * codegreeBound)
    (hMediumBound :
      (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + mediumWitness.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmallCard : (C.SPart I ε).card ≤ smallBound)
    (hSmallBound :
      (Twobites.paperT3 ε n / 2) *
          (Twobites.paperKNat κ n + smallBound.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
              (Twobites.paperLargeWitnessNat κ ε n : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
        2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
        C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
      ⌈9 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ := by
  have hκ0 : 0 ≤ κ := by linarith
  have hReveal :
      (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2 := by
    exact
      C.cast_section4RevealBudget_le_eps_mul_paperKSq_of_paperLargeWitness_of_paperHugeWitness
        hD I hn hε hI hκ0 hT2 hT1 hLChoose hHChoose hRevealArith
  have hLargeWitness :
      Twobites.paperKNat κ n <
        Twobites.paperLargeWitnessNat κ ε n * ⌈Twobites.paperT2 ε n⌉₊ -
          (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound := by
    exact
      Twobites.paperKNat_lt_mul_ceil_paperT2_sub_choose_mul_of_two_mul_lt
        (Twobites.two_mul_paperKNat_lt_paperLargeWitnessNat_mul_ceil_paperT2 hκ0 hT2)
        hLChoose
  have hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2 :=
    C.paper_large_deterministic hD I (show 0 ≤ Twobites.paperT1 n by linarith) hI
      hLargeWitness hLargeBound
  have hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2 :=
    C.paper_medium_deterministic hD I hI hMediumWitness hMediumBound
  have hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2 :=
    C.paper_small_deterministic hD I hI hSmallCard hSmallBound
  have hHuge :
      (((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
          ε1 * Twobites.paperK κ n ^ 2) ∧
        (((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
            ε1 * Twobites.paperK κ n ^ 2) ∧
          (((C.blueProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
              (1 + ε1) *
                ((C.paperHugeBlueCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) :
                  ℝ)) ∧
            (((C.redProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
                (1 + ε1) *
                  ((C.paperHugeRedCrossTargetNat I κ (Twobites.paperCapNat β ε2 n) : ℕ) :
                    ℝ)) :=
    C.paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale_of_doubleEps_of_kSmall
      hD I hI hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hκ hρR hρB
      hβ hε2 hε1pos hε1le hloglogGap (le_of_lt hε1pos) hdiagScale hcodegScale hsumGap
      hdegBound hchooseCodegBound hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B
      hredCrossSmall
  rcases hHuge with ⟨hHugeRed, hHugeBlue, _, _⟩
  have hreal :=
    C.cast_section4LossTarget_le_nine_mul_eps_mul_paperKSq_of_uniformBounds
      I ht32 hReveal hLarge hMedium hSmall hHugeRed hHugeBlue
  have hceil :
      ((((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
                2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
                C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
                C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℕ) :
            ℝ)) ≤
        (⌈9 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ : ℝ) := by
    exact hreal.trans (Nat.le_ceil _)
  exact_mod_cast hceil

theorem redOppositeWitnessBiUnion_card_le_redProjectionPairCount (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.redOppositeWitnessBiUnion I A).card ≤
      C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr) := by
  calc
    (C.redOppositeWitnessBiUnion I A).card ≤
        ∑ b ∈ Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A,
          (((C.redProjectionImage I (Sum.inr b)).offDiag.image Sym2.mk).card) := by
      simpa [redOppositeWitnessBiUnion] using
        (Finset.card_biUnion_le
          (s := Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A)
          (t := fun b => (C.redProjectionImage I (Sum.inr b)).offDiag.image Sym2.mk))
    _ = ∑ b ∈ Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A,
          ((C.redProjectionImage I (Sum.inr b)).card).choose 2 := by
      simp [Sym2.card_image_offDiag]
    _ = C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr) := by
      simp [redProjectionPairCount]

theorem blueOppositeWitnessBiUnion_card_le_blueProjectionPairCount (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.blueOppositeWitnessBiUnion I A).card ≤
      C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl) := by
  calc
    (C.blueOppositeWitnessBiUnion I A).card ≤
        ∑ r ∈ Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A,
          (((C.blueProjectionImage I (Sum.inl r)).offDiag.image Sym2.mk).card) := by
      simpa [blueOppositeWitnessBiUnion] using
        (Finset.card_biUnion_le
          (s := Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A)
          (t := fun r => (C.blueProjectionImage I (Sum.inl r)).offDiag.image Sym2.mk))
    _ = ∑ r ∈ Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A,
          ((C.blueProjectionImage I (Sum.inl r)).card).choose 2 := by
      simp [Sym2.card_image_offDiag]
    _ = C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl) := by
      simp [blueProjectionPairCount]

theorem sym2_mk_mem_redOppositeWitnessBiUnion_of_openPairOn_of_openPairPlus_of_not_finalGraph
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {v w : Fin n} (hopen : C.OpenPairOn I A v w) (hopenPlus : C.OpenPairPlus I v w)
    (hnotFinal : ¬ C.finalGraph.Adj v w) (hred : C.redLift.Adj v w) :
    Sym2.mk (C.redProj v, C.redProj w) ∈ C.redOppositeWitnessBiUnion I A := by
  rcases hopen with ⟨hvI, hwI, hvw, hopenA⟩
  rcases hopenPlus with ⟨-, -, -, hopenPlus'⟩
  have hdel : C.redDeleted v w := by
    by_contra hdel
    exact hnotFinal ((C.finalGraph_adj_iff).2 <|
      Or.inl ((C.retainedRed_adj_iff).2 ⟨hred, hdel⟩))
  rcases hdel with ⟨u, hmono | hmixed⟩
  · exact (hopenPlus' (C.closedPairPlus_of_redMonochromaticDeletionWitness hvI hwI hvw hmono)).elim
  · rcases hmixed with ⟨huv, huw, -⟩
    have hnotA : Sum.inr (C.blueProj u) ∉ A := by
      intro hxA
      exact hopenA (C.closedPairOn_of_mem hxA
        ((C.mem_X_blue).2 ⟨hvI, huv⟩)
        ((C.mem_X_blue).2 ⟨hwI, huw⟩) hvw)
    refine Finset.mem_biUnion.2 ⟨C.blueProj u, by simpa using hnotA, ?_⟩
    refine Finset.mem_image.2 ⟨(C.redProj v, C.redProj w), ?_, rfl⟩
    refine Finset.mem_offDiag.2 ⟨?_, ?_, C.redProj_ne_of_redLift_adj hred⟩
    · refine Finset.mem_image.2 ⟨v, (C.mem_X_blue).2 ⟨hvI, huv⟩, rfl⟩
    · refine Finset.mem_image.2 ⟨w, (C.mem_X_blue).2 ⟨hwI, huw⟩, rfl⟩

theorem sym2_mk_mem_blueOppositeWitnessBiUnion_of_openPairOn_of_openPairPlus_of_not_finalGraph
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {v w : Fin n} (hopen : C.OpenPairOn I A v w) (hopenPlus : C.OpenPairPlus I v w)
    (hnotFinal : ¬ C.finalGraph.Adj v w) (hblue : C.blueLift.Adj v w) :
    Sym2.mk (C.blueProj v, C.blueProj w) ∈ C.blueOppositeWitnessBiUnion I A := by
  rcases hopen with ⟨hvI, hwI, hvw, hopenA⟩
  rcases hopenPlus with ⟨-, -, -, hopenPlus'⟩
  have hdel : C.blueDeleted v w := by
    by_contra hdel
    exact hnotFinal ((C.finalGraph_adj_iff).2 <|
      Or.inr ((C.retainedBlue_adj_iff).2 ⟨hblue, hdel⟩))
  rcases hdel with ⟨u, hmono | hmixed⟩
  · exact
      (hopenPlus' (C.closedPairPlus_of_blueMonochromaticDeletionWitness hvI hwI hvw hmono)).elim
  · rcases hmixed with ⟨huv, huw, -⟩
    have hnotA : Sum.inl (C.redProj u) ∉ A := by
      intro hxA
      exact hopenA (C.closedPairOn_of_mem hxA
        ((C.mem_X_red).2 ⟨hvI, huv⟩)
        ((C.mem_X_red).2 ⟨hwI, huw⟩) hvw)
    refine Finset.mem_biUnion.2 ⟨C.redProj u, by simpa using hnotA, ?_⟩
    refine Finset.mem_image.2 ⟨(C.blueProj v, C.blueProj w), ?_, rfl⟩
    refine Finset.mem_offDiag.2 ⟨?_, ?_, C.blueProj_ne_of_blueLift_adj hblue⟩
    · refine Finset.mem_image.2 ⟨v, (C.mem_X_red).2 ⟨hvI, huv⟩, rfl⟩
    · refine Finset.mem_image.2 ⟨w, (C.mem_X_red).2 ⟨hwI, huw⟩, rfl⟩

theorem section4URedCondPairSet_image_sym2_subset_redOppositeWitnessBiUnion_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w) :
    (C.section4URedCondPairSet I A).image Sym2.mk ⊆ C.redOppositeWitnessBiUnion I A := by
  intro z hz
  rcases Finset.mem_image.1 hz with ⟨p, hp, rfl⟩
  rcases p with ⟨r, r'⟩
  rcases (C.mem_section4URedCondPairSet.1 hp) with
    ⟨hpU, v, hvI, w, hwI, hv, hw, hvw, hopen, hopenPlus⟩
  have hredBase : C.redBase.Adj r r' := (C.mem_section4URedPairSet.1 hpU).2
  have hred : C.redLift.Adj v w := by
    rw [C.redLift_adj_iff, hv, hw]
    exact hredBase
  convert
    C.sym2_mk_mem_redOppositeWitnessBiUnion_of_openPairOn_of_openPairPlus_of_not_finalGraph
      hopen hopenPlus (hindep hvI hwI hvw) hred using 1
  · exact Sym2.eq_iff.2 <| Or.inl <| And.intro
      (by simpa [ConstructionData.redProj] using hv.symm)
      (by simpa [ConstructionData.redProj] using hw.symm)

theorem section4UBlueCondPairSet_image_sym2_subset_blueOppositeWitnessBiUnion_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w) :
    (C.section4UBlueCondPairSet I A).image Sym2.mk ⊆ C.blueOppositeWitnessBiUnion I A := by
  intro z hz
  rcases Finset.mem_image.1 hz with ⟨p, hp, rfl⟩
  rcases p with ⟨b, b'⟩
  rcases (C.mem_section4UBlueCondPairSet.1 hp) with
    ⟨hpU, v, hvI, w, hwI, hv, hw, hvw, hopen, hopenPlus⟩
  have hblueBase : C.blueBase.Adj b b' := (C.mem_section4UBluePairSet.1 hpU).2
  have hblue : C.blueLift.Adj v w := by
    rw [C.blueLift_adj_iff, hv, hw]
    exact hblueBase
  convert
    C.sym2_mk_mem_blueOppositeWitnessBiUnion_of_openPairOn_of_openPairPlus_of_not_finalGraph
      hopen hopenPlus (hindep hvI hwI hvw) hblue using 1
  · exact Sym2.eq_iff.2 <| Or.inl <| And.intro
      (by simpa [ConstructionData.blueProj] using hv.symm)
      (by simpa [ConstructionData.blueProj] using hw.symm)

theorem section4URedCondPairSet_card_le_redProjectionPairCount_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w) :
    (C.section4URedCondPairSet I A).card ≤
      C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr) := by
  have hstrict :
      ∀ p ∈ C.section4URedCondPairSet I A, p.1 < p.2 := by
    intro p hp
    have hpU := (C.mem_section4URedCondPairSet.1 hp).1
    have hpT := (C.mem_section4URedPairSet.1 hpU).1
    have hpUn := (C.mem_section4TRedPairSet.1 hpT).1
    exact (C.mem_redBasePairSet.1 ((C.mem_unrevealedRedBasePairSet.1 hpUn).1)).2.2
  calc
    (C.section4URedCondPairSet I A).card =
        ((C.section4URedCondPairSet I A).image Sym2.mk).card := by
      symm
      exact card_image_sym2_mk_of_strictPairSet _ hstrict
    _ ≤ (C.redOppositeWitnessBiUnion I A).card := by
      exact Finset.card_le_card
        (C.section4URedCondPairSet_image_sym2_subset_redOppositeWitnessBiUnion_of_indep hindep)
    _ ≤
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr) :=
      C.redOppositeWitnessBiUnion_card_le_redProjectionPairCount I A

theorem section4UBlueCondPairSet_card_le_blueProjectionPairCount_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w) :
    (C.section4UBlueCondPairSet I A).card ≤
      C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl) := by
  have hstrict :
      ∀ p ∈ C.section4UBlueCondPairSet I A, p.1 < p.2 := by
    intro p hp
    have hpU := (C.mem_section4UBlueCondPairSet.1 hp).1
    have hpT := (C.mem_section4UBluePairSet.1 hpU).1
    have hpUn := (C.mem_section4TBluePairSet.1 hpT).1
    exact (C.mem_blueBasePairSet.1 ((C.mem_unrevealedBlueBasePairSet.1 hpUn).1)).2.2
  calc
    (C.section4UBlueCondPairSet I A).card =
        ((C.section4UBlueCondPairSet I A).image Sym2.mk).card := by
      symm
      exact card_image_sym2_mk_of_strictPairSet _ hstrict
    _ ≤ (C.blueOppositeWitnessBiUnion I A).card := by
      exact Finset.card_le_card
        (C.section4UBlueCondPairSet_image_sym2_subset_blueOppositeWitnessBiUnion_of_indep
          hindep)
    _ ≤
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl) :=
      C.blueOppositeWitnessBiUnion_card_le_blueProjectionPairCount I A

theorem section4URedCondPairSet_image_sym2_card_eq
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} :
    ((C.section4URedCondPairSet I A).image Sym2.mk).card =
      (C.section4URedCondPairSet I A).card := by
  have hstrict :
      ∀ p ∈ C.section4URedCondPairSet I A, p.1 < p.2 := by
    intro p hp
    have hpU := (C.mem_section4URedCondPairSet.1 hp).1
    have hpT := (C.mem_section4URedPairSet.1 hpU).1
    have hpUn := (C.mem_section4TRedPairSet.1 hpT).1
    exact (C.mem_redBasePairSet.1 ((C.mem_unrevealedRedBasePairSet.1 hpUn).1)).2.2
  exact card_image_sym2_mk_of_strictPairSet _ hstrict

theorem section4UBlueCondPairSet_image_sym2_card_eq
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} :
    ((C.section4UBlueCondPairSet I A).image Sym2.mk).card =
      (C.section4UBlueCondPairSet I A).card := by
  have hstrict :
      ∀ p ∈ C.section4UBlueCondPairSet I A, p.1 < p.2 := by
    intro p hp
    have hpU := (C.mem_section4UBlueCondPairSet.1 hp).1
    have hpT := (C.mem_section4UBluePairSet.1 hpU).1
    have hpUn := (C.mem_section4TBluePairSet.1 hpT).1
    exact (C.mem_blueBasePairSet.1 ((C.mem_unrevealedBlueBasePairSet.1 hpUn).1)).2.2
  exact card_image_sym2_mk_of_strictPairSet _ hstrict

theorem section4TRedPairSet_image_sym2_card_eq
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} :
    ((C.section4TRedPairSet I A).image Sym2.mk).card =
      (C.section4TRedPairSet I A).card := by
  have hstrict :
      ∀ p ∈ C.section4TRedPairSet I A, p.1 < p.2 := by
    intro p hp
    have hpUn := (C.mem_section4TRedPairSet.1 hp).1
    exact (C.mem_redBasePairSet.1 ((C.mem_unrevealedRedBasePairSet.1 hpUn).1)).2.2
  exact card_image_sym2_mk_of_strictPairSet _ hstrict

theorem section4TBluePairSet_image_sym2_card_eq
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} :
    ((C.section4TBluePairSet I A).image Sym2.mk).card =
      (C.section4TBluePairSet I A).card := by
  have hstrict :
      ∀ p ∈ C.section4TBluePairSet I A, p.1 < p.2 := by
    intro p hp
    have hpUn := (C.mem_section4TBluePairSet.1 hp).1
    exact (C.mem_blueBasePairSet.1 ((C.mem_unrevealedBlueBasePairSet.1 hpUn).1)).2.2
  exact card_image_sym2_mk_of_strictPairSet _ hstrict

theorem section4URedCondPairSet_image_sym2_subset_section4TRedPairSet_image_sym2
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} :
    (C.section4URedCondPairSet I A).image Sym2.mk ⊆
      (C.section4TRedPairSet I A).image Sym2.mk := by
  intro s hs
  rcases Finset.mem_image.1 hs with ⟨p, hp, rfl⟩
  have hpT : p ∈ C.section4TRedPairSet I A :=
    (C.mem_section4URedPairSet.1 ((C.mem_section4URedCondPairSet.1 hp).1)).1
  exact Finset.mem_image.2 ⟨p, hpT, rfl⟩

theorem section4UBlueCondPairSet_image_sym2_subset_section4TBluePairSet_image_sym2
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} :
    (C.section4UBlueCondPairSet I A).image Sym2.mk ⊆
      (C.section4TBluePairSet I A).image Sym2.mk := by
  intro s hs
  rcases Finset.mem_image.1 hs with ⟨p, hp, rfl⟩
  have hpT : p ∈ C.section4TBluePairSet I A :=
    (C.mem_section4UBluePairSet.1 ((C.mem_section4UBlueCondPairSet.1 hp).1)).1
  exact Finset.mem_image.2 ⟨p, hpT, rfl⟩

@[simp] theorem section4URedChoiceSet_card_eq (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) (uR : ℕ) :
    (C.section4URedChoiceSet I A uR).card = (C.redOppositeWitnessBiUnion I A).card.choose uR := by
  simp [section4URedChoiceSet]

@[simp] theorem section4UBlueChoiceSet_card_eq (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) (uB : ℕ) :
    (C.section4UBlueChoiceSet I A uB).card =
      (C.blueOppositeWitnessBiUnion I A).card.choose uB := by
  simp [section4UBlueChoiceSet]

@[simp] theorem section4UChoiceSet_card_eq (C : ConstructionData n m)
    (I : Finset (Fin n)) (A : Finset (BaseVertex m)) (uR uB : ℕ) :
    (C.section4UChoiceSet I A uR uB).card =
      (C.redOppositeWitnessBiUnion I A).card.choose uR *
        (C.blueOppositeWitnessBiUnion I A).card.choose uB := by
  simp [section4UChoiceSet]

theorem section4URedCondPairSet_image_sym2_mem_section4URedChoiceSet_of_card_eq_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {uR : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (huR : (C.section4URedCondPairSet I A).card = uR) :
    (C.section4URedCondPairSet I A).image Sym2.mk ∈ C.section4URedChoiceSet I A uR := by
  refine Finset.mem_powersetCard.2 ?_
  constructor
  · exact C.section4URedCondPairSet_image_sym2_subset_redOppositeWitnessBiUnion_of_indep hindep
  · rw [C.section4URedCondPairSet_image_sym2_card_eq, huR]

theorem section4UBlueCondPairSet_image_sym2_mem_section4UBlueChoiceSet_of_card_eq_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {uB : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (huB : (C.section4UBlueCondPairSet I A).card = uB) :
    (C.section4UBlueCondPairSet I A).image Sym2.mk ∈ C.section4UBlueChoiceSet I A uB := by
  refine Finset.mem_powersetCard.2 ?_
  constructor
  · exact C.section4UBlueCondPairSet_image_sym2_subset_blueOppositeWitnessBiUnion_of_indep hindep
  · rw [C.section4UBlueCondPairSet_image_sym2_card_eq, huB]

theorem section4UCondPair_images_mem_section4UChoiceSet_of_card_eq_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {uR uB : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (huR : (C.section4URedCondPairSet I A).card = uR)
    (huB : (C.section4UBlueCondPairSet I A).card = uB) :
    ((C.section4URedCondPairSet I A).image Sym2.mk,
        (C.section4UBlueCondPairSet I A).image Sym2.mk) ∈
      C.section4UChoiceSet I A uR uB := by
  simp [section4UChoiceSet,
    C.section4URedCondPairSet_image_sym2_mem_section4URedChoiceSet_of_card_eq_of_indep
      hindep huR,
    C.section4UBlueCondPairSet_image_sym2_mem_section4UBlueChoiceSet_of_card_eq_of_indep
      hindep huB]

@[simp] theorem section4UCondChoiceOutcome_fst_card_eq
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.section4UCondChoiceOutcome I A).1.card = (C.section4URedCondPairSet I A).card := by
  simp [section4UCondChoiceOutcome, C.section4URedCondPairSet_image_sym2_card_eq]

@[simp] theorem section4UCondChoiceOutcome_snd_card_eq
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m)) :
    (C.section4UCondChoiceOutcome I A).2.card = (C.section4UBlueCondPairSet I A).card := by
  simp [section4UCondChoiceOutcome, C.section4UBlueCondPairSet_image_sym2_card_eq]

theorem section4UCondChoiceOutcome_mem_section4UChoiceSet_of_card_eq_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {uR uB : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (huR : (C.section4URedCondPairSet I A).card = uR)
    (huB : (C.section4UBlueCondPairSet I A).card = uB) :
    C.section4UCondChoiceOutcome I A ∈ C.section4UChoiceSet I A uR uB := by
  simpa [section4UCondChoiceOutcome] using
    C.section4UCondPair_images_mem_section4UChoiceSet_of_card_eq_of_indep hindep huR huB

theorem section4UCondChoiceOutcome_mem_section4TChoiceSet_of_card_eq
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {uR uB : ℕ}
    (huR : (C.section4URedCondPairSet I A).card = uR)
    (huB : (C.section4UBlueCondPairSet I A).card = uB) :
    C.section4UCondChoiceOutcome I A ∈ C.section4TChoiceSet I A uR uB := by
  refine Finset.mem_product.2 ?_
  constructor
  · refine Finset.mem_powersetCard.2 ?_
    constructor
    · exact C.section4URedCondPairSet_image_sym2_subset_section4TRedPairSet_image_sym2
    · rw [C.section4UCondChoiceOutcome_fst_card_eq, huR]
  · refine Finset.mem_powersetCard.2 ?_
    constructor
    · exact C.section4UBlueCondPairSet_image_sym2_subset_section4TBluePairSet_image_sym2
    · rw [C.section4UCondChoiceOutcome_snd_card_eq, huB]

theorem section4UCondChoiceEvent_subset_section4TChoiceSet_of_card_eq
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {uR uB : ℕ}
    (huR : (C.section4URedCondPairSet I A).card = uR)
    (huB : (C.section4UBlueCondPairSet I A).card = uB) :
    C.section4UCondChoiceEvent I A uR uB ⊆ C.section4TChoiceSet I A uR uB := by
  intro outcome houtcome
  simp [section4UCondChoiceEvent, huR, huB] at houtcome
  simpa [houtcome] using C.section4UCondChoiceOutcome_mem_section4TChoiceSet_of_card_eq huR huB

theorem section4URedChoiceSet_card_le_choose_redProjectionPairCount
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {uR : ℕ} :
    (C.section4URedChoiceSet I A uR).card ≤
      (C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr)).choose uR := by
  rw [C.section4URedChoiceSet_card_eq]
  exact Nat.choose_le_choose uR (C.redOppositeWitnessBiUnion_card_le_redProjectionPairCount I A)

theorem section4UBlueChoiceSet_card_le_choose_blueProjectionPairCount
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {uB : ℕ} :
    (C.section4UBlueChoiceSet I A uB).card ≤
      (C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl)).choose uB := by
  rw [C.section4UBlueChoiceSet_card_eq]
  exact Nat.choose_le_choose uB
    (C.blueOppositeWitnessBiUnion_card_le_blueProjectionPairCount I A)

theorem section4UChoiceSet_card_le_choose_mul_choose
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {uR uB : ℕ} :
    (C.section4UChoiceSet I A uR uB).card ≤
      (C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr)).choose uR *
        (C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl)).choose uB := by
  rw [C.section4UChoiceSet_card_eq]
  exact Nat.mul_le_mul
    (Nat.choose_le_choose uR (C.redOppositeWitnessBiUnion_card_le_redProjectionPairCount I A))
    (Nat.choose_le_choose uB (C.blueOppositeWitnessBiUnion_card_le_blueProjectionPairCount I A))

theorem one_sub_pow_le_one_sub_pow_of_le {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    (1 - p) ^ n ≤ (1 - p) ^ m := by
  refine pow_le_pow_of_le_one ?_ ?_ hmn
  · linarith
  · linarith

theorem section4ChoiceMass_le_of_choiceBound_of_le_remaining
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {uR uB remaining R B L : ℕ}
    (hchoice : (C.section4UChoiceSet I A uR uB).card ≤ R.choose uR * B.choose uB)
    (hremaining : L ≤ remaining) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    C.section4ChoiceMass I A p uR uB remaining ≤
      ((((R.choose uR : ℕ) : ℝ) * p ^ uR) *
          (((B.choose uB : ℕ) : ℝ) * p ^ uB)) *
        (1 - p) ^ L := by
  have hchoice' :
      ((C.section4UChoiceSet I A uR uB).card : ℝ) ≤
        (((R.choose uR * B.choose uB : ℕ) : ℝ)) := by
    exact_mod_cast hchoice
  have hpow : 0 ≤ p ^ (uR + uB) := pow_nonneg hp0 _
  have hone : 0 ≤ (1 - p) ^ remaining := by
    have hsub : 0 ≤ 1 - p := by linarith
    exact pow_nonneg hsub _
  have hfirst :
      ((C.section4UChoiceSet I A uR uB).card : ℝ) * p ^ (uR + uB) ≤
        (((R.choose uR * B.choose uB : ℕ) : ℝ)) * p ^ (uR + uB) := by
    exact mul_le_mul_of_nonneg_right hchoice' hpow
  have hsecond :
      (1 - p) ^ remaining ≤ (1 - p) ^ L :=
    one_sub_pow_le_one_sub_pow_of_le hp0 hp1 hremaining
  have hbase :
      (((C.section4UChoiceSet I A uR uB).card : ℝ) * p ^ (uR + uB)) * (1 - p) ^ remaining ≤
        ((((R.choose uR * B.choose uB : ℕ) : ℝ)) * p ^ (uR + uB)) * (1 - p) ^ L := by
    exact mul_le_mul hfirst hsecond hone (by positivity)
  calc
    C.section4ChoiceMass I A p uR uB remaining =
        (((C.section4UChoiceSet I A uR uB).card : ℝ) * p ^ (uR + uB)) *
          (1 - p) ^ remaining := by
      simp [section4ChoiceMass, section4BernoulliMass, mul_assoc]
    _ ≤ ((((R.choose uR * B.choose uB : ℕ) : ℝ)) * p ^ (uR + uB)) *
          (1 - p) ^ L := hbase
    _ =
        ((((R.choose uR : ℕ) : ℝ) * p ^ uR) *
            (((B.choose uB : ℕ) : ℝ) * p ^ uB)) *
          (1 - p) ^ L := by
      rw [pow_add, Nat.cast_mul]
      ring

theorem section4BernoulliMass_eq_of_mem_section4UChoiceSet
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {uR uB remaining : ℕ}
    {outcome : Finset (Sym2 (Fin m)) × Finset (Sym2 (Fin m))}
    (houtcome : outcome ∈ C.section4UChoiceSet I A uR uB) :
    section4BernoulliMass p outcome.1.card outcome.2.card remaining =
      section4BernoulliMass p uR uB remaining := by
  rcases Finset.mem_product.1 houtcome with ⟨hR, hB⟩
  have hRc : outcome.1.card = uR := (Finset.mem_powersetCard.1 hR).2
  have hBc : outcome.2.card = uB := (Finset.mem_powersetCard.1 hB).2
  simp [section4BernoulliMass, hRc, hBc]

theorem section4ChoiceEventMass_eq_section4ChoiceMass
    (C : ConstructionData n m) (I : Finset (Fin n)) (A : Finset (BaseVertex m))
    (p : ℝ) (uR uB remaining : ℕ) :
    C.section4ChoiceEventMass I A p uR uB remaining =
      C.section4ChoiceMass I A p uR uB remaining := by
  classical
  unfold section4ChoiceEventMass
  calc
    Finset.sum (C.section4UChoiceSet I A uR uB) (fun outcome =>
        section4BernoulliMass p outcome.1.card outcome.2.card remaining) =
      Finset.sum (C.section4UChoiceSet I A uR uB) (fun _outcome =>
        section4BernoulliMass p uR uB remaining) := by
        refine Finset.sum_congr rfl ?_
        intro outcome houtcome
        exact C.section4BernoulliMass_eq_of_mem_section4UChoiceSet houtcome
    _ = ((C.section4UChoiceSet I A uR uB).card : ℝ) *
          section4BernoulliMass p uR uB remaining := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = C.section4ChoiceMass I A p uR uB remaining := by
        simp [section4ChoiceMass]

theorem section4ChoiceEventMass_le_projectionChoiceMass
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {uR uB remaining : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    C.section4ChoiceEventMass I A p uR uB remaining ≤
      ((((C.redProjectionPairCount I
              ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr)).choose uR :
            ℝ) *
          p ^ uR) *
        (((C.blueProjectionPairCount I
              ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl)).choose uB :
            ℝ) *
          p ^ uB)) *
        (1 - p) ^ remaining := by
  rw [C.section4ChoiceEventMass_eq_section4ChoiceMass]
  exact
    C.section4ChoiceMass_le_of_choiceBound_of_le_remaining
      (C.section4UChoiceSet_card_le_choose_mul_choose (I := I) (A := A)) (le_rfl) hp0 hp1

theorem section4ChoiceEventMassSum_le_projectionChoiceMassSum
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {remaining : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    C.section4ChoiceEventMassSum I A p remaining
        (C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr))
        (C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl)) ≤
      section4ProjectionChoiceMassSum p remaining
        (C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr))
        (C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl)) := by
  unfold section4ChoiceEventMassSum section4ProjectionChoiceMassSum
  exact Finset.sum_le_sum fun uv : ℕ × ℕ => fun _ =>
    C.section4ChoiceEventMass_le_projectionChoiceMass
      (I := I) (A := A) (remaining := remaining) (uR := uv.1) (uB := uv.2) hp0 hp1

theorem section4ProjectionChoiceMassSum_eq_closedForm
    (p : ℝ) (remaining uRMax uBMax : ℕ) :
    section4ProjectionChoiceMassSum p remaining uRMax uBMax =
      ((1 + p) ^ uRMax) * ((1 + p) ^ uBMax) * (1 - p) ^ remaining := by
  let f : ℕ → ℝ := fun uR => ((uRMax.choose uR : ℕ) : ℝ) * p ^ uR
  let g : ℕ → ℝ := fun uB => ((uBMax.choose uB : ℕ) : ℝ) * p ^ uB
  let c : ℝ := (1 - p) ^ remaining
  have hR :
      Finset.sum (Finset.range (uRMax + 1)) f = (1 + p) ^ uRMax := by
    calc
      Finset.sum (Finset.range (uRMax + 1)) f =
          Finset.sum (Finset.range (uRMax + 1))
            (fun uR => p ^ uR * 1 ^ (uRMax - uR) * ((uRMax.choose uR : ℕ) : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro uR huR
          simp [f]
          ring
      _ = (p + 1) ^ uRMax := by
          simpa [add_comm] using (add_pow p (1 : ℝ) uRMax).symm
      _ = (1 + p) ^ uRMax := by rw [add_comm]
  have hB :
      Finset.sum (Finset.range (uBMax + 1)) g = (1 + p) ^ uBMax := by
    calc
      Finset.sum (Finset.range (uBMax + 1)) g =
          Finset.sum (Finset.range (uBMax + 1))
            (fun uB => p ^ uB * 1 ^ (uBMax - uB) * ((uBMax.choose uB : ℕ) : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro uB huB
          simp [g]
          ring
      _ = (p + 1) ^ uBMax := by
          simpa [add_comm] using (add_pow p (1 : ℝ) uBMax).symm
      _ = (1 + p) ^ uBMax := by rw [add_comm]
  calc
    section4ProjectionChoiceMassSum p remaining uRMax uBMax =
        Finset.sum (Finset.range (uRMax + 1))
          (fun uR =>
            Finset.sum (Finset.range (uBMax + 1)) fun uB => (f uR * g uB) * c) := by
      unfold section4ProjectionChoiceMassSum section4CountIndexSet
      rw [Finset.sum_product]
    _ = (Finset.sum (Finset.range (uRMax + 1)) f) *
          (Finset.sum (Finset.range (uBMax + 1)) g) * c := by
      calc
        Finset.sum (Finset.range (uRMax + 1))
            (fun uR =>
              Finset.sum (Finset.range (uBMax + 1)) fun uB => (f uR * g uB) * c) =
            Finset.sum (Finset.range (uRMax + 1))
              (fun uR => f uR * Finset.sum (Finset.range (uBMax + 1)) (fun uB => g uB * c)) := by
          refine Finset.sum_congr rfl ?_
          intro uR huR
          calc
            Finset.sum (Finset.range (uBMax + 1)) (fun uB => (f uR * g uB) * c) =
                Finset.sum (Finset.range (uBMax + 1)) (fun uB => f uR * (g uB * c)) := by
              refine Finset.sum_congr rfl ?_
              intro uB huB
              ring
            _ = f uR * Finset.sum (Finset.range (uBMax + 1)) (fun uB => g uB * c) := by
              rw [Finset.mul_sum]
        _ = Finset.sum (Finset.range (uRMax + 1))
              (fun uR => f uR * (Finset.sum (Finset.range (uBMax + 1)) g * c)) := by
          refine Finset.sum_congr rfl ?_
          intro uR huR
          rw [Finset.sum_mul]
        _ = Finset.sum (Finset.range (uRMax + 1)) f *
              (Finset.sum (Finset.range (uBMax + 1)) g * c) := by
          rw [← Finset.sum_mul]
        _ = Finset.sum (Finset.range (uRMax + 1)) f *
              Finset.sum (Finset.range (uBMax + 1)) g * c := by
          ring
    _ = ((1 + p) ^ uRMax) * ((1 + p) ^ uBMax) * (1 - p) ^ remaining := by
      simp [hR, hB, c]

theorem section4ProjectionChoiceMassSum_le_exp
    {p : ℝ} {remaining uRMax uBMax : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    section4ProjectionChoiceMassSum p remaining uRMax uBMax ≤
      Real.exp (p * (uRMax : ℝ) + p * (uBMax : ℝ) - p * (remaining : ℝ)) := by
  have honep_nonneg : 0 ≤ 1 + p := by linarith
  have hsub_nonneg : 0 ≤ 1 - p := by linarith
  have hR :
      (1 + p) ^ uRMax ≤ Real.exp (p * (uRMax : ℝ)) := by
    have hbase : 1 + p ≤ Real.exp p := by simpa [add_comm] using Real.add_one_le_exp p
    calc
      (1 + p) ^ uRMax ≤ (Real.exp p) ^ uRMax := pow_le_pow_left₀ honep_nonneg hbase _
      _ = Real.exp (p * (uRMax : ℝ)) := by
        rw [← Real.exp_nat_mul]
        ring_nf
  have hB :
      (1 + p) ^ uBMax ≤ Real.exp (p * (uBMax : ℝ)) := by
    have hbase : 1 + p ≤ Real.exp p := by simpa [add_comm] using Real.add_one_le_exp p
    calc
      (1 + p) ^ uBMax ≤ (Real.exp p) ^ uBMax := pow_le_pow_left₀ honep_nonneg hbase _
      _ = Real.exp (p * (uBMax : ℝ)) := by
        rw [← Real.exp_nat_mul]
        ring_nf
  have hremaining :
      (1 - p) ^ remaining ≤ Real.exp (-p * (remaining : ℝ)) := by
    calc
      (1 - p) ^ remaining ≤ (Real.exp (-p)) ^ remaining := by
        exact pow_le_pow_left₀ hsub_nonneg (Real.one_sub_le_exp_neg p) _
      _ = Real.exp ((remaining : ℝ) * (-p)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (-p * (remaining : ℝ)) := by ring_nf
  have hpair :
      ((1 + p) ^ uRMax) * ((1 + p) ^ uBMax) ≤
        Real.exp (p * (uRMax : ℝ)) * Real.exp (p * (uBMax : ℝ)) := by
    exact
      (mul_le_mul_of_nonneg_right hR (pow_nonneg honep_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hB (by positivity))
  have htriple :
      (((1 + p) ^ uRMax) * ((1 + p) ^ uBMax)) * (1 - p) ^ remaining ≤
        (Real.exp (p * (uRMax : ℝ)) * Real.exp (p * (uBMax : ℝ))) *
          Real.exp (-p * (remaining : ℝ)) := by
    exact
      (mul_le_mul_of_nonneg_right hpair (pow_nonneg hsub_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hremaining (by positivity))
  calc
    section4ProjectionChoiceMassSum p remaining uRMax uBMax =
        (((1 + p) ^ uRMax) * ((1 + p) ^ uBMax)) * (1 - p) ^ remaining := by
      simpa [mul_assoc] using
        (section4ProjectionChoiceMassSum_eq_closedForm p remaining uRMax uBMax)
    _ ≤ (Real.exp (p * (uRMax : ℝ)) * Real.exp (p * (uBMax : ℝ))) *
          Real.exp (-p * (remaining : ℝ)) := htriple
    _ = Real.exp (p * (uRMax : ℝ) + p * (uBMax : ℝ) - p * (remaining : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem section4BernoulliMass_nonneg {p : ℝ} {uR uB remaining : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ section4BernoulliMass p uR uB remaining := by
  unfold section4BernoulliMass
  have hsub : 0 ≤ 1 - p := by linarith
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hsub _)

theorem section4ChoiceEventMass_nonneg
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {uR uB remaining : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ C.section4ChoiceEventMass I A p uR uB remaining := by
  unfold section4ChoiceEventMass
  exact Finset.sum_nonneg fun _ _ => section4BernoulliMass_nonneg hp0 hp1

theorem section4UCondChoiceEventMass_eq_bernoulliMass_of_card_eq
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {uR uB remaining : ℕ}
    (huR : (C.section4URedCondPairSet I A).card = uR)
    (huB : (C.section4UBlueCondPairSet I A).card = uB) :
    C.section4UCondChoiceEventMass I A p uR uB remaining =
      section4BernoulliMass p uR uB remaining := by
  simp [section4UCondChoiceEventMass, section4SecondStageEventMass,
    section4UCondChoiceEvent, huR, huB]

theorem section4UCondChoiceEventMass_eq_zero_of_not_card_eq
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {uR uB remaining : ℕ}
    (hcount :
      ¬ ((C.section4URedCondPairSet I A).card = uR ∧
        (C.section4UBlueCondPairSet I A).card = uB)) :
    C.section4UCondChoiceEventMass I A p uR uB remaining = 0 := by
  simp [section4UCondChoiceEventMass, section4SecondStageEventMass,
    section4UCondChoiceEvent, hcount]

theorem section4BernoulliMass_antitone_remaining {p : ℝ} {uR uB remaining₁ remaining₂ : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hremaining : remaining₁ ≤ remaining₂) :
    section4BernoulliMass p uR uB remaining₂ ≤
      section4BernoulliMass p uR uB remaining₁ := by
  unfold section4BernoulliMass
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · exact one_sub_pow_le_one_sub_pow_of_le hp0 hp1 hremaining
  · exact pow_nonneg hp0 _

theorem section4ActualConditionedEventMass_antitone
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p : ℝ} {N₁ N₂ : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : N₁ ≤ N₂) :
    C.section4ActualConditionedEventMass I ε p N₂ ≤
      C.section4ActualConditionedEventMass I ε p N₁ := by
  let uRActual := (C.section4URedCondPairSet I (C.section4F I ε)).card
  let uBActual := (C.section4UBlueCondPairSet I (C.section4F I ε)).card
  let loss := C.section4SecondStageLossNat I ε
  have hremaining : N₁ - loss ≤ N₂ - loss := Nat.sub_le_sub_right hN loss
  have hmass :=
    section4BernoulliMass_antitone_remaining (uR := uRActual) (uB := uBActual)
      hp0 hp1 hremaining
  have huR : (C.section4URedCondPairSet I (C.section4F I ε)).card = uRActual := rfl
  have huB : (C.section4UBlueCondPairSet I (C.section4F I ε)).card = uBActual := rfl
  calc
    C.section4ActualConditionedEventMass I ε p N₂ =
        section4BernoulliMass p uRActual uBActual (N₂ - loss) := by
      unfold section4ActualConditionedEventMass
      simp [uRActual, uBActual, loss,
        C.section4UCondChoiceEventMass_eq_bernoulliMass_of_card_eq
          (A := C.section4F I ε) (uR := uRActual) (uB := uBActual) huR huB]
    _ ≤ section4BernoulliMass p uRActual uBActual (N₁ - loss) := hmass
    _ = C.section4ActualConditionedEventMass I ε p N₁ := by
      unfold section4ActualConditionedEventMass
      simp [uRActual, uBActual, loss,
        C.section4UCondChoiceEventMass_eq_bernoulliMass_of_card_eq
          (A := C.section4F I ε) (uR := uRActual) (uB := uBActual) huR huB]

theorem section4UCondChoiceEventMass_le_section4ChoiceEventMass_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {uR uB remaining : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    C.section4UCondChoiceEventMass I A p uR uB remaining ≤
      C.section4ChoiceEventMass I A p uR uB remaining := by
  by_cases hcount :
      (C.section4URedCondPairSet I A).card = uR ∧
        (C.section4UBlueCondPairSet I A).card = uB
  · rcases hcount with ⟨huR, huB⟩
    have hmem :
        C.section4UCondChoiceOutcome I A ∈ C.section4UChoiceSet I A uR uB :=
      C.section4UCondChoiceOutcome_mem_section4UChoiceSet_of_card_eq_of_indep hindep huR huB
    have hsingle' :
        section4BernoulliMass p
            (C.section4UCondChoiceOutcome I A).1.card
            (C.section4UCondChoiceOutcome I A).2.card remaining ≤
          C.section4ChoiceEventMass I A p uR uB remaining := by
      unfold section4ChoiceEventMass
      simpa using
        (Finset.single_le_sum
          (f := fun outcome =>
            section4BernoulliMass p outcome.1.card outcome.2.card remaining)
          (fun _ _ => section4BernoulliMass_nonneg hp0 hp1) hmem)
    have hsingle :
        section4BernoulliMass p uR uB remaining ≤
          C.section4ChoiceEventMass I A p uR uB remaining := by
      calc
        section4BernoulliMass p uR uB remaining =
            section4BernoulliMass p
              (C.section4URedCondPairSet I A).card
              (C.section4UBlueCondPairSet I A).card remaining := by
          simp [huR, huB]
        _ = section4BernoulliMass p
              (C.section4UCondChoiceOutcome I A).1.card
              (C.section4UCondChoiceOutcome I A).2.card remaining := by
          unfold section4UCondChoiceOutcome
          rw [C.section4URedCondPairSet_image_sym2_card_eq,
            C.section4UBlueCondPairSet_image_sym2_card_eq]
        _ ≤ C.section4ChoiceEventMass I A p uR uB remaining := hsingle'
    rw [C.section4UCondChoiceEventMass_eq_bernoulliMass_of_card_eq huR huB]
    exact hsingle
  · rw [C.section4UCondChoiceEventMass_eq_zero_of_not_card_eq hcount]
    exact C.section4ChoiceEventMass_nonneg hp0 hp1

theorem section4UCondChoiceEventMassSum_eq_section4UCondChoiceEventMass_of_card_le
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {remaining uRMax uBMax : ℕ}
    (hUR : (C.section4URedCondPairSet I A).card ≤ uRMax)
    (hUB : (C.section4UBlueCondPairSet I A).card ≤ uBMax) :
    C.section4UCondChoiceEventMassSum I A p remaining uRMax uBMax =
      C.section4UCondChoiceEventMass I A p
        (C.section4URedCondPairSet I A).card
        (C.section4UBlueCondPairSet I A).card remaining := by
  let uv0 : ℕ × ℕ :=
    ((C.section4URedCondPairSet I A).card, (C.section4UBlueCondPairSet I A).card)
  have hmem : uv0 ∈ section4CountIndexSet uRMax uBMax := by
    refine Finset.mem_product.2 ?_
    exact ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hUR),
      Finset.mem_range.2 (Nat.lt_succ_of_le hUB)⟩
  unfold section4UCondChoiceEventMassSum
  calc
    Finset.sum (section4CountIndexSet uRMax uBMax) (fun uv =>
        C.section4UCondChoiceEventMass I A p uv.1 uv.2 remaining) =
      C.section4UCondChoiceEventMass I A p uv0.1 uv0.2 remaining := by
        apply Finset.sum_eq_single uv0
        · intro uv huv hne
          have hcount :
              ¬ ((C.section4URedCondPairSet I A).card = uv.1 ∧
                (C.section4UBlueCondPairSet I A).card = uv.2) := by
            intro huv0
            apply hne
            rcases uv with ⟨uR, uB⟩
            rcases huv0 with ⟨huR, huB⟩
            simp [uv0, huR, huB]
          exact C.section4UCondChoiceEventMass_eq_zero_of_not_card_eq
            (I := I) (A := A) (p := p) (uR := uv.1) (uB := uv.2)
            (remaining := remaining) hcount
        · intro hnotmem
          exact (hnotmem hmem).elim
    _ = C.section4UCondChoiceEventMass I A p
          (C.section4URedCondPairSet I A).card
          (C.section4UBlueCondPairSet I A).card remaining := by
        simp [uv0]

theorem section4UCondChoiceEventMassSum_eq_bernoulliMass_of_card_le
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {remaining uRMax uBMax : ℕ}
    (hUR : (C.section4URedCondPairSet I A).card ≤ uRMax)
    (hUB : (C.section4UBlueCondPairSet I A).card ≤ uBMax) :
    C.section4UCondChoiceEventMassSum I A p remaining uRMax uBMax =
      section4BernoulliMass p
        (C.section4URedCondPairSet I A).card
        (C.section4UBlueCondPairSet I A).card remaining := by
  rw [C.section4UCondChoiceEventMassSum_eq_section4UCondChoiceEventMass_of_card_le hUR hUB]
  exact C.section4UCondChoiceEventMass_eq_bernoulliMass_of_card_eq rfl rfl

theorem section4UCondChoiceEventMassSum_le_section4ChoiceEventMassSum_of_indep
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)}
    {p : ℝ} {remaining uRMax uBMax : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    C.section4UCondChoiceEventMassSum I A p remaining uRMax uBMax ≤
      C.section4ChoiceEventMassSum I A p remaining uRMax uBMax := by
  unfold section4UCondChoiceEventMassSum section4ChoiceEventMassSum
  exact Finset.sum_le_sum fun uv : ℕ × ℕ => fun _ =>
    C.section4UCondChoiceEventMass_le_section4ChoiceEventMass_of_indep
      (I := I) (A := A) (p := p) (uR := uv.1) (uB := uv.2)
      (remaining := remaining) hindep hp0 hp1

set_option linter.style.longLine false in
theorem
    section4TPairSet_lower_bound_sub_oppositeProjectionCounts_of_indep_le_section4TRemainingPairSet
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {N : ℕ}
    (hT : N ≤ (C.section4TPairSet I A).card)
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w) :
    N -
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr) -
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl) ≤
      (C.section4TRemainingPairSet I A).card := by
  exact
    C.section4TPairSet_lower_bound_sub_condCounts_le_section4TRemainingPairSet I A hT
      (C.section4URedCondPairSet_card_le_redProjectionPairCount_of_indep hindep)
      (C.section4UBlueCondPairSet_card_le_blueProjectionPairCount_of_indep hindep)

set_option linter.style.longLine false in
theorem
    section4TPairSet_lower_bound_sub_oppositeProjectionCounts_of_indep_le_card_sub_uR_sub_uB
    (C : ConstructionData n m) {I : Finset (Fin n)} {A : Finset (BaseVertex m)} {N uR uB : ℕ}
    (hT : N ≤ (C.section4TPairSet I A).card)
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (huR : (C.section4URedCondPairSet I A).card = uR)
    (huB : (C.section4UBlueCondPairSet I A).card = uB) :
    N -
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ A).image Sum.inr) -
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ A).image Sum.inl) ≤
      (C.section4TPairSet I A).card - uR - uB := by
  have hbase :=
    C.section4TPairSet_lower_bound_sub_oppositeProjectionCounts_of_indep_le_section4TRemainingPairSet
      hT hindep
  rw [C.section4TRemainingPairSet_card_eq_of_card_eq_condCounts I A huR huB] at hbase
  exact hbase

set_option linter.style.longLine false in
theorem
    openPair_lower_bound_sub_section4_budget_sub_projectionPairCount_sum_sub_oppositeProjectionCounts_le_section4TRemainingPairSet
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ} {N : ℕ}
    (hopen : N ≤ (C.baseOpenPairSet I).card)
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w) :
    N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
        (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
      (C.section4TRemainingPairSet I (C.section4F I ε)).card := by
  exact
    C.section4TPairSet_lower_bound_sub_oppositeProjectionCounts_of_indep_le_section4TRemainingPairSet
      (A := C.section4F I ε)
      (C.openPair_lower_bound_sub_section4_budget_sub_projectionPairCount_sum_le_section4TPairSet
        I hopen)
      hindep

set_option linter.style.longLine false in
theorem
    openPair_lower_bound_sub_section4_budget_sub_projectionPairCount_sum_sub_oppositeProjectionCounts_le_card_sub_uR_sub_uB
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε : ℝ} {N uR uB : ℕ}
    (hopen : N ≤ (C.baseOpenPairSet I).card)
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (huR : (C.section4URedCondPairSet I (C.section4F I ε)).card = uR)
    (huB : (C.section4UBlueCondPairSet I (C.section4F I ε)).card = uB) :
    N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
        (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
      (C.section4TPairSet I (C.section4F I ε)).card - uR - uB := by
  exact
    C.section4TPairSet_lower_bound_sub_oppositeProjectionCounts_of_indep_le_card_sub_uR_sub_uB
      (A := C.section4F I ε)
      (C.openPair_lower_bound_sub_section4_budget_sub_projectionPairCount_sum_le_section4TPairSet
        I hopen)
      hindep huR huB

set_option linter.style.longLine false in
theorem
    openPair_lower_bound_sub_section4_budget_sub_projectionPairCount_sum_sub_oppositeProjectionCounts_le_section4ChoiceMass
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p : ℝ} {N uR uB : ℕ}
    (hopen : N ≤ (C.baseOpenPairSet I).card)
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (huR : (C.section4URedCondPairSet I (C.section4F I ε)).card = uR)
    (huB : (C.section4UBlueCondPairSet I (C.section4F I ε)).card = uB)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    C.section4ChoiceMass I (C.section4F I ε) p uR uB
        ((C.section4TRemainingPairSet I (C.section4F I ε)).card) ≤
      ((((C.redProjectionPairCount I
              ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr)).choose uR :
            ℝ) *
          p ^ uR) *
        (((C.blueProjectionPairCount I
              ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)).choose uB :
            ℝ) *
          p ^ uB)) *
        (1 - p) ^
          (N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
            (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
              C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
            C.redProjectionPairCount I
              ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
            C.blueProjectionPairCount I
              ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)) := by
  have hchoice :
      (C.section4UChoiceSet I (C.section4F I ε) uR uB).card ≤
        (C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr)).choose uR *
          (C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)).choose uB :=
    C.section4UChoiceSet_card_le_choose_mul_choose
      (I := I) (A := C.section4F I ε)
  have hremaining :
      N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
        (C.section4TRemainingPairSet I (C.section4F I ε)).card := by
    have hbase :=
      C.openPair_lower_bound_sub_section4_budget_sub_projectionPairCount_sum_sub_oppositeProjectionCounts_le_card_sub_uR_sub_uB
        I hopen hindep huR huB
    calc
      N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
              (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
                C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
            C.redProjectionPairCount I
              ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
          (C.section4TPairSet I (C.section4F I ε)).card - uR - uB := hbase
      _ = (C.section4TRemainingPairSet I (C.section4F I ε)).card := by
        symm
        exact C.section4TRemainingPairSet_card_eq_of_card_eq_condCounts
          I (C.section4F I ε) huR huB
  exact
    C.section4ChoiceMass_le_of_choiceBound_of_le_remaining hchoice hremaining hp0 hp1

set_option linter.style.longLine false in
theorem
    section4ChoiceEventMassSum_section4F_le_projectionChoiceMassSum
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p : ℝ} {N : ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    C.section4ChoiceEventMassSum I (C.section4F I ε) p
        (N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl))
        (C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr))
        (C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)) ≤
      section4ProjectionChoiceMassSum p
        (N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl))
        (C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr))
        (C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)) := by
  exact
    C.section4ChoiceEventMassSum_le_projectionChoiceMassSum
      (I := I) (A := C.section4F I ε) hp0 hp1

set_option linter.style.longLine false in
theorem
    section4UCondChoiceEventMassSum_section4F_le_projectionChoiceMassSum_of_indep
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p : ℝ} {N : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    C.section4UCondChoiceEventMassSum I (C.section4F I ε) p
        (N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl))
        (C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr))
        (C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)) ≤
      section4ProjectionChoiceMassSum p
        (N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl))
        (C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr))
        (C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)) := by
  calc
    C.section4UCondChoiceEventMassSum I (C.section4F I ε) p
        (N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl))
        (C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr))
        (C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)) ≤
      C.section4ChoiceEventMassSum I (C.section4F I ε) p
        (N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl))
        (C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr))
        (C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)) := by
      exact
        C.section4UCondChoiceEventMassSum_le_section4ChoiceEventMassSum_of_indep
          (I := I) (A := C.section4F I ε) hindep hp0 hp1
    _ ≤ section4ProjectionChoiceMassSum p
        (N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl))
        (C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr))
        (C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)) := by
      exact C.section4ChoiceEventMassSum_section4F_le_projectionChoiceMassSum
        (I := I) (ε := ε) (N := N) hp0 hp1

set_option linter.style.longLine false in
theorem
    section4UCondChoiceEventMassSum_section4F_le_exp_of_indep
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p : ℝ} {N : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let remainingNat :=
      N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
        (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
    let uRNat :=
      C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr)
    let uBNat :=
      C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
    C.section4UCondChoiceEventMassSum I (C.section4F I ε) p remainingNat uRNat uBNat ≤
      Real.exp (p * (uRNat : ℝ) + p * (uBNat : ℝ) - p * (remainingNat : ℝ)) := by
  let remainingNat :=
    N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
      (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
      C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
      C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
  let uRNat :=
    C.redProjectionPairCount I
      ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr)
  let uBNat :=
    C.blueProjectionPairCount I
      ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
  change
    C.section4UCondChoiceEventMassSum I (C.section4F I ε) p remainingNat uRNat uBNat ≤
      Real.exp (p * (uRNat : ℝ) + p * (uBNat : ℝ) - p * (remainingNat : ℝ))
  calc
    C.section4UCondChoiceEventMassSum I (C.section4F I ε) p remainingNat uRNat uBNat ≤
      section4ProjectionChoiceMassSum p remainingNat uRNat uBNat := by
      exact C.section4UCondChoiceEventMassSum_section4F_le_projectionChoiceMassSum_of_indep
        (I := I) (ε := ε) (N := N) hindep hp0 hp1
    _ ≤ Real.exp (p * (uRNat : ℝ) + p * (uBNat : ℝ) - p * (remainingNat : ℝ)) := by
      exact section4ProjectionChoiceMassSum_le_exp
        (p := p) (remaining := remainingNat) (uRMax := uRNat) (uBMax := uBNat) hp0 hp1

set_option linter.style.longLine false in
theorem
    section4UCondChoiceEventMassSum_section4F_le_exp_of_indep_of_bounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p : ℝ} {N : ℕ}
    {remainingBound uRBound uBBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hRemaining :
      remainingBound ≤
        N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl))
    (hUR :
      C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) ≤
        uRBound)
    (hUB :
      C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
        uBBound) :
    let remainingNat :=
      N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
        (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
    let uRNat :=
      C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr)
    let uBNat :=
      C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
    C.section4UCondChoiceEventMassSum I (C.section4F I ε) p remainingNat uRNat uBNat ≤
      Real.exp (p * (uRBound : ℝ) + p * (uBBound : ℝ) - p * (remainingBound : ℝ)) := by
  let remainingNat :=
    N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
      (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
      C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
      C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
  let uRNat :=
    C.redProjectionPairCount I
      ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr)
  let uBNat :=
    C.blueProjectionPairCount I
      ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
  change
    C.section4UCondChoiceEventMassSum I (C.section4F I ε) p remainingNat uRNat uBNat ≤
      Real.exp (p * (uRBound : ℝ) + p * (uBBound : ℝ) - p * (remainingBound : ℝ))
  refine
    (C.section4UCondChoiceEventMassSum_section4F_le_exp_of_indep
      (I := I) (ε := ε) (p := p) (N := N) hindep hp0 hp1).trans ?_
  apply Real.exp_le_exp.mpr
  have hRemainingR : (remainingBound : ℝ) ≤ remainingNat := by exact_mod_cast hRemaining
  have hURR : (uRNat : ℝ) ≤ uRBound := by exact_mod_cast hUR
  have hUBR : (uBNat : ℝ) ≤ uBBound := by exact_mod_cast hUB
  nlinarith

set_option linter.style.longLine false in
theorem
    section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_bounds
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p : ℝ} {N : ℕ}
    {remainingBound uRBound uBBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hRemaining :
      remainingBound ≤
        N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl))
    (hUR :
      C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) ≤
        uRBound)
    (hUB :
      C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
        uBBound) :
    let remainingNat :=
      N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
        (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
    let uRActual := (C.section4URedCondPairSet I (C.section4F I ε)).card
    let uBActual := (C.section4UBlueCondPairSet I (C.section4F I ε)).card
    C.section4UCondChoiceEventMass I (C.section4F I ε) p uRActual uBActual remainingNat ≤
      Real.exp (p * (uRBound : ℝ) + p * (uBBound : ℝ) - p * (remainingBound : ℝ)) := by
  let remainingNat :=
    N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
      (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
      C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
      C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
  let uRNat :=
    C.redProjectionPairCount I
      ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr)
  let uBNat :=
    C.blueProjectionPairCount I
      ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
  let uRActual := (C.section4URedCondPairSet I (C.section4F I ε)).card
  let uBActual := (C.section4UBlueCondPairSet I (C.section4F I ε)).card
  change
    C.section4UCondChoiceEventMass I (C.section4F I ε) p uRActual uBActual remainingNat ≤
      Real.exp (p * (uRBound : ℝ) + p * (uBBound : ℝ) - p * (remainingBound : ℝ))
  have hURactual : uRActual ≤ uRNat := by
    simpa [uRActual, uRNat] using
      (C.section4URedCondPairSet_card_le_redProjectionPairCount_of_indep
        (I := I) (A := C.section4F I ε) hindep)
  have hUBactual : uBActual ≤ uBNat := by
    simpa [uBActual, uBNat] using
      (C.section4UBlueCondPairSet_card_le_blueProjectionPairCount_of_indep
        (I := I) (A := C.section4F I ε) hindep)
  rw [← C.section4UCondChoiceEventMassSum_eq_section4UCondChoiceEventMass_of_card_le
    (I := I) (A := C.section4F I ε) (p := p) (remaining := remainingNat)
    (uRMax := uRNat) (uBMax := uBNat) hURactual hUBactual]
  exact
    C.section4UCondChoiceEventMassSum_section4F_le_exp_of_indep_of_bounds
      (I := I) (ε := ε) (p := p) (N := N) hindep hp0 hp1 hRemaining hUR hUB

set_option linter.style.longLine false in
theorem
    section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_bounds_of_sum_le
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p errorBound : ℝ} {N : ℕ}
    {remainingBound uRBound uBBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hRemaining :
      remainingBound ≤
        N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl))
    (hUR :
      C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) ≤
        uRBound)
    (hUB :
      C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
        uBBound)
    (hError : (uRBound : ℝ) + (uBBound : ℝ) ≤ errorBound) :
    let remainingNat :=
      N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
        (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
    let uRActual := (C.section4URedCondPairSet I (C.section4F I ε)).card
    let uBActual := (C.section4UBlueCondPairSet I (C.section4F I ε)).card
    C.section4UCondChoiceEventMass I (C.section4F I ε) p uRActual uBActual remainingNat ≤
      Real.exp (p * errorBound - p * (remainingBound : ℝ)) := by
  let remainingNat :=
    N - I.card * (C.section4F1 I ∪ C.section4F2 I ε).card -
      (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) -
      C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) -
      C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
  let uRActual := (C.section4URedCondPairSet I (C.section4F I ε)).card
  let uBActual := (C.section4UBlueCondPairSet I (C.section4F I ε)).card
  change
    C.section4UCondChoiceEventMass I (C.section4F I ε) p uRActual uBActual remainingNat ≤
      Real.exp (p * errorBound - p * (remainingBound : ℝ))
  refine
    (C.section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_bounds
      (I := I) (ε := ε) (p := p) (N := N) hindep hp0 hp1
      hRemaining hUR hUB).trans ?_
  apply Real.exp_le_exp.mpr
  nlinarith

set_option linter.style.longLine false in
theorem
    section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_totalError
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p totalError : ℝ} {N : ℕ}
    {uRBound uBBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUR :
      C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) ≤
        uRBound)
    (hUB :
      C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
        uBBound)
    (hRemovedLeN :
      let removedNat :=
        I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) +
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) +
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
      removedNat ≤ N)
    (hTotal :
      let removedNat :=
        I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) +
          C.redProjectionPairCount I
            ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) +
          C.blueProjectionPairCount I
            ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
      (removedNat : ℝ) + (uRBound : ℝ) + (uBBound : ℝ) ≤ totalError) :
    let removedNat :=
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
        (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) +
        C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) +
        C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
    let remainingNat := N - removedNat
    let uRActual := (C.section4URedCondPairSet I (C.section4F I ε)).card
    let uBActual := (C.section4UBlueCondPairSet I (C.section4F I ε)).card
    C.section4UCondChoiceEventMass I (C.section4F I ε) p uRActual uBActual remainingNat ≤
      Real.exp (p * totalError - p * (N : ℝ)) := by
  let removedNat :=
    I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
      (C.redProjectionPairCount I ((C.baseImage I).filter IsRedBaseVertex) +
        C.blueProjectionPairCount I ((C.baseImage I).filter IsBlueBaseVertex)) +
      C.redProjectionPairCount I
        ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) +
      C.blueProjectionPairCount I
        ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
  let remainingNat := N - removedNat
  let uRActual := (C.section4URedCondPairSet I (C.section4F I ε)).card
  let uBActual := (C.section4UBlueCondPairSet I (C.section4F I ε)).card
  have hremoved : removedNat ≤ N := by
    simpa [removedNat] using hRemovedLeN
  have htotal :
      (removedNat : ℝ) + (uRBound : ℝ) + (uBBound : ℝ) ≤ totalError := by
    simpa [removedNat] using hTotal
  change
    C.section4UCondChoiceEventMass I (C.section4F I ε) p uRActual uBActual remainingNat ≤
      Real.exp (p * totalError - p * (N : ℝ))
  have hraw :=
    C.section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_bounds_of_sum_le
      (I := I) (ε := ε) (p := p) (N := N)
      (errorBound := totalError - (removedNat : ℝ))
      (remainingBound := remainingNat)
      hindep hp0 hp1
      (by simp [remainingNat, removedNat, Nat.sub_sub])
      hUR hUB
      (by nlinarith)
  have hbase :
      C.section4UCondChoiceEventMass I (C.section4F I ε) p uRActual uBActual remainingNat ≤
        Real.exp (p * (totalError - (removedNat : ℝ)) - p * (remainingNat : ℝ)) := by
    simpa [uRActual, uBActual, remainingNat, removedNat, Nat.sub_sub] using hraw
  refine hbase.trans ?_
  apply Real.exp_le_exp.mpr
  have hcast :
      (remainingNat : ℝ) = (N : ℝ) - (removedNat : ℝ) := by
    simp [remainingNat, Nat.cast_sub hremoved]
  nlinarith

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_totalError
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p totalError : ℝ} {N : ℕ}
    {uRBound uBBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hUR :
      C.redProjectionPairCount I
          ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr) ≤
        uRBound)
    (hUB :
      C.blueProjectionPairCount I
          ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl) ≤
        uBBound)
    (hLossLeN : C.section4SecondStageLossNat I ε ≤ N)
    (hTotal :
      (C.section4SecondStageLossNat I ε : ℝ) + (uRBound : ℝ) + (uBBound : ℝ) ≤ totalError) :
    C.section4ActualConditionedEventMass I ε p N ≤ Real.exp (p * totalError - p * (N : ℝ)) := by
  unfold section4ActualConditionedEventMass section4SecondStageLossNat
  simpa using
    (C.section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_totalError
      (I := I) (ε := ε) (p := p) (N := N)
      (uRBound := uRBound) (uBBound := uBBound)
      hindep hp0 hp1 hUR hUB hLossLeN hTotal)

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_LMS_totalError
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p totalError : ℝ} {N : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeN :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        N)
    (hTotal :
      (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
            3 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
            C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ)) ≤
        totalError) :
    C.section4ActualConditionedEventMass I ε p N ≤ Real.exp (p * totalError - p * (N : ℝ)) := by
  let uRBound :=
    C.redProjectionPairCount I
      ((Finset.univ.filter fun b : Fin m => Sum.inr b ∉ C.section4F I ε).image Sum.inr)
  let uBBound :=
    C.blueProjectionPairCount I
      ((Finset.univ.filter fun r : Fin m => Sum.inl r ∉ C.section4F I ε).image Sum.inl)
  have hLoss :
      C.section4SecondStageLossNat I ε ≤
        I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) := by
    exact
      C.section4SecondStageLossNat_le_revealBudget_add_two_mul_partPairCount_LMS_add_huge
        I hHsubset ht21 ht32
  have hLossLeN' : C.section4SecondStageLossNat I ε ≤ N := hLoss.trans hLossLeN
  have hTotalNat :
      C.section4SecondStageLossNat I ε + uRBound + uBBound ≤
        I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          3 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) := by
    simpa [uRBound, uBBound] using
      C.section4SecondStageLossNat_add_witnessCaps_le_revealBudget_add_three_mul_partPairCount_LMS_add_huge
        I hHsubset ht21 ht32
  have hTotal' :
      (C.section4SecondStageLossNat I ε : ℝ) + (uRBound : ℝ) + (uBBound : ℝ) ≤ totalError := by
    have hTotalNatR :
        (C.section4SecondStageLossNat I ε : ℝ) + (uRBound : ℝ) + (uBBound : ℝ) ≤
          (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
                3 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
                C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
                C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ)) := by
      exact_mod_cast hTotalNat
    exact hTotalNatR.trans hTotal
  exact
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_totalError
      (I := I) (ε := ε) (p := p) (N := N)
      (uRBound := uRBound) (uBBound := uBBound)
      hindep hp0 hp1
      (by simp [uRBound]) (by simp [uBBound]) hLossLeN' hTotal'

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_splitPartTotalError
    (C : ConstructionData n m) (I : Finset (Fin n))
    {ε p totalError revealError largeError mediumError smallError hugeRedError hugeBlueError : ℝ}
    {N : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeN :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        N)
    (hReveal :
      (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) ≤ revealError)
    (hLarge : ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤ largeError)
    (hMedium : ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤ mediumError)
    (hSmall : ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤ smallError)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        hugeRedError)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        hugeBlueError)
    (hTotal :
      revealError + 3 * (largeError + mediumError + smallError) + hugeRedError + hugeBlueError ≤
        totalError) :
    C.section4ActualConditionedEventMass I ε p N ≤ Real.exp (p * totalError - p * (N : ℝ)) := by
  have hLMS :
      ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) ≤
        largeError + mediumError + smallError := by
    exact C.cast_partPairCount_LMS_le_sum_of_thresholds I ht32 hLarge hMedium hSmall
  have hTotal' :
      (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
            3 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
            C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
            C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ)) ≤
        totalError := by
    have hCast :
        (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
              3 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
              C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
              C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ)) =
          (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) +
            3 * ((C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) : ℕ) : ℝ) +
            ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) +
            ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) := by
      norm_num
    rw [hCast]
    nlinarith
  exact
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_LMS_totalError
      (I := I) (ε := ε) (p := p) (N := N)
      hindep hp0 hp1 hHsubset ht21 ht32 hLossLeN hTotal'

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_uniformPartError
    (C : ConstructionData n m) (I : Finset (Fin n))
    {ε p revealError ε1 κ : ℝ} {N : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeN :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        N)
    (hReveal :
      (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) ≤ revealError)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p N ≤
      Real.exp
        (p * (revealError + 11 * (ε1 * Twobites.paperK κ n ^ 2)) - p * (N : ℝ)) := by
  refine
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_splitPartTotalError
      (I := I) (ε := ε) (p := p) (N := N)
      (totalError := revealError + 11 * (ε1 * Twobites.paperK κ n ^ 2))
      (revealError := revealError)
      (largeError := ε1 * Twobites.paperK κ n ^ 2)
      (mediumError := ε1 * Twobites.paperK κ n ^ 2)
      (smallError := ε1 * Twobites.paperK κ n ^ 2)
      (hugeRedError := ε1 * Twobites.paperK κ n ^ 2)
      (hugeBlueError := ε1 * Twobites.paperK κ n ^ 2)
      hindep hp0 hp1 hHsubset ht21 ht32 hLossLeN hReveal hLarge hMedium hSmall
      hHugeRed hHugeBlue ?_
  nlinarith

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError
    (C : ConstructionData n m) (I : Finset (Fin n)) {ε p ε1 κ : ℝ} {N : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeN :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        N)
    (hReveal :
      (((I.card * (C.section4F1 I ∪ C.section4F2 I ε).card : ℕ) : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p N ≤
      Real.exp (p * (12 * (ε1 * Twobites.paperK κ n ^ 2)) - p * (N : ℝ)) := by
  have hbase :=
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_uniformPartError
      (I := I) (ε := ε) (p := p) (N := N) (revealError := ε1 * Twobites.paperK κ n ^ 2)
      hindep hp0 hp1 hHsubset ht21 ht32 hLossLeN hReveal hLarge hMedium hSmall
      hHugeRed hHugeBlue
  refine hbase.trans ?_
  apply Real.exp_le_exp.mpr
  ring_nf
  linarith

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealWitnessBounds
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε p ε1 : ℝ} {N : ℕ} {lWitness hWitness : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeN :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        N)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hLWitness :
      Twobites.paperKNat κ n < lWitness * ⌈Twobites.paperT2 ε n⌉₊ -
        lWitness.choose 2 * codegreeBound)
    (hHWitness :
      Twobites.paperKNat κ n < hWitness * ⌈Twobites.paperT1 n⌉₊ -
        hWitness.choose 2 * codegreeBound)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + (lWitness : ℝ) + (hWitness : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p N ≤
      Real.exp (p * (12 * (ε1 * Twobites.paperK κ n ^ 2)) - p * (N : ℝ)) := by
  apply C.section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError
    (I := I) (ε := ε) (p := p) (κ := κ) (N := N)
  · exact hindep
  · exact hp0
  · exact hp1
  · exact hHsubset
  · exact ht21
  · exact ht32
  · exact hLossLeN
  · exact
      C.cast_section4RevealBudget_le_eps_mul_paperKSq_of_goodEventD_of_witnessBounds
        hD I hn hε hI hLWitness hHWitness hRevealArith
  · exact hLarge
  · exact hMedium
  · exact hSmall
  · exact hHugeRed
  · exact hHugeBlue

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealLWitness_of_paperHugeWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε p ε1 : ℝ} {N : ℕ} {lWitness : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeN :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        N)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT1 : 2 < Twobites.paperT1 n)
    (hLWitness :
      Twobites.paperKNat κ n < lWitness * ⌈Twobites.paperT2 ε n⌉₊ -
        lWitness.choose 2 * codegreeBound)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + (lWitness : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p N ≤
      Real.exp (p * (12 * (ε1 * Twobites.paperK κ n ^ 2)) - p * (N : ℝ)) := by
  have hHWitness :
      Twobites.paperKNat κ n <
        Twobites.paperHugeWitnessNat κ n * ⌈Twobites.paperT1 n⌉₊ -
          (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound := by
    exact
      Twobites.paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_of_two_mul_lt
        (Twobites.two_mul_paperKNat_lt_paperHugeWitnessNat_mul_ceil_paperT1 hκ hT1)
        hHChoose
  exact
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealWitnessBounds
      hD I hindep hp0 hp1 hHsubset ht21 ht32 hLossLeN hn hε hI hLWitness hHWitness
      hRevealArith hLarge hMedium hSmall hHugeRed hHugeBlue

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealLBound_of_paperHugeWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {κ ε p ε1 lBound : ℝ} {N : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeN :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        N)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT1 : 2 < Twobites.paperT1 n)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hL : ((C.LPart I ε).card : ℝ) ≤ lBound)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + lBound +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p N ≤
      Real.exp (p * (12 * (ε1 * Twobites.paperK κ n ^ 2)) - p * (N : ℝ)) := by
  apply C.section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError
    (I := I) (ε := ε) (p := p) (κ := κ) (N := N)
  · exact hindep
  · exact hp0
  · exact hp1
  · exact hHsubset
  · exact ht21
  · exact ht32
  · exact hLossLeN
  · exact
      C.cast_section4RevealBudget_le_eps_mul_paperKSq_of_LBound_of_paperHugeWitness
        hD I hn hε hI hκ hT1 hHChoose hL hRevealArith
  · exact hLarge
  · exact hMedium
  · exact hSmall
  · exact hHugeRed
  · exact hHugeBlue

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealWitnessBounds_of_targetGap
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {κ ε p ε1 : ℝ} {cap openError : ℕ} {lWitness hWitness : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeTarget :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        C.paperSection4OpenPairTargetNat I κ cap - openError)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hLWitness :
      Twobites.paperKNat κ n < lWitness * ⌈Twobites.paperT2 ε n⌉₊ -
        lWitness.choose 2 * codegreeBound)
    (hHWitness :
      Twobites.paperKNat κ n < hWitness * ⌈Twobites.paperT1 n⌉₊ -
        hWitness.choose 2 * codegreeBound)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + (lWitness : ℝ) + (hWitness : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p
        (C.paperSection4OpenPairTargetNat I κ cap - openError) ≤
      Real.exp
        (p * (12 * (ε1 * Twobites.paperK κ n ^ 2) + (openError : ℝ)) -
          p * C.paperSection4OpenPairTarget I κ cap) := by
  have hbase :=
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealWitnessBounds
      hD I hindep hp0 hp1 hHsubset ht21 ht32 hLossLeTarget hn hε hI hLWitness hHWitness
      hRevealArith hLarge hMedium hSmall hHugeRed hHugeBlue
  refine hbase.trans ?_
  apply Real.exp_le_exp.mpr
  have hsub :
      (C.paperSection4OpenPairTargetNat I κ cap : ℝ) - (openError : ℝ) ≤
        (((C.paperSection4OpenPairTargetNat I κ cap - openError : ℕ) : ℝ)) := by
    by_cases hle : openError ≤ C.paperSection4OpenPairTargetNat I κ cap
    · rw [Nat.cast_sub hle]
    · have hzero :
        (((C.paperSection4OpenPairTargetNat I κ cap - openError : ℕ) : ℝ)) = 0 := by
        simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hle))]
      have hnonpos :
          (C.paperSection4OpenPairTargetNat I κ cap : ℝ) - (openError : ℝ) ≤ 0 := by
        exact sub_nonpos.mpr (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hle))
      simpa [hzero] using hnonpos
  have hmul :
      p * ((C.paperSection4OpenPairTargetNat I κ cap : ℝ) - (openError : ℝ)) ≤
        p * (((C.paperSection4OpenPairTargetNat I κ cap - openError : ℕ) : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hsub hp0
  unfold paperSection4OpenPairTarget
  nlinarith

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealLBound_of_paperHugeWitness_of_targetGap
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {κ ε p ε1 lBound : ℝ} {cap openError : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeTarget :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        C.paperSection4OpenPairTargetNat I κ cap - openError)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT1 : 2 < Twobites.paperT1 n)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hL : ((C.LPart I ε).card : ℝ) ≤ lBound)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + lBound +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p
        (C.paperSection4OpenPairTargetNat I κ cap - openError) ≤
      Real.exp
        (p * (12 * (ε1 * Twobites.paperK κ n ^ 2) + (openError : ℝ)) -
          p * C.paperSection4OpenPairTarget I κ cap) := by
  have hbase :=
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealLBound_of_paperHugeWitness
      hD I hindep hp0 hp1 hHsubset ht21 ht32 hLossLeTarget hn hε hI hκ hT1 hHChoose
      hL hRevealArith hLarge hMedium hSmall hHugeRed hHugeBlue
  refine hbase.trans ?_
  apply Real.exp_le_exp.mpr
  have hsub :
      (C.paperSection4OpenPairTargetNat I κ cap : ℝ) - (openError : ℝ) ≤
        (((C.paperSection4OpenPairTargetNat I κ cap - openError : ℕ) : ℝ)) := by
    by_cases hle : openError ≤ C.paperSection4OpenPairTargetNat I κ cap
    · rw [Nat.cast_sub hle]
    · have hzero :
        (((C.paperSection4OpenPairTargetNat I κ cap - openError : ℕ) : ℝ)) = 0 := by
        simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hle))]
      have hnonpos :
          (C.paperSection4OpenPairTargetNat I κ cap : ℝ) - (openError : ℝ) ≤ 0 := by
        exact sub_nonpos.mpr (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hle))
      simpa [hzero] using hnonpos
  have hmul :
      p * ((C.paperSection4OpenPairTargetNat I κ cap : ℝ) - (openError : ℝ)) ≤
        p * (((C.paperSection4OpenPairTargetNat I κ cap - openError : ℕ) : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hsub hp0
  unfold paperSection4OpenPairTarget
  nlinarith

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealLWitness_of_paperHugeWitness_of_targetGap
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {κ ε p ε1 : ℝ} {cap openError : ℕ} {lWitness : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeTarget :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        C.paperSection4OpenPairTargetNat I κ cap - openError)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT1 : 2 < Twobites.paperT1 n)
    (hLWitness :
      Twobites.paperKNat κ n < lWitness * ⌈Twobites.paperT2 ε n⌉₊ -
        lWitness.choose 2 * codegreeBound)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) + (lWitness : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p
        (C.paperSection4OpenPairTargetNat I κ cap - openError) ≤
      Real.exp
        (p * (12 * (ε1 * Twobites.paperK κ n ^ 2) + (openError : ℝ)) -
          p * C.paperSection4OpenPairTarget I κ cap) := by
  have hHWitness :
      Twobites.paperKNat κ n <
        Twobites.paperHugeWitnessNat κ n * ⌈Twobites.paperT1 n⌉₊ -
          (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound := by
    exact
      Twobites.paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_of_two_mul_lt
        (Twobites.two_mul_paperKNat_lt_paperHugeWitnessNat_mul_ceil_paperT1 hκ hT1)
        hHChoose
  exact
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealWitnessBounds_of_targetGap
      hD I hindep hp0 hp1 hHsubset ht21 ht32 hLossLeTarget hn hε hI hLWitness
      hHWitness hRevealArith hLarge hMedium hSmall hHugeRed hHugeBlue

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_paperLargeWitness_of_paperHugeWitness
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {κ ε p ε1 : ℝ} {N : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeN :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        N)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT2 : 2 < Twobites.paperT2 ε n) (hT1 : 2 < Twobites.paperT1 n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
              (Twobites.paperLargeWitnessNat κ ε n : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p N ≤
      Real.exp (p * (12 * (ε1 * Twobites.paperK κ n ^ 2)) - p * (N : ℝ)) := by
  have hL :
      ((C.LPart I ε).card : ℝ) ≤ (Twobites.paperLargeWitnessNat κ ε n : ℝ) :=
    C.cast_LPart_card_le_paperLargeWitnessNat_of_goodEventD hD I hI hκ hT2 hLChoose
  exact
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealLBound_of_paperHugeWitness
      hD I hindep hp0 hp1 hHsubset ht21 ht32 hLossLeN hn hε hI hκ hT1 hHChoose
      hL hRevealArith hLarge hMedium hSmall hHugeRed hHugeBlue

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_paperLargeWitness_of_paperHugeWitness_of_targetGap
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {κ ε p ε1 : ℝ} {cap openError : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeTarget :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        C.paperSection4OpenPairTargetNat I κ cap - openError)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT2 : 2 < Twobites.paperT2 ε n) (hT1 : 2 < Twobites.paperT1 n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
              (Twobites.paperLargeWitnessNat κ ε n : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p
        (C.paperSection4OpenPairTargetNat I κ cap - openError) ≤
      Real.exp
        (p * (12 * (ε1 * Twobites.paperK κ n ^ 2) + (openError : ℝ)) -
          p * C.paperSection4OpenPairTarget I κ cap) := by
  have hL :
      ((C.LPart I ε).card : ℝ) ≤ (Twobites.paperLargeWitnessNat κ ε n : ℝ) :=
    C.cast_LPart_card_le_paperLargeWitnessNat_of_goodEventD hD I hI hκ hT2 hLChoose
  exact
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_revealLBound_of_paperHugeWitness_of_targetGap
      hD I hindep hp0 hp1 hHsubset ht21 ht32 hLossLeTarget hn hε hI hκ hT1 hHChoose
      hL hRevealArith hLarge hMedium hSmall hHugeRed hHugeBlue

set_option linter.style.longLine false in
theorem
    section4ActualConditionedEventMass_baseOpenPairSet_card_le_exp_of_indep_of_uniformError_of_paperLargeWitness_of_paperHugeWitness_of_targetGap
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {κ ε p ε1 : ℝ} {cap openError : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeTarget :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        C.paperSection4OpenPairTargetNat I κ cap - openError)
    (hTargetGap :
      C.paperSection4OpenPairTargetNat I κ cap - openError ≤ (C.baseOpenPairSet I).card)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 0 ≤ κ) (hT2 : 2 < Twobites.paperT2 ε n) (hT1 : 2 < Twobites.paperT1 n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
              (Twobites.paperLargeWitnessNat κ ε n : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2) :
    C.section4ActualConditionedEventMass I ε p (C.baseOpenPairSet I).card ≤
      Real.exp
        (p * (12 * (ε1 * Twobites.paperK κ n ^ 2) + (openError : ℝ)) -
          p * C.paperSection4OpenPairTarget I κ cap) := by
  have hmono :
      C.section4ActualConditionedEventMass I ε p (C.baseOpenPairSet I).card ≤
        C.section4ActualConditionedEventMass I ε p
          (C.paperSection4OpenPairTargetNat I κ cap - openError) := by
    exact C.section4ActualConditionedEventMass_antitone I hp0 hp1 hTargetGap
  exact hmono.trans <|
    C.section4ActualConditionedEventMass_le_exp_of_indep_of_uniformError_of_paperLargeWitness_of_paperHugeWitness_of_targetGap
      hD I hindep hp0 hp1 hHsubset ht21 ht32 hLossLeTarget hn hε hI hκ hT2 hT1
      hLChoose hHChoose hRevealArith hLarge hMedium hSmall hHugeRed hHugeBlue

set_option linter.style.longLine false in
/-- Paper Lemma `lem:RISI`, expressed in the repo's literal finite Bernoulli semantics for the
actual conditioned second-stage event on `section4F`. -/
theorem
    section4ActualConditionedEventMass_baseOpenPairSet_card_le_exp_of_indep_of_uniformError_of_paperLargeWitness_of_paperHugeWitness_of_paperDeterministicTargetGap
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε p ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB : ℝ}
    {mediumWitness smallBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hLossLeTarget :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) -
          ⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 1 ≤ κ) (hT2 : 2 < Twobites.paperT2 ε n) (hT1 : 2 < Twobites.paperT1 n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hLargeBound :
      (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n +
            (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMediumWitness :
      Twobites.paperKNat κ n < mediumWitness * ⌈Twobites.paperT3 ε n⌉₊ -
        mediumWitness.choose 2 * codegreeBound)
    (hMediumBound :
      (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + mediumWitness.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmallCard : (C.SPart I ε).card ≤ smallBound)
    (hSmallBound :
      (Twobites.paperT3 ε n / 2) *
          (Twobites.paperKNat κ n + smallBound.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
              (Twobites.paperLargeWitnessNat κ ε n : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1)) :
    C.section4ActualConditionedEventMass I ε p (C.baseOpenPairSet I).card ≤
      Real.exp
        (p * (12 * (ε1 * Twobites.paperK κ n ^ 2) +
            (⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ : ℝ)) -
          p * C.paperSection4OpenPairTarget I κ (Twobites.paperCapNat β ε2 n)) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hTargetGap :=
    C.paperSection4OpenPairTargetNat_sub_ceil_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministic
      hD I hindep ht21 ht32 (show 0 ≤ Twobites.paperT1 n by linarith) hn hI hκ hT2 hLChoose
      hLargeBound hMediumWitness hMediumBound hSmallCard hSmallBound
      hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hρR hρB hβ hε2
      hε1pos hε1le hloglogGap hdiagScale hcodegScale hsumGap hdegBound hchooseCodegBound
      hcodegBound hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall
  exact
    C.section4ActualConditionedEventMass_baseOpenPairSet_card_le_exp_of_indep_of_uniformError_of_paperLargeWitness_of_paperHugeWitness_of_targetGap
      hD I hindep hp0 hp1 hHsubset ht21 ht32 hLossLeTarget hTargetGap hn hε hI hκ0 hT2 hT1 hLChoose hHChoose hRevealArith
      hLarge hMedium hSmall hHugeRed hHugeBlue

set_option linter.style.longLine false in
/-- Paper Lemma `lem:RISI`, reduced to one remaining arithmetic hypothesis saying that the paper
target dominates the deterministic `9 * ε₁ * k²` Section 4 loss together with the sharpened
`10 * ε₁ * k²` target-gap slack. -/
theorem paper_risi_finiteMassBound_of_targetGapArithmetic
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε p ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB : ℝ}
    {mediumWitness smallBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 1 ≤ κ) (hT2 : 2 < Twobites.paperT2 ε n) (hT1 : 2 < Twobites.paperT1 n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hLargeBound :
      (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n +
            (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMediumWitness :
      Twobites.paperKNat κ n < mediumWitness * ⌈Twobites.paperT3 ε n⌉₊ -
        mediumWitness.choose 2 * codegreeBound)
    (hMediumBound :
      (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + mediumWitness.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmallCard : (C.SPart I ε).card ≤ smallBound)
    (hSmallBound :
      (Twobites.paperT3 ε n / 2) *
          (Twobites.paperKNat κ n + smallBound.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
              (Twobites.paperLargeWitnessNat κ ε n : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hLossGap :
      ⌈9 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ +
          ⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ ≤
        C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n)) :
    C.section4ActualConditionedEventMass I ε p (C.baseOpenPairSet I).card ≤
      Real.exp
        (p * (12 * (ε1 * Twobites.paperK κ n ^ 2) +
            (⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ : ℝ)) -
          p * C.paperSection4OpenPairTarget I κ (Twobites.paperCapNat β ε2 n)) := by
  have hLossNat :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        ⌈9 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ := by
    exact
      C.section4LossTargetNat_le_ceil_nine_mul_eps_mul_paperKSq_of_paperDeterministic
        hD I ht21 ht32 hn hε hI hκ hT2 hT1 hLChoose hLargeBound hMediumWitness
        hMediumBound hSmallCard hSmallBound hHChoose hRevealArith hred hblue hblueCap
        hblueCapWeight hredCap hredCapWeight hρR hρB hβ hε2 hε1pos hε1le hloglogGap
        hdiagScale hcodegScale hsumGap hdegBound hchooseCodegBound hcodegBound
        hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall
  have hLossLeTarget :
      I.card * (C.section4F1 I ∪ C.section4F2 I ε).card +
          2 * C.partPairCount I (C.LPart I ε ∪ C.MPart I ε ∪ C.SPart I ε) +
          C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) +
          C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) ≤
        C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n) -
          ⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ := by
    omega
  exact
    C.section4ActualConditionedEventMass_baseOpenPairSet_card_le_exp_of_indep_of_uniformError_of_paperLargeWitness_of_paperHugeWitness_of_paperDeterministicTargetGap
      hD I hindep hp0 hp1 hHsubset ht21 ht32 hLossLeTarget hn hε hI hκ hT2 hT1
      hLChoose hLargeBound hMediumWitness hMediumBound hSmallCard hSmallBound hHChoose
      hRevealArith hLarge hMedium hSmall hHugeRed hHugeBlue hred hblue hblueCap
      hblueCapWeight hredCap hredCapWeight hρR hρB hβ hε2 hε1pos hε1le hloglogGap
      hdiagScale hcodegScale hsumGap hdegBound hchooseCodegBound hcodegBound
      hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall

set_option linter.style.longLine false in
/-- Paper Lemma `lem:RISI`, with the remaining arithmetic expressed directly as the natural target
domination `paperRISILossNat ≤ f(ℓ_R,ℓ_B)`. -/
theorem paper_risi_finiteMassBound_of_paperRISILossGap
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n))
    {ρR ρB β κ ε p ε1 ε2 βdeg qcodeg δsumGap δgapR δgapB : ℝ}
    {mediumWitness smallBound : ℕ}
    (hindep :
      ∀ {v w : Fin n}, v ∈ I → w ∈ I → v ≠ w → ¬ C.finalGraph.Adj v w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHsubset : C.baseImage I ∩ C.HPart I ⊆ C.section4F2 I ε)
    (ht21 : Twobites.paperT2 ε n ≤ Twobites.paperT1 n)
    (ht32 : Twobites.paperT3 ε n ≤ Twobites.paperT2 ε n)
    (hn : 1 < n) (hε : ε ≤ (1 / 4 : ℝ))
    (hI : I.card ≤ Twobites.paperKNat κ n)
    (hκ : 1 ≤ κ) (hT2 : 2 < Twobites.paperT2 ε n) (hT1 : 2 < Twobites.paperT1 n)
    (hLChoose :
      (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hLargeBound :
      (Twobites.paperT1 n / 2) *
          (Twobites.paperKNat κ n +
            (Twobites.paperLargeWitnessNat κ ε n).choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMediumWitness :
      Twobites.paperKNat κ n < mediumWitness * ⌈Twobites.paperT3 ε n⌉₊ -
        mediumWitness.choose 2 * codegreeBound)
    (hMediumBound :
      (Twobites.paperT2 ε n / 2) *
          (Twobites.paperKNat κ n + mediumWitness.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmallCard : (C.SPart I ε).card ≤ smallBound)
    (hSmallBound :
      (Twobites.paperT3 ε n / 2) *
          (Twobites.paperKNat κ n + smallBound.choose 2 * codegreeBound : ℕ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHChoose :
      (Twobites.paperHugeWitnessNat κ n).choose 2 * codegreeBound ≤
        Twobites.paperKNat κ n)
    (hRevealArith :
      (I.card : ℝ) *
          (2 * (I.card : ℝ) / Real.log (n : ℝ) +
              (Twobites.paperLargeWitnessNat κ ε n : ℝ) +
            (Twobites.paperHugeWitnessNat κ n : ℝ)) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hLarge :
      ((C.partPairCount I (C.LPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hMedium :
      ((C.partPairCount I (C.MPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hSmall :
      ((C.partPairCount I (C.SPart I ε) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeRed :
      ((C.redProjectionPairCount I ((C.HPart I).filter IsRedBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hHugeBlue :
      ((C.blueProjectionPairCount I ((C.HPart I).filter IsBlueBaseVertex) : ℕ) : ℝ) ≤
        ε1 * Twobites.paperK κ n ^ 2)
    (hred : (C.redImage I).card ≤ Twobites.paperKNat ρR n)
    (hblue : (C.blueImage I).card ≤ Twobites.paperKNat ρB n)
    (hblueCap :
      ∀ x ∈ (C.HPart I).filter IsRedBaseVertex,
        (C.blueProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hblueCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.blueProjectionWeight I ((C.HPart I).filter IsRedBaseVertex))
    (hredCap :
      ∀ x ∈ (C.HPart I).filter IsBlueBaseVertex,
        (C.redProjectionImage I x).card ≤ Twobites.paperCapNat β ε2 n)
    (hredCapWeight :
      Twobites.paperCapNat β ε2 n ≤
        C.redProjectionWeight I ((C.HPart I).filter IsBlueBaseVertex))
    (hρR : 0 ≤ ρR) (hρB : 0 ≤ ρB) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
    (hloglogGap : 2 / ε1 ≤ Real.log (Real.log (n : ℝ)))
    (hdiagScale :
      3 * βdeg * Real.log (Real.log (n : ℝ)) ≤ ε1 * Twobites.paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * qcodeg) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ)
    (hsumGap : 1 ≤ Twobites.paperK δsumGap n)
    (hdegBound : (degreeBound : ℝ) ≤ Twobites.paperP βdeg n * Twobites.paperM n)
    (hchooseCodegBound : (codegreeBound : ℝ) ≤ qcodeg)
    (hcodegBound : (projCodegreeBound : ℝ) ≤ qcodeg)
    (hgap2R : 2 ≤ Twobites.paperK δgapR n)
    (hκ2R :
      ρR + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapR ≤ κ)
    (hblueCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρR n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hgap2B : 2 ≤ Twobites.paperK δgapB n)
    (hκ2B :
      ρB + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgapB ≤ κ)
    (hredCrossSmall :
      6 * Twobites.paperK κ n ≤
        (((Twobites.paperKNat κ n - Twobites.paperKNat ρB n -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) - 1))
    (hLossGap :
      paperRISILossNat κ ε1 n ≤
        C.paperSection4OpenPairTargetNat I κ (Twobites.paperCapNat β ε2 n)) :
    C.section4ActualConditionedEventMass I ε p (C.baseOpenPairSet I).card ≤
      Real.exp
        (p * (12 * (ε1 * Twobites.paperK κ n ^ 2) +
            (⌈10 * (ε1 * Twobites.paperK κ n ^ 2)⌉₊ : ℝ)) -
          p * C.paperSection4OpenPairTarget I κ (Twobites.paperCapNat β ε2 n)) := by
  simpa [paperRISILossNat] using
    C.paper_risi_finiteMassBound_of_targetGapArithmetic hD I hindep hp0 hp1 hHsubset ht21 ht32
      hn hε hI hκ hT2 hT1 hLChoose hLargeBound hMediumWitness hMediumBound hSmallCard
      hSmallBound hHChoose hRevealArith hLarge hMedium hSmall hHugeRed hHugeBlue hred
      hblue hblueCap hblueCapWeight hredCap hredCapWeight hρR hρB hβ hε2 hε1pos hε1le
      hloglogGap hdiagScale hcodegScale hsumGap hdegBound hchooseCodegBound hcodegBound
      hgap2R hκ2R hblueCrossSmall hgap2B hκ2B hredCrossSmall hLossGap

end

end ConstructionData

end Twobites
