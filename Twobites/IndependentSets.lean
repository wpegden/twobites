import Twobites.Construction
import Twobites.ParameterBounds
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
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

/-- The current natural-number upper bound for the `H_I ∩ V_R` cross-projection term, before the
final paper asymptotic simplifications are applied. -/
def paperHugeBlueCrossErrorNat (C : ConstructionData n m) (I : Finset (Fin n))
    (witnessSize degreeBound projCodegreeBound : ℕ) : ℕ :=
  witnessSize * degreeBound +
    ((C.HPart I).filter IsRedBaseVertex).card.choose 2 * projCodegreeBound

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

/-- The current natural-number upper bound for the `H_I ∩ V_B` cross-projection term, before the
final paper asymptotic simplifications are applied. -/
def paperHugeRedCrossErrorNat (C : ConstructionData n m) (I : Finset (Fin n))
    (witnessSize degreeBound projCodegreeBound : ℕ) : ℕ :=
  witnessSize * degreeBound +
    ((C.HPart I).filter IsBlueBaseVertex).card.choose 2 * projCodegreeBound

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

theorem redImage_card_le_card (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.redImage I).card ≤ I.card := by
  simpa [ConstructionData.redImage] using
    (Finset.card_image_le (s := I) (f := C.redProj))

theorem blueImage_card_le_card (C : ConstructionData n m) (I : Finset (Fin n)) :
    (C.blueImage I).card ≤ I.card := by
  simpa [ConstructionData.blueImage] using
    (Finset.card_image_le (s := I) (f := C.blueProj))

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

/-- Paper Lemma `lem:huge`, with the cross-term witness errors supplied through a single real
upper bound `W = o(k)` rather than the older `3B` smallness specialization. -/
theorem paper_huge_deterministic_of_witnessErrorBounds_of_realErrorBound
    (C : ConstructionData n m) {fiberBound degreeBound codegreeBound projCodegreeBound : ℕ}
    (hD : GoodEventD C fiberBound degreeBound codegreeBound projCodegreeBound)
    (I : Finset (Fin n)) {ρR ρB β κ ε1 ε2 δR δB W : ℝ} {witnessSize : ℕ}
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
    (herror :
      (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤ W)
    (hblueCrossLeft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) * W + W ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hblueCrossRight :
      (((Twobites.paperKNat κ n - (C.redImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * W + W ^ 2 / 2) ≤
        ε1 *
          C.paperHugeBlueCrossRightTarget I κ (Twobites.paperCapNat β ε2 n))
    (hredCrossLeft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) * W + W ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hredCrossRight :
      (((Twobites.paperKNat κ n - (C.blueImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * W + W ^ 2 / 2) ≤
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
  apply C.paper_huge_deterministic_of_witnessErrorBounds hD I hI hwitness hred hblue hblueCap
    hblueCapWeight hredCap hredCapWeight hn hρR hρB hβ hε2 hgapR hgapB hκR hκB hdiagRed
    hdiagBlue hε1
  · exact C.paperHugeBlueCrossLeftError_of_le_of_sq_bound I herror hblueCrossLeft
  · exact
      C.paperHugeBlueCrossWitnessRightErrorProp_of_le_of_sq_bound I herror hblueCrossRight
  · exact C.paperHugeRedCrossLeftError_of_le_of_sq_bound I herror hredCrossLeft
  · exact
      C.paperHugeRedCrossWitnessRightErrorProp_of_le_of_sq_bound I herror hredCrossRight

/-- Paper Lemma `lem:huge`, with the Section 3 witness error packaged through a witness-size scale
`B` and a combined coefficient `δ`, so the remaining cross-term work is stated directly as four
`paperK δ` coefficient inequalities. -/
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
    (hblueCrossLeft :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) * Twobites.paperK δ n +
        (Twobites.paperK δ n) ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)))
    (hblueCrossRight :
      (((Twobites.paperKNat κ n - (C.redImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * Twobites.paperK δ n +
          (Twobites.paperK δ n) ^ 2 / 2) ≤
        ε1 *
          C.paperHugeBlueCrossRightTarget I κ (Twobites.paperCapNat β ε2 n))
    (hredCrossLeft :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) * Twobites.paperK δ n +
        (Twobites.paperK δ n) ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)))
    (hredCrossRight :
      (((Twobites.paperKNat κ n - (C.blueImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * Twobites.paperK δ n +
          (Twobites.paperK δ n) ^ 2 / 2) ≤
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
  have herror0 :
      (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤
        Twobites.paperK
          ((B * βdeg) / Twobites.paperS n +
            ((B ^ 2 / 2) * qcodeg) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n := by
    exact
      Twobites.cast_witnessError_le_paperK_of_real_bound
        hbound hβdeg hn hdegBound hcodegBound
  have herror :
      (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤
        Twobites.paperK δ n := by
    exact herror0.trans (Twobites.paperK_le_paperK_of_le hsplit)
  exact
    C.paper_huge_deterministic_of_witnessErrorBounds_of_realErrorBound
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight
      (lt_trans Nat.zero_lt_one hn) hρR hρB hβ hε2 hgapR hgapB hκR hκB hdiagRed hdiagBlue
      hε1 herror hblueCrossLeft hblueCrossRight hredCrossLeft hredCrossRight

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
    (hε1 : 0 ≤ ε1)
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
  have hW : 0 ≤ Twobites.paperK δ n := Twobites.paperK_nonneg hδ0 n
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
  have hblueCrossLeftCoeff :
      ((Twobites.paperKNat κ n - (C.redImage I).card : ℕ) : ℝ) * Twobites.paperK δ n +
        (Twobites.paperK δ n) ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.redImage I).card).choose 2 : ℕ) : ℝ)) := by
    exact
      real_mul_add_sq_half_le_eps_mul_choose_two_of_le_of_three_mul_le
        hW hblueLeftBound hblueLeftSmall
  have hblueCrossRightCoeff :
      (((Twobites.paperKNat κ n - (C.redImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * Twobites.paperK δ n +
          (Twobites.paperK δ n) ^ 2 / 2) ≤
        ε1 *
          C.paperHugeBlueCrossRightTarget I κ (Twobites.paperCapNat β ε2 n) := by
    unfold ConstructionData.paperHugeBlueCrossRightTarget
    exact
      real_mul_add_sq_half_le_eps_mul_choose_two_cap_add_choose_two_sub_of_le_of_three_mul_le
        hε1 hW hblueBound' hblueCrossSmall'
  have hredCrossLeftCoeff :
      ((Twobites.paperKNat κ n - (C.blueImage I).card : ℕ) : ℝ) * Twobites.paperK δ n +
        (Twobites.paperK δ n) ^ 2 / 2 ≤
        ε1 * ((((Twobites.paperKNat κ n - (C.blueImage I).card).choose 2 : ℕ) : ℝ)) := by
    exact
      real_mul_add_sq_half_le_eps_mul_choose_two_of_le_of_three_mul_le
        hW hredLeftBound hredLeftSmall
  have hredCrossRightCoeff :
      (((Twobites.paperKNat κ n - (C.blueImage I).card -
            Twobites.paperCapNat β ε2 n : ℕ) : ℝ) * Twobites.paperK δ n +
          (Twobites.paperK δ n) ^ 2 / 2) ≤
        ε1 *
          C.paperHugeRedCrossRightTarget I κ (Twobites.paperCapNat β ε2 n) := by
    unfold ConstructionData.paperHugeRedCrossRightTarget
    exact
      real_mul_add_sq_half_le_eps_mul_choose_two_cap_add_choose_two_sub_of_le_of_three_mul_le
        hε1 hW hredBound' hredCrossSmall'
  exact
    C.paper_huge_deterministic_of_witnessErrorBounds_of_coeffBound
      hD I hI hwitness hred hblue hblueCap hblueCapWeight hredCap hredCapWeight hn hρR
      hρB hβ hε2 hgapR hgapB hκR hκB hdiagRed hdiagBlue hε1 hbound hdegBound
      hcodegBound hsplit hblueCrossLeftCoeff hblueCrossRightCoeff hredCrossLeftCoeff
      hredCrossRightCoeff

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
    have hdivpos : 0 < 2 / η := by positivity
    linarith
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
    have hdivpos : 0 < 2 / ε1 := by positivity
    linarith
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
    have hdivpos : 0 < 2 / ε1 := by positivity
    linarith
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
    have hdivpos : 0 < 2 / ε1 := by positivity
    linarith
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
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
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
    have hdivpos : 0 < 2 / ε1 := by positivity
    linarith
  have hκloglog : 0 ≤ κ * Real.log (Real.log (n : ℝ)) := by
    exact mul_nonneg hκ0 hloglog.le
  have hB :
      (2 + ε1) * κ * Real.log (Real.log (n : ℝ)) ≤
        3 * κ * Real.log (Real.log (n : ℝ)) := by
    have hconst : 2 + ε1 ≤ 3 := by linarith
    nlinarith
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
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
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
    have htwo : (2 : ℝ) ≤ 2 / ε1 := by
      refine (le_div_iff₀ hε1pos).2 ?_
      nlinarith
    linarith
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
      hρB hβ hε2 hT1 hε1pos hε1le hloglogGap hε1 hdiagCoeff hsplit hsumGap
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
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
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
      hρB hβ hε2 hT1 hε1pos hε1le hloglogGap hε1 hdiagScale hsplit hsumGap
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
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
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
      hρB hβ hε2 hT1 hε1pos hε1le hloglogGap hε1 hdiagScale hcodegCoeff
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
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
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
      hredCapWeight hn hκ hρR hρB hβ hε2 hT1 hε1pos hε1le hloglogGap hε1 hdiagScale
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
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
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
      hredCapWeight hn hκ hρR hρB hβ hε2 hT1 hε1pos hε1le hloglogGap hε1 hdiagScale
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
    (hT1 : 2 < Twobites.paperT1 n) (hε1pos : 0 < ε1) (hε1le : ε1 ≤ 1)
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
      hβ hε2 hT1 hε1pos hε1le hloglogGap hε1 hdiagScale hcodegScale hsumGap hdegBound
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
