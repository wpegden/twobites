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
