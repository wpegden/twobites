import Twobites.Construction
import Twobites.ParameterBounds
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Cast

namespace Twobites

open scoped BigOperators

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

/-- The total blue-projection weight `∑_{v ∈ A} |π_B(X_v(I))|`. -/
def blueProjectionWeight (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : ℕ :=
  ∑ x ∈ A, (C.blueProjectionImage I x).card

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

theorem redProjectionWeight_le_partWeight (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : C.redProjectionWeight I A ≤ C.partWeight I A := by
  unfold redProjectionWeight partWeight
  simpa using (Finset.sum_le_sum fun x _ => C.card_redProjectionImage_le_xCard I x)

theorem blueProjectionWeight_le_partWeight (C : ConstructionData n m) (I : Finset (Fin n))
    (A : Finset (BaseVertex m)) : C.blueProjectionWeight I A ≤ C.partWeight I A := by
  unfold blueProjectionWeight partWeight
  simpa using (Finset.sum_le_sum fun x _ => C.card_blueProjectionImage_le_xCard I x)

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
