import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Real.Sqrt

namespace Twobites

noncomputable section

/-- The paper's scale parameter `s = log^2 n`, recorded as a real-valued abbreviation. -/
def paperS (n : ℕ) : ℝ :=
  Real.log (n : ℝ) ^ 2

/-- The paper's auxiliary base-graph size `m = n / s`, again kept as a real-valued abbreviation at
this stage so that the asymptotic inequalities can be stated directly. -/
def paperM (n : ℕ) : ℝ :=
  (n : ℝ) / paperS n

/-- The paper's random-edge parameter `p = β * sqrt(log n / n)`. -/
def paperP (β : ℝ) (n : ℕ) : ℝ :=
  β * Real.sqrt (Real.log (n : ℝ) / (n : ℝ))

/-- The huge-case projection cap `(1 + ε₂)pn` appearing in Lemma `lem:huge`. -/
def paperCap (β ε2 : ℝ) (n : ℕ) : ℝ :=
  (1 + ε2) * paperP β n * n

/-- The paper's target independent-set scale `k = κ * sqrt(n log n)`. -/
def paperK (κ : ℝ) (n : ℕ) : ℝ :=
  κ * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))

/-- Paper Section 3 threshold `t₁ = sqrt(n log n) / log log n`. -/
def paperT1 (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / Real.log (Real.log (n : ℝ))

/-- Paper Section 3 threshold `t₂ = n^(1/4 + ε)`. -/
def paperT2 (ε : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) ((1 / 4 : ℝ) + ε)

/-- Paper Section 3 threshold `t₃ = n^(2ε)`. -/
def paperT3 (ε : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (2 * ε)

/-- A natural-number version of the paper's scale parameter, rounded up and forced to stay
positive so it can be used as a divisor in graph-size parameters. -/
def paperSNat (n : ℕ) : ℕ :=
  max 1 ⌈paperS n⌉₊

/-- The natural-number base-graph size used when the construction needs a genuine vertex count. -/
def paperMNat (n : ℕ) : ℕ :=
  n / paperSNat n

/-- A natural-number version of the paper's target independent-set scale. -/
def paperKNat (κ : ℝ) (n : ℕ) : ℕ :=
  ⌈paperK κ n⌉₊

def paperHugeWitnessNat (κ : ℝ) (n : ℕ) : ℕ :=
  ⌈2 * (paperK κ n / paperT1 n)⌉₊ + 1

/-- The huge-case witness contribution coming from the union-size / degree term. -/
def paperHugeWitnessDegreeCoeff (κ β : ℝ) (n : ℕ) : ℝ :=
  ((3 * κ * Real.log (Real.log (n : ℝ))) * β) / paperS n

/-- The huge-case witness contribution coming from the projected-codegree term. -/
def paperHugeWitnessCodegCoeff (κ q : ℝ) (n : ℕ) : ℝ :=
  ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * q) /
    Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))

/-- The Section 3 witness-error coefficient obtained from the huge-part union-size and
projected-codegree estimates. -/
def paperHugeWitnessCoeff (κ β q : ℝ) (n : ℕ) : ℝ :=
  paperHugeWitnessDegreeCoeff κ β n + paperHugeWitnessCodegCoeff κ q n

/-- The branch-deficit parameter attached to the union-size / degree witness term. -/
def paperHugeWitnessDegreeBranchParam (ε1 κ β : ℝ) (n : ℕ) : ℝ :=
  (3 / ε1) * paperHugeWitnessDegreeCoeff κ β n

/-- The branch-deficit parameter attached to the projected-codegree witness term. -/
def paperHugeWitnessCodegBranchParam (ε1 κ q : ℝ) (n : ℕ) : ℝ :=
  (3 / ε1) * paperHugeWitnessCodegCoeff κ q n

/-- The branch-deficit parameter obtained by dividing the exact Section 3 witness-error
coefficient by the smallness factor `ε₁ / 3`. -/
def paperHugeWitnessBranchParam (ε1 κ β q : ℝ) (n : ℕ) : ℝ :=
  (3 / ε1) * paperHugeWitnessCoeff κ β q n

/-- A natural-number version of the huge-case cap `(1 + ε₂)pn`. -/
def paperCapNat (β ε2 : ℝ) (n : ℕ) : ℕ :=
  ⌈paperCap β ε2 n⌉₊

theorem paperS_nonneg (n : ℕ) : 0 ≤ paperS n := by
  unfold paperS
  nlinarith [sq_nonneg (Real.log (n : ℝ))]

theorem paperS_pos {n : ℕ} (hn : 1 < n) : 0 < paperS n := by
  have hlog : 0 < Real.log (n : ℝ) := by
    have hcast : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    exact Real.log_pos hcast
  unfold paperS
  nlinarith [sq_pos_of_ne_zero hlog.ne']

theorem paperLog_pos {n : ℕ} (hn : 1 < n) : 0 < Real.log (n : ℝ) := by
  have hcast : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  exact Real.log_pos hcast

theorem paperM_nonneg (n : ℕ) : 0 ≤ paperM n := by
  unfold paperM
  exact div_nonneg (Nat.cast_nonneg n) (paperS_nonneg n)

theorem paperM_pos {n : ℕ} (hn : 1 < n) : 0 < paperM n := by
  unfold paperM
  have hn' : 0 < (n : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  exact div_pos hn' (paperS_pos hn)

theorem paperM_mul_paperS {n : ℕ} (hS : paperS n ≠ 0) :
    paperM n * paperS n = (n : ℝ) := by
  simpa [paperM] using (div_mul_cancel₀ (n : ℝ) hS)

theorem paperP_nonneg {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) : 0 ≤ paperP β n := by
  unfold paperP
  exact mul_nonneg hβ (Real.sqrt_nonneg _)

theorem paperCap_nonneg {β ε2 : ℝ} (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) (n : ℕ) :
    0 ≤ paperCap β ε2 n := by
  unfold paperCap
  have hfac : 0 ≤ 1 + ε2 := by
    linarith
  exact mul_nonneg (mul_nonneg hfac (paperP_nonneg hβ n)) (Nat.cast_nonneg n)

theorem paperP_pos {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 1 < n) : 0 < paperP β n := by
  unfold paperP
  refine mul_pos hβ ?_
  apply Real.sqrt_pos.2
  exact div_pos (paperLog_pos hn) (by exact_mod_cast (lt_trans Nat.zero_lt_one hn))

theorem paperP_mul_n_eq_paperK {β : ℝ} {n : ℕ} (hn : 0 < n) :
    paperP β n * n = paperK β n := by
  have hn' : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hn1)
  have hsqrt :
      Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) =
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    calc
      Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) =
          Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) * Real.sqrt ((n : ℝ) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hn'.le]
      _ = Real.sqrt ((Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) ^ 2) := by
            rw [← Real.sqrt_mul (div_nonneg hlog hn'.le) ((n : ℝ) ^ 2)]
      _ = Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
            congr 1
            field_simp [hn'.ne']
  calc
    paperP β n * n = β * (Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ)) := by
      unfold paperP
      ring
    _ = β * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by rw [hsqrt]
    _ = paperK β n := by rw [paperK]

theorem paperCap_eq_mul_paperK {β ε2 : ℝ} {n : ℕ} (hn : 0 < n) :
    paperCap β ε2 n = (1 + ε2) * paperK β n := by
  calc
    paperCap β ε2 n = (1 + ε2) * (paperP β n * n) := by
      unfold paperCap
      ring
    _ = (1 + ε2) * paperK β n := by rw [paperP_mul_n_eq_paperK hn]

theorem paperP_mul_paperM_eq_paperK_div_paperS {β : ℝ} {n : ℕ} (hn : 1 < n) :
    paperP β n * paperM n = paperK (β / paperS n) n := by
  have hn' : 0 < n := lt_trans Nat.zero_lt_one hn
  calc
    paperP β n * paperM n = paperP β n * ((n : ℝ) / paperS n) := by
      rw [paperM]
    _ = (paperP β n * n) / paperS n := by ring
    _ = paperK β n / paperS n := by rw [paperP_mul_n_eq_paperK hn']
    _ = paperK (β / paperS n) n := by
      unfold paperK
      ring

theorem mul_paperP_mul_paperM_eq_paperK_div_paperS {c β : ℝ} {n : ℕ} (hn : 1 < n) :
    c * (paperP β n * paperM n) = paperK (c * β / paperS n) n := by
  calc
    c * (paperP β n * paperM n) = c * paperK (β / paperS n) n := by
      rw [paperP_mul_paperM_eq_paperK_div_paperS hn]
    _ = paperK (c * β / paperS n) n := by
      unfold paperK
      ring

theorem cast_mul_le_paperK_of_le_of_le_paperP_mul_paperM
    {w bound degreeBound : ℕ} {β : ℝ} {n : ℕ}
    (hw : w ≤ bound) (hβ : 0 ≤ β) (hn : 1 < n)
    (hdegree : (degreeBound : ℝ) ≤ paperP β n * paperM n) :
    ((w * degreeBound : ℕ) : ℝ) ≤ paperK (((bound : ℕ) : ℝ) * β / paperS n) n := by
  have hw' : (w : ℝ) ≤ bound := by
    exact_mod_cast hw
  have hpm_nonneg : 0 ≤ paperP β n * paperM n := by
    exact mul_nonneg (paperP_nonneg hβ n) (paperM_nonneg n)
  calc
    ((w * degreeBound : ℕ) : ℝ) = (w : ℝ) * (degreeBound : ℝ) := by
      norm_num
    _ ≤ (bound : ℝ) * (degreeBound : ℝ) := by
      gcongr
    _ ≤ (bound : ℝ) * (paperP β n * paperM n) := by
      exact mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg bound)
    _ = paperK (((bound : ℕ) : ℝ) * β / paperS n) n := by
      simpa using mul_paperP_mul_paperM_eq_paperK_div_paperS (c := (bound : ℝ)) hn

theorem nonneg_of_natCast_le {a : ℕ} {x : ℝ} (h : (a : ℝ) ≤ x) : 0 ≤ x := by
  have ha : 0 ≤ (a : ℝ) := by positivity
  linarith

theorem nonneg_of_le_paperP_mul_paperM
    {degreeBound : ℕ} {β : ℝ} {n : ℕ} (hn : 1 < n)
    (hdegree : (degreeBound : ℝ) ≤ paperP β n * paperM n) : 0 ≤ β := by
  have hpm_nonneg : 0 ≤ paperP β n * paperM n := by
    exact nonneg_of_natCast_le hdegree
  have hm : 0 < paperM n := paperM_pos hn
  have hp_nonneg : 0 ≤ paperP β n := by
    by_contra hp
    have hpneg : paperP β n < 0 := lt_of_not_ge hp
    have hprod_neg : paperP β n * paperM n < 0 := mul_neg_of_neg_of_pos hpneg hm
    linarith
  have hsqrt :
      0 < Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) := by
    apply Real.sqrt_pos.2
    exact div_pos (paperLog_pos hn) (by exact_mod_cast (lt_trans Nat.zero_lt_one hn))
  by_contra hβ
  have hβneg : β < 0 := lt_of_not_ge hβ
  have hpneg : paperP β n < 0 := by
    unfold paperP
    exact mul_neg_of_neg_of_pos hβneg hsqrt
  linarith

theorem paperK_ratio_eq {x : ℝ} {n : ℕ} (hn : 1 < n) :
    paperK (x / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n = x := by
  let s : ℝ := Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
  have hs : 0 < s := by
    dsimp [s]
    apply Real.sqrt_pos.2
    exact mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hn)) (paperLog_pos hn)
  calc
    paperK (x / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n = (x / s) * s := by
      simp [paperK, s]
    _ = x := by
      field_simp [hs.ne']

theorem cast_choose_mul_le_paperK_of_le_of_le
    {w bound projCodegreeBound : ℕ} {q : ℝ} {n : ℕ}
    (hw : w ≤ bound) (hn : 1 < n)
    (hproj : (projCodegreeBound : ℝ) ≤ q) :
    ((w.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
      paperK ((((bound.choose 2 : ℕ) : ℝ) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n := by
  have hchoose : w.choose 2 ≤ bound.choose 2 := Nat.choose_le_choose 2 hw
  calc
    ((w.choose 2 * projCodegreeBound : ℕ) : ℝ) = (w.choose 2 : ℝ) * (projCodegreeBound : ℝ) := by
      norm_num
    _ ≤ (bound.choose 2 : ℝ) * (projCodegreeBound : ℝ) := by
      gcongr
    _ ≤ (bound.choose 2 : ℝ) * q := by
      exact mul_le_mul_of_nonneg_left hproj (by positivity)
    _ = paperK ((((bound.choose 2 : ℕ) : ℝ) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n := by
      rw [paperK_ratio_eq hn]

theorem cast_choose_mul_le_paperK_of_real_bound
    {w projCodegreeBound : ℕ} {B q : ℝ} {n : ℕ}
    (hB : (w : ℝ) ≤ B) (hn : 1 < n)
    (hproj : (projCodegreeBound : ℝ) ≤ q) :
    ((w.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
      paperK (((B ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n := by
  have hchoose : (w.choose 2 : ℝ) ≤ B ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith [hB]
  calc
    ((w.choose 2 * projCodegreeBound : ℕ) : ℝ) = (w.choose 2 : ℝ) * (projCodegreeBound : ℝ) := by
      norm_num
    _ ≤ (B ^ 2 / 2) * (projCodegreeBound : ℝ) := by
      gcongr
    _ ≤ (B ^ 2 / 2) * q := by
      exact mul_le_mul_of_nonneg_left hproj (by positivity)
    _ = paperK (((B ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n := by
      rw [paperK_ratio_eq hn]

theorem choose_mul_le_paperKNat_of_real_bound
    {w projCodegreeBound : ℕ} {B q : ℝ} {n : ℕ}
    (hB : (w : ℝ) ≤ B) (hn : 1 < n)
    (hproj : (projCodegreeBound : ℝ) ≤ q) :
    w.choose 2 * projCodegreeBound ≤
      paperKNat (((B ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n := by
  unfold paperKNat
  exact_mod_cast
    (cast_choose_mul_le_paperK_of_real_bound hB hn hproj).trans (Nat.le_ceil _)

theorem paperK_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) : 0 ≤ paperK κ n := by
  unfold paperK
  exact mul_nonneg hκ (Real.sqrt_nonneg _)

theorem nonneg_of_paperK_nonneg {κ : ℝ} {n : ℕ} (hn : 1 < n)
    (hκ : 0 ≤ paperK κ n) : 0 ≤ κ := by
  by_contra hneg
  have hκneg : κ < 0 := lt_of_not_ge hneg
  have hsqrt :
      0 < Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    apply Real.sqrt_pos.2
    exact mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hn)) (paperLog_pos hn)
  unfold paperK at hκ
  have hprod : κ * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) < 0 :=
    mul_neg_of_neg_of_pos hκneg hsqrt
  linarith

theorem nonneg_of_one_le_paperK {κ : ℝ} {n : ℕ} (hn : 1 < n)
    (hκ : 1 ≤ paperK κ n) : 0 ≤ κ := by
  apply nonneg_of_paperK_nonneg hn
  linarith

theorem splitCoeff_nonneg {bound n : ℕ} {β q : ℝ} (hβ : 0 ≤ β) (hq : 0 ≤ q) :
    0 ≤ (((bound : ℕ) : ℝ) * β) / paperS n +
      ((((bound.choose 2 : ℕ) : ℝ) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
  refine add_nonneg ?_ ?_
  · exact div_nonneg (mul_nonneg (by positivity) hβ) (paperS_nonneg n)
  · exact div_nonneg (mul_nonneg (by positivity) hq) (Real.sqrt_nonneg _)

theorem cast_choose_two_le_sq_div_two (b : ℕ) :
    ((b.choose 2 : ℕ) : ℝ) ≤ (b : ℝ) ^ 2 / 2 := by
  rw [Nat.cast_choose_two]
  have hmul : (b : ℝ) * ((b : ℝ) - 1) ≤ (b : ℝ) ^ 2 := by
    nlinarith
  have htwo : (0 : ℝ) < 2 := by norm_num
  exact div_le_div_of_nonneg_right hmul (le_of_lt htwo)

theorem splitCoeff_le_of_bound_le {bound n : ℕ} {β q B : ℝ}
    (hn : 1 < n) (hbound : (bound : ℝ) ≤ B) (hβ : 0 ≤ β) (hq : 0 ≤ q) :
    (((bound : ℕ) : ℝ) * β) / paperS n +
        ((((bound.choose 2 : ℕ) : ℝ) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      (B * β) / paperS n + ((B ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  have hs : 0 < paperS n := paperS_pos hn
  have hsqrt : 0 < Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    apply Real.sqrt_pos.2
    exact mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hn)) (paperLog_pos hn)
  have hfirst :
      (((bound : ℕ) : ℝ) * β) / paperS n ≤ (B * β) / paperS n := by
    exact (div_le_div_iff₀ hs hs).2 <| by
      nlinarith [mul_le_mul_of_nonneg_right hbound hβ]
  have hchoose :
      ((bound.choose 2 : ℕ) : ℝ) ≤ B ^ 2 / 2 := by
    refine (cast_choose_two_le_sq_div_two bound).trans ?_
    have hsquare : (bound : ℝ) ^ 2 ≤ B ^ 2 := by
      nlinarith [sq_nonneg (B - (bound : ℝ))]
    nlinarith
  have hsecond :
      ((((bound.choose 2 : ℕ) : ℝ) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        ((B ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    exact (div_le_div_iff₀ hsqrt hsqrt).2 <| by
      nlinarith [mul_le_mul_of_nonneg_right hchoose hq]
  linarith

theorem diagCoeffTerm_le_of_le {κ β B₁ B₂ : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hB : B₁ ≤ B₂) :
    (B₁ * β / paperS n) * (paperK κ n + 1) ≤
      (B₂ * β / paperS n) * (paperK κ n + 1) := by
  have hfac : 0 ≤ (β / paperS n) * (paperK κ n + 1) := by
    refine mul_nonneg ?_ ?_
    · exact div_nonneg hβ (paperS_nonneg n)
    · have hk : 0 ≤ paperK κ n := paperK_nonneg hκ n
      linarith
  calc
    (B₁ * β / paperS n) * (paperK κ n + 1) =
        B₁ * ((β / paperS n) * (paperK κ n + 1)) := by ring
    _ ≤ B₂ * ((β / paperS n) * (paperK κ n + 1)) := by
      exact mul_le_mul_of_nonneg_right hB hfac
    _ = (B₂ * β / paperS n) * (paperK κ n + 1) := by ring

theorem splitCoeffReal_le_of_le {β q B₁ B₂ : ℝ} {n : ℕ}
    (hB₁ : 0 ≤ B₁) (hB : B₁ ≤ B₂) (hβ : 0 ≤ β) (hq : 0 ≤ q) :
    (B₁ * β) / paperS n + ((B₁ ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      (B₂ * β) / paperS n + ((B₂ ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  have hfirst : (B₁ * β) / paperS n ≤ (B₂ * β) / paperS n := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB hβ) (paperS_nonneg n)
  have hsq : B₁ ^ 2 ≤ B₂ ^ 2 := by
    nlinarith
  have hsecond :
      ((B₁ ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        ((B₂ ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_right (by nlinarith) hq
  linarith

theorem cast_witnessError_le_paperK_of_real_bound
    {witnessSize degreeBound projCodegreeBound : ℕ} {B β q : ℝ} {n : ℕ}
    (hB : (witnessSize : ℝ) ≤ B) (hβ : 0 ≤ β) (hn : 1 < n)
    (hdegree : (degreeBound : ℝ) ≤ paperP β n * paperM n)
    (hproj : (projCodegreeBound : ℝ) ≤ q) :
    (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) ≤
      paperK ((B * β) / paperS n +
        ((B ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n := by
  have hdegreePart :
      ((witnessSize * degreeBound : ℕ) : ℝ) ≤
        paperK (((witnessSize : ℝ) * β) / paperS n) n := by
    simpa using
      (cast_mul_le_paperK_of_le_of_le_paperP_mul_paperM
        (w := witnessSize) (bound := witnessSize) (degreeBound := degreeBound)
        (β := β) (n := n) (le_rfl : witnessSize ≤ witnessSize) hβ hn hdegree)
  have hdegreeCoeff :
      ((witnessSize : ℝ) * β) / paperS n ≤ (B * β) / paperS n := by
    exact
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB hβ) (paperS_nonneg n)
  have hdegreePartB :
      ((witnessSize * degreeBound : ℕ) : ℝ) ≤ paperK ((B * β) / paperS n) n :=
    hdegreePart.trans <| by
      unfold paperK
      exact mul_le_mul_of_nonneg_right hdegreeCoeff (Real.sqrt_nonneg _)
  have hcodegPart :
      ((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) ≤
        paperK (((B ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n :=
    cast_choose_mul_le_paperK_of_real_bound hB hn hproj
  calc
    (((witnessSize * degreeBound + witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ)) =
        ((witnessSize * degreeBound : ℕ) : ℝ) +
          ((witnessSize.choose 2 * projCodegreeBound : ℕ) : ℝ) := by
      norm_num
    _ ≤ paperK ((B * β) / paperS n) n +
          paperK (((B ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n := by
      gcongr
    _ = paperK ((B * β) / paperS n +
          ((B ^ 2 / 2) * q) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) n := by
      unfold paperK
      ring

theorem paperK_le_paperK_of_le {κ₁ κ₂ : ℝ} {n : ℕ} (hκ : κ₁ ≤ κ₂) :
    paperK κ₁ n ≤ paperK κ₂ n := by
  unfold paperK
  exact mul_le_mul_of_nonneg_right hκ (Real.sqrt_nonneg _)

theorem paperKNat_le_paperKNat_of_le {κ₁ κ₂ : ℝ} {n : ℕ} (hκ : κ₁ ≤ κ₂) :
    paperKNat κ₁ n ≤ paperKNat κ₂ n := by
  apply Nat.ceil_le.2
  exact (paperK_le_paperK_of_le hκ).trans (Nat.le_ceil _)

theorem natCeil_add_natCeil_le_natCeil_add_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ⌈a⌉₊ + ⌈b⌉₊ ≤ ⌈a + b⌉₊ + 1 := by
  have hlt :
      ((⌈a⌉₊ + ⌈b⌉₊ : ℕ) : ℝ) < ((⌈a + b⌉₊ + 2 : ℕ) : ℝ) := by
    calc
      ((⌈a⌉₊ + ⌈b⌉₊ : ℕ) : ℝ) = (⌈a⌉₊ : ℝ) + (⌈b⌉₊ : ℝ) := by
        norm_num
      _ < (a + 1) + (b + 1) := by
        nlinarith [Nat.ceil_lt_add_one ha, Nat.ceil_lt_add_one hb]
      _ = a + b + 2 := by ring
      _ ≤ (⌈a + b⌉₊ : ℝ) + 2 := by
        gcongr
        exact Nat.le_ceil (a + b)
      _ = ((⌈a + b⌉₊ + 2 : ℕ) : ℝ) := by
        norm_num
  have hlt_nat : ⌈a⌉₊ + ⌈b⌉₊ < ⌈a + b⌉₊ + 2 := by
    exact_mod_cast hlt
  omega

theorem paperT2_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ paperT2 ε n := by
  unfold paperT2
  exact Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem paperT3_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ paperT3 ε n := by
  unfold paperT3
  exact Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem paperT1_nonneg_of_loglog_nonneg {n : ℕ}
    (hloglog : 0 ≤ Real.log (Real.log (n : ℝ))) : 0 ≤ paperT1 n := by
  unfold paperT1
  exact div_nonneg (Real.sqrt_nonneg _) hloglog

theorem paperT1_mul_loglog_eq_sqrt {n : ℕ}
    (hloglog : Real.log (Real.log (n : ℝ)) ≠ 0) :
    paperT1 n * Real.log (Real.log (n : ℝ)) = Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  unfold paperT1
  field_simp [hloglog]

theorem paperK_eq_mul_loglog_mul_paperT1 {κ : ℝ} {n : ℕ}
    (hloglog : Real.log (Real.log (n : ℝ)) ≠ 0) :
    paperK κ n = κ * Real.log (Real.log (n : ℝ)) * paperT1 n := by
  rw [paperK, ← paperT1_mul_loglog_eq_sqrt hloglog]
  ring

theorem paperK_div_paperT1_eq_mul_loglog {κ : ℝ} {n : ℕ}
    (hn : 1 < n) (hloglog : 0 < Real.log (Real.log (n : ℝ))) :
    paperK κ n / paperT1 n = κ * Real.log (Real.log (n : ℝ)) := by
  have hsqrt :
      0 < Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    apply Real.sqrt_pos.2
    exact mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hn)) (paperLog_pos hn)
  have hT1 : 0 < paperT1 n := by
    unfold paperT1
    exact div_pos hsqrt hloglog
  apply (div_eq_iff hT1.ne').2
  exact paperK_eq_mul_loglog_mul_paperT1 hloglog.ne'

theorem le_mul_mul_loglog_of_le_mul_paperK_div_paperT1 {x a κ : ℝ} {n : ℕ}
    (h : x ≤ a * (paperK κ n / paperT1 n))
    (hn : 1 < n) (hloglog : 0 < Real.log (Real.log (n : ℝ))) :
    x ≤ a * κ * Real.log (Real.log (n : ℝ)) := by
  rw [paperK_div_paperT1_eq_mul_loglog hn hloglog] at h
  simpa [mul_assoc] using h

theorem two_le_mul_of_two_div_le {η x : ℝ} (hη : 0 < η) (hx : 2 / η ≤ x) :
    2 ≤ η * x := by
  have hmul : η * (2 / η) ≤ η * x := by
    exact mul_le_mul_of_nonneg_left hx hη.le
  have hleft : η * (2 / η) = 2 := by
    field_simp [hη.ne']
  linarith

theorem two_le_eta_mul_mul_loglog_of_two_div_loglog_le {κ η : ℝ} {n : ℕ}
    (hκ : 1 ≤ κ) (hη : 0 < η)
    (hloglog : 2 / η ≤ Real.log (Real.log (n : ℝ))) :
    2 ≤ η * (κ * Real.log (Real.log (n : ℝ))) := by
  have hllpos : 0 < Real.log (Real.log (n : ℝ)) := by
    have hdivpos : 0 < 2 / η := by positivity
    linarith
  have hbase : 2 ≤ η * Real.log (Real.log (n : ℝ)) :=
    two_le_mul_of_two_div_le hη hloglog
  have hmono : η * Real.log (Real.log (n : ℝ)) ≤ η * (κ * Real.log (Real.log (n : ℝ))) := by
    gcongr
    nlinarith
  exact hbase.trans hmono

theorem two_le_eta_mul_paperK_div_paperT1_of_two_div_loglog_le {κ η : ℝ} {n : ℕ}
    (hn : 1 < n) (hκ : 1 ≤ κ) (hη : 0 < η)
    (hloglog : 2 / η ≤ Real.log (Real.log (n : ℝ))) :
    2 ≤ η * (paperK κ n / paperT1 n) := by
  have hllpos : 0 < Real.log (Real.log (n : ℝ)) := by
    have hdivpos : 0 < 2 / η := by positivity
    linarith
  rw [paperK_div_paperT1_eq_mul_loglog hn hllpos]
  exact two_le_eta_mul_mul_loglog_of_two_div_loglog_le hκ hη hloglog

theorem paperK_pos {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : 1 < n) : 0 < paperK κ n := by
  unfold paperK
  refine mul_pos hκ ?_
  apply Real.sqrt_pos.2
  exact mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hn)) (paperLog_pos hn)

theorem paperT2_pos (ε : ℝ) {n : ℕ} (hn : 0 < n) : 0 < paperT2 ε n := by
  unfold paperT2
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem paperT3_pos (ε : ℝ) {n : ℕ} (hn : 0 < n) : 0 < paperT3 ε n := by
  unfold paperT3
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem paperT3_le_paperT2 {ε : ℝ} {n : ℕ} (hn : 1 ≤ n) (hε : ε ≤ (1 / 4 : ℝ)) :
    paperT3 ε n ≤ paperT2 ε n := by
  unfold paperT3 paperT2
  have hx : 1 ≤ (n : ℝ) := by
    exact_mod_cast hn
  apply Real.rpow_le_rpow_of_exponent_le hx
  linarith

theorem paperT1_le_paperK_one {n : ℕ} (hloglog : 1 ≤ Real.log (Real.log (n : ℝ))) :
    paperT1 n ≤ paperK 1 n := by
  unfold paperT1 paperK
  have hden : 0 < Real.log (Real.log (n : ℝ)) := by
    linarith
  have hsqrt : 0 ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := Real.sqrt_nonneg _
  have hdiv :
      Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / Real.log (Real.log (n : ℝ)) ≤
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 1 := by
    rw [div_one]
    exact (div_le_iff₀ hden).2 <| by
      simpa [one_mul] using mul_le_mul_of_nonneg_left hloglog hsqrt
  simpa using hdiv

theorem paperK_one_le_paperK {κ : ℝ} {n : ℕ} (hκ : 1 ≤ κ) : paperK 1 n ≤ paperK κ n := by
  unfold paperK
  have hsqrt : 0 ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_right hκ hsqrt

theorem paperT1_le_paperK {κ : ℝ} {n : ℕ}
    (hloglog : 1 ≤ Real.log (Real.log (n : ℝ))) (hκ : 1 ≤ κ) : paperT1 n ≤ paperK κ n := by
  exact (paperT1_le_paperK_one hloglog).trans (paperK_one_le_paperK hκ)

theorem paperT2_le_paperK {ε κ : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ)) (hε : ε ≤ (1 / 4 : ℝ)) (hκ : 1 ≤ κ) :
    paperT2 ε n ≤ paperK κ n := by
  have hn' : 1 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg hn'
  calc
    paperT2 ε n = (n : ℝ) ^ ((1 / 4 : ℝ) + ε) := by
      rfl
    _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hn'
      linarith
    _ = Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      apply Real.sqrt_le_sqrt
      have hn0 : 0 ≤ (n : ℝ) := by
        positivity
      nlinarith
    _ ≤ κ * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      have hsqrt : 0 ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := Real.sqrt_nonneg _
      nlinarith
    _ = paperK κ n := by
      rw [paperK]

theorem ceil_paperT1_le_paperKNat {κ : ℝ} {n : ℕ}
    (hloglog : 1 ≤ Real.log (Real.log (n : ℝ))) (hκ : 1 ≤ κ) :
    ⌈paperT1 n⌉₊ ≤ paperKNat κ n := by
  exact (Nat.ceil_le).2 <| (paperT1_le_paperK hloglog hκ).trans (Nat.le_ceil (paperK κ n))

theorem ceil_paperT2_le_paperKNat {ε κ : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hlog : 1 ≤ Real.log (n : ℝ)) (hε : ε ≤ (1 / 4 : ℝ)) (hκ : 1 ≤ κ) :
    ⌈paperT2 ε n⌉₊ ≤ paperKNat κ n := by
  exact (Nat.ceil_le).2 <| (paperT2_le_paperK hn hlog hε hκ).trans (Nat.le_ceil (paperK κ n))

theorem ceil_paperT3_le_ceil_paperT2 {ε : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hε : ε ≤ (1 / 4 : ℝ)) : ⌈paperT3 ε n⌉₊ ≤ ⌈paperT2 ε n⌉₊ := by
  apply Nat.ceil_le.2
  exact (paperT3_le_paperT2 hn hε).trans (Nat.le_ceil _)

theorem paperT2_le_paperT1_of_loglog_le {ε : ℝ} {n : ℕ} (hn : 0 < n)
    (hlog : 0 ≤ Real.log (n : ℝ)) (hloglog : 0 < Real.log (Real.log (n : ℝ)))
    (hbound :
      Real.log (Real.log (n : ℝ)) ≤
        (n : ℝ) ^ ((1 / 4 : ℝ) - ε) * Real.sqrt (Real.log (n : ℝ))) :
    paperT2 ε n ≤ paperT1 n := by
  have hn' : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hmul :
      paperT2 ε n * Real.log (Real.log (n : ℝ)) ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    have hrpow :
        (n : ℝ) ^ ((1 / 4 : ℝ) + ε) * (n : ℝ) ^ ((1 / 4 : ℝ) - ε) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hn']
      congr 1
      linarith
    calc
      paperT2 ε n * Real.log (Real.log (n : ℝ))
          ≤ paperT2 ε n * ((n : ℝ) ^ ((1 / 4 : ℝ) - ε) * Real.sqrt (Real.log (n : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hbound (paperT2_nonneg ε n)
      _ = Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
        unfold paperT2
        rw [← mul_assoc]
        change (n : ℝ) ^ ((1 / 4 : ℝ) + ε) * (n : ℝ) ^ ((1 / 4 : ℝ) - ε) *
            Real.sqrt (Real.log (n : ℝ)) = Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
        rw [hrpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
          ← Real.mul_rpow (Nat.cast_nonneg n) hlog]
  unfold paperT1
  exact (le_div_iff₀ hloglog).2 hmul

theorem ceil_paperT2_le_ceil_paperT1_of_loglog_le {ε : ℝ} {n : ℕ} (hn : 0 < n)
    (hlog : 0 ≤ Real.log (n : ℝ)) (hloglog : 0 < Real.log (Real.log (n : ℝ)))
    (hbound :
      Real.log (Real.log (n : ℝ)) ≤
        (n : ℝ) ^ ((1 / 4 : ℝ) - ε) * Real.sqrt (Real.log (n : ℝ))) :
    ⌈paperT2 ε n⌉₊ ≤ ⌈paperT1 n⌉₊ := by
  apply Nat.ceil_le.2
  exact (paperT2_le_paperT1_of_loglog_le hn hlog hloglog hbound).trans (Nat.le_ceil _)

theorem ceil_paperT1_lt_paperT1_add_one {n : ℕ} (hT1 : 0 ≤ paperT1 n) :
    (⌈paperT1 n⌉₊ : ℝ) < paperT1 n + 1 := by
  exact Nat.ceil_lt_add_one hT1

theorem ceil_paperT1_le_paperT1_add_one {n : ℕ} (hT1 : 0 ≤ paperT1 n) :
    (⌈paperT1 n⌉₊ : ℝ) ≤ paperT1 n + 1 := by
  exact (ceil_paperT1_lt_paperT1_add_one hT1).le

theorem ceil_paperT2_lt_paperT2_add_one (ε : ℝ) (n : ℕ) :
    (⌈paperT2 ε n⌉₊ : ℝ) < paperT2 ε n + 1 := by
  exact Nat.ceil_lt_add_one (paperT2_nonneg ε n)

theorem ceil_paperT2_le_paperT2_add_one (ε : ℝ) (n : ℕ) :
    (⌈paperT2 ε n⌉₊ : ℝ) ≤ paperT2 ε n + 1 := by
  exact (ceil_paperT2_lt_paperT2_add_one ε n).le

theorem ceil_paperT3_lt_paperT3_add_one (ε : ℝ) (n : ℕ) :
    (⌈paperT3 ε n⌉₊ : ℝ) < paperT3 ε n + 1 := by
  exact Nat.ceil_lt_add_one (paperT3_nonneg ε n)

theorem ceil_paperT3_le_paperT3_add_one (ε : ℝ) (n : ℕ) :
    (⌈paperT3 ε n⌉₊ : ℝ) ≤ paperT3 ε n + 1 := by
  exact (ceil_paperT3_lt_paperT3_add_one ε n).le

theorem paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_iff
    {κ : ℝ} {n witnessSize codegreeBound : ℕ} :
    paperKNat κ n < witnessSize * ⌈paperT1 n⌉₊ - witnessSize.choose 2 * codegreeBound ↔
      paperKNat κ n + witnessSize.choose 2 * codegreeBound < witnessSize * ⌈paperT1 n⌉₊ :=
  Nat.lt_sub_iff_add_lt

theorem paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_of_two_mul_lt
    {κ : ℝ} {n witnessSize codegreeBound : ℕ}
    (htwo : 2 * paperKNat κ n < witnessSize * ⌈paperT1 n⌉₊)
    (hchoose : witnessSize.choose 2 * codegreeBound ≤ paperKNat κ n) :
    paperKNat κ n < witnessSize * ⌈paperT1 n⌉₊ - witnessSize.choose 2 * codegreeBound := by
  rw [paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_iff]
  omega

theorem paperHugeWitnessNat_lt_two_mul_paperK_div_paperT1_add_two {κ : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hT1 : 0 < paperT1 n) :
    (paperHugeWitnessNat κ n : ℝ) < 2 * (paperK κ n / paperT1 n) + 2 := by
  have hratio : 0 ≤ 2 * (paperK κ n / paperT1 n) := by
    have hk : 0 ≤ paperK κ n := paperK_nonneg hκ n
    have hdiv : 0 ≤ paperK κ n / paperT1 n := div_nonneg hk hT1.le
    nlinarith
  have hceil :
      ((⌈2 * (paperK κ n / paperT1 n)⌉₊ : ℕ) : ℝ) <
        2 * (paperK κ n / paperT1 n) + 1 := Nat.ceil_lt_add_one hratio
  calc
    (paperHugeWitnessNat κ n : ℝ) = (⌈2 * (paperK κ n / paperT1 n)⌉₊ : ℝ) + 1 := by
      unfold paperHugeWitnessNat
      norm_num
    _ < (2 * (paperK κ n / paperT1 n) + 1) + 1 := by linarith
    _ = 2 * (paperK κ n / paperT1 n) + 2 := by ring

theorem paperHugeWitnessNat_le_two_mul_paperK_div_paperT1_add_two {κ : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hT1 : 0 < paperT1 n) :
    (paperHugeWitnessNat κ n : ℝ) ≤ 2 * (paperK κ n / paperT1 n) + 2 := by
  exact (paperHugeWitnessNat_lt_two_mul_paperK_div_paperT1_add_two hκ hT1).le

theorem paperHugeWitnessNat_le_two_mul_mul_loglog_add_two {κ : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hn : 1 < n) (hloglog : 0 < Real.log (Real.log (n : ℝ))) :
    (paperHugeWitnessNat κ n : ℝ) ≤ 2 * κ * Real.log (Real.log (n : ℝ)) + 2 := by
  have hT1 : 0 < paperT1 n := by
    unfold paperT1
    refine div_pos ?_ hloglog
    apply Real.sqrt_pos.2
    exact mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hn)) (paperLog_pos hn)
  calc
    (paperHugeWitnessNat κ n : ℝ) ≤ 2 * (paperK κ n / paperT1 n) + 2 := by
      exact paperHugeWitnessNat_le_two_mul_paperK_div_paperT1_add_two hκ hT1
    _ = 2 * κ * Real.log (Real.log (n : ℝ)) + 2 := by
      rw [paperK_div_paperT1_eq_mul_loglog hn hloglog]
      ring

theorem paperHugeWitnessNat_le_two_add_eta_mul_paperK_div_paperT1 {κ η : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hT1 : 0 < paperT1 n)
    (hgap : 2 ≤ η * (paperK κ n / paperT1 n)) :
    (paperHugeWitnessNat κ n : ℝ) ≤ (2 + η) * (paperK κ n / paperT1 n) := by
  have hratio : 0 ≤ paperK κ n / paperT1 n := by
    exact div_nonneg (paperK_nonneg hκ n) hT1.le
  calc
    (paperHugeWitnessNat κ n : ℝ) ≤ 2 * (paperK κ n / paperT1 n) + 2 := by
      exact paperHugeWitnessNat_le_two_mul_paperK_div_paperT1_add_two hκ hT1
    _ ≤ 2 * (paperK κ n / paperT1 n) + η * (paperK κ n / paperT1 n) := by
      linarith
    _ = (2 + η) * (paperK κ n / paperT1 n) := by ring

theorem paperHugeWitnessNat_le_two_add_eta_mul_mul_loglog {κ η : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hn : 1 < n) (hloglog : 0 < Real.log (Real.log (n : ℝ)))
    (hgap : 2 ≤ η * (κ * Real.log (Real.log (n : ℝ)))) :
    (paperHugeWitnessNat κ n : ℝ) ≤ (2 + η) * κ * Real.log (Real.log (n : ℝ)) := by
  have hT1 : 0 < paperT1 n := by
    unfold paperT1
    refine div_pos ?_ hloglog
    apply Real.sqrt_pos.2
    exact mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hn)) (paperLog_pos hn)
  have hgap' : 2 ≤ η * (paperK κ n / paperT1 n) := by
    simpa [paperK_div_paperT1_eq_mul_loglog hn hloglog, mul_assoc] using hgap
  calc
    (paperHugeWitnessNat κ n : ℝ) ≤ (2 + η) * (paperK κ n / paperT1 n) := by
      exact paperHugeWitnessNat_le_two_add_eta_mul_paperK_div_paperT1 hκ hT1 hgap'
    _ = (2 + η) * κ * Real.log (Real.log (n : ℝ)) := by
      rw [paperK_div_paperT1_eq_mul_loglog hn hloglog]
      ring

theorem paperHugeWitnessNat_splitCoeff_le_of_loglog {κ β q : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hn : 1 < n) (hloglog : 0 < Real.log (Real.log (n : ℝ)))
    (hβ : 0 ≤ β) (hq : 0 ≤ q) :
    (((paperHugeWitnessNat κ n : ℕ) : ℝ) * β) / paperS n +
        ((((paperHugeWitnessNat κ n).choose 2 : ℕ) : ℝ) * q) /
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
      ((2 * κ * Real.log (Real.log (n : ℝ)) + 2) * β) / paperS n +
        (((2 * κ * Real.log (Real.log (n : ℝ)) + 2) ^ 2 / 2) * q) /
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  exact
    splitCoeff_le_of_bound_le (bound := paperHugeWitnessNat κ n) (n := n)
      hn (paperHugeWitnessNat_le_two_mul_mul_loglog_add_two hκ hn hloglog) hβ hq

theorem two_mul_paperKNat_lt_paperHugeWitnessNat_mul_ceil_paperT1 {κ : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hT1 : 2 < paperT1 n) :
    2 * paperKNat κ n < paperHugeWitnessNat κ n * ⌈paperT1 n⌉₊ := by
  have hT1pos : 0 < paperT1 n := by linarith
  have hwitnessLower :
      2 * (paperK κ n / paperT1 n) + 1 ≤ (paperHugeWitnessNat κ n : ℝ) := by
    have hceil :
        2 * (paperK κ n / paperT1 n) ≤ ((⌈2 * (paperK κ n / paperT1 n)⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    calc
      2 * (paperK κ n / paperT1 n) + 1 ≤ ((⌈2 * (paperK κ n / paperT1 n)⌉₊ : ℕ) : ℝ) + 1 := by
        linarith
      _ = (paperHugeWitnessNat κ n : ℝ) := by
        unfold paperHugeWitnessNat
        norm_num
  have hceilT1 : paperT1 n ≤ (⌈paperT1 n⌉₊ : ℝ) := Nat.le_ceil _
  have hprod :
      2 * paperK κ n + paperT1 n ≤
        ((paperHugeWitnessNat κ n * ⌈paperT1 n⌉₊ : ℕ) : ℝ) := by
    have hmul :
        (2 * (paperK κ n / paperT1 n) + 1) * paperT1 n ≤
          (paperHugeWitnessNat κ n : ℝ) * (⌈paperT1 n⌉₊ : ℝ) := by
      gcongr
    have hrewrite :
        (2 * (paperK κ n / paperT1 n) + 1) * paperT1 n =
          2 * paperK κ n + paperT1 n := by
      field_simp [hT1pos.ne']
    simpa [Nat.cast_mul] using hrewrite ▸ hmul
  have hceilk : ((2 * paperKNat κ n : ℕ) : ℝ) < 2 * paperK κ n + 2 := by
    have hk : (paperKNat κ n : ℝ) < paperK κ n + 1 := by
      exact Nat.ceil_lt_add_one (paperK_nonneg hκ n)
    calc
      ((2 * paperKNat κ n : ℕ) : ℝ) = 2 * (paperKNat κ n : ℝ) := by norm_num
      _ < 2 * (paperK κ n + 1) := by gcongr
      _ = 2 * paperK κ n + 2 := by ring
  have hlt :
      ((2 * paperKNat κ n : ℕ) : ℝ) <
        ((paperHugeWitnessNat κ n * ⌈paperT1 n⌉₊ : ℕ) : ℝ) := by
    have : ((2 * paperKNat κ n : ℕ) : ℝ) < 2 * paperK κ n + paperT1 n := by
      linarith
    exact this.trans_le hprod
  exact_mod_cast hlt

theorem paperKNat_lt_mul_ceil_paperT2_sub_choose_mul_iff
    {κ ε : ℝ} {n witnessSize codegreeBound : ℕ} :
    paperKNat κ n < witnessSize * ⌈paperT2 ε n⌉₊ - witnessSize.choose 2 * codegreeBound ↔
      paperKNat κ n + witnessSize.choose 2 * codegreeBound < witnessSize * ⌈paperT2 ε n⌉₊ :=
  Nat.lt_sub_iff_add_lt

theorem paperKNat_lt_mul_ceil_paperT3_sub_choose_mul_iff
    {κ ε : ℝ} {n witnessSize codegreeBound : ℕ} :
    paperKNat κ n < witnessSize * ⌈paperT3 ε n⌉₊ - witnessSize.choose 2 * codegreeBound ↔
      paperKNat κ n + witnessSize.choose 2 * codegreeBound < witnessSize * ⌈paperT3 ε n⌉₊ :=
  Nat.lt_sub_iff_add_lt

theorem one_le_paperSNat (n : ℕ) : 1 ≤ paperSNat n := by
  unfold paperSNat
  exact Nat.le_max_left _ _

theorem paperSNat_ne_zero (n : ℕ) : paperSNat n ≠ 0 := by
  exact Nat.ne_of_gt (Nat.succ_le_iff.mp (one_le_paperSNat n))

theorem paperS_le_paperSNat (n : ℕ) : paperS n ≤ paperSNat n := by
  have hceil : paperS n ≤ (⌈paperS n⌉₊ : ℝ) := Nat.le_ceil (paperS n)
  have hmax : ((⌈paperS n⌉₊ : ℕ) : ℝ) ≤ paperSNat n := by
    exact_mod_cast (Nat.le_max_right 1 ⌈paperS n⌉₊)
  exact hceil.trans hmax

theorem paperMNat_mul_paperSNat_le (n : ℕ) : paperMNat n * paperSNat n ≤ n := by
  unfold paperMNat
  exact Nat.div_mul_le_self n (paperSNat n)

theorem paperMNat_cast_le_div (n : ℕ) :
    (paperMNat n : ℝ) ≤ (n : ℝ) / paperSNat n := by
  unfold paperMNat
  simpa using (Nat.cast_div_le : ((n / paperSNat n : ℕ) : ℝ) ≤ n / paperSNat n)

theorem div_paperSNat_le_paperM {n : ℕ} (hn : 1 < n) :
    (n : ℝ) / paperSNat n ≤ paperM n := by
  unfold paperM
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (paperS_pos hn) (paperS_le_paperSNat n)

theorem paperMNat_le_paperM {n : ℕ} (hn : 1 < n) : (paperMNat n : ℝ) ≤ paperM n := by
  exact (paperMNat_cast_le_div n).trans (div_paperSNat_le_paperM hn)

theorem paperK_le_paperKNat (κ : ℝ) (n : ℕ) : paperK κ n ≤ paperKNat κ n := by
  unfold paperKNat
  exact Nat.le_ceil (paperK κ n)

theorem paperCap_le_paperCapNat (β ε2 : ℝ) (n : ℕ) : paperCap β ε2 n ≤ paperCapNat β ε2 n := by
  unfold paperCapNat
  exact Nat.le_ceil (paperCap β ε2 n)

theorem paperCapNat_lt_paperCap_add_one {β ε2 : ℝ}
    (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) (n : ℕ) :
    (paperCapNat β ε2 n : ℝ) < paperCap β ε2 n + 1 := by
  unfold paperCapNat
  exact Nat.ceil_lt_add_one (paperCap_nonneg hβ hε2 n)

theorem paperCapNat_le_paperCap_add_one {β ε2 : ℝ}
    (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) (n : ℕ) :
    (paperCapNat β ε2 n : ℝ) ≤ paperCap β ε2 n + 1 := by
  exact (paperCapNat_lt_paperCap_add_one hβ hε2 n).le

theorem paperCapNat_le_mul_paperK_add_one {β ε2 : ℝ} {n : ℕ}
    (hn : 0 < n) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) :
    (paperCapNat β ε2 n : ℝ) ≤ (1 + ε2) * paperK β n + 1 := by
  calc
    (paperCapNat β ε2 n : ℝ) ≤ paperCap β ε2 n + 1 := paperCapNat_le_paperCap_add_one hβ hε2 n
    _ = (1 + ε2) * paperK β n + 1 := by rw [paperCap_eq_mul_paperK hn]

theorem paperCap_eq_paperK_scaled {β ε2 : ℝ} {n : ℕ} (hn : 0 < n) :
    paperCap β ε2 n = paperK ((1 + ε2) * β) n := by
  calc
    paperCap β ε2 n = (1 + ε2) * paperK β n := paperCap_eq_mul_paperK hn
    _ = ((1 + ε2) * β) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      rw [paperK]
      ring
    _ = paperK ((1 + ε2) * β) n := by rw [paperK]

theorem paperCap_le_paperK_of_mul_le {β ε2 κ : ℝ} {n : ℕ} (hn : 0 < n)
    (hκ : (1 + ε2) * β ≤ κ) :
    paperCap β ε2 n ≤ paperK κ n := by
  rw [paperCap_eq_paperK_scaled hn]
  exact paperK_le_paperK_of_le hκ

theorem paperCapNat_le_paperKNat_of_mul_le {β ε2 κ : ℝ} {n : ℕ} (hn : 0 < n)
    (hκ : (1 + ε2) * β ≤ κ) :
    paperCapNat β ε2 n ≤ paperKNat κ n := by
  apply Nat.ceil_le.2
  exact (paperCap_le_paperK_of_mul_le hn hκ).trans (Nat.le_ceil _)

theorem paperK_add {κ₁ κ₂ : ℝ} (n : ℕ) :
    paperK κ₁ n + paperK κ₂ n = paperK (κ₁ + κ₂) n := by
  unfold paperK
  ring

theorem paperKNat_add_paperCapNat_le_paperKNat_add_one {ρ β ε2 : ℝ} {n : ℕ}
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2) :
    paperKNat ρ n + paperCapNat β ε2 n ≤ paperKNat (ρ + (1 + ε2) * β) n + 1 := by
  unfold paperKNat paperCapNat
  calc
    ⌈paperK ρ n⌉₊ + ⌈paperCap β ε2 n⌉₊ ≤ ⌈paperK ρ n + paperCap β ε2 n⌉₊ + 1 := by
      exact natCeil_add_natCeil_le_natCeil_add_one (paperK_nonneg hρ n) (paperCap_nonneg hβ hε2 n)
    _ = ⌈paperK (ρ + (1 + ε2) * β) n⌉₊ + 1 := by
      congr 1
      rw [paperCap_eq_paperK_scaled hn, paperK_add]

theorem paperKNat_add_paperKNat_le_paperKNat_add_one {ρ δ : ℝ} {n : ℕ}
    (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) :
    paperKNat ρ n + paperKNat δ n ≤ paperKNat (ρ + δ) n + 1 := by
  unfold paperKNat
  calc
    ⌈paperK ρ n⌉₊ + ⌈paperK δ n⌉₊ ≤ ⌈paperK ρ n + paperK δ n⌉₊ + 1 := by
      exact natCeil_add_natCeil_le_natCeil_add_one (paperK_nonneg hρ n) (paperK_nonneg hδ n)
    _ = ⌈paperK (ρ + δ) n⌉₊ + 1 := by
      congr 1
      rw [paperK_add]

theorem paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_add_two
    {ρ β ε2 δ : ℝ} {n : ℕ} (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β)
    (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ) :
    paperKNat ρ n + paperCapNat β ε2 n + paperKNat δ n ≤
      paperKNat (ρ + (1 + ε2) * β + δ) n + 2 := by
  have hcap :
      paperKNat ρ n + paperCapNat β ε2 n ≤
        paperKNat (ρ + (1 + ε2) * β) n + 1 := by
    exact paperKNat_add_paperCapNat_le_paperKNat_add_one hn hρ hβ hε2
  have hsum :
      paperKNat (ρ + (1 + ε2) * β) n + paperKNat δ n ≤
        paperKNat ((ρ + (1 + ε2) * β) + δ) n + 1 := by
    apply paperKNat_add_paperKNat_le_paperKNat_add_one
    · have hfac : 0 ≤ 1 + ε2 := by linarith
      exact add_nonneg hρ (mul_nonneg hfac hβ)
    · exact hδ
  calc
    paperKNat ρ n + paperCapNat β ε2 n + paperKNat δ n ≤
        (paperKNat (ρ + (1 + ε2) * β) n + 1) + paperKNat δ n := by
      exact Nat.add_le_add_right hcap (paperKNat δ n)
    _ = paperKNat (ρ + (1 + ε2) * β) n + paperKNat δ n + 1 := by
      omega
    _ ≤ paperKNat ((ρ + (1 + ε2) * β) + δ) n + 1 + 1 := by
      exact Nat.add_le_add_right hsum 1
    _ = paperKNat (ρ + (1 + ε2) * β + δ) n + 2 := by
      congr 1

theorem paperKNat_add_one_le_paperKNat_of_one_le_gap {σ δ : ℝ} {n : ℕ}
    (hσ : 0 ≤ σ) (hgap : 1 ≤ paperK δ n) :
    paperKNat σ n + 1 ≤ paperKNat (σ + δ) n := by
  unfold paperKNat
  rw [← Nat.ceil_add_one (paperK_nonneg hσ n)]
  apply Nat.ceil_le.2
  calc
    paperK σ n + 1 ≤ paperK σ n + paperK δ n := by linarith
    _ = paperK (σ + δ) n := by rw [paperK_add]
    _ ≤ (⌈paperK (σ + δ) n⌉₊ : ℝ) := by exact Nat.le_ceil _

theorem paperKNat_add_two_le_paperKNat_of_two_le_gap {σ δ : ℝ} {n : ℕ}
    (hσ : 0 ≤ σ) (hgap : 2 ≤ paperK δ n) :
    paperKNat σ n + 2 ≤ paperKNat (σ + δ) n := by
  unfold paperKNat
  rw [← Nat.ceil_add_natCast (paperK_nonneg hσ n) 2]
  apply Nat.ceil_le.2
  calc
    paperK σ n + 2 ≤ paperK σ n + paperK δ n := by linarith
    _ = paperK (σ + δ) n := by rw [paperK_add]
    _ ≤ (⌈paperK (σ + δ) n⌉₊ : ℝ) := by exact Nat.le_ceil _

theorem paperKNat_add_paperCapNat_le_paperKNat_of_one_le_gap {ρ β ε2 δ : ℝ} {n : ℕ}
    (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hgap : 1 ≤ paperK δ n) :
    paperKNat ρ n + paperCapNat β ε2 n ≤ paperKNat (ρ + (1 + ε2) * β + δ) n := by
  have hσ : 0 ≤ ρ + (1 + ε2) * β := by
    have hfac : 0 ≤ 1 + ε2 := by linarith
    have hcap : 0 ≤ (1 + ε2) * β := by exact mul_nonneg hfac hβ
    linarith
  calc
    paperKNat ρ n + paperCapNat β ε2 n ≤ paperKNat (ρ + (1 + ε2) * β) n + 1 := by
      exact paperKNat_add_paperCapNat_le_paperKNat_add_one hn hρ hβ hε2
    _ ≤ paperKNat ((ρ + (1 + ε2) * β) + δ) n := by
      exact paperKNat_add_one_le_paperKNat_of_one_le_gap hσ hgap
    _ = paperKNat (ρ + (1 + ε2) * β + δ) n := by ring_nf

theorem paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_of_two_le_gap
    {ρ β ε2 δ η : ℝ} {n : ℕ} (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β)
    (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ) (hgap : 2 ≤ paperK η n) :
    paperKNat ρ n + paperCapNat β ε2 n + paperKNat δ n ≤
      paperKNat (ρ + (1 + ε2) * β + δ + η) n := by
  have hσ : 0 ≤ ρ + (1 + ε2) * β + δ := by
    have hfac : 0 ≤ 1 + ε2 := by linarith
    exact add_nonneg (add_nonneg hρ (mul_nonneg hfac hβ)) hδ
  calc
    paperKNat ρ n + paperCapNat β ε2 n + paperKNat δ n ≤
        paperKNat (ρ + (1 + ε2) * β + δ) n + 2 := by
      exact paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_add_two hn hρ hβ hε2 hδ
    _ ≤ paperKNat ((ρ + (1 + ε2) * β + δ) + η) n := by
      exact paperKNat_add_two_le_paperKNat_of_two_le_gap hσ hgap
    _ = paperKNat (ρ + (1 + ε2) * β + δ + η) n := by ring_nf

theorem paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_of_two_le_gap_of_le
    {ρ β ε2 δ η κ : ℝ} {n : ℕ} (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β)
    (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ) (hgap : 2 ≤ paperK η n)
    (hκ : ρ + (1 + ε2) * β + δ + η ≤ κ) :
    paperKNat ρ n + paperCapNat β ε2 n + paperKNat δ n ≤ paperKNat κ n := by
  calc
    paperKNat ρ n + paperCapNat β ε2 n + paperKNat δ n ≤
        paperKNat (ρ + (1 + ε2) * β + δ + η) n := by
      exact paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_of_two_le_gap
        hn hρ hβ hε2 hδ hgap
    _ ≤ paperKNat κ n := by
      exact paperKNat_le_paperKNat_of_le hκ

theorem paperKNat_add_paperCapNat_add_paperKNat_add_one_le_paperKNat_of_gap1_gap2_of_le
    {ρ β ε2 δ δsumGap δgap κ : ℝ} {n : ℕ} (hn : 1 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β)
    (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ) (hsumGap : 1 ≤ paperK δsumGap n)
    (hgap : 2 ≤ paperK δgap n)
    (hκ : ρ + (1 + ε2) * β + δ + δsumGap + δgap ≤ κ) :
    paperKNat ρ n + paperCapNat β ε2 n + paperKNat δ n + 1 ≤ paperKNat κ n := by
  have hfac : 0 ≤ 1 + ε2 := by linarith
  have hδsumGap : 0 ≤ δsumGap := nonneg_of_one_le_paperK hn hsumGap
  have hδgap : 0 ≤ δgap := nonneg_of_one_le_paperK hn (by linarith [hgap])
  have hσ :
      0 ≤ ρ + (1 + ε2) * β + δ := by
    exact add_nonneg (add_nonneg hρ (mul_nonneg hfac hβ)) hδ
  have hσgap :
      0 ≤ ρ + (1 + ε2) * β + δ + δgap := by
    exact add_nonneg hσ hδgap
  have hbase :
      paperKNat ρ n + paperCapNat β ε2 n + paperKNat δ n ≤
        paperKNat (ρ + (1 + ε2) * β + δ) n + 2 := by
    exact paperKNat_add_paperCapNat_add_paperKNat_le_paperKNat_add_two
      (lt_trans Nat.zero_lt_one hn) hρ hβ hε2 hδ
  have hgapStep :
      paperKNat (ρ + (1 + ε2) * β + δ) n + 2 ≤
        paperKNat (ρ + (1 + ε2) * β + δ + δgap) n := by
    exact paperKNat_add_two_le_paperKNat_of_two_le_gap hσ hgap
  have hsumStep :
      paperKNat (ρ + (1 + ε2) * β + δ + δgap) n + 1 ≤
        paperKNat ((ρ + (1 + ε2) * β + δ + δgap) + δsumGap) n := by
    exact paperKNat_add_one_le_paperKNat_of_one_le_gap hσgap hsumGap
  calc
    paperKNat ρ n + paperCapNat β ε2 n + paperKNat δ n + 1 ≤
        (paperKNat (ρ + (1 + ε2) * β + δ) n + 2) + 1 := by
      exact Nat.add_le_add_right hbase 1
    _ = (paperKNat (ρ + (1 + ε2) * β + δ) n + 2) + 1 := by ring_nf
    _ ≤ paperKNat (ρ + (1 + ε2) * β + δ + δgap) n + 1 := by
      exact Nat.add_le_add_right hgapStep 1
    _ ≤ paperKNat ((ρ + (1 + ε2) * β + δ + δgap) + δsumGap) n := by
      exact hsumStep
    _ = paperKNat (ρ + (1 + ε2) * β + δ + δsumGap + δgap) n := by
      congr 1
      ring
    _ ≤ paperKNat κ n := by
      exact paperKNat_le_paperKNat_of_le hκ

theorem add_le_paperKNat_of_le_paperKNat_of_le_paperKNat_of_one_le_gap_of_le
    {a b : ℕ} {α β γ κ : ℝ} {n : ℕ} (ha : a ≤ paperKNat α n) (hb : b ≤ paperKNat β n)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hgap : 1 ≤ paperK γ n) (hκ : α + β + γ ≤ κ) :
    a + b ≤ paperKNat κ n := by
  calc
    a + b ≤ paperKNat α n + paperKNat β n := by
      exact Nat.add_le_add ha hb
    _ ≤ paperKNat (α + β) n + 1 := by
      exact paperKNat_add_paperKNat_le_paperKNat_add_one hα hβ
    _ ≤ paperKNat ((α + β) + γ) n := by
      exact paperKNat_add_one_le_paperKNat_of_one_le_gap (add_nonneg hα hβ) hgap
    _ = paperKNat (α + β + γ) n := by ring_nf
    _ ≤ paperKNat κ n := by
      exact paperKNat_le_paperKNat_of_le hκ

theorem paperKNat_add_paperCapNat_le_paperKNat_of_one_le_gap_of_le
    {ρ β ε2 δ κ : ℝ} {n : ℕ} (hn : 0 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β)
    (hε2 : -1 ≤ ε2) (hgap : 1 ≤ paperK δ n)
    (hκ : ρ + (1 + ε2) * β + δ ≤ κ) :
    paperKNat ρ n + paperCapNat β ε2 n ≤ paperKNat κ n := by
  calc
    paperKNat ρ n + paperCapNat β ε2 n ≤ paperKNat (ρ + (1 + ε2) * β + δ) n := by
      exact paperKNat_add_paperCapNat_le_paperKNat_of_one_le_gap hn hρ hβ hε2 hgap
    _ ≤ paperKNat κ n := by
      exact paperKNat_le_paperKNat_of_le hκ

theorem paperKNat_lt_paperK_add_one {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) :
    (paperKNat κ n : ℝ) < paperK κ n + 1 := by
  unfold paperKNat
  exact Nat.ceil_lt_add_one (paperK_nonneg hκ n)

theorem paperKNat_le_paperK_add_one {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) :
    (paperKNat κ n : ℝ) ≤ paperK κ n + 1 := by
  exact (paperKNat_lt_paperK_add_one hκ n).le

theorem nat_le_paperKNat_of_le_paperK {a : ℕ} {κ : ℝ} {n : ℕ}
    (h : (a : ℝ) ≤ paperK κ n) : a ≤ paperKNat κ n := by
  exact_mod_cast h.trans (Nat.le_ceil (paperK κ n))

theorem one_le_paperKNat {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : 1 < n) :
    1 ≤ paperKNat κ n := by
  unfold paperKNat
  rw [Nat.one_le_ceil_iff]
  exact paperK_pos hκ hn

theorem half_sub_nonneg {ε : ℝ} (hε : ε ≤ (1 / 2 : ℝ)) : 0 ≤ (1 / 2 : ℝ) - ε := by
  linarith

theorem half_sub_pos {ε : ℝ} (hε : ε < (1 / 2 : ℝ)) : 0 < (1 / 2 : ℝ) - ε := by
  linarith

theorem paperP_sq (β : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    paperP β n ^ 2 = β ^ 2 * (Real.log (n : ℝ) / (n : ℝ)) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    have hcast : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact Real.log_nonneg hcast
  have harg : 0 ≤ Real.log (n : ℝ) / (n : ℝ) := by
    exact div_nonneg hlog (Nat.cast_nonneg n)
  unfold paperP
  rw [mul_pow, Real.sq_sqrt harg]

theorem paperK_sq (κ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    paperK κ n ^ 2 = κ ^ 2 * ((n : ℝ) * Real.log (n : ℝ)) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    have hcast : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    exact Real.log_nonneg hcast
  have harg : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by
    exact mul_nonneg (Nat.cast_nonneg n) hlog
  unfold paperK
  rw [mul_pow, Real.sq_sqrt harg]

theorem half_add_one_mul_paperK_le_eps_mul_paperKSq_of_le
    {κ α ε : ℝ} {n : ℕ} (hn : 1 < n)
    (hcoeff : α * (paperK κ n + 1) ≤ 2 * ε * κ * paperK κ n) :
    ((paperK κ n + 1) / 2) * paperK α n ≤ ε * paperK κ n ^ 2 := by
  have hsqrt :
      0 < Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    apply Real.sqrt_pos.2
    exact mul_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hn)) (paperLog_pos hn)
  unfold paperK at hcoeff ⊢
  nlinarith [hsqrt]

theorem three_loglog_split_first_le {β κ ε : ℝ} {n : ℕ}
    (hn : 1 < n) (hκ : 0 ≤ κ)
    (hcoeff : 3 * β * Real.log (Real.log (n : ℝ)) ≤ ε * paperS n) :
    ((3 * κ * Real.log (Real.log (n : ℝ))) * β / paperS n) ≤ ε * κ := by
  have hs : 0 < paperS n := paperS_pos hn
  have hcoeff' : (3 * β * Real.log (Real.log (n : ℝ))) / paperS n ≤ ε := by
    exact (div_le_iff₀ hs).2 hcoeff
  have hmul : κ * ((3 * β * Real.log (Real.log (n : ℝ))) / paperS n) ≤ κ * ε := by
    exact mul_le_mul_of_nonneg_left hcoeff' hκ
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

theorem three_loglog_codegCoeff_eq {κ q : ℝ} {n : ℕ} :
    ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) =
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
  ring_nf

theorem three_loglog_witnessCoeff_le_two_eps_mul {β κ ε q : ℝ} {n : ℕ}
    (hn : 1 < n) (hκ : 0 ≤ κ)
    (hdiagScale : 3 * β * Real.log (Real.log (n : ℝ)) ≤ ε * paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε * κ) :
    paperHugeWitnessCoeff κ β q n ≤ 2 * ε * κ := by
  have hfirst :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * β) / paperS n ≤ ε * κ := by
    exact three_loglog_split_first_le hn hκ hdiagScale
  have hsecond :
      ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε * κ := by
    convert hcodegScale using 1
    ring_nf
  unfold paperHugeWitnessCoeff
  calc
    ((3 * κ * Real.log (Real.log (n : ℝ))) * β) / paperS n +
        ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * q) /
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε * κ + ε * κ := by
        exact add_le_add hfirst hsecond
    _ = 2 * ε * κ := by ring

theorem three_mul_paperK_two_mul_eq {ε κ : ℝ} {n : ℕ} :
    (3 : ℝ) * paperK (2 * ε * κ) n = ε * (6 * paperK κ n) := by
  unfold paperK
  ring

theorem paperK_mul (c κ : ℝ) (n : ℕ) :
    paperK (c * κ) n = c * paperK κ n := by
  unfold paperK
  ring

theorem three_mul_paperK_le_mul_paperK_of_le_mul {δ₁ δ₂ ε : ℝ} {n : ℕ}
    (hδ : δ₁ ≤ (ε / 3) * δ₂) :
    (3 : ℝ) * paperK δ₁ n ≤ ε * paperK δ₂ n := by
  have hmono : paperK δ₁ n ≤ paperK ((ε / 3) * δ₂) n := paperK_le_paperK_of_le hδ
  calc
    (3 : ℝ) * paperK δ₁ n ≤ (3 : ℝ) * paperK ((ε / 3) * δ₂) n := by
      exact mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = ε * paperK δ₂ n := by
      rw [paperK_mul]
      ring

theorem three_mul_paperK_paperHugeWitnessCoeff_le_of_le_mul_of_le
    {κ β q ε δ rhs : ℝ} {n : ℕ} (hε : 0 ≤ ε)
    (hcoeff : paperHugeWitnessCoeff κ β q n ≤ (ε / 3) * δ)
    (hsmall : paperK δ n ≤ rhs) :
    (3 : ℝ) * paperK (paperHugeWitnessCoeff κ β q n) n ≤ ε * rhs := by
  calc
    (3 : ℝ) * paperK (paperHugeWitnessCoeff κ β q n) n ≤ ε * paperK δ n := by
      exact three_mul_paperK_le_mul_paperK_of_le_mul hcoeff
    _ ≤ ε * rhs := by
      exact mul_le_mul_of_nonneg_left hsmall hε

theorem paperHugeWitnessDegreeCoeff_nonneg {κ β : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β)
    (hloglog : 0 ≤ Real.log (Real.log (n : ℝ))) :
    0 ≤ paperHugeWitnessDegreeCoeff κ β n := by
  unfold paperHugeWitnessDegreeCoeff
  refine div_nonneg ?_ (paperS_nonneg n)
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hκ) hloglog) hβ

theorem paperHugeWitnessCodegCoeff_nonneg {κ q : ℝ} {n : ℕ}
    (hq : 0 ≤ q) :
    0 ≤ paperHugeWitnessCodegCoeff κ q n := by
  unfold paperHugeWitnessCodegCoeff
  refine div_nonneg ?_ (Real.sqrt_nonneg _)
  have hsq : 0 ≤ (3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2 := by positivity
  exact mul_nonneg hsq hq

theorem paperHugeWitnessCoeff_nonneg {κ β q : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hq : 0 ≤ q)
    (hloglog : 0 ≤ Real.log (Real.log (n : ℝ))) :
    0 ≤ paperHugeWitnessCoeff κ β q n := by
  rw [paperHugeWitnessCoeff]
  exact add_nonneg
    (paperHugeWitnessDegreeCoeff_nonneg hκ hβ hloglog)
    (paperHugeWitnessCodegCoeff_nonneg hq)

theorem paperHugeWitnessDegreeBranchParam_nonneg {ε1 κ β : ℝ} {n : ℕ}
    (hε1 : 0 < ε1) (hκ : 0 ≤ κ) (hβ : 0 ≤ β)
    (hloglog : 0 ≤ Real.log (Real.log (n : ℝ))) :
    0 ≤ paperHugeWitnessDegreeBranchParam ε1 κ β n := by
  unfold paperHugeWitnessDegreeBranchParam
  exact mul_nonneg (by positivity) (paperHugeWitnessDegreeCoeff_nonneg hκ hβ hloglog)

theorem paperHugeWitnessCodegBranchParam_nonneg {ε1 κ q : ℝ} {n : ℕ}
    (hε1 : 0 < ε1) (hq : 0 ≤ q) :
    0 ≤ paperHugeWitnessCodegBranchParam ε1 κ q n := by
  unfold paperHugeWitnessCodegBranchParam
  exact mul_nonneg (by positivity) (paperHugeWitnessCodegCoeff_nonneg hq)

theorem paperHugeWitnessBranchParam_eq_add {ε1 κ β q : ℝ} {n : ℕ} :
    paperHugeWitnessBranchParam ε1 κ β q n =
      paperHugeWitnessDegreeBranchParam ε1 κ β n +
        paperHugeWitnessCodegBranchParam ε1 κ q n := by
  unfold paperHugeWitnessBranchParam paperHugeWitnessCoeff
    paperHugeWitnessDegreeBranchParam paperHugeWitnessCodegBranchParam
  ring

theorem paperHugeWitnessDegreeCoeff_le_eps_third_mul_branchParam {ε1 κ β : ℝ} {n : ℕ}
    (hε1 : 0 < ε1) :
    paperHugeWitnessDegreeCoeff κ β n ≤
      (ε1 / 3) * paperHugeWitnessDegreeBranchParam ε1 κ β n := by
  have hε1_ne : ε1 ≠ 0 := ne_of_gt hε1
  have hmul : (ε1 / 3) * (3 / ε1) = 1 := by
    field_simp [hε1_ne]
  refine le_of_eq ?_
  unfold paperHugeWitnessDegreeBranchParam
  calc
    paperHugeWitnessDegreeCoeff κ β n = 1 * paperHugeWitnessDegreeCoeff κ β n := by ring
    _ = ((ε1 / 3) * (3 / ε1)) * paperHugeWitnessDegreeCoeff κ β n := by rw [hmul]
    _ = (ε1 / 3) * ((3 / ε1) * paperHugeWitnessDegreeCoeff κ β n) := by ring

theorem paperHugeWitnessCodegCoeff_le_eps_third_mul_branchParam {ε1 κ q : ℝ} {n : ℕ}
    (hε1 : 0 < ε1) :
    paperHugeWitnessCodegCoeff κ q n ≤
      (ε1 / 3) * paperHugeWitnessCodegBranchParam ε1 κ q n := by
  have hε1_ne : ε1 ≠ 0 := ne_of_gt hε1
  have hmul : (ε1 / 3) * (3 / ε1) = 1 := by
    field_simp [hε1_ne]
  refine le_of_eq ?_
  unfold paperHugeWitnessCodegBranchParam
  calc
    paperHugeWitnessCodegCoeff κ q n = 1 * paperHugeWitnessCodegCoeff κ q n := by ring
    _ = ((ε1 / 3) * (3 / ε1)) * paperHugeWitnessCodegCoeff κ q n := by rw [hmul]
    _ = (ε1 / 3) * ((3 / ε1) * paperHugeWitnessCodegCoeff κ q n) := by ring

theorem paperHugeWitnessDegreeBranchParam_le_of_coeff_le {ε1 κ β δ : ℝ} {n : ℕ}
    (hε1 : 0 < ε1)
    (hcoeff : paperHugeWitnessDegreeCoeff κ β n ≤ (ε1 / 3) * δ) :
    paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ δ := by
  have hε1_ne : ε1 ≠ 0 := ne_of_gt hε1
  have hfac : 0 ≤ 3 / ε1 := by positivity
  have hmul : (3 / ε1) * (ε1 / 3) = 1 := by
    field_simp [hε1_ne]
  unfold paperHugeWitnessDegreeBranchParam
  calc
    (3 / ε1) * paperHugeWitnessDegreeCoeff κ β n ≤ (3 / ε1) * ((ε1 / 3) * δ) := by
      exact mul_le_mul_of_nonneg_left hcoeff hfac
    _ = ((3 / ε1) * (ε1 / 3)) * δ := by ring
    _ = δ := by rw [hmul, one_mul]

theorem paperHugeWitnessCodegBranchParam_le_of_coeff_le {ε1 κ q δ : ℝ} {n : ℕ}
    (hε1 : 0 < ε1)
    (hcoeff : paperHugeWitnessCodegCoeff κ q n ≤ (ε1 / 3) * δ) :
    paperHugeWitnessCodegBranchParam ε1 κ q n ≤ δ := by
  have hε1_ne : ε1 ≠ 0 := ne_of_gt hε1
  have hfac : 0 ≤ 3 / ε1 := by positivity
  have hmul : (3 / ε1) * (ε1 / 3) = 1 := by
    field_simp [hε1_ne]
  unfold paperHugeWitnessCodegBranchParam
  calc
    (3 / ε1) * paperHugeWitnessCodegCoeff κ q n ≤ (3 / ε1) * ((ε1 / 3) * δ) := by
      exact mul_le_mul_of_nonneg_left hcoeff hfac
    _ = ((3 / ε1) * (ε1 / 3)) * δ := by ring
    _ = δ := by rw [hmul, one_mul]

theorem paperHugeWitnessDegreeBranchParam_le_of_le {ε1 κ β δ : ℝ} {n : ℕ}
    (hε1 : 0 < ε1)
    (hcoeff :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * β) / paperS n ≤ (ε1 / 3) * δ) :
    paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ δ := by
  exact
    paperHugeWitnessDegreeBranchParam_le_of_coeff_le hε1
      (by simpa [paperHugeWitnessDegreeCoeff] using hcoeff)

theorem paperHugeWitnessCodegBranchParam_le_of_le {ε1 κ q δ : ℝ} {n : ℕ}
    (hε1 : 0 < ε1)
    (hcoeff :
      ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        (ε1 / 3) * δ) :
    paperHugeWitnessCodegBranchParam ε1 κ q n ≤ δ := by
  exact
    paperHugeWitnessCodegBranchParam_le_of_coeff_le hε1
      (by simpa [paperHugeWitnessCodegCoeff] using hcoeff)

theorem paperHugeWitnessCoeff_le_of_exact_piece_branchParam
    {ε1 κ β q : ℝ} {n : ℕ} (hε1 : 0 < ε1) :
    paperHugeWitnessCoeff κ β q n ≤
      (ε1 / 3) *
        (paperHugeWitnessDegreeBranchParam ε1 κ β n +
          paperHugeWitnessCodegBranchParam ε1 κ q n) := by
  have hfirst :
      paperHugeWitnessDegreeCoeff κ β n ≤
        (ε1 / 3) * paperHugeWitnessDegreeBranchParam ε1 κ β n := by
    exact paperHugeWitnessDegreeCoeff_le_eps_third_mul_branchParam hε1
  have hsecond :
      paperHugeWitnessCodegCoeff κ q n ≤
        (ε1 / 3) * paperHugeWitnessCodegBranchParam ε1 κ q n := by
    exact paperHugeWitnessCodegCoeff_le_eps_third_mul_branchParam hε1
  unfold paperHugeWitnessCoeff
  calc
    paperHugeWitnessDegreeCoeff κ β n + paperHugeWitnessCodegCoeff κ q n ≤
        (ε1 / 3) * paperHugeWitnessDegreeBranchParam ε1 κ β n +
          (ε1 / 3) * paperHugeWitnessCodegBranchParam ε1 κ q n := by
      exact add_le_add hfirst hsecond
    _ = (ε1 / 3) *
          (paperHugeWitnessDegreeBranchParam ε1 κ β n +
            paperHugeWitnessCodegBranchParam ε1 κ q n) := by
      ring

theorem paperHugeWitnessBranchParam_nonneg {ε1 κ β q : ℝ} {n : ℕ}
    (hε1 : 0 < ε1) (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hq : 0 ≤ q)
    (hloglog : 0 ≤ Real.log (Real.log (n : ℝ))) :
    0 ≤ paperHugeWitnessBranchParam ε1 κ β q n := by
  unfold paperHugeWitnessBranchParam
  exact
    mul_nonneg (by positivity) (paperHugeWitnessCoeff_nonneg hκ hβ hq hloglog)

theorem paperHugeWitnessCoeff_le_eps_third_mul_branchParam {ε1 κ β q : ℝ} {n : ℕ}
    (hε1 : 0 < ε1) :
    paperHugeWitnessCoeff κ β q n ≤
      (ε1 / 3) * paperHugeWitnessBranchParam ε1 κ β q n := by
  have hε1_ne : ε1 ≠ 0 := ne_of_gt hε1
  have hmul : (ε1 / 3) * (3 / ε1) = 1 := by
    field_simp [hε1_ne]
  refine le_of_eq ?_
  unfold paperHugeWitnessBranchParam
  calc
    paperHugeWitnessCoeff κ β q n = 1 * paperHugeWitnessCoeff κ β q n := by ring
    _ = ((ε1 / 3) * (3 / ε1)) * paperHugeWitnessCoeff κ β q n := by rw [hmul]
    _ = (ε1 / 3) * ((3 / ε1) * paperHugeWitnessCoeff κ β q n) := by ring

theorem paperHugeWitnessBranchParam_le_of_coeff_le {ε1 κ β q δ : ℝ} {n : ℕ}
    (hε1 : 0 < ε1)
    (hcoeff : paperHugeWitnessCoeff κ β q n ≤ (ε1 / 3) * δ) :
    paperHugeWitnessBranchParam ε1 κ β q n ≤ δ := by
  have hε1_ne : ε1 ≠ 0 := ne_of_gt hε1
  have hfac : 0 ≤ 3 / ε1 := by positivity
  have hmul : (3 / ε1) * (ε1 / 3) = 1 := by
    field_simp [hε1_ne]
  unfold paperHugeWitnessBranchParam
  calc
    (3 / ε1) * paperHugeWitnessCoeff κ β q n ≤ (3 / ε1) * ((ε1 / 3) * δ) := by
      exact mul_le_mul_of_nonneg_left hcoeff hfac
    _ = ((3 / ε1) * (ε1 / 3)) * δ := by ring
    _ = δ := by rw [hmul, one_mul]

theorem paperHugeWitnessBranchParam_le_of_pieceBranchParamBounds
    {ε1 κ β q δdeg δcodeg δbranch : ℝ} {n : ℕ}
    (hdeg :
      paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ δdeg)
    (hcodeg :
      paperHugeWitnessCodegBranchParam ε1 κ q n ≤ δcodeg)
    (hsum : δdeg + δcodeg ≤ δbranch) :
    paperHugeWitnessBranchParam ε1 κ β q n ≤ δbranch := by
  rw [paperHugeWitnessBranchParam_eq_add]
  exact (add_le_add hdeg hcodeg).trans hsum

theorem paperHugeWitnessDegreeBranchParam_eventually_le
    {ε1 κ β δ : ℝ} (hε1 : 0 < ε1) (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n → paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ δ := by
  let c : ℝ := (9 * κ * β) / ε1
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hratio :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ (2 : ℝ))
        Filter.atTop (nhds 0) := by
    have hlo :
        (fun n : ℕ => Real.log (Real.log (n : ℝ))) =o[Filter.atTop]
          (fun n : ℕ => (Real.log (n : ℝ)) ^ (2 : ℝ)) := by
      simpa [pow_one] using
        ((isLittleO_log_rpow_rpow_atTop (r := (1 : ℝ)) (s := (2 : ℝ)) (by positivity)).comp_tendsto
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    simpa using hlo.tendsto_div_nhds_zero
  have htendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          c * (Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ (2 : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa [c] using hratio.const_mul c
  have hlogevent : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ Real.log (n : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  rcases Metric.tendsto_atTop.mp htendsto δ hδ with ⟨N1, hN1⟩
  rcases Filter.eventually_atTop.1 hlogevent with ⟨N0, hN0⟩
  refine ⟨max N0 N1, ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N1 ≤ n := le_trans (le_max_right _ _) hn
  have hlog2 : 2 ≤ Real.log (n : ℝ) := hN0 n hn0
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by
    linarith
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := by
    exact Real.log_nonneg hlog1
  have hratio_nonneg :
      0 ≤ Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ (2 : ℝ) := by
    exact div_nonneg hloglog_nonneg (by positivity)
  have hlt_abs :
      |c| * (|Real.log (Real.log (n : ℝ))| / (Real.log (n : ℝ)) ^ (2 : ℝ)) < δ := by
    simpa [Real.dist_eq] using hN1 n hn1
  have hlt :
      c * (Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ (2 : ℝ)) < δ := by
    simpa [abs_of_nonneg hc, abs_of_nonneg hloglog_nonneg] using hlt_abs
  have hEq :
      paperHugeWitnessDegreeBranchParam ε1 κ β n =
        c * (Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ (2 : ℝ)) := by
    simp [paperHugeWitnessDegreeBranchParam, paperHugeWitnessDegreeCoeff, paperS, c,
      div_eq_mul_inv]
    ring
  rw [hEq]
  exact le_of_lt hlt

theorem paperHugeWitnessCodegBranchParam_eventually_le
    {ε1 κ q δ : ℝ} (hε1 : 0 < ε1) (hq : 0 ≤ q) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n → paperHugeWitnessCodegBranchParam ε1 κ q n ≤ δ := by
  let c : ℝ := (((27 : ℝ) / 2) * κ ^ 2 * q) / ε1
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hsmall :
      Filter.Tendsto
        (fun n : ℕ => c * (((Real.log (n : ℝ)) ^ (2 : ℝ)) / ((n : ℝ) ^ (1 / 4 : ℝ))))
        Filter.atTop (nhds 0) := by
    have hlo :
        Filter.Tendsto
          (fun n : ℕ => ((Real.log (n : ℝ)) ^ (2 : ℝ)) / ((n : ℝ) ^ (1 / 4 : ℝ)))
          Filter.atTop (nhds 0) := by
      have hlo' :
          (fun n : ℕ => (Real.log (n : ℝ)) ^ (2 : ℝ)) =o[Filter.atTop]
            (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) := by
        simpa using
          ((isLittleO_log_rpow_rpow_atTop (r := (2 : ℝ)) (s := (1 / 4 : ℝ))
            (by positivity)).comp_tendsto tendsto_natCast_atTop_atTop)
      simpa using hlo'.tendsto_div_nhds_zero
    simpa [c] using hlo.const_mul c
  have hlogevent : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ Real.log (n : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  rcases Metric.tendsto_atTop.mp hsmall δ hδ with ⟨N1, hN1⟩
  rcases Filter.eventually_atTop.1 hlogevent with ⟨N0, hN0⟩
  refine ⟨max N0 N1, ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : N1 ≤ n := le_trans (le_max_right _ _) hn
  have hlog2 : 2 ≤ Real.log (n : ℝ) := hN0 n hn0
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by
    linarith
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    linarith
  have hlogsq_nonneg : 0 ≤ (Real.log (n : ℝ)) ^ (2 : ℝ) := by
    positivity
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    positivity
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := by
    exact Real.log_nonneg hlog1
  have hcomp_num :
      (Real.log (Real.log (n : ℝ))) ^ (2 : ℝ) ≤ (Real.log (n : ℝ)) ^ (2 : ℝ) := by
    have hloglog_le : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
      exact Real.log_le_self hlog_nonneg
    exact Real.rpow_le_rpow hloglog_nonneg hloglog_le (by positivity)
  have hn_one : 1 ≤ (n : ℝ) := by
    have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self hn_nonneg
    nlinarith
  have hn_pos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn_one
  have hpow_den_pos : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := by
    exact Real.rpow_pos_of_pos hn_pos _
  have hpow_den_nonneg : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := hpow_den_pos.le
  have hcomp_den : (n : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    have hpow_le : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      have hquarter_le_half : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) := by
        norm_num
      exact Real.rpow_le_rpow_of_exponent_le hn_one hquarter_le_half
    have hsqrt_eq :
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) =
          ((n : ℝ) * Real.log (n : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    have hbase : (n : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
      nlinarith
    have hmul_le :
        (n : ℝ) ^ (1 / 2 : ℝ) ≤ ((n : ℝ) * Real.log (n : ℝ)) ^ (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow hn_nonneg hbase (by positivity)
    exact hpow_le.trans (by simpa [hsqrt_eq] using hmul_le)
  have hcomp_div :
      ((Real.log (Real.log (n : ℝ))) ^ (2 : ℝ)) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤
        ((Real.log (n : ℝ)) ^ (2 : ℝ)) / ((n : ℝ) ^ (1 / 4 : ℝ)) := by
    exact div_le_div₀ hlogsq_nonneg hcomp_num hpow_den_pos hcomp_den
  have hlt_abs :
      |c| * ((Real.log (n : ℝ)) ^ (2 : ℝ) / |(n : ℝ) ^ (1 / 4 : ℝ)|) < δ := by
    simpa [Real.dist_eq] using hN1 n hn1
  have habs_den : |(n : ℝ) ^ (1 / 4 : ℝ)| = (n : ℝ) ^ (1 / 4 : ℝ) := by
    exact abs_of_nonneg hpow_den_nonneg
  rw [habs_den] at hlt_abs
  have hlt_upper :
      c * (((Real.log (n : ℝ)) ^ (2 : ℝ)) / ((n : ℝ) ^ (1 / 4 : ℝ))) < δ := by
    simpa [abs_of_nonneg hc, abs_of_nonneg hlogsq_nonneg] using hlt_abs
  have hEq :
      paperHugeWitnessCodegBranchParam ε1 κ q n =
        c * (((Real.log (Real.log (n : ℝ))) ^ (2 : ℝ)) /
          Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
    simp [paperHugeWitnessCodegBranchParam, paperHugeWitnessCodegCoeff, c, div_eq_mul_inv]
    ring_nf
  rw [hEq]
  have hmono :
      c * (((Real.log (Real.log (n : ℝ))) ^ (2 : ℝ)) / Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
        c * (((Real.log (n : ℝ)) ^ (2 : ℝ)) / ((n : ℝ) ^ (1 / 4 : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hcomp_div hc
  exact le_of_lt (lt_of_le_of_lt hmono hlt_upper)

theorem paperHugeWitnessBranchwisePieceBranchParamBounds_eventually_le
    {ε1 κ β q δdegBlue δcodegBlue δdegRed δcodegRed : ℝ}
    (hε1 : 0 < ε1) (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hq : 0 ≤ q)
    (hδdegBlue : 0 < δdegBlue) (hδcodegBlue : 0 < δcodegBlue)
    (hδdegRed : 0 < δdegRed) (hδcodegRed : 0 < δcodegRed) :
    ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n →
      paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ δdegBlue ∧
        paperHugeWitnessCodegBranchParam ε1 κ q n ≤ δcodegBlue ∧
          paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ δdegRed ∧
            paperHugeWitnessCodegBranchParam ε1 κ q n ≤ δcodegRed := by
  rcases paperHugeWitnessDegreeBranchParam_eventually_le hε1 hκ hβ hδdegBlue with
    ⟨NdegBlue, hdegBlue⟩
  rcases paperHugeWitnessCodegBranchParam_eventually_le hε1 hq hδcodegBlue with
    ⟨NcodegBlue, hcodegBlue⟩
  rcases paperHugeWitnessDegreeBranchParam_eventually_le hε1 hκ hβ hδdegRed with
    ⟨NdegRed, hdegRed⟩
  rcases paperHugeWitnessCodegBranchParam_eventually_le hε1 hq hδcodegRed with
    ⟨NcodegRed, hcodegRed⟩
  refine ⟨max (max NdegBlue NcodegBlue) (max NdegRed NcodegRed), ?_⟩
  intro n hn
  have hBlue : max NdegBlue NcodegBlue ≤ n := le_trans (le_max_left _ _) hn
  have hRed : max NdegRed NcodegRed ≤ n := le_trans (le_max_right _ _) hn
  have hNdegBlue : NdegBlue ≤ n := le_trans (le_max_left _ _) hBlue
  have hNcodegBlue : NcodegBlue ≤ n := le_trans (le_max_right _ _) hBlue
  have hNdegRed : NdegRed ≤ n := le_trans (le_max_left _ _) hRed
  have hNcodegRed : NcodegRed ≤ n := le_trans (le_max_right _ _) hRed
  exact ⟨hdegBlue hNdegBlue, hcodegBlue hNcodegBlue, hdegRed hNdegRed, hcodegRed hNcodegRed⟩

theorem paperHugeWitnessBranchwiseBranchParamBounds_eventually_le
    {ε1 κ β q δdegBlue δcodegBlue δblue δdegRed δcodegRed δred : ℝ}
    (hε1 : 0 < ε1) (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hq : 0 ≤ q)
    (hδdegBlue : 0 < δdegBlue) (hδcodegBlue : 0 < δcodegBlue)
    (hblueBranchSum : δdegBlue + δcodegBlue ≤ δblue)
    (hδdegRed : 0 < δdegRed) (hδcodegRed : 0 < δcodegRed)
    (hredBranchSum : δdegRed + δcodegRed ≤ δred) :
    ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n →
      paperHugeWitnessBranchParam ε1 κ β q n ≤ δblue ∧
        paperHugeWitnessBranchParam ε1 κ β q n ≤ δred := by
  rcases
      paperHugeWitnessBranchwisePieceBranchParamBounds_eventually_le hε1 hκ hβ hq
        hδdegBlue hδcodegBlue hδdegRed hδcodegRed with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN hn with ⟨hdegBlue, hcodegBlue, hdegRed, hcodegRed⟩
  exact
    ⟨paperHugeWitnessBranchParam_le_of_pieceBranchParamBounds hdegBlue hcodegBlue hblueBranchSum,
      paperHugeWitnessBranchParam_le_of_pieceBranchParamBounds hdegRed hcodegRed hredBranchSum⟩

theorem paperHugeWitnessBranchwisePieceBranchParamBounds_eventually_le_eps_mul
    {ε1 κ β q : ℝ} (hε1 : 0 < ε1) (hκ : 0 < κ) (hβ : 0 ≤ β) (hq : 0 ≤ q) :
    ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n →
      paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ ε1 * κ ∧
        paperHugeWitnessCodegBranchParam ε1 κ q n ≤ ε1 * κ ∧
          paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ ε1 * κ ∧
            paperHugeWitnessCodegBranchParam ε1 κ q n ≤ ε1 * κ := by
  have hδ : 0 < ε1 * κ := by
    positivity
  exact
    paperHugeWitnessBranchwisePieceBranchParamBounds_eventually_le
      hε1 hκ.le hβ hq hδ hδ hδ hδ

theorem paperHugeWitnessBranchwiseBranchParamBounds_eventually_le_two_eps_mul
    {ε1 κ β q : ℝ} (hε1 : 0 < ε1) (hκ : 0 < κ) (hβ : 0 ≤ β) (hq : 0 ≤ q) :
    ∃ N : ℕ, ∀ ⦃n : ℕ⦄, N ≤ n →
      paperHugeWitnessBranchParam ε1 κ β q n ≤ 2 * ε1 * κ ∧
        paperHugeWitnessBranchParam ε1 κ β q n ≤ 2 * ε1 * κ := by
  have hδ : 0 < ε1 * κ := by
    positivity
  have hsum : ε1 * κ + ε1 * κ ≤ 2 * ε1 * κ := by
    exact le_of_eq (by ring)
  exact
    paperHugeWitnessBranchwiseBranchParamBounds_eventually_le
      hε1 hκ.le hβ hq hδ hδ hsum hδ hδ hsum

/-- A canonical large-`n` threshold for the concrete huge-case specialization
`δdeg = δcodeg = ε₁ κ`. When the positivity assumptions fail we return `0`; the specification
lemma below is used only under the paper's usual hypotheses. -/
noncomputable def paperHugeWitnessTwoEpsBranchPieceThreshold (ε1 κ β q : ℝ) : ℕ :=
  if h : 0 < ε1 ∧ 0 < κ ∧ 0 ≤ β ∧ 0 ≤ q then
    Classical.choose
      (paperHugeWitnessBranchwisePieceBranchParamBounds_eventually_le_eps_mul
        h.1 h.2.1 h.2.2.1 h.2.2.2)
  else
    0

theorem paperHugeWitnessTwoEpsBranchPieceThreshold_spec
    {ε1 κ β q : ℝ} (hε1 : 0 < ε1) (hκ : 0 < κ) (hβ : 0 ≤ β) (hq : 0 ≤ q) :
    ∀ ⦃n : ℕ⦄, paperHugeWitnessTwoEpsBranchPieceThreshold ε1 κ β q ≤ n →
      paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ ε1 * κ ∧
        paperHugeWitnessCodegBranchParam ε1 κ q n ≤ ε1 * κ ∧
          paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ ε1 * κ ∧
            paperHugeWitnessCodegBranchParam ε1 κ q n ≤ ε1 * κ := by
  classical
  intro n hn
  let h : 0 < ε1 ∧ 0 < κ ∧ 0 ≤ β ∧ 0 ≤ q := ⟨hε1, hκ, hβ, hq⟩
  have hspec :
      ∀ ⦃m : ℕ⦄,
        Classical.choose
            (paperHugeWitnessBranchwisePieceBranchParamBounds_eventually_le_eps_mul
              hε1 hκ hβ hq) ≤
          m →
          paperHugeWitnessDegreeBranchParam ε1 κ β m ≤ ε1 * κ ∧
            paperHugeWitnessCodegBranchParam ε1 κ q m ≤ ε1 * κ ∧
              paperHugeWitnessDegreeBranchParam ε1 κ β m ≤ ε1 * κ ∧
                paperHugeWitnessCodegBranchParam ε1 κ q m ≤ ε1 * κ :=
    Classical.choose_spec
      (paperHugeWitnessBranchwisePieceBranchParamBounds_eventually_le_eps_mul
        hε1 hκ hβ hq)
  have hn' :
      Classical.choose
          (paperHugeWitnessBranchwisePieceBranchParamBounds_eventually_le_eps_mul
            hε1 hκ hβ hq) ≤
        n := by
    simpa [paperHugeWitnessTwoEpsBranchPieceThreshold, h] using hn
  simpa using hspec hn'

theorem paperHugeWitnessDegreeBranchParam_le_three_mul_of_diagScale
    {ε1 κ β : ℝ} {n : ℕ} (hε1 : 0 < ε1) (hn : 1 < n) (hκ : 0 ≤ κ)
    (hdiagScale : 3 * β * Real.log (Real.log (n : ℝ)) ≤ ε1 * paperS n) :
    paperHugeWitnessDegreeBranchParam ε1 κ β n ≤ 3 * κ := by
  have hcoeff : paperHugeWitnessDegreeCoeff κ β n ≤ ε1 * κ := by
    simpa [paperHugeWitnessDegreeCoeff] using
      (three_loglog_split_first_le (β := β) (κ := κ) (ε := ε1) hn hκ hdiagScale)
  have hmul : (ε1 / 3) * (3 * κ) = ε1 * κ := by ring
  have hcoeff' : paperHugeWitnessDegreeCoeff κ β n ≤ (ε1 / 3) * (3 * κ) := by
    rw [hmul]
    exact hcoeff
  exact
    paperHugeWitnessDegreeBranchParam_le_of_coeff_le hε1 hcoeff'

theorem paperHugeWitnessCodegBranchParam_le_three_mul_of_codegScale
    {ε1 κ q : ℝ} {n : ℕ} (hε1 : 0 < ε1)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ) :
    paperHugeWitnessCodegBranchParam ε1 κ q n ≤ 3 * κ := by
  have hcoeff : paperHugeWitnessCodegCoeff κ q n ≤ ε1 * κ := by
    unfold paperHugeWitnessCodegCoeff
    rw [three_loglog_codegCoeff_eq]
    exact hcodegScale
  have hmul : (ε1 / 3) * (3 * κ) = ε1 * κ := by ring
  have hcoeff' : paperHugeWitnessCodegCoeff κ q n ≤ (ε1 / 3) * (3 * κ) := by
    rw [hmul]
    exact hcoeff
  exact
    paperHugeWitnessCodegBranchParam_le_of_coeff_le hε1 hcoeff'

theorem paperHugeWitnessBranchParam_le_six_mul_of_diagScale_of_codegScale
    {ε1 κ β q : ℝ} {n : ℕ} (hε1 : 0 < ε1) (hn : 1 < n) (hκ : 0 ≤ κ)
    (hdiagScale : 3 * β * Real.log (Real.log (n : ℝ)) ≤ ε1 * paperS n)
    (hcodegScale :
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      ε1 * κ) :
    paperHugeWitnessBranchParam ε1 κ β q n ≤ 6 * κ := by
  refine
    paperHugeWitnessBranchParam_le_of_pieceBranchParamBounds
      (paperHugeWitnessDegreeBranchParam_le_three_mul_of_diagScale hε1 hn hκ hdiagScale)
      (paperHugeWitnessCodegBranchParam_le_three_mul_of_codegScale hε1 hcodegScale) ?_
  nlinarith

theorem paperHugeWitnessCoeff_le_of_le_of_le {κ β q a b : ℝ} {n : ℕ}
    (hfirst :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * β) / paperS n ≤ a)
    (hsecond :
      ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤ b) :
    paperHugeWitnessCoeff κ β q n ≤ a + b := by
  have hfirst' : paperHugeWitnessDegreeCoeff κ β n ≤ a := by
    simpa [paperHugeWitnessDegreeCoeff] using hfirst
  have hsecond' : paperHugeWitnessCodegCoeff κ q n ≤ b := by
    simpa [paperHugeWitnessCodegCoeff] using hsecond
  rw [paperHugeWitnessCoeff]
  linarith

theorem paperHugeWitnessBranchParam_le_of_le_of_le_of_add_le
    {ε1 κ β q a b δ : ℝ} {n : ℕ} (hε1 : 0 < ε1)
    (hfirst :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * β) / paperS n ≤ a)
    (hsecond :
      ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤ b)
    (hsum : a + b ≤ (ε1 / 3) * δ) :
    paperHugeWitnessBranchParam ε1 κ β q n ≤ δ := by
  exact
    paperHugeWitnessBranchParam_le_of_coeff_le hε1
      ((paperHugeWitnessCoeff_le_of_le_of_le hfirst hsecond).trans hsum)

theorem paperHugeWitnessCoeff_le_eps_third_mul_of_piece_bounds
    {ε1 κ β q δdeg δcodeg δbranch : ℝ} {n : ℕ}
    (hε1 : 0 ≤ ε1)
    (hfirst :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * β) / paperS n ≤ (ε1 / 3) * δdeg)
    (hsecond :
      ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤ (ε1 / 3) * δcodeg)
    (hsum : δdeg + δcodeg ≤ δbranch) :
    paperHugeWitnessCoeff κ β q n ≤ (ε1 / 3) * δbranch := by
  calc
    paperHugeWitnessCoeff κ β q n ≤ (ε1 / 3) * δdeg + (ε1 / 3) * δcodeg := by
      exact paperHugeWitnessCoeff_le_of_le_of_le hfirst hsecond
    _ = (ε1 / 3) * (δdeg + δcodeg) := by ring
    _ ≤ (ε1 / 3) * δbranch := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem paperHugeWitnessBranchParam_le_of_piece_bounds
    {ε1 κ β q δdeg δcodeg δbranch : ℝ} {n : ℕ} (hε1 : 0 < ε1)
    (hfirst :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * β) / paperS n ≤ (ε1 / 3) * δdeg)
    (hsecond :
      ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤ (ε1 / 3) * δcodeg)
    (hsum : δdeg + δcodeg ≤ δbranch) :
    paperHugeWitnessBranchParam ε1 κ β q n ≤ δbranch := by
  exact
    paperHugeWitnessBranchParam_le_of_coeff_le hε1
      (paperHugeWitnessCoeff_le_eps_third_mul_of_piece_bounds hε1.le hfirst hsecond hsum)

theorem three_mul_paperK_le_eps_mul_of_le_two_eps_mul_of_six_mul_paperK_le
    {δ κ ε rhs : ℝ} {n : ℕ} (hδ : δ ≤ 2 * ε * κ) (hsmall : 6 * paperK κ n ≤ rhs)
    (hε : 0 ≤ ε) :
    (3 : ℝ) * paperK δ n ≤ ε * rhs := by
  have hmono : paperK δ n ≤ paperK (2 * ε * κ) n := paperK_le_paperK_of_le hδ
  calc
    (3 : ℝ) * paperK δ n ≤ (3 : ℝ) * paperK (2 * ε * κ) n := by
      exact mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = ε * (6 * paperK κ n) := by rw [three_mul_paperK_two_mul_eq]
    _ ≤ ε * rhs := by
      exact mul_le_mul_of_nonneg_left hsmall hε

theorem cross_residual_sub_one_le_paperK
    {ρ β ε2 κ : ℝ} {n : ℕ} (hκ : 0 ≤ κ) :
    (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1) ≤
      paperK κ n := by
  have hsub_nat :
      paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n ≤ paperKNat κ n := by
    omega
  have hsub_cast :
      (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ)) ≤
        paperKNat κ n := by
    exact_mod_cast hsub_nat
  have hkceil : (paperKNat κ n : ℝ) ≤ paperK κ n + 1 :=
    paperKNat_le_paperK_add_one hκ n
  linarith

theorem paperK_le_cross_residual_sub_one_of_nonneg_of_gap1_gap2_of_le
    {ρ β ε2 δ δsumGap δgap κ : ℝ} {n : ℕ} (hn : 1 < n) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β)
    (hε2 : -1 ≤ ε2) (hδ : 0 ≤ δ) (hsumGap : 1 ≤ paperK δsumGap n)
    (hgap : 2 ≤ paperK δgap n)
    (hκ : ρ + (1 + ε2) * β + δ + δsumGap + δgap ≤ κ) :
    paperK δ n ≤
      (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
  have hnat :
      paperKNat ρ n + paperCapNat β ε2 n + paperKNat δ n + 1 ≤ paperKNat κ n := by
    exact
      paperKNat_add_paperCapNat_add_paperKNat_add_one_le_paperKNat_of_gap1_gap2_of_le
        hn hρ hβ hε2 hδ hsumGap hgap hκ
  have hk :
      paperKNat ρ n + paperCapNat β ε2 n ≤ paperKNat κ n := by
    exact le_trans (Nat.le_add_right _ _) <| le_trans (Nat.le_add_right _ _) hnat
  have hnatDef :
      paperKNat δ n + 1 ≤
        paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n := by
    have hbase :
        paperKNat δ n + 1 ≤
          paperKNat κ n - (paperKNat ρ n + paperCapNat β ε2 n) := by
      exact (Nat.le_sub_iff_add_le hk).2 <| by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnat
    simpa [Nat.sub_sub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbase
  have hcast :
      (paperKNat δ n : ℝ) + 1 ≤
        ((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) := by
    exact_mod_cast hnatDef
  calc
    paperK δ n ≤ paperKNat δ n := Nat.le_ceil _
    _ ≤ (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
      linarith

theorem four_eps_mul_le_two_eps_mul_add_of_two_eps_mul_le
    {ε1 κ δextra : ℝ} (hextra : 2 * ε1 * κ ≤ δextra) :
    4 * ε1 * κ ≤ 2 * ε1 * κ + δextra := by
  nlinarith

theorem paperHugeWitness_four_eps_budget_of_extraDeficit
    {ρ β ε1 ε2 κ δextra δsumGap δgap : ℝ}
    (hextra : 2 * ε1 * κ ≤ δextra)
    (hκ :
      ρ + (1 + ε2) * β + 2 * ε1 * κ + δextra + δsumGap + δgap ≤ κ) :
    ρ + (1 + ε2) * β + 4 * ε1 * κ + δsumGap + δgap ≤ κ := by
  nlinarith [four_eps_mul_le_two_eps_mul_add_of_two_eps_mul_le hextra]

theorem paperHugeWitness_two_eps_budget_of_four_eps_budget
    {ρ β ε1 ε2 κ δsumGap δgap : ℝ}
    (hκ :
      ρ + (1 + ε2) * β + 4 * ε1 * κ + δsumGap + δgap ≤ κ) :
    ρ + (1 + ε2) * β + 2 * ε1 * κ + (2 * ε1 * κ) + δsumGap + δgap ≤ κ := by
  nlinarith

/-- The maximum projection parameter `ρ` compatible with the sharpened huge-case budget
`ρ + (1 + ε₂)β + 4 ε₁ κ + δsumGap + δgap ≤ κ`. -/
def paperHugeWitnessFourEpsRhoBudget
    (β ε1 ε2 κ δsumGap δgap : ℝ) : ℝ :=
  κ - ((1 + ε2) * β + 4 * ε1 * κ + δsumGap + δgap)

theorem paperHugeWitness_four_eps_budget_of_rho_le
    {ρ β ε1 ε2 κ δsumGap δgap : ℝ}
    (hρ :
      ρ ≤ paperHugeWitnessFourEpsRhoBudget β ε1 ε2 κ δsumGap δgap) :
    ρ + (1 + ε2) * β + 4 * ε1 * κ + δsumGap + δgap ≤ κ := by
  unfold paperHugeWitnessFourEpsRhoBudget at hρ
  linarith

theorem paperHugeWitnessFourEpsRhoBudget_half_one_add_eps_of_rho_le
    {ρ ε ε1 ε2 δsumGap δgap : ℝ}
    (hρ : ρ ≤ (((1 / 2 : ℝ) + ε / 4) * (1 + ε)))
    (hsmall :
      ε2 / 2 + 4 * ε1 * (1 + ε) + δsumGap + δgap ≤ ε * (1 - ε) / 4) :
    ρ ≤ paperHugeWitnessFourEpsRhoBudget (1 / 2) ε1 ε2 (1 + ε) δsumGap δgap := by
  unfold paperHugeWitnessFourEpsRhoBudget
  linarith

theorem paperHugeWitnessFourEpsRhoBudget_half_one_add_eps_of_x_le
    {ρ x ε ε1 ε2 δsumGap δgap : ℝ}
    (hε : 0 ≤ ε)
    (hρ : ρ ≤ x * (1 + ε))
    (hx : x ≤ (1 / 2 : ℝ) + ε / 4)
    (hsmall :
      ε2 / 2 + 4 * ε1 * (1 + ε) + δsumGap + δgap ≤ ε * (1 - ε) / 4) :
    ρ ≤ paperHugeWitnessFourEpsRhoBudget (1 / 2) ε1 ε2 (1 + ε) δsumGap δgap := by
  have hρ' : ρ ≤ (((1 / 2 : ℝ) + ε / 4) * (1 + ε)) := by
    nlinarith
  exact paperHugeWitnessFourEpsRhoBudget_half_one_add_eps_of_rho_le hρ' hsmall

theorem paperHugeWitnessQuarterProjection_of_middleSum_of_blueLeRed
    {ρR ρB ε : ℝ}
    (hblueLeRed : ρB ≤ ρR)
    (hsum : ρR + ρB ≤ (1 + ε / 2) * (1 + ε)) :
    ρB ≤ (((1 / 2 : ℝ) + ε / 4) * (1 + ε)) := by
  have hhalf : ρB ≤ ((1 + ε / 2) * (1 + ε)) / 2 := by
    linarith
  have hform : ((1 + ε / 2) * (1 + ε)) / 2 = (((1 / 2 : ℝ) + ε / 4) * (1 + ε)) := by
    ring
  simpa [hform] using hhalf

theorem paperHugeWitness_crossSmall_of_twoEpsThreshold_of_rhoBudget
    {ρ β κ ε1 ε2 βdeg qcodeg δsumGap δgap : ℝ} {n : ℕ}
    (hn : 1 < n) (hκ : 1 ≤ κ) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hε2 : -1 ≤ ε2)
    (hε1pos : 0 < ε1) (hε1 : 0 ≤ ε1) (hβdeg : 0 ≤ βdeg) (hqcodeg : 0 ≤ qcodeg)
    (hlarge : paperHugeWitnessTwoEpsBranchPieceThreshold ε1 κ βdeg qcodeg ≤ n)
    (hsumGap : 1 ≤ paperK δsumGap n) (hgap2 : 2 ≤ paperK δgap n)
    (hρbudget : ρ ≤ paperHugeWitnessFourEpsRhoBudget β ε1 ε2 κ δsumGap δgap) :
    (3 : ℝ) * paperK (paperHugeWitnessCoeff κ βdeg qcodeg n) n ≤
      ε1 *
        (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
  let δbranch : ℝ := paperHugeWitnessBranchParam ε1 κ βdeg qcodeg n
  have hκ0 : 0 ≤ κ := by linarith
  have hκpos : 0 < κ := by linarith
  have hcoeffSmall :
      paperHugeWitnessCoeff κ βdeg qcodeg n ≤ (ε1 / 3) * δbranch := by
    dsimp [δbranch]
    exact paperHugeWitnessCoeff_le_eps_third_mul_branchParam hε1pos
  have hbranchwise :=
    paperHugeWitnessTwoEpsBranchPieceThreshold_spec hε1pos hκpos hβdeg hqcodeg hlarge
  rcases hbranchwise with ⟨hdeg, hcodeg, _, _⟩
  have hδbranch : δbranch ≤ 2 * ε1 * κ := by
    dsimp [δbranch]
    exact paperHugeWitnessBranchParam_le_of_pieceBranchParamBounds hdeg hcodeg (by nlinarith)
  have hκ4 :
      ρ + (1 + ε2) * β + 4 * ε1 * κ + δsumGap + δgap ≤ κ := by
    exact paperHugeWitness_four_eps_budget_of_rho_le hρbudget
  have hκ2 :
      ρ + (1 + ε2) * β + 2 * ε1 * κ + δsumGap + δgap ≤ κ := by
    nlinarith
  have hdoubleEps : 0 ≤ 2 * ε1 * κ := by nlinarith
  have hresidualAux :
      paperK (2 * ε1 * κ) n ≤
        (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    exact
      paperK_le_cross_residual_sub_one_of_nonneg_of_gap1_gap2_of_le
        hn hρ hβ hε2 hdoubleEps hsumGap hgap2 hκ2
  have hresidual :
      paperK δbranch n ≤
        (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    exact (paperK_le_paperK_of_le hδbranch).trans hresidualAux
  exact three_mul_paperK_paperHugeWitnessCoeff_le_of_le_mul_of_le hε1 hcoeffSmall hresidual

theorem not_six_mul_paperK_le_cross_residual
    {ρ β ε2 κ : ℝ} {n : ℕ} (hn : 1 < n) (hκ : 1 ≤ κ) :
    ¬ 6 * paperK κ n ≤
        (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
  intro hsmall
  have hκ0 : 0 ≤ κ := by linarith
  have hκpos : 0 < κ := by linarith
  have hkpos : 0 < paperK κ n := paperK_pos hκpos hn
  have hsub_nat :
      paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n ≤ paperKNat κ n := by
    omega
  have hsub_cast :
      (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ)) ≤
        paperKNat κ n := by
    exact_mod_cast hsub_nat
  have hres_le :
      (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1) ≤
        paperK κ n := cross_residual_sub_one_le_paperK hκ0
  have : 6 * paperK κ n ≤ paperK κ n := hsmall.trans hres_le
  linarith

theorem not_three_mul_paperK_add_nonneg_le_cross_residual
    {ρ β ε2 κ ε δ : ℝ} {n : ℕ} (hn : 1 < n) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hδ : 0 ≤ δ) :
    ¬ (3 : ℝ) * paperK (ε * κ + δ) n ≤
        ε *
          ((((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1)) := by
  intro hsmall
  have hκ0 : 0 ≤ κ := by linarith
  have hκpos : 0 < κ := by linarith
  have hkpos : 0 < paperK κ n := paperK_pos hκpos hn
  have hmono :
      paperK (ε * κ) n ≤ paperK (ε * κ + δ) n := by
    exact paperK_le_paperK_of_le (by linarith)
  have hscaled :
      ε * (3 * paperK κ n) ≤
        ε * ((((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1)) := by
    calc
      ε * (3 * paperK κ n) = (3 : ℝ) * paperK (ε * κ) n := by
        unfold paperK
        ring
      _ ≤ (3 : ℝ) * paperK (ε * κ + δ) n := by
        exact mul_le_mul_of_nonneg_left hmono (by positivity)
      _ ≤ ε *
            ((((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1)) := hsmall
  have hthree :
      3 * paperK κ n ≤
        (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1) := by
    nlinarith
  have hres_le :
      (((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1) ≤
        paperK κ n := cross_residual_sub_one_le_paperK hκ0
  have : 3 * paperK κ n ≤ paperK κ n := hthree.trans hres_le
  linarith

theorem three_loglog_diagCoeff_le {β κ ε : ℝ} {n : ℕ}
    (hn : 1 < n) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hk : 1 ≤ paperK κ n)
    (hcoeff : 3 * β * Real.log (Real.log (n : ℝ)) ≤ ε * paperS n) :
    ((3 * κ * Real.log (Real.log (n : ℝ))) * β / paperS n) * (paperK κ n + 1) ≤
      2 * ε * κ * paperK κ n := by
  have hk0 : 0 ≤ paperK κ n := paperK_nonneg hκ n
  have hk2 : paperK κ n + 1 ≤ 2 * paperK κ n := by
    linarith
  have hleftCoeff :
      ((3 * κ * Real.log (Real.log (n : ℝ))) * β / paperS n) ≤ ε * κ := by
    exact three_loglog_split_first_le hn hκ hcoeff
  calc
    ((3 * κ * Real.log (Real.log (n : ℝ))) * β / paperS n) * (paperK κ n + 1) ≤
        (ε * κ) * (paperK κ n + 1) := by
          exact mul_le_mul_of_nonneg_right hleftCoeff (by linarith)
    _ ≤ (ε * κ) * (2 * paperK κ n) := by
      exact mul_le_mul_of_nonneg_left hk2 (mul_nonneg hε hκ)
    _ = 2 * ε * κ * paperK κ n := by ring

end

end Twobites
