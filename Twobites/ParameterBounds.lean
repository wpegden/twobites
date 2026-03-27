import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Finset.Sigma
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

def paperLargeWitnessNat (κ ε : ℝ) (n : ℕ) : ℕ :=
  ⌈2 * (paperK κ n / paperT2 ε n)⌉₊ + 1

def paperHugeWitnessNat (κ : ℝ) (n : ℕ) : ℕ :=
  ⌈2 * (paperK κ n / paperT1 n)⌉₊ + 1

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

theorem loglog_pos_of_two_div_le {η : ℝ} {n : ℕ} (hη : 0 < η)
    (hloglog : 2 / η ≤ Real.log (Real.log (n : ℝ))) :
    0 < Real.log (Real.log (n : ℝ)) := by
  have hdivpos : 0 < 2 / η := by positivity
  linarith

theorem one_le_loglog_of_two_div_le_of_le_one {η : ℝ} {n : ℕ}
    (hη : 0 < η) (hηle : η ≤ 1)
    (hloglog : 2 / η ≤ Real.log (Real.log (n : ℝ))) :
    1 ≤ Real.log (Real.log (n : ℝ)) := by
  have htwo : (2 : ℝ) ≤ 2 / η := by
    exact (le_div_iff₀ hη).2 (by linarith)
  linarith

theorem two_le_loglog_of_two_div_le_of_le_one {η : ℝ} {n : ℕ}
    (hη : 0 < η) (hηle : η ≤ 1)
    (hloglog : 2 / η ≤ Real.log (Real.log (n : ℝ))) :
    2 ≤ Real.log (Real.log (n : ℝ)) := by
  have htwo : (2 : ℝ) ≤ 2 / η := by
    exact (le_div_iff₀ hη).2 (by linarith)
  linarith

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

theorem loglog_le_sqrt_log_of_two_le_loglog {n : ℕ}
    (hlog : 0 ≤ Real.log (n : ℝ))
    (hloglog : 2 ≤ Real.log (Real.log (n : ℝ))) :
    Real.log (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log (n : ℝ)) := by
  have hlogpos : 0 < Real.log (n : ℝ) := by
    have hloglogpos : 0 < Real.log (Real.log (n : ℝ)) := by
      linarith
    have hone : 1 < Real.log (n : ℝ) := (Real.log_pos_iff hlog).1 hloglogpos
    linarith
  have hexp2 :
      Real.exp 2 ≤ Real.log (n : ℝ) := by
    exact (Real.le_log_iff_exp_le hlogpos).1 hloglog
  have hratio :
      Real.log (Real.log (n : ℝ)) / Real.sqrt (Real.log (n : ℝ)) ≤
        Real.log (Real.exp 2) / Real.sqrt (Real.exp 2) := by
    exact Real.log_div_sqrt_antitoneOn (by simp) hexp2 hexp2
  have hsqrt_exp2 : Real.sqrt (Real.exp 2) = Real.exp 1 := by
    calc
      Real.sqrt (Real.exp 2) = Real.sqrt (Real.exp 1 ^ 2) := by
        rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by
              rw [← Real.exp_add]
              norm_num]
        ring_nf
      _ = Real.exp 1 := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos 1)]
  have hratio_bound :
      Real.log (Real.exp 2) / Real.sqrt (Real.exp 2) ≤ 1 := by
    rw [Real.log_exp, hsqrt_exp2]
    have htwoexp : (2 : ℝ) ≤ 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_two]
    exact (div_le_iff₀ (Real.exp_pos 1)).2 htwoexp
  have hsqrt_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.2 hlogpos
  simpa [one_mul] using (div_le_iff₀ hsqrt_pos).1 (hratio.trans hratio_bound)

theorem paperT2_le_paperT1_of_two_le_loglog {ε : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hε : ε ≤ (1 / 4 : ℝ)) (hloglog : 2 ≤ Real.log (Real.log (n : ℝ))) :
    paperT2 ε n ≤ paperT1 n := by
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hn)
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) := by
    linarith
  have hpow :
      1 ≤ (n : ℝ) ^ ((1 / 4 : ℝ) - ε) := by
    exact Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_nonneg _
  have hbound :
      Real.log (Real.log (n : ℝ)) ≤
        (n : ℝ) ^ ((1 / 4 : ℝ) - ε) * Real.sqrt (Real.log (n : ℝ)) := by
    calc
      Real.log (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log (n : ℝ)) :=
        loglog_le_sqrt_log_of_two_le_loglog hlog hloglog
      _ ≤ (n : ℝ) ^ ((1 / 4 : ℝ) - ε) * Real.sqrt (Real.log (n : ℝ)) := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right hpow hsqrt_nonneg
  exact paperT2_le_paperT1_of_loglog_le hn0 hlog hloglog_pos hbound

theorem ceil_paperT2_le_ceil_paperT1_of_two_le_loglog {ε : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hε : ε ≤ (1 / 4 : ℝ)) (hloglog : 2 ≤ Real.log (Real.log (n : ℝ))) :
    ⌈paperT2 ε n⌉₊ ≤ ⌈paperT1 n⌉₊ := by
  apply Nat.ceil_le.2
  exact (paperT2_le_paperT1_of_two_le_loglog hn hε hloglog).trans (Nat.le_ceil _)

theorem paperSection4FiberTerm_le_half_paperT1_of_two_le_loglog_of_fiberScale
    {ε2 : ℝ} {n : ℕ} (hn : 1 < n)
    (hloglog : 2 ≤ Real.log (Real.log (n : ℝ)))
    (hfiber :
      (1 + ε2) * Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 / 8 : ℝ) - ε2) / 2) :
    (1 + ε2) * paperS n * (paperT2 ε2 n / Real.log (n : ℝ)) ≤ paperT1 n / 2 := by
  have hn1 : 1 ≤ n := Nat.le_of_lt hn
  have hn' : 0 < (n : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  have hlogpos : 0 < Real.log (n : ℝ) := paperLog_pos hn
  have hscale :
      (1 + ε2) * paperS n * (paperT2 ε2 n / Real.log (n : ℝ)) =
        ((1 + ε2) * Real.log (n : ℝ)) * paperT2 ε2 n := by
    unfold paperS
    field_simp [hlogpos.ne']
  have hmul :
      ((1 + ε2) * Real.log (n : ℝ)) * paperT2 ε2 n ≤
        ((n : ℝ) ^ ((1 / 8 : ℝ) - ε2) / 2) * paperT2 ε2 n := by
    exact mul_le_mul_of_nonneg_right hfiber (paperT2_nonneg ε2 n)
  have hrpow :
      ((n : ℝ) ^ ((1 / 8 : ℝ) - ε2) / 2) * paperT2 ε2 n =
        paperT2 (1 / 8 : ℝ) n / 2 := by
    calc
      ((n : ℝ) ^ ((1 / 8 : ℝ) - ε2) / 2) * paperT2 ε2 n
          = (((n : ℝ) ^ ((1 / 8 : ℝ) - ε2)) * paperT2 ε2 n) / 2 := by ring
      _ = paperT2 (1 / 8 : ℝ) n / 2 := by
        unfold paperT2
        change ((n : ℝ) ^ ((1 / 8 : ℝ) - ε2) * (n : ℝ) ^ ((1 / 4 : ℝ) + ε2)) / 2 =
          (n : ℝ) ^ ((1 / 4 : ℝ) + (1 / 8 : ℝ)) / 2
        rw [← Real.rpow_add hn']
        congr 1
        ring_nf
  have hT2 :
      paperT2 (1 / 8 : ℝ) n ≤ paperT1 n :=
    paperT2_le_paperT1_of_two_le_loglog hn1 (by norm_num) hloglog
  calc
    (1 + ε2) * paperS n * (paperT2 ε2 n / Real.log (n : ℝ))
        = ((1 + ε2) * Real.log (n : ℝ)) * paperT2 ε2 n := hscale
    _ ≤ ((n : ℝ) ^ ((1 / 8 : ℝ) - ε2) / 2) * paperT2 ε2 n := hmul
    _ = paperT2 (1 / 8 : ℝ) n / 2 := hrpow
    _ ≤ paperT1 n / 2 := by
      linarith

theorem paperSection4DegreeTerm_le_half_paperT1_of_two_le_loglog
    {β ε2 : ℝ} {n : ℕ} (hn : 1 < n) (hβ0 : 0 ≤ β) (hβ : β ≤ (1 / 2 : ℝ))
    (hε2low : -1 ≤ ε2) (hε2 : ε2 ≤ 1)
    (hloglog : 2 ≤ Real.log (Real.log (n : ℝ))) :
    Real.log (n : ℝ) * ((1 + ε2) * paperP β n * paperM n) ≤ paperT1 n / 2 := by
  have hlogpos : 0 < Real.log (n : ℝ) := paperLog_pos hn
  have hlog : 0 ≤ Real.log (n : ℝ) := hlogpos.le
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := by
    linarith
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) := by
    linarith
  have hloglog_le_sqrt :
      Real.log (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log (n : ℝ)) :=
    loglog_le_sqrt_log_of_two_le_loglog hlog hloglog
  have hlog_ge_four : 4 ≤ Real.log (n : ℝ) := by
    have hexp2_le : Real.exp 2 ≤ Real.log (n : ℝ) := by
      exact (Real.le_log_iff_exp_le hlogpos).1 hloglog
    have hfour_lt : (4 : ℝ) < Real.exp 2 := by
      calc
        (4 : ℝ) < Real.exp 1 * Real.exp 1 := by
          nlinarith [Real.exp_one_gt_two]
        _ = Real.exp 2 := by
          rw [← Real.exp_add]
          norm_num
    linarith
  have hsqrt_le_half_log :
      Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 2 := by
    have hsq :
        Real.sqrt (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ) / 2) ^ 2 := by
      rw [Real.sq_sqrt hlog]
      nlinarith
    have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hloglog_le_half_log :
      Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 2 :=
    hloglog_le_sqrt.trans hsqrt_le_half_log
  have hratio :
      Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) ≤ (1 / 2 : ℝ) := by
    have hloglog_le_half_log' :
        Real.log (Real.log (n : ℝ)) ≤ (1 / 2 : ℝ) * Real.log (n : ℝ) := by
      nlinarith
    exact (div_le_iff₀ hlogpos).2 hloglog_le_half_log'
  have hratio_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    exact div_nonneg hloglog_nonneg hlog
  have hfac_nonneg : 0 ≤ 1 + ε2 := by
    linarith
  have hcoef_le_one : (1 + ε2) * β ≤ 1 := by
    nlinarith
  have hcoef_nonneg : 0 ≤ (1 + ε2) * β := by
    exact mul_nonneg hfac_nonneg hβ0
  have hcoeff :
      ((1 + ε2) * β) * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ≤ (1 / 2 : ℝ) := by
    calc
      ((1 + ε2) * β) * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))
          ≤ 1 * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) := by
            gcongr
      _ ≤ (1 / 2 : ℝ) := by
        simpa using hratio
  have hrewrite :
      Real.log (n : ℝ) * ((1 + ε2) * paperP β n * paperM n) =
        (((1 + ε2) * β) * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))) * paperT1 n := by
    calc
      Real.log (n : ℝ) * ((1 + ε2) * paperP β n * paperM n)
          = Real.log (n : ℝ) * ((1 + ε2) * (paperP β n * paperM n)) := by ring
      _ = Real.log (n : ℝ) * ((1 + ε2) * paperK (β / paperS n) n) := by
            rw [paperP_mul_paperM_eq_paperK_div_paperS hn]
      _ = (((1 + ε2) * β) * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))) * paperT1 n := by
            rw [paperK_eq_mul_loglog_mul_paperT1 hloglog_pos.ne']
            unfold paperS
            field_simp [hlogpos.ne']
  have hT1_nonneg : 0 ≤ paperT1 n := paperT1_nonneg_of_loglog_nonneg hloglog_nonneg
  calc
    Real.log (n : ℝ) * ((1 + ε2) * paperP β n * paperM n)
        = (((1 + ε2) * β) * (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ))) * paperT1 n := by
            rw [hrewrite]
    _ ≤ (1 / 2 : ℝ) * paperT1 n := by
      exact mul_le_mul_of_nonneg_right hcoeff hT1_nonneg
    _ = paperT1 n / 2 := by
      ring

theorem paperSection4Bound_le_paperT1_of_two_le_loglog_of_fiberScale
    {β ε2 : ℝ} {n : ℕ} (hn : 1 < n) (hβ0 : 0 ≤ β) (hβ : β ≤ (1 / 2 : ℝ))
    (hε2low : -1 ≤ ε2) (hε2 : ε2 ≤ (1 / 8 : ℝ))
    (hloglog : 2 ≤ Real.log (Real.log (n : ℝ)))
    (hfiber :
      (1 + ε2) * Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 / 8 : ℝ) - ε2) / 2) :
    (1 + ε2) * paperS n * (paperT2 ε2 n / Real.log (n : ℝ)) +
        Real.log (n : ℝ) * ((1 + ε2) * paperP β n * paperM n) ≤
      paperT1 n := by
  have hFiber :=
    paperSection4FiberTerm_le_half_paperT1_of_two_le_loglog_of_fiberScale hn hloglog hfiber
  have hε2one : ε2 ≤ 1 := by
    linarith
  have hDegree :=
    paperSection4DegreeTerm_le_half_paperT1_of_two_le_loglog hn hβ0 hβ hε2low hε2one hloglog
  linarith

theorem two_lt_paperT1_of_two_le_loglog {n : ℕ}
    (hn : 1 < n) (hloglog : 2 ≤ Real.log (Real.log (n : ℝ))) :
    2 < paperT1 n := by
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (lt_trans Nat.zero_lt_one hn)
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hn1)
  have hnot_le_one : ¬ Real.log (n : ℝ) ≤ 1 := by
    intro hle
    have hnonpos : Real.log (Real.log (n : ℝ)) ≤ 0 := Real.log_nonpos hlog_nonneg hle
    linarith
  have hlog_pos : 0 < Real.log (n : ℝ) := by
    linarith
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) := by
    linarith
  have hexp2_le : Real.exp 2 ≤ Real.log (n : ℝ) := by
    exact (Real.le_log_iff_exp_le hlog_pos).1 hloglog
  have hexp2_gt_four : 4 < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two]
  have hn_gt_five : 5 < (n : ℝ) := by
    have hupper : Real.log (n : ℝ) ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hn0
    linarith [lt_of_lt_of_le hexp2_gt_four hexp2_le, hupper]
  have hsqrt_n_gt_two : 2 < Real.sqrt (n : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have hsqrt_log_ge_loglog :
      Real.log (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log (n : ℝ)) :=
    loglog_le_sqrt_log_of_two_le_loglog hlog_nonneg hloglog
  have hratio_ge_one :
      1 ≤ Real.sqrt (Real.log (n : ℝ)) / Real.log (Real.log (n : ℝ)) := by
    rwa [one_le_div hloglog_pos]
  have hmul_ge :
      Real.sqrt (n : ℝ) ≤
        Real.sqrt (n : ℝ) *
          (Real.sqrt (Real.log (n : ℝ)) / Real.log (Real.log (n : ℝ))) := by
    simpa [one_mul] using
      mul_le_mul_of_nonneg_left hratio_ge_one (Real.sqrt_nonneg (n : ℝ))
  have hrewrite :
      paperT1 n =
        Real.sqrt (n : ℝ) *
          (Real.sqrt (Real.log (n : ℝ)) / Real.log (Real.log (n : ℝ))) := by
    unfold paperT1
    rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    ring
  calc
    2 < Real.sqrt (n : ℝ) := hsqrt_n_gt_two
    _ ≤ Real.sqrt (n : ℝ) *
          (Real.sqrt (Real.log (n : ℝ)) / Real.log (Real.log (n : ℝ))) := hmul_ge
    _ = paperT1 n := by rw [hrewrite]

theorem two_lt_paperT1_of_two_div_le_of_le_one {η : ℝ} {n : ℕ}
    (hn : 1 < n) (hη : 0 < η) (hηle : η ≤ 1)
    (hloglog : 2 / η ≤ Real.log (Real.log (n : ℝ))) :
    2 < paperT1 n := by
  exact
    two_lt_paperT1_of_two_le_loglog hn
      (two_le_loglog_of_two_div_le_of_le_one hη hηle hloglog)

theorem two_le_paperK_of_two_div_le_of_le_one {η : ℝ} {n : ℕ}
    (hn : 1 < n) (hη : 0 < η) (hηle : η ≤ 1)
    (hloglog : 2 / η ≤ Real.log (Real.log (n : ℝ))) :
    2 ≤ paperK η n := by
  have hllpos : 0 < Real.log (Real.log (n : ℝ)) :=
    loglog_pos_of_two_div_le hη hloglog
  have hratio : 2 ≤ paperK η n / paperT1 n := by
    rw [paperK_div_paperT1_eq_mul_loglog hn hllpos]
    exact two_le_mul_of_two_div_le hη hloglog
  have hT1gt : 2 < paperT1 n :=
    two_lt_paperT1_of_two_div_le_of_le_one hn hη hηle hloglog
  have hT1ge : 1 ≤ paperT1 n := by
    linarith
  have hT1pos : 0 < paperT1 n := by
    linarith
  have hprod : (2 : ℝ) ≤ (paperK η n / paperT1 n) * paperT1 n := by
    nlinarith
  calc
    (2 : ℝ) ≤ (paperK η n / paperT1 n) * paperT1 n := hprod
    _ = paperK η n := by
      field_simp [hT1pos.ne']

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

theorem paperLargeWitnessNat_lt_two_mul_paperK_div_paperT2_add_two {κ ε : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hT2 : 0 < paperT2 ε n) :
    (paperLargeWitnessNat κ ε n : ℝ) < 2 * (paperK κ n / paperT2 ε n) + 2 := by
  have hratio : 0 ≤ 2 * (paperK κ n / paperT2 ε n) := by
    have hk : 0 ≤ paperK κ n := paperK_nonneg hκ n
    have hdiv : 0 ≤ paperK κ n / paperT2 ε n := div_nonneg hk hT2.le
    nlinarith
  have hceil :
      ((⌈2 * (paperK κ n / paperT2 ε n)⌉₊ : ℕ) : ℝ) <
        2 * (paperK κ n / paperT2 ε n) + 1 := Nat.ceil_lt_add_one hratio
  calc
    (paperLargeWitnessNat κ ε n : ℝ) =
        (⌈2 * (paperK κ n / paperT2 ε n)⌉₊ : ℝ) + 1 := by
          unfold paperLargeWitnessNat
          norm_num
    _ < (2 * (paperK κ n / paperT2 ε n) + 1) + 1 := by linarith
    _ = 2 * (paperK κ n / paperT2 ε n) + 2 := by ring

theorem paperLargeWitnessNat_le_two_mul_paperK_div_paperT2_add_two {κ ε : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hT2 : 0 < paperT2 ε n) :
    (paperLargeWitnessNat κ ε n : ℝ) ≤ 2 * (paperK κ n / paperT2 ε n) + 2 := by
  exact (paperLargeWitnessNat_lt_two_mul_paperK_div_paperT2_add_two hκ hT2).le

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

theorem two_mul_paperKNat_lt_paperLargeWitnessNat_mul_ceil_paperT2 {κ ε : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (hT2 : 2 < paperT2 ε n) :
    2 * paperKNat κ n < paperLargeWitnessNat κ ε n * ⌈paperT2 ε n⌉₊ := by
  have hT2pos : 0 < paperT2 ε n := by linarith
  have hwitnessLower :
      2 * (paperK κ n / paperT2 ε n) + 1 ≤ (paperLargeWitnessNat κ ε n : ℝ) := by
    have hceil :
        2 * (paperK κ n / paperT2 ε n) ≤
          ((⌈2 * (paperK κ n / paperT2 ε n)⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    calc
      2 * (paperK κ n / paperT2 ε n) + 1 ≤
          ((⌈2 * (paperK κ n / paperT2 ε n)⌉₊ : ℕ) : ℝ) + 1 := by
            linarith
      _ = (paperLargeWitnessNat κ ε n : ℝ) := by
          unfold paperLargeWitnessNat
          norm_num
  have hprod :
      2 * paperK κ n + paperT2 ε n ≤
        ((paperLargeWitnessNat κ ε n * ⌈paperT2 ε n⌉₊ : ℕ) : ℝ) := by
    have hceilT2 : paperT2 ε n ≤ (⌈paperT2 ε n⌉₊ : ℝ) := Nat.le_ceil _
    have hmul :
        (2 * (paperK κ n / paperT2 ε n) + 1) * paperT2 ε n ≤
          (paperLargeWitnessNat κ ε n : ℝ) * (⌈paperT2 ε n⌉₊ : ℝ) := by
      gcongr
    have hrewrite :
        (2 * (paperK κ n / paperT2 ε n) + 1) * paperT2 ε n =
          2 * paperK κ n + paperT2 ε n := by
      field_simp [hT2pos.ne']
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
        ((paperLargeWitnessNat κ ε n * ⌈paperT2 ε n⌉₊ : ℕ) : ℝ) := by
    have : ((2 * paperKNat κ n : ℕ) : ℝ) < 2 * paperK κ n + paperT2 ε n := by
      linarith
    exact this.trans_le hprod
  exact_mod_cast hlt

theorem paperKNat_lt_mul_ceil_paperT2_sub_choose_mul_iff
    {κ ε : ℝ} {n witnessSize codegreeBound : ℕ} :
    paperKNat κ n < witnessSize * ⌈paperT2 ε n⌉₊ - witnessSize.choose 2 * codegreeBound ↔
      paperKNat κ n + witnessSize.choose 2 * codegreeBound < witnessSize * ⌈paperT2 ε n⌉₊ :=
  Nat.lt_sub_iff_add_lt

theorem paperKNat_lt_mul_ceil_paperT2_sub_choose_mul_of_two_mul_lt
    {κ ε : ℝ} {n witnessSize codegreeBound : ℕ}
    (htwo : 2 * paperKNat κ n < witnessSize * ⌈paperT2 ε n⌉₊)
    (hchoose : witnessSize.choose 2 * codegreeBound ≤ paperKNat κ n) :
    paperKNat κ n < witnessSize * ⌈paperT2 ε n⌉₊ - witnessSize.choose 2 * codegreeBound := by
  rw [paperKNat_lt_mul_ceil_paperT2_sub_choose_mul_iff]
  omega

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

theorem mul_paperK_eq_paperK_mul {a κ : ℝ} {n : ℕ} :
    a * paperK κ n = paperK (a * κ) n := by
  unfold paperK
  ring

theorem le_paperKNat_of_cast_le_paperK {a : ℕ} {κ : ℝ} {n : ℕ}
    (h : (a : ℝ) ≤ paperK κ n) :
    a ≤ paperKNat κ n := by
  have h' : (a : ℝ) ≤ paperKNat κ n := h.trans (Nat.le_ceil _)
  exact_mod_cast h'

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

theorem le_paperKNat_half_of_two_mul_le_paperKNat {a : ℕ} {κ : ℝ} {n : ℕ}
    (hκ : 0 ≤ κ) (h : 2 * a ≤ paperKNat κ n) :
    a ≤ paperKNat (κ / 2) n := by
  by_contra ha
  have ha' : paperKNat (κ / 2) n + 1 ≤ a := by
    omega
  have hκhalf : 0 ≤ κ / 2 := by
    linarith
  have haReal : paperK (κ / 2) n + 1 ≤ (a : ℝ) := by
    have hceil : paperK (κ / 2) n ≤ paperKNat (κ / 2) n :=
      paperK_le_paperKNat (κ / 2) n
    have haReal' : (paperKNat (κ / 2) n : ℝ) + 1 ≤ (a : ℝ) := by
      exact_mod_cast ha'
    linarith
  have hdouble : paperK κ n + 2 ≤ ((2 * a : ℕ) : ℝ) := by
    have htmp : 2 * (paperK (κ / 2) n + 1) ≤ 2 * (a : ℝ) := by
      linarith
    have hkey : 2 * (paperK (κ / 2) n + 1) = paperK κ n + 2 := by
      unfold paperK
      ring
    simpa [Nat.cast_mul, hkey] using htmp
  have hceilLt : (paperKNat κ n : ℝ) < paperK κ n + 1 := by
    exact Nat.ceil_lt_add_one (paperK_nonneg hκ n)
  have hnatLt : paperKNat κ n < 2 * a := by
    have hrealLt : (paperKNat κ n : ℝ) < ((2 * a : ℕ) : ℝ) := by
      linarith
    exact_mod_cast hrealLt
  omega

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

theorem splitRightCoeff_le_eps_mul_choose_two_of_sum_le_of_three_mul_le
    {a : ℕ} {ε U O W : ℝ}
    (hε : 0 ≤ ε) (hεle : ε ≤ 1) (hU : 0 ≤ U) (hO : 0 ≤ O)
    (hsum : U + O ≤ W)
    (hsmall : (3 : ℝ) * W ≤ ε * ((a : ℝ) - 1)) :
    ((3 : ℝ) / 2) * (a : ℝ) * U + ((((a : ℝ) + U) * O) + O ^ 2 / 2) ≤
      ε * (((a.choose 2 : ℕ) : ℝ)) := by
  have hW : 0 ≤ W := by
    have hUO : 0 ≤ U + O := add_nonneg hU hO
    linarith
  have hhalf : W ≤ (a : ℝ) / 2 := by
    have ha0 : 0 ≤ (a : ℝ) := by positivity
    nlinarith
  have hsum_half : U + O ≤ (a : ℝ) / 2 := hsum.trans hhalf
  have hcross :
      U * O + O ^ 2 / 2 ≤ ((a : ℝ) / 2) * O := by
    have haux : U + O / 2 ≤ (a : ℝ) / 2 := by
      nlinarith
    calc
      U * O + O ^ 2 / 2 = O * (U + O / 2) := by ring
      _ ≤ O * ((a : ℝ) / 2) := by
            exact mul_le_mul_of_nonneg_left haux hO
      _ = ((a : ℝ) / 2) * O := by ring
  have hcoeff :
      ((3 : ℝ) / 2) * (a : ℝ) * U + ((((a : ℝ) + U) * O) + O ^ 2 / 2) ≤
        ((3 : ℝ) / 2) * (a : ℝ) * W := by
    calc
      ((3 : ℝ) / 2) * (a : ℝ) * U + ((((a : ℝ) + U) * O) + O ^ 2 / 2) =
          ((3 : ℝ) / 2) * (a : ℝ) * U + (a : ℝ) * O + (U * O + O ^ 2 / 2) := by
            ring
      _ ≤ ((3 : ℝ) / 2) * (a : ℝ) * U + (a : ℝ) * O + ((a : ℝ) / 2) * O := by
            gcongr
      _ = ((3 : ℝ) / 2) * (a : ℝ) * (U + O) := by
            ring
      _ ≤ ((3 : ℝ) / 2) * (a : ℝ) * W := by
            gcongr
  have hmain :
      ((3 : ℝ) / 2) * (a : ℝ) * W ≤ ε * (((a.choose 2 : ℕ) : ℝ)) := by
    rw [Nat.cast_choose_two]
    nlinarith
  exact hcoeff.trans hmain

theorem splitRightCoeff_le_eps_mul_cap_choose_two_add_choose_two_of_sum_le_of_three_mul_le
    {a cap : ℕ} {ε U O W : ℝ}
    (hε : 0 ≤ ε) (hεle : ε ≤ 1) (hU : 0 ≤ U) (hO : 0 ≤ O)
    (hsum : U + O ≤ W)
    (hsmall : (3 : ℝ) * W ≤ ε * ((a : ℝ) - 1)) :
    ((3 : ℝ) / 2) * (a : ℝ) * U + ((((a : ℝ) + U) * O) + O ^ 2 / 2) ≤
      ε * (((cap.choose 2 + a.choose 2 : ℕ) : ℝ)) := by
  have hbase :
      ((3 : ℝ) / 2) * (a : ℝ) * U + ((((a : ℝ) + U) * O) + O ^ 2 / 2) ≤
        ε * (((a.choose 2 : ℕ) : ℝ)) := by
    exact splitRightCoeff_le_eps_mul_choose_two_of_sum_le_of_three_mul_le
      hε hεle hU hO hsum hsmall
  have hmono :
      ε * (((a.choose 2 : ℕ) : ℝ)) ≤ ε * (((cap.choose 2 + a.choose 2 : ℕ) : ℝ)) := by
    have hnat : a.choose 2 ≤ cap.choose 2 + a.choose 2 := by
      exact Nat.le_add_left _ _
    have hcast :
        (((a.choose 2 : ℕ) : ℝ)) ≤ (((cap.choose 2 + a.choose 2 : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    exact mul_le_mul_of_nonneg_left hcast hε
  exact hbase.trans hmono

theorem three_loglog_codegCoeff_eq {κ q : ℝ} {n : ℕ} :
    ((((3 * κ * Real.log (Real.log (n : ℝ))) ^ 2 / 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) =
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
  ring_nf

theorem three_mul_paperK_two_mul_eq {ε κ : ℝ} {n : ℕ} :
    (3 : ℝ) * paperK (2 * ε * κ) n = ε * (6 * paperK κ n) := by
  unfold paperK
  ring

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

theorem three_loglog_codegCoeff_nonneg {κ q : ℝ} {n : ℕ}
    (hq : 0 ≤ q) :
    0 ≤
      ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * q) /
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hq)
    (Real.sqrt_nonneg _)

theorem not_three_mul_paperK_three_loglog_codegCoeff_le_cross_residual
    {ρ β ε2 κ ε1 q : ℝ} {n : ℕ} (hn : 1 < n) (hκ : 1 ≤ κ) (hε1 : 0 < ε1)
    (hq : 0 ≤ q) :
    ¬ (3 : ℝ) *
          paperK
            (ε1 * κ +
              ((((9 : ℝ) / 2) * κ ^ 2 * (Real.log (Real.log (n : ℝ)) ^ 2) * q) /
                Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))) n ≤
        ε1 *
          ((((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1)) := by
  exact
    not_three_mul_paperK_add_nonneg_le_cross_residual hn hκ hε1
      (three_loglog_codegCoeff_nonneg hq)

theorem not_three_mul_paperK_two_mul_le_cross_residual
    {ρ β ε2 κ ε1 : ℝ} {n : ℕ} (hn : 1 < n) (hκ : 1 ≤ κ) (hε1 : 0 < ε1) :
    ¬ (3 : ℝ) * paperK (2 * ε1 * κ) n ≤
        ε1 *
          ((((paperKNat κ n - paperKNat ρ n - paperCapNat β ε2 n : ℕ) : ℝ) - 1)) := by
  simpa [show 2 * ε1 * κ = ε1 * κ + ε1 * κ by ring] using
    (not_three_mul_paperK_add_nonneg_le_cross_residual
      (ρ := ρ) (β := β) (ε2 := ε2) (κ := κ) (ε := ε1) (δ := ε1 * κ) hn hκ hε1
      (by nlinarith : 0 ≤ ε1 * κ))

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

theorem paperRI_nearOne_blueCoeff_le_of_symm_of_sum_le
    {ε xR xB : ℝ} (hblue : xB ≤ xR) (hsum : xR + xB ≤ 1 + ε / 2) :
    xB ≤ (2 + ε) / 4 := by
  nlinarith

theorem paperRI_nearOne_mixedCoeff_eq
    {ε xR xB : ℝ} (hε0 : 0 ≤ ε) :
    -(1 - xR - xB) / 2 -
        (1 / (4 * (1 + ε))) *
          (-2 * (1 + ε) ^ 2 + 2 * (1 + ε) ^ 2 * (xR + xB) + (1 + ε) -
            xB * (1 + ε) - (1 / 2 : ℝ) - 2 * ε ^ 3 * (1 + ε) ^ 2) =
      (1 / (8 * (1 + ε))) *
        (2 * xB - 1 - (4 * ε ^ 2 + 2 * ε) * (xR + xB - 1) - 2 * ε * xR +
          4 * ε ^ 3 * (1 + ε) ^ 2) := by
  have hε : 1 + ε ≠ 0 := by nlinarith
  field_simp [hε]
  ring

theorem paperRI_nearOne_mixedCoeff_le_final
    {ε xR xB : ℝ}
    (hε0 : 0 ≤ ε)
    (hεsmall : 8 * (1 + ε) ^ 2 ≤ (9 : ℝ))
    (hsumLower : 1 - ε / 2 ≤ xR + xB)
    (hsumUpper : xR + xB ≤ 1 + ε / 2)
    (hblue : xB ≤ xR) :
    (1 / (8 * (1 + ε))) *
        (2 * xB - 1 - (4 * ε ^ 2 + 2 * ε) * (xR + xB - 1) - 2 * ε * xR +
          4 * ε ^ 3 * (1 + ε) ^ 2) ≤
      ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε)) := by
  have hnum :
      2 * xB - 1 - (4 * ε ^ 2 + 2 * ε) * (xR + xB - 1) - 2 * ε * xR +
          4 * ε ^ 3 * (1 + ε) ^ 2 ≤
        ε * (-1 + ε + 22 * ε ^ 2) / 2 := by
    have hxB :
        xB ≤ (2 + ε) / 4 :=
      paperRI_nearOne_blueCoeff_le_of_symm_of_sum_le hblue hsumUpper
    have hstep1 :
        -2 * ε * xR + 4 * ε ^ 3 * (1 + ε) ^ 2 ≤
          -2 * ε * xB + 9 * ε ^ 3 := by
      have hleft : 0 ≤ 2 * ε * (xR - xB) := by
        nlinarith
      have hcoef : 4 * (1 + ε) ^ 2 - 9 ≤ 0 := by
        nlinarith
      have hε3 : 0 ≤ ε ^ 3 := by
        positivity
      have hright : ε ^ 3 * (4 * (1 + ε) ^ 2 - 9) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos hε3 hcoef
      nlinarith
    have hstep2 :
        -(4 * ε ^ 2 + 2 * ε) * (xR + xB - 1) ≤ ε ^ 2 + 2 * ε ^ 3 := by
      nlinarith
    calc
      2 * xB - 1 - (4 * ε ^ 2 + 2 * ε) * (xR + xB - 1) - 2 * ε * xR +
          4 * ε ^ 3 * (1 + ε) ^ 2 ≤
        2 * xB - 1 + (ε ^ 2 + 2 * ε ^ 3) + (-2 * ε * xB + 9 * ε ^ 3) := by
          linarith
      _ = 2 * (1 - ε) * xB - 1 + ε ^ 2 + 11 * ε ^ 3 := by ring
      _ ≤ 2 * (1 - ε) * ((2 + ε) / 4) - 1 + ε ^ 2 + 11 * ε ^ 3 := by
          nlinarith
      _ = ε * (-1 + ε + 22 * ε ^ 2) / 2 := by ring
  have hden : 0 < 8 * (1 + ε) := by
    nlinarith
  have hdiv :
      (2 * xB - 1 - (4 * ε ^ 2 + 2 * ε) * (xR + xB - 1) - 2 * ε * xR +
            4 * ε ^ 3 * (1 + ε) ^ 2) /
          (8 * (1 + ε)) ≤
        ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε)) := by
    have htmp :
        (2 * xB - 1 - (4 * ε ^ 2 + 2 * ε) * (xR + xB - 1) - 2 * ε * xR +
              4 * ε ^ 3 * (1 + ε) ^ 2) /
            (8 * (1 + ε)) ≤
          (ε * (-1 + ε + 22 * ε ^ 2) / 2) / (8 * (1 + ε)) := by
      exact div_le_div_of_nonneg_right hnum (by linarith)
    calc
      (2 * xB - 1 - (4 * ε ^ 2 + 2 * ε) * (xR + xB - 1) - 2 * ε * xR +
            4 * ε ^ 3 * (1 + ε) ^ 2) /
          (8 * (1 + ε)) ≤
        (ε * (-1 + ε + 22 * ε ^ 2) / 2) / (8 * (1 + ε)) := htmp
      _ = ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε)) := by
        field_simp [hden.ne']
        ring
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

theorem paperRI_nearOne_finalCoeff_neg
    {ε : ℝ} (hε : 0 < ε) (hneg : -1 + ε + 22 * ε ^ 2 < 0) :
    ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε)) < 0 := by
  have hden : 0 < 16 * (1 + ε) := by
    nlinarith
  have hnum : ε * (-1 + ε + 22 * ε ^ 2) < 0 := by
    nlinarith
  exact div_neg_of_neg_of_pos hnum hden

/-- The red-coordinate image of a `k`-subset of `V_R × V_B` in the outer counting step of Paper
Lemma `lem:RI`. -/
def paperRIOuterRedImage {m : ℕ} (S : Finset (Fin m × Fin m)) : Finset (Fin m) :=
  S.image Prod.fst

/-- The blue-coordinate image of a `k`-subset of `V_R × V_B` in the outer counting step of Paper
Lemma `lem:RI`. -/
def paperRIOuterBlueImage {m : ℕ} (S : Finset (Fin m × Fin m)) : Finset (Fin m) :=
  S.image Prod.snd

/-- The exact outer event family `\mathcal S_{I,\ell_R,\ell_B}` from Paper Lemma `lem:RI`,
expressed as the family of `k`-subsets of `V_R × V_B` whose red and blue coordinate images have
cardinalities `lR` and `lB`. -/
def paperRIOuterEventSet (m lR lB k : ℕ) : Finset (Finset (Fin m × Fin m)) :=
  ((Finset.univ : Finset (Fin m × Fin m)).powersetCard k).filter fun S =>
    (paperRIOuterRedImage S).card = lR ∧ (paperRIOuterBlueImage S).card = lB

/-- A witness family for the outer event counting step: choose the red image, choose the blue
image, then choose a `k`-subset of their product. -/
def paperRIOuterWitnessSet (m lR lB k : ℕ) :
    Finset (Sigma fun _AB : Finset (Fin m) × Finset (Fin m) => Finset (Fin m × Fin m)) :=
  ((((Finset.univ : Finset (Fin m)).powersetCard lR).product
      ((Finset.univ : Finset (Fin m)).powersetCard lB)).sigma fun AB =>
    (AB.1 ×ˢ AB.2).powersetCard k)

/-- The finite mass of the exact outer event family `\mathcal S_{I,\ell_R,\ell_B}` when `π(I)` is
uniformly distributed over the `k`-subsets of `V_R × V_B`. -/
def paperRIOuterEventMass (m lR lB k : ℕ) : ℝ :=
  ((paperRIOuterEventSet m lR lB k).card : ℝ) / ((m * m).choose k : ℝ)

theorem paperRIOuter_subset_product_images {m : ℕ} {S : Finset (Fin m × Fin m)} :
    S ⊆ (paperRIOuterRedImage S ×ˢ paperRIOuterBlueImage S) := by
  intro p hp
  rcases p with ⟨r, b⟩
  refine Finset.mem_product.2 ?_
  constructor
  · exact Finset.mem_image.2 ⟨(r, b), hp, rfl⟩
  · exact Finset.mem_image.2 ⟨(r, b), hp, rfl⟩

theorem mem_paperRIOuterWitnessSet_of_mem_paperRIOuterEventSet
    {m lR lB k : ℕ} {S : Finset (Fin m × Fin m)}
    (hS : S ∈ paperRIOuterEventSet m lR lB k) :
    Sigma.mk (paperRIOuterRedImage S, paperRIOuterBlueImage S) S ∈
      paperRIOuterWitnessSet m lR lB k := by
  rcases Finset.mem_filter.1 hS with ⟨hkset, himages⟩
  rcases himages with ⟨hredCard, hblueCard⟩
  have hk : S.card = k := (Finset.mem_powersetCard.1 hkset).2
  have hred :
      paperRIOuterRedImage S ∈ (Finset.univ : Finset (Fin m)).powersetCard lR := by
    refine Finset.mem_powersetCard.2 ?_
    constructor
    · exact Finset.subset_univ _
    · simpa using hredCard
  have hblue :
      paperRIOuterBlueImage S ∈ (Finset.univ : Finset (Fin m)).powersetCard lB := by
    refine Finset.mem_powersetCard.2 ?_
    constructor
    · exact Finset.subset_univ _
    · simpa using hblueCard
  have hsubset : S ⊆ paperRIOuterRedImage S ×ˢ paperRIOuterBlueImage S :=
    paperRIOuter_subset_product_images
  have hprod :
      S ∈ (paperRIOuterRedImage S ×ˢ paperRIOuterBlueImage S).powersetCard k := by
    exact Finset.mem_powersetCard.2 ⟨hsubset, hk⟩
  refine Finset.mem_sigma.2 ?_
  exact ⟨Finset.mem_product.2 ⟨hred, hblue⟩, hprod⟩

theorem paperRIOuterEventSet_card_le_witnessSet_card
    (m lR lB k : ℕ) :
    (paperRIOuterEventSet m lR lB k).card ≤ (paperRIOuterWitnessSet m lR lB k).card := by
  refine Finset.card_le_card_of_injOn
      (f := fun S => Sigma.mk (paperRIOuterRedImage S, paperRIOuterBlueImage S) S) ?_ ?_
  · intro S hS
    exact mem_paperRIOuterWitnessSet_of_mem_paperRIOuterEventSet hS
  · intro S hS T hT hEq
    exact congrArg Sigma.snd hEq

theorem paperRIOuterWitnessSet_card_eq_choose_choose_choose
    (m lR lB k : ℕ) :
    (paperRIOuterWitnessSet m lR lB k).card =
      (m.choose lR) * (m.choose lB) * ((lR * lB).choose k) := by
  let Aset : Finset (Finset (Fin m)) := (Finset.univ : Finset (Fin m)).powersetCard lR
  let Bset : Finset (Finset (Fin m)) := (Finset.univ : Finset (Fin m)).powersetCard lB
  calc
    (paperRIOuterWitnessSet m lR lB k).card =
        ∑ AB ∈ Aset ×ˢ Bset, (((AB.1 ×ˢ AB.2).powersetCard k).card) := by
      rw [paperRIOuterWitnessSet, Finset.card_sigma]
      simp [Aset, Bset]
    _ = ∑ _AB ∈ Aset ×ˢ Bset, ((lR * lB).choose k) := by
      refine Finset.sum_congr rfl ?_
      intro AB hAB
      rcases Finset.mem_product.1 hAB with ⟨hA, hB⟩
      have hAcard : AB.1.card = lR := (Finset.mem_powersetCard.1 hA).2
      have hBcard : AB.2.card = lB := (Finset.mem_powersetCard.1 hB).2
      rw [Finset.card_powersetCard, Finset.card_product, hAcard, hBcard]
    _ = (Aset ×ˢ Bset).card * ((lR * lB).choose k) := by
      simp
    _ = (Aset.card * Bset.card) * ((lR * lB).choose k) := by
      rw [Finset.card_product]
    _ = (m.choose lR) * (m.choose lB) * ((lR * lB).choose k) := by
      simp [Aset, Bset, Nat.mul_assoc]

/-- The exact finite outer event family from Paper Lemma `lem:RI` is bounded by the combinatorial
overcount that chooses red and blue coordinate images and then a `k`-subset of their product. -/
theorem paperRIOuterEventSet_card_le_choose_choose_choose
    (m lR lB k : ℕ) :
    (paperRIOuterEventSet m lR lB k).card ≤
      (m.choose lR) * (m.choose lB) * ((lR * lB).choose k) := by
  exact
    (paperRIOuterEventSet_card_le_witnessSet_card m lR lB k).trans
      (by rw [paperRIOuterWitnessSet_card_eq_choose_choose_choose])

/-- The combinatorial outer bound from the opening lines of Paper Lemma `lem:RI`. This packages
the counting term for the event `\mathcal S_{I,\ell_R,\ell_B}` before it is simplified
asymptotically. -/
def paperRIOuterCombBound (m lR lB k : ℕ) : ℝ :=
  ((m.choose lR : ℝ) * (m.choose lB : ℝ) * ((lR * lB).choose k : ℝ)) / ((m * m).choose k : ℝ)

/-- The corresponding finite mass bound for the exact outer event family `\mathcal S_{I,\ell_R,
\ell_B}`. This is the paper's first counting step before the later ratio and exponential
simplifications. -/
theorem paperRIOuterEventMass_le_outerCombBound
    {m lR lB k : ℕ} :
    paperRIOuterEventMass m lR lB k ≤ paperRIOuterCombBound m lR lB k := by
  have hcard :
      ((paperRIOuterEventSet m lR lB k).card : ℝ) ≤
        (m.choose lR : ℝ) * (m.choose lB : ℝ) * ((lR * lB).choose k : ℝ) := by
    exact_mod_cast paperRIOuterEventSet_card_le_choose_choose_choose m lR lB k
  unfold paperRIOuterEventMass paperRIOuterCombBound
  have hden : 0 ≤ (((m * m).choose k : ℕ) : ℝ) := by positivity
  exact
    (div_le_div_of_nonneg_right hcard hden).trans_eq <| by ring

/-- The raw binomial-ratio estimate behind the first finite counting step in Paper Lemma `lem:RI`.
It is the exact comparison obtained by bounding the numerator with `choose_le_pow_div` and the
denominator with `pow_le_choose`. -/
theorem paperRI_outerChooseRatio_le_pow_ratio
    {m lR lB k : ℕ} (hk : k ≤ m * m) :
    (((lR * lB).choose k : ℝ) / ((m * m).choose k : ℝ)) ≤
      (((lR * lB : ℕ) : ℝ) ^ k) / (((m * m + 1 - k : ℕ) : ℝ) ^ k) := by
  let num : ℝ := ((lR * lB).choose k : ℝ)
  let den : ℝ := ((m * m).choose k : ℝ)
  let up : ℝ := (((lR * lB : ℕ) : ℝ) ^ k) / ((Nat.factorial k : ℕ) : ℝ)
  let low : ℝ := ((((m * m + 1 - k : ℕ) ^ k : ℕ) : ℝ) / ((Nat.factorial k : ℕ) : ℝ))
  have hnum : num ≤ up := by
    simp [num, up]
    simpa using (Nat.choose_le_pow_div (α := ℝ) k (lR * lB))
  have hlow : low ≤ den := by
    simp [den, low]
    simpa [Nat.mul_comm] using (Nat.pow_le_choose (α := ℝ) k (m * m))
  have hnum_nonneg : 0 ≤ num := by positivity
  have hbaseNat : 0 < m * m + 1 - k := by
    omega
  have hlow_pos : 0 < low := by
    have hbase : 0 < (((m * m + 1 - k : ℕ) ^ k : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < (m * m + 1 - k : ℕ) ^ k by exact Nat.pow_pos hbaseNat)
    have hfact : 0 < (((Nat.factorial k : ℕ) : ℝ)) := by
      positivity
    exact div_pos hbase hfact
  have h1 : num / den ≤ num / low := by
    exact div_le_div_of_nonneg_left hnum_nonneg hlow_pos hlow
  have h2 : num / low ≤ up / low := by
    exact div_le_div_of_nonneg_right hnum hlow_pos.le
  have h3 : up / low = ((((lR * lB : ℕ) : ℝ) ^ k) / ((((m * m + 1 - k : ℕ) : ℝ) ^ k))) := by
    simp [up, low, div_eq_mul_inv]
    field_simp
  exact h1.trans (h2.trans (by simpa [num, den] using h3.le))

/-- The previous ratio estimate lifted to the full combinatorial outer bound from Paper Lemma
`lem:RI`. This is still a finite exact bound, before the later exponent simplifications. -/
theorem paperRIOuterCombBound_le_choose_choose_mul_pow_ratio
    {m lR lB k : ℕ} (hk : k ≤ m * m) :
    paperRIOuterCombBound m lR lB k ≤
      (m.choose lR : ℝ) * (m.choose lB : ℝ) *
        ((((lR * lB : ℕ) : ℝ) ^ k) / ((((m * m + 1 - k : ℕ) : ℝ) ^ k))) := by
  have hchoose_nonneg : 0 ≤ (m.choose lR : ℝ) * (m.choose lB : ℝ) := by
    positivity
  have hden_ne : (((m * m).choose k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  calc
    paperRIOuterCombBound m lR lB k =
        ((m.choose lR : ℝ) * (m.choose lB : ℝ)) *
          ((((lR * lB).choose k : ℝ) / ((m * m).choose k : ℝ))) := by
      unfold paperRIOuterCombBound
      field_simp [hden_ne]
    _ ≤ (m.choose lR : ℝ) * (m.choose lB : ℝ) *
          ((((lR * lB : ℕ) : ℝ) ^ k) / ((((m * m + 1 - k : ℕ) : ℝ) ^ k))) := by
      exact mul_le_mul_of_nonneg_left (paperRI_outerChooseRatio_le_pow_ratio hk) hchoose_nonneg

/-- The exact outer event family also satisfies the simplified power-ratio version of the paper's
counting bound. -/
theorem paperRIOuterEventMass_le_choose_choose_mul_pow_ratio
    {m lR lB k : ℕ} (hk : k ≤ m * m) :
    paperRIOuterEventMass m lR lB k ≤
      (m.choose lR : ℝ) * (m.choose lB : ℝ) *
        ((((lR * lB : ℕ) : ℝ) ^ k) / ((((m * m + 1 - k : ℕ) : ℝ) ^ k))) := by
  exact (paperRIOuterEventMass_le_outerCombBound).trans
    (paperRIOuterCombBound_le_choose_choose_mul_pow_ratio hk)

/-- The simplified choose/power-ratio upper bound for the outer event mass in Paper Lemma
`lem:RI`. This is the exact finite term that later gets converted into the manuscript's
exponential `eq:long` exponent. -/
def paperRIOuterPowRatioBound (m lR lB k : ℕ) : ℝ :=
  (m.choose lR : ℝ) * (m.choose lB : ℝ) *
    ((((lR * lB : ℕ) : ℝ) ^ k) / ((((m * m + 1 - k : ℕ) : ℝ) ^ k)))

theorem paperRIOuterEventMass_le_powRatioBound
    {m lR lB k : ℕ} (hk : k ≤ m * m) :
    paperRIOuterEventMass m lR lB k ≤ paperRIOuterPowRatioBound m lR lB k := by
  simpa [paperRIOuterPowRatioBound] using
    (paperRIOuterEventMass_le_choose_choose_mul_pow_ratio (m := m) (lR := lR)
      (lB := lB) (k := k) hk)

theorem paperRIOuterPowRatioBound_pos
    {m lR lB k : ℕ} (hk : k ≤ m * m) (hkpos : 0 < k)
    (hlR : lR ≤ m) (hlB : lB ≤ m) (hkprod : k ≤ lR * lB) :
    0 < paperRIOuterPowRatioBound m lR lB k := by
  have hchooseR : 0 < (m.choose lR : ℝ) := by
    exact_mod_cast Nat.choose_pos hlR
  have hchooseB : 0 < (m.choose lB : ℝ) := by
    exact_mod_cast Nat.choose_pos hlB
  have hprodBaseNat : 0 < lR * lB := by
    omega
  have hprodBase : 0 < ((lR * lB : ℕ) : ℝ) := by
    exact_mod_cast hprodBaseNat
  have hnum : 0 < (((lR * lB : ℕ) : ℝ) ^ k) := by
    exact pow_pos hprodBase k
  have hdenBaseNat : 0 < m * m + 1 - k := by
    omega
  have hden : 0 < ((((m * m + 1 - k : ℕ) : ℝ) ^ k)) := by
    exact_mod_cast (show 0 < (m * m + 1 - k : ℕ) ^ k by exact Nat.pow_pos hdenBaseNat)
  unfold paperRIOuterPowRatioBound
  exact mul_pos (mul_pos hchooseR hchooseB) (div_pos hnum hden)

theorem paperRIOuterEventMass_le_exp_log_powRatioBound
    {m lR lB k : ℕ} (hk : k ≤ m * m) (hkpos : 0 < k)
    (hlR : lR ≤ m) (hlB : lB ≤ m) (hkprod : k ≤ lR * lB) :
    paperRIOuterEventMass m lR lB k ≤
      Real.exp (Real.log (paperRIOuterPowRatioBound m lR lB k)) := by
  have hmass :
      paperRIOuterEventMass m lR lB k ≤ paperRIOuterPowRatioBound m lR lB k :=
    paperRIOuterEventMass_le_powRatioBound hk
  have hpos :
      0 < paperRIOuterPowRatioBound m lR lB k :=
    paperRIOuterPowRatioBound_pos hk hkpos hlR hlB hkprod
  simpa [Real.exp_log hpos] using hmass

theorem paperRIOuterEventMass_le_exp_of_log_powRatioBound_le
    {m lR lB k : ℕ} (hk : k ≤ m * m) (hkpos : 0 < k)
    (hlR : lR ≤ m) (hlB : lB ≤ m) (hkprod : k ≤ lR * lB)
    {outerExp : ℝ}
    (hlog :
      Real.log (paperRIOuterPowRatioBound m lR lB k) ≤ outerExp) :
    paperRIOuterEventMass m lR lB k ≤ Real.exp outerExp := by
  exact
    (paperRIOuterEventMass_le_exp_log_powRatioBound hk hkpos hlR hlB hkprod).trans
      (Real.exp_le_exp.mpr hlog)

theorem paperRIOuterPowRatioBound_log_eq
    {m lR lB k : ℕ} (hk : k ≤ m * m) (hkpos : 0 < k)
    (hlR : lR ≤ m) (hlB : lB ≤ m) (hkprod : k ≤ lR * lB) :
    Real.log (paperRIOuterPowRatioBound m lR lB k) =
      Real.log (m.choose lR : ℝ) + Real.log (m.choose lB : ℝ) +
        ((k : ℝ) * Real.log (((lR * lB : ℕ) : ℝ)) -
          (k : ℝ) * Real.log (((m * m + 1 - k : ℕ) : ℝ))) := by
  have hchooseR : 0 < (m.choose lR : ℝ) := by
    exact_mod_cast Nat.choose_pos hlR
  have hchooseB : 0 < (m.choose lB : ℝ) := by
    exact_mod_cast Nat.choose_pos hlB
  have hprodBaseNat : 0 < lR * lB := by
    omega
  have hprodBase : 0 < (((lR * lB : ℕ) : ℝ)) := by
    exact_mod_cast hprodBaseNat
  have hnum : 0 < ((((lR * lB : ℕ) : ℝ) ^ k)) := by
    exact pow_pos hprodBase k
  have hdenBaseNat : 0 < m * m + 1 - k := by
    omega
  have hdenBase : 0 < (((m * m + 1 - k : ℕ) : ℝ)) := by
    exact_mod_cast hdenBaseNat
  have hden : 0 < ((((m * m + 1 - k : ℕ) : ℝ) ^ k)) := by
    exact pow_pos hdenBase k
  unfold paperRIOuterPowRatioBound
  rw [Real.log_mul (mul_ne_zero hchooseR.ne' hchooseB.ne') (div_ne_zero hnum.ne' hden.ne'),
    Real.log_mul hchooseR.ne' hchooseB.ne',
    Real.log_div hnum.ne' hden.ne',
    Real.log_pow, Real.log_pow]

theorem paperRIOuterEventMass_le_exp_of_chooseLogs_le
    {m lR lB k : ℕ} (hk : k ≤ m * m) (hkpos : 0 < k)
    (hlR : lR ≤ m) (hlB : lB ≤ m) (hkprod : k ≤ lR * lB)
    {redLog blueLog outerExp : ℝ}
    (hred : Real.log (m.choose lR : ℝ) ≤ redLog)
    (hblue : Real.log (m.choose lB : ℝ) ≤ blueLog)
    (htotal :
      redLog + blueLog +
          ((k : ℝ) * Real.log (((lR * lB : ℕ) : ℝ)) -
            (k : ℝ) * Real.log (((m * m + 1 - k : ℕ) : ℝ))) ≤
        outerExp) :
    paperRIOuterEventMass m lR lB k ≤ Real.exp outerExp := by
  apply paperRIOuterEventMass_le_exp_of_log_powRatioBound_le hk hkpos hlR hlB hkprod
  rw [paperRIOuterPowRatioBound_log_eq hk hkpos hlR hlB hkprod]
  linarith

theorem choose_cast_le_exp_mul_div_pow
    {m l : ℕ} (hlpos : 0 < l) :
    (m.choose l : ℝ) ≤ Real.exp (l : ℝ) * (((m : ℝ) / l) ^ l) := by
  have hlposR : 0 < (l : ℝ) := by
    exact_mod_cast hlpos
  have hdiv_nonneg : 0 ≤ (m : ℝ) / l := by
    exact div_nonneg (Nat.cast_nonneg m) hlposR.le
  calc
    (m.choose l : ℝ) ≤ (m : ℝ) ^ l / ((l.factorial : ℕ) : ℝ) := by
      simpa using (Nat.choose_le_pow_div (α := ℝ) l m)
    _ = (((m : ℝ) / l) ^ l) * (((l : ℝ) ^ l) / ((l.factorial : ℕ) : ℝ)) := by
      rw [div_pow]
      field_simp [hlposR.ne']
    _ ≤ (((m : ℝ) / l) ^ l) * Real.exp (l : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.pow_div_factorial_le_exp (l : ℝ) (by positivity) l)
        (pow_nonneg hdiv_nonneg _)
    _ = Real.exp (l : ℝ) * (((m : ℝ) / l) ^ l) := by ring

theorem paperRI_logChoose_le
    {m l : ℕ} (hlpos : 0 < l) (hlm : l ≤ m) :
    Real.log (m.choose l : ℝ) ≤ (l : ℝ) * (1 + Real.log (m : ℝ) - Real.log (l : ℝ)) := by
  have hmposNat : 0 < m := lt_of_lt_of_le hlpos hlm
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast hmposNat
  have hlposR : 0 < (l : ℝ) := by
    exact_mod_cast hlpos
  have hchoosePos : 0 < (m.choose l : ℝ) := by
    exact_mod_cast Nat.choose_pos hlm
  have hratioPos : 0 < (((m : ℝ) / l) ^ l) := by
    exact pow_pos (div_pos hmpos hlposR) l
  have hbound :
      (m.choose l : ℝ) ≤ Real.exp (l : ℝ) * (((m : ℝ) / l) ^ l) :=
    choose_cast_le_exp_mul_div_pow (m := m) hlpos
  calc
    Real.log (m.choose l : ℝ) ≤ Real.log (Real.exp (l : ℝ) * (((m : ℝ) / l) ^ l)) := by
      exact Real.log_le_log hchoosePos hbound
    _ = (l : ℝ) + Real.log ((((m : ℝ) / l) ^ l)) := by
      rw [Real.log_mul (Real.exp_ne_zero _) hratioPos.ne', Real.log_exp]
    _ = (l : ℝ) + (l : ℝ) * Real.log ((m : ℝ) / l) := by
      rw [Real.log_pow]
    _ = (l : ℝ) + (l : ℝ) * (Real.log (m : ℝ) - Real.log (l : ℝ)) := by
      rw [Real.log_div hmpos.ne' hlposR.ne']
    _ = (l : ℝ) * (1 + Real.log (m : ℝ) - Real.log (l : ℝ)) := by
      ring

theorem paperRIOuterEventMass_le_exp_of_logChooseFormula_le
    {m lR lB k : ℕ} (hk : k ≤ m * m) (hkpos : 0 < k)
    (hlR : lR ≤ m) (hlB : lB ≤ m) (hkprod : k ≤ lR * lB)
    {outerExp : ℝ}
    (htotal :
      (lR : ℝ) * (1 + Real.log (m : ℝ) - Real.log (lR : ℝ)) +
          (lB : ℝ) * (1 + Real.log (m : ℝ) - Real.log (lB : ℝ)) +
          ((k : ℝ) * Real.log (((lR * lB : ℕ) : ℝ)) -
            (k : ℝ) * Real.log (((m * m + 1 - k : ℕ) : ℝ))) ≤
        outerExp) :
    paperRIOuterEventMass m lR lB k ≤ Real.exp outerExp := by
  have hmulpos : 0 < lR * lB := lt_of_lt_of_le hkpos hkprod
  have hlRpos : 0 < lR := by
    refine Nat.pos_of_ne_zero ?_
    intro hR
    subst hR
    simp at hmulpos
  have hlBpos : 0 < lB := by
    refine Nat.pos_of_ne_zero ?_
    intro hB
    subst hB
    simp at hmulpos
  apply paperRIOuterEventMass_le_exp_of_chooseLogs_le hk hkpos hlR hlB hkprod
  · exact paperRI_logChoose_le hlRpos hlR
  · exact paperRI_logChoose_le hlBpos hlB
  · exact htotal

theorem paperRI_smallSumCoeff_le
    {ε x : ℝ} (hsum : x ≤ 1 - ε / 2) :
    -(1 - x) / 2 ≤ -ε / 4 := by
  nlinarith

theorem paperRI_smallSumCoeff_neg {ε : ℝ} (hε : 0 < ε) :
    -ε / 4 < (0 : ℝ) := by
  nlinarith

theorem paperRI_eqLongCoeff_neg_of_smallSum
    {ε x : ℝ} (hε : 0 < ε) (hsum : x ≤ 1 - ε / 2) :
    -(1 - x) / 2 < (0 : ℝ) := by
  calc
    -(1 - x) / 2 ≤ -ε / 4 :=
      paperRI_smallSumCoeff_le hsum
    _ < 0 :=
      paperRI_smallSumCoeff_neg hε

theorem paperRI_largeSumCoeff_eq
    {ε x : ℝ} :
    (x - 1) / 2 -
        ((1 / 2 : ℝ) * (-2 * (1 + ε) + 2 * (1 + ε) * x - 2 * ε ^ 3 * (1 + ε)) / 2) =
      -(ε * (x - 1 - ε ^ 2 - ε ^ 3)) / 2 := by
  ring

theorem paperRI_largeSumCoeff_le_final
    {ε x : ℝ} (hε0 : 0 ≤ ε) (hsum : 1 + ε / 2 ≤ x) :
    -(ε * (x - 1 - ε ^ 2 - ε ^ 3)) / 2 ≤
      -(ε ^ 2 * (1 - 2 * ε - 2 * ε ^ 2)) / 4 := by
  nlinarith

theorem paperRI_largeSum_finalCoeff_neg
    {ε : ℝ} (hε : 0 < ε) (hpos : 0 < 1 - 2 * ε - 2 * ε ^ 2) :
    -(ε ^ 2 * (1 - 2 * ε - 2 * ε ^ 2)) / 4 < (0 : ℝ) := by
  have hsq : 0 < ε ^ 2 := by positivity
  have hnum : -(ε ^ 2 * (1 - 2 * ε - 2 * ε ^ 2)) < 0 := by
    nlinarith
  have hden : (0 : ℝ) < 4 := by positivity
  exact div_neg_of_neg_of_pos hnum hden

theorem paperRI_eqLongCoeff_neg_of_largeSum
    {ε x : ℝ} (hε : 0 < ε) (hpos : 0 < 1 - 2 * ε - 2 * ε ^ 2)
    (hsum : 1 + ε / 2 ≤ x) :
    (x - 1) / 2 -
        ((1 / 2 : ℝ) * (-2 * (1 + ε) + 2 * (1 + ε) * x - 2 * ε ^ 3 * (1 + ε)) / 2) <
      (0 : ℝ) := by
  calc
    (x - 1) / 2 -
        ((1 / 2 : ℝ) * (-2 * (1 + ε) + 2 * (1 + ε) * x - 2 * ε ^ 3 * (1 + ε)) / 2) =
      -(ε * (x - 1 - ε ^ 2 - ε ^ 3)) / 2 :=
        paperRI_largeSumCoeff_eq
    _ ≤ -(ε ^ 2 * (1 - 2 * ε - 2 * ε ^ 2)) / 4 :=
      paperRI_largeSumCoeff_le_final hε.le hsum
    _ < 0 :=
      paperRI_largeSum_finalCoeff_neg hε hpos

theorem paperRI_eqLongCoeff_neg_of_nearOne
    {ε xR xB : ℝ}
    (hε : 0 < ε)
    (hεsmall : 8 * (1 + ε) ^ 2 ≤ (9 : ℝ))
    (hsumLower : 1 - ε / 2 ≤ xR + xB)
    (hsumUpper : xR + xB ≤ 1 + ε / 2)
    (hblue : xB ≤ xR)
    (hneg : -1 + ε + 22 * ε ^ 2 < 0) :
    -(1 - xR - xB) / 2 -
        (1 / (4 * (1 + ε))) *
          (-2 * (1 + ε) ^ 2 + 2 * (1 + ε) ^ 2 * (xR + xB) + (1 + ε) -
            xB * (1 + ε) - (1 / 2 : ℝ) - 2 * ε ^ 3 * (1 + ε) ^ 2) <
      (0 : ℝ) := by
  calc
    -(1 - xR - xB) / 2 -
        (1 / (4 * (1 + ε))) *
          (-2 * (1 + ε) ^ 2 + 2 * (1 + ε) ^ 2 * (xR + xB) + (1 + ε) -
            xB * (1 + ε) - (1 / 2 : ℝ) - 2 * ε ^ 3 * (1 + ε) ^ 2) =
      (1 / (8 * (1 + ε))) *
        (2 * xB - 1 - (4 * ε ^ 2 + 2 * ε) * (xR + xB - 1) - 2 * ε * xR +
          4 * ε ^ 3 * (1 + ε) ^ 2) :=
        paperRI_nearOne_mixedCoeff_eq hε.le
    _ ≤ ε * (-1 + ε + 22 * ε ^ 2) / (16 * (1 + ε)) :=
      paperRI_nearOne_mixedCoeff_le_final hε.le hεsmall hsumLower hsumUpper hblue
    _ < 0 :=
      paperRI_nearOne_finalCoeff_neg hε hneg

theorem paperRI_eqLongExp_neg_of_smallSum
    {ε x : ℝ} {n : ℕ}
    (hn : 1 < n) (hε : 0 < ε) (hsum : x ≤ 1 - ε / 2) :
    (-(1 - x) / 2) * paperK (1 + ε) n * Real.log (n : ℝ) < 0 := by
  have hcoeff : -(1 - x) / 2 < (0 : ℝ) := paperRI_eqLongCoeff_neg_of_smallSum hε hsum
  have hkpos : 0 < paperK (1 + ε) n := by
    have hκ : 0 < 1 + ε := by nlinarith
    exact paperK_pos hκ hn
  have hlogpos : 0 < Real.log (n : ℝ) := paperLog_pos hn
  have hfac : 0 < paperK (1 + ε) n * Real.log (n : ℝ) := by
    exact mul_pos hkpos hlogpos
  nlinarith [mul_neg_of_neg_of_pos hcoeff hfac]

theorem paperRI_eqLongExp_neg_of_largeSum
    {ε x : ℝ} {n : ℕ}
    (hn : 1 < n) (hε : 0 < ε) (hpos : 0 < 1 - 2 * ε - 2 * ε ^ 2)
    (hsum : 1 + ε / 2 ≤ x) :
    ((x - 1) / 2 -
        ((1 / 2 : ℝ) * (-2 * (1 + ε) + 2 * (1 + ε) * x - 2 * ε ^ 3 * (1 + ε)) / 2)) *
      paperK (1 + ε) n * Real.log (n : ℝ) < 0 := by
  have hcoeff :
      (x - 1) / 2 -
          ((1 / 2 : ℝ) * (-2 * (1 + ε) + 2 * (1 + ε) * x - 2 * ε ^ 3 * (1 + ε)) / 2) <
        (0 : ℝ) := paperRI_eqLongCoeff_neg_of_largeSum hε hpos hsum
  have hkpos : 0 < paperK (1 + ε) n := by
    have hκ : 0 < 1 + ε := by nlinarith
    exact paperK_pos hκ hn
  have hlogpos : 0 < Real.log (n : ℝ) := paperLog_pos hn
  have hfac : 0 < paperK (1 + ε) n * Real.log (n : ℝ) := by
    exact mul_pos hkpos hlogpos
  nlinarith [mul_neg_of_neg_of_pos hcoeff hfac]

theorem paperRI_eqLongExp_neg_of_nearOne
    {ε xR xB : ℝ} {n : ℕ}
    (hn : 1 < n) (hε : 0 < ε)
    (hεsmall : 8 * (1 + ε) ^ 2 ≤ (9 : ℝ))
    (hsumLower : 1 - ε / 2 ≤ xR + xB)
    (hsumUpper : xR + xB ≤ 1 + ε / 2)
    (hblue : xB ≤ xR)
    (hneg : -1 + ε + 22 * ε ^ 2 < 0) :
    (-(1 - xR - xB) / 2 -
        (1 / (4 * (1 + ε))) *
          (-2 * (1 + ε) ^ 2 + 2 * (1 + ε) ^ 2 * (xR + xB) + (1 + ε) -
            xB * (1 + ε) - (1 / 2 : ℝ) - 2 * ε ^ 3 * (1 + ε) ^ 2)) *
      paperK (1 + ε) n * Real.log (n : ℝ) < 0 := by
  have hcoeff :
      -(1 - xR - xB) / 2 -
          (1 / (4 * (1 + ε))) *
            (-2 * (1 + ε) ^ 2 + 2 * (1 + ε) ^ 2 * (xR + xB) + (1 + ε) -
              xB * (1 + ε) - (1 / 2 : ℝ) - 2 * ε ^ 3 * (1 + ε) ^ 2) <
        (0 : ℝ) :=
    paperRI_eqLongCoeff_neg_of_nearOne hε hεsmall hsumLower hsumUpper hblue hneg
  have hkpos : 0 < paperK (1 + ε) n := by
    have hκ : 0 < 1 + ε := by nlinarith
    exact paperK_pos hκ hn
  have hlogpos : 0 < Real.log (n : ℝ) := paperLog_pos hn
  have hfac : 0 < paperK (1 + ε) n * Real.log (n : ℝ) := by
    exact mul_pos hkpos hlogpos
  nlinarith [mul_neg_of_neg_of_pos hcoeff hfac]

end

end Twobites
