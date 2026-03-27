import Mathlib.Algebra.Order.Floor.Semiring
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

end

end Twobites
