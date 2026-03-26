import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

theorem paperP_pos {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 1 < n) : 0 < paperP β n := by
  unfold paperP
  refine mul_pos hβ ?_
  apply Real.sqrt_pos.2
  exact div_pos (paperLog_pos hn) (by exact_mod_cast (lt_trans Nat.zero_lt_one hn))

theorem paperK_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) : 0 ≤ paperK κ n := by
  unfold paperK
  exact mul_nonneg hκ (Real.sqrt_nonneg _)

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

theorem paperKNat_lt_mul_ceil_paperT1_sub_choose_mul_iff
    {κ : ℝ} {n witnessSize codegreeBound : ℕ} :
    paperKNat κ n < witnessSize * ⌈paperT1 n⌉₊ - witnessSize.choose 2 * codegreeBound ↔
      paperKNat κ n + witnessSize.choose 2 * codegreeBound < witnessSize * ⌈paperT1 n⌉₊ :=
  Nat.lt_sub_iff_add_lt

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

end

end Twobites
