import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

theorem paperK_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) : 0 ≤ paperK κ n := by
  unfold paperK
  exact mul_nonneg hκ (Real.sqrt_nonneg _)

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
