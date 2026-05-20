import Tablet.Preamble

open Real

-- [TABLET NODE: HypergeometricMgfExpBound]

theorem HypergeometricMgfExpBound :
    ∀ N n m : ℕ, m ≤ N →
    ∀ L : ℝ,
    let q : ℝ := (m : ℝ) / (N : ℝ)
    let μ : ℝ := (n : ℝ) * q
    (1 - q + q * exp L) ^ n ≤ exp (μ * (exp L - 1)) := by
-- BODY
  intro N n m hmN L
  dsimp
  let q : ℝ := (m : ℝ) / (N : ℝ)
  have hq_nonneg : 0 ≤ q :=
    div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg N)
  have hq_le_one : q ≤ 1 := by
    by_cases hN : N = 0
    · subst N
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hmN
      simp [q, hm0]
    · have hN_pos_nat : 0 < N := Nat.pos_of_ne_zero hN
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos_nat
      have hmN_real : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
      rw [div_le_one hN_pos]
      exact hmN_real
  have hbase_nonneg : 0 ≤ 1 - q + q * exp L := by
    have hexp_nonneg : 0 ≤ exp L := (exp_pos L).le
    have h_one_sub : 0 ≤ 1 - q := by linarith
    nlinarith [mul_nonneg hq_nonneg hexp_nonneg]
  have hbase_le : 1 - q + q * exp L ≤ exp (q * (exp L - 1)) := by
    calc
      1 - q + q * exp L = q * (exp L - 1) + 1 := by ring
      _ ≤ exp (q * (exp L - 1)) := Real.add_one_le_exp _
  calc
    (1 - q + q * exp L) ^ n ≤ (exp (q * (exp L - 1))) ^ n :=
      pow_le_pow_left₀ hbase_nonneg hbase_le n
    _ = exp ((n : ℝ) * (q * (exp L - 1))) := by
      rw [← Real.exp_nat_mul]
    _ = exp (((n : ℝ) * q) * (exp L - 1)) := by
      ring_nf
