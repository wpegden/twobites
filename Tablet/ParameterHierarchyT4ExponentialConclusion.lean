import Tablet.RealChooseTwo
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: ParameterHierarchyT4ExponentialConclusion]

theorem ParameterHierarchyT4ExponentialConclusion :
    ∀ η : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let K := TwoBiteNaturalIndependenceScale (1 + η) n
      let k := (K : ℝ)
      let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
      0 < (n : ℝ) →
      0 ≤ k * L →
      (Nat.choose n K : ℝ) ≤ Real.exp (k * L) →
      2 * k * L + L ≤
        RealChooseTwo k ^ 2 /
          (L * m * Real.rpow (n : ℝ) (8 * η)) →
      Real.exp
          (-(RealChooseTwo k ^ 2 /
              (L * m * Real.rpow (n : ℝ) (8 * η)))) *
        (Nat.choose n K : ℝ) ≤ (n : ℝ)⁻¹ := by
-- BODY
  intro η n
  dsimp
  let L := Real.log (n : ℝ)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
  intro hn_pos hkL_nonneg hchoose hA
  let A := RealChooseTwo k ^ 2 / (L * m * Real.rpow (n : ℝ) (8 * η))
  have hL_exp : Real.exp L = (n : ℝ) := by
    dsimp [L]
    exact Real.exp_log hn_pos
  have hA' : k * L + -A ≤ -L := by
    dsimp [A] at hA ⊢
    nlinarith
  have hexp_bound : Real.exp (k * L + -A) ≤ Real.exp (-L) :=
    Real.exp_le_exp.mpr hA'
  have hprod_exp : Real.exp (-A) * Real.exp (k * L) = Real.exp (k * L + -A) := by
    rw [← Real.exp_add]
    ring_nf
  calc
    Real.exp (-A) * (Nat.choose n K : ℝ)
        ≤ Real.exp (-A) * Real.exp (k * L) :=
          mul_le_mul_of_nonneg_left hchoose (Real.exp_pos _).le
    _ = Real.exp (k * L + -A) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod_exp
    _ ≤ Real.exp (-L) := hexp_bound
    _ = (n : ℝ)⁻¹ := by
      rw [Real.exp_neg, hL_exp]
