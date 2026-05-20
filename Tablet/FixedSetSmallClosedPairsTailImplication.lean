import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Tablet.Preamble

-- [TABLET NODE: FixedSetSmallClosedPairsTailImplication]

theorem FixedSetSmallClosedPairsTailImplication
    {K L C ε1 : ℝ}
    {C_I A_int A_sf Z_I mu t : ℝ}
    (h_decomp : C_I ≤ A_int + A_sf + Z_I)
    (h_A_int : A_int ≤ (ε1 / 2) * K ^ 2)
    (h_A_sf : A_sf ≤ 2 * K * L ^ 2)
    (h_mu : mu ≤ C / (2 * L))
    (h_t : t = C / Real.sqrt L)
    (h_hier1 : (1 / (2 * L)) * C + 2 * K * L ^ 2 + (1 / Real.sqrt L) * C ≤ (2 / Real.sqrt L) * C)
    (h_hier2 : (2 / Real.sqrt L) * C ≤ (ε1 / 2) * K ^ 2) :
    C_I > ε1 * K ^ 2 → Z_I ≥ mu + t := by
-- BODY
  intro h_fail
  by_contra h_not
  push Not at h_not
  have h1 : A_sf + Z_I < 2 * K * L ^ 2 + C / (2 * L) + C / Real.sqrt L := by linarith
  have h2 : 2 * K * L ^ 2 + C / (2 * L) + C / Real.sqrt L = (1 / (2 * L)) * C + 2 * K * L ^ 2 + (1 / Real.sqrt L) * C := by ring
  have h3 : A_sf + Z_I < (2 / Real.sqrt L) * C := by linarith
  have h4 : A_sf + Z_I < (ε1 / 2) * K ^ 2 := by linarith
  have h5 : C_I < ε1 * K ^ 2 := by linarith
  linarith
