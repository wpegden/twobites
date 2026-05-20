import Tablet.HypergeometricMgfBinomialDomination
import Tablet.HypergeometricMgfExpBound
open Real

-- [TABLET NODE: HypergeometricMgfComparison]

theorem HypergeometricMgfComparison :
  ∀ N n m : ℕ, n ≤ N → m ≤ N →
  ∀ (M : Finset (Fin N)), M.card = m →
  ∀ L : ℝ,
  let q : ℝ := (m : ℝ) / (N : ℝ)
  let μ : ℝ := (n : ℝ) * q
  let Y_mgf : ℝ := (Nat.choose N n : ℝ)⁻¹ * ∑ S ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)), exp (L * (S ∩ M).card)
  Y_mgf ≤ (1 - q + q * exp L) ^ n ∧
  (1 - q + q * exp L) ^ n ≤ exp (μ * (exp L - 1)) := by
-- BODY
  intro N n m hnN hmN M hM L
  constructor
  · exact HypergeometricMgfBinomialDomination N n m hnN hmN M hM L
  · exact HypergeometricMgfExpBound N n m hmN L
