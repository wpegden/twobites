import Twobites.PaperDefinitions

namespace Twobites

noncomputable section

/-- Paper Theorem `main`: for every positive `ε`, sufficiently large `n` admit a triangle-free graph
with independence number below `(1 + ε) * sqrt (n log n)`. -/
def paperMainStatement : Prop :=
  ∀ ε > 0, ∃ n0 : ℕ, ∀ ⦃n : ℕ⦄, n ≥ n0 → triangleFreeWithSmallIndepNum ε n

/-- A witness-form version of Paper Theorem `main2`, closer to the actual output of Theorem
`main`. This avoids the `+1` bookkeeping hidden in the Ramsey-number definition. -/
def paperMain2WitnessStatement : Prop :=
  ∀ ε > 0, ∃ k0 : ℕ, ∀ ⦃k : ℕ⦄, k ≥ k0 →
    ∃ n : ℕ,
      (((1 / 2 : ℝ) - ε) * (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ (n : ℝ)) ∧
        triangleFreeRamseyWitness n k

/-- Paper Theorem `main2`, stated using the local Ramsey-number definition from
`PaperDefinitions.lean`. -/
def paperMain2Statement : Prop :=
  ∀ ε > 0, ∃ k0 : ℕ, ∀ ⦃k : ℕ⦄, k ≥ k0 →
    (((1 / 2 : ℝ) - ε) * (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ (triangleRamseyNumber k : ℝ))

end

end Twobites
