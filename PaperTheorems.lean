import Twobites.IndependentSets

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

/-- A triangle-free Ramsey witness on `n` vertices restricts to one on any smaller vertex set.
This is the monotonicity input needed when later relating witness-form lower bounds to the local
Ramsey-number definition. -/
theorem triangleFreeRamseyWitness_mono {n k : ℕ}
    (hW : triangleFreeRamseyWitness n k) {m : ℕ} (hmn : m ≤ n) :
    triangleFreeRamseyWitness m k := by
  classical
  rcases hW with ⟨G, hclique, hfree⟩
  let emb : Fin m ↪ Fin n := Fin.castLEEmb hmn
  refine ⟨G.comap emb, ?_, ?_⟩
  · exact SimpleGraph.CliqueFree.comap (f := SimpleGraph.Embedding.comap emb G) hclique
  · intro t ht
    apply hfree (t.map emb)
    refine ⟨?_, by simp [ht.card_eq]⟩
    intro a ha b hb hab
    rcases Finset.mem_map.1 ha with ⟨a', ha', rfl⟩
    rcases Finset.mem_map.1 hb with ⟨b', hb', rfl⟩
    have hab' : a' ≠ b' := by
      intro hEq
      apply hab
      simp [hEq]
    exact ht.isIndepSet ha' hb' hab'

/-- A theorem-level wrapper isolating the last missing ingredient for Theorem `main`: once the
global random-construction layer produces a `ConstructionData` whose final graph has no surviving
independent set of size `paperKNat (1 + ε) n`, the paper-facing existence statement follows
immediately from the deterministic final-graph endpoint. -/
theorem paperMainStatement_of_eventually_exists_finalGraphWitness
    (hexists :
      ∀ ε > 0, ∃ n0 : ℕ, ∀ ⦃n : ℕ⦄, n ≥ n0 →
        ∃ m : ℕ,
          ∃ C : ConstructionData n m,
            ConstructionData.NoSurvivingIndepSetCard C (Twobites.paperKNat (1 + ε) n)) :
    paperMainStatement := by
  intro ε hε
  rcases hexists ε hε with ⟨n0, hn0⟩
  refine ⟨n0, ?_⟩
  intro n hn
  rcases hn0 hn with ⟨m, C, hnot⟩
  exact ConstructionData.triangleFreeWithSmallIndepNum_of_noSurvivingIndepSetCard C hnot

/-- The witness-form `main2` statement follows from an eventual supply of final graphs whose
`k`-subsets all fail to survive as independent sets. This isolates the remaining global existence
work from the deterministic Ramsey-witness packaging. -/
theorem paperMain2WitnessStatement_of_eventually_exists_finalGraphWitness
    (hexists :
      ∀ ε > 0, ∃ k0 : ℕ, ∀ ⦃k : ℕ⦄, k ≥ k0 →
        ∃ n : ℕ, ∃ m : ℕ,
          (((1 / 2 : ℝ) - ε) * (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ (n : ℝ)) ∧
          ∃ C : ConstructionData n m, ConstructionData.NoSurvivingIndepSetCard C k) :
    paperMain2WitnessStatement := by
  intro ε hε
  rcases hexists ε hε with ⟨k0, hk0⟩
  refine ⟨k0, ?_⟩
  intro k hk
  rcases hk0 hk with ⟨n, m, hbound, C, hnot⟩
  refine ⟨n, hbound, ?_⟩
  exact ConstructionData.triangleFreeRamseyWitness_of_noSurvivingIndepSetCard C hnot

end

end Twobites
