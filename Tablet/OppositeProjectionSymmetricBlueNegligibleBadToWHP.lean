import Tablet.WithHighProbability
import Tablet.NegligibleProbability
import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.TwoBiteEventProbabilityTotalMassBound
import Tablet.TwoBiteNaturalTotalMassOneEventually

-- [TABLET NODE: OppositeProjectionSymmetricBlueNegligibleBadToWHP]

theorem OppositeProjectionSymmetricBlueNegligibleBadToWHP :
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        NegligibleProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                let sizeBound : Prop :=
                  ∀ x : TwoBiteBaseVertex (m n),
                  ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                    2 * TwoBiteEdgeProbability β n * (n : ℝ)
                let blueBad : Prop :=
                  ∃ b c : Fin (m n), b ≠ c ∧
                  (((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                        (TwoBiteRedProjection ω)) ∩
                      ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                        (TwoBiteRedProjection ω))).card : ℝ)
                    >
                    (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                        TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
                      100 * (Real.log (n : ℝ)) ^ 3))
                sizeBound ∧ blueBad)) →
        WithHighProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                let sizeBound : Prop :=
                  ∀ x : TwoBiteBaseVertex (m n),
                  ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                    2 * TwoBiteEdgeProbability β n * (n : ℝ)
                let blueBound : Prop :=
                  ∀ b c : Fin (m n), b ≠ c →
                  ((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                        (TwoBiteRedProjection ω)) ∩
                      ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                        (TwoBiteRedProjection ω))).card : ℝ)
                    ≤
                    (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                        TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
                      100 * (Real.log (n : ℝ)) ^ 3)
                sizeBound → blueBound)) := by
-- BODY
  classical
  intro β hβ m hm hBad
  unfold WithHighProbability
  unfold NegligibleProbability at hBad
  let p : ℕ → ℝ := fun n => TwoBiteEdgeProbability β n
  let Good : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω =>
      let sizeBound : Prop :=
        ∀ x : TwoBiteBaseVertex (m n),
        ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
          2 * p n * (n : ℝ)
      let blueBound : Prop :=
        ∀ b c : Fin (m n), b ≠ c →
        ((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
              (TwoBiteRedProjection ω)) ∩
            ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
              (TwoBiteRedProjection ω))).card : ℝ)
          ≤
          (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
            100 * (Real.log (n : ℝ)) ^ 3)
      sizeBound → blueBound
  let Bad : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω =>
      let sizeBound : Prop :=
        ∀ x : TwoBiteBaseVertex (m n),
        ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
          2 * p n * (n : ℝ)
      let blueBad : Prop :=
        ∃ b c : Fin (m n), b ≠ c ∧
        (((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
              (TwoBiteRedProjection ω)) ∩
            ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
              (TwoBiteRedProjection ω))).card : ℝ)
          >
          (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
            100 * (Real.log (n : ℝ)) ^ 3))
      sizeBound ∧ blueBad
  have hBad' :
      Filter.Tendsto
        (fun n =>
          TwoBiteEventProbability n (m n) (p n) (Bad n))
        Filter.atTop (nhds (0 : ℝ)) := by
    simpa [p, Bad] using hBad
  have htotal := TwoBiteNaturalTotalMassOneEventually β hβ m hm
  have hprob_eq :
      ∀ᶠ n in Filter.atTop,
        TwoBiteEventProbability n (m n) (p n) (Good n) =
          1 - TwoBiteEventProbability n (m n) (p n) (Bad n) := by
    filter_upwards [htotal] with n htot
    have hcompl : ∀ ω : TwoBiteSample n (m n) (p n), Bad n ω ↔ ¬ Good n ω := by
      intro ω
      dsimp [Bad, Good, p]
      constructor
      · rintro ⟨hsize, hbad⟩ hgood
        rcases hbad with ⟨b, c, hne, hgt⟩
        have hle := hgood hsize b c hne
        linarith
      · intro hnot
        by_cases hsize :
            ∀ x : TwoBiteBaseVertex (m n),
              ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                2 * TwoBiteEdgeProbability β n * (n : ℝ)
        · refine ⟨hsize, ?_⟩
          by_contra hnoBad
          apply hnot
          intro _hsize b c hne
          by_contra hnotle
          have hgt :
              (((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                    (TwoBiteRedProjection ω)) ∩
                  ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                    (TwoBiteRedProjection ω))).card : ℝ)
                >
                (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                    TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
                  100 * (Real.log (n : ℝ)) ^ 3)) :=
            lt_of_not_ge hnotle
          exact hnoBad ⟨b, c, hne, hgt⟩
        · exfalso
          apply hnot
          intro hsize'
          exact False.elim (hsize hsize')
    have hsum :
        TwoBiteEventProbability n (m n) (p n) (Good n) +
          TwoBiteEventProbability n (m n) (p n) (Bad n) =
            TwoBiteEventProbability n (m n) (p n) (fun _ => True) := by
      unfold TwoBiteEventProbability
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hgood : Good n ω
      · have hnotbad : ¬ Bad n ω := by
          intro hbadω
          exact (hcompl ω).1 hbadω hgood
        simp [hgood, hnotbad]
      · have hbadω : Bad n ω := (hcompl ω).2 hgood
        simp [hgood, hbadω]
    have htotal_one : TwoBiteEventProbability n (m n) (p n) (fun _ => True) = 1 := by
      simpa [p] using htot.2
    linarith
  have htend :
      Filter.Tendsto
        (fun n => 1 - TwoBiteEventProbability n (m n) (p n) (Bad n))
        Filter.atTop (nhds (1 : ℝ)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) :=
      tendsto_const_nhds
    have hsub := hconst.sub hBad'
    simpa using hsub
  have hprob_eq_symm :
      (fun n => 1 - TwoBiteEventProbability n (m n) (p n) (Bad n))
        =ᶠ[Filter.atTop]
      (fun n => TwoBiteEventProbability n (m n) (p n) (Good n)) :=
    hprob_eq.mono (fun n hn => hn.symm)
  have hfinal :
      Filter.Tendsto
        (fun n => TwoBiteEventProbability n (m n) (p n) (Good n))
        Filter.atTop (nhds (1 : ℝ)) :=
    Filter.Tendsto.congr' hprob_eq_symm htend
  simpa [p, Good] using hfinal
