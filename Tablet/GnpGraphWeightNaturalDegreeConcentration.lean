import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne
import Tablet.GnpAllVerticesDegreeFailureUnionBound
import Tablet.BernoulliMgfTailEnvelope
import Tablet.BernoulliMgfEnvelopeFiniteBridge
import Tablet.NaturalDegreeExponentialEnvelopeNegligible
import Tablet.GnpVertexDegreeMarkovTailBounds
import Tablet.GnpVertexDegreeUpperTailUnionBound
import Tablet.GnpVertexIncidentEdgeGeneratingFunction
import Tablet.GnpVertexCylinderSum
import Tablet.GraphDegreeCount
import Tablet.WithinRelativeError
import Tablet.NegligibleProbability
import Tablet.ProductWeightSumOne
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.OppositeProjectionEdgeProbBounds

open Filter
open Classical

-- [TABLET NODE: GnpGraphWeightNaturalDegreeConcentration]

theorem GnpGraphWeightNaturalDegreeConcentration :
    ∀ ε β : ℝ, 0 < ε → β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        NegligibleProbability
          (fun n =>
            ∑ G : SimpleGraph (Fin (m n)),
              if ¬ ∀ v : Fin (m n),
                  WithinRelativeError ε
                    (TwoBiteEdgeProbability β n * (m n : ℝ))
                    (GraphDegreeCount G v : ℝ)
              then GnpGraphWeight (TwoBiteEdgeProbability β n) G else 0) := by
-- BODY
  intro ε β hε hβ m hm
  subst β
  have hVertexCylinder :
      ∀ (m : ℕ) (p : ℝ) (S : Finset (Fin m)) (r : Fin m),
        r ∉ S →
          (∑ G : SimpleGraph (Fin m),
            if (∀ t ∈ S, G.Adj r t) then GnpGraphWeight p G else 0) =
          p ^ S.card := by
    intro m p S r hr
    exact GnpVertexCylinderSum m p S r hr
  have hIncidentGeneratingFunction :
      ∀ (m : ℕ) (p z : ℝ) (r : Fin m),
        (∑ G : SimpleGraph (Fin m),
          (∏ e : {e : Fin m × Fin m // e.1.val < e.2.val},
            if e.1.1 = r ∨ e.1.2 = r then
              if G.Adj e.1.1 e.1.2 then z else 1
            else 1) *
          GnpGraphWeight p G) =
        (1 - p + p * z) ^
          ((Finset.univ.filter
            (fun e : {e : Fin m × Fin m // e.1.val < e.2.val} =>
              e.1.1 = r ∨ e.1.2 = r)).card) := by
    intro m p z r
    exact GnpVertexIncidentEdgeGeneratingFunction m p z r
  have hDegreeMarkovTailBounds := GnpVertexDegreeMarkovTailBounds
  have hDegreeUpperTailUnionBound := GnpVertexDegreeUpperTailUnionBound
  have hAllVerticesDegreeFailureUnionBound := GnpAllVerticesDegreeFailureUnionBound
  have hBernoulliMgfTailEnvelope := BernoulliMgfTailEnvelope
  have hBernoulliMgfEnvelopeFiniteBridge := BernoulliMgfEnvelopeFiniteBridge
  have hNaturalDegreeExponentialEnvelopeNegligible :=
    NaturalDegreeExponentialEnvelopeNegligible
  let δ : ℝ := min ε 1
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hε zero_lt_one
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_right ε 1
  have hδ_le_ε : δ ≤ ε := by
    dsimp [δ]
    exact min_le_left ε 1
  let prob : ℕ → ℝ := fun n =>
    ∑ G : SimpleGraph (Fin (m n)),
      if ¬ ∀ v : Fin (m n),
          WithinRelativeError ε
            (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ))
            (GraphDegreeCount G v : ℝ)
      then GnpGraphWeight (TwoBiteEdgeProbability (1 / 2 : ℝ) n) G else 0
  let simple : ℕ → ℝ := fun n =>
    let M : ℝ := (m n : ℝ)
    let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
    let c : ℝ := δ ^ 2 / 100
    M * (Real.exp (-(c * p * M)) + Real.exp (-(c * p * M)))
  change Filter.Tendsto prob Filter.atTop (nhds (0 : ℝ))
  have hGnp_nonneg :
      ∀ (M : ℕ) (p : ℝ), 0 ≤ p → p ≤ 1 →
        ∀ G : SimpleGraph (Fin M), 0 ≤ GnpGraphWeight p G := by
    intro M p hp0 hp1 G
    unfold GnpGraphWeight
    apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact hp0
    · linarith
  have hp_bounds :
      ∀ᶠ n : ℕ in Filter.atTop,
        0 ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n ∧
          TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ 1 :=
    OppositeProjectionEdgeProbBounds
  have hprob_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ prob n := by
    filter_upwards [hp_bounds] with n hp
    dsimp [prob]
    apply Finset.sum_nonneg
    intro G _
    split_ifs
    · rfl
    · exact hGnp_nonneg (m n) (TwoBiteEdgeProbability (1 / 2 : ℝ) n) hp.1 hp.2 G
  have hlog_ge_one :
      ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have hn_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop (R := ℝ)
    exact (Real.tendsto_log_atTop.comp hn_atTop).eventually_ge_atTop (1 : ℝ)
  have hlarge :
      ∀ᶠ n : ℕ in Filter.atTop,
        100 / δ ≤
          TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ) := by
    have hA_pos : 0 < 100 / δ := by positivity
    have hdom := NaturalDegreeMassDominatesLogCube (100 / δ) hA_pos
    filter_upwards [hlog_ge_one, hdom] with n hlog hdom_n
    have hA_nonneg : 0 ≤ 100 / δ := by positivity
    have hlog_pow_ge_one : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
      nlinarith [hlog, sq_nonneg (Real.log (n : ℝ))]
    have hA_le : 100 / δ ≤ (100 / δ) * (Real.log (n : ℝ)) ^ 3 := by
      nlinarith
    calc
      100 / δ ≤ (100 / δ) * (Real.log (n : ℝ)) ^ 3 := hA_le
      _ ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n *
          (TwoBiteNaturalReducedVertexCount n : ℝ) := hdom_n
      _ = TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ) := by
          rw [hm n]
  have hupper : ∀ᶠ n : ℕ in Filter.atTop, prob n ≤ simple n := by
    filter_upwards [hp_bounds, hlarge] with n hp hlarge_n
    let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
    let t : ℝ := Real.log (1 + δ / 2)
    have hbridge := BernoulliMgfEnvelopeFiniteBridge (m n) p δ
      hδ_pos hδ_le_one hp.1 hp.2 (by simpa [p] using hlarge_n)
    have ht_nonneg : 0 ≤ t := by
      simpa [t] using hbridge.1.le
    have htarget_nonneg :
        0 ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ) :=
      mul_nonneg hp.1 (Nat.cast_nonneg _)
    have hmono :
        prob n ≤
          ∑ G : SimpleGraph (Fin (m n)),
            if ¬ ∀ v : Fin (m n),
                WithinRelativeError δ
                  (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ))
                  (GraphDegreeCount G v : ℝ)
            then GnpGraphWeight (TwoBiteEdgeProbability (1 / 2 : ℝ) n) G else 0 := by
      dsimp [prob]
      apply Finset.sum_le_sum
      intro G _
      by_cases hbadε :
          ¬ ∀ v : Fin (m n),
              WithinRelativeError ε
                (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ))
                (GraphDegreeCount G v : ℝ)
      · rw [if_pos hbadε]
        have hbadδ :
            ¬ ∀ v : Fin (m n),
                WithinRelativeError δ
                  (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ))
                  (GraphDegreeCount G v : ℝ) := by
          intro hgoodδ
          apply hbadε
          intro v
          have hv := hgoodδ v
          unfold WithinRelativeError at hv ⊢
          have hscale :
              δ * (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ)) ≤
                ε * (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ)) :=
            mul_le_mul_of_nonneg_right hδ_le_ε htarget_nonneg
          exact le_trans hv hscale
        rw [if_pos hbadδ]
      · rw [if_neg hbadε]
        split_ifs
        · rfl
        · exact hGnp_nonneg (m n) (TwoBiteEdgeProbability (1 / 2 : ℝ) n) hp.1 hp.2 G
    have hall := GnpAllVerticesDegreeFailureUnionBound (m n) p δ t hp.1 hp.2 ht_nonneg
    have henv := BernoulliMgfTailEnvelope (m n) p δ t hp.1 hp.2
    have hchain :
        (∑ G : SimpleGraph (Fin (m n)),
            if ¬ ∀ v : Fin (m n),
                WithinRelativeError δ
                  (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ))
                  (GraphDegreeCount G v : ℝ)
            then GnpGraphWeight (TwoBiteEdgeProbability (1 / 2 : ℝ) n) G else 0) ≤
          simple n := by
      calc
        (∑ G : SimpleGraph (Fin (m n)),
            if ¬ ∀ v : Fin (m n),
                WithinRelativeError δ
                  (TwoBiteEdgeProbability (1 / 2 : ℝ) n * (m n : ℝ))
                  (GraphDegreeCount G v : ℝ)
            then GnpGraphWeight (TwoBiteEdgeProbability (1 / 2 : ℝ) n) G else 0)
            ≤ (m n : ℝ) *
              (Real.exp (-(t * ((1 + δ) * p * (m n : ℝ)))) *
                  (1 - p + p * Real.exp t) ^ (m n - 1) +
                Real.exp (t * ((1 - δ) * p * (m n : ℝ))) *
                  (1 - p + p * Real.exp (-t)) ^ (m n - 1)) := by
              simpa [p] using hall
        _ ≤ (m n : ℝ) *
              (Real.exp (-(t * ((1 + δ) * p * (m n : ℝ))) +
                  ((m n - 1 : ℕ) : ℝ) * (p * (Real.exp t - 1))) +
                Real.exp (t * ((1 - δ) * p * (m n : ℝ)) +
                  ((m n - 1 : ℕ) : ℝ) * (p * (Real.exp (-t) - 1)))) := by
              simpa using henv
        _ ≤ simple n := by
              simpa [simple, p, t, mul_assoc] using hbridge.2
    exact le_trans hmono hchain
  have hsimple_tendsto : Filter.Tendsto simple Filter.atTop (nhds (0 : ℝ)) := by
    have hnat := NaturalDegreeExponentialEnvelopeNegligible δ hδ_pos
    apply Filter.Tendsto.congr' _ hnat
    filter_upwards with n
    simp [simple, hm n]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsimple_tendsto hprob_nonneg hupper
