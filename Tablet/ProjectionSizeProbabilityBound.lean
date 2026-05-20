import Tablet.ProjectionOpenPairFunction
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEventProbabilityInjectionOnly
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.GnpGraphWeight
import Tablet.UniformInjectionWeight
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.NaturalParameterApproximation
import Tablet.InjectionOnlyEventProbabilityBound
import Tablet.ProjectionSizeAnalyticParameterBounds
import Tablet.ProjectionSizeAnalyticBinomialBound

-- [TABLET NODE: ProjectionSizeProbabilityBound]

theorem ProjectionSizeProbabilityBound :
    ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ n0 : ℕ, ∀ {n m k ℓR ℓB : ℕ} {p : ℝ}
        (I : Finset (Fin n)),
        n0 ≤ n →
        m = TwoBiteNaturalReducedVertexCount n →
        I.card = k →
        k = TwoBiteNaturalIndependenceScale (1 + ε) n →
        ℓR * ℓB ≥ k →
        let xR : ℝ := (ℓR : ℝ) / (k : ℝ)
        let xB : ℝ := (ℓB : ℝ) / (k : ℝ)
        TwoBiteEventProbability n m p
            (fun ω => TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I)
          ≤
          Real.exp
            ((δ - (2 - xR - xB) / 2) * (k : ℝ) *
              Real.log (n : ℝ)) := by
-- BODY
  intro δ ε hδ hε
  rcases ProjectionSizeAnalyticBinomialBound δ ε hδ hε with ⟨n0_bin, hn0_bin⟩
  let n0 := max n0_bin 1
  use n0
  intro n m k ℓR ℓB p I hn hm hI hk hℓ
  let xR : ℝ := (ℓR : ℝ) / (k : ℝ)
  let xB : ℝ := (ℓB : ℝ) / (k : ℝ)
  
  have hn_bin : n0_bin ≤ n := le_trans (le_max_left n0_bin 1) hn
  have hn_pos : 1 ≤ (n : ℝ) := by
    have h1 : 1 ≤ n := le_trans (le_max_right n0_bin 1) hn
    exact Nat.one_le_cast.mpr h1
  
  by_cases hs : ((2 : ℝ) - xR - xB) * (k : ℝ) ≤ 2 * δ * (k : ℝ)
  · have h_exp_nonneg : 0 ≤ (δ - (2 - xR - xB) / 2) * (k : ℝ) * Real.log (n : ℝ) := by
      have h1 : ((2 : ℝ) - xR - xB) / 2 * (k : ℝ) ≤ δ * (k : ℝ) := by
        calc ((2 : ℝ) - xR - xB) / 2 * (k : ℝ) = ((2 : ℝ) - xR - xB) * (k : ℝ) / 2 := by ring
          _ ≤ 2 * δ * (k : ℝ) / 2 := by linarith [hs]
          _ = δ * (k : ℝ) := by ring
      have h2 : 0 ≤ (δ - (2 - xR - xB) / 2) * (k : ℝ) := by
        calc 0 ≤ δ * (k : ℝ) - ((2 : ℝ) - xR - xB) / 2 * (k : ℝ) := by linarith [h1]
          _ = (δ - (2 - xR - xB) / 2) * (k : ℝ) := by ring
      have h3 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_pos
      exact mul_nonneg h2 h3
    
    have h_prob_le_1 : TwoBiteEventProbability n m p (fun ω => TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I) ≤ 1 := by
      let event : (Fin n ↪ Fin m × Fin m) → Prop :=
        fun pi => I.card = k ∧ (I.image (fun i => (pi i).1)).card = ℓR ∧ (I.image (fun i => (pi i).2)).card = ℓB
      have h_eq : (fun ω : TwoBiteSample n m p => TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I) =
          (fun ω => event ω.2.2) := by
        ext ω
        dsimp [TwoBiteProjectionSizeEvent, event, TwoBiteRedProjection, TwoBiteBlueProjection, TwoBiteEmbedding]
        rfl
      rw [h_eq, TwoBiteEventProbabilityInjectionOnly event]
      unfold UniformInjectionWeight
      split_ifs with h
      · simp
      · have h_pos_inj : (0 : ℝ) < Fintype.card (Fin n ↪ Fin m × Fin m) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
        rw [← div_eq_mul_inv, div_le_iff₀ h_pos_inj, one_mul]
        exact Nat.cast_le.mpr (Finset.card_le_univ _)

    have h_one_le_exp : 1 ≤ Real.exp ((δ - (2 - xR - xB) / 2) * (k : ℝ) * Real.log (n : ℝ)) := by
      exact Real.one_le_exp h_exp_nonneg
    
    exact le_trans h_prob_le_1 h_one_le_exp

  · push Not at hs
    have h1 : TwoBiteEventProbability n m p (fun ω => TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I)
        ≤ (Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k : ℝ) / (Nat.choose (m * m) k : ℝ) :=
      InjectionOnlyEventProbabilityBound I hI
    have h2 : ((Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k : ℝ) / (Nat.choose (m * m) k : ℝ))
        ≤ Real.exp ((δ - (2 - xR - xB) / 2) * (k : ℝ) * Real.log (n : ℝ)) :=
      hn0_bin hn_bin hm hk hℓ hs
    exact le_trans h1 h2
