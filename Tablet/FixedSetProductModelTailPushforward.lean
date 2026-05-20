import Tablet.FixedSetProductModelMassFn
import Tablet.FixedSetProductModelMass
import Tablet.FixedSetProductModelVar
import Tablet.FixedSetFakeGraph
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.GnpGraphWeight
import Tablet.UniformInjectionWeight
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteFinalPairs
import Tablet.TwoBiteX
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.FixedSetProductModelTailPushforwardGraphFiberSum
import Tablet.FixedSetProductModelTailPushforwardProductFiberSum
import Tablet.FixedSetProductModelTailPushforwardAgreement

-- [TABLET NODE: FixedSetProductModelTailPushforward]

open scoped Classical BigOperators

theorem FixedSetProductModelTailPushforward {n : ℕ} (I : Finset (Fin n)) (ε : ℝ)
    {m_sub : ℕ} (p_sub : ℝ) (hp0 : 0 ≤ p_sub) (hp1 : p_sub ≤ 1)
    (π : Fin n ↪ (Fin m_sub × Fin m_sub))
    (H : ℝ → Prop) :
    let r_prod := 2 * m_sub
    let P_R := I.image (fun u => (π u).1)
    let P_B := I.image (fun u => (π u).2)
    let q := FixedSetProductModelMassFn p_sub P_R P_B
    let Z_prod := FixedSetProductModelVar I ε p_sub π
    let Z_I : TwoBiteSample n m_sub p_sub → ℝ := fun ω => by
      classical
      exact
        let P_R := I.image (TwoBiteRedProjection ω)
        let P_B := I.image (TwoBiteBlueProjection ω)
        let P_I := (P_R.image Sum.inl) ∪ (P_B.image Sum.inr)
        let S_I_ext := (Finset.univ.filter (TwoBiteSmallClass ω ε I)) \ P_I
        let ext_pairs := S_I_ext.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))
        let Z_pairs := ext_pairs.filter (fun e =>
          TwoBiteRedProjection ω e.1 ≠ TwoBiteRedProjection ω e.2 ∧
          TwoBiteBlueProjection ω e.1 ≠ TwoBiteBlueProjection ω e.2)
        (Z_pairs.card : ℝ)
    TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π ∧ H (Z_I ω))
    = TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) *
      (Finset.univ.filter (fun v => H (Z_prod v))).sum (fun v => Finset.univ.prod (fun i => q (v i))) := by
-- BODY
  intros r_prod P_R P_B q Z_prod Z_I
  let D_ω : TwoBiteSample n m_sub p_sub → ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) := fun ω =>
    (fun x => if x ∈ P_R then ∅ else P_R.filter (fun r => ω.1.Adj x r),
     fun y => if y ∈ P_B then ∅ else P_B.filter (fun b => ω.2.1.Adj y b))
  let D_v : (Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub)) → ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) := fun v =>
    (fun x => if x ∈ P_R then ∅ else (v ⟨x.val, by omega⟩).1,
     fun y => if y ∈ P_B then ∅ else (v ⟨y.val + m_sub, by omega⟩).2)
  let H_D : ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) → Prop :=
    fun D => ∃ v, D_v v = D ∧ H (Z_prod v)
  have h_equiv := FixedSetProductModelTailPushforwardAgreement I ε p_sub π H
  have h_graph := FixedSetProductModelTailPushforwardGraphFiberSum I p_sub hp0 hp1 π H_D
  have h_left : TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π ∧ H (Z_I ω))
              = TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π ∧ H_D (D_ω ω)) := by
    apply congrArg
    funext ω
    have h_imp : TwoBiteEmbedding ω = π → (H (Z_I ω) ↔ H_D (D_ω ω)) := h_equiv.1 ω
    by_cases h : TwoBiteEmbedding ω = π
    · rw [h_imp h]
    · simp [h]
  have h_right : (Finset.univ.filter (fun v => H (Z_prod v))).sum (fun v => Finset.univ.prod (fun i => q (v i)))
               = (Finset.univ.filter (fun v => H_D (D_v v))).sum (fun v => Finset.univ.prod (fun i => q (v i))) := by
    rw [h_equiv.2]
  have step1 := h_left.trans h_graph
  have step2 := FixedSetProductModelTailPushforwardProductFiberSum I p_sub hp0 hp1 π H_D
  let valid_D (D : ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub)))) : Prop :=
    (∀ x ∈ P_R, D.1 x = ∅) ∧ (∀ x ∉ P_R, D.1 x ⊆ P_R) ∧
    (∀ y ∈ P_B, D.2 y = ∅) ∧ (∀ y ∉ P_B, D.2 y ⊆ P_B)
  let ν_D (D : ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub)))) : ℝ :=
    (∏ x ∈ Finset.univ \ P_R, p_sub ^ (D.1 x).card * (1 - p_sub) ^ (P_R.card - (D.1 x).card)) *
    (∏ y ∈ Finset.univ \ P_B, p_sub ^ (D.2 y).card * (1 - p_sub) ^ (P_B.card - (D.2 y).card))
  dsimp only [valid_D, ν_D, D_v, D_ω, q, P_R, P_B] at step1 step2 h_right ⊢
  rw [step1]
  rw [← step2]
  congr 1
  convert h_right.symm
