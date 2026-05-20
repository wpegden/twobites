import Tablet.Preamble
import Tablet.TwoBiteSample
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteFinalPairs
import Tablet.TwoBiteX
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection
import Tablet.FixedSetFakeGraph

-- [TABLET NODE: FixedSetProductModelVar]

open scoped Classical

noncomputable def FixedSetProductModelVar {n : ℕ} (I : Finset (Fin n)) (ε : ℝ)
    {m_sub : ℕ} (p_sub : ℝ) (π : Fin n ↪ (Fin m_sub × Fin m_sub))
    (v : Fin (2 * m_sub) → Finset (Fin m_sub) × Finset (Fin m_sub)) : ℝ :=
-- BODY
  let ω : TwoBiteSample n m_sub p_sub :=
    (FixedSetFakeGraph (I.image (fun u => (π u).1)) (fun i => (v ⟨i.val, by omega⟩).1),
     FixedSetFakeGraph (I.image (fun u => (π u).2)) (fun i => (v ⟨i.val + m_sub, by omega⟩).2),
     π)
  let P_R := I.image (TwoBiteRedProjection ω)
  let P_B := I.image (TwoBiteBlueProjection ω)
  let P_I := (P_R.image Sum.inl) ∪ (P_B.image Sum.inr)
  let S_I_ext := (Finset.univ.filter (TwoBiteSmallClass ω ε I)) \ P_I
  let ext_pairs := S_I_ext.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))
  let Z_pairs := ext_pairs.filter (fun e =>
    TwoBiteRedProjection ω e.1 ≠ TwoBiteRedProjection ω e.2 ∧
    TwoBiteBlueProjection ω e.1 ≠ TwoBiteBlueProjection ω e.2)
  (Z_pairs.card : ℝ)
