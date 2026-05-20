import Mathlib.Tactic
import Tablet.FiberAndDegreeEvent
import Tablet.ParameterHierarchyT4ChooseExpBound
import Tablet.TwoBiteMediumClosedPairsEvent
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

open scoped BigOperators

-- [TABLET NODE: MediumClosedPairsDeterministicWitnessCandidatePackage]

theorem MediumClosedPairsDeterministicWitnessCandidatePackage
    {n m k S : ℕ} {p ε ε1 ε2 countExp : ℝ}
    (hWitness :
      ∀ ω : TwoBiteSample n m p,
        (¬ TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω ∧
          FiberAndDegreeEvent ω ε2) →
        ∃ I : Finset (Fin n),
          I.card = k ∧
          ¬ ClosedPairsBound
            ((TwoBiteClosedPairsInClass ω I
              (TwoBiteMediumClass ω ε I)).card : ℝ)
            ε1 (k : ℝ) ∧
          ∃ B : Finset (TwoBiteBaseVertex m),
            let A0 := (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε)
            B.Nonempty ∧
            (∀ x ∈ B, TwoBiteMediumClass ω ε I x) ∧
            A0 < (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ)) ∧
            (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ))
              ≤ A0 + TwoBiteLargeCutoff ε n ∧
            (B.card : ℝ) * TwoBiteSmallCutoff ε n
              ≤ A0 + TwoBiteLargeCutoff ε n ∧
            (let redCenters : Finset (Fin m) :=
                Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ B)
             let blueCenters : Finset (Fin m) :=
                Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ B)
             let redProjection : Finset (Fin m) := I.image (TwoBiteRedProjection ω)
             let blueProjection : Finset (Fin m) := I.image (TwoBiteBlueProjection ω)
             let normalize : Fin m × Fin m → Fin m × Fin m :=
                fun e => if e.1.val < e.2.val then e else (e.2, e.1)
             let redOrdered : Finset (Fin m × Fin m) :=
                @Finset.filter (Fin m × Fin m)
                  (fun e => (TwoBiteRedGraph ω).Adj e.1 e.2)
                  (Classical.decPred _)
                  (redCenters.product redProjection)
             let blueOrdered : Finset (Fin m × Fin m) :=
                @Finset.filter (Fin m × Fin m)
                  (fun e => (TwoBiteBlueGraph ω).Adj e.1 e.2)
                  (Classical.decPred _)
                  (blueCenters.product blueProjection)
             let redEdges : Finset (Fin m × Fin m) := redOrdered.image normalize
             let blueEdges : Finset (Fin m × Fin m) := blueOrdered.image normalize
             A0 / (6 * (Real.log (n : ℝ)) ^ 2) <
              ((redEdges.card + blueEdges.card : ℕ) : ℝ)))
    (hSsize :
      ∀ B : Finset (TwoBiteBaseVertex m),
        B.Nonempty →
        (B.card : ℝ) * TwoBiteSmallCutoff ε n
          ≤ (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
              TwoBiteLargeCutoff ε n →
        B.card ≤ S)
    (hn_pos : 0 < (n : ℝ))
    (hbase_card :
      (Fintype.card (TwoBiteBaseVertex m) : ℝ) ≤ (n : ℝ) ^ 2)
    (hcountExp :
      (k : ℝ) * Real.log (n : ℝ) +
          2 * (S : ℝ) * Real.log (n : ℝ) ≤ countExp) :
    ∃ Candidate :
      ({I : Finset (Fin n) // I.card = k} ×
          (Fin S → TwoBiteBaseVertex m)) →
        TwoBiteSample n m p → Prop,
      (∀ ω : TwoBiteSample n m p,
        (¬ TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω ∧
          FiberAndDegreeEvent ω ε2) →
          ∃ i : {I : Finset (Fin n) // I.card = k} ×
              (Fin S → TwoBiteBaseVertex m),
            Candidate i ω) ∧
      (Fintype.card
          ({I : Finset (Fin n) // I.card = k} ×
            (Fin S → TwoBiteBaseVertex m)) : ℝ)
        ≤ Real.exp countExp := by
-- BODY
  classical
  let Index :=
    {I : Finset (Fin n) // I.card = k} ×
      (Fin S → TwoBiteBaseVertex m)
  let Candidate : Index → TwoBiteSample n m p → Prop :=
    fun i ω =>
      let I : Finset (Fin n) := i.1.1
      let coverB : Finset (TwoBiteBaseVertex m) := Finset.univ.image i.2
      ¬ ClosedPairsBound
          ((TwoBiteClosedPairsInClass ω I
            (TwoBiteMediumClass ω ε I)).card : ℝ)
          ε1 (k : ℝ) ∧
        ∃ B : Finset (TwoBiteBaseVertex m),
          let A0 := (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε)
          B.Nonempty ∧
          B.card ≤ S ∧
          B ⊆ coverB ∧
          (∀ x ∈ B, TwoBiteMediumClass ω ε I x) ∧
          A0 < (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ)) ∧
          (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ))
            ≤ A0 + TwoBiteLargeCutoff ε n ∧
          (B.card : ℝ) * TwoBiteSmallCutoff ε n
            ≤ A0 + TwoBiteLargeCutoff ε n ∧
          (let redCenters : Finset (Fin m) :=
              Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ B)
           let blueCenters : Finset (Fin m) :=
              Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ B)
           let redProjection : Finset (Fin m) := I.image (TwoBiteRedProjection ω)
           let blueProjection : Finset (Fin m) := I.image (TwoBiteBlueProjection ω)
           let normalize : Fin m × Fin m → Fin m × Fin m :=
              fun e => if e.1.val < e.2.val then e else (e.2, e.1)
           let redOrdered : Finset (Fin m × Fin m) :=
              @Finset.filter (Fin m × Fin m)
                (fun e => (TwoBiteRedGraph ω).Adj e.1 e.2)
                (Classical.decPred _)
                (redCenters.product redProjection)
           let blueOrdered : Finset (Fin m × Fin m) :=
              @Finset.filter (Fin m × Fin m)
                (fun e => (TwoBiteBlueGraph ω).Adj e.1 e.2)
                (Classical.decPred _)
                (blueCenters.product blueProjection)
           let redEdges : Finset (Fin m × Fin m) := redOrdered.image normalize
           let blueEdges : Finset (Fin m × Fin m) := blueOrdered.image normalize
           A0 / (6 * (Real.log (n : ℝ)) ^ 2) <
            ((redEdges.card + blueEdges.card : ℕ) : ℝ))
  have hcover_fun :
      ∀ B : Finset (TwoBiteBaseVertex m),
        B.Nonempty → B.card ≤ S →
          ∃ f : Fin S → TwoBiteBaseVertex m, B ⊆ Finset.univ.image f := by
    intro B hBne hBcard
    obtain ⟨b0, _hb0⟩ := hBne
    have hcard_sub :
        Fintype.card {x // x ∈ B} ≤ Fintype.card (Fin S) := by
      simpa [Fintype.card_coe, Fintype.card_fin] using hBcard
    obtain ⟨e : {x // x ∈ B} ↪ Fin S⟩ :=
      Function.Embedding.nonempty_of_card_le hcard_sub
    let f : Fin S → TwoBiteBaseVertex m :=
      fun j =>
        if h : ∃ x : {x // x ∈ B}, e x = j then
          (Classical.choose h).1
        else
          b0
    refine ⟨f, ?_⟩
    intro x hx
    refine Finset.mem_image.mpr ?_
    refine ⟨e ⟨x, hx⟩, Finset.mem_univ _, ?_⟩
    dsimp [f]
    let hw : ∃ y : {x // x ∈ B}, e y = e ⟨x, hx⟩ := ⟨⟨x, hx⟩, rfl⟩
    simp only [dif_pos hw]
    have hchoose : e (Classical.choose hw) = e ⟨x, hx⟩ :=
      Classical.choose_spec hw
    exact congrArg Subtype.val (e.injective hchoose)
  refine ⟨Candidate, ?_, ?_⟩
  · intro ω hbad
    have hwitness := hWitness ω hbad
    rcases hwitness with ⟨I, hIcard, hIbad, B, hB⟩
    dsimp only at hB
    rcases hB with
      ⟨hBne, hBmedium, hsum_gt, hsum_le, hBsmall, hcoord⟩
    have hBcard : B.card ≤ S := hSsize B hBne hBsmall
    obtain ⟨f, hBsubset⟩ := hcover_fun B hBne hBcard
    refine ⟨(⟨I, hIcard⟩, f), ?_⟩
    dsimp [Candidate]
    refine ⟨hIbad, B, ?_⟩
    dsimp
    exact ⟨hBne, hBcard, hBsubset, hBmedium, hsum_gt, hsum_le,
      hBsmall, hcoord⟩
  · have hchoose :
        (Fintype.card {I : Finset (Fin n) // I.card = k} : ℝ) ≤
          Real.exp ((k : ℝ) * Real.log (n : ℝ)) := by
      have hcardI :
          Fintype.card {I : Finset (Fin n) // I.card = k} = Nat.choose n k := by
        rw [Fintype.card_of_subtype
          (Finset.powersetCard k (Finset.univ : Finset (Fin n)))]
        · simp [Finset.card_powersetCard]
        · intro I
          simp [Finset.mem_powersetCard]
      rw [hcardI]
      exact ParameterHierarchyT4ChooseExpBound n k hn_pos
    have hbase_nonneg :
        0 ≤ (Fintype.card (TwoBiteBaseVertex m) : ℝ) := by
      positivity
    have hfun_card :
        (Fintype.card (Fin S → TwoBiteBaseVertex m) : ℝ) ≤
          Real.exp (2 * (S : ℝ) * Real.log (n : ℝ)) := by
      have hpow :
          (Fintype.card (Fin S → TwoBiteBaseVertex m) : ℝ) =
            (Fintype.card (TwoBiteBaseVertex m) : ℝ) ^ S := by
        simp
      rw [hpow]
      calc
        (Fintype.card (TwoBiteBaseVertex m) : ℝ) ^ S
            ≤ ((n : ℝ) ^ 2) ^ S := by
              exact pow_le_pow_left₀ hbase_nonneg hbase_card S
        _ = (n : ℝ) ^ (2 * S) := by
              rw [← pow_mul]
        _ = (n : ℝ) ^ ((2 * S : ℕ) : ℝ) := by
              rw [Real.rpow_natCast]
        _ = Real.exp (((2 * S : ℕ) : ℝ) * Real.log (n : ℝ)) := by
              rw [Real.rpow_def_of_pos hn_pos]
              ring_nf
        _ = Real.exp (2 * (S : ℝ) * Real.log (n : ℝ)) := by
              congr 1
              norm_num
    have hprod :
        (Fintype.card
            ({I : Finset (Fin n) // I.card = k} ×
              (Fin S → TwoBiteBaseVertex m)) : ℝ) ≤
          Real.exp ((k : ℝ) * Real.log (n : ℝ)) *
            Real.exp (2 * (S : ℝ) * Real.log (n : ℝ)) := by
      rw [Fintype.card_prod]
      rw [Nat.cast_mul]
      exact mul_le_mul hchoose hfun_card (Nat.cast_nonneg _)
        (le_of_lt (Real.exp_pos _))
    calc
      (Fintype.card
          ({I : Finset (Fin n) // I.card = k} ×
            (Fin S → TwoBiteBaseVertex m)) : ℝ)
          ≤ Real.exp ((k : ℝ) * Real.log (n : ℝ)) *
            Real.exp (2 * (S : ℝ) * Real.log (n : ℝ)) := hprod
      _ = Real.exp
            ((k : ℝ) * Real.log (n : ℝ) +
              2 * (S : ℝ) * Real.log (n : ℝ)) := by
            rw [← Real.exp_add]
      _ ≤ Real.exp countExp := Real.exp_le_exp.mpr hcountExp
