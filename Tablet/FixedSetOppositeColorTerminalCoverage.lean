import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteLargeClass
import Tablet.TwoBiteMediumClass
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteTerminalCoordinateUniverse
import Tablet.TwoBiteX

-- [TABLET NODE: FixedSetOppositeColorTerminalCoverage]

theorem FixedSetOppositeColorTerminalCoverage :
    ∀ {n m : ℕ} {p ε : ℝ}
      (I : Finset (Fin n))
      (recorded terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (ω ωFirst : TwoBiteSample n m p),
      (∀ x : Fin n, ω.2.2 x = ωFirst.2.2 x) →
      (∀ e,
        e ∈ recorded →
          (TwoBiteEdgeCoordinateValue ω e ↔
            TwoBiteEdgeCoordinateValue ωFirst e)) →
      (∀ e,
        e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔ e ∈ recorded) →
      (∀ e,
        e ∈ TwoBitePreTerminalRecordedPairs ωFirst ε I ↔ e ∈ recorded) →
      (∀ e,
        e ∈ terminal ↔
          e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded) →
        (((∀ e,
            e ∈ terminal →
              match e with
              | Sum.inl _ => True
              | Sum.inr _ =>
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue ωFirst e)) →
            ∀ b : Fin m,
              TwoBiteX ω I (Sum.inr b) =
                  TwoBiteX ωFirst I (Sum.inr b) ∧
                (TwoBiteLargeClass ω ε I (Sum.inr b) ↔
                  TwoBiteLargeClass ωFirst ε I (Sum.inr b)) ∧
                (TwoBiteMediumClass ω ε I (Sum.inr b) ↔
                  TwoBiteMediumClass ωFirst ε I (Sum.inr b)) ∧
                (TwoBiteSmallClass ω ε I (Sum.inr b) ↔
                  TwoBiteSmallClass ωFirst ε I (Sum.inr b)) ∧
                (∀ q : Fin m × Fin m,
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ω I (Sum.inr b)).image
                        (TwoBiteRedProjection ω)) ↔
                    q ∈
                      TwoBiteBasePairs
                        ((TwoBiteX ωFirst I (Sum.inr b)).image
                          (TwoBiteRedProjection ωFirst)))) ∧
          ((∀ e,
            e ∈ terminal →
              match e with
              | Sum.inl _ =>
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue ωFirst e)
              | Sum.inr _ => True) →
            ∀ r : Fin m,
              TwoBiteX ω I (Sum.inl r) =
                  TwoBiteX ωFirst I (Sum.inl r) ∧
                (TwoBiteLargeClass ω ε I (Sum.inl r) ↔
                  TwoBiteLargeClass ωFirst ε I (Sum.inl r)) ∧
                (TwoBiteMediumClass ω ε I (Sum.inl r) ↔
                  TwoBiteMediumClass ωFirst ε I (Sum.inl r)) ∧
                (TwoBiteSmallClass ω ε I (Sum.inl r) ↔
                  TwoBiteSmallClass ωFirst ε I (Sum.inl r)) ∧
                (∀ q : Fin m × Fin m,
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ω I (Sum.inl r)).image
                        (TwoBiteBlueProjection ω)) ↔
                    q ∈
                      TwoBiteBasePairs
                        ((TwoBiteX ωFirst I (Sum.inl r)).image
                          (TwoBiteBlueProjection ωFirst))))) := by
-- BODY
  classical
  intro n m p ε I recorded terminal ω ωFirst hEmb hRecorded _hPreω
    _hPreFirst hTerminal
  constructor
  · intro hBlueTerminal b
    have hBlueEdge :
        ∀ b y : Fin m,
          (TwoBiteBlueGraph ω).Adj b y ↔
            (TwoBiteBlueGraph ωFirst).Adj b y := by
      intro b y
      rcases lt_trichotomy b.val y.val with hlt | heq | hgt
      · let e : Sum (Fin m × Fin m) (Fin m × Fin m) := Sum.inr (b, y)
        have hUniverse : e ∈ TwoBiteTerminalCoordinateUniverse m := by
          simp [TwoBiteTerminalCoordinateUniverse, e]
          exact hlt
        by_cases hrec : e ∈ recorded
        · simpa [TwoBiteEdgeCoordinateValue, e] using hRecorded e hrec
        · have hterm : e ∈ terminal := (hTerminal e).2 ⟨hUniverse, hrec⟩
          simpa [TwoBiteEdgeCoordinateValue, e] using hBlueTerminal e hterm
      · have hby : b = y := Fin.ext heq
        subst y
        constructor <;> intro h
        · exact (SimpleGraph.irrefl (TwoBiteBlueGraph ω) h).elim
        · exact (SimpleGraph.irrefl (TwoBiteBlueGraph ωFirst) h).elim
      · let e : Sum (Fin m × Fin m) (Fin m × Fin m) := Sum.inr (y, b)
        have hUniverse : e ∈ TwoBiteTerminalCoordinateUniverse m := by
          simp [TwoBiteTerminalCoordinateUniverse, e]
          exact hgt
        have hiff :
            (TwoBiteBlueGraph ω).Adj y b ↔
              (TwoBiteBlueGraph ωFirst).Adj y b := by
          by_cases hrec : e ∈ recorded
          · simpa [TwoBiteEdgeCoordinateValue, e] using hRecorded e hrec
          · have hterm : e ∈ terminal := (hTerminal e).2 ⟨hUniverse, hrec⟩
            simpa [TwoBiteEdgeCoordinateValue, e] using hBlueTerminal e hterm
        constructor
        · intro h
          exact
            (SimpleGraph.adj_comm (TwoBiteBlueGraph ωFirst) b y).2
              (hiff.1 ((SimpleGraph.adj_comm (TwoBiteBlueGraph ω) b y).1 h))
        · intro h
          exact
            (SimpleGraph.adj_comm (TwoBiteBlueGraph ω) b y).2
              (hiff.2
                ((SimpleGraph.adj_comm (TwoBiteBlueGraph ωFirst) b y).1 h))
    have hX :
        TwoBiteX ω I (Sum.inr b) =
          TwoBiteX ωFirst I (Sum.inr b) := by
      ext v
      simp [TwoBiteX, TwoBiteLiftedNeighborhood, TwoBiteBlueProjection,
        TwoBiteEmbedding, hEmb v, hBlueEdge]
    have hImage :
        (TwoBiteX ω I (Sum.inr b)).image (TwoBiteRedProjection ω) =
          (TwoBiteX ωFirst I (Sum.inr b)).image
            (TwoBiteRedProjection ωFirst) := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨v, hv, hvproj⟩
        exact
          Finset.mem_image.mpr
            ⟨v, by simpa [hX] using hv,
              by
                simpa [TwoBiteRedProjection, TwoBiteEmbedding, ← hEmb v]
                  using hvproj⟩
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨v, hv, hvproj⟩
        exact
          Finset.mem_image.mpr
            ⟨v, by simpa [hX] using hv,
              by
                simpa [TwoBiteRedProjection, TwoBiteEmbedding, hEmb v]
                  using hvproj⟩
    refine ⟨hX, ?_, ?_, ?_, ?_⟩
    · simp [TwoBiteLargeClass, hX]
    · simp [TwoBiteMediumClass, hX]
    · simp [TwoBiteSmallClass, hX]
    · intro q
      simp [hImage]
  · intro hRedTerminal r
    have hRedEdge :
        ∀ r y : Fin m,
          (TwoBiteRedGraph ω).Adj r y ↔
            (TwoBiteRedGraph ωFirst).Adj r y := by
      intro r y
      rcases lt_trichotomy r.val y.val with hlt | heq | hgt
      · let e : Sum (Fin m × Fin m) (Fin m × Fin m) := Sum.inl (r, y)
        have hUniverse : e ∈ TwoBiteTerminalCoordinateUniverse m := by
          simp [TwoBiteTerminalCoordinateUniverse, e]
          exact hlt
        by_cases hrec : e ∈ recorded
        · simpa [TwoBiteEdgeCoordinateValue, e] using hRecorded e hrec
        · have hterm : e ∈ terminal := (hTerminal e).2 ⟨hUniverse, hrec⟩
          simpa [TwoBiteEdgeCoordinateValue, e] using hRedTerminal e hterm
      · have hry : r = y := Fin.ext heq
        subst y
        constructor <;> intro h
        · exact (SimpleGraph.irrefl (TwoBiteRedGraph ω) h).elim
        · exact (SimpleGraph.irrefl (TwoBiteRedGraph ωFirst) h).elim
      · let e : Sum (Fin m × Fin m) (Fin m × Fin m) := Sum.inl (y, r)
        have hUniverse : e ∈ TwoBiteTerminalCoordinateUniverse m := by
          simp [TwoBiteTerminalCoordinateUniverse, e]
          exact hgt
        have hiff :
            (TwoBiteRedGraph ω).Adj y r ↔
              (TwoBiteRedGraph ωFirst).Adj y r := by
          by_cases hrec : e ∈ recorded
          · simpa [TwoBiteEdgeCoordinateValue, e] using hRecorded e hrec
          · have hterm : e ∈ terminal := (hTerminal e).2 ⟨hUniverse, hrec⟩
            simpa [TwoBiteEdgeCoordinateValue, e] using hRedTerminal e hterm
        constructor
        · intro h
          exact
            (SimpleGraph.adj_comm (TwoBiteRedGraph ωFirst) r y).2
              (hiff.1 ((SimpleGraph.adj_comm (TwoBiteRedGraph ω) r y).1 h))
        · intro h
          exact
            (SimpleGraph.adj_comm (TwoBiteRedGraph ω) r y).2
              (hiff.2
                ((SimpleGraph.adj_comm (TwoBiteRedGraph ωFirst) r y).1 h))
    have hX :
        TwoBiteX ω I (Sum.inl r) =
          TwoBiteX ωFirst I (Sum.inl r) := by
      ext v
      simp [TwoBiteX, TwoBiteLiftedNeighborhood, TwoBiteRedProjection,
        TwoBiteEmbedding, hEmb v, hRedEdge]
    have hImage :
        (TwoBiteX ω I (Sum.inl r)).image (TwoBiteBlueProjection ω) =
          (TwoBiteX ωFirst I (Sum.inl r)).image
            (TwoBiteBlueProjection ωFirst) := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨v, hv, hvproj⟩
        exact
          Finset.mem_image.mpr
            ⟨v, by simpa [hX] using hv,
              by
                simpa [TwoBiteBlueProjection, TwoBiteEmbedding, ← hEmb v]
                  using hvproj⟩
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨v, hv, hvproj⟩
        exact
          Finset.mem_image.mpr
            ⟨v, by simpa [hX] using hv,
              by
                simpa [TwoBiteBlueProjection, TwoBiteEmbedding, hEmb v]
                  using hvproj⟩
    refine ⟨hX, ?_, ?_, ?_, ?_⟩
    · simp [TwoBiteLargeClass, hX]
    · simp [TwoBiteMediumClass, hX]
    · simp [TwoBiteSmallClass, hX]
    · intro q
      simp [hImage]
