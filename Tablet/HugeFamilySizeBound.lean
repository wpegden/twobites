import Tablet.FiberAndDegreeEvent
import Tablet.HugeFamilyEventualNumerics
import Tablet.HugeFamilyFiniteOverlapCounting
import Tablet.HugeFamilyPairwiseOverlapBound
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteX

-- [TABLET NODE: HugeFamilySizeBound]

theorem HugeFamilySizeBound : by
  classical
  exact
    ∀ {n m k : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (ε ε1 ε2 : ℝ) {n0 : ℕ},
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      I.card = k →
      FiberAndDegreeEvent ω ε2 →
        let huge : TwoBiteBaseVertex m → Prop :=
          fun x => TwoBiteHugeClass ω I x
        let H : Finset (TwoBiteBaseVertex m) :=
          (Finset.univ.filter huge)
        let t1 : ℝ := TwoBiteHugeCutoff n
        H.sum (fun x => ((TwoBiteX ω I x).card : ℝ)) ≤ 2 * (k : ℝ) ∧
          (H.card : ℝ) ≤ 2 * (k : ℝ) / t1 := by
-- BODY
  classical
  intro n m k p ω I ε ε1 ε2 n0 hcomparisons hn hk hI hfiber
  dsimp
  let huge : TwoBiteBaseVertex m → Prop :=
    fun x => TwoBiteHugeClass ω I x
  let H : Finset (TwoBiteBaseVertex m) :=
    (Finset.univ.filter huge)
  let t1 : ℝ := TwoBiteHugeCutoff n
  let C : ℝ := 100 * (Real.log (n : ℝ)) ^ 3
  have hnumerics :
      0 < t1 ∧ 0 ≤ C ∧
        RealChooseTwo (2 * (k : ℝ) / t1 + 1) * C ≤ (1 / 2 : ℝ) * (k : ℝ) := by
    simpa [t1, C] using
      HugeFamilyEventualNumerics (n := n) (k := k) (ε := ε) (ε1 := ε1)
        (ε2 := ε2) (n0 := n0) hcomparisons hn hk
  have hsubset :
      ∀ x, x ∈ H → TwoBiteX ω I x ⊆ I := by
    intro x _hx v hv
    exact (Finset.mem_filter.mp (by simpa [TwoBiteX] using hv)).1
  have hclass_bounds :
      ∀ x, x ∈ H →
        t1 < ((TwoBiteX ω I x).card : ℝ) ∧
          ((TwoBiteX ω I x).card : ℝ) ≤ (k : ℝ) := by
    intro x hx
    have hxHuge : TwoBiteHugeClass ω I x := by
      simpa [H, huge] using hx
    exact ⟨by simpa [t1] using hxHuge.1,
      by
        calc
          ((TwoBiteX ω I x).card : ℝ) ≤ (I.card : ℝ) := hxHuge.2
          _ = (k : ℝ) := by exact_mod_cast hI⟩
  have hoverlap :
      ∀ x, x ∈ H → ∀ y, y ∈ H → x ≠ y →
        (((TwoBiteX ω I x ∩ TwoBiteX ω I y).card : ℝ) ≤ C) := by
    intro x _hx y _hy hxy
    simpa [C] using HugeFamilyPairwiseOverlapBound ω I ε2 hfiber hxy
  simpa [H, t1] using
    HugeFamilyFiniteOverlapCounting H I (fun x => TwoBiteX ω I x) k t1 C hI
      hsubset hclass_bounds hoverlap hnumerics.1 hnumerics.2.1 hnumerics.2.2
