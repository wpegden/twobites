import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Twobites

open SimpleGraph

theorem SimpleGraph.indepNum_lt_of_indepSetFree
    {α : Type*} {G : SimpleGraph α} {k : ℕ}
    (hfree : G.IndepSetFree k) :
    G.indepNum < k := by
  classical
  by_contra hge
  rcases G.exists_isNIndepSet_indepNum with ⟨s, hs⟩
  rcases Finset.exists_subset_card_eq (show k ≤ s.card by simpa [hs.card_eq] using hge) with
    ⟨t, hts, htcard⟩
  apply hfree t
  refine ⟨?_, htcard⟩
  intro a ha b hb hab
  exact hs.isIndepSet (hts ha) (hts hb) hab

end Twobites
