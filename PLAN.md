# Formalization Plan

## Main Results
- Scope: formalize only the paper's main-result material from Sections 2-4, together with the appendix inequalities actually used there. Do not formalize the hypergraph proof sketch in Section 5.
- Public theorem target 1: Theorem `main`, stated in an explicit finitary form instead of `o(1)` notation.
  Suggested Lean shape:
  ```lean
  theorem paper_main
      {ε : ℝ} (hε : 0 < ε) :
      ∃ n0 : ℕ, ∀ ⦃n : ℕ⦄, n ≥ n0 →
        ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
          (G.indepNum : ℝ) < (1 + ε) * Real.sqrt (n * Real.log n)
  ```
- Public theorem target 2: the Ramsey lower bound corresponding to Theorem `main2`.
  Because mathlib does not appear to provide Ramsey numbers directly, the clean implementation route is:
  1. first formalize a witness theorem of the form
     `∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.IndepSetFree k`,
  2. then package it into a local Ramsey-number definition or a local lower-bound corollary.
- The paper-check notes imply one necessary Lean-side cleanup: the proof should explicitly reduce to sufficiently small `ε`, since the paper's asymptotic inequalities use `ε << 1`.

## Imported Dependencies
- Graph theory from mathlib:
  - `Mathlib.Combinatorics.SimpleGraph.Basic`
  - `Mathlib.Combinatorics.SimpleGraph.Operations`
  - `Mathlib.Combinatorics.SimpleGraph.Clique`
  - `Mathlib.Combinatorics.SimpleGraph.Triangle.Basic`
- Useful graph notions already in mathlib:
  - `SimpleGraph.CliqueFree`
  - `SimpleGraph.IsIndepSet`
  - `SimpleGraph.IndepSetFree`
  - `SimpleGraph.indepNum`
  - neighborhood lemmas such as `isIndepSet_neighborSet_of_triangleFree`
- Finite combinatorics/cardinality:
  - `Mathlib.Data.Finset.Basic`
  - `Mathlib.Data.Finset.Powerset`
  - `Mathlib.Data.Nat.Choose.Bounds`
  - `Mathlib.Combinatorics.Enumerative.DoubleCounting`
- Probability infrastructure that looks directly relevant:
  - `Mathlib.Probability.ProbabilityMassFunction.Basic`
  - `Mathlib.Probability.ProbabilityMassFunction.Binomial`
  - `Mathlib.Probability.Distributions.Uniform`
  - `Mathlib.Probability.Independence.Basic`
  - `Mathlib.Probability.Moments.Basic`
  - `Mathlib.Probability.Moments.SubGaussian`
- Real-analysis/asymptotics support:
  - `Mathlib.Analysis.SpecialFunctions.Log.Basic`
  - `Mathlib.Data.Real.Sqrt`
  - `Mathlib.Analysis.Asymptotics.Defs`
  - `Mathlib.Analysis.Asymptotics.SpecificAsymptotics`
- What should come from mathlib rather than be rebuilt locally:
  - simple-graph basic API, clique/independent-set API, and `indepNum`
  - general finite-cardinality lemmas and binomial-coefficient bounds
  - Chernoff/Hoeffding/Azuma-Hoeffding style probability bounds from the subgaussian toolkit
- What still needs project-local formalization:
  - the two-layer random construction and its deletion rules
  - the fiber/projection bookkeeping
  - the open/closed pair apparatus (`X_v`, `C(I)`, `C⁺(I)`, etc.)
  - a finite-sample hypergeometric concentration lemma, unless an exact ready-made statement is found during implementation
  - a bounded-difference / McDiarmid-style lemma if the existing Azuma-Hoeffding API is not directly ergonomic
  - a local Ramsey witness/number definition

## New Definitions
- Public-facing definitions for `PaperDefinitions.lean`:
  - a local witness predicate for triangle-free graphs with no independent set of size `k`
  - optionally a local off-diagonal Ramsey number definition, built only after the witness predicate is in place
  - paper-facing parameter abbreviations if they make theorem statements cleaner
- Internal construction data:
  - `RVertex := Fin m`, `BVertex := Fin m`, `Vertex := Fin n`
  - a record containing `G_R`, `G_B`, and the injection `π : Vertex ↪ RVertex × BVertex`
  - projection maps `π_R`, `π_B`
  - fibers `F(r)` and `F(b)`
- Colored graph model:
  - represent the paper's multigraph bookkeeping as two simple-graph layers on the same vertex type
  - define the lifted red and blue pregraphs on `Vertex`
  - define deletion predicates for monochromatic and mixed triangles
  - define the final simple graph as the union of retained red and blue edges
  - do not formalize an actual multigraph unless later forced to; the paper itself only uses the multigraph for bookkeeping, and the final theorem is about a simple graph
- Closed-pair bookkeeping:
  - `X_v(I)`, `X_v⁺(I)`
  - `C(I)`, `C⁺(I)`, `O(I)`, `O⁺(I)`
  - thresholds `t1`, `t2`, `t3`
  - the partitions `H_I`, `L_I`, `M_I`, `S_I`
  - the counting function `f(ℓ_R, ℓ_B)` used in Section 4
- Good-event definitions:
  - the analogue of `𝒟`
  - the events for medium and small contributions (`𝒨`, `𝒮`)
  - the combined good event `𝓡`

## Proof Roadmap
- File/module structure:
  - `Twobites/PaperDefinitions.lean`: public definitions and statement-facing notation
  - `Twobites/PaperTheorems.lean`: final paper-facing theorem statements and imports
  - helper modules likely needed:
    - `Twobites/ParameterBounds.lean`
    - `Twobites/Construction.lean`
    - `Twobites/Concentration.lean`
    - `Twobites/ClosedPairs.lean`
    - `Twobites/IndependentSets.lean`
    - `Twobites/Ramsey.lean`
- Dependency order:
  1. Statement layer first:
     - settle the exact Lean signatures for the public theorems
     - decide whether the Ramsey corollary is exposed through a local Ramsey-number definition or through a witness theorem plus a wrapper theorem
  2. Deterministic construction layer:
     - define the two-color lift from `G_R`, `G_B`, and `π`
     - prove basic facts about fibers, projections, neighborhoods, and the final graph
     - isolate the paper corrections already recorded in `PAPERNOTES.md` so they never appear as inconsistencies in the Lean development
  3. Parameter-arithmetic layer:
     - package all "for sufficiently large `n`" inequalities involving
       `s = log^2 n`, `m = n / s`, `p = β * sqrt (log n / n)`, `k = κ * sqrt (n log n)`
     - isolate the small-`ε` inequalities needed in Lemma `RI`
     - keep these arithmetic lemmas separate so the probabilistic files do not get buried in routine real-analysis rewrites
  4. Concentration layer:
     - formalize the appendix inequalities actually used
     - reuse mathlib's subgaussian/Chernoff/Hoeffding tools where possible
     - derive a project-local bounded-difference statement for the `lem:small` argument if a direct McDiarmid theorem is not already available
     - prove a local hypergeometric-style tail bound for intersections created by uniform sampling without replacement
  5. Event `𝒟` layer:
     - split `lem:fiber_and_degree` into separate concentration lemmas:
       - fiber sizes
       - degrees in `G_R`, `G_B`
       - sizes of lifted neighborhoods
       - codegrees in the lifted graph
       - projected codegrees
     - this should mirror the paper-check note that the proof sketch must become several reusable lemmas
  6. Closed-pair counting layer:
     - formalize the `large`, `medium`, `small`, and `huge` lemmas as four separate files/sections
     - treat the huge-case projection inequalities as the bridge between the raw construction and the final independence-number calculation
    - in the huge cross-term bridge, keep separate the union-size slack and the projected-codegree overlap slack; the capped/right-branch comparison should only pay a quadratic penalty on the overlap slack, not on the full combined error
    - the direct witness theorem `paper_huge_deterministic_of_witnessSplitRightErrorBounds` is now in place and the canonical helper chain `...of_realErrorBound` / `...of_coeffBound` / `...of_rightSmall` / `...of_paramDeficit` has been rethreaded through `paperHuge*CrossWitnessRightSplitErrorProp`
    - the paper-scale split right-branch arithmetic is now formalized both at general witness scale `B` and at the specialization `B = 3 * κ * log log n`, via `splitRightCoeff_le_eps_mul_choose_two_of_sum_le_of_three_mul_le` and `splitRightCoeff_le_eps_mul_cap_choose_two_add_choose_two_of_sum_le_of_three_mul_le`, so the canonical huge-case wrappers no longer need the ruled-out combined-error right-smallness target
    - the threshold comparison `t_2 ≤ t_1` is now discharged directly from the large-`n` hypothesis `2 ≤ log log n`, and the later huge wrappers now use reusable `log log n` positivity/lower-bound lemmas instead of local ad hoc derivations
    - the large-`n` lower bound `2 < t_1` is now proved directly from `2 ≤ log log n` via `two_lt_paperT1_of_two_le_loglog` / `two_lt_paperT1_of_two_div_le_of_le_one`, and the later `(2 + ε₁)` paperHugeWitness wrappers no longer carry `hT1` as an external assumption
    - the later collapsed paperHugeWitness wrappers are now formally understood to be dead ends: `not_three_mul_paperK_three_loglog_codegCoeff_le_cross_residual`, `not_three_mul_paperK_two_mul_le_cross_residual`, and `not_six_mul_paperK_le_cross_residual` show that the `...of_split` / `...of_doubleEps` / `...of_kSmall` right-smallness hypotheses cannot hold in the paper regime
    - the viable huge-case endpoint is therefore `paper_huge_deterministic_of_paperHugeWitness_of_eps1Slack_of_three_of_diagScale_of_codegScale`, with an explicit `δsplit` still carried through the final gap assumptions; the next proof frontier moves upward into the Section 4 reveal-process and independence-number argument rather than further collapsing the huge-case coefficient package
    - the first Section 4 infrastructure is now in place in `IndependentSets.lean`: `baseImage`, `baseFiber`, `baseNeighborSet`, `section4F0/F1/F2/F`, and `OpenPairOn` / `OpenPairPlusOn` provide a checked language for “revealed” and “unrevealed” pairs that can be reused in the `lem:RISI` formalization
    - the Section 4 bookkeeping now also has the first checked reveal consequences: same-color projection images match `baseNeighborSet ∩ baseImage`, the red/blue `X_v(I)` sets decompose as disjoint unions of same-color fibers, `section4F1_card_mul_log_le_two_mul_card` gives the paper's total `|F_1|` bound, `section4F2_subset_LPart_union_HPart_of_log_pos_of_paperT3_le_paperT2` packages the easy `F₂ ⊆ L_I ∪ H_I` direction, and the new lemmas `baseFiber_card_le_log_of_mem_baseImage_of_not_mem_section4F1`, `xCard_*_le_fiberBound_mul_section4F1_neighbor_card_add_log_mul_degreeBound_of_goodEventD`, and `baseImage_inter_HPart_subset_section4F2_of_goodEventD_of_section4_bound` formalize the hard `H_I`-to-`F₂` route in the same split form as the paper
    - the paper-scale Section 4 arithmetic is now specialized as `paperSection4Bound_le_paperT1_of_two_le_loglog_of_fiberScale` in `ParameterBounds.lean`, and `IndependentSets.lean` now exposes the corresponding paper wrapper `baseImage_inter_HPart_subset_section4F2_of_goodEventD_of_paperSection4Bound` together with the paper-normalized size bounds `section4F1_card_le_two_mul_card_div_log`, `section4F2_card_le_card_LPart_union_HPart_of_paper`, `section4F2_card_le_card_LPart_add_card_HPart_of_paper`, and the combined reveal-budget lemmas `section4F1_union_section4F2_card_le_two_mul_card_div_log_add_card_LPart_add_card_HPart` / `card_mul_section4F1_union_section4F2_card_le_two_mul_card_sq_div_log_add_card_mul_parts`
    - the next concrete subgoal is to turn that `|I| * |F_1 ∪ F_2|` vertex-budget inequality into an actual upper bound on how many open pairs the Section 4 reveal process destroys, and then package the remaining unrevealed pairs as an `OpenPairOn I (section4F I ε)` lower bound combining the large/medium/small/huge deterministic lemmas with the reveal-set bookkeeping
  7. Section 4 layer:
     - formalize the reveal process
     - prove the unrevealed-open-pair lower bound
     - prove the conditional bound analogous to `lem:RISI`
     - isolate the pure algebra/optimization in `lem:RI` into standalone lemmas, especially the three cases in `x_R + x_B`
  8. Existence theorem:
     - show the probability of a bad `k`-set is summably small
     - deduce a positive-probability good outcome
     - extract an existential witness `G : SimpleGraph (Fin n)`
  9. Ramsey corollary:
     - convert the witness graph to `IndepSetFree k`
     - package the lower bound in the chosen local Ramsey-language
- Tactical implementation advice:
  - keep all probabilistic objects on finite sample spaces whenever possible
  - prefer PMF/uniform finite distributions for the actual construction, and only coerce to measures when needed for existing concentration theorems
  - isolate every asymptotic inequality that depends only on `n`, `ε`, `β`, `κ` into separate lemmas before attacking the main proofs
  - prove deterministic helper lemmas before introducing probability

## Design Questions
- No external input is currently required.
- The default implementation choices are:
  - use simple graphs plus separate red/blue layers instead of a genuine multigraph
  - formalize the Ramsey statement through a local witness definition first, then add a local Ramsey-number wrapper if it remains lightweight
  - absorb the paper corrections from `PAPERNOTES.md` directly into the Lean statements/proofs rather than formalizing the uncorrected LaTeX text
