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
    - the Section 4 reveal budget now has a concrete finite counting object: `revealedBaseArcSet` / `revealedBasePairSet` and their specialization `section4RevealPairSet` count the same-color base-image pairs exposed by querying vertices in `F_1 ∪ F_2`, with checked bounds `section4RevealPairSet_card_le_section4_budget` and `cast_section4RevealPairSet_card_le_two_mul_card_sq_div_log_add_card_mul_parts`
    - the actual base-image open pairs touched by the reveal process are now formalized as `revealedBaseOpenPairSet` / `unrevealedBaseOpenPairSet`; the orientation map `orientBaseOpenPairToReveal` gives an injection into `section4RevealPairSet`, and the equalities `revealedBaseOpenPairSet_section4F_eq_union` / `unrevealedBaseOpenPairSet_section4F_eq_union` show that `F_0` contributes nothing on base-image open pairs because both endpoints already lie in `π_R(I) ∪ π_B(I)`
    - the current Section 4 subtraction endpoint is `openPair_lower_bound_sub_section4_budget_le_unrevealed_section4F`: any deterministic lower bound on `|baseOpenPairSet I|` now yields the corresponding lower bound on unrevealed base open pairs after subtracting the `|I| * |F_1 ∪ F_2|` reveal budget
    - the paper’s actual unrevealed same-color pair object is now formalized separately as `basePairSet` / `unrevealedBasePairSet`; the inclusion `unrevealedBaseOpenPairSet_subset_unrevealedBasePairSet` and the specialization `openPair_lower_bound_sub_section4_budget_le_unrevealedBasePairSet_section4F` already move the deterministic lower bound onto the `E_I` side
    - the later semantic split from `E_I` to `T_R` / `T_B` is now formalized at the finset level: `redBaseClosedPlusPair` / `blueBaseClosedPlusPair` capture the same-color `ClosedPairPlus` contribution, `section4TRedPairSet` / `section4TBluePairSet` / `section4TPairSet` package the survivors, and `openPair_lower_bound_sub_section4_budget_sub_sameColorClosedPlus_le_section4TPairSet` transfers the current deterministic lower bound once an upper bound on `sameColorClosedPlusBasePairSet` is supplied
    - the same-color subtraction term is now discharged by a finitary witness count from `π_R(I)` and `π_B(I)`: `redBaseClosedPlusPairSet_card_le_redProjectionPairCount`, `blueBaseClosedPlusPairSet_card_le_blueProjectionPairCount`, `sameColorClosedPlusBasePairSet_card_le_projectionPairCount_sum`, and `openPair_lower_bound_sub_section4_budget_sub_projectionPairCount_sum_le_section4TPairSet` show that the current `T`-count loses at most the red/blue same-color projection-pair contribution
    - the opposite-color witness side is now also formalized: `redOppositeWitnessBiUnion` / `blueOppositeWitnessBiUnion` package the mixed-witness pools from the red and blue images, `section4URedCondPairSet` / `section4UBlueCondPairSet` package the exact conditioned `U_R` / `U_B` finsets using `OpenPairOn`, `OpenPairPlus`, and nonadjacency in `finalGraph`, and the inclusion/cardinality bounds `section4URedCondPairSet_image_sym2_subset_redOppositeWitnessBiUnion_of_indep`, `section4UBlueCondPairSet_image_sym2_subset_blueOppositeWitnessBiUnion_of_indep`, `section4URedCondPairSet_card_le_redProjectionPairCount_of_indep`, and `section4UBlueCondPairSet_card_le_blueProjectionPairCount_of_indep` now feed a checked event-counting layer: `section4UCondPairSet`, `section4TRemainingPairSet`, `section4TRemainingPairSet_card_eq_of_card_eq_condCounts`, `section4TPairSet_lower_bound_sub_oppositeProjectionCounts_of_indep_le_card_sub_uR_sub_uB`, and `openPair_lower_bound_sub_section4_budget_sub_projectionPairCount_sum_sub_oppositeProjectionCounts_le_card_sub_uR_sub_uB` reduce the remaining Section 4 work to the actual Bernoulli/conditional-probability estimate of `lem:RISI`
    - the finite second-stage wrapper is now explicit both as a literal sample space and as an exponential count bound: `section4TRedChoiceSet` / `section4TBlueChoiceSet` / `section4TChoiceSet` package the genuine size-`(u_R,u_B)` second-stage outcome space inside `T_R × T_B`, `section4SecondStageEventMass` is the generic Bernoulli mass on such finite event families, and `section4UCondChoiceOutcome_mem_section4TChoiceSet_of_card_eq` / `section4UCondChoiceEvent_subset_section4TChoiceSet_of_card_eq` place the actual conditioned outcome/event inside that space; meanwhile `section4URedChoiceSet` / `section4UBlueChoiceSet` / `section4UChoiceSet` still package the opposite-witness overcount used for the union bound, `section4UCondChoiceOutcome` / `section4UCondChoiceEvent` / `section4UCondChoiceEventMass` / `section4UCondChoiceEventMassSum` package the actual conditioned outcome as a literal finite event family, `section4UCondChoiceEventMass_le_section4ChoiceEventMass_of_indep` and `section4UCondChoiceEventMassSum_le_section4ChoiceEventMassSum_of_indep` compare that actual family against the choice-count mass, and the exact-count lemmas `section4UCondChoiceEventMass_eq_bernoulliMass_of_card_eq`, `section4UCondChoiceEventMass_eq_zero_of_not_card_eq`, `section4UCondChoiceEventMassSum_eq_section4UCondChoiceEventMass_of_card_le`, and `section4UCondChoiceEventMassSum_eq_bernoulliMass_of_card_le` collapse the full summed counted-event family back to the single actual conditioned outcome whenever the index caps cover the true `(u_R,u_B)` counts; `section4ProjectionChoiceMassSum_eq_closedForm` and `section4ProjectionChoiceMassSum_le_exp` collapse the summed projection-count mass to a closed form and then to one exponential, `section4UCondChoiceEventMassSum_section4F_le_exp_of_indep` packages the full summed Section 4 event count directly in exponential paper scale, `section4UCondChoiceEventMassSum_section4F_le_exp_of_indep_of_bounds` lets later `lem:RISI` work plug in abstract bounds on the remaining-pair count and the red/blue witness caps without reopening the raw Section 4 count expression, `section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_bounds` transfers that exponential estimate to the literal actual conditioned event mass on `section4F`, `section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_bounds_of_sum_le` trades the separate red/blue witness caps for one paper-style exponent error term, and `section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_totalError` packages the entire checked reveal-plus-witness loss into a single total-error exponent against a chosen lower bound `N` for the canonical base open-pair count; the new semantic aliases `section4SecondStageLossNat` and `section4ActualConditionedEventMass`, together with `section4ActualConditionedEventMass_le_exp_of_indep_of_totalError`, now identify the literal actual conditioned Section 4 event inside this finite Bernoulli framework, while the new structural loss lemmas `outside_section4F_subset_LPart_union_MPart_union_SPart_of_HPart_subset_section4F2`, `oppositeProjectionPairCount_sum_outside_section4F_le_partPairCount_LMS_of_HPart_subset_section4F2`, `projectionPairCount_sum_baseImage_le_partPairCount_LMS_add_huge_of_thresholds`, `section4SecondStageLossNat_le_revealBudget_add_two_mul_partPairCount_LMS_add_huge`, `section4SecondStageLossNat_add_witnessCaps_le_revealBudget_add_three_mul_partPairCount_LMS_add_huge`, `cast_partPairCount_LMS_le_sum_of_thresholds`, `section4ActualConditionedEventMass_le_exp_of_indep_of_LMS_totalError`, and `section4ActualConditionedEventMass_le_exp_of_indep_of_splitPartTotalError` reduce the remaining Section 4 work to paper-scale arithmetic instantiation of the separate reveal, large, medium, small, and huge error terms; the later wrappers `paperSection4OpenPairTargetNat` / `paperSection4OpenPairTarget`, the closed-pair target-gap bridges in both target orderings (`paperSection4OpenPairTargetNat_sub_errorSum_le_baseOpenPairSet_card_of_closedErrorBounds`, `paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_closedErrorBounds`, and the swapped-color/real variants), the natural-color closed-pair error wrappers `redBaseClosedPairSet_card_le_paperHugeRedCrossTargetNat_add_of_indep_of_LMSHugeBounds` / `blueBaseClosedPairSet_card_le_paperHugeBlueCrossTargetNat_add_of_indep_of_LMSHugeBounds`, the combined bridge `paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_splitClosedErrorBounds`, the paper deterministic instantiations `paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_uniformPaperErrorBounds` / `paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_paperDeterministic`, the raw huge-cross slack lemmas `paperHugeRedCrossTargetNat_cast_le_paperKSq`, `paperHugeBlueCrossTargetNat_cast_le_paperKSq`, and `four_mul_eps_mul_paperKSq_add_eps_mul_natTarget_le_ceil_five_mul_eps_mul_paperKSq`, and the sharpened manuscript-scale target-gap theorems `paperSection4OpenPairTarget_sub_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_uniformPaperErrorBounds`, `paperSection4OpenPairTarget_sub_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministic`, and `paperSection4OpenPairTargetNat_sub_ceil_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministic` now collapse the canonical closed-pair bookkeeping to the paper’s `10 * ε1 * k^2` loss form; the new loss-side theorems `cast_section4LossTarget_le_nine_mul_eps_mul_paperKSq_of_uniformBounds` and `section4LossTargetNat_le_ceil_nine_mul_eps_mul_paperKSq_of_paperDeterministic` isolate the complementary manuscript-scale `9 * ε1 * k^2` Section 4 loss term itself, the new target lower-bound lemmas `paperSection4OpenPairTarget_lower_bound_of_targetBounds`, `paperSection4OpenPairTarget_lower_bound_of_blueLeft_of_redLeft`, `paperSection4OpenPairTarget_lower_bound_of_blueLeft_of_redRight`, and `paperSection4OpenPairTarget_lower_bound_of_blueRight_of_redLeft` expose the exact `min`-branch choices appearing in the paper’s three `x_R + x_B` regimes, and the new shorthand `paperRISILossNat` together with `paper_risi_hLossGap_of_blueLeft_of_redLeft`, `paper_risi_hLossGap_of_blueLeft_of_redRight`, and `paper_risi_hLossGap_of_blueRight_of_redLeft` now turn those regime-specific real lower bounds directly into the nat-valued `hLossGap` required by `paper_risi_finiteMassBound_of_targetGapArithmetic`; the new exact large-sum identity `paperSection4Branch_blueLeft_redLeft_eq` and its wrapper `paper_risi_hLossGap_of_blueLeft_of_redLeft_sumGap` further reduce the left/left regime to a single lower bound on `(|π_R(I)| + |π_B(I)| - k) * (k - 1)`. On the literal event side `section4BernoulliMass_antitone_remaining`, `section4ActualConditionedEventMass_antitone`, `section4ActualConditionedEventMass_baseOpenPairSet_card_le_exp_of_indep_of_uniformError_of_paperLargeWitness_of_paperHugeWitness_of_targetGap`, `section4ActualConditionedEventMass_baseOpenPairSet_card_le_exp_of_indep_of_uniformError_of_paperLargeWitness_of_paperHugeWitness_of_paperDeterministicTargetGap`, and the new wrapper `paper_risi_finiteMassBound_of_targetGapArithmetic` reduce `lem:RISI` to one remaining arithmetic hypothesis: show that the relevant branch expression from the paper’s `f(ℓ_R,ℓ_B)` case split dominates `paperRISILossNat` (equivalently `⌈9 * ε1 * k^2⌉ + ⌈10 * ε1 * k^2⌉`). The remaining Section 4 work is therefore exactly the final image-size arithmetic in the mixed branches together with the asymptotic simplification/summation feeding `lem:RI`
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
