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
  The witness-form side now has the basic monotonicity lemma `triangleFreeRamseyWitness_mono`, so a
  witness on `n` vertices automatically restricts to one on every `m ≤ n`; the remaining gap on
  the Ramsey-number side is therefore only the separate existence/nonemptiness layer for the local
  `sInf`-based definition.
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
    - the finite second-stage wrapper is now explicit both as a literal sample space and as an exponential count bound: `section4TRedChoiceSet` / `section4TBlueChoiceSet` / `section4TChoiceSet` package the genuine size-`(u_R,u_B)` second-stage outcome space inside `T_R × T_B`, `section4SecondStageEventMass` is the generic Bernoulli mass on such finite event families, and `section4UCondChoiceOutcome_mem_section4TChoiceSet_of_card_eq` / `section4UCondChoiceEvent_subset_section4TChoiceSet_of_card_eq` place the actual conditioned outcome/event inside that space; meanwhile `section4URedChoiceSet` / `section4UBlueChoiceSet` / `section4UChoiceSet` still package the opposite-witness overcount used for the union bound, `section4UCondChoiceOutcome` / `section4UCondChoiceEvent` / `section4UCondChoiceEventMass` / `section4UCondChoiceEventMassSum` package the actual conditioned outcome as a literal finite event family, `section4UCondChoiceEventMass_le_section4ChoiceEventMass_of_indep` and `section4UCondChoiceEventMassSum_le_section4ChoiceEventMassSum_of_indep` compare that actual family against the choice-count mass, and the exact-count lemmas `section4UCondChoiceEventMass_eq_bernoulliMass_of_card_eq`, `section4UCondChoiceEventMass_eq_zero_of_not_card_eq`, `section4UCondChoiceEventMassSum_eq_section4UCondChoiceEventMass_of_card_le`, and `section4UCondChoiceEventMassSum_eq_bernoulliMass_of_card_le` collapse the full summed counted-event family back to the single actual conditioned outcome whenever the index caps cover the true `(u_R,u_B)` counts; `section4ProjectionChoiceMassSum_eq_closedForm` and `section4ProjectionChoiceMassSum_le_exp` collapse the summed projection-count mass to a closed form and then to one exponential, `section4UCondChoiceEventMassSum_section4F_le_exp_of_indep` packages the full summed Section 4 event count directly in exponential paper scale, `section4UCondChoiceEventMassSum_section4F_le_exp_of_indep_of_bounds` lets later `lem:RISI` work plug in abstract bounds on the remaining-pair count and the red/blue witness caps without reopening the raw Section 4 count expression, `section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_bounds` transfers that exponential estimate to the literal actual conditioned event mass on `section4F`, `section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_bounds_of_sum_le` trades the separate red/blue witness caps for one paper-style exponent error term, and `section4UCondChoiceEventMass_section4F_le_exp_of_indep_of_totalError` packages the entire checked reveal-plus-witness loss into a single total-error exponent against a chosen lower bound `N` for the canonical base open-pair count; the new semantic aliases `section4SecondStageLossNat` and `section4ActualConditionedEventMass`, together with `section4ActualConditionedEventMass_le_exp_of_indep_of_totalError`, now identify the literal actual conditioned Section 4 event inside this finite Bernoulli framework, while the new structural loss lemmas `outside_section4F_subset_LPart_union_MPart_union_SPart_of_HPart_subset_section4F2`, `oppositeProjectionPairCount_sum_outside_section4F_le_partPairCount_LMS_of_HPart_subset_section4F2`, `projectionPairCount_sum_baseImage_le_partPairCount_LMS_add_huge_of_thresholds`, `section4SecondStageLossNat_le_revealBudget_add_two_mul_partPairCount_LMS_add_huge`, `section4SecondStageLossNat_add_witnessCaps_le_revealBudget_add_three_mul_partPairCount_LMS_add_huge`, `cast_partPairCount_LMS_le_sum_of_thresholds`, `section4ActualConditionedEventMass_le_exp_of_indep_of_LMS_totalError`, and `section4ActualConditionedEventMass_le_exp_of_indep_of_splitPartTotalError` reduce the remaining Section 4 work to paper-scale arithmetic instantiation of the separate reveal, large, medium, small, and huge error terms; the later wrappers `paperSection4OpenPairTargetNat` / `paperSection4OpenPairTarget`, the closed-pair target-gap bridges in both target orderings (`paperSection4OpenPairTargetNat_sub_errorSum_le_baseOpenPairSet_card_of_closedErrorBounds`, `paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_closedErrorBounds`, and the swapped-color/real variants), the natural-color closed-pair error wrappers `redBaseClosedPairSet_card_le_paperHugeRedCrossTargetNat_add_of_indep_of_LMSHugeBounds` / `blueBaseClosedPairSet_card_le_paperHugeBlueCrossTargetNat_add_of_indep_of_LMSHugeBounds`, the combined bridge `paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_splitClosedErrorBounds`, the paper deterministic instantiations `paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_uniformPaperErrorBounds` / `paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_paperDeterministic`, the raw huge-cross slack lemmas `paperHugeRedCrossTargetNat_cast_le_paperKSq`, `paperHugeBlueCrossTargetNat_cast_le_paperKSq`, and `four_mul_eps_mul_paperKSq_add_eps_mul_natTarget_le_ceil_five_mul_eps_mul_paperKSq`, and the sharpened manuscript-scale target-gap theorems `paperSection4OpenPairTarget_sub_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_uniformPaperErrorBounds`, `paperSection4OpenPairTarget_sub_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministic`, and `paperSection4OpenPairTargetNat_sub_ceil_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministic` now collapse the canonical closed-pair bookkeeping to the paper’s `10 * ε1 * k^2` loss form; the new loss-side theorems `cast_section4LossTarget_le_nine_mul_eps_mul_paperKSq_of_uniformBounds` and `section4LossTargetNat_le_ceil_nine_mul_eps_mul_paperKSq_of_paperDeterministic` isolate the complementary manuscript-scale `9 * ε1 * k^2` Section 4 loss term itself, the new target lower-bound lemmas `paperSection4OpenPairTarget_lower_bound_of_targetBounds`, `paperSection4OpenPairTarget_lower_bound_of_blueLeft_of_redLeft`, `paperSection4OpenPairTarget_lower_bound_of_blueLeft_of_redRight`, and `paperSection4OpenPairTarget_lower_bound_of_blueRight_of_redLeft` expose the exact `min`-branch choices appearing in the paper’s three `x_R + x_B` regimes, and the new shorthand `paperRISILossNat` together with `paperRISILossNat_le_natCeil_nineteen_mul_eps_mul_paperKSq_add_one`, `paper_risi_hLossGap_of_blueLeft_of_redLeft`, `paper_risi_hLossGap_of_blueLeft_of_redRight`, `paper_risi_hLossGap_of_blueRight_of_redLeft`, `paper_risi_hLossGap_of_blueLeft_of_redRight_subGap`, `paper_risi_hLossGap_of_blueLeft_of_redRight_subGap_of_card_le_of_one_le_gap_of_le`, `paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_card_le_of_one_le_gap_of_le`, `paper_risi_hLossGap_of_blueRight_of_redLeft_subGap`, `paper_risi_hLossGap_of_blueRight_of_redLeft_subGap_of_card_le_of_one_le_gap_of_le`, and `paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_card_le_of_one_le_gap_of_le` now turn the branchwise real lower bounds directly into the nat-valued target domination used by the literal finite-mass endpoint `paper_risi_finiteMassBound_of_paperRISILossGap`; the large-sum branch is reduced to a concrete natural sum-gap times `(k-1)`, and the two mixed branches are reduced to concrete natural shortfall-versus-right-gap inequalities together with the one-gap cap arithmetic that upgrades image-card parameter bounds and a separately proved lower bound on the right gap into the exact mixed-branch hypotheses. The remaining Section 4 work is now exactly the paper-parameter arithmetic showing that the near-one regimes at `β = 1/2` and `κ = 1 + ε` imply those mixed shortfall/right-gap bounds, followed by the final asymptotic simplification/summation feeding `lem:RI`.
    - the new direct right-gap bridges `paperKNat_le_paperKNat_sub_redImage_card_sub_paperCapNat_of_card_le_of_two_le_gap_of_le`, `paperKNat_le_paperKNat_sub_blueImage_card_sub_paperCapNat_of_card_le_of_two_le_gap_of_le`, `paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_card_le_of_two_le_gap_of_le`, and `paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_card_le_of_two_le_gap_of_le` eliminate the last ad hoc mixed-branch bookkeeping: once the paper-parameter inequalities provide a positive lower bound `paperKNat δ` on the right-gap term, the near-one branches feed directly into `paper_risi_finiteMassBound_of_paperRISILossGap`
    - the new manuscript-coefficient wrappers `paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_paperNearOne` and `paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_paperNearOne` specialize that route to the paper’s mixed-case parameters `β = 1/2`, `κ = 1 + ε`, and residual split `ε (1 - ε) / 8 + ε (1 - ε) / 8`, so the remaining gap is just the actual near-one image-size arithmetic from the manuscript
    - the new parameter lemmas `two_le_paperK_of_two_div_le_of_le_one`, `mul_paperK_eq_paperK_mul`, `le_paperKNat_of_cast_le_paperK`, `paperRI_nearOne_blueCoeff_le_of_symm_of_sum_le`, `paperRI_nearOne_mixedCoeff_eq`, `paperRI_nearOne_mixedCoeff_le_final`, and `paperRI_nearOne_finalCoeff_neg`, the coefficient-halving bound `le_paperKNat_half_of_two_mul_le_paperKNat`, the image-card specializations `blueImage_card_le_paperKNat_half_of_sum_le_of_blue_le_red` / `redImage_card_le_paperKNat_half_of_sum_le_of_red_le_blue`, the real-to-nat near-one bridge `imageSum_card_le_paperKNat_of_paperNearOneReal`, the paper-specific near-one image bounds `blueImage_card_le_paperKNat_of_paperNearOneSum_of_blue_le_red` / `redImage_card_le_paperKNat_of_paperNearOneSum_of_red_le_blue` and `blueImage_card_le_paperKNat_of_paperNearOneReal_of_blue_le_red` / `redImage_card_le_paperKNat_of_paperNearOneReal_of_red_le_blue`, and the lifted mixed-case wrappers `paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_paperNearOne_of_two_div_le_loglog`, `paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_paperNearOne_of_two_div_le_loglog`, `paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_paperNearOneSum_of_blue_le_red_of_two_div_le_loglog`, `paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_paperNearOneSum_of_red_le_blue_of_two_div_le_loglog`, `paper_risi_hLossGap_of_blueLeft_of_redRight_gapLower_of_paperNearOneReal_of_blue_le_red_of_two_div_le_loglog`, and `paper_risi_hLossGap_of_blueRight_of_redLeft_gapLower_of_paperNearOneReal_of_red_le_blue_of_two_div_le_loglog` now absorb both the separate `2 ≤ paperK (ε (1 - ε) / 8) n` side-condition and the manuscript’s symmetry-to-image-card ceiling step into checked wrappers. The key remaining point is no longer raw Section 4 target positivity in the middle case: the mixed branches have to be finished at the combined `P(\mathcal S_{I,\ell_R,\ell_B})` plus `lem:RISI` exponent level, exactly as in the manuscript, because the raw mixed Section 4 target can be negative near the lower edge of the near-one regime.
    - the new outer-exponent arithmetic lemmas `paperRI_smallSumCoeff_le`, `paperRI_smallSumCoeff_neg`, `paperRI_largeSumCoeff_eq`, `paperRI_largeSumCoeff_le_final`, and `paperRI_largeSum_finalCoeff_neg` now settle the small- and large-sum `lem:RI` coefficients directly from `eq:long`; the remaining gap is to package those coefficients together with the existing middle-regime lemmas into one paper-scale `lem:RI` wrapper and then run the final union-bound summation for Theorem `main`
    - the direct sign wrappers `paperRI_eqLongCoeff_neg_of_smallSum`, `paperRI_eqLongCoeff_neg_of_largeSum`, `paperRI_eqLongCoeff_neg_of_nearOne`, together with the new exponent-scale versions `paperRI_eqLongExp_neg_of_smallSum`, `paperRI_eqLongExp_neg_of_largeSum`, and `paperRI_eqLongExp_neg_of_nearOne`, now reduce all three `lem:RI` regimes to one missing interface theorem packaging the outer `P(\mathcal S_{I,\ell_R,\ell_B})` contribution in the exact `eq:long` form used by the manuscript; after that wrapper exists, the final union-bound sum for Theorem `main` is a bookkeeping step rather than new coefficient algebra
    - the new interface theorem `paper_ri_eqLong_bound_of_outer_le_exp_of_paperRISILossGap` now provides exactly that product-level `eq:long` bridge in the repo’s finite-mass language by multiplying an abstract outer exponential bound with the checked Section 4 `lem:RISI` estimate; the earlier specialization wrappers `paper_ri_outerEventMass_le_exp_of_paperParameterLogs_of_images` / `paper_ri_eqLong_bound_of_outerEventMass_le_exp_of_paperParameterLogs_of_le` already feed the exact outer family `paperRIOuterEventMass (paperMNat n) |π_R(I)| |π_B(I)| (paperKNat (1 + ε) n)` into that bridge using the actual image-card hypotheses on `I`, and the new union-factor wrappers `paperRI_choosePaperKNat_le_exp`, `paperRIChooseOuterEventMass_le_exp_of_paperParameterLogs`, `paper_ri_chooseOuterEventMass_le_exp_of_paperParameterLogs_of_images`, and `paper_ri_eqLong_bound_of_chooseOuterEventMass_le_exp_of_paperParameterLogs_of_le` now insert the literal `{n \choose k}` factor as well. The newest rewrite layer `paperRI_chooseOuterExp_eq`, `paperRI_chooseOuterExp_le_mainRemainder`, `paper_ri_chooseOuterEventMass_le_exp_of_mainRemainder_of_images`, and `paper_ri_eqLong_bound_of_chooseOuterEventMass_le_exp_of_mainRemainder_of_le` has also collapsed the raw union-plus-outer exponent to one main `((x_R+x_B-1)/2) k log n` term plus explicit lower-order remainders. The remaining gap is therefore no longer outer-event plumbing or raw algebra unpacking, but the final numerical absorption of those cleaned remainder terms in the small, large, and near-one regimes.
    - the endpoint cleanups `section4BernoulliMass_le_one`, `section4ActualConditionedEventMass_le_one`, `paper_ri_eqLong_bound_of_outer_smallSum`, and `paper_ri_eqLong_bound_of_outer_le_exp_of_paperRISILossGap_of_le` remove the small-sum branch from the frontier; the new cleaned-remainder support `paperKNat_le_two_mul_paperK_of_one_le`, `paperRI_chooseOuterRemainder_le_largeSum_budget`, `paperRI_chooseOuterRemainder_le_nearOne_budget`, `two_le_delta_mul_paperK_one_add_eps_of_two_div_le`, `paperRI_chooseOuterExp_le_largeSum_main_plus_budget`, `paperRI_chooseOuterExp_le_nearOne_main_plus_budget`, `paperRI_chooseOuterExp_add_risiLargeSum_le_htotal`, and `paperRI_chooseOuterExp_add_risiNearOne_le_htotal`, together with the post-composition wrappers `paper_ri_eqLong_bound_largeSum_of_le`, `paper_ri_eqLong_bound_nearOne_of_le`, `paper_ri_eqLong_bound_largeSum_of_chooseOuterEventMass_le_exp_of_mainRemainder_of_images_of_le`, and `paper_ri_eqLong_bound_nearOne_of_chooseOuterEventMass_le_exp_of_mainRemainder_of_images_of_le`, now isolate the remaining large-/near-one work to the Section 4 side. The newest specializations `paper_ri_eqLong_bound_largeSum_of_chooseOuterEventMass_le_exp_of_mainRemainder_of_images_of_section_le` and `paper_ri_eqLong_bound_nearOne_of_chooseOuterEventMass_le_exp_of_mainRemainder_of_images_of_section_le` complete the generic `htotal` plumbing: once the Section 4 side supplies a branchwise exponent with explicit `- 2 * δ * k * log n` slack, the literal `{n \choose k} * P(\mathcal S_{I,\ell_R,\ell_B})` term now closes automatically. The frontier is therefore no longer outer-event integration or raw `htotal` bookkeeping, but exactly the remaining Section 4 branch coefficients with that explicit slack, followed by the final theorem-level union-bound sum.
    - the large-sum Section 4 slack is now also packaged concretely, and the mixed near-one arithmetic is now checked as well. On the large side, `paperP_mul_paperK_eq_mul_log`, `paperP_mul_paperK_sq_eq_mul_paperK_log`, `paperPHalf_le_one`, `paperPHalf_mul_lossBound_le`, `paperPHalf_mul_sumGapBranch_ge_main_sub_delta`, `paperRI_largeSum_sectionExp_le_of_budget`, and `paper_ri_eqLong_bound_largeSum_of_chooseOuterEventMass_le_exp_of_mainRemainder_of_images_of_budget` reduce the literal `p * (12 * (ε₁ k²) + ⌈10 ε₁ k²⌉) - p * ((x_R + x_B - 1) k (k - 1))` term to the manuscript budget hypothesis `11 * (1 + ε) * ε₁ + 4 * δ ≤ (1 + ε) * ε^3 / 2`. On the mixed near-one side, the lemmas `paperP_half_mul_paperK_half_eq_quarter_log`, `paperK_half_eq_div_paperK_one_add_eps`, `paperPHalf_mul_nearOneCapResidual_ge_main_sub_delta`, `paperRI_nearOne_branchCoeff_eq`, and `paperRI_nearOne_sectionExp_le_of_budget` package the corresponding capped-right-target exponent with the required explicit `- 2 * δ * k * log n` slack, `paper_ri_eqLong_bound_nearOne_of_chooseOuterEventMass_le_exp_of_mainRemainder_of_images_of_budget_of_blueCapNat` feeds that checked budget into the `lem:RI` endpoint under an explicit natural right-gap hypothesis, and the new wrapper `paper_ri_eqLong_bound_nearOne_of_chooseOuterEventMass_le_exp_of_mainRemainder_of_images_of_budget` derives that right-gap hypothesis internally from the existing generic near-one budget data. The new case-split dispatcher `paper_ri_exists_negCoeff_of_chooseOuterEventMass` packages the complete small-, large-, and near-one RI endpoint family into one theorem for a fixed `I`, the uniform shell `paperRIUniformFinalCoeff`, `paper_ri_uniformCoeff_bound_of_chooseOuterEventMass`, `finset_sum_le_of_card_mul_le`, and `sum_powersetCard_le_of_choose_mul_le` packages the remaining finite summation step abstractly, the deterministic endpoints `NoSurvivingIndepSetCard`, `finalGraph_indepSetFree_of_noSurvivingIndepSetCard`, `triangleFreeRamseyWitness_of_noSurvivingIndepSetCard`, and `triangleFreeWithSmallIndepNum_of_noSurvivingIndepSetCard` package the final-graph witness side of the paper statements once a no-surviving-`k`-set theorem is available, the generic support lemma `SimpleGraph.indepNum_lt_of_indepSetFree` has been moved out of `Twobites/PaperDefinitions.lean` into `Twobites/Basic.lean`, the public theorem-level shells `paperMainStatement_of_eventually_exists_finalGraphWitness` and `paperMain2WitnessStatement_of_eventually_exists_finalGraphWitness` now isolate the remaining global existence assumption at the paper-facing level, the finite unweighted sample-space skeleton is now explicit via `ConstructionData.sampleSpace` and `goodEventDSet`, and the minimal weighted layer is now explicit via `constructionGraphBernoulliWeight`, `constructionEmbeddingUniformWeight`, `constructionProductWeight`, `paperConstructionWeight`, `constructionEventMass`, the fixed/global good-surviving event families, the weighted union-bound bridge `constructionEventMass_goodSurvivingIndepSetCardBadSet_le_of_choose_mul_le`, the generic extraction wrapper `exists_goodEventD_with_noSurvivingIndepSetCard_of_choose_mul_le_lt_goodMass`, the paper-weight specializations `exists_goodEventD_with_noSurvivingIndepSetCard_of_paperChooseMulLe_lt_goodMass` / `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_lt_goodMass`, and the new explicit lower-bound specialization `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_lt_explicitGoodMass`. The mass layer now also has exact normalization formulas `constructionGraphBernoulliWeight_sum_univ_eq`, `constructionEmbeddingUniformWeight_sum_univ_eq_one`, `constructionProductWeight_sum_univ_eq`, and `paperConstructionMass_sampleSpace_eq`, while the explicit-witness layer has exact lower-bound formulas `constructionGraphBernoulliWeight_bot_eq`, `constructionProductWeight_emptyBalancedConstructionData_eq`, `paperConstructionWeight_emptyBalancedConstructionData_eq`, and `paperConstructionMass_goodEventDSet_ge_emptyBalancedConstructionWeight_explicit`. The new decomposition theorems `constructionEventMass_eq_sum_embeddings_graphWeights`, `paperGoodSurvivingGraphPairMass`, and `paperConstructionMass_goodSurvivingIndepSetEventSet_eq_sum_by_embedding` now isolate the precise first-stage/embedding split for one fixed `I`: the weighted bad-event mass is reduced to a sum over embeddings of an inner base-graph-pair mass at fixed `π`. The remaining frontier is therefore no longer abstract sample-space plumbing or how to unfold the weighted event family, but the actual quantitative probabilistic estimates on that decomposition: prove the paper weight of each fixed-set event `goodSurvivingIndepSetEventSet ... I` is bounded by the completed RI coefficient by controlling the fixed-embedding inner mass `paperGoodSurvivingGraphPairMass ... I e`, and strengthen the good-event lower bound from these explicit witness and full-space mass formulas to one strong enough to dominate that summed RI bound in the paper regime.
    - the new projection-choice exponential shell now matches the older actual-conditioned shell directly: `section4ProjectionChoiceMassSum_section4F_le_exp_of_bounds`, `section4ProjectionChoiceMassSum_section4F_le_exp_of_totalError`, and `section4ProjectionChoiceMassSum_section4F_le_exp_of_LMS_totalError` let the fixed-embedding reduction stop at the literal `section4ProjectionChoiceMassSum` layer without reopening the full `section4ActualConditionedEventMass` wrapper. This means the only remaining fixed-embedding work is the quantitative collapse of the finite sum of projection-choice masses via the checked three-pool witness decomposition.
    - that shell is now also available in the same split-part error language as the older actual-conditioned endpoint: `section4ProjectionChoiceMassSum_section4F_le_exp_of_splitPartTotalError` packages the reveal/L/M/S/huge error interface directly at the projection-choice layer, and `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_splitPartTotalError` specializes it to one graph-pair summand in the fixed-embedding bad-event reduction. The next step is therefore to convert the checked three-pool cover/cardinality lemmas into the concrete `revealError`, `largeError`, `mediumError`, `smallError`, `hugeRedError`, and `hugeBlueError` inputs for that wrapper and then sum over graph pairs for one embedding.
    - the same projection-choice shell is now uniformized as well: `section4ProjectionChoiceMassSum_section4F_le_exp_of_uniformPartError` and `section4ProjectionChoiceMassSum_section4F_le_exp_of_uniformError` mirror the actual-conditioned `12 * ε_1 * k^2` endpoint directly at the projection-choice layer, the fixed-embedding wrappers `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_uniformPartError`, `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_uniformError`, and `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_uniformError_of_revealWitnessBounds` expose that endpoint directly on one graph-pair summand, and the new target-gap refinements `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_uniformError_of_revealWitnessBounds_of_targetGap`, `..._of_paperLargeWitness_of_paperHugeWitness_of_targetGap`, and `..._of_targetGap_of_paperSection4Bound` now repackage the same pointwise shell in the manuscript’s natural “target minus open-error” form while discharging `H_I ⊆ F_2` automatically from `GoodEventD`. The new lifted wrappers `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_targetGap_of_paperSection4Bound` and `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_targetGap_of_paperSection4Bound` propagate that exact target-gap interface through the filtered fixed-embedding and fixed-set mass reductions, so later combinatorial lemmas can plug in the literal natural target-gap inequalities they prove without first repackaging them into the coarser `paperRISILossNat` shell. Even more directly, the new composed shells `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_section4FTotalError_of_targetGap_of_paperSection4Bound`, `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_section4FTotalError_of_targetGap_of_paperSection4Bound`, and `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_section4FTotalError_of_targetGap_of_paperSection4Bound` now accept a direct Section 4 total-error bound together with a paper target-gap bound, without separately rebuilding the intermediate `hLossLeTarget` inequality. The new deterministic-target-gap wrappers `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_uniformError_of_paperLargeWitness_of_paperHugeWitness_of_paperDeterministicTargetGap_of_paperSection4Bound`, `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_paperSection4Bound`, and `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_paperSection4Bound` now remove even the separate target-gap input from the graph-pair, fixed-embedding, and fixed-set shells by deriving it from the existing deterministic Section 4 bounds, while the new `_of_embeddingImageBounds` variants for the fixed-embedding and fixed-set theorems now pull the red/blue image-cardinality hypotheses out of the graph-pair quantifiers there as well, and the new extraction theorem `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_paperSection4Bound_of_embeddingImageBounds_lt_explicitGoodMass` lifts that deterministic shell through the final explicit-good-mass witness step too. The stronger wrappers `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperDeterministicTargetGap_of_paperSection4Bound`, `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`, `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`, and `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass` now also discharge the routine large/medium/small/huge deterministic contribution bounds internally, so the deterministic-target-gap route carries only the genuinely graph-dependent `hLossLeTarget`, `hSmallCard`, and opposite-color projection-cap hypotheses above the raw graph-pair level. The new helper theorem `goodSurvivingGraphPair_section4LossLeTarget_of_paperRISILossGap` now exposes that exact loss-to-target inequality as a standalone graph-pair lemma under the manuscript loss-gap assumption, instead of leaving it buried inside the heavier exponential endpoint. The manuscript-scale wrapper `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperRISILossGap` now packages the full deterministic `paperRISILossNat ≤ f(ℓ_R,\ell_B)` arithmetic on a single fixed graph-pair contribution, and the wrapper `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperRISILossGap_of_paperSection4Bound` discharges the `H_I ⊆ F_2` hypothesis directly from the paper Section 4 bound. The new `_of_embeddingImageBounds` lifts for `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperRISILossGap_of_paperSection4Bound` and `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperRISILossGap_of_paperSection4Bound` now remove the red/blue image-cardinality hypotheses from that manuscript loss-gap shell as well, and the new extraction wrapper `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds_lt_explicitGoodMass` carries that same route all the way to the final explicit-good-mass witness theorem too, so the remaining combinatorial work on the manuscript loss-gap route is also purely graph-dependent. The near-one branch wrappers `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperNearOneReal_of_blue_le_red_of_two_div_le_loglog_of_paperSection4Bound` and `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperNearOneReal_of_red_le_blue_of_two_div_le_loglog_of_paperSection4Bound` now also absorb the RI loss-gap step itself once the image-sum/order branch and the manuscript near-one loss inequality are supplied, the new lower-level dispatchers `paper_risi_hLossGap_of_paperNearOneReal_of_two_div_le_loglog` and `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperNearOneReal_of_two_div_le_loglog_of_paperSection4Bound` eliminate the remaining manual red/blue order split at the ConstructionData and graph-pair levels, the fixed-embedding lifts `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperNearOneReal_of_blue_le_red_of_two_div_le_loglog_of_paperSection4Bound` / `..._of_red_le_blue_...` and the merged dispatcher `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_paperSection4Bound` make that simplification available directly at the filtered graph-pair sum level, and the wrappers `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_paperSection4Bound_of_embeddingImageBounds`, `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_paperSection4Bound_of_embeddingImageBounds`, and `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_paperSection4Bound_of_embeddingImageBounds_lt_explicitGoodMass` now pull the embedding-only red/blue image bounds, image-sum inequality, and near-one loss inequality out of the graph-pair, fixed-set, and final-extraction quantifiers. The fixed-set lifts `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperNearOneReal_of_blue_le_red_of_two_div_le_loglog_of_paperSection4Bound` / `..._of_red_le_blue_...` together with the merged dispatcher `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_paperSection4Bound` propagate the same near-one shell through the embedding sum for one fixed `I` without needing a separate external image-order case split. The filtered bridge `goodSurvivingGraphPairActualMassIntegrand_le_if_good_projectionChoiceMassBound` / `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_projectionChoiceMass` means the remaining fixed-embedding sum can now stay restricted to graph pairs that actually satisfy `GoodEventD ∧ SurvivesAsIndependent I`, the generic/specialized wrappers `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_of_le` / `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperRISILossGap_of_paperSection4Bound` package the pointwise passage from that filtered sum to a filtered sum of manuscript-scale Section 4 exponents, and the new monotone comparison layer `section4ProjectionChoiceMassSum_mono`, `goodSurvivingGraphPairProjectionChoiceMassBound_le_section4ProjectionChoiceMassSum_of_le`, and `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_section4ProjectionChoiceMass_of_le` now expose the exact three natural parameters that still need to be controlled combinatorially: a lower bound on the surviving `remaining` open-pair count and upper bounds on the red/blue opposite-witness projection counts. The new total-budget wrappers `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_totalBudget_of_le`, `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_totalBudget_of_le`, and `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_totalBudget_of_le` collapse that `(remaining,u_R,u_B)` layer to exponentials once a single natural-number budget inequality of the form `|O_I| - remaining + u_R + u_B ≤ totalError` is proved for each good graph pair, and the new direct `section4F` wrappers `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_section4FTotalError`, `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_section4FTotalError`, and `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_section4FTotalError` re-express the same frontier directly in the paper's natural Section 4 loss coordinates `reveal + 3 * LMS + huge`. Their new `_of_paperSection4Bound` specializations now discharge the residual `H_I ⊆ F_2` side condition automatically from `GoodEventD`, so the remaining RI combinatorics is reduced to the literal Section 4 total-error inequality itself: manufacture that natural-number inequality for each good graph pair from the checked three-pool witness decomposition and the existing `GoodEventD` contribution bounds, then pass it through the already-packaged embedding, fixed-set, near-one, and final-extraction shells. The fixed-set wrappers `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_by_embedding_of_le` / `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperRISILossGap_of_paperSection4Bound` now lift the same shell through `paperConstructionMass_goodSurvivingIndepSetEventSet_eq_sum_by_embedding`. The new extraction wrappers `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_lt_explicitGoodMass_of_massBound`, `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_paperSection4Bound_lt_explicitGoodMass`, `..._of_embeddingImageBounds_lt_explicitGoodMass`, `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_paperSection4Bound_of_embeddingImageBounds_lt_explicitGoodMass`, `..._of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass`, and `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds_lt_explicitGoodMass` now package the final passage from a fixed-set mass majorant to the paper-facing witness theorem, so the frontier is sharpened further: the only remaining substantive task is the genuine combinatorial collapse of the filtered exponential sum for one embedding using the checked three-pool witness decomposition and the existing `GoodEventD` contribution bounds, now concretely phrased as explicit upper/lower bounds on those three naturals or, equivalently, on the single Section 4 total-error natural, with the embedding-only image-size hypotheses already factored out of that remaining graph-pair work.
    - the manuscript `paperRISILossGap` route now also has explicit bridge wrappers into the
      stronger deterministic-target-gap shell:
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperRISILossGap_via_paperDeterministicTargetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`
      and
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperRISILossGap_via_paperDeterministicTargetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`
    - the generic arbitrary-`openError` target-gap interface is now fully packaged through deterministic-bounds fixed-embedding, fixed-set, and final extraction shells as well: `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_targetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`, `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_targetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`, and `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_targetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass`. This means the remaining three-pool collapse can now target a literal graph-pair natural target-gap budget with arbitrary `openError` and feed it straight to the paper-facing witness theorem, without any further wrapper work above the graph-pair layer.
    - the reduced uniform-paper-error target-gap route now also has graph-pair-native open-pair target-gap bridges: `goodSurvivingGraphPair_paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_uniformPaperErrorBounds` and `goodSurvivingGraphPair_paperSection4OpenPairTargetNat_sub_ceil_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_uniformPaperErrorBounds` expose the literal natural-number Section 4 target-gap inequalities directly from `goodSurvivingGraphPairPred` plus the bundled large/medium/small/huge paper-error hypotheses, and `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperDeterministicTargetGap_of_uniformPaperErrorBounds_of_paperSection4Bound` now reuses that graph-pair bridge instead of reopening the underlying `ConstructionData` package. This trims another repeated unpacking block from the reduced target-gap shell and leaves the remaining work concentrated on the genuine three-pool combinatorial hypotheses.
    - there is now also a lighter reduced manuscript route for literal split closed-pair error budgets that does not require the stronger deterministic-bounds packaging above graph-pair level: `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperRISILossGap_of_splitClosedErrorBounds_of_paperSection4Bound`, `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperRISILossGap_of_splitClosedErrorBounds_of_paperSection4Bound`, and `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperRISILossGap_of_splitClosedErrorBounds_of_paperSection4Bound_lt_explicitGoodMass` now carry caller-supplied red/blue/open error budgets from the graph-pair shell through fixed embeddings, fixed sets, and the final explicit-good-mass witness theorem. The remaining combinatorial collapse can therefore target literal split error estimates directly even before the deterministic image-bound hypotheses are available.
      now convert `paperRISILossGap` directly into the stronger `hLossLeTarget` shell via
      `goodSurvivingGraphPair_section4LossLeTarget_of_paperRISILossGap`, and the new pointwise
      theorem
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperRISILossGap_via_paperDeterministicTargetGap_of_paperSection4Bound`
      exposes that same bridge already at the individual good graph-pair level, so later
      combinatorial lemmas can stay in manuscript loss-gap coordinates while reusing the
      deterministic contribution bounds already discharged from `GoodEventD`. The corresponding final extraction
      wrapper
      `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperRISILossGap_via_paperDeterministicTargetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass`
      now carries that bridge route all the way to the paper-facing witness theorem as well.
      The new direct pointwise endpoint
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_section4FTotalError_of_paperRISILossGap_of_paperSection4Bound`
      also bypasses that bridge entirely when later combinatorial lemmas can prove the literal
      Section 4 total-error inequality together with `paperRISILossGap` on one good graph pair, so
      the remaining fixed-embedding collapse can now target those manuscript-native hypotheses
      directly instead of rebuilding the intermediate target-gap cast step. The new lifted shells
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_section4FTotalError_of_paperRISILossGap_of_paperSection4Bound`
      and
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_section4FTotalError_of_paperRISILossGap_of_paperSection4Bound`
      now carry that same direct `hTotal` + `paperRISILossGap` interface through the filtered
      embedding and fixed-set mass reductions, and the new embedding-image-bounds specializations
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_section4FTotalError_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds`
      and
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_section4FTotalError_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds`
      factor the red/blue image-size hypotheses out of that direct route as well. The remaining
      combinatorial step can therefore aim at the manuscript-native graph-pair hypotheses
      `hTotal`, `paperRISILossGap`, `hSmallCard`, and the opposite-color projection-cap bounds all
      the way up to the choose-multiplied bad-event estimate. The final extraction wrapper
      `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_section4FTotalError_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds_lt_explicitGoodMass`
      now carries that same direct route through the explicit-good-mass endpoint too, so the
      remaining blocker is purely to prove those graph-pair hypotheses uniformly and then collapse
      the filtered sum. The new pointwise helper
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_section4FTotalErrorNat_of_paperRISILossGap_of_paperSection4Bound`
      also lets that last graph-pair argument keep the crucial `section4F` total-error hypothesis
      in natural numbers until the final cast to `ℝ`, and the lifted wrappers
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_section4FTotalErrorNat_of_paperRISILossGap_of_paperSection4Bound`,
      `..._of_embeddingImageBounds`,
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_section4FTotalErrorNat_of_paperRISILossGap_of_paperSection4Bound`,
      and `..._of_embeddingImageBounds` now preserve that nat-valued total-error interface through
      the filtered embedding and fixed-set mass shells as well, so the remaining three-pool witness
      collapse can stay in pure counting coordinates right up to the choose-multiplied mass bound.
      The stronger deterministic-bounds specializations
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_section4FTotalErrorNat_of_paperRISILossGap_of_paperSection4Bound_of_paperDeterministicBounds`,
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_section4FTotalErrorNat_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`,
      and
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_section4FTotalErrorNat_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`
      now internalize the routine `12 * ε₁ * k²` estimate coming from the checked reveal/L/M/S/huge
      deterministic bounds, so the nat manuscript-native route is narrowed further: above the
      graph-pair level, only the genuinely graph-dependent `paperRISILossGap`, `SPart`, and
      opposite-color projection-cap hypotheses still remain to be supplied uniformly. The new
      helper
      `goodSurvivingGraphPair_section4FTotalErrorNat_cast_le_twelve_mul_eps_mul_paperKSq_of_paperDeterministicBounds`
      now exposes that deterministic `12 * ε₁ * k²` package directly for one good graph pair, so
      the remaining graph-pair work can focus on manufacturing the literal nat-valued total-error
      inequality and the manuscript loss-gap bound without reopening the deterministic
      large/medium/small/huge contribution arithmetic. The new reusable helper
      `section4UniformContributionBounds_of_paperDeterministic` now centralizes the repeated
      reveal/L/M/S/huge-diagonal `GoodEventD` package itself and is consumed by the current
      deterministic target-gap, direct manuscript-loss-gap, and nat-valued `section4F` graph-pair
      shells, so any later direct huge-case rewrite only has to retarget one deterministic
      contribution lemma instead of several near-duplicate wrappers. The new helper
      `section4SecondStageLossNat_add_witnessCaps_cast_le_totalError_of_LMS_totalError` likewise
      isolates the coercion step from the literal
      `section4SecondStageLossNat + u_R + u_B ≤ reveal + 3 * LMS + huge` counting inequality into a
      reusable theorem before the exponential shell, so the remaining three-pool collapse can target
      the actual graph-pair counting statement directly rather than redoing the cast arithmetic
      inside `section4ProjectionChoiceMassSum_section4F_le_exp_of_LMS_totalError`. The new
      graph-pair helpers
      `goodSurvivingGraphPair_section4SecondStageLossNat_le_revealBudget_add_two_mul_partPairCount_LMS_add_huge_of_paperSection4Bound`
      and
      `goodSurvivingGraphPair_section4SecondStageLossNat_add_witnessCaps_cast_le_totalError_of_LMS_totalError_of_paperSection4Bound`
      now discharge the residual `H_I ⊆ F₂` side condition automatically from `GoodEventD` at the
      literal Section 4 loss layer, so the remaining three-pool witness decomposition only needs to
      manufacture the actual counting inequalities themselves. The final
      fixed-embedding direct manuscript-loss-gap shell
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`
      now exposes the same deterministic-bounds route without naming the intermediate
      deterministic target-gap bridge, so the remaining combinatorial collapse can target a direct
      manuscript-loss-gap interface already at the embedding-sum layer. The matching fixed-set
      shell
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`
      now pushes that same direct deterministic-bounds route through
      `paperConstructionMass_goodSurvivingIndepSetEventSet_eq_sum_by_embedding`, so the remaining
      graph-dependent collapse can stay in manuscript loss-gap coordinates even after fixing the
      independent set `I`. The new final extraction wrapper
      `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass`
      now carries that same direct deterministic-bounds manuscript route through the explicit-good-mass
      endpoint too, so neither the final existence theorem nor the fixed-set shell needs to route
      through the nat total-error specialization or the deterministic target-gap bridge anymore.
      The final
      extraction wrapper
      `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_section4FTotalErrorNat_of_paperRISILossGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass`
      now carries that nat deterministic-bounds manuscript-native route through the explicit-good-mass
      endpoint as well, so the only unfinished step on that branch is the genuinely graph-dependent
      fixed-embedding collapse. In parallel, the new reduced-hypothesis deterministic-target-gap
      lifts
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_uniformPaperErrorBounds_of_paperSection4Bound`
      and
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_uniformPaperErrorBounds_of_paperSection4Bound`
      now bypass the old cap-weight interface above the graph-pair layer entirely: once one good
      graph pair supplies the literal Section 4 loss-to-target inequality and the four huge
      pair-count bounds, the embedding and fixed-set mass shells no longer need any separate
      projection-cap-weight hypotheses. This better matches the checked three-pool witness
      decomposition, whose remaining job is precisely to prove those graph-pair counting bounds.
      The matching final extraction wrapper
      `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_uniformPaperErrorBounds_of_paperSection4Bound_lt_explicitGoodMass`
      now carries that reduced target-gap route through the explicit-good-mass witness theorem as
      well, so the reduced shell no longer stops at a fixed-set bad-event estimate. The new
      deterministic-bounds lifts
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperDeterministicTargetGap_of_uniformPaperErrorBounds_of_paperSection4Bound_of_paperDeterministicBounds`,
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_uniformPaperErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`,
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_uniformPaperErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`,
      and
      `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperDeterministicTargetGap_of_uniformPaperErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass`
      now expose that same lighter target-gap interface with the routine large/medium/small/huge
      contribution bounds discharged internally from the embedding-only image bounds and the
      deterministic Section 4 hypotheses, so the remaining fixed-embedding collapse can target a
      reduced `hLossLeTarget` statement directly without separately restating those contribution
      estimates.
      On the near-one route, the manuscript loss-gap step is now factored out already at raw
      graph-pair level by `graphPair_paperRISILossGap_of_paperNearOneReal_of_blue_le_red_of_two_div_le_loglog`,
      `..._of_red_le_blue_...`, and the merged dispatcher
      `graphPair_paperRISILossGap_of_paperNearOneReal_of_two_div_le_loglog`, so later fixed-embedding
      combinatorics can target that standalone per-pair hypothesis directly instead of reopening the
      `ConstructionData.paper_risi_hLossGap...` lemmas inside each pointwise endpoint. The new
      graph-pair wrappers
      `graphPair_paperRISILossGap_of_blueLeft_of_redRight_gapLower_of_card_le_of_two_le_gap_of_le`
      and
      `graphPair_paperRISILossGap_of_blueRight_of_redLeft_gapLower_of_card_le_of_two_le_gap_of_le`
      now factor out the exact mixed-branch manuscript step one level further: later three-pool
      fixed-embedding lemmas can aim directly at a branch-local image-card bound, a separate
      `2 ≤ paperK η n` right-gap lower bound, and the literal mixed deficit inequality, without
      routing back through the specialized near-one `ConstructionData` lemmas.
      The fixed-embedding, fixed-set, and final explicit-good-mass near-one wrappers
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`,
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`,
      and
      `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass`
      now route that near-one branch through the stronger direct deterministic-bounds manuscript
      `paperRISILossGap` shell all the way to the witness-existence endpoint, so the remaining
      near-one obstruction is the same graph-dependent fixed-embedding collapse as on the direct
      manuscript-loss-gap branch.
      The new reduced graph-pair bridge
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperRISILossGap_of_uniformPaperErrorBounds_of_paperSection4Bound`,
      built on top of
      `section4LossTargetNat_le_ceil_nine_mul_eps_mul_paperKSq_of_uniformBounds` and
      `section4LossLeTarget_of_paperRISILossGap_of_uniformPaperErrorBounds`,
      now also feeds the manuscript `paperRISILossGap` hypothesis directly into the lighter
      uniform-paper-error deterministic-target-gap shell. This means later three-pool
      combinatorial lemmas can choose between proving the direct nat-valued `section4F`
      total-error route or proving the reduced `hLossLeTarget` / huge-cross-count route, without
      reopening the heavier cap-weight deterministic interface.
      The standalone graph-pair lemma
      `goodSurvivingGraphPair_section4LossLeTarget_of_paperRISILossGap_of_uniformPaperErrorBounds`
      now isolates that reduced `hLossLeTarget` conclusion itself, so the remaining combinatorial
      collapse can target a literal natural inequality on one good graph pair before worrying about
      the exponential mass shell.
      The fixed-embedding and fixed-set shells
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperRISILossGap_of_uniformPaperErrorBounds_of_paperSection4Bound`
      and
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperRISILossGap_of_uniformPaperErrorBounds_of_paperSection4Bound`
      now lift that reduced manuscript-loss-gap route above graph-pair level, so later three-pool
      combinatorial lemmas can remain in manuscript `paperRISILossGap` coordinates all the way up
      to the current filtered bad-event mass shell.
      The deterministic-bounds/image-bounds lifts
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperRISILossGap_of_uniformPaperErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`
      and
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperRISILossGap_of_uniformPaperErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`,
      together with the final extraction wrapper
      `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperRISILossGap_of_uniformPaperErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass`,
      now carry that same reduced manuscript interface through the embedding-only image hypotheses,
      the routine deterministic Section 4 contribution bounds, and the explicit-good-mass witness
      theorem as well.
      The reusable graph-pair deterministic contribution wrapper
      `goodSurvivingGraphPair_section4UniformContributionBounds_of_paperDeterministicBounds`
      now exposes the reveal/L/M/S/huge-diagonal estimates directly from
      `goodSurvivingGraphPairPred`, and the main pointwise deterministic target-gap,
      manuscript-loss-gap, and nat-valued `section4F` total-error shells have been refactored to
      use that wrapper. This removes another layer of repeated `GoodEventD` unpacking from the
      graph-pair frontier and isolates the remaining work to the genuinely graph-dependent
      three-pool collapse hypotheses themselves.
      The rounded deterministic target-gap bounds are now also exposed directly at graph-pair
      level via
      `goodSurvivingGraphPair_paperSection4OpenPairTargetNat_sub_ceil_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministicBounds`
      and
      `goodSurvivingGraphPair_paperSection4OpenPairTarget_sub_ceil_ten_mul_eps_mul_paperKSq_le_baseOpenPairSet_card_of_paperDeterministicBounds`,
      and the nearby pointwise deterministic target-gap / manuscript-loss-gap shells have been
      refactored through those helpers. This removes another repeated `GoodEventD` plus
      independence unpacking step from the RI graph-pair layer and keeps the remaining frontier
      focused on supplying the actual three-pool combinatorial inequalities.
      The raw nat-valued good-graph-pair witness-cap inequality
      `goodSurvivingGraphPair_section4SecondStageLossNat_add_witnessCaps_le_revealBudget_add_three_mul_partPairCount_LMS_add_huge_of_paperSection4Bound`
      is now exposed separately as well, with the casted helper
      `goodSurvivingGraphPair_section4SecondStageLossNat_add_witnessCaps_cast_le_totalError_of_LMS_totalError_of_paperSection4Bound`
      refactored through it. This keeps one more step of the fixed-embedding collapse in natural
      counting coordinates and makes the remaining three-pool/cardinality assembly closer to the
      literal manuscript inequalities.
      The full huge diagonal/cross package is now also exposed directly at graph-pair level via
      `goodSurvivingGraphPair_hugeContributionBounds_of_paperDeterministicBounds`, and the new
      pointwise bridge
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperRISILossGap_of_uniformPaperErrorBounds_of_paperSection4Bound_of_paperDeterministicHugeBounds`
      uses that helper to feed the reduced manuscript-loss-gap shell without requiring callers to
      provide the four huge inequalities separately. This further compresses the graph-pair
      interface toward the actual three-pool combinatorial hypotheses that still need to be proved.
      The new helper
      `goodSurvivingGraphPair_uniformPaperErrorBounds_of_paperDeterministicBounds`
      now bundles the reveal/L/M/S/huge-diagonal and huge-cross packages together in the exact
      eight-field order consumed by the reduced deterministic-target-gap and manuscript-loss-gap
      shells, and the pointwise theorem
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperDeterministicTargetGap_of_paperSection4Bound`
      has already been refactored through that bundled graph-pair interface. This trims one more
      layer of duplicated deterministic wrapper plumbing from the live RI frontier.
      The literal nat-valued graph-pair target-gap inequality is now also exposed directly in the
      reduced manuscript branch via
      `goodSurvivingGraphPair_section4LossLeTarget_of_paperRISILossGap_of_uniformPaperErrorBounds_of_paperDeterministicBounds`,
      and the pointwise theorem
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperRISILossGap_of_uniformPaperErrorBounds_of_paperSection4Bound_of_paperDeterministicBounds`
      has been refactored to route through that bridge before invoking the reduced deterministic
      target-gap endpoint. This sharpens the graph-pair frontier again: one of the key literal
      counting hypotheses needed for the fixed-embedding collapse now has a reusable deterministic
      wrapper of its own, leaving the genuinely graph-dependent three-pool cap/cardinality inputs
      as the remaining live obstruction.
      There is now also a graph-pair-native deterministic wrapper for the more general open-pair
      target-gap inequality with caller-supplied closed-pair error budgets:
      `goodSurvivingGraphPair_paperSection4OpenPairTargetNat_sub_openError_le_baseOpenPairSet_card_of_paperDeterministicBounds`.
      This keeps one more layer of the remaining collapse in literal natural-number error-budget
      coordinates before specializing to the manuscript `⌈10 ε₁ k²⌉` shell, which should make the
      eventual three-pool red/blue error assembly easier to feed into the existing RI endpoints.
      On top of that, the generic arbitrary-`openError` target-gap route is now also lifted
      through the deterministic graph-pair, fixed-embedding, and fixed-set shells via
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_targetGap_of_paperSection4Bound_of_paperDeterministicBounds`,
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_targetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`,
      and
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_targetGap_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`.
      This means later three-pool lemmas can now target the literal graph-pair hypotheses
      `hLossLeTarget` and `paperSection4OpenPairTargetNat - openError ≤ |O(I)|` directly, without
      restating the deterministic reveal/L/M/S/huge-diagonal contribution package each time.
      The reduced manuscript route now also has a matching split-closed-error interface:
      `goodSurvivingGraphPairProjectionChoiceMassBound_le_exp_of_paperRISILossGap_of_splitClosedErrorBounds_of_paperSection4Bound_of_paperDeterministicBounds`,
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperRISILossGap_of_splitClosedErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`,
      and
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperRISILossGap_of_splitClosedErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`.
      These wrappers combine the reduced manuscript `paperRISILossGap` shell with caller-supplied
      red/blue/open closed-pair error budgets whenever `openError ≤ ⌈10 ε₁ k²⌉`, so future
      three-pool lemmas can feed split red/blue closed-error estimates directly into the reduced
      manuscript route instead of first reassembling the intermediate target-gap theorem. The same
      split-error route now also reaches the explicit-good-mass endpoint via
      `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperRISILossGap_of_splitClosedErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass`,
      so there is no remaining wrapper gap above the fixed-set split-error interface: once the
      three-pool collapse produces the per-graph-pair manuscript loss-gap together with split
      red/blue/open closed-pair error bounds, that data can be pushed all the way to the final
      witness-existence theorem.
      The near-one branch now also reaches the reduced uniform-paper-error shell above graph-pair
      level: the new wrappers
      `constructionEmbeddingUniformWeight_mul_paperGoodSurvivingGraphPairMass_le_outerMass_mul_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_uniformPaperErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`
      and
      `paperConstructionMass_goodSurvivingIndepSetEventSet_le_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_uniformPaperErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds`
      convert the near-one graph-pair inequality to manuscript `paperRISILossGap` via
      `graphPair_paperRISILossGap_of_paperNearOneReal_of_two_div_le_loglog` and then reuse the
      lighter reduced manuscript shell rather than the heavier direct deterministic-bounds route.
      Together with the new extraction wrapper
      `exists_triangleFreeWithSmallIndepNum_of_paperChooseMulLe_sum_if_good_sectionExp_of_paperNearOneReal_of_two_div_le_loglog_of_uniformPaperErrorBounds_of_paperSection4Bound_of_embeddingImageBounds_of_paperDeterministicBounds_lt_explicitGoodMass`,
      this gives the near-one branch the same reduced fixed-embedding, fixed-set, and final
      witness-existence interface as the generic manuscript-loss-gap branch, leaving the actual
      three-pool combinatorial collapse as the remaining substantive blocker.
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
