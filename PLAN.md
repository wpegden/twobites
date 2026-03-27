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
