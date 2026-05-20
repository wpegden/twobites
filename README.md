# Two Bites Tablet

This directory contains a Lean formalization of the graph main theorem from the
arXiv paper `2510.19718`, "Improving R(3,k) in just two bites".  The local paper
source used as reference is `paper/reference.tex`.

The tablet was produced by the Trellis autoformalization system while Trellis
itself was still under active development.  In the course of this, the
autoformalization reached a state where it was nearly done but with a structure
that was incompatible with newer Trellis features (allowing things like
backtracking, etc.).  For that reason, this copy was handfixed: a human
operator asked Codex to complete the repair without supplying
mathematical content, Lean proof steps, or formalization-specific hints beyond
directing it to follow the paper-faithful route that the automated system had
identified.  The prompts from that fixing phase are listed in
`HANDFIX_PROMPTS.md`.  The last manual process did not change the Lean
declarations that determine the statements of the public theorems:
`MainIndependence`, `MainRamseyLowerBound`, `IndependenceNumberLess`,
`RamseyWitness`, or `RamseyScale`.

Paper correspondence:

- Paper Theorem `main` corresponds to tablet node `MainIndependence`.  This
  node states the existence, for all sufficiently large `n`, of a simple graph
  `G : SimpleGraph (Fin n)` with `G.CliqueFree 3` and
  `IndependenceNumberLess G ((1 + ε) * sqrt (n * log n))`.  The additional
  tablet semantic dependency in this statement is `IndependenceNumberLess`.
- Paper Theorem `main2` corresponds to tablet node `MainRamseyLowerBound`.
  This node states the lower bound in witness form: for every `η > 0` and all
  sufficiently large `k`, there is an `N` with `RamseyWitness N k` and
  `((1 / 2) - η) * RamseyScale k <= N`.  The additional tablet semantic
  dependencies in this statement are `RamseyWitness` and `RamseyScale`.

Here "semantic dependency" means the narrow statement surface: the
tablet-local Lean definitions needed to interpret the theorem statements.

Line-count estimate, using the first commit in this repository as the Trellis
baseline and counting `Tablet/*.lean`, `Tablet/*.tex`, `Tablet/INDEX.md`, and
`Tablet/README.md`:

- Trellis-generated baseline: about 102,838 LOC
  (`65,200` Lean, `36,654` TeX, `984` Markdown).
- Handfix/manual follow-up after that baseline: about 7,965 added LOC and 361
  deleted LOC, for a net increase of about 7,604 LOC
  (`7,645` Lean, `289` TeX, `31` Markdown added).
- Current tablet source total: about 110,442 LOC.

This is an estimate of source provenance from the git baseline.  It does not
count explanatory files such as this README.

Repository layout:

- `Tablet/`: Lean nodes and matching TeX proof sketches.
- `Tablet/INDEX.md`: node index and dependency table.
- `paper/reference.tex`: flattened source of the reference paper used during
  formalization.
- `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json`: Lean project
  configuration.
