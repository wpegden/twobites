# Tasks

<!-- SUPERVISOR_TASKS:START -->
## Supervisor Tasks
- [ ] Read `repo/paper/reference.tex` carefully from start to finish.
- [ ] Verify the mathematics of each proof, not just the statements.
- [ ] Record corrections, clarifications, and dependencies in `PAPERNOTES.md`.
- [ ] Report `STUCK` only for a genuine gap or incorrect statement after serious repair attempts.
<!-- SUPERVISOR_TASKS:END -->

## Worker Tasks
- [ ] Create `repo/PLAN.md` for the main-results formalization (Sections 2-4 and the appendix inequalities they use).
- [ ] Extract Lean-facing definitions and theorem statements for the checked main proof into `PaperDefinitions.lean` and `PaperTheorems.lean`.

## Completed
- [x] Read `repo/paper/reference.tex` end to end, with the paper-check focused on the main-result sections.
- [x] Check the proof chain for Theorem `main`, including Lemmas `lem:fiber_and_degree`, `lem:large`, `lem:med`, `lem:small`, `lem:huge`, `lem:RISI`, and `lem:RI`.
- [x] Record corrections, hidden assumptions, and proof clarifications in `repo/PAPERNOTES.md`.
- [x] Confirm that no genuine gap was found in the main-result argument; the hypergraph section is only a proof sketch and remains out of scope for this formalization project.
