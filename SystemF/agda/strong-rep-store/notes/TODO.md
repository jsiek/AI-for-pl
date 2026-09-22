* Replace the Boundary record with an alias to List Change.
  I think we can then replace Θ₁ ⋉ Θ₂ with Θ₁ ++ Θ₂.
  addLock0 should be inlined.

* Rename instantiate to inst.

* Rename dualBoundary to dual.

* Audit TermSubst.agda to determine which definitions are used
  by other public files (directly inside the strong-rep-store/ directory)
  versus which definitions are used only in private files (the proof/ directory).
  The definitions only used in private files should move
  to the proof/ directory, call it proof/TermSubst.agda
  This refactoring is needed so that this repo complies with the
  public/private mandate in the AGENTS.md file.

