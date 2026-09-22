* Audit the notes/notes.md file to make sure it is synchronized
  with the Agda development.

## Completed

### 2026-09-22

* Replace the Boundary record with an alias to List Change.
  `Boundary = List Change`; `Θ₁ ⋉ Θ₂` is now `Θ₁ ++ Θ₂` (`_⋉_` deleted)
  and `addLock0 Θ` is inlined as `Θ ++ (lock 0 0 ∷ [])` (`addLock0`
  deleted).  The two transport lemmas kept their statements under the
  names `snoc-lock0-interior-ren`/`snoc-lock0-conversion-ren`.

* Rename instantiate to inst.
  Also `inst-interior`, `inst-conversion`, `inst-boundarywf`.

* Rename dualBoundary to dual.
  With the alias, `dualBoundary Θ = dual Θ`, so the definition was
  deleted and every use now names Boundary.agda §2's `dual` directly.

* Audit TermSubst.agda to determine which definitions are used
  by other public files (directly inside the strong-rep-store/ directory)
  versus which definitions are used only in private files (the proof/ directory).
  The definitions only used in private files should move
  to the proof/ directory, call it proof/TermSubst.agda
  This refactoring is needed so that this repo complies with the
  public/private mandate in the AGENTS.md file.
  Public (TermSubst.agda, §1/§2/§5): `TyRename`/`ren²`/`ordinary`/
  `represent`, `idᵗ`, `underΛ-ren`, `renᶠ²`, `renᴮ²`, `renᴹ²`, `renᴹᴿ`,
  `↑ᴹ[_]`, `↑ᴮ[_]`, `Img`/`ivar`/`ival`, `imgTm`, `shiftᴵ`, `crossΛᴹ`,
  `⇑ᴵ`, `extᴵ`, `substᵐ`, `betaEnv`, `_[_∶_]ᵐ`.  Private
  (proof/TermSubst.agda, keeping the section numbers §1–§6): everything
  else.
