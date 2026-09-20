* DONE: Rename ValidRVar Ξ α to Ξ ∋ʳ α

* DONE: Rename Fresh α Δ to Δ ∌ʳ α

* DONE: Rename SameTy Γ A Γ′ B to Γ ⊢ A ≈ B ⊣ Γ′

* DONE: Delete ∀-payload-wf

* Add file charters to 
  Types
  TypeSubst
  Ctx
  CtxMorph
  Terms
  TermSubst
  Reduction
  TypeCheck
  Eval
  Preservation
  Progress
  TypeSafety

* Refactor CtxMorph

  Move stuff about RepCtx, TyCtx, and Ctxᵗ to Ctx.agda
  Keep suff about Change and CtxMorph in CtxMorph.agda

* Cleanup All.agda

  It should not import a file if that file is already indirectly imported
  from one of the imported files that lives in the strong/ directory.
  For example, most of the files in the proof/ directory should not be 
  directly imported from All.agda.
  Regarding the imports of files from the notes/ directory, 
  create a notes/All.agda file that imports all those files from
  the notes/ directory, and the main All.agda can import just the notes/All.agda file.
  of those files in the notes/ directory.
  
* DONE: Rename Var in Types.agda to TyVar

* DONE: In Terms, define Var to be ℕ and then change the term variable
  constructor's type:

data Term : Set where
  `_      : ℕ → Term

data Term : Set where
  `_      : Var → Term

  and similarly, change uses of ℕ for term variables to Var.
  
* Move lemmas from Types.agda to a new file proof/Types.agda.

* Move lemmas from Ctx.agda to a new file proof/Ctx.agda.

