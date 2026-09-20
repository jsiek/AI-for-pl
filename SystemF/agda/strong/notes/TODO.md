* DONE: Rename ValidRVar Ξ α to Ξ ∋ʳ α

* DONE: Rename Fresh α Δ to Δ ∌ʳ α

* DONE: Rename SameTy Γ A Γ′ B to Γ ⊢ A ≈ B ⊣ Γ′

* DONE: Delete ∀-payload-wf

* DONE: Add file charters to
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

  All twelve carry a `-- File Charter:` header in the house style of
  notes/RepresentationReductionExamples.agda, notes/CancelRShiftWall.agda
  and notes/RawRunProbe.agda: what the file holds, what does not belong
  here and where it lives instead, and the one or two invariants a reader
  must know first.  proof/Types.agda and proof/Ctx.agda got short
  charters too, since batch B created them and they are the private half
  of Types/Ctx.  TypeSubst.agda DOES still exist at strong/ and is still
  imported by All.agda, so it was chartered as well.

* DONE: Refactor CtxMorph

  Move stuff about RepCtx, TyCtx, and Ctxᵗ to Ctx.agda
  Keep suff about Change and CtxMorph in CtxMorph.agda

* DONE: Cleanup All.agda

  It should not import a file if that file is already indirectly imported
  from one of the imported files that lives in the strong/ directory.
  For example, most of the files in the proof/ directory should not be 
  directly imported from All.agda.
  Regarding the imports of files from the notes/ directory, 
  create a notes/All.agda file that imports all those files from
  the notes/ directory, and the main All.agda can import just the
  notes/All.agda file.
  of those files in the notes/ directory.
  
* DONE: Rename Var in Types.agda to TyVar

* DONE: In Terms, define Var to be ℕ and then change the term variable
  constructor's type:

data Term : Set where
  `_      : ℕ → Term

data Term : Set where
  `_      : Var → Term

  and similarly, change uses of ℕ for term variables to Var.
  
* DONE: Move lemmas from Types.agda to a new file proof/Types.agda.

* DONE: Move lemmas from Ctx.agda to a new file proof/Ctx.agda.
