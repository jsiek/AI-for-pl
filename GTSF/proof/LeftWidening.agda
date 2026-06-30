module proof.LeftWidening where

-- File Charter:
--   * Mechanized work on the GTSF Left Widening Lemma used by
--     `proof.Catchup`.
--   * The target statement matches the current `left-widening-lemma`
--     postulate in `proof.Catchup`.
--   * The old statement is kept as `LeftWideningWithoutNo•` because it was
--     false; the current statement adds the missing source/result `No•`
--     invariants.
--   * The proof search is kept here to avoid obscuring the larger catchup
--     proof and to make failed strategies explicit.
--
-- Strategy log:
--   * Directly reusing `cast+⊒` works only when the dual cast is inert, since
--     then `V ⟨ - t ⟩` is already a value.  This should cover function,
--     universal, and tag/untag cases.  The raw `unseal` and `inst` forms also
--     have inert duals, and are included below as zero-step edge cases, but the
--     `r ≈ t ⨾ⁿ p` premise carries a narrowing proof for `t`, so the reachable
--     hard heads are still `seal`, `s ︔ seal`, `gen`, and sequence variants.
--     The function, universal, and tag/untag forms below are mechanized as
--     zero-step branches through `left-widening-inert`.
--   * The exact identity branch, where the result index is syntactically `p`,
--     is mechanized below by one `β-id` step.  The general identity branch
--     still requires turning the endpoint-equivalence premise
--     `r ≈ id A ⨾ⁿ p` into a term-narrowing derivation at `r`.  A broad
--     `termNarrowing-resp-≈` principle was checked in
--     `proof.LeftSealNarrowingInversion`, but it is too strong as stated:
--     constructors such as `⊒blame` require a cast-like index, not only an
--     endpoint-equivalent narrowing.
--     A candidate counterexample using
--     `(unseal α (＇ α)) ↦ (seal (＇ α) α)` also fails: the store invariant
--     requires a seal store entry `(α , A)` to have `WfTy α A`, so the
--     self-reference `A = ＇ α` is not well formed.
--   * The seal/unseal and inst/gen branches are not mere congruence cases:
--     the paper handles them with right-seal/nu-specific reasoning.  These
--     branches are the first place to look for either a missing algebraic
--     lemma or a counterexample.
--   * Counterexample found in the inst/gen branch: the statement assumes only
--     `Value V`, but the `ν-step` after `β-inst` additionally needs
--     `No• V`.
--     A lambda value can hide a runtime bullet in its body, so the reduction
--     reaches a stuck non-value `ν ★ V c`.
--   * After main added the `RuntimeOK`/`No•` premises, this particular
--     counterexample is blocked: `badPoly-no-No•` proves the bad value cannot
--     satisfy the `No• V` premise, and `badPoly-no-RuntimeOK` proves the same
--     term cannot arise from a `RuntimeOK` source at value shape.
--   * The guarded sibling of that counterexample is positive:
--     `left-widening-ex4-gen` follows the Example 4 `gen` branch through
--     `β-inst`, `ν-step`, and `β-Λ•`.  The bookkeeping mismatch it exposed is
--     that emitted `bind` steps raise `Δ`; for now the small Example 4
--     derivation is replayed at the raised context.  A general `gen` proof
--     should use a reusable term-narrowing type-context weakening lemma.
--     The common operational spine is now factored as
--     `left-widening-gen-reduction`, and `left-widening-gen-prefix` lets later
--     reductions from the exposed body cast be prefixed by that spine.  This
--     removes the old counterexample's only stuck step.  The wrapper
--     `left-widening-gen-spine-package` also factors the emitted-store
--     existential bookkeeping once a relation for the exposed body cast is
--     available.  These lemmas do not by themselves build that final
--     term-narrowing relation or prove the result is a value when the exposed
--     body cast is active rather than inert.
--     The relation-side wrappers
--     The `⊒Λ` and `⊒⟨ν⟩` relation-side wrappers cover the two
--     term-narrowing constructors that can consume an inert exposed body cast;
--     Example 4 now goes through the `⊒Λ` wrapper.
--     For sequence variants, `dual-seq` and `left-widening-seq-prefix` factor
--     only the initial `β-seq` step; the remaining recursive catchup/left-
--     widening obligations are deliberately left explicit.
--     `left-widening-seq-inner-reduction` adds the emitted-store action on
--     the outer dual cast while the inner dual cast reduces, and
--     `left-widening-seq-package` packages the two-stage reduction plus final
--     relation witness.  A full sequence branch still needs recursive
--     left-widening evidence for both component casts and the composition
--     algebra relating their indices.
--     The reusable `left-widening-compose-witnesses` proof factors the
--     store/relation transport needed to combine two emitted source-only
--     prefixes, following the existing algebra in `proof.Catchup`.
--     `left-widening-seq-compose-package` combines that transport with the
--     sequence reduction package, so the future sequence branch can focus on
--     producing the two recursive component witnesses.
--   * A direct suc-only induction for that weakening lemma is the wrong
--     formulation: under `Λ`, the body is renamed by `extᵗ suc`, not plain
--     `suc`.  The reusable pieces started in `proof.TermNarrowingProperties`
--     (`shift-var`, `shift-blame`, `shift-ƛ`, `shift-·`) should therefore be
--     generalized to a parallel type-renaming theorem with an explicit
--     store-narrowing renamer and mode-renamer premise.
--     Current progress in that direction includes `renameStoreNrw`,
--     `renameCtxNrw`, `rename-var`, `rename-blame`, `rename-ƛ`, `rename-·`,
--     `rename-Λ`, `rename-⊒Λ`, `rename-⊒⟨ν⟩`, `rename-α⊒α`,
--     `rename-⊒α`, `rename-ν⊒ν`, `rename-⊒ν`, `rename-ν⊒`, `rename-κ`,
--     and `rename-⊕`.
--   * Trying to make that renaming theorem fully arbitrary runs into the
--     composition witnesses used by cast constructors: their internal mode
--     environment is existential, and `TyRenameWf` alone permits renamings
--     that collapse or reorder store variables.  Such renamings do not
--     preserve the `StoreDetWf` uniqueness/older-variable invariants needed by
--     composition determinacy.  The surviving algebraic shape is therefore:
--     carry an `AllModeRename` witness for existential mode environments and
--     an explicit `StoreDetWf` transport for the renaming.  This is now
--     mechanized in `proof.TermNarrowingProperties` as `narrow-renameᵗ-any`,
--     `⊒ˢ-rename`, `≈ⁿ-rename`, `compose-leftⁿ-rename`,
--     and `compose-rightⁿ-rename`.
--     A usable `StoreDetWf` transport has to assume both order preservation
--     and injectivity.  That refinement is mechanized as `TyRenameStrict`,
--     `StoreDetWf-rename`, and the binder-preserving `StoreDetWf-ext-suc`,
--     with direct `≈ⁿ-ext-suc`, `compose-leftⁿ-ext-suc`, and
--     `compose-rightⁿ-ext-suc` corollaries.
--     The `suc`-specific cast cases are still mechanized there via `≈ⁿ-⇑ˢ`,
--     `compose-leftⁿ-⇑ˢ`, `compose-rightⁿ-⇑ˢ`, `shift-⊒cast+`,
--     `shift-⊒cast-`, `shift-cast+⊒`, and `shift-cast-⊒`.
--   * The cast constructors can also be renamed once the composition
--     side-condition has already been transported.  The constructor-level
--     lemmas `rename-⊒cast+`, `rename-⊒cast-`, `rename-cast+⊒`, and
--     `rename-cast-⊒`, plus their `-det` wrappers, avoid rebuilding the
--     dual-cast and composition transports by hand in the eventual induction.
--   * The `ν` renaming helpers are intentionally stated in constructor-native
--     form rather than as pointwise renamings of whole `ν` terms: `ν` renames
--     its term body with `ρ`, while the narrowing premises under the fresh
--     store entry need `extᵗ ρ`.  Keeping that mismatch explicit avoids a
--     false "obvious" helper.
--   * The bindery store constructors need the same constructor-native shape:
--     `rename-extend` and `rename-split` are now mechanized in
--     `proof.TermNarrowingProperties`, using the parallel type-renaming/opening
--     commutation lemmas for terms and coercions.
--   * A full pointwise theorem
--     `M ⊒ M′ ∶ p -> renameᵗᵐ ρ M ⊒ renameᵗᵐ ρ M′ ∶ renameᶜ ρ p`
--     is too strong for the current relation.  The `⊒⟨ν⟩` constructor exposes
--     the mismatch: its recursive premise renames the target value under
--     `extᵗ ρ`, but pointwise renaming of the conclusion
--     `V′ ⟨ gen A s ⟩` renames `V′` under plain `ρ`.  The eventual reusable
--     theorem needs a proof-directed target translation or a more local
--     statement for the gen/nu cases, not ordinary whole-term renaming.
--     The useful local support lemmas from this failed attempt are now in
--     `proof.CoercionProperties` and `proof.NuTermProperties`:
--     `renameᶜ-reflects-Inert`, `renameᵗᵐ-reflects-Value`, and
--     `renameᵗᵐ-reflects-No•`.  They should help peel `⇑ᵗᵐ` values and
--     no-bullet evidence in the shifted-source inversion lemmas.
--     `proof.ReductionProperties` now lifts those to emitted store-change
--     actions as `applyTerms-reflects-Value`, `applyTerms-reflects-No•`,
--     `applyTermsUnderTyBinders-reflects-Value`, and
--     `applyTermsUnderTyBinders-reflects-No•`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; z<s)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import NarrowingExamples
  using
    ( ex1-line272-≈
    ; forall-id-var0-fun-cast
    ; id★-cast
    ; id★-store-narrowing
    ; id-var0-cast
    ; id-var0-fun-cast
    ; id-var0-fun-narrowingᵐ
    ; poly-fun-cast
    ; star-seal-fun
    ; star-seal-fun-narrowingᵐ
    ; var0-fun
    ; var0-fun-cast
    ; var0-fun-narrowing
    ; wf-var-fun-endpoints
    )
open import proof.NarrowWidenProperties using (StoreDetWf; ⊒ˢ-empty-anyᵗ)
open import proof.CatchupStore
  using
    ( combineStoreNrw
    ; combineStoreNrw-assoc
    ; combineStoreNrw-empty-⊒ˢ
    ; combineStoreNrw-applyStores
    )
open import proof.ReductionProperties
  using
    ( applyCoercions
    ; applyCoercions-++
    ; applyTerms-++
    ; applyTyCtxs-++
    ; cast-dual-↠
    ; ↠-trans
    )
open import proof.NuTermProperties
  using (open0-ext-suc-cancelᵐ; renameᵗᵐ-preserves-Value)
open import proof.CoercionProperties using (renameᶜ-preserves-Inert)

dual-untag-inert :
  ∀ {G} →
  Ground G →
  Inert (- (G ？))
dual-untag-inert (＇ α) = (＇ α) !
dual-untag-inert (‵ ι) = (‵ ι) !
dual-untag-inert ★⇒★ = (★ ⇒ ★) !

dual-unseal-inert :
  ∀ {α A} →
  Inert (- unseal α A)
dual-unseal-inert {α = α} {A = A} = seal A α

dual-inst-inert :
  ∀ {B c} →
  Inert (- inst B c)
dual-inst-inert {B = B} {c = c} = gen B (dual (instᵃ normalᵃ) c)

dual-gen :
  ∀ A c →
  - (gen A c) ≡ inst A (dual (genᵃ normalᵃ) c)
dual-gen A c = refl

dual-seq :
  ∀ c d →
  - (c ︔ d) ≡ (- d) ︔ (- c)
dual-seq c d = refl

LeftWideningWithoutNo• : Set₁
LeftWideningWithoutNo• =
  ∀ {Δ σ V V′ p r t A B C D} →
  Value V →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    (V ⟨ - t ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r

LeftWidening : Set₁
LeftWidening =
  ∀ {Δ σ V V′ p r t A B C D} →
  Value V →
  No• V →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (V ⟨ - t ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r

left-widening-inert :
  ∀ {Δ σ V V′ p r t A B C D} →
  Inert (- t) →
  Value V →
  No• V →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (V ⟨ - t ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r
left-widening-inert {Δ = Δ} {σ = σ} {V = V} {V′ = V′}
    {p = p} {r = r} {t = t} inert-t vV noV pᶜ r≈t⨟p V⊒V′ =
  [] , V ⟨ - t ⟩ , Δ , [] , [] , [] ,
  vV ⟨ inert-t ⟩ ,
  no•-⟨⟩ noV ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  cast+⊒ pᶜ r≈t⨟p V⊒V′

left-widening-fun :
  ∀ {Δ σ V V′ p r s t A B C D} →
  Value V →
  No• V →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ (s ↦ t) ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (V ⟨ - (s ↦ t) ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r
left-widening-fun {s = s} {t = t} vV noV pᶜ r≈t⨟p V⊒V′ =
  left-widening-inert ((- s) ↦ (- t)) vV noV pᶜ r≈t⨟p V⊒V′

left-widening-∀ :
  ∀ {Δ σ V V′ p r s A B C D} →
  Value V →
  No• V →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ (`∀ s) ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (V ⟨ - (`∀ s) ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r
left-widening-∀ {s = s} vV noV pᶜ r≈t⨟p V⊒V′ =
  left-widening-inert (`∀ (dual (extᵃ normalᵃ) s))
    vV noV pᶜ r≈t⨟p V⊒V′

left-widening-untag :
  ∀ {Δ σ V V′ p r G A B C D} →
  Ground G →
  Value V →
  No• V →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ (G ？) ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (V ⟨ - (G ？) ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r
left-widening-untag gG vV noV pᶜ r≈t⨟p V⊒V′ =
  left-widening-inert (dual-untag-inert gG)
    vV noV pᶜ r≈t⨟p V⊒V′

left-widening-unseal :
  ∀ {Δ σ V V′ p r α A A₀ B C D} →
  Value V →
  No• V →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ unseal α A ⨾ⁿ p ∶ A₀ ⊒ B →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (V ⟨ - unseal α A ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r
left-widening-unseal {α = α} {A = A} vV noV pᶜ r≈t⨟p V⊒V′ =
  left-widening-inert (dual-unseal-inert {α = α} {A = A})
    vV noV pᶜ r≈t⨟p V⊒V′

left-widening-inst :
  ∀ {Δ σ V V′ p r B c A₀ B₀ C D} →
  Value V →
  No• V →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ⊢ r ≈ inst B c ⨾ⁿ p ∶ A₀ ⊒ B₀ →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (V ⟨ - inst B c ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r
left-widening-inst {B = B} {c = c} vV noV pᶜ r≈t⨟p V⊒V′ =
  left-widening-inert (dual-inst-inert {B = B} {c = c})
    vV noV pᶜ r≈t⨟p V⊒V′

left-widening-seq-reduction :
  ∀ {c d V} →
  Value V →
  V ⟨ - (c ︔ d) ⟩
    —↠[ keep ∷ [] ]
    (V ⟨ - d ⟩) ⟨ - c ⟩
left-widening-seq-reduction {c = c} {d = d} vV
    rewrite dual-seq c d =
  ↠-step (pure-step (β-seq vV)) ↠-refl

left-widening-seq-prefix :
  ∀ {c d V χs W} →
  Value V →
  (V ⟨ - d ⟩) ⟨ - c ⟩ —↠[ χs ] W →
  V ⟨ - (c ︔ d) ⟩ —↠[ keep ∷ χs ] W
left-widening-seq-prefix {c = c} {d = d} vV V↠W =
  ↠-trans (left-widening-seq-reduction {c = c} {d = d} vV) V↠W

left-widening-seq-inner-reduction :
  ∀ {c d V χs W} →
  Value V →
  V ⟨ - d ⟩ —↠[ χs ] W →
  V ⟨ - (c ︔ d) ⟩ —↠[ keep ∷ χs ] W ⟨ - applyCoercions χs c ⟩
left-widening-seq-inner-reduction {c = c} {d = d} vV Vd↠W =
  left-widening-seq-prefix {c = c} {d = d} vV
    (cast-dual-↠ {c = c} Vd↠W)

left-widening-seq-package :
  ∀ {Δ σ V V′ c d r χs χs′ W U π} →
  Value V →
  V ⟨ - d ⟩ —↠[ χs ] W →
  W ⟨ - applyCoercions χs c ⟩ —↠[ χs′ ] U →
  Value U →
  No• U →
  applyTyCtxs (keep ∷ (χs ++ χs′)) Δ
    ⊢ π ꞉ applyStores (keep ∷ (χs ++ χs′)) []
      ⊒ˢ applyStore keep [] →
  applyTyCtxs (keep ∷ (χs ++ χs′)) Δ ∣ combineStoreNrw π σ ∣ []
    ⊢ U ⊒ applyTerms (keep ∷ (χs ++ χs′)) V′
      ∶ applyCoercions (keep ∷ (χs ++ χs′)) r →
  ∃[ χs″ ] ∃[ W′ ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π′ ]
    Value W′ ×
    No• W′ ×
    (V ⟨ - (c ︔ d) ⟩ —↠[ χs″ ] W′) ×
    (Δ′ ≡ applyTyCtxs χs″ Δ) ×
    (Π ≡ applyStores χs″ []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π′ ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs″ V′ ∶ applyCoercions χs″ r
left-widening-seq-package {Δ = Δ} {σ = σ} {V = V}
    {c = c} {d = d} {χs = χs} {χs′ = χs′} {U = U} {π = π}
    vV Vd↠W Wc↠U vU noU π⊒ U⊒V′ =
  keep ∷ (χs ++ χs′) ,
  U ,
  applyTyCtxs (keep ∷ (χs ++ χs′)) Δ ,
  applyStores (keep ∷ (χs ++ χs′)) [] ,
  applyStore keep [] ,
  π ,
  vU ,
  noU ,
  ↠-trans (left-widening-seq-inner-reduction {c = c} {d = d} vV Vd↠W)
          Wc↠U ,
  refl ,
  refl ,
  refl ,
  π⊒ ,
  U⊒V′

left-widening-compose-witnesses :
  ∀ {Δ σ V′ r χs₁ χs₂ W₂ Δ₁ Δ₂ Π₁ Π₁′}
    {Π₂ Π₂′ π₁ π₂} →
  Δ₁ ≡ applyTyCtxs χs₁ Δ →
  Π₁ ≡ applyStores χs₁ [] →
  Π₁′ ≡ applyStore keep [] →
  Δ₁ ⊢ π₁ ꞉ Π₁ ⊒ˢ Π₁′ →
  Δ₂ ≡ applyTyCtxs χs₂ Δ₁ →
  Π₂ ≡ applyStores χs₂ [] →
  Π₂′ ≡ applyStore keep [] →
  Δ₂ ⊢ π₂ ꞉ Π₂ ⊒ˢ Π₂′ →
  Δ₂ ∣ combineStoreNrw π₂ (combineStoreNrw π₁ σ) ∣ []
    ⊢ W₂ ⊒ applyTerms χs₂ (applyTerms χs₁ V′)
      ∶ applyCoercions χs₂ (applyCoercions χs₁ r) →
  ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    (Δ′ ≡ applyTyCtxs (χs₁ ++ χs₂) Δ) ×
    (Π ≡ applyStores (χs₁ ++ χs₂) []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W₂ ⊒ applyTerms (χs₁ ++ χs₂) V′
        ∶ applyCoercions (χs₁ ++ χs₂) r
left-widening-compose-witnesses {Δ = Δ} {σ = σ} {V′ = V′}
    {r = r} {χs₁ = χs₁} {χs₂ = χs₂} {W₂ = W₂}
    {Δ₁ = Δ₁} {Δ₂ = Δ₂} {π₁ = π₁} {π₂ = π₂}
    Δ₁≡ Π₁≡ Π₁′≡ π₁⊒
    Δ₂≡ Π₂≡ Π₂′≡ π₂⊒ W₂⊒V′ =
  Δ₂ ,
  srcStoreⁿ (combineStoreNrw π₂ π₁) ,
  [] ,
  combineStoreNrw π₂ π₁ ,
  trans Δ₂≡
    (trans (cong (applyTyCtxs χs₂) Δ₁≡)
      (sym (applyTyCtxs-++ χs₁ χs₂ Δ))) ,
  combineStoreNrw-applyStores
    {χs₂ = χs₂} {χs₁ = χs₁}
    π₂⊒ Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡ ,
  refl ,
  combineStoreNrw-empty-⊒ˢ
    (subst (λ Π′ → _ ⊢ π₂ ꞉ _ ⊒ˢ Π′) Π₂′≡ π₂⊒)
    (⊒ˢ-empty-anyᵗ Δ₂
      (subst
        (λ Π′ → _ ⊢ π₁ ꞉ _ ⊒ˢ Π′)
        Π₁′≡
        π₁⊒)) ,
  subst
    (λ c → Δ₂ ∣ combineStoreNrw (combineStoreNrw π₂ π₁) σ ∣ []
      ⊢ W₂ ⊒ applyTerms (χs₁ ++ χs₂) V′ ∶ c)
    (sym (applyCoercions-++ χs₁ χs₂ r))
    (subst
      (λ T →
        Δ₂ ∣ combineStoreNrw (combineStoreNrw π₂ π₁) σ ∣ []
          ⊢ W₂ ⊒ T ∶ applyCoercions χs₂ (applyCoercions χs₁ r))
      (sym (applyTerms-++ χs₁ χs₂ V′))
      (subst
        (λ τ → Δ₂ ∣ τ ∣ [] ⊢ W₂
          ⊒ applyTerms χs₂ (applyTerms χs₁ V′) ∶
            applyCoercions χs₂ (applyCoercions χs₁ r))
        (sym (combineStoreNrw-assoc π₂ π₁ σ))
        W₂⊒V′))

left-widening-seq-compose-package :
  ∀ {Δ σ V V′ c d r χs₁ χs₂ W U
      Δ₁ Δ₂ Π₁ Π₁′ Π₂ Π₂′ π₁ π₂} →
  Value V →
  V ⟨ - d ⟩ —↠[ χs₁ ] W →
  W ⟨ - applyCoercions χs₁ c ⟩ —↠[ χs₂ ] U →
  Value U →
  No• U →
  Δ₁ ≡ applyTyCtxs χs₁ Δ →
  Π₁ ≡ applyStores χs₁ [] →
  Π₁′ ≡ applyStore keep [] →
  Δ₁ ⊢ π₁ ꞉ Π₁ ⊒ˢ Π₁′ →
  Δ₂ ≡ applyTyCtxs χs₂ Δ₁ →
  Π₂ ≡ applyStores χs₂ [] →
  Π₂′ ≡ applyStore keep [] →
  Δ₂ ⊢ π₂ ꞉ Π₂ ⊒ˢ Π₂′ →
  Δ₂ ∣ combineStoreNrw π₂ (combineStoreNrw π₁ σ) ∣ []
    ⊢ U ⊒ applyTerms χs₂ (applyTerms χs₁ V′)
      ∶ applyCoercions χs₂ (applyCoercions χs₁ r) →
  ∃[ χs″ ] ∃[ W′ ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W′ ×
    No• W′ ×
    (V ⟨ - (c ︔ d) ⟩ —↠[ χs″ ] W′) ×
    (Δ′ ≡ applyTyCtxs χs″ Δ) ×
    (Π ≡ applyStores χs″ []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W′ ⊒ applyTerms χs″ V′ ∶ applyCoercions χs″ r
left-widening-seq-compose-package {Δ = Δ} {σ = σ} {V = V}
    {V′ = V′} {c = c} {d = d} {r = r} {χs₁ = χs₁}
    {χs₂ = χs₂} {W = W} {U = U} vV Vd↠W Wc↠U vU noU
    Δ₁≡ Π₁≡ Π₁′≡ π₁⊒
    Δ₂≡ Π₂≡ Π₂′≡ π₂⊒ U⊒V′ =
  let
    composed =
      left-widening-compose-witnesses
        {Δ = Δ} {σ = σ} {V′ = V′} {r = r}
        {χs₁ = χs₁} {χs₂ = χs₂} {W₂ = U}
        Δ₁≡ Π₁≡ Π₁′≡ π₁⊒
        Δ₂≡ Π₂≡ Π₂′≡ π₂⊒ U⊒V′

    Δ′ , Π , Π′ , π ,
      Δ′≡ , Π≡ , Π′≡ , π⊒ , U⊒V′′ =
      composed
  in
  keep ∷ (χs₁ ++ χs₂) ,
  U ,
  Δ′ ,
  Π ,
  Π′ ,
  π ,
  vU ,
  noU ,
  ↠-trans
    (left-widening-seq-inner-reduction {c = c} {d = d} vV Vd↠W)
    Wc↠U ,
  Δ′≡ ,
  Π≡ ,
  Π′≡ ,
  π⊒ ,
  U⊒V′′

left-widening-gen-reduction :
  ∀ {A c V} →
  Value V →
  No• V →
  (Λ V) ⟨ - (gen A c) ⟩
    —↠[ keep ∷ bind ★ ∷ keep ∷ [] ]
    V ⟨ dual (genᵃ normalᵃ) c ⟩
left-widening-gen-reduction {A = A} {c = c} {V = V} vV noV
    rewrite dual-gen A c =
  subst
    (λ T →
      (Λ V) ⟨ inst A (dual (genᵃ normalᵃ) c) ⟩
        —↠[ keep ∷ bind ★ ∷ keep ∷ [] ]
        T ⟨ dual (genᵃ normalᵃ) c ⟩)
    (open0-ext-suc-cancelᵐ V)
    (↠-step
      (pure-step
        (β-inst {V = Λ V} {B = A} {c = dual (genᵃ normalᵃ) c}
          (Λ vV)))
      (↠-step (ν-step (Λ vV) (no•-Λ noV))
        (↠-step
          (ξ-⟨⟩
            (pure-step
              (β-Λ•
                (renameᵗᵐ-preserves-Value (extᵗ suc) vV))))
          ↠-refl)))

left-widening-gen-prefix :
  ∀ {A c V χs W} →
  Value V →
  No• V →
  V ⟨ dual (genᵃ normalᵃ) c ⟩ —↠[ χs ] W →
  (Λ V) ⟨ - (gen A c) ⟩
    —↠[ keep ∷ bind ★ ∷ keep ∷ χs ]
    W
left-widening-gen-prefix {A = A} {c = c} vV noV V↠W =
  ↠-trans (left-widening-gen-reduction {A = A} {c = c} vV noV) V↠W

left-widening-gen-spine-package :
  ∀ {Δ σ N V′ A c r} →
  Value N →
  No• N →
  Value (N ⟨ dual (genᵃ normalᵃ) c ⟩) →
  No• (N ⟨ dual (genᵃ normalᵃ) c ⟩) →
  suc Δ ∣ combineStoreNrw ((⊒ zero ꞉=☆) ∷ []) σ ∣ []
    ⊢ N ⟨ dual (genᵃ normalᵃ) c ⟩
      ⊒ applyTerms (keep ∷ bind ★ ∷ keep ∷ []) V′
      ∶ applyCoercions (keep ∷ bind ★ ∷ keep ∷ []) r →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    ((Λ N) ⟨ - (gen A c) ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r
left-widening-gen-spine-package {Δ = Δ} {σ = σ} {N = N}
    {A = A} {c = c} vN noN vW noW W⊒V′ =
  keep ∷ bind ★ ∷ keep ∷ [] ,
  N ⟨ dual (genᵃ normalᵃ) c ⟩ ,
  suc Δ ,
  (zero , ★) ∷ [] ,
  [] ,
  (⊒ zero ꞉=☆) ∷ [] ,
  vW ,
  noW ,
  left-widening-gen-reduction {A = A} {c = c} vN noN ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-left ⊒ˢ-nil ,
  W⊒V′

left-widening-gen-inert-⊒Λ-package :
  ∀ {Δ σ N V′ A B c} →
  Value N →
  No• N →
  Inert (dual (genᵃ normalᵃ) c) →
  suc Δ ∣ srcStoreⁿ (combineStoreNrw ((⊒ zero ꞉=☆) ∷ []) σ)
    ⊢ gen (⇑ᵗ A) (renameᶜ (extᵗ suc) c) ∶ᶜ ⇑ᵗ A ⊒ `∀ B →
  suc (suc Δ) ∣ (zero ꞉= ★ ⊒)
      ∷ ⇑ˢ (combineStoreNrw ((⊒ zero ꞉=☆) ∷ []) σ) ∣ []
    ⊢ ⇑ᵗᵐ (N ⟨ dual (genᵃ normalᵃ) c ⟩)
      ⊒ renameᵗᵐ (extᵗ suc) V′
      ∶ renameᶜ (extᵗ suc) c →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    ((Λ N) ⟨ - (gen A c) ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs (Λ V′)
        ∶ applyCoercions χs (gen A c)
left-widening-gen-inert-⊒Λ-package {Δ = Δ} {σ = σ} {N = N}
    {V′ = V′} {A = A} {c = c} vN noN inert-c genᶜ body⊒ =
  left-widening-gen-spine-package
    {Δ = Δ} {σ = σ} {N = N} {V′ = Λ V′}
    {A = A} {c = c} {r = gen A c}
    vN
    noN
    (vN ⟨ inert-c ⟩)
    (no•-⟨⟩ noN)
    (⊒Λ genᶜ body⊒)

left-widening-gen-inert-⊒⟨ν⟩-package :
  ∀ {Δ σ N V′ A B c s} →
  Value N →
  No• N →
  Inert (dual (genᵃ normalᵃ) c) →
  Inert s →
  suc Δ ∣ srcStoreⁿ (combineStoreNrw ((⊒ zero ꞉=☆) ∷ []) σ)
    ⊢ gen (⇑ᵗ A) (renameᶜ (extᵗ suc) c) ∶ᶜ ⇑ᵗ A ⊒ `∀ B →
  suc (suc Δ) ∣ (zero ꞉= ★ ⊒)
      ∷ ⇑ˢ (combineStoreNrw ((⊒ zero ꞉=☆) ∷ []) σ) ∣ []
    ⊢ ⇑ᵗᵐ (N ⟨ dual (genᵃ normalᵃ) c ⟩)
      ⊒ ⇑ᵗᵐ V′ ⟨ renameᶜ (extᵗ suc) s ⟩
      ∶ renameᶜ (extᵗ suc) c →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    ((Λ N) ⟨ - (gen A c) ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs (V′ ⟨ gen A s ⟩)
        ∶ applyCoercions χs (gen A c)
left-widening-gen-inert-⊒⟨ν⟩-package
    {Δ = Δ} {σ = σ} {N = N} {V′ = V′} {A = A} {c = c}
    {s = s} vN noN inert-c inert-s genᶜ body⊒ =
  left-widening-gen-spine-package
    {Δ = Δ} {σ = σ} {N = N} {V′ = V′ ⟨ gen A s ⟩}
    {A = A} {c = c} {r = gen A c}
    vN
    noN
    (vN ⟨ inert-c ⟩)
    (no•-⟨⟩ noN)
    (⊒⟨ν⟩ genᶜ
      (renameᶜ-preserves-Inert (extᵗ suc) inert-s)
      body⊒)

left-widening-id-exact :
  ∀ {Δ σ V V′ p A C D} →
  Value V →
  No• V →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
  Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (V ⟨ - id A ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p
left-widening-id-exact {Δ = Δ} {σ = σ} {V = V}
    vV noV pᶜ V⊒V′ =
  keep ∷ [] , V , Δ , [] , [] , [] ,
  vV ,
  noV ,
  ↠-step (pure-step (β-id vV)) ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  V⊒V′

badBody : Term
badBody = ƛ ((` zero) •)

badBody′ : Term
badBody′ = ƛ blame

badPoly : Term
badPoly = Λ badBody

badPoly′ : Term
badPoly′ = Λ badBody′

badBody-value : Value badBody
badBody-value = ƛ ((` zero) •)

badPoly-value : Value badPoly
badPoly-value = Λ badBody-value

badBody-narrow :
  1 ∣ [] ∣ []
    ⊢ badBody ⊒ badBody′
    ∶ id (＇ 0) ↦ id (＇ 0)
badBody-narrow =
  ƛ⊒ƛ id-var0-fun-cast (⊒blame id-var0-cast)

badPoly-narrow :
  0 ∣ [] ∣ []
    ⊢ badPoly ⊒ badPoly′
    ∶ `∀ (id (＇ 0) ↦ id (＇ 0))
badPoly-narrow =
  Λ⊒Λ forall-id-var0-fun-cast badBody-value badBody-narrow

badPoly-no-step :
  ∀ {χ M} →
  badPoly —→[ χ ] M →
  ⊥
badPoly-no-step (pure-step ())

badPoly-no-No• :
  No• badPoly →
  ⊥
badPoly-no-No• (no•-Λ (no•-ƛ ()))

badPoly-no-RuntimeOK :
  RuntimeOK badPoly →
  ⊥
badPoly-no-RuntimeOK (ok-no no-bullet) =
  badPoly-no-No• no-bullet

badInstCast-no-value :
  Value (badPoly ⟨ - (gen (★ ⇒ ★) var0-fun) ⟩) →
  ⊥
badInstCast-no-value (badPoly-value ⟨ () ⟩)

badNu-no-value :
  ∀ {c} →
  Value (ν ★ badPoly c) →
  ⊥
badNu-no-value ()

badNu-no-step :
  ∀ {χ M c} →
  ν ★ badPoly c —→[ χ ] M →
  ⊥
badNu-no-step (ν-step badPoly-value no-bullet) =
  badPoly-no-No• no-bullet
badNu-no-step (ξ-ν badPoly-step) =
  badPoly-no-step badPoly-step

badNu-no-value-after :
  ∀ {χs W c} →
  ν ★ badPoly c —↠[ χs ] W →
  Value W →
  ⊥
badNu-no-value-after ↠-refl vW =
  badNu-no-value vW
badNu-no-value-after (↠-step step steps) vW =
  ⊥-elim (badNu-no-step step)

badInstCast-no-value-after :
  ∀ {χs W} →
  badPoly ⟨ - (gen (★ ⇒ ★) var0-fun) ⟩ —↠[ χs ] W →
  Value W →
  ⊥
badInstCast-no-value-after ↠-refl vW =
  badInstCast-no-value vW
badInstCast-no-value-after (↠-step (pure-step (β-inst badPoly-value)) steps)
    vW =
  badNu-no-value-after steps vW
badInstCast-no-value-after (↠-step (ξ-⟨⟩ badPoly-step) steps) vW =
  ⊥-elim (badPoly-no-step badPoly-step)

left-widening-without-No•-counterexample :
  LeftWideningWithoutNo• →
  ⊥
left-widening-without-No•-counterexample left-widening
    with left-widening
           badPoly-value
           forall-id-var0-fun-cast
           ex1-line272-≈
           badPoly-narrow
left-widening-without-No•-counterexample left-widening
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , bad↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′ =
  badInstCast-no-value-after bad↠W vW

left-widening-counterexample-prevented :
  No• badPoly →
  ⊥
left-widening-counterexample-prevented =
  badPoly-no-No•

left-widening-counterexample-prevented-runtime :
  RuntimeOK badPoly →
  ⊥
left-widening-counterexample-prevented-runtime =
  badPoly-no-RuntimeOK

goodPoly : Term
goodPoly = Λ (ƛ (` zero))

goodPoly-value : Value goodPoly
goodPoly-value = Λ (ƛ (` zero))

goodPoly-no• : No• goodPoly
goodPoly-no• = no•-Λ (no•-ƛ no•-`)

star-store-det-2 :
  StoreDetWf 2 ((0 , ★) ∷ [])
star-store-det-2 =
  record
    { at = record
        { bound = λ { (here refl) → z<s }
        ; wfTy = λ { (here refl) → wf★ }
        }
    ; wfOlder = λ { (here refl) → wf★ }
    ; unique = λ { (here refl) (here refl) → refl }
    }

ex4-line294-≈-Δ2 :
  2 ∣ (0 ꞉ id ★) ∷ [] ⊢
    var0-fun ≈ star-seal-fun ⨾ⁿ (id (＇ 0) ↦ id (＇ 0))
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex4-line294-≈-Δ2 =
  compose-rightⁿ star-store-det-2 star-seal-fun⊒ id-var0-fun⊒
    (endpointsⁿ refl refl refl refl
      id★-store-narrowing
      wf-var-fun-endpoints
      wf-var-fun-endpoints
      var0-fun-narrowing
      (_ , proj₂ (_⨟ⁿ_ {wfΣ = star-store-det-2}
        star-seal-fun⊒ id-var0-fun⊒)))
  where
    star-seal-fun⊒ = star-seal-fun-narrowingᵐ

    id-var0-fun⊒ =
      id-var0-fun-narrowingᵐ {μ = seal-or-idᵈ} refl

ex4-line352-Δ2 :
  2 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ id (＇ 0) ↦ id (＇ 0)
ex4-line352-Δ2 =
  ƛ⊒ƛ id-var0-fun-cast (x⊒x id-var0-cast Z)

ex4-line353-Δ2 :
  2 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ - star-seal-fun ⟩
      ⊒ ƛ (` 0)
    ∶ var0-fun
ex4-line353-Δ2 =
  cast+⊒
    {p = id (＇ 0) ↦ id (＇ 0)}
    {r = var0-fun}
    {t = star-seal-fun}
    id-var0-fun-cast ex4-line294-≈-Δ2 ex4-line352-Δ2

ex4-split-Δ2 :
  2 ∣ (0 ꞉= ★ ⊒) ∷ (⊒ 1 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ - ((unseal 1 ★) ↦ (seal ★ 1)) ⟩
      ⊒ ƛ (` 0)
    ∶ var0-fun
ex4-split-Δ2 =
  split
    {N =
      (ƛ (` 0))
        ⟨ - star-seal-fun ⟩}
    {N′ = ƛ (` 0)}
    {p = var0-fun}
    {q = id ★}
    {A = ★}
    {α = 0}
    {αᵢ = 1}
    id★-cast
    var0-fun-cast
    ex4-line353-Δ2

ex4-after-reduction-Δ1 :
  1 ∣ (⊒ 0 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ - star-seal-fun ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★)
        var0-fun
ex4-after-reduction-Δ1 =
  ⊒Λ poly-fun-cast ex4-split-Δ2

left-widening-ex4-gen :
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (goodPoly ⟨ - (gen (★ ⇒ ★) var0-fun) ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs 0) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π [] ∣ []
      ⊢ W ⊒ applyTerms χs goodPoly
      ∶ applyCoercions χs (gen (★ ⇒ ★) var0-fun)
left-widening-ex4-gen =
  left-widening-gen-inert-⊒Λ-package
    {Δ = 0} {σ = []} {N = ƛ (` zero)} {V′ = ƛ (` zero)}
    {A = ★ ⇒ ★} {B = ＇ zero ⇒ ＇ zero} {c = var0-fun}
    (ƛ (` zero))
    (no•-ƛ no•-`)
    (_ ↦ _)
    poly-fun-cast
    ex4-split-Δ2
