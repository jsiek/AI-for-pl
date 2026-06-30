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
--   * After main added the `No• V` premise, this particular counterexample is
--     blocked: `badPoly-no-No•` proves the bad value cannot satisfy it.
--   * The guarded sibling of that counterexample is positive:
--     `left-widening-ex4-gen` follows the Example 4 `gen` branch through
--     `β-inst`, `ν-step`, and `β-Λ•`.  The bookkeeping mismatch it exposed is
--     that emitted `bind` steps raise `Δ`; for now the small Example 4
--     derivation is replayed at the raised context.  A general `gen` proof
--     should use a reusable term-narrowing type-context weakening lemma.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; z<s)
open import Data.Product using (_×_; _,_; proj₂; ∃-syntax)

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
open import proof.NarrowWidenProperties using (StoreDetWf)
open import proof.CatchupStore using (combineStoreNrw)
open import proof.ReductionProperties using (applyCoercions)

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

badInstCast-no-value :
  Value (badPoly ⟨ - gen (★ ⇒ ★) var0-fun ⟩) →
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
  badPoly ⟨ - gen (★ ⇒ ★) var0-fun ⟩ —↠[ χs ] W →
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
    (goodPoly ⟨ - gen (★ ⇒ ★) var0-fun ⟩ —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs 0) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π [] ∣ []
      ⊢ W ⊒ applyTerms χs goodPoly
      ∶ applyCoercions χs (gen (★ ⇒ ★) var0-fun)
left-widening-ex4-gen =
  keep ∷ bind ★ ∷ keep ∷ [] ,
  (ƛ (` zero)) ⟨ - star-seal-fun ⟩ ,
  1 ,
  (zero , ★) ∷ [] ,
  [] ,
  (⊒ zero ꞉=☆) ∷ [] ,
  (ƛ (` zero)) ⟨ _ ↦ _ ⟩ ,
  no•-⟨⟩ (no•-ƛ no•-`) ,
  ↠-step (pure-step (β-inst goodPoly-value))
    (↠-step (ν-step goodPoly-value goodPoly-no•)
      (↠-step (ξ-⟨⟩ (pure-step (β-Λ• (ƛ (` zero)))))
        ↠-refl)) ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-left ⊒ˢ-nil ,
  ex4-after-reduction-Δ1
