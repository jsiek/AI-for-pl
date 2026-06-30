module proof.LeftWidening where

-- File Charter:
--   * Mechanized work on the GTSF Left Widening Lemma used by
--     `proof.Catchup`.
--   * The target statement matches the current `left-widening-lemma`
--     postulate in `proof.Catchup`.
--   * The proof search is kept here to avoid obscuring the larger catchup
--     proof and to make failed strategies explicit.
--
-- Strategy log:
--   * Directly reusing `cast+⊒` works only when the dual cast is inert, since
--     then `V ⟨ - t ⟩` is already a value.  This should cover function,
--     universal, tag, and generated-function/all inert cases.
--   * Reducing identity casts requires turning the endpoint-equivalence
--     premise into a syntactic index equality.  The intended route is the
--     existing mode-indexed narrowing determinacy theorem.
--   * The seal/unseal and inst/gen branches are not mere congruence cases:
--     the paper handles them with right-seal/nu-specific reasoning.  These
--     branches are the first place to look for either a missing algebraic
--     lemma or a counterexample.
--   * Counterexample found in the inst/gen branch: the statement assumes only
--     `Value V`, but the `ν-step` after `β-inst` additionally needs
--     `No• V`.
--     A lambda value can hide a runtime bullet in its body, so the reduction
--     reaches a stuck non-value `ν ★ V c`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; ∃-syntax)

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
    ; id-var0-cast
    ; id-var0-fun-cast
    ; var0-fun
    )
open import proof.CatchupStore using (combineStoreNrw)
open import proof.ReductionProperties using (applyCoercions)

dual-untag-inert :
  ∀ {G} →
  Ground G →
  Inert (- (G ？))
dual-untag-inert (＇ α) = (＇ α) !
dual-untag-inert (‵ ι) = (‵ ι) !
dual-untag-inert ★⇒★ = (★ ⇒ ★) !

LeftWidening : Set₁
LeftWidening =
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

left-widening-inert :
  ∀ {Δ σ V V′ p r t A B C D} →
  Inert (- t) →
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
left-widening-inert {Δ = Δ} {σ = σ} {V = V} {V′ = V′}
    {p = p} {r = r} {t = t} inert-t vV pᶜ r≈t⨟p V⊒V′ =
  [] , V ⟨ - t ⟩ , Δ , [] , [] , [] ,
  vV ⟨ inert-t ⟩ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  cast+⊒ pᶜ r≈t⨟p V⊒V′

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

left-widening-counterexample :
  LeftWidening →
  ⊥
left-widening-counterexample left-widening
    with left-widening
           badPoly-value
           forall-id-var0-fun-cast
           ex1-line272-≈
           badPoly-narrow
left-widening-counterexample left-widening
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , bad↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′ =
  badInstCast-no-value-after bad↠W vW
