module strong.proof.PreserveTyDef where

-- Strong System F v8 — the THREE preservation obligations that are
-- still being proved, stated so that `proof.Preservation` can be
-- written and checked against them now and instantiated later.  This
-- is the repo's `…Def` convention: a statement module plus a
-- parameterized importer.
--
--   `TyBetaOk`  the normal-form builder `revTy` types the crossing that
--               `TyBeta` inserts (proof.BuilderTyping)
--   `TyWrapOk`  the instantiated conversion `instReveal` types the one
--               `TyWrap` inserts; it is `revTy` composed with a type
--               substitution on the annotations
--   `AllocOk`   discharging the `ν`'s base binder into a fresh store
--               level preserves typing, and keeps the store well
--               formed (proof.PreserveAlloc)

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst
open import strong.proof.Flat using (Flat)
open import strong.proof.Scoped using (Scoped)

TyBetaOk : Set
-- The result type is left FREE and read off the given derivation, as
-- in `preserve-Wrap`: `B [ A ]ᵗ` is a stuck substitution, which the
-- unifier cannot match against the goal's type.
TyBetaOk = ∀ {Sg Δ V A B R C}
  → StoreOk Sg → Flat Δ → NameFn Δ → Scoped Sg Δ
  → Sg ∣ Δ ⊢⌊ A ⌋ R
  → Sg ∣ Δ ∣ [] ⊢ (Λ V) • B [ A ] ⦂ C
  → Sg ∣ Δ ∣ [] ⊢ ν R ∙ (V ⟨ revTy zero (bse zero) A B ⟩) ⦂ C

-- `instReveal` consults the context for the spine's source, so the
-- obligation carries the same interior equation the rule does.
TyWrapOk : Set
TyWrapOk = ∀ {Sg Δ Δᵢ V c d A B R C}
  → StoreOk Sg → Flat Δ → NameFn Δ → Scoped Sg Δ
  → allView c ≡ just d
  → Sg ∣ Δ ⊢⌊ A ⌋ R
  → interior c Δ ≡ just Δᵢ
  → Sg ∣ Δ ∣ [] ⊢ ((Λ V) ⟨ c ⟩) • B [ A ] ⦂ C
  → Sg ∣ Δ ∣ [] ⊢ ν R ∙ (V ⟨ instReveal Sg (bind ∷ stk Δᵢ ∥ bas Δᵢ)
                               zero (bse zero) A d ⟩) ⦂ C

AllocOk : Set
AllocOk = ∀ {Sg Δ Γ R M A}
  → StoreOk Sg → Flat Δ → Scoped Sg Δ
  → Sg ∣ Δ ∣ Γ ⊢ ν R ∙ M ⦂ A
  → (StoreOk (Sg ∷ʳ R))
    × ((Sg ∷ʳ R) ∣ Δ ∣ Γ ⊢ M [ lvl (length Sg) ]ᵃᴹ ⦂ A)
