module strong.proof.ArrTyping where

-- Strong System F v8 — `arr` splits a typed conversion into two typed
-- conversions, one contravariant and one covariant.
--
-- The split is ELEMENTWISE, so the proof walks the conversion: a `↦`
-- element contributes its own two components, and an identity crossing
-- contributes ITSELF to the covariant side and its DUAL to the
-- contravariant one — which is why the two crossing rules were made
-- exact duals.  The components are appends, and `⧺-typing` types them;
-- `arr` then normalizes, and `preserve-↠` carries the typing along.

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction
open import strong.proof.CompositionTyping using (⧺-typing; preserve-↠)

private
  variable
    Sg : Store
    Δ Δᵢ Δ₂ : Ctxᵗ
    A B A₀ B₀ A′ B′ : Ty
    c : Conv

-- `attach` splits along an append: the first block keeps its elements
-- and gives up its terminator.
attach-++ : ∀ (Ls es : List ConvElt) (T A : Ty)
  → attach (Ls ++ es) A ≡ (attach Ls T ⧺ attach es A)
attach-++ [] es T A = refl
attach-++ (ĉ ∷ Ls) es T A = cong (ĉ ∷ᶜ_) (attach-++ Ls es T A)

-- A rename cannot turn a non-arrow into an arrow.
shift-⇒-inv : ∀ X A {A₀ B₀} → renameᵗ (shiftAtᵗ X) A ≡ (A₀ ⇒ B₀)
  → Σ[ A₁ ∈ Ty ] Σ[ B₁ ∈ Ty ]
      ((A ≡ A₁ ⇒ B₁) × (renameᵗ (shiftAtᵗ X) A₁ ≡ A₀)
       × (renameᵗ (shiftAtᵗ X) B₁ ≡ B₀))
shift-⇒-inv X (A ⇒ B) refl = A , B , refl , refl , refl
shift-⇒-inv X (` Y) ()
shift-⇒-inv X `ℕ ()
shift-⇒-inv X `𝔹 ()
shift-⇒-inv X (`∀ A) ()

wf-⇒-inv : ∀ {Γ A B} → Γ ⊢ᵗ (A ⇒ B) → (Γ ⊢ᵗ A) × (Γ ⊢ᵗ B)
wf-⇒-inv (wf-⇒ a b) = a , b

------------------------------------------------------------------------
-- What the split still needs
------------------------------------------------------------------------
-- The remaining induction is `arrElts-typing`, carrying the SOURCE as
-- an equation (the crossing rules state their types as renames, which
-- the unifier cannot match against an arrow):
--
--   arrElts-typing : ⊢ c ∶ S ⇝ T ⊣ Δ → S ≡ A₀ ⇒ B₀ → T ≡ A′ ⇒ B′
--                  → arrElts (elts c) ≡ just (Ls , Rs)
--                  → (Δ ⊢ attach Ls A₀ ∶ A′ ⇝ A₀ ⊣ Δᵢ)
--                    × (Δᵢ ⊢ attach Rs B′ ∶ B₀ ⇝ B′ ⊣ Δ)
--
-- with three element cases (`↦`, `hide`, `show`), each splitting the
-- fold's output with a `consArr` inversion and gluing by `⧺-typing`
-- and `attach-++`.  `arr-typing` then follows by `preserve-↠` along
-- `normalize-↠`, since `arr` normalizes each component.
--
-- ONE LEMMA IS STILL MISSING for the crossing cases: the terminator
-- `id A₀` of the contravariant component must be well formed at the
-- LARGER context, i.e.
--
--   wf-shift : Γₑ ▷ X := α ⇒ Γᵢ → Γᵢ ⊢ᵗ A
--            → Γₑ ⊢ᵗ renameᵗ (shiftAtᵗ X) A
--
-- — the well-formedness counterpart of a crossing, which needs the
-- corresponding fact for `_∋n_:=_` under insertion.
