module strong.proof.Interior where

-- Strong System F v8 — the interior walk is SOUND for typed
-- conversions: `pushAsgn`/`popAsgn` are the functional forms of the pop
-- judgment, so a typed conversion's interior context is the one
-- `interior` computes.  This is what `ξ-⟨⟩` needs in `Progress`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion

private
  variable
    Σ : Store
    Γ Γ′ Δ Δᵢ : Ctxᵗ
    A B : Ty
    X : ℕ
    α : Addr
    c : Conv
    ĉ : ConvElt

pop-sound : Γ ▷ X := α ⇒ Γ′ → popAsgn X α Γ ≡ just Γ′
pop-sound (pop-here {α = α}) with α ≟ᵃ α
pop-sound (pop-here {α = α}) | yes _ = refl
pop-sound (pop-here {α = α}) | no ne = ⊥-elim (ne refl)
pop-sound (pop-bind-b p) rewrite pop-sound p = refl
pop-sound (pop-bind-l p) rewrite pop-sound p = refl

-- At name 0 the push is on top, whatever the context looks like.
push-zero : ∀ α Γ → pushAsgn zero α Γ ≡ just (asgn α ∷ Γ)
push-zero α [] = refl
push-zero α (asgn β ∷ Γ) = refl
push-zero α (bind ∷ Γ) = refl
push-zero α (addr ∷ Γ) = refl
push-zero α (nuBind R ∷ Γ) = refl

push-sound : Γ ▷ X := α ⇒ Γ′ → pushAsgn X α Γ′ ≡ just Γ
push-sound (pop-here {α = α} {Γ = Γ}) = push-zero α Γ
push-sound (pop-bind-b p) rewrite push-sound p = refl
push-sound (pop-bind-l p) rewrite push-sound p = refl

mutual
  elt-interior : Σ ∣ Δᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Δ → interiorElt ĉ Δ ≡ just Δᵢ
  elt-interior (conv-seal r rd p) = pop-sound p
  elt-interior (conv-hide wf p na) = pop-sound p
  elt-interior (conv-unseal r rd p na) = push-sound p
  elt-interior (conv-show wf p na) = push-sound p
  elt-interior (conv-fun s t) = conv-interior t
  elt-interior (conv-all s) rewrite conv-interior s = refl

  conv-interior : Σ ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → interior c Δ ≡ just Δᵢ
  conv-interior (conv-id wf) = refl
  conv-interior (conv-cons hd tl)
    rewrite conv-interior tl = elt-interior hd
