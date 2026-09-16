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
open Ctxᵗ
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

-- Both are STACK operations, so soundness is an induction on the
-- stack and the base rides along untouched.
pop-soundS : ∀ {Ss Ss′ Bs} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → popAsgnS X α Ss ≡ just Ss′
pop-soundS (pop-here {α = α}) with α ≟ᵃ α
pop-soundS (pop-here {α = α}) | yes _ = refl
pop-soundS (pop-here {α = α}) | no ne = ⊥-elim (ne refl)
pop-soundS (pop-bind p) rewrite pop-soundS p = refl

pop-base : ∀ {Γ Γ′ X α} → Γ ▷ X := α ⇒ Γ′ → bas Γ ≡ bas Γ′
pop-base pop-here = refl
pop-base (pop-bind p) = refl

pop-sound : Γ ▷ X := α ⇒ Γ′ → popAsgn X α Γ ≡ just Γ′
pop-sound (pop-here {α = α}) with α ≟ᵃ α
pop-sound (pop-here {α = α}) | yes _ = refl
pop-sound (pop-here {α = α}) | no ne = ⊥-elim (ne refl)
pop-sound (pop-bind p) rewrite pop-soundS p = refl

push-soundS : ∀ {Ss Ss′ Bs} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → pushAsgnS X α Ss′ ≡ just Ss
push-soundS pop-here = refl
push-soundS (pop-bind p) rewrite push-soundS p = refl

push-sound : Γ ▷ X := α ⇒ Γ′ → pushAsgn X α Γ′ ≡ just Γ
push-sound pop-here = refl
push-sound (pop-bind p) rewrite push-soundS p = refl

mutual
  elt-interior : Σ ∣ Δᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Δ → interiorElt ĉ Δ ≡ just Δᵢ
  elt-interior (conv-seal r rd p) = pop-sound p
  elt-interior (conv-hide sc wf p na) = pop-sound p
  elt-interior (conv-unseal r rd p na) = push-sound p
  elt-interior (conv-show sc wf p na) = push-sound p
  elt-interior (conv-fun s t) = conv-interior t
  elt-interior (conv-all s) rewrite conv-interior s = refl

  conv-interior : Σ ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → interior c Δ ≡ just Δᵢ
  conv-interior (conv-id wf) = refl
  conv-interior (conv-cons hd tl)
    rewrite conv-interior tl = elt-interior hd
