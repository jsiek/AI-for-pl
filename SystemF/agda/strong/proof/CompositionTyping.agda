module strong.proof.CompositionTyping where

-- Strong System F v8 — COMPOSITION preserves typing.
--
-- The raw append is the easy half, and v8's strictly reflexive
-- terminator is why: `id A ⧺ d = d`, and a typed `id A` has EQUAL
-- endpoints AND an equal context, so the second conversion already has
-- exactly the type and the context the composite needs — no bridging,
-- no transport.  Under v7's bridging terminator this single case was
-- the whole difficulty of the composition campaign.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion

private
  variable
    Sg : Store
    Γ Γ₁ Γ₂ Γ₃ : Ctxᵗ
    A B C : Ty
    R S : RepTy
    α : Addr
    c d : Conv

------------------------------------------------------------------------
-- Appending
------------------------------------------------------------------------

⧺-typing : Sg ∣ Γ₁ ⊢ c ∶ A ⇝ B ⊣ Γ₂ → Sg ∣ Γ₂ ⊢ d ∶ B ⇝ C ⊣ Γ₃
  → Sg ∣ Γ₁ ⊢ (c ⧺ d) ∶ A ⇝ C ⊣ Γ₃
⧺-typing (conv-id wf) ⊢d = ⊢d
⧺-typing (conv-cons hd tl) ⊢d = conv-cons hd (⧺-typing tl ⊢d)

------------------------------------------------------------------------
-- The representation of an address is unique
------------------------------------------------------------------------
-- Driven by the address's own structure: a level indexes the store, a
-- bound index counts entries.  No well-formedness is needed.

∋ˡ-unique : ∀ {Sg ℓ R S} → Sg ∋ˡ ℓ := R → Sg ∋ˡ ℓ := S → R ≡ S
∋ˡ-unique l-here l-here = refl
∋ˡ-unique (l-there p) (l-there q) = ∋ˡ-unique p q

∋r-unique : Sg ∣ Γ ∋r α := R → Sg ∣ Γ ∋r α := S → R ≡ S
∋r-unique (r-lvl l) (r-lvl m) = ∋ˡ-unique l m
∋r-unique r-here r-here = refl
∋r-unique (r-skip-addr p) (r-skip-addr q) = cong ⇑ᴿ (∋r-unique p q)
∋r-unique (r-skip-nu p) (r-skip-nu q) = cong ⇑ᴿ (∋r-unique p q)
∋r-unique (r-skip-bind p) (r-skip-bind q) = cong ⇑ᴿ (∋r-unique p q)
∋r-unique (r-skip-asgn p) (r-skip-asgn q) = ∋r-unique p q

------------------------------------------------------------------------
-- What the normalizing half still needs
------------------------------------------------------------------------
-- `preserve-step`'s cancelling cases reconnect exactly: `pop-unique`
-- forces the remover to the address and the context the adder created,
-- and `∋r-unique` forces the two representations to agree.  The one
-- remaining gap is that BOTH READ-BACKS must then give the same type,
--
--   Sg ∣ Γ ⊢ R ⇓ A → Sg ∣ Γ ⊢ R ⇓ B → A ≡ B,
--
-- which is FALSE for an arbitrary context: `read-var` reads an address
-- through a name, and a context that assigns two names to one address
-- reads it two ways.  Contexts a well-formed program builds never do —
-- that is the notes' `Γ ∌ _:=α` side condition on `Γ,X:=α` — so this
-- needs a context well-formedness invariant, and the design question is
-- where to enforce it.  See notes/DECISIONS.md (2026-09-15).
