module strong.proof.PreserveTyBeta where

-- Strong System F v7 — preservation for `TyBeta`, the rule that MINTS a
-- boundary.
--
--   (Λ V) • B [ A ]  -→  ν (α:=⌊A⌋Δ) , (+X:=α) [ V | +X(B) ]
--
-- Three things have to line up.  The store gives the `∀`'s anchor the
-- representation `⌊A⌋Δ`, so the body moves from `abst` to `bind` (`Fill`).
-- The scope change reveals a source name for that anchor, making the
-- interior a TIGHT reveal pair over the exterior `ΔΘ` (`rev-here`).  And
-- the minted conversion `revTy zero zero A B` targets `closeAt zero A B`,
-- which is exactly `⊢•[]`'s result type `B [ A ]ᵗ`.

open import Data.List using ([]; _∷_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.Reduction
open import strong.proof.CtxProperties using (quote-wfᴿ)
open import strong.proof.CloseTy using (closeAt-single)
open import strong.proof.RevealTyping using
  (Reveals; rev-at; revTy-typing; revTy-NF; read-rename; NameMap)
open import strong.proof.FillAnchor using
  (Fill; fill-here; fill-wf; fill-⊢)
open import strong.proof.TypeWf using (typing-wf-closed)

------------------------------------------------------------------------
-- Reading a freshly stored representation
------------------------------------------------------------------------

renameᵗ-id : ∀ {ρ : Renameᵗ} → (∀ X → ρ X ≡ X) → ∀ A → renameᵗ ρ A ≡ A
renameᵗ-id h (` X) = cong `_ (h X)
renameᵗ-id h `ℕ = refl
renameᵗ-id h `𝔹 = refl
renameᵗ-id h (A ⇒ B) = cong₂ _⇒_ (renameᵗ-id h A) (renameᵗ-id h B)
renameᵗ-id {ρ = ρ} h (`∀ A) = cong `∀ (renameᵗ-id h′ A)
  where
  h′ : ∀ X → extᵗ ρ X ≡ X
  h′ zero = refl
  h′ (suc X) = cong suc (h X)

-- Representation soundness, in the form TyBeta needs it: what `⌊_⌋` writes
-- down, the exterior reads back — and a `bind` pushed in front shifts the
-- anchors without touching a single source index.
quote-read : ∀ {Δ A R} → Δ ⊢⌊ A ⌋ R → Δ ⊢ R ⇓ A
quote-read (quote-var n) = read-var n
quote-read quote-ℕ = read-ℕ
quote-read quote-𝔹 = read-𝔹
quote-read (quote-⇒ q r) = read-⇒ (quote-read q) (quote-read r)
quote-read (quote-∀ q) = read-∀ (quote-read q)

read-bind : ∀ {Δ R A b} → Δ ⊢ R ⇓ A
  → (anch concealed b ∷ Δ) ⊢ ⇑ᴿ R ⇓ A
read-bind {Δ = Δ} {A = A} {b = b} rd =
  subst (λ T → (anch concealed b ∷ Δ) ⊢ _ ⇓ T) (renameᵗ-id (λ X → refl) A)
    (read-rename {ρᵗ = λ X → X} {ρᴿ = suc} n-concealed rd)

------------------------------------------------------------------------
-- The case
------------------------------------------------------------------------

preserve-TyBeta : ∀ {Δ V B A R C}
  → Δ ok
  → Value V
  → Δ ⊢⌊ A ⌋ R
  → Δ ∣ [] ⊢ (Λ V) • B [ A ] ⦂ C
  → Δ ∣ [] ⊢ ν repBind R ∷ [] , reveal zero ∷ []
       [ V ∣ revTy zero zero A B ] ⦂ C
preserve-TyBeta {Δ = Δ} {V = V} {B = B} {A = A} {R = R}
  ctx-ok value q (⊢•[] (⊢Λ body) wfA) =
  subst (λ T → Δ ∣ [] ⊢ ν repBind R ∷ [] , reveal zero ∷ []
                          [ V ∣ revTy zero zero A B ] ⦂ T)
    (closeAt-single A B)
    (⊢ν store scope (revTy-NF zero zero A B) body′ conv)
  where
  wfR : Δ ⊢ᴿ R
  wfR = quote-wfᴿ q

  -- The store introduces the anchor CONCEALED; the scope change reveals
  -- it, which is a flip of one bit.
  store : Δ ⊢ˢ repBind R ∷ [] ⇒ anch concealed (bindA R) ∷ Δ
  store = store-bind wfR store[]

  scope : (anch concealed (bindA R) ∷ Δ) ⊢χ reveal zero ∷ []
        ⇒ (anch revealed (bindA R) ∷ Δ)
  scope = scope∷ rev-here scope[]

  -- The Λ's anchor, abstract in the body's context, is represented here —
  -- the same entry, the same name, a different BINDING.
  give : Fill R zero (anch revealed abstA ∷ Δ)
           (anch revealed (bindA R) ∷ Δ)
  give = fill-here

  body′ : (anch revealed (bindA R) ∷ Δ) ∣ [] ⊢ V ⦂ B
  body′ = fill-⊢ give body

  conv : (anch revealed (bindA R) ∷ Δ)
         ⊢ revTy zero zero A B ∶ B ⇝ closeAt zero A B
         ⊣ (anch concealed (bindA R) ∷ Δ)
  conv = revTy-typing rev-at r-here (read-bind (quote-read q))
           (fill-wf give (typing-wf-closed body))
