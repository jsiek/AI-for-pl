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
  (Reveals; rev-here; revTy-typing; revTy-NF; read-rename; NameMap)
open import strong.proof.FillAnchor using
  (Fill; fill-here; fill-name; fill-wf; fill-⊢)
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

read-bind : ∀ {Δ R S A} → Δ ⊢ R ⇓ A → (bind S ∷ Δ) ⊢ ⇑ᴿ R ⇓ A
read-bind {Δ = Δ} {S = S} {A = A} rd =
  subst (λ T → (bind S ∷ Δ) ⊢ _ ⇓ T) (renameᵗ-id (λ X → refl) A)
    (read-rename {ρᵗ = λ X → X} {ρᴿ = suc} n-over-bind rd)

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
  wfR = quote-wfᴿ ctx-ok q

  okΘ : (bind R ∷ Δ) ok
  okΘ = ok-bind ctx-ok wfR

  fresh : Unoccupied (bind R ∷ Δ) zero
  fresh X (_ , n-over-bind _ , ())

  okᵢ : (name zero ∷ bind R ∷ Δ) ok
  okᵢ = ok-name okΘ a-here-bind fresh

  store : Δ ⊢ˢ repBind R ∷ [] ⇒ bind R ∷ Δ
  store = store-bind wfR store[]

  scope : (bind R ∷ Δ) ⊢χ reveal zero ∷ [] ⇒ name zero ∷ bind R ∷ Δ
  scope = scope∷ (step-reveal a-here-bind fresh) scope[]

  -- The Λ's anchor, abstract in the body's context, is represented here.
  give : Fill R (name zero ∷ abst ∷ Δ) (name zero ∷ bind R ∷ Δ)
  give = fill-name fill-here

  body′ : (name zero ∷ bind R ∷ Δ) ∣ [] ⊢ V ⦂ B
  body′ = fill-⊢ give body

  conv : (name zero ∷ bind R ∷ Δ)
         ⊢ revTy zero zero A B ∶ B ⇝ closeAt zero A B ⊣ (bind R ∷ Δ)
  conv = revTy-typing rev-here okᵢ okΘ (r-over-name r-here)
           (read-bind (quote-read q))
           (fill-wf give (typing-wf-closed body))
