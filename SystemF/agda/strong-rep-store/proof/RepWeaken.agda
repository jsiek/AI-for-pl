module strong-rep-store.proof.RepWeaken where

-- REPRESENTATION-ONLY MOVES OF A TYPING DERIVATION.  This module proves
-- the two transports whose movers have an identity ordinary component:
-- `ShiftTyping` — THE SIBLING SHIFT of the store experiment
-- (notes/RepStoreSketch.md), which every congruence of `preserve`
-- consumes — and `CrossΛTyping`, which term substitution consumes when an
-- image crosses `Λ` (strong-rep-store.proof.Preserve §3).  When a step
-- allocates a cell the whole program lives under one more representation
-- binder, so the redex's SIBLINGS move up by one: `allocate R Δ` only
-- RENUMBERS the ordinary name map — every ordinary position survives — so
-- a sibling's type does not change and no ordinary spelling inside it
-- moves.  What moves is every representation occurrence: the payloads its
-- own boundary scopes cite and the representation variable each of their
-- changes carries.  `renᴹᴿ` is exactly that traversal.
--
-- THE WORKHORSE is not the statement itself but its generalisation to a
-- CUT.  The induction goes under `Λ`, which pushes one `abstR`, so the
-- inserted cell stops being at the head of the representation context and
-- the name map stops being the exterior's.  Both are absorbed by
-- abstracting the insertion into an arbitrary representation renaming ρ
-- together with the four facts it must supply — `RepWk ρ Ξ Ξ′`,
-- strong-rep-store.Ctx §11 — and renaming the name map POINTWISE, as
-- `map ρ`:
--
--   ⊢renᴿ : RepWk ρ Ξ Ξ′ → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A
--         → (Ξ′ ∣ map ρ η) ∣ Γ ⊢ renᴹᴿ ρ M ⦂ A
--
-- The term context Γ passes through UNCHANGED: `⊢`'s variable rule does
-- not read the type context at all, and an ordinary type spelling is
-- untouched by a representation renaming.  Under `Λ` the renaming becomes
-- `extᵗ ρ` (`repwk-abst`), which is precisely how `renᴹᴿ` recurses.
-- CROSSING A BOUNDARY CHANGES NOTHING any more: since the store
-- experiment a boundary scope carries no bind block, so the SAME ρ runs
-- inside it (`interior-ren`/`conversion-ren` at ρ, no `extN` offset).
--
-- THE HARD CASE IS `env`, and every one of its premises transports by a
-- lemma of strong-rep-store.proof.Ctx §3, strong-rep-store.Boundary §3d or
-- strong-rep-store.Conversion §2d: the exterior well-formedness by
-- `wfctx-ren`, the two readings by `interior-ren`/`conversion-ren`, the
-- conversion's TYPING by `conv-ren` (the conversion and both of its types
-- are unchanged — a conversion is rep-free — but the lookup square it
-- cites now reads a renamed payload), the two alignment premises by
-- `same-ren`, and the exterior type's well-formedness by `wf-ren-rep`.
-- The two alignment premises are now the SAME relation at the same depth,
-- which is what retired the old `shiftRep` bookkeeping here.
--
-- THE PAYLOAD MUST BE WELL FORMED.  `repwk-alloc` (Preserve §2) demands
-- `Ξ ⊢ᴿ R`, and without it the shift is FALSE: `env` stores a
-- `BoundaryWf` whose `bw-exterior` is a `WfCtx`, so the ALLOCATED context
-- must be well formed, and `WfRepCtx (bindR R ∷ Ξ)` holds only when R
-- checks over Ξ.  At every call site it is `same-wfᴿ` of the allocating
-- rule's own reading premise (`step-alloc`).
--
-- `CrossΛTyping` runs the same induction at the base instance
-- `repwk-abst₀ : RepWk suc Ξ (abstR ∷ Ξ)`.  The moved term lands under
-- the new abstract representation binder but outside its ordinary name.
-- One `env` with `(lock 0 0 ∷ [])` then supplies exactly that
-- missing ordinary boundary: its interior deletes name zero, while its
-- conversion reading retains it for `mkId (⇑ᵗ A)`.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-cancelˡ-≡)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Boundary
open import strong-rep-store.Terms
open import strong-rep-store.TermSubst
open import strong-rep-store.proof.TermSubst
open import strong-rep-store.proof.Preserve
  using (CrossΛTyping; ShiftTyping; repwk-alloc; WfRen-wk; wf-ren;
         wf-same; same-weaken; wf-underΛ)

------------------------------------------------------------------------
-- §1  The renaming induction
------------------------------------------------------------------------

⊢cast : ∀ {Ξ : RepCtx} {η η′ : TyCtx} {Γ : Ctx} {M : Term} {A : Ty}
  → η ≡ η′ → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A → (Ξ ∣ η′) ∣ Γ ⊢ M ⦂ A
⊢cast refl ⊢M = ⊢M

⊢renᴿ : ∀ {Ξ Ξ′ : RepCtx} {η : TyCtx} {ρ : Renameᵗ}
          {Γ : Ctx} {M : Term} {A : Ty}
  → RepWk ρ Ξ Ξ′
  → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A
  → (Ξ′ ∣ map ρ η) ∣ Γ ⊢ renᴹᴿ ρ M ⦂ A
⊢renᴿ w (⊢` d) = ⊢` d
⊢renᴿ w ⊢$ = ⊢$
⊢renᴿ w ⊢true = ⊢true
⊢renᴿ w ⊢false = ⊢false
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} w (⊢ƛ wA ⊢N) =
  ⊢ƛ (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wA) (⊢renᴿ w ⊢N)
⊢renᴿ w (⊢· ⊢L ⊢M) = ⊢· (⊢renᴿ w ⊢L) (⊢renᴿ w ⊢M)
⊢renᴿ {η = η} {ρ = ρ} w (⊢Λ vN ⊢N) =
  ⊢Λ (value-renᴹᴿ (extᵗ ρ) vN)
     (⊢cast (names-underΛ-ren ρ η) (⊢renᴿ (repwk-abst w) ⊢N))
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} w (⊢·[] ⊢L wA) =
  ⊢·[] (⊢renᴿ w ⊢L) (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wA)
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {η = η} {ρ = ρ} w
      (env (bw wΔ (interior cs) (conversion csᶜ))
           ⊢M ⊢c (Rᵢ , pᵢ , qᵢ) (Rₑ , pₑ , qₑ) wE) =
  env (bw (wfctx-ren w wΔ)
          (interior-ren w (interior cs))
          (conversion-ren w (conversion csᶜ)))
      (⊢renᴿ w ⊢M)
      (conv-ren w ⊢c)
      (renameᵗ ρ Rᵢ , same-ren ρ pᵢ , same-ren ρ qᵢ)
      (renameᵗ ρ Rₑ , same-ren ρ pₑ , same-ren ρ qₑ)
      (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wE)

------------------------------------------------------------------------
-- §2  The sibling shift
------------------------------------------------------------------------

-- THE INSTANCE THE STORE RUNS AT.  Allocating a cell pushes `bindR R`
-- onto the head of the representation context and moves every existing
-- representation variable — and every name-map entry — up by one; that
-- is `RepWk suc` (`repwk-alloc`, strong-rep-store.proof.Preserve §2), and
-- `map suc` IS `shiftNames`, so `allocate R (Ξ ∣ η)` is literally
-- `(bindR R ∷ Ξ) ∣ map suc η`.  Hence THE ONE NEW LEMMA of the store
-- experiment is `⊢renᴿ` at that instance, with no cast at all.
shift-⊢ : ShiftTyping
shift-⊢ wR ⊢M = ⊢renᴿ (repwk-alloc wR) ⊢M

------------------------------------------------------------------------
-- §3  Crossing one `Λ`
------------------------------------------------------------------------

cross-Λ-⊢ : CrossΛTyping
cross-Λ-⊢ {Δ = Ξ ∣ η} {W = W} {A = A} wfΔ wA ⊢W =
  subst (λ M → underΛ (Ξ ∣ η) ∣ [] ⊢ M ⦂ ⇑ᵗ A) (sym term-eq)
        (env mwΛ inner (mkId-⊢ w↑) sameᵢ sameₑ w↑)
  where
  Δᵢ : Ctxᵗ
  Δᵢ = (abstR ∷ Ξ) ∣ shiftNames η

  w↑ : underΛ (Ξ ∣ η) ⊢ᵗ ⇑ᵗ A
  w↑ = wf-ren (WfRen-wk {Δ = Ξ ∣ η}) wA

  mwΛ : BoundaryWf (underΛ (Ξ ∣ η))
          ((lock 0 0 ∷ [])) Δᵢ (underΛ (Ξ ∣ η))
  mwΛ =
    bw (wf-underΛ wfΔ)
       (interior (changes∷ changes[]
                   (step-lock (_ , here) del-here fresh-zero-shift)))
       (conversion (conv-lock (_ , here) conv[]))

  inner : Δᵢ ∣ [] ⊢ renᴹᴿ suc W ⦂ A
  inner = ⊢renᴿ repwk-abst₀ ⊢W

  sameᵢ : Δᵢ ⊢ A ≈ ⇑ᵗ A ⊣ underΛ (Ξ ∣ η)
  sameᵢ with wf-same wA
  sameᵢ | R , p = ⇑ᵗ R , same-ren suc p , same-weaken p

  sameₑ : underΛ (Ξ ∣ η) ⊢ ⇑ᵗ A ≈ ⇑ᵗ A ⊣ underΛ (Ξ ∣ η)
  sameₑ with wf-same w↑
  sameₑ | R , p = R , p , p

  term-eq : crossΛᴹ W A
    ≡ renᴹᴿ suc W ⟪ (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫
  term-eq =
    cong (λ M → M ⟪ (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫)
         (renᴹ²-ord-id (λ X → refl) W)
