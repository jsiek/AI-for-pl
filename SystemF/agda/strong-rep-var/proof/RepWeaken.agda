module strong-rep-var.proof.RepWeaken where

-- REPRESENTATION-ONLY MOVES OF A TYPING DERIVATION.  This module proves
-- the two transports whose movers have an identity ordinary component:
-- `RepWeakenTyping`, which `Peel` consumes (strong-rep-var.proof.PeelDual §3),
-- and `CrossΛTyping`, which term substitution consumes when an image
-- crosses `Λ` (strong-rep-var.proof.Preserve §3).  `Peel` moves its argument
-- from the
-- boundary's exterior Δ to that exterior UNDER the boundary's own
-- representation bind block, `extendReps (binds Θ) Δ`.  The ordinary name
-- map is only RENUMBERED there — every ordinary position survives — so
-- the argument's type does not change and no ordinary spelling inside it
-- moves.  What moves is every representation occurrence: the payloads of
-- the morphisms in its own frames and the representation variable each of
-- their changes carries.  `renᴹᴿ` is exactly that traversal.
--
-- THE WORKHORSE is not the statement itself but its generalisation to a
-- CUT.  The induction goes under `Λ` (which pushes one `abstR`) and under
-- a boundary (which pushes a whole bind block), so the inserted block
-- stops being at the head of the representation context; and the name map
-- stops being the exterior's.  Both are absorbed by abstracting the
-- insertion into an arbitrary representation renaming ρ together with the
-- four facts it must supply — `RepWk ρ Ξ Ξ′`, strong-rep-var.Ctx §11 — and
-- renaming the name map POINTWISE, as `map ρ`:
--
--   ⊢renᴿ : RepWk ρ Ξ Ξ′ → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A
--         → (Ξ′ ∣ map ρ η) ∣ Γ ⊢ renᴹᴿ ρ M ⦂ A
--
-- The term context Γ passes through UNCHANGED: `⊢`'s variable rule does
-- not read the type context at all, and an ordinary type spelling is
-- untouched by a representation renaming.  Under `Λ` the renaming becomes
-- `extᵗ ρ` (`repwk-abst`) and under a boundary `extN (numBinds Θ) ρ`
-- (`repwk-push`), which is precisely how `renᴹᴿ` recurses.
--
-- THE HARD CASE IS `env`, and every one of its six premises transports
-- by a lemma of strong-rep-var.proof.Ctx §3, strong-rep-var.CtxMorph §3d or
-- strong-rep-var.Conversion §2d: the
-- exterior well-formedness by `wfctx-ren`, the bind block by
-- `binds-ren`, the two readings by `interior-ren`/`conversion-ren`, the
-- conversion's TYPING by `conv-ren` (the conversion and both of its types
-- are unchanged — a conversion is rep-free — but the lookup square it
-- cites now reads a renamed payload), the two alignment premises by
-- `same-ren`, and the exterior type's well-formedness by `wf-ren-rep`.
-- `TyBeta`-minted boundaries inside the argument and the lock/unlock
-- change lists are not special-cased anywhere: they are `env`s and change
-- runs like any other.
--
-- THE PREMISE `reps Δ ⊢ᴮ Rs` IS NECESSARY.  Without it the statement is
-- FALSE, machine-checked in notes/RepWeakenBindsWall.agda: `env` stores a
-- `MorphWf` whose `mw-exterior` is a `WfCtx`, so the WEAKENED context must
-- be well formed, and `WfRepCtx (pushRepBinds Rs (reps Δ))` holds only
-- when each inserted payload is well formed where it is written.  At the
-- one call site the premise is free — it is `mw-binds` of the very
-- boundary being crossed.
--
-- `CrossΛTyping` runs the same induction at the base instance
-- `repwk-abst₀ : RepWk suc Ξ (abstR ∷ Ξ)`.  The moved term lands under
-- the new abstract representation binder but outside its ordinary name.
-- One `env` with `morph [] (lock 0 0 ∷ [])` then supplies exactly that
-- missing ordinary boundary: its interior deletes name zero, while its
-- conversion reading retains it for `mkId (⇑ᵗ A)`.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-cancelˡ-≡)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong-rep-var.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-var.Ctx
open import strong-rep-var.proof.Ctx
open import strong-rep-var.Conversion
open import strong-rep-var.CtxMorph
open import strong-rep-var.Terms
open import strong-rep-var.TermSubst
open import strong-rep-var.proof.Preserve
  using (CrossΛTyping; RepWeakenTyping; WfRen-wk; wf-ren; wf-same;
         same-weaken; wf-underΛ)

------------------------------------------------------------------------
-- §1  The renaming induction
------------------------------------------------------------------------

-- `shiftRep` is `renameᵗ` at a weakening, at every depth.
renameᵗ-shiftRep : (n : ℕ) (ρ : Renameᵗ) (R : Ty)
  → renameᵗ (extN n ρ) (shiftRep n R) ≡ shiftRep n (renameᵗ ρ R)
renameᵗ-shiftRep zero    ρ R = refl
renameᵗ-shiftRep (suc n) ρ R =
  trans (renameᵗ-⇑ (extN n ρ) (shiftRep n R))
        (cong ⇑ᵗ (renameᵗ-shiftRep n ρ R))

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
⊢renᴿ {η = η} {ρ = ρ} w (⊢Λ ⊢N) =
  ⊢Λ (⊢cast (names-underΛ-ren ρ η) (⊢renᴿ (repwk-abst w) ⊢N))
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} w (⊢·[] ⊢L wA) =
  ⊢·[] (⊢renᴿ w ⊢L) (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wA)
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {η = η} {ρ = ρ} w
      (env {Θ = Θ} (mw wΔ bs (interior cs) (conversion csᶜ))
           ⊢M ⊢c (Rᵢ , pᵢ , qᵢ) (Rₑ , pₑ , qₑ) wE) =
  env (mw (wfctx-ren w wΔ) (binds-ren w bs)
          (interior-ren w (interior cs))
          (conversion-ren w (conversion csᶜ)))
      (⊢renᴿ (repwk-push w (binds Θ)) ⊢M)
      (conv-ren (repwk-push w (binds Θ)) ⊢c)
      (renameᵗ (extN (numBinds Θ) ρ) Rᵢ
        , same-ren (extN (numBinds Θ) ρ) pᵢ
        , same-ren (extN (numBinds Θ) ρ) qᵢ)
      (renameᵗ ρ Rₑ
        , same-ren ρ pₑ
        , subst (λ T → map (extN (numBinds Θ) ρ) _ ⊢ _ ~ T)
                (trans (renameᵗ-shiftRep (numBinds Θ) ρ Rₑ)
                       (cong (λ n → shiftRep n (renameᵗ ρ Rₑ))
                             (sym (length-map (renameᵗ ρ) (binds Θ)))))
                (same-ren (extN (numBinds Θ) ρ) qₑ))
      (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wE)

------------------------------------------------------------------------
-- §2  Inserting a bind block at the head, and the theorem
------------------------------------------------------------------------

wkN-+ : (n α : ℕ) → wkN n α ≡ n + α
wkN-+ zero    α = refl
wkN-+ (suc n) α = cong suc (wkN-+ n α)

map-wkN : (n : ℕ) (η : TyCtx) → map (wkN n) η ≡ shiftRVars n η
map-wkN n []      = refl
map-wkN n (α ∷ η) = cong₂ _∷_ (wkN-+ n α) (map-wkN n η)

renameᵗ-wkN : (n : ℕ) (R : Ty) → renameᵗ (wkN n) R ≡ shiftBy n R
renameᵗ-wkN zero    R = renameᵗ-pointwise-id (λ X → refl) R
renameᵗ-wkN (suc n) R =
  trans (sym (renameᵗ-fuse suc (wkN n) R))
        (cong ⇑ᵗ (renameᵗ-wkN n R))

renRepBinding-wkN : (n : ℕ) (b : RepBinding)
  → shiftByᵇ n b ≡ renRepBinding (wkN n) b
renRepBinding-wkN n abstR = shiftByᵇ-abstR n
renRepBinding-wkN n (bindR R) =
  trans (shiftByᵇ-bindR n R) (cong bindR (sym (renameᵗ-wkN n R)))

-- THE INSERTION ITSELF: pushing a well-formed bind block onto the head of
-- a representation context is a representation weakening by `wkN` of its
-- width.  This is the instance `⊢renᴿ` is run at; `repwk-abst` and
-- `repwk-push` carry it through the induction, at a CUT.
repwk-wkN : ∀ {Ξ : RepCtx} (Rs : List Ty) → Ξ ⊢ᴮ Rs
  → RepWk (wkN (length Rs)) Ξ (pushRepBinds Rs Ξ)
repwk-wkN {Ξ = Ξ} Rs bs = repwk inj look bnd (wfRepCtx-push bs)
  where
  n : ℕ
  n = length Rs

  inj : Injᵗ (wkN n)
  inj {α} {β} eq =
    +-cancelˡ-≡ n α β (trans (sym (wkN-+ n α)) (trans eq (wkN-+ n β)))

  look : ∀ {α b} → Ξ ∋ˡ α := b
    → ∃[ b′ ] (pushRepBinds Rs Ξ ∋ˡ wkN n α := b′)
  look {α = α} {b = b} d =
    b , subst (λ i → pushRepBinds Rs Ξ ∋ˡ i := b)
              (sym (wkN-+ n α)) (∋ˡ-push Rs d)

  bnd : ∀ {α b} → Ξ ∋ʳ α := b
    → pushRepBinds Rs Ξ ∋ʳ wkN n α := renRepBinding (wkN n) b
  bnd {α = α} {b = b} d =
    subst (λ i → pushRepBinds Rs Ξ ∋ʳ i := renRepBinding (wkN n) b)
          (sym (wkN-+ n α))
          (subst (λ c → pushRepBinds Rs Ξ ∋ʳ (n + α) := c)
                 (renRepBinding-wkN n b)
                 (∋ʳ-pushᵇ Rs d))

-- THE THEOREM.
rep-weaken-⊢ : RepWeakenTyping
rep-weaken-⊢ {Δ = Ξ ∣ η} Rs bs ⊢W =
  ⊢cast (map-wkN (length Rs) η) (⊢renᴿ (repwk-wkN Rs bs) ⊢W)

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

  mwΛ : MorphWf (underΛ (Ξ ∣ η))
          (morph [] (lock 0 0 ∷ [])) Δᵢ (underΛ (Ξ ∣ η))
  mwΛ =
    mw (wf-underΛ wfΔ) binds[]
       (interior
         (subst (λ D → (abstR ∷ Ξ) ∣ D
                          ⊢χ lock 0 0 ∷ [] ⇒ shiftNames η)
                (sym (shiftRVars-0 (zero ∷ shiftNames η)))
                (changes∷ changes[]
                  (step-lock (_ , here) del-here fresh-zero-shift))))
       (conversion
         (subst (λ D → (abstR ∷ Ξ) ∣ D
                          ⊢χᶜ lock 0 0 ∷ [] ⇒ zero ∷ shiftNames η)
                (sym (shiftRVars-0 (zero ∷ shiftNames η)))
                (conv-lock (_ , here) conv[])))

  inner : Δᵢ ∣ [] ⊢ renᴹᴿ suc W ⦂ A
  inner = ⊢renᴿ repwk-abst₀ ⊢W

  sameᵢ : Δᵢ ⊢ A ≈ ⇑ᵗ A ⊣ underΛ (Ξ ∣ η)
  sameᵢ with wf-same wA
  sameᵢ | R , p = ⇑ᵗ R , same-ren suc p , same-weaken p

  sameₑ : SameTyExt zero (underΛ (Ξ ∣ η)) (⇑ᵗ A)
                         (underΛ (Ξ ∣ η)) (⇑ᵗ A)
  sameₑ with wf-same w↑
  sameₑ | R , p = R , p , p

  term-eq : crossΛᴹ W A
    ≡ renᴹᴿ suc W ⟪ morph [] (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫
  term-eq =
    cong (λ M → M ⟪ morph [] (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫)
         (renᴹ²-ord-id (λ X → refl) W)
