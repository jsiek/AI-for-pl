module strong-rep-nu.proof.RepWeaken where

-- File Charter:
--   * REPRESENTATION-ONLY MOVES OF A TYPING DERIVATION — the two
--     transports whose movers have an IDENTITY ordinary component:
--     `ShiftTyping` (§2, THE SIBLING SHIFT every congruence of
--     `preserve` consumes) and `CrossΛTyping` (§3, what substitution
--     consumes when an image crosses `Λ`).  §1 is the renaming
--     induction they are both instances of.
--   * THE WORKHORSE IS THE CUT `⊢renᴿ`: the insertion is abstracted
--     into an arbitrary `RepWk ρ Ξ Ξ′` and the name map is renamed
--     POINTWISE, so going under `Λ` is just `extᵗ ρ`.  The term
--     context passes through UNCHANGED, and crossing a boundary runs
--     the SAME ρ — there is no bind block to offset.
--   * THE PAYLOAD MUST BE WELL FORMED, or the shift is FALSE.
-- Commentary: Commentary.md § proof/RepWeaken.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-cancelˡ-≡)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Boundary
open import strong-rep-nu.Terms
open import strong-rep-nu.TermSubst
open import strong-rep-nu.proof.TermSubst
open import strong-rep-nu.proof.Preserve
  using (CrossΛTyping; ShiftTyping; repwk-alloc; WfRen-wk; wf-ren;
         wf-same; same-weaken; wf-underΛ; ν-boundary-ren)

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
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} w (⊢ν wA rA ⊢L mw ⊢c smC same wB)
  with ν-boundary-ren w rA mw ⊢c smC same
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} w (⊢ν wA rA ⊢L mw ⊢c smC same wB)
  | Δ′ , mw′ , ⊢c′ , smC′ , same′ =
  ⊢ν (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wA) (same-ren ρ rA)
     (⊢renᴿ w ⊢L) mw′ ⊢c′ smC′ same′
     (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wB)
⊢renᴿ {Ξ = Ξ} {Ξ′ = Ξ′} {η = η} {ρ = ρ} w
      (boundary (bw wΔ (interior cs) (conversion csᶜ))
           ⊢M ⊢c pᵢ pₑ wE) =
  boundary (bw (wfctx-ren w wΔ)
          (interior-ren w (interior cs))
          (conversion-ren w (conversion csᶜ)))
      (⊢renᴿ w ⊢M)
      (conv-ren w ⊢c)
      (same-ren ρ pᵢ)
      (same-ren ρ pₑ)
      (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wE)

------------------------------------------------------------------------
-- §2  The sibling shift
------------------------------------------------------------------------

-- THE INSTANCE THE STORE RUNS AT: `allocate R (Ξ ∣ η)` is literally
-- `(bindR R ∷ Ξ) ∣ map suc η`, so the one new lemma of the store
-- experiment is `⊢renᴿ` at `repwk-alloc`, with no cast at all.
shift-⊢ : ShiftTyping
shift-⊢ wR ⊢M = ⊢renᴿ (repwk-alloc wR) ⊢M

------------------------------------------------------------------------
-- §3  Crossing one `Λ`
------------------------------------------------------------------------

cross-Λ-⊢ : CrossΛTyping
cross-Λ-⊢ {Δ = Ξ ∣ η} {W = W} {A = A} wfΔ wA ⊢W =
  subst (λ M → underΛ (Ξ ∣ η) ∣ [] ⊢ M ⦂ ⇑ᵗ A) (sym term-eq)
        (boundary mwΛ inner (mkId-⊢ sameₑ) sameᵢ sameₑ w↑)
  where
  Δᵢ : Ctxᵗ
  Δᵢ = (abstR ∷ Ξ) ∣ shiftReps η

  w↑ : underΛ (Ξ ∣ η) ⊢ᵗ ⇑ᵗ A
  w↑ = wf-ren (WfRen-wk {Δ = Ξ ∣ η}) wA

  mwΛ : BoundaryWf (underΛ (Ξ ∣ η))
          ((unbind 0 0 ∷ [])) Δᵢ (underΛ (Ξ ∣ η))
  mwΛ =
    bw (wf-underΛ wfΔ)
       (interior (changes∷ changes[]
                   (step-unbind (_ , here) del-here fresh-zero-shift)))
       (conversion (conv-unbind (_ , here) conv[]))

  inner : Δᵢ ∣ [] ⊢ renᴹᴿ suc W ⦂ A
  inner = ⊢renᴿ repwk-abst₀ ⊢W

  R : Ty
  R = proj₁ (wf-same wA)

  -- the crossing value's type and the wrapper's are ONE
  -- representation, shifted past the new cell
  sameᵢ : names Δᵢ ⊢ A ~ ⇑ᵗ R
  sameᵢ = same-ren suc (proj₂ (wf-same wA))

  sameₑ : names (underΛ (Ξ ∣ η)) ⊢ ⇑ᵗ A ~ ⇑ᵗ R
  sameₑ = same-weaken (proj₂ (wf-same wA))

  term-eq : crossΛᴹ W A
    ≡ renᴹᴿ suc W ⟪ (unbind 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫
  term-eq =
    cong (λ M → M ⟪ (unbind 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫)
         (renᴹ²-ord-id (λ X → refl) W)
