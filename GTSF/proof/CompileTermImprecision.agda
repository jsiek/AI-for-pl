module proof.CompileTermImprecision where

-- File Charter:
--   * Proves compilation monotone from gradual-term imprecision to the new
--     mutually recursive ordinary/quotiented Nu-term imprecision judgments.
--   * Uses quotiented type imprecision only between the hidden lower types of
--     compiled narrowing/widening pairs.
--   * Keeps application and cast reasoning orthogonal.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using
  (cong₂; subst; sym; trans)

open import Types
open import Ctx using (CtxWf; ctxWf-∷)
open import Coercions using (id-onlyᵈ; id-only≤tag-or-idᵈ)
open import Conversion using (reveal↑)
open import Compile using
  ( CastPlan
  ; cast
  ; compileᵀ
  ; compileᵀ-value
  ; consistency-cast-plan
  ; dynamic-application-function-consistent
  ; down⊒
  ; lower
  ; lower-selected
  ; lower⊑target
  ; up⊑
  ; ν-reveal-conversion
  ; seal★-tag-or-id
  )
open import GradualTerms
  using (GTerm)
  renaming
    ( `_ to `ᴳ_
    ; ƛ_⇒_ to ƛᴳ_⇒_
    ; _·[_]_ to _·ᴳ[_]_
    ; Λ_ to Λᴳ_
    ; _`[_] to _`ᴳ[_]
    ; $ to $ᴳ
    ; _⊕[_at_]_ to _⊕ᴳ[_at_]_
    ; _∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_
    ; ⊢` to ⊢ᴳ`
    ; ⊢ƛ to ⊢ᴳƛ
    ; ⊢· to ⊢ᴳ·
    ; ⊢·★ to ⊢ᴳ·★
    ; ⊢Λ to ⊢ᴳΛ
    ; ⊢• to ⊢ᴳ•
    ; ⊢$ to ⊢ᴳ$
    ; ⊢⊕ to ⊢ᴳ⊕
    )
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
import ImprecisionWf as IWF
import Imprecision as Imp
open import Imprecision using () renaming (idι to idιᴵ; ν to νᴵ)
open import ImprecisionWf
  using
    ( ImpAssm
    ; ImpCtx
    ; _ˣ⊑★
    ; _ˣ⊑ˣ_
    ; ⇑ᵢ
    ; ⇑ᴸᵢ
    ; _∣_⊢_⊑_⊣_
    )
open import NuTerms using (Term)
open import NarrowWiden using (narrow-mode-relax; widen-mode-relax)
open import Primitives using (Prim; addℕ; κℕ)
open import proof.NuTermProperties using (CtxWf-⤊)
open import proof.NarrowWidenProperties using (StoreDetWf)
open import proof.ImprecisionProperties using
  ( ⇑ᵢ-ˣ∈
  ; ⇑ᵢ-★∈
  ; ⇑ᴸᵢ-∈
  ; un⇑ᵢ-ˣ∈
  ; un⇑ᵢ-★∈
  ; no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star
  ; un⇑ᴸᵢ-ˣ∈
  ; no-⇑ᴸᵢ-zero-left
  ; ~-sym
  ; ⊑-base-inv-idᵢ
  ; ⊑-forall-base-⊥
  ; ⊑-refl-idᵢ
  )
open import proof.EndpointCanonicalMLBSimpleQuotient using
  (MLB-monotoneᵖ)
open import proof.MaximalLowerBoundsWf using (⊑-forgetᵢ)
open import proof.TypeProperties using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; TyRenameWf-suc
  ; occurs-zero-rename-ext
  ; renameᵗ-id
  ; renameᵗ-preserves-WfTy
  )
open import TermTyping using (SealModeStore★; cast-tag-or-id)

import GradualTermImprecision as GTI
open import GradualTermImprecision using (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
import NuTermImprecision as NTI
import QuotientedTermImprecision as QTI
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)

variable
  Φ Ψ : ImpCtx
  Δᴸ Δᴿ : TyCtx
  γ γ′ : GTI.CtxImp Φ Δᴸ Δᴿ
  A A′ B B′ C C′ : Ty
  p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ
  M M′ N N′ L L′ V V′ : GTerm
  x : Var
  ℓ : Label
  op : Prim

storeDetWf-[] :
  ∀ {Δ} →
  StoreDetWf Δ []
storeDetWf-[] =
  record
    { at = record { bound = λ (); wfTy = λ () }
    ; wfOlder = λ ()
    ; unique = λ ()
    }

seal★-id-only :
  ∀ {Σ} →
  SealModeStore★ id-onlyᵈ Σ
seal★-id-only α ()

------------------------------------------------------------------------
-- Context conversion
------------------------------------------------------------------------

ctxImpToNuEntry :
  GTI.CtxImpEntry Φ Δᴸ Δᴿ →
  NTI.CtxImpEntry Φ Δᴸ Δᴿ
ctxImpToNuEntry (GTI.ctx-imp A B p) =
  NTI.ctx-imp A B p

ctxImpToNu :
  GTI.CtxImp Φ Δᴸ Δᴿ →
  NTI.CtxImp Φ Δᴸ Δᴿ
ctxImpToNu [] = []
ctxImpToNu (entry ∷ γ) = ctxImpToNuEntry entry ∷ ctxImpToNu γ

leftCtx-ctxImpToNu :
  ∀ {Φ Δᴸ Δᴿ} →
  (γ : GTI.CtxImp Φ Δᴸ Δᴿ) →
  NTI.leftCtxⁱ (ctxImpToNu γ) ≡ GTI.srcCtxⁱ γ
leftCtx-ctxImpToNu [] = refl
leftCtx-ctxImpToNu (GTI.ctx-imp A B p ∷ γ) =
  cong₂ _∷_ refl (leftCtx-ctxImpToNu γ)

rightCtx-ctxImpToNu :
  ∀ {Φ Δᴸ Δᴿ} →
  (γ : GTI.CtxImp Φ Δᴸ Δᴿ) →
  NTI.rightCtxⁱ (ctxImpToNu γ) ≡ GTI.tgtCtxⁱ γ
rightCtx-ctxImpToNu [] = refl
rightCtx-ctxImpToNu (GTI.ctx-imp A B p ∷ γ) =
  cong₂ _∷_ refl (rightCtx-ctxImpToNu γ)

ctxImpToNu-∋ :
  ∀ {Φ Δᴸ Δᴿ γ x A B p} →
  γ ∋ x ⦂ GTI.ctx-imp A B p →
  ctxImpToNu {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} γ
    ∋ x ⦂ NTI.ctx-imp A B p
ctxImpToNu-∋ Z = Z
ctxImpToNu-∋ (S x∈) = S (ctxImpToNu-∋ x∈)

ctxImpToNu-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ}
    {γ : GTI.CtxImp Φ Δᴸ Δᴿ}
    {γ′ : GTI.CtxImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  GTI.LiftCtxⁱ Ψ γ γ′ →
  NTI.LiftCtxⁱ Ψ (ctxImpToNu γ) (ctxImpToNu γ′)
ctxImpToNu-lift GTI.lift-[] = NTI.lift-ctx-[]
ctxImpToNu-lift (GTI.lift-∷ liftγ) =
  NTI.lift-ctx-∷ (ctxImpToNu-lift liftγ)

ctxImpToNu-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ}
    {γ : GTI.CtxImp Φ Δᴸ Δᴿ}
    {γ′ : GTI.CtxImp Ψ (suc Δᴸ) Δᴿ} →
  GTI.LiftLeftCtxⁱ Ψ γ γ′ →
  NTI.LiftLeftCtxⁱ Ψ (ctxImpToNu γ) (ctxImpToNu γ′)
ctxImpToNu-lift-left GTI.lift-left-[] = NTI.lift-left-ctx-[]
ctxImpToNu-lift-left (GTI.lift-left-∷ liftγ) =
  NTI.lift-left-ctx-∷ (ctxImpToNu-lift-left liftγ)

------------------------------------------------------------------------
-- Type-imprecision lifting for ν compilation
------------------------------------------------------------------------

renameImpAssm : Renameᵗ → Renameᵗ → ImpAssm → ImpAssm
renameImpAssm ρ σ (X ˣ⊑★) = ρ X ˣ⊑★
renameImpAssm ρ σ (X ˣ⊑ˣ Y) = ρ X ˣ⊑ˣ σ Y

un⇑ᴸᵢ-★∈ :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  (X ˣ⊑★) ∈ Φ
un⇑ᴸᵢ-★∈ {Φ = []} ()
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-★∈ x∈)
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-★∈ x∈)

⇑ᴸᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢ-ˣ∈ {Φ = []} ()
⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ x∈)
⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-ˣ∈ x∈)

⇑ᴸᵢ-★∈ :
  ∀ {Φ X} →
  (X ˣ⊑★) ∈ Φ →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢ-★∈ {Φ = []} ()
⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-★∈ x∈)
⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (⇑ᴸᵢ-★∈ x∈)

no-⇑ᴸᵢ-zero-star :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  ⊥
no-⇑ᴸᵢ-zero-star {Φ = []} ()
no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-star x∈
no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-star x∈

renameImpAssm-⇑ᵢ :
  ∀ {ρ σ Φ Ψ} →
  (∀ {a} → a ∈ Φ → renameImpAssm ρ σ a ∈ Ψ) →
  ∀ {a} →
  a ∈ (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ →
  renameImpAssm (extᵗ ρ) (extᵗ σ) a ∈
    (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Ψ
renameImpAssm-⇑ᵢ h {a = zero ˣ⊑★} (here ())
renameImpAssm-⇑ᵢ h {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-star a∈)
renameImpAssm-⇑ᵢ h {a = suc X ˣ⊑★} (here ())
renameImpAssm-⇑ᵢ h {a = suc X ˣ⊑★} (there a∈) =
  there (⇑ᵢ-★∈ (h (un⇑ᵢ-★∈ a∈)))
renameImpAssm-⇑ᵢ h {a = zero ˣ⊑ˣ zero} (here refl) = here refl
renameImpAssm-⇑ᵢ h {a = zero ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
renameImpAssm-⇑ᵢ h {a = zero ˣ⊑ˣ suc Y} (here ())
renameImpAssm-⇑ᵢ h {a = zero ˣ⊑ˣ suc Y} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-left a∈)
renameImpAssm-⇑ᵢ h {a = suc X ˣ⊑ˣ zero} (here ())
renameImpAssm-⇑ᵢ h {a = suc X ˣ⊑ˣ zero} (there a∈) =
  ⊥-elim (no-⇑ᵢ-zero-right a∈)
renameImpAssm-⇑ᵢ h {a = suc X ˣ⊑ˣ suc Y} (here ())
renameImpAssm-⇑ᵢ h {a = suc X ˣ⊑ˣ suc Y} (there a∈) =
  there (⇑ᵢ-ˣ∈ (h (un⇑ᵢ-ˣ∈ a∈)))

renameImpAssm-⇑ᴸᵢ :
  ∀ {ρ σ Φ Ψ} →
  (∀ {a} → a ∈ Φ → renameImpAssm ρ σ a ∈ Ψ) →
  ∀ {a} →
  a ∈ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ →
  renameImpAssm (extᵗ ρ) σ a ∈ (zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ
renameImpAssm-⇑ᴸᵢ h {a = zero ˣ⊑★} (here refl) = here refl
renameImpAssm-⇑ᴸᵢ h {a = zero ˣ⊑★} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star a∈)
renameImpAssm-⇑ᴸᵢ h {a = suc X ˣ⊑★} (here ())
renameImpAssm-⇑ᴸᵢ h {a = suc X ˣ⊑★} (there a∈) =
  there (⇑ᴸᵢ-★∈ (h (un⇑ᴸᵢ-★∈ a∈)))
renameImpAssm-⇑ᴸᵢ h {a = zero ˣ⊑ˣ Y} (here ())
renameImpAssm-⇑ᴸᵢ h {a = zero ˣ⊑ˣ Y} (there a∈) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left a∈)
renameImpAssm-⇑ᴸᵢ h {a = suc X ˣ⊑ˣ Y} (here ())
renameImpAssm-⇑ᴸᵢ h {a = suc X ˣ⊑ˣ Y} (there a∈) =
  there (⇑ᴸᵢ-ˣ∈ (h (un⇑ᴸᵢ-ˣ∈ a∈)))

TyRenameWf-id :
  ∀ {Δ} →
  TyRenameWf Δ Δ (λ X → X)
TyRenameWf-id X<Δ = X<Δ

imp-renameᵗ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ Δᴿ′ ρ σ A B} →
  (∀ {a} → a ∈ Φ → renameImpAssm ρ σ a ∈ Ψ) →
  TyRenameWf Δᴸ Δᴸ′ ρ →
  TyRenameWf Δᴿ Δᴿ′ σ →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Ψ ∣ Δᴸ′ ⊢ renameᵗ ρ A ⊑ renameᵗ σ B ⊣ Δᴿ′
imp-renameᵗ h hρ hσ IWF.id★ = IWF.id★
imp-renameᵗ h hρ hσ (IWF.idˣ x∈ X<Δᴸ Y<Δᴿ) =
  IWF.idˣ (h x∈) (hρ X<Δᴸ) (hσ Y<Δᴿ)
imp-renameᵗ h hρ hσ IWF.idι = IWF.idι
imp-renameᵗ h hρ hσ (p IWF.↦ q) =
  imp-renameᵗ h hρ hσ p IWF.↦ imp-renameᵗ h hρ hσ q
imp-renameᵗ h hρ hσ (IWF.∀ⁱ p) =
  IWF.∀ⁱ (imp-renameᵗ (renameImpAssm-⇑ᵢ h)
    (TyRenameWf-ext hρ) (TyRenameWf-ext hσ) p)
imp-renameᵗ h hρ hσ (IWF.tag ι) = IWF.tag ι
imp-renameᵗ h hρ hσ (IWF.tag p ⇛ q) =
  IWF.tag (imp-renameᵗ h hρ hσ p) ⇛ imp-renameᵗ h hρ hσ q
imp-renameᵗ h hρ hσ (IWF.tagˣ x∈ X<Δᴸ) =
  IWF.tagˣ (h x∈) (hρ X<Δᴸ)
imp-renameᵗ {ρ = ρ} h hρ hσ (IWF.ν {A = A} occ p) =
  IWF.ν (trans (occurs-zero-rename-ext ρ A) occ)
    (imp-renameᵗ (renameImpAssm-⇑ᴸᵢ h)
      (TyRenameWf-ext hρ) hσ p)

imp-lift :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
    ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ
imp-lift =
  imp-renameᵗ {ρ = suc} {σ = suc}
    (λ { {a = X ˣ⊑★} a∈ → there (⇑ᵢ-★∈ a∈)
       ; {a = X ˣ⊑ˣ Y} a∈ → there (⇑ᵢ-ˣ∈ a∈) })
    TyRenameWf-suc TyRenameWf-suc

imp-lift-left :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ B ⊣ Δᴿ
imp-lift-left {B = B} p =
  subst
    (λ T →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ _) ∣ _ ⊢ _ ⊑ T ⊣ _)
    (renameᵗ-id B)
    (imp-renameᵗ {ρ = suc} {σ = λ X → X}
      (λ { {a = X ˣ⊑★} a∈ → there (⇑ᴸᵢ-★∈ a∈)
         ; {a = X ˣ⊑ˣ Y} a∈ → there (⇑ᴸᵢ-ˣ∈ a∈) })
      TyRenameWf-suc TyRenameWf-id p)

nuCtx⇑ :
  ∀ {Φ Δᴸ Δᴿ} →
  NTI.CtxImp Φ Δᴸ Δᴿ →
  NTI.CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) (suc Δᴸ) (suc Δᴿ)
nuCtx⇑ [] = []
nuCtx⇑ (NTI.ctx-imp A B p ∷ γ) =
  NTI.ctx-imp (⇑ᵗ A) (⇑ᵗ B) (imp-lift p) ∷ nuCtx⇑ γ

nuCtx⇑-lift :
  ∀ {Φ Δᴸ Δᴿ} →
  (γ : NTI.CtxImp Φ Δᴸ Δᴿ) →
  NTI.LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ (nuCtx⇑ γ)
nuCtx⇑-lift [] = NTI.lift-ctx-[]
nuCtx⇑-lift (NTI.ctx-imp A B p ∷ γ) =
  NTI.lift-ctx-∷ (nuCtx⇑-lift γ)

nuCtx⇑ᴸ :
  ∀ {Φ Δᴸ Δᴿ} →
  NTI.CtxImp Φ Δᴸ Δᴿ →
  NTI.CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ
nuCtx⇑ᴸ [] = []
nuCtx⇑ᴸ (NTI.ctx-imp A B p ∷ γ) =
  NTI.ctx-imp (⇑ᵗ A) B (imp-lift-left p) ∷ nuCtx⇑ᴸ γ

nuCtx⇑ᴸ-lift :
  ∀ {Φ Δᴸ Δᴿ} →
  (γ : NTI.CtxImp Φ Δᴸ Δᴿ) →
  NTI.LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ (nuCtx⇑ᴸ γ)
nuCtx⇑ᴸ-lift [] = NTI.lift-left-ctx-[]
nuCtx⇑ᴸ-lift (NTI.ctx-imp A B p ∷ γ) =
  NTI.lift-left-ctx-∷ (nuCtx⇑ᴸ-lift γ)

------------------------------------------------------------------------
-- Congruence helpers for compiler proof plumbing
------------------------------------------------------------------------

compile-context-subst-term-sym :
  ∀ {Δ Γ Γ′ M A}
  → (Γ′≡Γ : Γ′ ≡ Γ)
  → (Γ-wf : CtxWf Δ Γ)
  → (M⊢ : Δ ∣ Γ′ ⊢ᴳ M ⦂ A)
  → proj₁
      (compileᵀ
        (subst (CtxWf Δ) (sym Γ′≡Γ) Γ-wf)
        M⊢)
      ≡ proj₁
        (compileᵀ
          Γ-wf
          (subst (λ Γ₀ → Δ ∣ Γ₀ ⊢ᴳ M ⦂ A) Γ′≡Γ M⊢))
compile-context-subst-term-sym refl Γ-wf M⊢ = refl

nu-term-imprecision-cong-terms :
  ∀ {Φ Δᴸ Δᴿ ρ γ L L′ R R′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  L ≡ L′ →
  R ≡ R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ L ⊑ R ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ L′ ⊑ R′ ⦂ A ⊑ B ∶ p
nu-term-imprecision-cong-terms refl refl L⊑R = L⊑R

imprecision-target-subst :
  ∀ {Φ Δᴸ Δᴿ A B B′} →
  B ≡ B′ →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ
imprecision-target-subst refl A⊑B = A⊑B

compiled-argument-cast-imprecision :
  ∀ {Φ Δᴸ Δᴿ δ M M′ A A′ C C′ pA pC} →
  (plan : CastPlan Δᴸ [] C A) →
  (plan′ : CastPlan Δᴿ [] C′ A′) →
  Φ ∣ Δᴸ ⊢ lower plan ⊑ᵖ lower plan′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ cast plan M ⊑ cast plan′ M′ ⦂ A ⊑ A′ ∶ pA
compiled-argument-cast-imprecision {pA = pA}
    plan plan′ lower⊑lower′ M⊑M′ =
  QTI.up⊑upᵀ
    (QTI.down⊑downᵀ (down⊒ plan) (down⊒ plan′) M⊑M′
      lower⊑lower′)
    (up⊑ plan) (up⊑ plan′) pA

compiled-cast-nat-imprecision :
  ∀ {Φ Δᴸ Δᴿ δ M M′ A A′ p ℓ} →
  (A~ℕ : Imp._⊢_~_ Δᴸ A (‵ `ℕ)) →
  (A′~ℕ : Imp._⊢_~_ Δᴿ A′ (‵ `ℕ)) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ cast (consistency-cast-plan ℓ A~ℕ) M
      ⊑ cast (consistency-cast-plan ℓ A′~ℕ) M′
    ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ IWF.idι
compiled-cast-nat-imprecision
    {p = p} {ℓ = ℓ} A~ℕ A′~ℕ M⊑M′ =
  let
    plan = consistency-cast-plan ℓ A~ℕ
    plan′ = consistency-cast-plan ℓ A′~ℕ
    lower⊑ᵖlower′ =
      MLB-monotoneᵖ p IWF.idι
        (lower-selected plan) (lower-selected plan′)
  in
  compiled-argument-cast-imprecision plan plan′ lower⊑ᵖlower′ M⊑M′

dynamic-application-plan-lower :
  ∀ (Δ : TyCtx) (ℓ : Label) →
  lower
    (consistency-cast-plan {Δ = Δ} ℓ
      dynamic-application-function-consistent)
    ≡ ★ ⇒ ★
dynamic-application-plan-lower Δ ℓ = refl

compiled-right-dynamic-function-imprecision :
  ∀ {Φ Δᴸ Δᴿ δ L L′ A B pA pB ℓ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ L ⊑ L′ ⦂ A ⇒ B ⊑ ★ ∶ IWF.tag pA ⇛ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ L ⊑ cast
      (consistency-cast-plan {Δ = Δᴿ} ℓ
        dynamic-application-function-consistent) L′
    ⦂ A ⇒ B ⊑ ★ ⇒ ★ ∶ pA IWF.↦ pB
compiled-right-dynamic-function-imprecision
    {Δᴿ = Δᴿ} {pA = pA} {pB = pB} {ℓ = ℓ} L⊑L′ =
  let
    plan = consistency-cast-plan {Δ = Δᴿ} ℓ
      dynamic-application-function-consistent
    arrow⊑lower =
      imprecision-target-subst
        (sym (dynamic-application-plan-lower Δᴿ ℓ))
        (pA IWF.↦ pB)
    L⊑L′↓ =
      QTI.⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
        (narrow-mode-relax id-only≤tag-or-idᵈ (down⊒ plan))
        L⊑L′ arrow⊑lower
  in
  QTI.⊑cast⊑idᵀ storeDetWf-[] seal★-id-only
    (up⊑ plan) L⊑L′↓ (pA IWF.↦ pB)

compiled-dynamic-function-imprecision :
  ∀ {Φ Δᴸ Δᴿ δ L L′ ℓ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ L ⊑ L′ ⦂ ★ ⊑ ★ ∶ IWF.id★ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ cast
      (consistency-cast-plan {Δ = Δᴸ} ℓ
        dynamic-application-function-consistent) L
      ⊑ cast
        (consistency-cast-plan {Δ = Δᴿ} ℓ
          dynamic-application-function-consistent) L′
    ⦂ ★ ⇒ ★ ⊑ ★ ⇒ ★ ∶ IWF.id★ IWF.↦ IWF.id★
compiled-dynamic-function-imprecision
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ℓ = ℓ} L⊑L′ =
  let
    plan = consistency-cast-plan {Δ = Δᴸ} ℓ
      dynamic-application-function-consistent
    plan′ = consistency-cast-plan {Δ = Δᴿ} ℓ
      dynamic-application-function-consistent
    lower⊑ᵖlower′ =
      MLB-monotoneᵖ IWF.id★
        (IWF.id★ IWF.↦ IWF.id★)
        (lower-selected plan) (lower-selected plan′)
  in
  compiled-argument-cast-imprecision plan plan′ lower⊑ᵖlower′ L⊑L′

------------------------------------------------------------------------
-- Compile monotonicity
------------------------------------------------------------------------

compile-preserves-term-imprecision-typed :
  (srcΓ-wf : CtxWf Δᴸ (GTI.srcCtxⁱ γ)) →
  (tgtΓ-wf : CtxWf Δᴿ (GTI.tgtCtxⁱ γ)) →
  (M⊑M′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N = proj₁ (compileᵀ srcΓ-wf M⊢)
    N′ = proj₁ (compileᵀ tgtΓ-wf M′⊢)
  in
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ ctxImpToNu γ
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p
compile-preserves-term-imprecision-typed
    srcΓ-wf tgtΓ-wf (GTI.x⊑xᴳ x∈) =
  QTI.x⊑xᵀ (ctxImpToNu-∋ x∈)
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.ƛ⊑ƛᴳ hA hA′ N⊑N′) =
  QTI.ƛ⊑ƛᵀ hA hA′
    (compile-preserves-term-imprecision-typed
      (ctxWf-∷ hA srcΓ-wf)
      (ctxWf-∷ hA′ tgtΓ-wf)
      N⊑N′)
-- application, function endpoints on both sides
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.·⊑·ᴳ {ℓ = ℓ} {pA = pA} {pC = pC}
      L⊑L′ N⊑N′ A~C A′~C′) =
  let
    L⊑L′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        L⊑L′
    N⊑N′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        N⊑N′
    plan = consistency-cast-plan ℓ (~-sym A~C)
    plan′ = consistency-cast-plan ℓ (~-sym A′~C′)
    lower⊑ᵖlower′ =
      MLB-monotoneᵖ pC pA
        (lower-selected plan) (lower-selected plan′)
  in
  QTI.·⊑·ᵀ
    L⊑L′ᵀ
    (compiled-argument-cast-imprecision plan plan′
      lower⊑ᵖlower′ N⊑N′ᵀ)
-- application, right function type is ★
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.·⊑·★ᴳ {ℓ = ℓ} {pA = pA} {pB = pB} {pC = pC}
      L⊑L′ N⊑N′ A~C C′~★) =
  let
    L⊑L′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        L⊑L′
    N⊑N′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        N⊑N′
    argument-plan = consistency-cast-plan ℓ (~-sym A~C)
    argument-plan′ = consistency-cast-plan ℓ C′~★
    argument-lower⊑ᵖlower′ =
      MLB-monotoneᵖ pC pA
        (lower-selected argument-plan) (lower-selected argument-plan′)
  in
  QTI.·⊑·ᵀ
    (compiled-right-dynamic-function-imprecision {ℓ = ℓ} L⊑L′ᵀ)
    (compiled-argument-cast-imprecision argument-plan argument-plan′
      argument-lower⊑ᵖlower′ N⊑N′ᵀ)
-- application, both function types are ★
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.·★⊑·★ᴳ {ℓ = ℓ} {pC = pC}
      L⊑L′ N⊑N′ C~★ C′~★) =
  let
    L⊑L′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        L⊑L′
    N⊑N′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        N⊑N′
    argument-plan = consistency-cast-plan ℓ C~★
    argument-plan′ = consistency-cast-plan ℓ C′~★
    argument-lower⊑ᵖlower′ =
      MLB-monotoneᵖ pC IWF.id★
        (lower-selected argument-plan) (lower-selected argument-plan′)
  in
  QTI.·⊑·ᵀ
    (compiled-dynamic-function-imprecision {ℓ = ℓ} L⊑L′ᵀ)
    (compiled-argument-cast-imprecision argument-plan argument-plan′
      argument-lower⊑ᵖlower′ N⊑N′ᵀ)
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.Λ⊑Λᴳ liftγ vV vV′ occA occB V⊑V′) =
  QTI.Λ⊑Λᵀ
    NTI.lift-store-[]
    (ctxImpToNu-lift liftγ)
    (compileᵀ-value (CtxWf-⤊ srcΓ-wf) vV
      (subst
        (λ Γ → _ ∣ Γ ⊢ᴳ _ ⦂ _)
        (GTI.srcCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-source-typing V⊑V′)))
    (compileᵀ-value (CtxWf-⤊ tgtΓ-wf) vV′
      (subst
        (λ Γ → _ ∣ Γ ⊢ᴳ _ ⦂ _)
        (GTI.tgtCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-target-typing V⊑V′)))
    (nu-term-imprecision-cong-terms
      (compile-context-subst-term-sym
        (GTI.srcCtxⁱ-lift liftγ)
        (CtxWf-⤊ srcΓ-wf)
        (GTI.gradual-term-imprecision-source-typing V⊑V′))
      (compile-context-subst-term-sym
        (GTI.tgtCtxⁱ-lift liftγ)
        (CtxWf-⤊ tgtΓ-wf)
        (GTI.gradual-term-imprecision-target-typing V⊑V′))
      (compile-preserves-term-imprecision-typed
        (subst (CtxWf _) (sym (GTI.srcCtxⁱ-lift liftγ))
          (CtxWf-⤊ srcΓ-wf))
        (subst (CtxWf _) (sym (GTI.tgtCtxⁱ-lift liftγ))
          (CtxWf-⤊ tgtΓ-wf))
        V⊑V′))
-- left-only Λ imprecision
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    rel@(GTI.Λ⊑ᴳ occ liftγ vV V⊑N′) =
  let
    V⊑N′ᵀ =
      compile-preserves-term-imprecision-typed
        (subst (CtxWf _) (sym (GTI.srcCtxⁱ-lift-left liftγ))
          (CtxWf-⤊ srcΓ-wf))
        (subst (CtxWf _) (sym (GTI.tgtCtxⁱ-lift-left liftγ))
          tgtΓ-wf)
        V⊑N′
  in
  QTI.Λ⊑ᵀ occ
    NTI.lift-left-store-[]
    (ctxImpToNu-lift-left liftγ)
    (compileᵀ-value (CtxWf-⤊ srcΓ-wf) vV
      (subst
        (λ Γ → _ ∣ Γ ⊢ᴳ _ ⦂ _)
        (GTI.srcCtxⁱ-lift-left liftγ)
        (GTI.gradual-term-imprecision-source-typing V⊑N′)))
    (nu-term-imprecision-cong-terms
      (compile-context-subst-term-sym
        (GTI.srcCtxⁱ-lift-left liftγ)
        (CtxWf-⤊ srcΓ-wf)
        (GTI.gradual-term-imprecision-source-typing V⊑N′))
      (compile-context-subst-term-sym
        (GTI.tgtCtxⁱ-lift-left liftγ)
        tgtΓ-wf
        (GTI.gradual-term-imprecision-target-typing V⊑N′))
      V⊑N′ᵀ)
-- synchronized type application
compile-preserves-term-imprecision-typed
    {γ = γ} srcΓ-wf tgtΓ-wf
    rel@(GTI.[]⊑[]ᴳ hA hT hB hT′ M⊑M′ q r) =
  let
    M⊑M′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        M⊑M′
  in
  QTI.ν⊑νᵀ hT hT′
    (reveal↑ (ν-reveal-conversion hT hA))
    (reveal↑ (ν-reveal-conversion hT′ hB))
    q
    (imp-lift q)
    NTI.lift-store-[]
    (nuCtx⇑-lift (ctxImpToNu γ))
    M⊑M′ᵀ
-- left-only type application
compile-preserves-term-imprecision-typed
    {γ = γ} srcΓ-wf tgtΓ-wf
    rel@(GTI.[]⊑ᴳ hA hT M⊑M′ q r) =
  let
    M⊑M′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        M⊑M′
  in
  QTI.ν⊑ᵀ hT
    (renameᵗ-preserves-WfTy hT TyRenameWf-suc)
    (reveal↑ (ν-reveal-conversion hT hA))
    NTI.lift-left-store-[]
    (nuCtx⇑ᴸ-lift (ctxImpToNu γ))
    M⊑M′ᵀ
compile-preserves-term-imprecision-typed
    srcΓ-wf tgtΓ-wf GTI.κ⊑κᴳ =
  QTI.κ⊑κᵀ
-- primitive addition
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    prim@(GTI.⊕⊑⊕ᴳ {op = addℕ} {ℓ = ℓ} L⊑L′ A~ℕ A′~ℕ
      N⊑N′ B~ℕ B′~ℕ) =
  let
    L⊑L′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        L⊑L′
    N⊑N′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        N⊑N′
  in
  QTI.⊕⊑⊕ᵀ
    (compiled-cast-nat-imprecision {ℓ = ℓ} A~ℕ A′~ℕ L⊑L′ᵀ)
    (compiled-cast-nat-imprecision {ℓ = ℓ} B~ℕ B′~ℕ N⊑N′ᵀ)

compile-preserves-term-imprecision :
  (srcΓ-wf : CtxWf Δᴸ (GTI.srcCtxⁱ γ)) →
  (tgtΓ-wf : CtxWf Δᴿ (GTI.tgtCtxⁱ γ)) →
  (M⊑M′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N = proj₁ (compileᵀ srcΓ-wf M⊢)
    N′ = proj₁ (compileᵀ tgtΓ-wf M′⊢)
  in
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ ctxImpToNu γ
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p
compile-preserves-term-imprecision
    srcΓ-wf tgtΓ-wf M⊑M′ =
  compile-preserves-term-imprecision-typed
    srcΓ-wf
    tgtΓ-wf
    M⊑M′
