module Preservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (cong; cong₂; sym; trans)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (zero; suc; _≟_)
open import Data.Nat.Base using (_<_; z<s; s<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)

open import PolyBlame
open import Ctx
open import Store public
open import TypeSubst 

------------------------------------------------------------------------
-- Term renaming and substitution infrastructure
------------------------------------------------------------------------

rename-renameˢᵀ :
  {ρ : Rename} {ϱ : Renameˢ} {M : Term} →
  rename ρ (renameˢᵀ ϱ M) ≡ renameˢᵀ ϱ (rename ρ M)
rename-renameˢᵀ {ρ} {ϱ} {` x} = refl
rename-renameˢᵀ {ρ} {ϱ} {ƛ A ⇒ N} =
  cong (λ N' → ƛ (renameˢ ϱ A) ⇒ N')
       (rename-renameˢᵀ {ρ = ext ρ} {ϱ = ϱ} {M = N})
rename-renameˢᵀ {ρ} {ϱ} {L · M} =
  cong₂ _·_ (rename-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = L})
            (rename-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = M})
rename-renameˢᵀ {ρ} {ϱ} {Λ N} =
  cong Λ_ (rename-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = N})
rename-renameˢᵀ {ρ} {ϱ} {L ·α α} =
  cong (λ L' → L' ·α (ϱ α))
       (rename-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = L})
rename-renameˢᵀ {ρ} {ϱ} {ν:= A ∙ N} =
  cong (λ N' → ν:= (renameˢ ϱ A) ∙ N')
       (rename-renameˢᵀ {ρ = ρ} {ϱ = extˢ ϱ} {M = N})
rename-renameˢᵀ {ρ} {ϱ} {$ κ} = refl
rename-renameˢᵀ {ρ} {ϱ} {M ⊕[ op ] N} =
  cong₂ (λ M' N' → M' ⊕[ op ] N')
        (rename-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = M})
        (rename-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = N})
rename-renameˢᵀ {ρ} {ϱ} {M at up p} =
  cong (λ M' → M' at up (renameImpˢ ϱ p))
       (rename-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = M})
rename-renameˢᵀ {ρ} {ϱ} {M at down p} =
  cong (λ M' → M' at down (renameImpˢ ϱ p))
       (rename-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = M})
rename-renameˢᵀ {ρ} {ϱ} {blame} = refl

renameᵀ-renameˢᵀ :
  {ρ : Renameᵗ} {ϱ : Renameˢ} {M : Term} →
  renameᵀ ρ (renameˢᵀ ϱ M) ≡ renameˢᵀ ϱ (renameᵀ ρ M)
renameᵀ-renameˢᵀ {ρ} {ϱ} {` x} = refl
renameᵀ-renameˢᵀ {ρ} {ϱ} {ƛ A ⇒ N} =
  cong₂ ƛ_⇒_
        (renameᵗ-renameˢ {ρ = ρ} {ϱ = ϱ} {A = A})
        (renameᵀ-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = N})
renameᵀ-renameˢᵀ {ρ} {ϱ} {L · M} =
  cong₂ _·_
        (renameᵀ-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = L})
        (renameᵀ-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = M})
renameᵀ-renameˢᵀ {ρ} {ϱ} {Λ N} =
  cong Λ_ (renameᵀ-renameˢᵀ {ρ = extᵗ ρ} {ϱ = ϱ} {M = N})
renameᵀ-renameˢᵀ {ρ} {ϱ} {L ·α α} =
  cong (λ L' → L' ·α (ϱ α))
       (renameᵀ-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = L})
renameᵀ-renameˢᵀ {ρ} {ϱ} {ν:= A ∙ N} =
  cong₂ ν:=_∙_
        (renameᵗ-renameˢ {ρ = ρ} {ϱ = ϱ} {A = A})
        (renameᵀ-renameˢᵀ {ρ = ρ} {ϱ = extˢ ϱ} {M = N})
renameᵀ-renameˢᵀ {ρ} {ϱ} {$ κ} = refl
renameᵀ-renameˢᵀ {ρ} {ϱ} {M ⊕[ op ] N} =
  cong₂ (λ M' N' → M' ⊕[ op ] N')
        (renameᵀ-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = M})
        (renameᵀ-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = N})
renameᵀ-renameˢᵀ {ρ} {ϱ} {M at up p} =
  cong₂ (λ M' p' → M' at up p')
        (renameᵀ-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = M})
        (renameImpᵗ-renameImpˢ {ρ = ρ} {ϱ = ϱ} {p = p})
renameᵀ-renameˢᵀ {ρ} {ϱ} {M at down p} =
  cong₂ (λ M' p' → M' at down p')
        (renameᵀ-renameˢᵀ {ρ = ρ} {ϱ = ϱ} {M = M})
        (renameImpᵗ-renameImpˢ {ρ = ρ} {ϱ = ϱ} {p = p})
renameᵀ-renameˢᵀ {ρ} {ϱ} {blame} = refl

typing-rename :
  {Δ : TyCtx} {Σ : Store} {Γ Γ' : Ctx} {M : Term} {A : Ty} {ρ : Rename} →
  RenameWf Γ Γ' ρ →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ⊢ Γ' ⊢ rename ρ M ⦂ A
typing-rename hρ (⊢` h) = ⊢` (hρ h)
typing-rename hρ (⊢ƛ hA hN) =
  ⊢ƛ hA (typing-rename (RenameWf-ext hρ) hN)
typing-rename hρ (⊢· hL hM) =
  ⊢· (typing-rename hρ hL) (typing-rename hρ hM)
typing-rename {Γ = Γ} {Γ' = Γ'} {ρ = ρ} hρ (⊢Λ hN) =
  ⊢Λ (typing-rename hρ' hN)
  where
    hρ' : RenameWf (⤊ Γ) (⤊ Γ') ρ
    hρ' h with lookup-map-inv h
    ... | A , (hA , eq)
      rewrite eq = lookup-map-renameᵗ (hρ hA)
typing-rename hρ (⊢·α hL hα) =
  ⊢·α (typing-rename hρ hL) hα
typing-rename {Γ = Γ} {Γ' = Γ'} {ρ = ρ} hρ (⊢ν hA hN hB) =
  ⊢ν hA (typing-rename hρˢ hN) hB
  where
    hρˢ : RenameWf (⤊ˢ Γ) (⤊ˢ Γ') ρ
    hρˢ h with lookup-map-inv h
    ... | A , (hA , eq)
      rewrite eq = lookup-map-renameˢ (hρ hA)
typing-rename hρ ⊢$ = ⊢$
typing-rename hρ (⊢⊕ hM hN) =
  ⊢⊕ (typing-rename hρ hM) (typing-rename hρ hN)
typing-rename hρ (⊢cast-up hM hp) =
  ⊢cast-up (typing-rename hρ hM) hp
typing-rename hρ (⊢cast-down hM hp) =
  ⊢cast-down (typing-rename hρ hM) hp
typing-rename hρ (⊢blame hA) = ⊢blame hA

rename-shift :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {M : Term} {A B : Ty} →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ⊢ (B ∷ Γ) ⊢ rename suc M ⦂ A
rename-shift hM = typing-rename (λ h → S h) hM

renameˢ-constTy :
  {ρ : Renameˢ} {κ : Const} →
  renameˢ ρ (constTy κ) ≡ constTy κ
renameˢ-constTy {κ = κℕ n} = refl

postulate
  lookupRenameˢ-lift-star :
    ∀ {ρ : Renameˢ} {Σ₀ Σ₁ : Store} →
    LookupRenameˢ ρ Σ₀ Σ₁ →
    LookupRenameˢ (extˢ ρ) (`★ ∷ Σ₀) (`★ ∷ Σ₁)

  lookupRenameˢ-lift-cons-shift :
    ∀ {ρ : Renameˢ} {Σ₀ Σ₁ : Store} {C : Ty} →
    LookupRenameˢ ρ Σ₀ Σ₁ →
    LookupRenameˢ (extˢ ρ)
      (C ∷ ⟰ˢ Σ₀)
      (renameˢ ρ C ∷ ⟰ˢ Σ₁)

typing-renameˢᵀ :
  {Δ : TyCtx} {ρ : Renameˢ} {Σ₀ Σ₁ : Store}
  {Γ : Ctx} {M : Term} {A : Ty} →
  LookupRenameˢ ρ Σ₀ Σ₁ →
  Δ ∣ Σ₀ ⊢ Γ ⊢ M ⦂ A →
  Δ ∣ Σ₁ ⊢ map (renameˢ ρ) Γ ⊢ renameˢᵀ ρ M ⦂ renameˢ ρ A
typing-renameˢᵀ hρ (⊢` h) =
  ⊢` (lookup-map-renameˢ h)
typing-renameˢᵀ hρ (⊢ƛ hA hN) =
  ⊢ƛ
    (renameˢ-preserves-WfTy lookupRenameˢ-lift-star hρ hA)
    (typing-renameˢᵀ hρ hN)
typing-renameˢᵀ hρ (⊢· hL hM) =
  ⊢·
    (typing-renameˢᵀ hρ hL)
    (typing-renameˢᵀ hρ hM)
typing-renameˢᵀ
               {Δ = Δ} {ρ = ρ} {Σ₁ = Σ₁} {Γ = Γ}
               hρ (⊢Λ hN) =
  ⊢Λ
    (Eq.subst
      (λ Ψ → (suc Δ) ∣ renameStoreᵗ suc Σ₁ ⊢ Ψ ⊢
               renameˢᵀ ρ _ ⦂ renameˢ ρ _)
      (map-renameᵗ-renameˢ {ρ = suc} {ϱ = ρ} Γ)
      (typing-renameˢᵀ
        (lookupRenameˢ-suc hρ)
        hN))
typing-renameˢᵀ
               {ρ = ρ} {Σ₁ = Σ₁} {Γ = Γ}
               hρ (⊢·α {L = L} {A = A} {α = α} hL hα) =
  Eq.subst
    (λ T → _ ∣ Σ₁ ⊢ map (renameˢ ρ) Γ ⊢ renameˢᵀ ρ L ·α (ρ α) ⦂ T)
    (sym (renameˢ-[]ᵗ-commute ρ A α))
    (⊢·α
      (typing-renameˢᵀ hρ hL)
      (hρ hα))
typing-renameˢᵀ
               {Δ = Δ} {ρ = ρ} {Σ₁ = Σ₁} {Γ = Γ}
               hρ (⊢ν {A = A} {B = B} {N = N} hA hN hB) =
  ⊢ν
    (renameˢ-preserves-WfTy lookupRenameˢ-lift-star hρ hA)
    (Eq.subst
      (λ T → Δ ∣ (renameˢ ρ A ∷ ⟰ˢ Σ₁) ⊢ ⤊ˢ (map (renameˢ ρ) Γ) ⊢
               renameˢᵀ (extˢ ρ) N ⦂ T)
      (renameˢ-commute-suc ρ B)
      (Eq.subst
        (λ Ψ → Δ ∣ (renameˢ ρ A ∷ ⟰ˢ Σ₁) ⊢ Ψ ⊢
                 renameˢᵀ (extˢ ρ) N ⦂ renameˢ (extˢ ρ) (⇑ˢ B))
        (map-renameˢ-commute-suc ρ Γ)
        (typing-renameˢᵀ
          (lookupRenameˢ-lift-cons-shift hρ)
          hN)))
    (renameˢ-preserves-WfTy lookupRenameˢ-lift-star hρ hB)
typing-renameˢᵀ hρ ⊢$ =
  Eq.subst
    (λ T → _ ∣ _ ⊢ _ ⊢ _ ⦂ T)
    (sym renameˢ-constTy)
    ⊢$
typing-renameˢᵀ hρ (⊢⊕ hM hN) =
  ⊢⊕
    (typing-renameˢᵀ hρ hM)
    (typing-renameˢᵀ hρ hN)
typing-renameˢᵀ hρ (⊢cast-up hM hp) =
  ⊢cast-up
    (typing-renameˢᵀ hρ hM)
    (renameImpˢ-preserves-typing lookupRenameˢ-lift-star hρ hp)
typing-renameˢᵀ hρ (⊢cast-down hM hp) =
  ⊢cast-down
    (typing-renameˢᵀ hρ hM)
    (renameImpˢ-preserves-typing lookupRenameˢ-lift-star hρ hp)
typing-renameˢᵀ hρ (⊢blame hA) =
  ⊢blame (renameˢ-preserves-WfTy lookupRenameˢ-lift-star hρ hA)

typing-singleSealEnv-fresh :
  ∀ {Δ Σ Γ A B N} →
  Δ ∣ (A ∷ ⟰ˢ Σ) ⊢ ⤊ˢ Γ ⊢ N ⦂ ⇑ˢ B →
  Δ ∣ extendStore Σ A ⊢ Γ ⊢ renameˢᵀ (singleSealEnv (fresh Σ)) N ⦂ B
typing-singleSealEnv-fresh {Δ} {Σ} {Γ} {A} {B} {N} hN =
  Eq.subst
    (λ Ψ → Δ ∣ extendStore Σ A ⊢ Ψ ⊢ renameˢᵀ (singleSealEnv (fresh Σ)) N ⦂ B)
    (map-singleSealEnv-suc-cancel (fresh Σ) Γ)
    (Eq.subst
      (λ T → Δ ∣ extendStore Σ A ⊢
               map (renameˢ (singleSealEnv (fresh Σ))) (⤊ˢ Γ) ⊢
               renameˢᵀ (singleSealEnv (fresh Σ)) N ⦂ T)
      (singleSealEnv-suc-cancel (fresh Σ) B)
      (typing-renameˢᵀ single-fresh-lookup hN))
  where
    postulate
      single-fresh-lookup :
        LookupRenameˢ (singleSealEnv (fresh Σ))
          (A ∷ ⟰ˢ Σ)
          (extendStore Σ A)

nu-up-body-preserve :
  ∀ {Σ V p A B} →
  0 ∣ Σ ⊢ [] ⊢ V ⦂ `∀ A →
  0 ∣ (`★ ∷ ⟰ˢ Σ) ⊢ᵖ p ⦂ ((⇑ˢ A) [ ｀ zero ]ᵗ) ⊑ ⇑ˢ B →
  0 ∣ (`★ ∷ ⟰ˢ Σ) ⊢ [] ⊢
    (((renameˢᵀ suc V) ·α zero) at up ((renameImpˢ suc p) [ zero ]ᴾα)) ⦂ ⇑ˢ B
nu-up-body-preserve {Σ} {V} {p} {A} {B} hV hp =
  ⊢cast-up
    (⊢·α hV↑ Zˢ)
    hImp
  where
    postulate
      suc-lookup :
        LookupRenameˢ suc Σ (`★ ∷ ⟰ˢ Σ)

      hImp :
        0 ∣ (`★ ∷ ⟰ˢ Σ) ⊢ᵖ ((renameImpˢ suc p) [ zero ]ᴾα) ⦂
          ((⇑ˢ A) [ ｀ zero ]ᵗ) ⊑ ⇑ˢ B

    hV↑ :
      0 ∣ (`★ ∷ ⟰ˢ Σ) ⊢ [] ⊢ renameˢᵀ suc V ⦂ `∀ (⇑ˢ A)
    hV↑ =
      typing-renameˢᵀ suc-lookup hV

SubstWf : TyCtx → Store → Ctx → Ctx → Subst → Set
SubstWf Δ Σ Γ Γ' σ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Σ ⊢ Γ' ⊢ σ x ⦂ A

SubstWf-exts :
  {Δ : TyCtx} {Σ : Store} {Γ Γ' : Ctx} {B : Ty} {σ : Subst} →
  SubstWf Δ Σ Γ Γ' σ →
  SubstWf Δ Σ (B ∷ Γ) (B ∷ Γ') (exts σ)
SubstWf-exts hσ Z = ⊢` Z
SubstWf-exts hσ (S h) = rename-shift (hσ h)

nu-down-preserve :
  ∀ {Δ Σ α p A B C} →
  Δ ∣ (`★ ∷ ⟰ˢ Σ) ⊢ᵖ p ⦂ ((⇑ˢ A) [ ｀ zero ]ᵗ) ⊑ ⇑ˢ B →
  Σ ∋ˢ α ⦂ C →
  Δ ∣ Σ ⊢ᵖ sealToTag α (openImpˢ α p) ⦂ A [ ｀ α ]ᵗ ⊑ B
nu-down-preserve {Δ = Δ} {Σ = Σ} {α = α} {p = p} {A = A} {B = B} hp hβ =
  Eq.subst
    (λ T → Δ ∣ Σ ⊢ᵖ sealToTag α (openImpˢ α p) ⦂ T ⊑ B)
    source-eq
    (Eq.subst
      (λ T → Δ ∣ Σ ⊢ᵖ sealToTag α (openImpˢ α p) ⦂
         renameˢ (singleSealEnv α) (((⇑ˢ A) [ ｀ zero ]ᵗ)) ⊑ T)
      target-eq
      (open-preserve-imp open-lookup hp))
  where
    postulate
      open-lookup :
        ∀ {α' C} →
        (`★ ∷ ⟰ˢ Σ) ∋ˢ α' ⦂ C →
        Σ ∋ˢ singleSealEnv α α' ⦂ renameˢ (singleSealEnv α) C

      lift-ext-renaming :
        ∀ {ρ : Renameˢ} {Σ₀ Σ₁ : Store} →
        LookupRenameˢ ρ Σ₀ Σ₁ →
        LookupRenameˢ (extˢ ρ) (`★ ∷ Σ₀) (`★ ∷ Σ₁)

    renameˢ-inst-eq :
      (ρ : Renameˢ) (A : Ty) →
      renameˢ (extˢ ρ) (((⇑ˢ A) [ ｀ zero ]ᵗ)) ≡
      ((⇑ˢ (renameˢ ρ A)) [ ｀ zero ]ᵗ)
    renameˢ-inst-eq ρ A =
      trans
        (renameˢ-[]ᵗ-commute (extˢ ρ) (⇑ˢ A) zero)
        (cong (λ T → T [ ｀ zero ]ᵗ) (renameˢ-commute-suc ρ A))

    renameˢ-target-eq :
      (ρ : Renameˢ) (B : Ty) →
      renameˢ (extˢ ρ) (⇑ˢ B) ≡ ⇑ˢ (renameˢ ρ B)
    renameˢ-target-eq = renameˢ-commute-suc

    sealToTag-self-id★ :
      (α : Seal) →
      sealToTag α (sealImp α id★) ≡ injTag (idα α) (G-α α)
    sealToTag-self-id★ α with α ≟ α
    sealToTag-self-id★ α | yes _ = refl
    sealToTag-self-id★ α | no neq = ⊥-elim (neq refl)

    sealToTag-id★-yes :
      (x y : Seal) →
      x ≡ y →
      sealToTag x (sealImp y id★) ≡ injTag (idα x) (G-α x)
    sealToTag-id★-yes x .x refl = sealToTag-self-id★ x

    sealToTag-id★-no :
      (x y : Seal) →
      (x ≡ y → ⊥) →
      sealToTag x (sealImp y id★) ≡ sealImp y id★
    sealToTag-id★-no x y neq with x ≟ y
    sealToTag-id★-no x y neq | yes eq = ⊥-elim (neq eq)
    sealToTag-id★-no x y neq | no _ = refl

    mutual
      sealToTag-preserves-cimp :
        {Δ' : TyCtx} {Σ : Store} {g : CImp} {A B : Ty} {α : Seal} →
        Δ' ∣ Σ ⊢ᶜ g ⦂ A ⊑ B →
        Δ' ∣ Σ ⊢ᶜ sealToTagC α g ⦂ A ⊑ B
      sealToTag-preserves-cimp (⊢idα hα) = ⊢idα hα
      sealToTag-preserves-cimp (⊢idX x<Δ) = ⊢idX x<Δ
      sealToTag-preserves-cimp ⊢idι = ⊢idι
      sealToTag-preserves-cimp (⊢→ᵖ hp hq) =
        ⊢→ᵖ
          (sealToTag-preserves-imp hp)
          (sealToTag-preserves-imp hq)
      sealToTag-preserves-cimp (⊢∀ᵖ hp) =
        ⊢∀ᵖ (sealToTag-preserves-imp hp)

      sealToTag-preserves-imp :
        {Δ' : TyCtx} {Σ : Store} {p : Imp} {A B : Ty} {α : Seal} →
        Δ' ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
        Δ' ∣ Σ ⊢ᵖ sealToTag α p ⦂ A ⊑ B
      sealToTag-preserves-imp (⊢⌈⌉ hg) =
        ⊢⌈⌉ (sealToTag-preserves-cimp hg)
      sealToTag-preserves-imp ⊢id★ = ⊢id★
      sealToTag-preserves-imp (⊢tag hg) =
        ⊢tag (sealToTag-preserves-cimp hg)
      sealToTag-preserves-imp {α = α} (⊢seal {α = β} {p = p} hα hp) with hp
      sealToTag-preserves-imp {α = α} (⊢seal {α = β} {p = p} hα hp) | ⊢id★ with α ≟ β
      sealToTag-preserves-imp {Δ' = Δ'} {Σ = Σ} {α = α}
        (⊢seal {α = β} {p = p} hα hp) | ⊢id★ | yes eq =
        Eq.subst
          (λ src → Δ' ∣ Σ ⊢ᵖ injTag (idα α) (G-α α) ⦂ src ⊑ `★)
          (cong (λ α' → ｀ α') eq)
          (⊢tag (⊢idα hb))
        where
          hb : Σ ∋ˢ α ⦂ `★
          hb = Eq.subst (λ X → Σ ∋ˢ X ⦂ `★) (sym eq) hα
      sealToTag-preserves-imp {α = α} (⊢seal {α = β} {p = p} hα hp) | ⊢id★ | no neq =
        ⊢seal hα ⊢id★
      sealToTag-preserves-imp {α = α} (⊢seal {α = β} {p = p} hα hp) | ⊢⌈⌉ hg =
        ⊢seal hα (sealToTag-preserves-imp (⊢⌈⌉ hg))
      sealToTag-preserves-imp {α = α} (⊢seal {α = β} {p = p} hα hp) | ⊢tag hg =
        ⊢seal hα (sealToTag-preserves-imp (⊢tag hg))
      sealToTag-preserves-imp {α = α} (⊢seal {α = β} {p = p} hα hp) | ⊢seal hα' hp' =
        ⊢seal hα (sealToTag-preserves-imp (⊢seal hα' hp'))
      sealToTag-preserves-imp {α = α} (⊢seal {α = β} {p = p} hα hp) | ⊢ν hp' hA hB =
        ⊢seal hα (sealToTag-preserves-imp (⊢ν hp' hA hB))
      sealToTag-preserves-imp {α = α} (⊢ν hp hA hB) =
        ⊢ν
          (sealToTag-preserves-imp hp)
          hA
          hB

    open-preserve-imp :
      {Δ' : TyCtx} {ρ : Renameˢ} {Σ₀ Σ₁ : Store} {p : Imp} {A B : Ty} {α : Seal} →
      LookupRenameˢ ρ Σ₀ Σ₁ →
      Δ' ∣ Σ₀ ⊢ᵖ p ⦂ A ⊑ B →
      Δ' ∣ Σ₁ ⊢ᵖ sealToTag α (renameImpˢ ρ p) ⦂ renameˢ ρ A ⊑ renameˢ ρ B
    open-preserve-imp hlookup hp =
      sealToTag-preserves-imp
        (renameImpˢ-preserves-typing lift-ext-renaming hlookup hp)

    source-eq :
      renameˢ (singleSealEnv α) (((⇑ˢ A) [ ｀ zero ]ᵗ)) ≡ A [ ｀ α ]ᵗ
    source-eq = singleSealEnv-source-eq α A

    target-eq :
      renameˢ (singleSealEnv α) (⇑ˢ B) ≡ B
    target-eq = singleSealEnv-suc-cancel α B

renameᵗ-constTy :
  {ρ : Renameᵗ} {κ : Const} →
  renameᵗ ρ (constTy κ) ≡ constTy κ
renameᵗ-constTy {κ = κℕ n} = refl

typing-renameᵀ :
  {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx} {M : Term} {A : Ty} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
  Δ' ∣ renameStoreᵗ ρ Σ ⊢ map (renameᵗ ρ) Γ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A
typing-renameᵀ hρ (⊢` h) = ⊢` (lookup-map-renameᵗ h)
typing-renameᵀ hρ (⊢ƛ hA hN) =
  ⊢ƛ
    (renameᵗ-preserves-WfTy hA hρ)
    (typing-renameᵀ hρ hN)
typing-renameᵀ hρ (⊢· hL hM) =
  ⊢· (typing-renameᵀ hρ hL) (typing-renameᵀ hρ hM)
typing-renameᵀ {Δ = Δ} {Δ' = Δ'} {Σ = Σ} {Γ = Γ} {ρ = ρ} hρ (⊢Λ hN) =
  ⊢Λ (lift hN)
  where
    lift :
      {N : Term} {A : Ty} →
      (suc Δ) ∣ (renameStoreᵗ suc Σ) ⊢ (⤊ Γ) ⊢ N ⦂ A →
      (suc Δ') ∣ (renameStoreᵗ suc (renameStoreᵗ ρ Σ)) ⊢
      (⤊ (map (renameᵗ ρ) Γ)) ⊢
      renameᵀ (extᵗ ρ) N ⦂ renameᵗ (extᵗ ρ) A
    lift {N = N} {A = A} hN =
      Eq.subst
        (λ S → (suc Δ') ∣ S ⊢ ⤊ (map (renameᵗ ρ) Γ) ⊢
                 renameᵀ (extᵗ ρ) N ⦂ renameᵗ (extᵗ ρ) A)
        (map-renameStore-suc ρ Σ)
        (Eq.subst
          (λ Ψ → (suc Δ') ∣ renameStoreᵗ (extᵗ ρ) (renameStoreᵗ suc Σ) ⊢ Ψ ⊢
                   renameᵀ (extᵗ ρ) N ⦂ renameᵗ (extᵗ ρ) A)
          (map-renameᵗ-⤊ ρ Γ)
          (typing-renameᵀ (TyRenameWf-ext hρ) hN))

typing-renameᵀ {Δ = Δ} {Δ' = Δ'} {Σ = Σ} {Γ = Γ} {ρ = ρ} hρ (⊢·α hL hα) =
  lift hL hα
  where
    lift :
      {L : Term} {A B : Ty} {α : Seal} →
      Δ ∣ Σ ⊢ Γ ⊢ L ⦂ `∀ A →
      Σ ∋ˢ α ⦂ B →
      Δ' ∣ renameStoreᵗ ρ Σ ⊢ map (renameᵗ ρ) Γ ⊢ renameᵀ ρ L ·α α ⦂
      renameᵗ ρ (A [ ｀ α ]ᵗ)
    lift {L = L} {A = A} {α = α} hL hα =
      Eq.subst
        (λ T → Δ' ∣ renameStoreᵗ ρ Σ ⊢ map (renameᵗ ρ) Γ ⊢ renameᵀ ρ L ·α α ⦂ T)
        (sym (rename-[]ᵗ-commute ρ A (｀ α)))
        (⊢·α
          (typing-renameᵀ hρ hL)
          (lookupˢ-map-renameᵗ hα))

typing-renameᵀ {Δ = Δ} {Δ' = Δ'} {Σ = Σ} {Γ = Γ} {ρ = ρ}
              hρ (⊢ν hA hN hB) =
  ⊢ν
    (renameᵗ-preserves-WfTy hA hρ)
    (lift hN)
    (renameᵗ-preserves-WfTy hB hρ)
  where
    store-renameᵗ-renameˢ :
      (Σ₀ : Store) →
      renameStoreᵗ ρ (⟰ˢ Σ₀) ≡
      ⟰ˢ (renameStoreᵗ ρ Σ₀)
    store-renameᵗ-renameˢ [] = refl
    store-renameᵗ-renameˢ (C ∷ Σ₀) =
      cong₂ _∷_
        (renameᵗ-renameˢ {ρ = ρ} {ϱ = suc} {A = C})
        (store-renameᵗ-renameˢ Σ₀)

    lift :
      {N : Term} {A B : Ty} →
      Δ ∣ (A ∷ ⟰ˢ Σ) ⊢ ⤊ˢ Γ ⊢ N ⦂ ⇑ˢ B →
      Δ' ∣ (renameᵗ ρ A ∷ ⟰ˢ (renameStoreᵗ ρ Σ)) ⊢
      ⤊ˢ (map (renameᵗ ρ) Γ) ⊢
      renameᵀ ρ N ⦂ ⇑ˢ (renameᵗ ρ B)
    lift {N = N} {A = A} {B = B} hN =
      Eq.subst
        (λ S → Δ' ∣ (renameᵗ ρ A ∷ S) ⊢ ⤊ˢ (map (renameᵗ ρ) Γ) ⊢
                 renameᵀ ρ N ⦂ ⇑ˢ (renameᵗ ρ B))
        (store-renameᵗ-renameˢ Σ)
        (Eq.subst
          (λ Ψ → Δ' ∣ (renameᵗ ρ A ∷ renameStoreᵗ ρ (⟰ˢ Σ)) ⊢ Ψ ⊢
                   renameᵀ ρ N ⦂ ⇑ˢ (renameᵗ ρ B))
          (sym (map-renameᵗ-renameˢ {ρ = ρ} {ϱ = suc} Γ))
          (Eq.subst
            (λ T → Δ' ∣ (renameᵗ ρ A ∷ renameStoreᵗ ρ (⟰ˢ Σ)) ⊢
                     map (renameᵗ ρ) (⤊ˢ Γ) ⊢
                     renameᵀ ρ N ⦂ T)
            (renameᵗ-renameˢ {ρ = ρ} {ϱ = suc} {A = B})
            (typing-renameᵀ hρ hN)))
typing-renameᵀ hρ ⊢$ =
  Eq.subst
    (λ T → _ ∣ _ ⊢ _ ⊢ _ ⦂ T)
    (sym renameᵗ-constTy)
    ⊢$
typing-renameᵀ hρ (⊢⊕ hM hN) =
  ⊢⊕ (typing-renameᵀ hρ hM) (typing-renameᵀ hρ hN)
typing-renameᵀ hρ (⊢cast-up hM hp) =
  ⊢cast-up
    (typing-renameᵀ hρ hM)
    (renameImpᵗ-preserves-typing hρ hp)
typing-renameᵀ hρ (⊢cast-down hM hp) =
  ⊢cast-down
    (typing-renameᵀ hρ hM)
    (renameImpᵗ-preserves-typing hρ hp)
typing-renameᵀ hρ (⊢blame hA) =
  ⊢blame (renameᵗ-preserves-WfTy hA hρ)

typing-renameᵀ-suc :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {M : Term} {A : Ty} →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
  (suc Δ) ∣ (renameStoreᵗ suc Σ) ⊢ (⤊ Γ) ⊢ renameᵀ suc M ⦂ renameᵗ suc A
typing-renameᵀ-suc h = typing-renameᵀ suc-rename-wf h

data IsVar : Ty → Set where
  X-var : ∀ {X} → IsVar (＇ X)
  α-var : ∀ {α} → IsVar (｀ α)
  ι-var : ∀ {ι} → IsVar (‵ ι)

TySubstIsVar : Substᵗ → Set
TySubstIsVar σ = ∀ {X} → IsVar (σ X)

renameᵗ-preserves-IsVar :
  {A : Ty} {ρ : Renameᵗ} →
  IsVar A →
  IsVar (renameᵗ ρ A)
renameᵗ-preserves-IsVar X-var = X-var
renameᵗ-preserves-IsVar α-var = α-var
renameᵗ-preserves-IsVar ι-var = ι-var

renameˢ-preserves-IsVar :
  {A : Ty} {ρ : Renameˢ} →
  IsVar A →
  IsVar (renameˢ ρ A)
renameˢ-preserves-IsVar X-var = X-var
renameˢ-preserves-IsVar α-var = α-var
renameˢ-preserves-IsVar ι-var = ι-var

TySubstIsVar-exts :
  {σ : Substᵗ} →
  TySubstIsVar σ →
  TySubstIsVar (extsᵗ σ)
TySubstIsVar-exts hσ {zero} = X-var
TySubstIsVar-exts hσ {suc X} =
  renameᵗ-preserves-IsVar (hσ {X})

atomize-var-preserves-typing :
  {Δ' : TyCtx} {Σ : Store} {A : Ty} →
  WfTy Δ' Σ A →
  IsVar A →
  Δ' ∣ Σ ⊢ᶜ atomize A ⦂ A ⊑ A
atomize-var-preserves-typing {A = ＇ X} (wfX x<Δ) X-var = ⊢idX x<Δ
atomize-var-preserves-typing {A = ｀ a} (wfα hα) α-var = ⊢idα hα
atomize-var-preserves-typing {A = ‵ b} wfι ι-var = ⊢idι

TySubstWf-exts-same :
  {Δ Δ' : TyCtx} {Σ : Store} {σ : Substᵗ} →
  TySubstWf Δ Δ' Σ σ →
  TySubstWf (suc Δ) (suc Δ') Σ (extsᵗ σ)
TySubstWf-exts-same hσ {zero} z<s = wfX z<s
TySubstWf-exts-same hσ {suc X} (s<s x<Δ) =
  wfty-store-unshift
    (renameᵗ-preserves-WfTy (hσ x<Δ) suc-rename-wf)

postulate
  imp-substᵗ-preserves-typing-wf-ν :
    {Δ Δ' : TyCtx} {Σ : Store} {p : Imp} {A B : Ty} {σ : Substᵗ} →
    WfStore Σ →
    TySubstWf Δ Δ' Σ σ →
    TySubstIsVar σ →
    Δ ∣ (`★ ∷ ⟰ˢ Σ) ⊢ᵖ p ⦂ ((⇑ˢ A) [ ｀ zero ]ᵗ) ⊑ ⇑ˢ B →
    WfTy (suc Δ) Σ A →
    WfTy Δ Σ B →
    Δ' ∣ Σ ⊢ᵖ substImpᵗ σ (nuImp p) ⦂ substᵗ σ (`∀ A) ⊑ substᵗ σ B

  imp-substᵗ-preserves-typing-store-ν :
    {Δ Δ' : TyCtx} {Σ : Store} {p : Imp} {A B : Ty} {σ : Substᵗ} →
    TySubstWf Δ Δ' Σ σ →
    TySubstIsVar σ →
    Δ ∣ (`★ ∷ ⟰ˢ Σ) ⊢ᵖ p ⦂ ((⇑ˢ A) [ ｀ zero ]ᵗ) ⊑ ⇑ˢ B →
    WfTy (suc Δ) Σ A →
    WfTy Δ Σ B →
    Δ' ∣ substStoreᵗ σ Σ ⊢ᵖ substImpᵗ σ (nuImp p) ⦂ substᵗ σ (`∀ A) ⊑ substᵗ σ B

  typing-substᵀ-store-ν :
    {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx}
    {A B : Ty} {N : Term} {σ : Substᵗ} →
    TySubstWf Δ Δ' Σ σ →
    TySubstIsVar σ →
    WfTy Δ Σ A →
    Δ ∣ (A ∷ ⟰ˢ Σ) ⊢ ⤊ˢ Γ ⊢ N ⦂ ⇑ˢ B →
    WfTy Δ Σ B →
    Δ' ∣ substStoreᵗ σ Σ ⊢ map (substᵗ σ) Γ ⊢ substᵀ σ (ν:= A ∙ N) ⦂ substᵗ σ B

substᵗ-constTy :
  {σ : Substᵗ} {κ : Const} →
  substᵗ σ (constTy κ) ≡ constTy κ
substᵗ-constTy {κ = κℕ n} = refl

typing-store-unshift :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {M : Term} {A : Ty} →
  WfStore Σ →
  Δ ∣ renameStoreᵗ suc Σ ⊢ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A
typing-store-unshift {Δ = Δ} {Σ = Σ} {Γ = Γ} {M = M} {A = A} hΣ hM =
  Eq.subst
    (λ S → Δ ∣ S ⊢ Γ ⊢ M ⦂ A)
    (renameStore-suc-id hΣ)
    hM

imp-store-unshift :
  {Δ : TyCtx} {Σ : Store} {p : Imp} {A B : Ty} →
  WfStore Σ →
  Δ ∣ renameStoreᵗ suc Σ ⊢ᵖ p ⦂ A ⊑ B →
  Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B
imp-store-unshift {Δ = Δ} {Σ = Σ} {p = p} {A = A} {B = B} hΣ hp =
  Eq.subst
    (λ S → Δ ∣ S ⊢ᵖ p ⦂ A ⊑ B)
    (renameStore-suc-id hΣ)
    hp

mutual
  cimp-substᵗ-preserves-typing-wf :
    {Δ Δ' : TyCtx} {Σ : Store} {g : CImp} {A B : Ty} {σ : Substᵗ} →
    WfStore Σ →
    TySubstWf Δ Δ' Σ σ →
    TySubstIsVar σ →
    Δ ∣ Σ ⊢ᶜ g ⦂ A ⊑ B →
    Δ' ∣ Σ ⊢ᶜ substCImpᵗ σ g ⦂ substᵗ σ A ⊑ substᵗ σ B
  cimp-substᵗ-preserves-typing-wf wfΣ hσ hσv (⊢idα hα) =
    ⊢idα hα
  cimp-substᵗ-preserves-typing-wf {Δ' = Δ'} {Σ = Σ} {σ = σ}
    wfΣ hσ hσv (⊢idX {X = X} x<Δ) =
    atomize-var-preserves-typing {Δ' = Δ'} {Σ = Σ} {A = σ X}
      (hσ x<Δ)
      (hσv {X = X})
  cimp-substᵗ-preserves-typing-wf wfΣ hσ hσv ⊢idι = ⊢idι
  cimp-substᵗ-preserves-typing-wf wfΣ hσ hσv (⊢→ᵖ hp hq) =
    ⊢→ᵖ
      (imp-substᵗ-preserves-typing-wf wfΣ hσ hσv hp)
      (imp-substᵗ-preserves-typing-wf wfΣ hσ hσv hq)
  cimp-substᵗ-preserves-typing-wf wfΣ hσ hσv (⊢∀ᵖ hp) =
    ⊢∀ᵖ
      (imp-substᵗ-preserves-typing-wf
        (wfStore-rename-suc wfΣ)
        (TySubstWf-exts hσ)
        (λ {X} → TySubstIsVar-exts hσv {X = X})
        hp)

  imp-substᵗ-preserves-typing-wf :
    {Δ Δ' : TyCtx} {Σ : Store} {p : Imp} {A B : Ty} {σ : Substᵗ} →
    WfStore Σ →
    TySubstWf Δ Δ' Σ σ →
    TySubstIsVar σ →
    Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
    Δ' ∣ Σ ⊢ᵖ substImpᵗ σ p ⦂ substᵗ σ A ⊑ substᵗ σ B
  imp-substᵗ-preserves-typing-wf wfΣ hσ hσv (⊢⌈⌉ hg) =
    ⊢⌈⌉ (cimp-substᵗ-preserves-typing-wf wfΣ hσ hσv hg)
  imp-substᵗ-preserves-typing-wf wfΣ hσ hσv ⊢id★ = ⊢id★
  imp-substᵗ-preserves-typing-wf {Δ' = Δ'} {Σ = Σ} {σ = σ}
    wfΣ hσ hσv (⊢tag {g = g} {G = G} {A = A} hg) =
    ⊢tag
      (Eq.subst
        (λ T → Δ' ∣ Σ ⊢ᶜ substCImpᵗ σ g ⦂ substᵗ σ A ⊑ T)
        (subst-groundTy {σ = σ} {G = G})
        (cimp-substᵗ-preserves-typing-wf wfΣ hσ hσv hg))
  imp-substᵗ-preserves-typing-wf {Δ' = Δ'} {Σ = Σ} {σ = σ}
    wfΣ hσ hσv (⊢seal {α = a} {A = A} {B = B} {p = p} hα hp)
    with lookupˢ-wfty0 wfΣ hα
  ... | hA0 =
    ⊢seal
      hα
      (Eq.subst
        (λ T → Δ' ∣ Σ ⊢ᵖ substImpᵗ σ p ⦂ T ⊑ substᵗ σ B)
        (substᵗ-id-closed hA0)
        (imp-substᵗ-preserves-typing-wf wfΣ hσ hσv hp))
  imp-substᵗ-preserves-typing-wf {Δ' = Δ'} {Σ = Σ} {σ = σ}
    wfΣ hσ hσv (⊢ν {A = A} {B = B} hp hA hB) =
    imp-substᵗ-preserves-typing-wf-ν
      wfΣ hσ hσv hp hA hB

mutual
  cimp-substᵗ-preserves-typing-store :
    {Δ Δ' : TyCtx} {Σ : Store} {g : CImp} {A B : Ty} {σ : Substᵗ} →
    TySubstWf Δ Δ' Σ σ →
    TySubstIsVar σ →
    Δ ∣ Σ ⊢ᶜ g ⦂ A ⊑ B →
    Δ' ∣ substStoreᵗ σ Σ ⊢ᶜ substCImpᵗ σ g ⦂ substᵗ σ A ⊑ substᵗ σ B
  cimp-substᵗ-preserves-typing-store {σ = σ} hσ hσv (⊢idα hα) =
    ⊢idα (lookupˢ-map-substᵗ {σ = σ} hα)
  cimp-substᵗ-preserves-typing-store {Δ' = Δ'} {σ = σ}
    hσ hσv (⊢idX {X = X} x<Δ) =
    atomize-var-preserves-typing {Δ' = Δ'} {A = σ X}
      (wfty-store-substᵗ (hσ x<Δ))
      (hσv {X = X})
  cimp-substᵗ-preserves-typing-store hσ hσv ⊢idι = ⊢idι
  cimp-substᵗ-preserves-typing-store hσ hσv (⊢→ᵖ hp hq) =
    ⊢→ᵖ
      (imp-substᵗ-preserves-typing-store hσ hσv hp)
      (imp-substᵗ-preserves-typing-store hσ hσv hq)
  cimp-substᵗ-preserves-typing-store {Δ' = Δ'} {Σ = Σ} {σ = σ}
    hσ hσv (⊢∀ᵖ {p = p} {A = A} {B = B} hp) =
    ⊢∀ᵖ
      (Eq.subst
        (λ S → (suc Δ') ∣ S ⊢ᵖ substImpᵗ (extsᵗ σ) p ⦂
               substᵗ (extsᵗ σ) A ⊑ substᵗ (extsᵗ σ) B)
        (map-substStore-suc σ Σ)
        (imp-substᵗ-preserves-typing-store
          {Σ = renameStoreᵗ suc Σ}
          {σ = extsᵗ σ}
          (TySubstWf-exts hσ)
          (λ {X} → TySubstIsVar-exts hσv {X = X})
          hp))

  imp-substᵗ-preserves-typing-store :
    {Δ Δ' : TyCtx} {Σ : Store} {p : Imp} {A B : Ty} {σ : Substᵗ} →
    TySubstWf Δ Δ' Σ σ →
    TySubstIsVar σ →
    Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
    Δ' ∣ substStoreᵗ σ Σ ⊢ᵖ substImpᵗ σ p ⦂ substᵗ σ A ⊑ substᵗ σ B
  imp-substᵗ-preserves-typing-store hσ hσv (⊢⌈⌉ hg) =
    ⊢⌈⌉ (cimp-substᵗ-preserves-typing-store hσ hσv hg)
  imp-substᵗ-preserves-typing-store hσ hσv ⊢id★ = ⊢id★
  imp-substᵗ-preserves-typing-store {Δ' = Δ'} {σ = σ}
    hσ hσv (⊢tag {g = g} {G = G} {A = A} hg) =
    ⊢tag
      (Eq.subst
        (λ T → Δ' ∣ _ ⊢ᶜ substCImpᵗ σ g ⦂ substᵗ σ A ⊑ T)
        (subst-groundTy {σ = σ} {G = G})
        (cimp-substᵗ-preserves-typing-store hσ hσv hg))
  imp-substᵗ-preserves-typing-store {σ = σ}
    hσ hσv (⊢seal {p = p} hα hp) =
    ⊢seal
      (lookupˢ-map-substᵗ {σ = σ} hα)
      (imp-substᵗ-preserves-typing-store hσ hσv hp)
  imp-substᵗ-preserves-typing-store {Δ' = Δ'} {Σ = Σ} {σ = σ}
    hσ hσv (⊢ν {A = A} {B = B} {p = p} hp hA hB) =
    imp-substᵗ-preserves-typing-store-ν
      hσ hσv hp hA hB

typing-substᵀ-store :
  {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx} {M : Term} {A : Ty} {σ : Substᵗ} →
  TySubstWf Δ Δ' Σ σ →
  TySubstIsVar σ →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
  Δ' ∣ substStoreᵗ σ Σ ⊢ map (substᵗ σ) Γ ⊢ substᵀ σ M ⦂ substᵗ σ A
typing-substᵀ-store hσ hσv (⊢` h) =
  ⊢` (lookup-map-substᵗ h)
typing-substᵀ-store hσ hσv (⊢ƛ hA hN) =
  ⊢ƛ
    (substᵗ-preserves-WfTy-store hA hσ)
    (typing-substᵀ-store hσ hσv hN)
typing-substᵀ-store hσ hσv (⊢· hL hM) =
  ⊢·
    (typing-substᵀ-store hσ hσv hL)
    (typing-substᵀ-store hσ hσv hM)
typing-substᵀ-store {Δ = Δ} {Δ' = Δ'} {Σ = Σ} {Γ = Γ} {σ = σ}
  hσ hσv (⊢Λ {N = N} {A = A} hN) =
  ⊢Λ
    (Eq.subst
      (λ S → (suc Δ') ∣ S ⊢ ⤊ (map (substᵗ σ) Γ) ⊢
             substᵀ (extsᵗ σ) N ⦂ substᵗ (extsᵗ σ) A)
      (map-substStore-suc σ Σ)
      (Eq.subst
        (λ Ψ → (suc Δ') ∣ substStoreᵗ (extsᵗ σ) (renameStoreᵗ suc Σ) ⊢ Ψ ⊢
               substᵀ (extsᵗ σ) N ⦂ substᵗ (extsᵗ σ) A)
        (map-substᵗ-⤊ σ Γ)
        (typing-substᵀ-store
          {Σ = renameStoreᵗ suc Σ}
          {σ = extsᵗ σ}
          (TySubstWf-exts hσ)
          (λ {X} → TySubstIsVar-exts hσv {X = X})
          hN)))
typing-substᵀ-store {Δ' = Δ'} {σ = σ} hσ hσv
  (⊢·α {L = L} {A = A} {α = α} hL hα) =
  Eq.subst
    (λ T → Δ' ∣ _ ⊢ _ ⊢ substᵀ σ L ·α α ⦂ T)
    (sym (subst-[]ᵗ-commute σ A (｀ α)))
    (⊢·α
      (typing-substᵀ-store hσ hσv hL)
      (lookupˢ-map-substᵗ {σ = σ} hα))
typing-substᵀ-store {Δ' = Δ'} {Σ = Σ} {Γ = Γ} {σ = σ}
  hσ hσv (⊢ν {A = A} hA hN hB) =
  typing-substᵀ-store-ν
    hσ hσv hA hN hB
typing-substᵀ-store {Δ' = Δ'} {σ = σ} hσ hσv (⊢$ {κ = κ}) =
  Eq.subst
    (λ T → Δ' ∣ _ ⊢ _ ⊢ ($ κ) ⦂ T)
    (sym substᵗ-constTy)
    ⊢$
typing-substᵀ-store hσ hσv (⊢⊕ hM hN) =
  ⊢⊕
    (typing-substᵀ-store hσ hσv hM)
    (typing-substᵀ-store hσ hσv hN)
typing-substᵀ-store hσ hσv (⊢cast-up hM hp) =
  ⊢cast-up
    (typing-substᵀ-store hσ hσv hM)
    (imp-substᵗ-preserves-typing-store hσ hσv hp)
typing-substᵀ-store hσ hσv (⊢cast-down hM hp) =
  ⊢cast-down
    (typing-substᵀ-store hσ hσv hM)
    (imp-substᵗ-preserves-typing-store hσ hσv hp)
typing-substᵀ-store hσ hσv (⊢blame hA) =
  ⊢blame (substᵗ-preserves-WfTy-store hA hσ)

postulate
  typing-substᵀ-ν-wf :
    {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx}
    {A B : Ty} {N : Term} {σ : Substᵗ} →
    WfStore Σ →
    TySubstWf Δ Δ' Σ σ →
    TySubstIsVar σ →
    WfTy Δ Σ A →
    Δ ∣ (A ∷ ⟰ˢ Σ) ⊢ ⤊ˢ Γ ⊢ N ⦂ ⇑ˢ B →
    WfTy Δ Σ B →
    Δ' ∣ Σ ⊢ map (substᵗ σ) Γ ⊢
      ν:= substᵗ σ A ∙ substᵀ (liftSealSubstᵗ σ) N ⦂ substᵗ σ B

typing-substᵀ-wf :
  {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx} {M : Term} {A : Ty} {σ : Substᵗ} →
  WfStore Σ →
  TySubstWf Δ Δ' Σ σ →
  TySubstIsVar σ →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
  Δ' ∣ Σ ⊢ map (substᵗ σ) Γ ⊢ substᵀ σ M ⦂ substᵗ σ A
typing-substᵀ-wf wfΣ hσ hσv (⊢` h) =
  ⊢` (lookup-map-substᵗ h)
typing-substᵀ-wf wfΣ hσ hσv (⊢ƛ hA hN) =
  ⊢ƛ
    (substᵗ-preserves-WfTy hA hσ)
    (typing-substᵀ-wf wfΣ hσ hσv hN)
typing-substᵀ-wf wfΣ hσ hσv (⊢· hL hM) =
  ⊢·
    (typing-substᵀ-wf wfΣ hσ hσv hL)
    (typing-substᵀ-wf wfΣ hσ hσv hM)
typing-substᵀ-wf {Δ = Δ} {Δ' = Δ'} {Σ = Σ} {Γ = Γ} {σ = σ}
  wfΣ hσ hσv (⊢Λ {N = N} {A = A} hN) =
  ⊢Λ
    (Eq.subst
      (λ Ψ → (suc Δ') ∣ renameStoreᵗ suc Σ ⊢ Ψ ⊢
               substᵀ (extsᵗ σ) N ⦂ substᵗ (extsᵗ σ) A)
      (map-substᵗ-⤊ σ Γ)
      (typing-substᵀ-wf
        (wfStore-rename-suc wfΣ)
        (TySubstWf-exts hσ)
        (λ {X} → TySubstIsVar-exts hσv {X = X})
        hN))
typing-substᵀ-wf {Δ' = Δ'} {Σ = Σ} {Γ = Γ} {σ = σ}
  wfΣ hσ hσv (⊢·α {L = L} {A = A} {α = α} hL hα) =
  Eq.subst
    (λ T → Δ' ∣ Σ ⊢ map (substᵗ σ) Γ ⊢ substᵀ σ L ·α α ⦂ T)
    (sym (subst-[]ᵗ-commute σ A (｀ α)))
    (⊢·α
      (typing-substᵀ-wf wfΣ hσ hσv hL)
      hα)
typing-substᵀ-wf wfΣ hσ hσv (⊢ν hA hN hB) =
  typing-substᵀ-ν-wf wfΣ hσ hσv hA hN hB
typing-substᵀ-wf {Δ' = Δ'} wfΣ hσ hσv (⊢$ {κ = κ}) =
  Eq.subst
    (λ T → Δ' ∣ _ ⊢ _ ⊢ ($ κ) ⦂ T)
    (sym substᵗ-constTy)
    ⊢$
typing-substᵀ-wf wfΣ hσ hσv (⊢⊕ hM hN) =
  ⊢⊕
    (typing-substᵀ-wf wfΣ hσ hσv hM)
    (typing-substᵀ-wf wfΣ hσ hσv hN)
typing-substᵀ-wf wfΣ hσ hσv (⊢cast-up hM hp) =
  ⊢cast-up
    (typing-substᵀ-wf wfΣ hσ hσv hM)
    (imp-substᵗ-preserves-typing-wf wfΣ hσ hσv hp)
typing-substᵀ-wf wfΣ hσ hσv (⊢cast-down hM hp) =
  ⊢cast-down
    (typing-substᵀ-wf wfΣ hσ hσv hM)
    (imp-substᵗ-preserves-typing-wf wfΣ hσ hσv hp)
typing-substᵀ-wf wfΣ hσ hσv (⊢blame hA) =
  ⊢blame (substᵗ-preserves-WfTy hA hσ)

typing-substᵀ :
  {Δ Δ' : TyCtx} {Σ : Store} {Γ : Ctx} {M : Term} {A : Ty} {σ : Substᵗ} →
  WfStore Σ →
  TySubstWf Δ Δ' Σ σ →
  TySubstIsVar σ →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
  Δ' ∣ Σ ⊢ map (substᵗ σ) Γ ⊢ substᵀ σ M ⦂ substᵗ σ A
typing-substᵀ = typing-substᵀ-wf

imp-substᵗ-preserves-typing :
  {Δ Δ' : TyCtx} {Σ : Store} {p : Imp} {A B : Ty} {σ : Substᵗ} →
  WfStore Σ →
  TySubstWf Δ Δ' Σ σ →
  TySubstIsVar σ →
  Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
  Δ' ∣ Σ ⊢ᵖ substImpᵗ σ p ⦂ substᵗ σ A ⊑ substᵗ σ B
imp-substᵗ-preserves-typing = imp-substᵗ-preserves-typing-wf

singleTySubstWf :
  {Δ : TyCtx} {Σ : Store} {B : Ty} →
  WfTy Δ Σ B →
  TySubstWf (suc Δ) Δ Σ (singleTyEnv B)
singleTySubstWf hB {zero} z<s = hB
singleTySubstWf hB {suc X} (s<s x<Δ) = wfX x<Δ

singleTySubstWf-α :
  {Δ : TyCtx} {Σ : Store} {α : Seal} {B : Ty} →
  Σ ∋ˢ α ⦂ B →
  TySubstWf (suc Δ) Δ (renameStoreᵗ suc Σ) (singleTyEnv (｀ α))
singleTySubstWf-α hα {zero} z<s = wfα (lookupˢ-map-renameᵗ hα)
singleTySubstWf-α hα {suc X} (s<s x<Δ) = wfX x<Δ

singleTyEnv-IsVar-α :
  {α : Seal} →
  TySubstIsVar (singleTyEnv (｀ α))
singleTyEnv-IsVar-α {α} {zero} = α-var
singleTyEnv-IsVar-α {α} {suc X} = X-var

SubstCoherent : Substᵗ → Substᶜ → Set
SubstCoherent σ τ = ∀ {X} → atomize (σ X) ≡ τ X

liftSealSubstᶜ : Substᶜ → Substᶜ
liftSealSubstᶜ τ X = renameCImpˢ suc (τ X)

atomize-renameᵗ-suc :
  {A : Ty} →
  IsVar A →
  atomize (renameᵗ suc A) ≡ renameCImpᵗ suc (atomize A)
atomize-renameᵗ-suc {A = ＇ X} X-var = refl
atomize-renameᵗ-suc {A = ｀ a} α-var = refl
atomize-renameᵗ-suc {A = ‵ b} ι-var = refl

atomize-renameˢ-suc :
  {A : Ty} →
  IsVar A →
  atomize (⇑ˢ A) ≡ renameCImpˢ suc (atomize A)
atomize-renameˢ-suc {A = ＇ X} X-var = refl
atomize-renameˢ-suc {A = ｀ a} α-var = refl
atomize-renameˢ-suc {A = ‵ b} ι-var = refl

SubstCoherent-exts :
  {σ : Substᵗ} {τ : Substᶜ} →
  TySubstIsVar σ →
  SubstCoherent σ τ →
  SubstCoherent (extsᵗ σ) (extsᶜ τ)
SubstCoherent-exts hσv hcoh {zero} = refl
SubstCoherent-exts hσv hcoh {suc X} =
  trans
    (atomize-renameᵗ-suc (hσv {X}))
    (cong (renameCImpᵗ suc) (hcoh {X}))

SubstCoherent-liftSeal :
  {σ : Substᵗ} {τ : Substᶜ} →
  TySubstIsVar σ →
  SubstCoherent σ τ →
  SubstCoherent
    (liftSealSubstᵗ σ)
    (liftSealSubstᶜ τ)
SubstCoherent-liftSeal hσv hcoh {X} =
  trans
    (atomize-renameˢ-suc (hσv {X}))
    (cong (renameCImpˢ suc) (hcoh {X}))

TySubstIsVar-liftSeal :
  {σ : Substᵗ} →
  TySubstIsVar σ →
  TySubstIsVar (liftSealSubstᵗ σ)
TySubstIsVar-liftSeal hσv {X} =
  renameˢ-preserves-IsVar (hσv {X})

mutual
  substCImpᵗ-coherent :
    {σ : Substᵗ} {τ : Substᶜ} →
    TySubstIsVar σ →
    SubstCoherent σ τ →
    (g : CImp) →
    substCImpᵗ σ g ≡ substCImpᶜ τ g
  substCImpᵗ-coherent hσv hcoh (idα α) = refl
  substCImpᵗ-coherent hσv hcoh (idX X) = hcoh {X}
  substCImpᵗ-coherent hσv hcoh (idι ι) = refl
  substCImpᵗ-coherent hσv hcoh (p →ᵖ q) =
    cong₂ _→ᵖ_
      (substImpᵗ-coherent hσv hcoh p)
      (substImpᵗ-coherent hσv hcoh q)
  substCImpᵗ-coherent {σ = σ} {τ = τ} hσv hcoh (∀ᵖ p) =
    cong ∀ᵖ_
      (substImpᵗ-coherent
        {σ = extsᵗ σ}
        {τ = extsᶜ τ}
        (λ {X} → TySubstIsVar-exts hσv {X})
        (λ {X} → SubstCoherent-exts hσv hcoh {X})
        p)

  substImpᵗ-coherent :
    {σ : Substᵗ} {τ : Substᶜ} →
    TySubstIsVar σ →
    SubstCoherent σ τ →
    (p : Imp) →
    substImpᵗ σ p ≡ substImpᶜ τ p
  substImpᵗ-coherent hσv hcoh (⌈ g ⌉) =
    cong ⌈_⌉ (substCImpᵗ-coherent hσv hcoh g)
  substImpᵗ-coherent hσv hcoh id★ = refl
  substImpᵗ-coherent hσv hcoh (injTag g G) =
    cong (λ cg → injTag cg G) (substCImpᵗ-coherent hσv hcoh g)
  substImpᵗ-coherent hσv hcoh (sealImp α p) =
    cong (sealImp α) (substImpᵗ-coherent hσv hcoh p)
  substImpᵗ-coherent {σ = σ} {τ = τ} hσv hcoh (nuImp p) =
    cong nuImp
      (substImpᵗ-coherent
        {σ = liftSealSubstᵗ σ}
        {τ = liftSealSubstᶜ τ}
        (TySubstIsVar-liftSeal {σ = σ} hσv)
        (SubstCoherent-liftSeal {σ = σ} {τ = τ} hσv hcoh)
        p)

singleTy-singleC-coherent :
  {α : Seal} →
  SubstCoherent (singleTyEnv (｀ α)) (singleCEnvα α)
singleTy-singleC-coherent {α} {zero} = refl
singleTy-singleC-coherent {α} {suc X} = refl

imp-subst-single-α :
  {α : Seal} {p : Imp} →
  substImpᵗ (singleTyEnv (｀ α)) p ≡ p [ α ]ᴾα
imp-subst-single-α {α} {p} =
  substImpᵗ-coherent
    singleTyEnv-IsVar-α
    singleTy-singleC-coherent
    p

type-inst-preserve-[] :
  ∀ {Δ Σ A B N α} →
  WfStore Σ →
  (suc Δ) ∣ (renameStoreᵗ suc Σ) ⊢ [] ⊢ N ⦂ A →
  Σ ∋ˢ α ⦂ B →
  Δ ∣ Σ ⊢ [] ⊢ N [ ｀ α ]ᵀ ⦂ A [ ｀ α ]ᵗ
type-inst-preserve-[] wfΣ hN hα =
  typing-store-unshift wfΣ
    (typing-substᵀ-wf
      (wfStore-rename-suc wfΣ)
      (singleTySubstWf-α hα)
      singleTyEnv-IsVar-α
      hN)

forall-inst-preserve :
  ∀ {Δ Σ A B α p C} →
  WfStore Σ →
  (suc Δ) ∣ (renameStoreᵗ suc Σ) ⊢ᵖ p ⦂ A ⊑ B →
  Σ ∋ˢ α ⦂ C →
  Δ ∣ Σ ⊢ᵖ (p [ α ]ᴾα) ⦂ A [ ｀ α ]ᵗ ⊑ B [ ｀ α ]ᵗ
forall-inst-preserve {Δ} {Σ} {A} {B} {α} wfΣ hp hα =
  imp-store-unshift wfΣ
    (Eq.subst
      (λ q → Δ ∣ renameStoreᵗ suc Σ ⊢ᵖ q ⦂ A [ ｀ α ]ᵗ ⊑ B [ ｀ α ]ᵗ)
      imp-subst-single-α
      (imp-substᵗ-preserves-typing-wf
        (wfStore-rename-suc wfΣ)
        (singleTySubstWf-α hα)
        singleTyEnv-IsVar-α
        hp))

wfty-type-inst :
  ∀ {Δ Σ A B α} →
  WfTy (suc Δ) (renameStoreᵗ suc Σ) A →
  Σ ∋ˢ α ⦂ B →
  WfTy Δ Σ (A [ ｀ α ]ᵗ)
wfty-type-inst hA hα =
  substᵗ-preserves-WfTy
    (wfty-store-unshift hA)
    (singleTySubstWf (wfα hα))

data WfCtx (Δ : TyCtx) (Σ : Store) : Ctx → Set where
  wf[] : WfCtx Δ Σ []
  wf∷  : {Γ : Ctx} {A : Ty} →
         WfCtx Δ Σ Γ →
         WfTy Δ Σ A →
         WfCtx Δ Σ (A ∷ Γ)

lookup-wfty :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {x : Var} {A : Ty} →
  WfCtx Δ Σ Γ →
  Γ ∋ x ⦂ A →
  WfTy Δ Σ A
lookup-wfty (wf∷ hΓ hA) Z = hA
lookup-wfty (wf∷ hΓ hA) (S h) = lookup-wfty hΓ h

wfctx-shift :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} →
  WfCtx Δ Σ Γ →
  WfCtx (suc Δ) (renameStoreᵗ suc Σ) (⤊ Γ)
wfctx-shift wf[] = wf[]
wfctx-shift (wf∷ hΓ hA) =
  wf∷
    (wfctx-shift hΓ)
    (renameᵗ-preserves-WfTy hA suc-rename-wf)

store-rel-preserves-WfCtx :
  {Δ : TyCtx} {Σ Σ′ : Store} {Γ : Ctx} →
  StoreRel Σ Σ′ →
  WfCtx Δ Σ Γ →
  WfCtx Δ Σ′ Γ
store-rel-preserves-WfCtx rel wf[] = wf[]
store-rel-preserves-WfCtx rel (wf∷ hΓ hA) =
  wf∷
    (store-rel-preserves-WfCtx rel hΓ)
    (store-rel-preserves-WfTy rel hA)

rename-lookup :
  {Σ Σ′ : Store} {ρ : Renameᵗ} →
  (∀ {a A} → Σ ∋ˢ a ⦂ A → Σ′ ∋ˢ a ⦂ A) →
  (∀ {a A} → renameStoreᵗ ρ Σ ∋ˢ a ⦂ A → renameStoreᵗ ρ Σ′ ∋ˢ a ⦂ A)
rename-lookup {ρ = ρ} hlookup h
  with lookupˢ-map-inv h
... | A , (hA , eq) =
  Eq.subst
    (λ T → renameStoreᵗ ρ _ ∋ˢ _ ⦂ T)
    (sym eq)
    (lookupˢ-map-renameᵗ (hlookup hA))

cons-lookup :
  {Σ Σ′ : Store} {A : Ty} →
  (∀ {a B} → Σ ∋ˢ a ⦂ B → Σ′ ∋ˢ a ⦂ B) →
  (∀ {a B} → (A ∷ Σ) ∋ˢ a ⦂ B → (A ∷ Σ′) ∋ˢ a ⦂ B)
cons-lookup hlookup Zˢ = Zˢ
cons-lookup hlookup (Sˢ h) = Sˢ (hlookup h)

postulate
  cons-lookup-shiftˢ :
    {Σ Σ′ : Store} {A : Ty} →
    (∀ {a B} → Σ ∋ˢ a ⦂ B → Σ′ ∋ˢ a ⦂ B) →
    (∀ {a B} →
      (A ∷ ⟰ˢ Σ) ∋ˢ a ⦂ B →
      (A ∷ ⟰ˢ Σ′) ∋ˢ a ⦂ B)

mutual
  lookup-preserves-WfTy :
    {Δ : TyCtx} {Σ Σ′ : Store} {A : Ty} →
    (∀ {a B} → Σ ∋ˢ a ⦂ B → Σ′ ∋ˢ a ⦂ B) →
    WfTy Δ Σ A →
    WfTy Δ Σ′ A
  lookup-preserves-WfTy hlookup (wfX x<Δ) = wfX x<Δ
  lookup-preserves-WfTy hlookup wfι = wfι
  lookup-preserves-WfTy hlookup wf★ = wf★
  lookup-preserves-WfTy hlookup (wfα hα) = wfα (hlookup hα)
  lookup-preserves-WfTy hlookup (wf⇒ hA hB) =
    wf⇒
      (lookup-preserves-WfTy hlookup hA)
      (lookup-preserves-WfTy hlookup hB)
  lookup-preserves-WfTy hlookup (wf∀ hA) =
    wf∀
      (lookup-preserves-WfTy
        (rename-lookup hlookup)
        hA)

  lookup-preserves-cimp :
    {Δ : TyCtx} {Σ Σ′ : Store} {g : CImp} {A B : Ty} →
    (∀ {a C} → Σ ∋ˢ a ⦂ C → Σ′ ∋ˢ a ⦂ C) →
    Δ ∣ Σ ⊢ᶜ g ⦂ A ⊑ B →
    Δ ∣ Σ′ ⊢ᶜ g ⦂ A ⊑ B
  lookup-preserves-cimp hlookup (⊢idα hα) = ⊢idα (hlookup hα)
  lookup-preserves-cimp hlookup (⊢idX x<Δ) = ⊢idX x<Δ
  lookup-preserves-cimp hlookup ⊢idι = ⊢idι
  lookup-preserves-cimp hlookup (⊢→ᵖ hp hq) =
    ⊢→ᵖ
      (lookup-preserves-imp hlookup hp)
      (lookup-preserves-imp hlookup hq)
  lookup-preserves-cimp hlookup (⊢∀ᵖ hp) =
    ⊢∀ᵖ
      (lookup-preserves-imp
        (rename-lookup hlookup)
        hp)

  lookup-preserves-imp :
    {Δ : TyCtx} {Σ Σ′ : Store} {p : Imp} {A B : Ty} →
    (∀ {a C} → Σ ∋ˢ a ⦂ C → Σ′ ∋ˢ a ⦂ C) →
    Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
    Δ ∣ Σ′ ⊢ᵖ p ⦂ A ⊑ B
  lookup-preserves-imp hlookup (⊢⌈⌉ hg) =
    ⊢⌈⌉ (lookup-preserves-cimp hlookup hg)
  lookup-preserves-imp hlookup ⊢id★ = ⊢id★
  lookup-preserves-imp hlookup (⊢tag hg) =
    ⊢tag (lookup-preserves-cimp hlookup hg)
  lookup-preserves-imp hlookup (⊢seal hα hp) =
    ⊢seal (hlookup hα) (lookup-preserves-imp hlookup hp)
  lookup-preserves-imp hlookup (⊢ν hp hA hB) =
    ⊢ν
      (lookup-preserves-imp (cons-lookup-shiftˢ hlookup) hp)
      (lookup-preserves-WfTy hlookup hA)
      (lookup-preserves-WfTy hlookup hB)

  lookup-preserves-typing :
    {Δ : TyCtx} {Σ Σ′ : Store} {Γ : Ctx} {M : Term} {A : Ty} →
    (∀ {a B} → Σ ∋ˢ a ⦂ B → Σ′ ∋ˢ a ⦂ B) →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
    Δ ∣ Σ′ ⊢ Γ ⊢ M ⦂ A
  lookup-preserves-typing hlookup (⊢` h) = ⊢` h
  lookup-preserves-typing hlookup (⊢ƛ hA hN) =
    ⊢ƛ
      (lookup-preserves-WfTy hlookup hA)
      (lookup-preserves-typing hlookup hN)
  lookup-preserves-typing hlookup (⊢· hL hM) =
    ⊢·
      (lookup-preserves-typing hlookup hL)
      (lookup-preserves-typing hlookup hM)
  lookup-preserves-typing hlookup (⊢Λ hN) =
    ⊢Λ
      (lookup-preserves-typing
        (rename-lookup hlookup)
        hN)
  lookup-preserves-typing hlookup (⊢·α hL hα) =
    ⊢·α
      (lookup-preserves-typing hlookup hL)
      (hlookup hα)
  lookup-preserves-typing hlookup (⊢ν hA hN hB) =
    ⊢ν
      (lookup-preserves-WfTy hlookup hA)
      (lookup-preserves-typing (cons-lookup-shiftˢ hlookup) hN)
      (lookup-preserves-WfTy hlookup hB)
  lookup-preserves-typing hlookup ⊢$ = ⊢$
  lookup-preserves-typing hlookup (⊢⊕ hM hN) =
    ⊢⊕
      (lookup-preserves-typing hlookup hM)
      (lookup-preserves-typing hlookup hN)
  lookup-preserves-typing hlookup (⊢cast-up hM hp) =
    ⊢cast-up
      (lookup-preserves-typing hlookup hM)
      (lookup-preserves-imp hlookup hp)
  lookup-preserves-typing hlookup (⊢cast-down hM hp) =
    ⊢cast-down
      (lookup-preserves-typing hlookup hM)
      (lookup-preserves-imp hlookup hp)
  lookup-preserves-typing hlookup (⊢blame hA) =
    ⊢blame (lookup-preserves-WfTy hlookup hA)

store-rel-preserves-cimp :
  {Δ : TyCtx} {Σ Σ′ : Store} {g : CImp} {A B : Ty} →
  StoreRel Σ Σ′ →
  Δ ∣ Σ ⊢ᶜ g ⦂ A ⊑ B →
  Δ ∣ Σ′ ⊢ᶜ g ⦂ A ⊑ B
store-rel-preserves-cimp rel =
  lookup-preserves-cimp (StoreRel.preserve-lookup rel)

store-rel-preserves-imp :
  {Δ : TyCtx} {Σ Σ′ : Store} {p : Imp} {A B : Ty} →
  StoreRel Σ Σ′ →
  Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
  Δ ∣ Σ′ ⊢ᵖ p ⦂ A ⊑ B
store-rel-preserves-imp rel =
  lookup-preserves-imp (StoreRel.preserve-lookup rel)

store-rel-preserves-typing :
  {Δ : TyCtx} {Σ Σ′ : Store} {Γ : Ctx} {M : Term} {A : Ty} →
  StoreRel Σ Σ′ →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
  Δ ∣ Σ′ ⊢ Γ ⊢ M ⦂ A
store-rel-preserves-typing rel =
  lookup-preserves-typing (StoreRel.preserve-lookup rel)

mutual
  cimp-wfty :
    ∀ {Δ Σ g A B} →
    Δ ∣ Σ ⊢ᶜ g ⦂ A ⊑ B →
    WfTy Δ Σ A × WfTy Δ Σ B
  cimp-wfty (⊢idα hα) = wfα hα , wfα hα
  cimp-wfty (⊢idX x<Δ) = wfX x<Δ , wfX x<Δ
  cimp-wfty ⊢idι = wfι , wfι
  cimp-wfty (⊢→ᵖ hp hq) with imp-wfty hp | imp-wfty hq
  ... | hA , hA' | hB , hB' = wf⇒ hA hB , wf⇒ hA' hB'
  cimp-wfty (⊢∀ᵖ hp) with imp-wfty hp
  ... | hA , hB = wf∀ hA , wf∀ hB

  imp-wfty :
    ∀ {Δ Σ p A B} →
    Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
    WfTy Δ Σ A × WfTy Δ Σ B
  imp-wfty (⊢⌈⌉ hg) = cimp-wfty hg
  imp-wfty ⊢id★ = wf★ , wf★
  imp-wfty (⊢tag hg) with cimp-wfty hg
  ... | hA , hG = hA , wf★
  imp-wfty (⊢seal hα hp) with imp-wfty hp
  ... | hA , hB = wfα hα , hB
  imp-wfty (⊢ν hp hA hB) = wf∀ (wfty-store-shift hA) , hB

constTy-wfty :
  {Δ : TyCtx} {Σ : Store} {κ : Const} →
  WfTy Δ Σ (constTy κ)
constTy-wfty {κ = κℕ n} = wfι

typing-wfty :
  ∀ {Δ Σ Γ M A} →
  WfCtx Δ Σ Γ →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
  WfTy Δ Σ A
typing-wfty hΓ (⊢` h) = lookup-wfty hΓ h
typing-wfty hΓ (⊢ƛ hA hN) =
  wf⇒ hA (typing-wfty (wf∷ hΓ hA) hN)
typing-wfty hΓ (⊢· hL hM) with typing-wfty hΓ hL
... | wf⇒ hA hB = hB
typing-wfty hΓ (⊢Λ hN) =
  wf∀ (typing-wfty (wfctx-shift hΓ) hN)
typing-wfty hΓ (⊢·α hL hα) with typing-wfty hΓ hL
... | wf∀ hA = wfty-type-inst hA hα
typing-wfty hΓ (⊢ν hA hN hB) = hB
typing-wfty hΓ ⊢$ = constTy-wfty
typing-wfty hΓ (⊢⊕ hM hN) = wfι
typing-wfty hΓ (⊢cast-up hM hp) with imp-wfty hp
... | hA , hB = hB
typing-wfty hΓ (⊢cast-down hM hp) with imp-wfty hp
... | hA , hB = hA
typing-wfty hΓ (⊢blame hA) = hA

wf-from-typing :
  ∀ {Δ Σ M A} →
  Δ ∣ Σ ⊢ [] ⊢ M ⦂ A →
  WfTy Δ Σ A
wf-from-typing h = typing-wfty wf[] h

SubstWf-⇑ :
  {Δ : TyCtx} {Σ : Store} {Γ Γ' : Ctx} {σ : Subst} →
  SubstWf Δ Σ Γ Γ' σ →
  SubstWf (suc Δ) (renameStoreᵗ suc Σ) (⤊ Γ) (⤊ Γ') (⇑ σ)
SubstWf-⇑ hσ h with lookup-map-inv h
... | A , (hA , eq)
  rewrite eq = typing-renameᵀ-suc (hσ hA)

postulate
  SubstWf-liftSeal :
    {Δ : TyCtx} {Σ : Store} {Γ Γ' : Ctx} {B : Ty} {σ : Subst} →
    SubstWf Δ Σ Γ Γ' σ →
    SubstWf Δ (B ∷ ⟰ˢ Σ) (⤊ˢ Γ) (⤊ˢ Γ') (liftSealSubst σ)

typing-subst :
  {Δ : TyCtx} {Σ : Store} {Γ Γ' : Ctx} {M : Term} {A : Ty} {σ : Subst} →
  SubstWf Δ Σ Γ Γ' σ →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ⊢ Γ' ⊢ subst σ M ⦂ A
typing-subst hσ (⊢` h) = hσ h
typing-subst hσ (⊢ƛ hA hN) =
  ⊢ƛ hA (typing-subst (SubstWf-exts hσ) hN)
typing-subst hσ (⊢· hL hM) =
  ⊢· (typing-subst hσ hL) (typing-subst hσ hM)
typing-subst hσ (⊢Λ hN) =
  ⊢Λ (typing-subst (SubstWf-⇑ hσ) hN)
typing-subst hσ (⊢·α hL hα) =
  ⊢·α (typing-subst hσ hL) hα
typing-subst {Δ = Δ} {Σ = Σ} {Γ = Γ} {Γ' = Γ'} {σ = σ}
             hσ (⊢ν {A = A} hA hN hB) =
  let IH = typing-subst (SubstWf-liftSeal {B = A} hσ) hN in
  ⊢ν hA IH hB
typing-subst hσ ⊢$ = ⊢$
typing-subst hσ (⊢⊕ hM hN) =
  ⊢⊕ (typing-subst hσ hM) (typing-subst hσ hN)
typing-subst hσ (⊢cast-up hM hp) =
  ⊢cast-up (typing-subst hσ hM) hp
typing-subst hσ (⊢cast-down hM hp) =
  ⊢cast-down (typing-subst hσ hM) hp
typing-subst hσ (⊢blame hA) = ⊢blame hA

singleSubstWf :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {A : Ty} {V : Term} →
  Δ ∣ Σ ⊢ Γ ⊢ V ⦂ A →
  SubstWf Δ Σ (A ∷ Γ) Γ (singleEnv V)
singleSubstWf hV Z = hV
singleSubstWf hV (S h) = ⊢` h

typing-single-subst :
  {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {N V : Term} {A B : Ty} →
  Δ ∣ Σ ⊢ (A ∷ Γ) ⊢ N ⦂ B →
  Δ ∣ Σ ⊢ Γ ⊢ V ⦂ A →
  Δ ∣ Σ ⊢ Γ ⊢ N [ V ] ⦂ B
typing-single-subst hN hV =
  typing-subst (singleSubstWf hV) hN

subst-preserve-[] :
  ∀ {Δ Σ A B N V} →
  Δ ∣ Σ ⊢ (A ∷ []) ⊢ N ⦂ B →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ A →
  Δ ∣ Σ ⊢ [] ⊢ N [ V ] ⦂ B
subst-preserve-[] = typing-single-subst

------------------------------------------------------------------------
-- Helper lemmas used by preservation
------------------------------------------------------------------------

seal-step-preserve :
  ∀ {Δ Σ A V α p q} →
  Δ ∣ Σ ⊢ [] ⊢ ((V at down (sealImp α p)) at up (sealImp α q)) ⦂ A →
  Δ ∣ Σ ⊢ [] ⊢ ((V at down p) at up q) ⦂ A
seal-step-preserve
  (⊢cast-up
    (⊢cast-down hV (⊢seal hα hp))
    (⊢seal hα' hq))
  rewrite lookupˢ-functional hα hα' =
    ⊢cast-up (⊢cast-down hV hp) hq

id-up-preserve :
  ∀ {Δ Σ V A B p} →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ A →
  Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
  IsId p →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ B
id-up-preserve hV (⊢⌈⌉ (⊢idα x)) tt = hV
id-up-preserve hV (⊢⌈⌉ (⊢idX x)) tt = hV
id-up-preserve hV (⊢⌈⌉ ⊢idι) tt = hV
id-up-preserve hV ⊢id★ tt = hV
id-up-preserve hV (⊢⌈⌉ (⊢→ᵖ hp hq)) ()
id-up-preserve hV (⊢⌈⌉ (⊢∀ᵖ hp)) ()
id-up-preserve hV (⊢tag hp) ()
id-up-preserve hV (⊢seal x hp) ()
id-up-preserve hV (⊢ν hp hA hB) ()

id-down-preserve :
  ∀ {Δ Σ V A B p} →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ B →
  Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
  IsId p →
  Δ ∣ Σ ⊢ [] ⊢ V ⦂ A
id-down-preserve hV (⊢⌈⌉ (⊢idα x)) tt = hV
id-down-preserve hV (⊢⌈⌉ (⊢idX x)) tt = hV
id-down-preserve hV (⊢⌈⌉ ⊢idι) tt = hV
id-down-preserve hV ⊢id★ tt = hV
id-down-preserve hV (⊢⌈⌉ (⊢→ᵖ hp hq)) ()
id-down-preserve hV (⊢⌈⌉ (⊢∀ᵖ hp)) ()
id-down-preserve hV (⊢tag hp) ()
id-down-preserve hV (⊢seal x hp) ()
id-down-preserve hV (⊢ν hp hA hB) ()

store-step-unique :
  ∀ {Σ Π M N} →
  (Σ ⊲ M) —→ (Π ⊲ N) →
  StoreUnique Σ →
  StoreUnique Π
store-step-unique (β-δ d) hΣ = hΣ
store-step-unique (β-ƛ v) hΣ = hΣ
store-step-unique β-Λ hΣ = hΣ
store-step-unique (β-id+ v pid) hΣ = hΣ
store-step-unique (β-id- v pid) hΣ = hΣ
store-step-unique (β-→+ v w) hΣ = hΣ
store-step-unique (β-→- v w) hΣ = hΣ
store-step-unique (β-∀+ v) hΣ = hΣ
store-step-unique (β-∀- v) hΣ = hΣ
store-step-unique (β-ν+ v) hΣ = hΣ
store-step-unique (β-ν- v) hΣ = hΣ
store-step-unique (β-tag-ok v) hΣ = hΣ
store-step-unique (β-tag-bad v neq) hΣ = hΣ
store-step-unique (β-seal v) hΣ = hΣ
store-step-unique (ξν {Σ = Σ} {A = A}) hΣ =
  storeUnique-extend {Σ = Σ} {A = A} hΣ
store-step-unique (ξξ eqM eqN s) hΣ = store-step-unique s hΣ
store-step-unique (ξξ-blame eqM) hΣ = hΣ

------------------------------------------------------------------------
-- Preservation (single-step and multi-step), closed terms
------------------------------------------------------------------------

mutual
  preservation :
    ∀ {Σ Π M N A} →
    0 ∣ Σ ⊢ [] ⊢ M ⦂ A →
    StoreUnique Σ →
    WfStore Σ →
    (Σ ⊲ M) —→ (Π ⊲ N) →
    (0 ∣ Π ⊢ [] ⊢ N ⦂ A) × StoreExt Σ Π × StoreUnique Π × WfStore Π

  preservation {M = ($ (κℕ m)) ⊕[ addℕ ] ($ (κℕ n))}
               (⊢⊕ hM hN) hΣ hWF s@(β-δ δ-add) =
    ⊢$ , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation (⊢· (⊢ƛ hA hN) hV) hΣ hWF s@(β-ƛ vV) =
    subst-preserve-[] hN hV , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation (⊢·α (⊢Λ hN) hα) hΣ hWF s@β-Λ =
    type-inst-preserve-[] hWF hN hα , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation (⊢cast-up hV hp) hΣ hWF s@(β-id+ vV pid) =
    id-up-preserve hV hp pid , store-rel-refl hWF , store-step-unique s hΣ , hWF
  preservation (⊢cast-down hV hp) hΣ hWF s@(β-id- vV pid) =
    id-down-preserve hV hp pid , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation (⊢· (⊢cast-up hV (⊢⌈⌉ (⊢→ᵖ hs ht))) hW) hΣ hWF s@(β-→+ vV vW) =
    ⊢cast-up (⊢· hV (⊢cast-down hW hs)) ht , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation (⊢· (⊢cast-down hV (⊢⌈⌉ (⊢→ᵖ hs ht))) hW) hΣ hWF s@(β-→- vV vW) =
    ⊢cast-down (⊢· hV (⊢cast-up hW hs)) ht , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation (⊢·α (⊢cast-up hV (⊢⌈⌉ (⊢∀ᵖ hp))) hα) hΣ hWF s@(β-∀+ vV) =
    ⊢cast-up (⊢·α hV hα) (forall-inst-preserve hWF hp hα) , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation (⊢·α (⊢cast-down hV (⊢⌈⌉ (⊢∀ᵖ hp))) hα) hΣ hWF s@(β-∀- vV) =
    ⊢cast-down (⊢·α hV hα) (forall-inst-preserve hWF hp hα) , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation {Σ = Σ}
               (⊢cast-up {M = V} hV (⊢ν {A = A} {B = B} {p = p} hp wfA wfB))
               hΣ hWF s@(β-ν+ vV) =
    ⊢ν wf★ (nu-up-body-preserve hV hp) wfB
    , store-rel-refl hWF
    , store-step-unique s hΣ
    , hWF

  preservation (⊢·α (⊢cast-down hV (⊢ν {A = A} hp wfA wfB)) hβ) hΣ hWF s@(β-ν- vV) =
    ⊢cast-down hV (nu-down-preserve {A = A} hp hβ) , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation (⊢cast-down (⊢cast-up hV (⊢tag hg)) (⊢tag hh)) hΣ hWF s@(β-tag-ok vV) =
    ⊢cast-down (⊢cast-up hV (⊢⌈⌉ hg)) (⊢⌈⌉ hh) , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation h@(⊢cast-down (⊢cast-up hV (⊢tag hg)) (⊢tag hh)) hΣ hWF s@(β-tag-bad vV neq) =
    ⊢blame (wf-from-typing h) , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation h hΣ hWF s@(β-seal vV) =
    seal-step-preserve h , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation (⊢ν {A = A} hA hN hB) hΣ hWF
               s@ξν =
    typing-singleSealEnv-fresh hN
    , store-rel-extend-end hWF hA
    , store-step-unique s hΣ
    , storeWfAt-extend-end hWF hA

  preservation {M = M'} {N = N'} h hΣ hWF s@(ξξ {F = F} eqM eqN s')
    rewrite eqM | eqN
    = preservation-frame h hΣ hWF s'

  preservation h hΣ hWF s@(ξξ-blame eqM) =
    ⊢blame (wf-from-typing h) , store-rel-refl hWF , store-step-unique s hΣ , hWF

  preservation-frame :
    ∀ {Σ Π M N A F} →
    0 ∣ Σ ⊢ [] ⊢ plug F M ⦂ A →
    StoreUnique Σ →
    WfStore Σ →
    (Σ ⊲ M) —→ (Π ⊲ N) →
    (0 ∣ Π ⊢ [] ⊢ plug F N ⦂ A) × StoreExt Σ Π × StoreUnique Π × WfStore Π

  preservation-frame {F = □· R} (⊢· hM hR) hΣ hWF s
    with preservation hM hΣ hWF s
  ... | hN , hExt , hΠ , hWFΠ =
    ⊢· hN (store-rel-preserves-typing hExt hR) , hExt , hΠ , hWFΠ

  preservation-frame {F = L ·□ vL} (⊢· hL hM) hΣ hWF s
    with preservation hM hΣ hWF s
  ... | hN , hExt , hΠ , hWFΠ =
    ⊢· (store-rel-preserves-typing hExt hL) hN , hExt , hΠ , hWFΠ

  preservation-frame {F = □·α α} (⊢·α hM hα) hΣ hWF s
    with preservation hM hΣ hWF s
  ... | hN , hExt , hΠ , hWFΠ =
    ⊢·α hN (StoreRel.preserve-lookup hExt hα) , hExt , hΠ , hWFΠ

  preservation-frame {F = □⊕[ op ] R} (⊢⊕ hM hR) hΣ hWF s
    with preservation hM hΣ hWF s
  ... | hN , hExt , hΠ , hWFΠ =
    ⊢⊕ hN (store-rel-preserves-typing hExt hR) , hExt , hΠ , hWFΠ

  preservation-frame {F = L ⊕[ op ]□ vL} (⊢⊕ hL hM) hΣ hWF s
    with preservation hM hΣ hWF s
  ... | hN , hExt , hΠ , hWFΠ =
    ⊢⊕ (store-rel-preserves-typing hExt hL) hN , hExt , hΠ , hWFΠ

  preservation-frame {F = □at-up p} (⊢cast-up hM hp) hΣ hWF s
    with preservation hM hΣ hWF s
  ... | hN , hExt , hΠ , hWFΠ =
    ⊢cast-up hN (store-rel-preserves-imp hExt hp) , hExt , hΠ , hWFΠ

  preservation-frame {F = □at-down p} (⊢cast-down hM hp) hΣ hWF s
    with preservation hM hΣ hWF s
  ... | hN , hExt , hΠ , hWFΠ =
    ⊢cast-down hN (store-rel-preserves-imp hExt hp) , hExt , hΠ , hWFΠ

config-shape :
  (c : Config) →
  Σ Store (λ Σ₀ → Σ Term (λ M₀ → c ≡ (Σ₀ ⊲ M₀)))
config-shape (Σ ⊲ M) = Σ , (M , refl)

multi-preservation :
  ∀ {Σ Π M N A} →
  0 ∣ Σ ⊢ [] ⊢ M ⦂ A →
  StoreUnique Σ →
  WfStore Σ →
  (Σ ⊲ M) —↠ (Π ⊲ N) →
  (0 ∣ Π ⊢ [] ⊢ N ⦂ A) × StoreExt Σ Π × StoreUnique Π × WfStore Π
multi-preservation hM hΣ hWF (_ ∎) = hM , store-rel-refl hWF , hΣ , hWF
multi-preservation hM hΣ hWF (_—→⟨_⟩_ c₁ {c₂} s ms) with config-shape c₂
... | Σ₁ , (M₁ , refl) with preservation hM hΣ hWF s
... | hM₁ , hExt₀₁ , hΣ₁ , hWF₁ with multi-preservation hM₁ hΣ₁ hWF₁ ms
... | hN , hExt₁₂ , hΠ , hWFΠ =
  hN , store-rel-trans hExt₀₁ hExt₁₂ , hΠ , hWFΠ
