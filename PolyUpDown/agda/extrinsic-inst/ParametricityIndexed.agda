module ParametricityIndexed where

-- File Charter:
--   * First compatibility-proof probe for the indexed imprecision design.
--   * Defines the indexed open-term semantic judgment using `interp` before
--   * relational substitution, so `𝒱`/`ℰ` see the same indexed types as
--   * `LogicalRelationIndexed`.
--   * Starts with the ν type-application compatibility case, isolating the
--   * remaining operational bridge as an explicit theorem target.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z<s; s<s; z≤n)
open import Data.Nat.Properties using (≤-refl; <-≤-trans; ≤-trans)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Level using (Lift; 0ℓ; lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Types
open import Store using (_⊆ˢ_; ⊆ˢ-refl; ⊆ˢ-trans; drop; StoreWf)
open import TypeCheckDec using (raiseVarFrom)
open import ImprecisionIndexed
open import Imprecision using (substᵗ-closed-id)
open import UpDown
open import Terms
open import TermPrecisionIndexed
open import TermProperties using (Substˣ; substˣ-term; []ᵀ-wt)
open import TypeProperties
  using
    ( TySubstWf
    ; TySubstWf-exts
    ; TyRenameWf-suc
    ; SealRenameWf-suc
    ; open-renᵗ-suc
    ; renameᵗ-⇑ˢ
    ; renameᵗ-preserves-WfTy
    ; renameˢ-preserves-WfTy
    ; substᵗ-preserves-WfTy
    ; substᵗ-cong
    ; substᵗ-substᵗ
    )
open import ReductionFresh
  using
    ( UpValue
    ; DownValue
    ; Value
    ; _∣_—→_∣_
    ; _∣_—↠_∣_
    ; _∎
    ; _—→⟨_⟩_
    ; multi-trans
    ; id-step
    ; id-up
    ; id-down
    ; seal-unseal
    ; tag-untag-ok
    ; tag-untag-bad
    ; blame-up
    ; blame-down
    ; blame-·α
    ; β-Λ
    ; β-up-∀
    ; β-down-∀
    ; β-down-ν
    ; β-up-ν
    ; β-up-；
    ; β-down-；
    ; ξ-·₁
    ; ξ-·₂
    ; ξ-·α
    ; ξ-up
    ; ξ-down
    ; ξ-⊕₁
    ; ξ-⊕₂
    ; store-growth
    ; value-no-step
    )
open import ProgressFresh
  using
    ( canonical-∀
    ; canonical-｀
    ; canonical-★
    ; AllView
    ; av-Λ
    ; av-up-∀
    ; av-down-∀
    ; av-down-ν
    ; SealView
    ; sv-down-seal
    ; StarView
    ; sv-up-tag
    )
open import PreservationFresh
  using
    ( StepCtxShape
    ; shape-id
    ; shape-suc
    ; StepCtxExact
    ; step-ctx-shape
    ; preservation-step
    ; wkΨ-term-suc
    ; len<suc-StoreWf
    )
open import LogicalRelationIndexed

------------------------------------------------------------------------
-- Interpreting indexed types inside terms and casts
------------------------------------------------------------------------

mutual
  interpUp : ICtx → Up → Up
  interpUp Ξ (tag G) = tag (interp Ξ G)
  interpUp Ξ (unseal α) = unseal (interpSeal Ξ α)
  interpUp Ξ (p ↦ q) = interpDown Ξ p ↦ interpUp Ξ q
  interpUp Ξ (∀ᵖ p) = ∀ᵖ (interpUp (plain ∷ Ξ) p)
  interpUp Ξ (ν p) = ν (interpUp (ν-bound ∷ Ξ) p)
  interpUp Ξ (id A) = id (interp Ξ A)
  interpUp Ξ (p ； q) = interpUp Ξ p ； interpUp Ξ q

  interpDown : ICtx → Down → Down
  interpDown Ξ (untag G ℓ) = untag (interp Ξ G) ℓ
  interpDown Ξ (seal α) = seal (interpSeal Ξ α)
  interpDown Ξ (p ↦ q) = interpUp Ξ p ↦ interpDown Ξ q
  interpDown Ξ (∀ᵖ p) = ∀ᵖ (interpDown (plain ∷ Ξ) p)
  interpDown Ξ (ν p) = ν (interpDown (ν-bound ∷ Ξ) p)
  interpDown Ξ (id A) = id (interp Ξ A)
  interpDown Ξ (p ； q) = interpDown Ξ p ； interpDown Ξ q

interpᵐ : ICtx → Term → Term
interpᵐ Ξ (` x) = ` x
interpᵐ Ξ (ƛ A ⇒ M) = ƛ interp Ξ A ⇒ interpᵐ Ξ M
interpᵐ Ξ (L · M) = interpᵐ Ξ L · interpᵐ Ξ M
interpᵐ Ξ (Λ M) = Λ interpᵐ (plain ∷ Ξ) M
interpᵐ Ξ (M ⦂∀ B [ T ]) =
  interpᵐ Ξ M ⦂∀ interp (plain ∷ Ξ) B [ interp Ξ T ]
interpᵐ Ξ ($ κ) = $ κ
interpᵐ Ξ (L ⊕[ op ] M) = interpᵐ Ξ L ⊕[ op ] interpᵐ Ξ M
interpᵐ Ξ (M up p) = interpᵐ Ξ M up interpUp Ξ p
interpᵐ Ξ (M down p) = interpᵐ Ξ M down interpDown Ξ p
interpᵐ Ξ (blame ℓ) = blame ℓ

closeˡᵐ : ∀ {Ξ} → RelSub Ξ → Term → Term
closeˡᵐ {Ξ = Ξ} ρ M = substᵗᵐ (leftᵗ ρ) (interpᵐ Ξ M)

closeʳᵐ : ∀ {Ξ} → RelSub Ξ → Term → Term
closeʳᵐ {Ξ = Ξ} ρ M = substᵗᵐ (rightᵗ ρ) (interpᵐ Ξ M)

mutual
  interpUpLRˡ : ICtx → List SealRel → Up → Up
  interpUpLRˡ Ξ η (tag G) = tag (interpLRˡ Ξ η G)
  interpUpLRˡ Ξ η (unseal α) = unseal α
  interpUpLRˡ Ξ η (p ↦ q) = interpDownLRˡ Ξ η p ↦ interpUpLRˡ Ξ η q
  interpUpLRˡ Ξ η (∀ᵖ p) = ∀ᵖ (interpUpLRˡ (plain ∷ Ξ) η p)
  interpUpLRˡ Ξ η (ν p) = ν (interpUp (ν-bound ∷ Ξ) p)
  interpUpLRˡ Ξ η (id A) = id (interpLRˡ Ξ η A)
  interpUpLRˡ Ξ η (p ； q) = interpUpLRˡ Ξ η p ； interpUpLRˡ Ξ η q

  interpDownLRˡ : ICtx → List SealRel → Down → Down
  interpDownLRˡ Ξ η (untag G ℓ) = untag (interpLRˡ Ξ η G) ℓ
  interpDownLRˡ Ξ η (seal α) = seal α
  interpDownLRˡ Ξ η (p ↦ q) = interpUpLRˡ Ξ η p ↦ interpDownLRˡ Ξ η q
  interpDownLRˡ Ξ η (∀ᵖ p) = ∀ᵖ (interpDownLRˡ (plain ∷ Ξ) η p)
  interpDownLRˡ Ξ η (ν p) = ν (interpDown (ν-bound ∷ Ξ) p)
  interpDownLRˡ Ξ η (id A) = id (interpLRˡ Ξ η A)
  interpDownLRˡ Ξ η (p ； q) =
    interpDownLRˡ Ξ η p ； interpDownLRˡ Ξ η q

mutual
  interpUpLRʳ : ICtx → List SealRel → Up → Up
  interpUpLRʳ Ξ η (tag G) = tag (interpLRʳ Ξ η G)
  interpUpLRʳ Ξ η (unseal α) = unseal α
  interpUpLRʳ Ξ η (p ↦ q) = interpDownLRʳ Ξ η p ↦ interpUpLRʳ Ξ η q
  interpUpLRʳ Ξ η (∀ᵖ p) = ∀ᵖ (interpUpLRʳ (plain ∷ Ξ) η p)
  interpUpLRʳ Ξ η (ν p) = ν (interpUp (ν-bound ∷ Ξ) p)
  interpUpLRʳ Ξ η (id A) = id (interpLRʳ Ξ η A)
  interpUpLRʳ Ξ η (p ； q) = interpUpLRʳ Ξ η p ； interpUpLRʳ Ξ η q

  interpDownLRʳ : ICtx → List SealRel → Down → Down
  interpDownLRʳ Ξ η (untag G ℓ) = untag (interpLRʳ Ξ η G) ℓ
  interpDownLRʳ Ξ η (seal α) = seal α
  interpDownLRʳ Ξ η (p ↦ q) = interpUpLRʳ Ξ η p ↦ interpDownLRʳ Ξ η q
  interpDownLRʳ Ξ η (∀ᵖ p) = ∀ᵖ (interpDownLRʳ (plain ∷ Ξ) η p)
  interpDownLRʳ Ξ η (ν p) = ν (interpDown (ν-bound ∷ Ξ) p)
  interpDownLRʳ Ξ η (id A) = id (interpLRʳ Ξ η A)
  interpDownLRʳ Ξ η (p ； q) =
    interpDownLRʳ Ξ η p ； interpDownLRʳ Ξ η q

interpᵐLRˡ : ICtx → List SealRel → Term → Term
interpᵐLRˡ Ξ η (` x) = ` x
interpᵐLRˡ Ξ η (ƛ A ⇒ M) = ƛ interpLRˡ Ξ η A ⇒ interpᵐLRˡ Ξ η M
interpᵐLRˡ Ξ η (L · M) = interpᵐLRˡ Ξ η L · interpᵐLRˡ Ξ η M
interpᵐLRˡ Ξ η (Λ M) = Λ interpᵐLRˡ (plain ∷ Ξ) η M
interpᵐLRˡ Ξ η (M ⦂∀ B [ T ]) =
  interpᵐLRˡ Ξ η M ⦂∀ interpLRˡ (plain ∷ Ξ) η B
    [ interpLRˡ Ξ η T ]
interpᵐLRˡ Ξ η ($ κ) = $ κ
interpᵐLRˡ Ξ η (L ⊕[ op ] M) =
  interpᵐLRˡ Ξ η L ⊕[ op ] interpᵐLRˡ Ξ η M
interpᵐLRˡ Ξ η (M up p) = interpᵐLRˡ Ξ η M up interpUpLRˡ Ξ η p
interpᵐLRˡ Ξ η (M down p) =
  interpᵐLRˡ Ξ η M down interpDownLRˡ Ξ η p
interpᵐLRˡ Ξ η (blame ℓ) = blame ℓ

interpᵐLRʳ : ICtx → List SealRel → Term → Term
interpᵐLRʳ Ξ η (` x) = ` x
interpᵐLRʳ Ξ η (ƛ A ⇒ M) = ƛ interpLRʳ Ξ η A ⇒ interpᵐLRʳ Ξ η M
interpᵐLRʳ Ξ η (L · M) = interpᵐLRʳ Ξ η L · interpᵐLRʳ Ξ η M
interpᵐLRʳ Ξ η (Λ M) = Λ interpᵐLRʳ (plain ∷ Ξ) η M
interpᵐLRʳ Ξ η (M ⦂∀ B [ T ]) =
  interpᵐLRʳ Ξ η M ⦂∀ interpLRʳ (plain ∷ Ξ) η B
    [ interpLRʳ Ξ η T ]
interpᵐLRʳ Ξ η ($ κ) = $ κ
interpᵐLRʳ Ξ η (L ⊕[ op ] M) =
  interpᵐLRʳ Ξ η L ⊕[ op ] interpᵐLRʳ Ξ η M
interpᵐLRʳ Ξ η (M up p) = interpᵐLRʳ Ξ η M up interpUpLRʳ Ξ η p
interpᵐLRʳ Ξ η (M down p) =
  interpᵐLRʳ Ξ η M down interpDownLRʳ Ξ η p
interpᵐLRʳ Ξ η (blame ℓ) = blame ℓ

closeLRˡᵐ : ∀ {Ξ} → RelSub Ξ → World → Term → Term
closeLRˡᵐ {Ξ = Ξ} ρ w M =
  substᵗᵐ (leftᵗ ρ) (interpᵐLRˡ Ξ (νenv ρ) M)

closeLRʳᵐ : ∀ {Ξ} → RelSub Ξ → World → Term → Term
closeLRʳᵐ {Ξ = Ξ} ρ w M =
  substᵗᵐ (rightᵗ ρ) (interpᵐLRʳ Ξ (νenv ρ) M)

------------------------------------------------------------------------
-- Open-term environments and semantic judgments
------------------------------------------------------------------------

record RelEnv : Set where
  field
    leftˣ : Substˣ
    rightˣ : Substˣ
open RelEnv public

⇓γ : RelEnv → RelEnv
(⇓γ γ .leftˣ) x = leftˣ γ (suc x)
(⇓γ γ .rightˣ) x = rightˣ γ (suc x)

𝒢 :
  ∀ {Ξ} →
  PCtx Ξ → ℕ → Dir → World → RelSub Ξ → RelEnv → Set₁
𝒢 [] n dir w ρ γ = Lift (lsuc 0ℓ) ⊤
𝒢 ((A , B , p) ∷ Γ) n dir w ρ γ =
  Value (leftˣ γ zero) ×
  Value (rightˣ γ zero) ×
  𝒱 ρ p n dir w (leftˣ γ zero) (rightˣ γ zero) ×
  𝒢 Γ n dir w ρ (⇓γ γ)

record InterpWf (Ξ : ICtx) (Δ : TyCtx)
    (Ψsrc Ψdst : SealCtx) : Set where
  field
    interp-var :
      ∀ {X} →
      X < Δ →
      WfTy (plainCount Ξ) Ψdst (interpVar Ξ X)
    interp-seal :
      ∀ {α} →
      α < Ψsrc →
      interpSeal Ξ α < Ψdst
open InterpWf public

InterpWf-plain :
  ∀ {Ξ Δ Ψsrc Ψdst} →
  InterpWf Ξ Δ Ψsrc Ψdst →
  InterpWf (plain ∷ Ξ) (suc Δ) Ψsrc Ψdst
InterpWf-plain iwf .InterpWf.interp-var {zero} z<s = wfVar z<s
InterpWf-plain iwf .InterpWf.interp-var {suc X} (s<s X<Δ) =
  renameᵗ-preserves-WfTy
    (interp-var iwf X<Δ)
    TyRenameWf-suc
InterpWf-plain iwf .InterpWf.interp-seal = interp-seal iwf

InterpWf-ν :
  ∀ {Ξ Δ Ψsrc Ψdst} →
  InterpWf Ξ Δ Ψsrc Ψdst →
  InterpWf (ν-bound ∷ Ξ) (suc Δ) Ψsrc (suc Ψdst)
InterpWf-ν iwf .InterpWf.interp-var {zero} z<s = wfSeal z<s
InterpWf-ν iwf .InterpWf.interp-var {suc X} (s<s X<Δ) =
  renameˢ-preserves-WfTy
    (interp-var iwf X<Δ)
    SealRenameWf-suc
InterpWf-ν iwf .InterpWf.interp-seal α<Ψsrc =
  s<s (interp-seal iwf α<Ψsrc)

InterpWf-weakenˢ :
  ∀ {Ξ Δ Ψsrc Ψdst Ψdst′} →
  Ψdst ≤ Ψdst′ →
  InterpWf Ξ Δ Ψsrc Ψdst →
  InterpWf Ξ Δ Ψsrc Ψdst′
InterpWf-weakenˢ Ψ≤ iwf .InterpWf.interp-var X<Δ =
  WfTy-weakenˢ (interp-var iwf X<Δ) Ψ≤
InterpWf-weakenˢ Ψ≤ iwf .InterpWf.interp-seal α<Ψsrc =
  <-≤-trans (interp-seal iwf α<Ψsrc) Ψ≤

interp-wf :
  ∀ {Ξ Δ Ψsrc Ψdst A} →
  InterpWf Ξ Δ Ψsrc Ψdst →
  WfTy Δ Ψsrc A →
  WfTy (plainCount Ξ) Ψdst (interp Ξ A)
interp-wf iwf (wfVar X<Δ) = interp-var iwf X<Δ
interp-wf iwf (wfSeal α<Ψ) = wfSeal (interp-seal iwf α<Ψ)
interp-wf iwf wfBase = wfBase
interp-wf iwf wf★ = wf★
interp-wf iwf (wf⇒ hA hB) =
  wf⇒ (interp-wf iwf hA) (interp-wf iwf hB)
interp-wf iwf (wf∀ hA) = wf∀ (interp-wf (InterpWf-plain iwf) hA)

record InterpLRWfˡ (Ξ : ICtx) (Δ : TyCtx)
    (Ψsrc Ψdst : SealCtx) (ηρ : List SealRel) : Set₁ where
  field
    interpLR-var :
      ∀ {X} →
      X < Δ →
      WfTy (plainCount Ξ) Ψdst (interpLRVarˡ Ξ ηρ X)
    interpLR-seal :
      ∀ {α} →
      α < Ψsrc →
      α < Ψdst
open InterpLRWfˡ public

InterpLRWfˡ-plain :
  ∀ {Ξ Δ Ψsrc Ψdst ηρ} →
  InterpLRWfˡ Ξ Δ Ψsrc Ψdst ηρ →
  InterpLRWfˡ (plain ∷ Ξ) (suc Δ) Ψsrc Ψdst ηρ
InterpLRWfˡ-plain iwf .InterpLRWfˡ.interpLR-var {zero} z<s =
  wfVar z<s
InterpLRWfˡ-plain iwf .InterpLRWfˡ.interpLR-var {suc X} (s<s X<Δ) =
  renameᵗ-preserves-WfTy
    (interpLR-var iwf X<Δ)
    TyRenameWf-suc
InterpLRWfˡ-plain iwf .InterpLRWfˡ.interpLR-seal = interpLR-seal iwf

InterpLRWfˡ-weakenˢ :
  ∀ {Ξ Δ Ψsrc Ψdst Ψdst′ ηρ} →
  Ψdst ≤ Ψdst′ →
  InterpLRWfˡ Ξ Δ Ψsrc Ψdst ηρ →
  InterpLRWfˡ Ξ Δ Ψsrc Ψdst′ ηρ
InterpLRWfˡ-weakenˢ Ψ≤ iwf .InterpLRWfˡ.interpLR-var X<Δ =
  WfTy-weakenˢ (interpLR-var iwf X<Δ) Ψ≤
InterpLRWfˡ-weakenˢ Ψ≤ iwf .InterpLRWfˡ.interpLR-seal α<Ψsrc =
  <-≤-trans (interpLR-seal iwf α<Ψsrc) Ψ≤

interpLRˡ-wf :
  ∀ {Ξ Δ Ψsrc Ψdst ηρ A} →
  InterpLRWfˡ Ξ Δ Ψsrc Ψdst ηρ →
  WfTy Δ Ψsrc A →
  WfTy (plainCount Ξ) Ψdst (interpLRˡ Ξ ηρ A)
interpLRˡ-wf iwf (wfVar X<Δ) = interpLR-var iwf X<Δ
interpLRˡ-wf iwf (wfSeal α<Ψ) = wfSeal (interpLR-seal iwf α<Ψ)
interpLRˡ-wf iwf wfBase = wfBase
interpLRˡ-wf iwf wf★ = wf★
interpLRˡ-wf iwf (wf⇒ hA hB) =
  wf⇒ (interpLRˡ-wf iwf hA) (interpLRˡ-wf iwf hB)
interpLRˡ-wf iwf (wf∀ hA) =
  wf∀ (interpLRˡ-wf (InterpLRWfˡ-plain iwf) hA)

interpLRVarˡ-plains-id :
  ∀ n Ξ η {X} →
  X < n →
  interpLRVarˡ (plains n Ξ) η X ≡ ＇ X
interpLRVarˡ-plains-id zero Ξ η ()
interpLRVarˡ-plains-id (suc n) Ξ η {zero} z<s = refl
interpLRVarˡ-plains-id (suc n) Ξ η {suc X} (s<s X<n) =
  cong ⇑ᵗ (interpLRVarˡ-plains-id n Ξ η X<n)

interpLRVarʳ-plains-id :
  ∀ n Ξ η {X} →
  X < n →
  interpLRVarʳ (plains n Ξ) η X ≡ ＇ X
interpLRVarʳ-plains-id zero Ξ η ()
interpLRVarʳ-plains-id (suc n) Ξ η {zero} z<s = refl
interpLRVarʳ-plains-id (suc n) Ξ η {suc X} (s<s X<n) =
  cong ⇑ᵗ (interpLRVarʳ-plains-id n Ξ η X<n)

interpLRˡ-plains-id :
  ∀ n Ξ η {Ψ T} →
  WfTy n Ψ T →
  interpLRˡ (plains n Ξ) η T ≡ T
interpLRˡ-plains-id n Ξ η (wfVar X<n) =
  interpLRVarˡ-plains-id n Ξ η X<n
interpLRˡ-plains-id n Ξ η (wfSeal α<Ψ) = refl
interpLRˡ-plains-id n Ξ η wfBase = refl
interpLRˡ-plains-id n Ξ η wf★ = refl
interpLRˡ-plains-id n Ξ η (wf⇒ hA hB) =
  cong₂ _⇒_ (interpLRˡ-plains-id n Ξ η hA)
             (interpLRˡ-plains-id n Ξ η hB)
interpLRˡ-plains-id n Ξ η (wf∀ hA) =
  cong `∀ (interpLRˡ-plains-id (suc n) Ξ η hA)

interpLRʳ-plains-id :
  ∀ n Ξ η {Ψ T} →
  WfTy n Ψ T →
  interpLRʳ (plains n Ξ) η T ≡ T
interpLRʳ-plains-id n Ξ η (wfVar X<n) =
  interpLRVarʳ-plains-id n Ξ η X<n
interpLRʳ-plains-id n Ξ η (wfSeal α<Ψ) = refl
interpLRʳ-plains-id n Ξ η wfBase = refl
interpLRʳ-plains-id n Ξ η wf★ = refl
interpLRʳ-plains-id n Ξ η (wf⇒ hA hB) =
  cong₂ _⇒_ (interpLRʳ-plains-id n Ξ η hA)
             (interpLRʳ-plains-id n Ξ η hB)
interpLRʳ-plains-id n Ξ η (wf∀ hA) =
  cong `∀ (interpLRʳ-plains-id (suc n) Ξ η hA)

leftᵢ-closed-id :
  ∀ {Ξ Ψ T w} (ρ : RelSub Ξ) →
  WfTy 0 Ψ T →
  leftᵢ ρ w T ≡ T
leftᵢ-closed-id {Ξ = Ξ} ρ hT =
  trans
    (cong (substᵗ (leftᵗ ρ)) (interpLRˡ-plains-id zero Ξ (νenv ρ) hT))
    (substᵗ-closed-id hT (leftᵗ ρ))

rightᵢ-closed-id :
  ∀ {Ξ Ψ T w} (ρ : RelSub Ξ) →
  WfTy 0 Ψ T →
  rightᵢ ρ w T ≡ T
rightᵢ-closed-id {Ξ = Ξ} ρ hT =
  trans
    (cong (substᵗ (rightᵗ ρ)) (interpLRʳ-plains-id zero Ξ (νenv ρ) hT))
    (substᵗ-closed-id hT (rightᵗ ρ))

closed-inst-⊑ᵢ :
  ∀ {Ξ Ψ T w} (ρ : RelSub Ξ) →
  WfTy 0 Ψ T →
  [] ⊢ leftᵢ ρ w T ⊑ᵢ rightᵢ ρ w T
closed-inst-⊑ᵢ {T = T} {w = w} ρ hT =
  ⊑ᵢ-cast (sym (leftᵢ-closed-id {w = w} ρ hT))
          (sym (rightᵢ-closed-id {w = w} ρ hT))
          (⊑ᵢ-refl {Γ = []})

record RelWfᴾ (E : TPEnv) (w : World)
    (ρ : RelSub (TPEnv.Ξ E)) : Set₁ where
  field
    Ψˡ≤ : TPEnv.Ψ E ≤ Ψˡ w
    Ψʳ≤ : TPEnv.Ψ E ≤ Ψʳ w
    interpWfˡ : InterpWf (TPEnv.Ξ E) (TPEnv.Δ E)
      (TPEnv.Ψ E) (Ψˡ w)
    interpWfʳ : InterpWf (TPEnv.Ξ E) (TPEnv.Δ E)
      (TPEnv.Ψ E) (Ψʳ w)
    interpLRWfˡ : InterpLRWfˡ (TPEnv.Ξ E) (TPEnv.Δ E)
      (TPEnv.Ψ E) (Ψˡ w) (νenv ρ)
    relWf : RelWf w ρ
open RelWfᴾ public

_∣_⊨_⊑_⦂_ :
  (E : TPEnv) → Dir → Term → Term →
  ∀ {A B} → TPEnv.Ξ E ⊢ A ⊑ᵢ B → Set₁
E ∣ dir ⊨ M ⊑ M′ ⦂ p =
  ∀ (n : ℕ) (w : World) (ρ : RelSub (TPEnv.Ξ E)) (γ : RelEnv) →
  RelWfᴾ E w ρ →
  𝒢 (TPEnv.Γ E) n dir w ρ γ →
  ℰ ρ p n dir w
    (closeLRˡᵐ ρ w (substˣ-term (leftˣ γ) M))
    (closeLRʳᵐ ρ w (substˣ-term (rightˣ γ) M′))

------------------------------------------------------------------------
-- The ν type-application compatibility probe
------------------------------------------------------------------------

substᵗ-open :
  (σ : Substᵗ) (A T : Ty) →
  substᵗ σ (A [ T ]ᵗ) ≡
  substᵗ (singleTyEnv (substᵗ σ T)) (substᵗ (extsᵗ σ) A)
substᵗ-open σ A T =
  trans
    (substᵗ-substᵗ σ (singleTyEnv T) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ (singleTyEnv (substᵗ σ T)) (extsᵗ σ) A)))
  where
  env : (X : TyVar) →
    substᵗ σ (singleTyEnv T X) ≡
    substᵗ (singleTyEnv (substᵗ σ T)) (extsᵗ σ X)
  env zero = refl
  env (suc X) = sym (open-renᵗ-suc (σ X) (substᵗ σ T))

interpSeal-plains-plain :
  ∀ n Ξ α →
  interpSeal (plains n (plain ∷ Ξ)) α ≡ interpSeal (plains n Ξ) α
interpSeal-plains-plain zero Ξ α = refl
interpSeal-plains-plain (suc n) Ξ α =
  interpSeal-plains-plain n Ξ α

interp-plains-plain-raise :
  ∀ k Ξ A →
  interp (plains k (plain ∷ Ξ)) (renameᵗ (raiseVarFrom k) A) ≡
  renameᵗ (raiseVarFrom k) (interp (plains k Ξ) A)
interp-plains-plain-raise zero Ξ (＇ X) = refl
interp-plains-plain-raise zero Ξ (｀ α) = refl
interp-plains-plain-raise zero Ξ (‵ ι) = refl
interp-plains-plain-raise zero Ξ ★ = refl
interp-plains-plain-raise zero Ξ (A ⇒ B) =
  cong₂ _⇒_
    (interp-plains-plain-raise zero Ξ A)
    (interp-plains-plain-raise zero Ξ B)
interp-plains-plain-raise zero Ξ (`∀ A) =
  cong `∀
    (trans
      (cong (interp (plains (suc zero) (plain ∷ Ξ)))
        (renameᵗ-cong (raise-ext zero) A))
      (trans
        (interp-plains-plain-raise (suc zero) Ξ A)
        (renameᵗ-cong (λ X → sym (raise-ext zero X))
          (interp (plains (suc zero) Ξ) A))))
interp-plains-plain-raise (suc k) Ξ (＇ zero) = refl
interp-plains-plain-raise (suc k) Ξ (＇ (suc X)) =
  trans
    (cong ⇑ᵗ (interp-plains-plain-raise k Ξ (＇ X)))
    (sym (rename-raise-⇑ᵗ k (interpVar (plains k Ξ) X)))
interp-plains-plain-raise (suc k) Ξ (｀ α) =
  cong ｀_ (interpSeal-plains-plain k Ξ α)
interp-plains-plain-raise (suc k) Ξ (‵ ι) = refl
interp-plains-plain-raise (suc k) Ξ ★ = refl
interp-plains-plain-raise (suc k) Ξ (A ⇒ B) =
  cong₂ _⇒_
    (interp-plains-plain-raise (suc k) Ξ A)
    (interp-plains-plain-raise (suc k) Ξ B)
interp-plains-plain-raise (suc k) Ξ (`∀ A) =
  cong `∀
    (trans
      (cong (interp (plains (suc (suc k)) (plain ∷ Ξ)))
        (renameᵗ-cong (raise-ext (suc k)) A))
      (trans
        (interp-plains-plain-raise (suc (suc k)) Ξ A)
        (renameᵗ-cong (λ X → sym (raise-ext (suc k) X))
          (interp (plains (suc (suc k)) Ξ) A))))

interpVar-open-at :
  ∀ n Ξ X T →
  interp (plains n Ξ) (substVarFrom n T X) ≡
  substᵗ (substVarFrom n (interp Ξ T))
    (interpVar (plains n (plain ∷ Ξ)) X)
interpVar-open-at zero Ξ zero T = refl
interpVar-open-at zero Ξ (suc X) T =
  sym (open-renᵗ-suc (interpVar Ξ X) (interp Ξ T))
interpVar-open-at (suc n) Ξ zero T = refl
interpVar-open-at (suc n) Ξ (suc X) T =
  trans
    (interp-plains-plain-raise zero (plains n Ξ) (substVarFrom n T X))
    (trans
      (cong ⇑ᵗ (interpVar-open-at n Ξ X T))
      (sym
        (substVarFrom-⇑ᵗ n (interp Ξ T)
          (interpVar (plains n (plain ∷ Ξ)) X))))

interp-open-at :
  ∀ n Ξ A T →
  interp (plains n Ξ) (substᵗ (substVarFrom n T) A) ≡
  substᵗ (substVarFrom n (interp Ξ T))
    (interp (plains n (plain ∷ Ξ)) A)
interp-open-at n Ξ (＇ X) T = interpVar-open-at n Ξ X T
interp-open-at n Ξ (｀ α) T =
  cong ｀_ (sym (interpSeal-plains-plain n Ξ α))
interp-open-at n Ξ (‵ ι) T = refl
interp-open-at n Ξ ★ T = refl
interp-open-at n Ξ (A ⇒ B) T =
  cong₂ _⇒_ (interp-open-at n Ξ A T) (interp-open-at n Ξ B T)
interp-open-at n Ξ (`∀ A) T = cong `∀ (interp-open-at (suc n) Ξ A T)

interp-open :
  ∀ Ξ A T →
  interp Ξ (A [ T ]ᵗ) ≡ (interp (plain ∷ Ξ) A) [ interp Ξ T ]ᵗ
interp-open Ξ A T = interp-open-at zero Ξ A T

interpLRˡ-plains-plain-raise :
  ∀ k Ξ η A →
  interpLRˡ (plains k (plain ∷ Ξ)) η (renameᵗ (raiseVarFrom k) A) ≡
  renameᵗ (raiseVarFrom k) (interpLRˡ (plains k Ξ) η A)
interpLRˡ-plains-plain-raise zero Ξ η (＇ X) = refl
interpLRˡ-plains-plain-raise zero Ξ η (｀ α) = refl
interpLRˡ-plains-plain-raise zero Ξ η (‵ ι) = refl
interpLRˡ-plains-plain-raise zero Ξ η ★ = refl
interpLRˡ-plains-plain-raise zero Ξ η (A ⇒ B) =
  cong₂ _⇒_
    (interpLRˡ-plains-plain-raise zero Ξ η A)
    (interpLRˡ-plains-plain-raise zero Ξ η B)
interpLRˡ-plains-plain-raise zero Ξ η (`∀ A) =
  cong `∀
    (trans
      (cong (interpLRˡ (plains (suc zero) (plain ∷ Ξ)) η)
        (renameᵗ-cong (raise-ext zero) A))
      (trans
        (interpLRˡ-plains-plain-raise (suc zero) Ξ η A)
        (renameᵗ-cong (λ X → sym (raise-ext zero X))
          (interpLRˡ (plains (suc zero) Ξ) η A))))
interpLRˡ-plains-plain-raise (suc k) Ξ η (＇ zero) = refl
interpLRˡ-plains-plain-raise (suc k) Ξ η (＇ (suc X)) =
  trans
    (cong ⇑ᵗ (interpLRˡ-plains-plain-raise k Ξ η (＇ X)))
    (sym (rename-raise-⇑ᵗ k (interpLRVarˡ (plains k Ξ) η X)))
interpLRˡ-plains-plain-raise (suc k) Ξ η (｀ α) = refl
interpLRˡ-plains-plain-raise (suc k) Ξ η (‵ ι) = refl
interpLRˡ-plains-plain-raise (suc k) Ξ η ★ = refl
interpLRˡ-plains-plain-raise (suc k) Ξ η (A ⇒ B) =
  cong₂ _⇒_
    (interpLRˡ-plains-plain-raise (suc k) Ξ η A)
    (interpLRˡ-plains-plain-raise (suc k) Ξ η B)
interpLRˡ-plains-plain-raise (suc k) Ξ η (`∀ A) =
  cong `∀
    (trans
      (cong (interpLRˡ (plains (suc (suc k)) (plain ∷ Ξ)) η)
        (renameᵗ-cong (raise-ext (suc k)) A))
      (trans
        (interpLRˡ-plains-plain-raise (suc (suc k)) Ξ η A)
        (renameᵗ-cong (λ X → sym (raise-ext (suc k) X))
          (interpLRˡ (plains (suc (suc k)) Ξ) η A))))

interpLRVarˡ-open-at :
  ∀ n Ξ η X T →
  interpLRˡ (plains n Ξ) η (substVarFrom n T X) ≡
  substᵗ (substVarFrom n (interpLRˡ Ξ η T))
    (interpLRVarˡ (plains n (plain ∷ Ξ)) η X)
interpLRVarˡ-open-at zero Ξ η zero T = refl
interpLRVarˡ-open-at zero Ξ η (suc X) T =
  sym (open-renᵗ-suc (interpLRVarˡ Ξ η X) (interpLRˡ Ξ η T))
interpLRVarˡ-open-at (suc n) Ξ η zero T = refl
interpLRVarˡ-open-at (suc n) Ξ η (suc X) T =
  trans
    (interpLRˡ-plains-plain-raise zero (plains n Ξ) η
      (substVarFrom n T X))
    (trans
      (cong ⇑ᵗ (interpLRVarˡ-open-at n Ξ η X T))
      (sym
        (substVarFrom-⇑ᵗ n (interpLRˡ Ξ η T)
          (interpLRVarˡ (plains n (plain ∷ Ξ)) η X))))

interpLRˡ-open-at :
  ∀ n Ξ η A T →
  interpLRˡ (plains n Ξ) η (substᵗ (substVarFrom n T) A) ≡
  substᵗ (substVarFrom n (interpLRˡ Ξ η T))
    (interpLRˡ (plains n (plain ∷ Ξ)) η A)
interpLRˡ-open-at n Ξ η (＇ X) T = interpLRVarˡ-open-at n Ξ η X T
interpLRˡ-open-at n Ξ η (｀ α) T = refl
interpLRˡ-open-at n Ξ η (‵ ι) T = refl
interpLRˡ-open-at n Ξ η ★ T = refl
interpLRˡ-open-at n Ξ η (A ⇒ B) T =
  cong₂ _⇒_
    (interpLRˡ-open-at n Ξ η A T)
    (interpLRˡ-open-at n Ξ η B T)
interpLRˡ-open-at n Ξ η (`∀ A) T =
  cong `∀ (interpLRˡ-open-at (suc n) Ξ η A T)

interpLRˡ-open :
  ∀ Ξ η A T →
  interpLRˡ Ξ η (A [ T ]ᵗ) ≡
  (interpLRˡ (plain ∷ Ξ) η A) [ interpLRˡ Ξ η T ]ᵗ
interpLRˡ-open Ξ η A T = interpLRˡ-open-at zero Ξ η A T

leftᵢ-open :
  ∀ {Ξ} (ρ : RelSub Ξ) (w : World) (A T : Ty) →
  leftᵢ ρ w (A [ T ]ᵗ) ≡
  (left∀ᵢ ρ w A) [ leftᵢ ρ w T ]ᵗ
leftᵢ-open {Ξ = Ξ} ρ w A T =
  trans
    (cong (substᵗ (leftᵗ ρ)) (interpLRˡ-open Ξ (νenv ρ) A T))
    (substᵗ-open
      (leftᵗ ρ)
      (interpLRˡ (plain ∷ Ξ) (νenv ρ) A)
      (interpLRˡ Ξ (νenv ρ) T))

left∀ᵢ-wf :
  ∀ {Ξ Δ Ψsrc A w} (ρ : RelSub Ξ) →
  InterpLRWfˡ (plain ∷ Ξ) (suc Δ) Ψsrc (Ψˡ w) (νenv ρ) →
  WfTy (suc Δ) Ψsrc A →
  TySubstWf (plainCount Ξ) 0 (Ψˡ w) (leftᵗ ρ) →
  WfTy (suc 0) (Ψˡ w) (left∀ᵢ ρ w A)
left∀ᵢ-wf {Ξ = Ξ} ρ iwf hA hσ =
  substᵗ-preserves-WfTy (interpLRˡ-wf iwf hA) (TySubstWf-exts hσ)

leftᵢ-wf :
  ∀ {Ξ Δ Ψsrc T w} (ρ : RelSub Ξ) →
  InterpLRWfˡ Ξ Δ Ψsrc (Ψˡ w) (νenv ρ) →
  WfTy Δ Ψsrc T →
  TySubstWf (plainCount Ξ) 0 (Ψˡ w) (leftᵗ ρ) →
  WfTy 0 (Ψˡ w) (leftᵢ ρ w T)
leftᵢ-wf ρ iwf hT hσ = substᵗ-preserves-WfTy (interpLRˡ-wf iwf hT) hσ

mkWorldˡ-⪰ :
  ∀ {w Σˡ′ Ψˡ′} {wfΣˡ′ : StoreWf 0 Ψˡ′ Σˡ′} →
  Σˡ w ⊆ˢ Σˡ′ →
  mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
mkWorldˡ-⪰ {w = w} {wfΣˡ′ = wfΣˡ′} grow ._⪰_.growΨˡ
  rewrite sym (StoreWf.len (wfΣˡ w)) | sym (StoreWf.len wfΣˡ′) =
  ⊆ˢ-length≤ grow
mkWorldˡ-⪰ grow ._⪰_.growΨʳ = ≤-refl
mkWorldˡ-⪰ grow ._⪰_.growˡ = grow
mkWorldˡ-⪰ grow ._⪰_.growʳ = ⊆ˢ-refl
mkWorldˡ-⪰ grow ._⪰_.growη = ⊆η-refl

mkWorldʳ-⪰ :
  ∀ {w Σʳ′ Ψʳ′} {wfΣʳ′ : StoreWf 0 Ψʳ′ Σʳ′} →
  Σʳ w ⊆ˢ Σʳ′ →
  mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
mkWorldʳ-⪰ grow ._⪰_.growΨˡ = ≤-refl
mkWorldʳ-⪰ {w = w} {wfΣʳ′ = wfΣʳ′} grow ._⪰_.growΨʳ
  rewrite sym (StoreWf.len (wfΣʳ w)) | sym (StoreWf.len wfΣʳ′) =
  ⊆ˢ-length≤ grow
mkWorldʳ-⪰ grow ._⪰_.growˡ = ⊆ˢ-refl
mkWorldʳ-⪰ grow ._⪰_.growʳ = grow
mkWorldʳ-⪰ grow ._⪰_.growη = ⊆η-refl

tyappν-left-typedᵢ :
  ∀ {Ξ Δ Ψsrc A T w L} {ρ : RelSub Ξ} →
  RelWf w ρ →
  InterpLRWfˡ (plain ∷ Ξ) (suc Δ) Ψsrc (Ψˡ w) (νenv ρ) →
  InterpLRWfˡ Ξ Δ Ψsrc (Ψˡ w) (νenv ρ) →
  WfTy (suc Δ) Ψsrc A →
  WfTy Δ Ψsrc T →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂ leftᵢ ρ w (`∀ A) →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    (L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂
    leftᵢ ρ w (A [ T ]ᵗ)
tyappν-left-typedᵢ {A = A} {T = T} {w = w} {L = L} {ρ = ρ}
    rwf iwfA iwfT wfA wfT L⊢ =
  subst
    (λ C → 0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂ C)
    (sym (leftᵢ-open ρ w A T))
    (⊢• L⊢
      (left∀ᵢ-wf {w = w} ρ iwfA wfA (leftᵗ-wf rwf))
      (leftᵢ-wf {w = w} ρ iwfT wfT (leftᵗ-wf rwf)))

tyapp-↠ :
  ∀ {Σ Σ′ L L′ B T} →
  Σ ∣ L —↠ Σ′ ∣ L′ →
  Σ ∣ (L ⦂∀ B [ T ]) —↠ Σ′ ∣ (L′ ⦂∀ B [ T ])
tyapp-↠ (L ∎) = (L ⦂∀ _ [ _ ]) ∎
tyapp-↠ (L —→⟨ L→M ⟩ M↠N) =
  (L ⦂∀ _ [ _ ]) —→⟨ ξ-·α L→M ⟩ tyapp-↠ M↠N

up-↠ :
  ∀ {Σ Σ′ M M′} {p : Up} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (M up p) —↠ Σ′ ∣ (M′ up p)
up-↠ {p = p} (M ∎) = (M up p) ∎
up-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠W) =
  (M up p) —→⟨ ξ-up M→M′ ⟩ up-↠ M′↠W

down-↠ :
  ∀ {Σ Σ′ M M′} {p : Down} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ ∣ (M down p) —↠ Σ′ ∣ (M′ down p)
down-↠ {p = p} (M ∎) = (M down p) ∎
down-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠W) =
  (M down p) —→⟨ ξ-down M→M′ ⟩ down-↠ M′↠W

up-blame-↠ :
  ∀ {Σ Σ′ M ℓ} {p : Up} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M up p) —↠ Σ′ ∣ blame ℓ
up-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ up p) —→⟨ id-step blame-up ⟩ blame ℓ ∎
up-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M up p) —→⟨ ξ-up M→M′ ⟩ up-blame-↠ M′↠blame

down-blame-↠ :
  ∀ {Σ Σ′ M ℓ} {p : Down} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M down p) —↠ Σ′ ∣ blame ℓ
down-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ down p) —→⟨ id-step blame-down ⟩ blame ℓ ∎
down-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M down p) —→⟨ ξ-down M→M′ ⟩ down-blame-↠ M′↠blame

tyapp-blame-↠ :
  ∀ {Σ Σ′ M ℓ B T} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ blame ℓ
tyapp-blame-↠ {ℓ = ℓ} {B = B} {T = T} (_ ∎) =
  (blame ℓ ⦂∀ B [ T ]) —→⟨ id-step blame-·α ⟩ blame ℓ ∎
tyapp-blame-↠ {B = B} {T = T} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩ tyapp-blame-↠ M′↠blame

data Resultᵢ (Σ : Store) (M : Term) (A : Ty) : Set where
  result-value :
    ∀ {Σ′ Ψ′ W} →
    StoreWf 0 Ψ′ Σ′ →
    Σ ∣ M —↠ Σ′ ∣ W →
    Value W →
    0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ W ⦂ A →
    Resultᵢ Σ M A

  result-blame :
    ∀ {Σ′ ℓ} →
    Σ ∣ M —↠ Σ′ ∣ blame ℓ →
    Resultᵢ Σ M A

prepend-resultᵢ :
  ∀ {Σ Σ′ M M′ A} →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Resultᵢ Σ′ M′ A →
  Resultᵢ Σ M A
prepend-resultᵢ M↠M′ (result-value wfΣ″ M′↠W vW W⊢) =
  result-value wfΣ″ (multi-trans M↠M′ M′↠W) vW W⊢
prepend-resultᵢ M↠M′ (result-blame M′↠blame) =
  result-blame (multi-trans M↠M′ M′↠blame)

multi-store-growth :
  ∀ {Σ Σ′ L L′} →
  Σ ∣ L —↠ Σ′ ∣ L′ →
  Σ ⊆ˢ Σ′
multi-store-growth (L ∎) = ⊆ˢ-refl
multi-store-growth (L —→⟨ L→M ⟩ M↠N) =
  ⊆ˢ-trans (store-growth L→M) (multi-store-growth M↠N)

ℰ-pull-≼-right-↠ :
  ∀ {Ξ A B} {ρ : RelSub Ξ} {p : Ξ ⊢ A ⊑ᵢ B}
    {k : ℕ} {w : World}
    {Σʳ′ : Store} {Ψʳ′ : SealCtx}
    {wfΣʳ′ : StoreWf 0 Ψʳ′ Σʳ′}
    {Mˡ Mʳ Mʳ′ : Term} →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ leftᵢ ρ w A →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ rightᵢ ρ w B →
  Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Mʳ′ →
  ℰ ρ p k ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Mʳ′ →
  ℰ ρ p k ≼ w Mˡ Mʳ
ℰ-pull-≼-right-↠ {k = zero} Mˡ⊢ Mʳ⊢ Mʳ↠Mʳ′ rel =
  (Mˡ⊢ , Mʳ⊢) , lift tt
ℰ-pull-≼-right-↠ {ρ = ρ} {p = p} {k = suc k} {w = w}
    Mˡ⊢ Mʳ⊢ Mʳ↠Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ , rel)) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₁
    (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ ,
      ℰ-pull-≼-right-↠ {ρ = ρ} {p = p} {k = k}
        {w = mkWorldˡ w Σˡ′ wfΣˡ′}
        (proj₁ (proj₁ rel)) Mʳ⊢ Mʳ↠Mʳ′ rel)
ℰ-pull-≼-right-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mʳ↠Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) ,
      inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , Mˡ↠blame))) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , Mˡ↠blame))
ℰ-pull-≼-right-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mʳ↠Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) ,
      inj₂ (inj₂ (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳ , Mʳ′↠Wʳ , rel))) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₂ (inj₂
    (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳ ,
     multi-trans Mʳ↠Mʳ′ Mʳ′↠Wʳ , rel))

ℰ-pull-≽-left-↠ :
  ∀ {Ξ A B} {ρ : RelSub Ξ} {p : Ξ ⊢ A ⊑ᵢ B}
    {k : ℕ} {w : World}
    {Σˡ′ : Store} {Ψˡ′ : SealCtx}
    {wfΣˡ′ : StoreWf 0 Ψˡ′ Σˡ′}
    {Mˡ Mˡ′ Mʳ : Term} →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ leftᵢ ρ w A →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ rightᵢ ρ w B →
  Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Mˡ′ →
  ℰ ρ p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Mˡ′ Mʳ →
  ℰ ρ p k ≽ w Mˡ Mʳ
ℰ-pull-≽-left-↠ {k = zero} Mˡ⊢ Mʳ⊢ Mˡ↠Mˡ′ rel =
  (Mˡ⊢ , Mʳ⊢) , lift tt
ℰ-pull-≽-left-↠ {ρ = ρ} {p = p} {k = suc k} {w = w}
    Mˡ⊢ Mʳ⊢ Mˡ↠Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , Mʳ→Mʳ′ , rel)) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₁
    (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , Mʳ→Mʳ′ ,
      ℰ-pull-≽-left-↠ {ρ = ρ} {p = p} {k = k}
        {w = mkWorldʳ w Σʳ′ wfΣʳ′}
        Mˡ⊢ (proj₂ (proj₁ rel)) Mˡ↠Mˡ′ rel)
ℰ-pull-≽-left-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mˡ↠Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) ,
      inj₂ (inj₁ (Σˡ″ , Ψˡ″ , wfΣˡ″ , ℓ , Mˡ′↠blame))) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₂ (inj₁ (Σˡ″ , Ψˡ″ , wfΣˡ″ , ℓ ,
    multi-trans Mˡ↠Mˡ′ Mˡ′↠blame))
ℰ-pull-≽-left-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mˡ↠Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) ,
      inj₂ (inj₂ (vMʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡ , Mˡ′↠Wˡ , rel))) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₂ (inj₂
    (vMʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡ ,
     multi-trans Mˡ↠Mˡ′ Mˡ′↠Wˡ , rel))

stepCtx : StepCtxShape → SealCtx → SealCtx
stepCtx shape-id Ψ = Ψ
stepCtx shape-suc Ψ = suc Ψ

step-storeWf :
  ∀ {Ψ Σ Σ′ Γ M M′ A} →
  StoreWf 0 Ψ Σ →
  0 ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  (red : Σ ∣ M —→ Σ′ ∣ M′) →
  StoreWf 0 (stepCtx (step-ctx-shape red) Ψ) Σ′
step-storeWf wfΣ M⊢ (id-step red) = wfΣ
step-storeWf wfΣ (⊢• (⊢Λ vN N⊢) wfB wfT) β-Λ =
  storeWf-fresh-extᴿ wfT wfΣ
step-storeWf wfΣ (⊢• V⊢ wfB wfT) (β-down-∀ vV) =
  storeWf-fresh-extᴿ wfT wfΣ
step-storeWf wfΣ (⊢• V⊢ wfB wfT) (β-down-ν vV) =
  storeWf-fresh-extᴿ wfT wfΣ
step-storeWf wfΣ (⊢up Φ lenΦ V⊢ hp) (β-up-ν vV) =
  storeWf-fresh-extᴿ wf★ wfΣ
step-storeWf wfΣ (⊢· L⊢ M⊢) (ξ-·₁ red) =
  step-storeWf wfΣ L⊢ red
step-storeWf wfΣ (⊢· L⊢ M⊢) (ξ-·₂ vV red) =
  step-storeWf wfΣ M⊢ red
step-storeWf wfΣ (⊢• M⊢ wfB wfT) (ξ-·α red) =
  step-storeWf wfΣ M⊢ red
step-storeWf wfΣ (⊢up Φ lenΦ M⊢ hp) (ξ-up red) =
  step-storeWf wfΣ M⊢ red
step-storeWf wfΣ (⊢down Φ lenΦ M⊢ hp) (ξ-down red) =
  step-storeWf wfΣ M⊢ red
step-storeWf wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red) =
  step-storeWf wfΣ L⊢ red
step-storeWf wfΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red) =
  step-storeWf wfΣ M⊢ red

exact-storeWf :
  ∀ {shape Ψ Ψ′ Σ} →
  StepCtxExact shape Ψ Ψ′ →
  StoreWf 0 (stepCtx shape Ψ) Σ →
  StoreWf 0 Ψ′ Σ
exact-storeWf {shape-id} eq wfΣ rewrite eq = wfΣ
exact-storeWf {shape-suc} eq wfΣ rewrite eq = wfΣ

preservation-↠ :
  ∀ {Ψ Σ Σ′ Γ M M′ A} →
  StoreWf 0 Ψ Σ →
  0 ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Σ ∣ M —↠ Σ′ ∣ M′ →
  Σ[ Ψ′ ∈ SealCtx ]
    StoreWf 0 Ψ′ Σ′ ×
    (0 ∣ Ψ′ ∣ Σ′ ∣ Γ ⊢ M′ ⦂ A)
preservation-↠ wfΣ M⊢ (M ∎) = _ , wfΣ , M⊢
preservation-↠ wfΣ M⊢ (M —→⟨ red ⟩ M′↠N)
    with preservation-step wfΣ M⊢ red
preservation-↠ wfΣ M⊢ (M —→⟨ red ⟩ M′↠N)
    | Ψ′ , eq , M′⊢ =
  preservation-↠ (exact-storeWf eq (step-storeWf wfΣ M⊢ red)) M′⊢ M′↠N

up-value-resultᵢ :
  ∀ {Ψ Σ M A B p} →
  StoreWf 0 Ψ Σ →
  UpValue p →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (M up p) ⦂ B →
  Resultᵢ Σ M A →
  Resultᵢ Σ (M up p) B
up-value-resultᵢ wfΣ vp outer⊢
    (result-value wfΣ′ M↠W vW W⊢)
    with preservation-↠ wfΣ outer⊢ (up-↠ M↠W)
up-value-resultᵢ wfΣ vp outer⊢
    (result-value wfΣ′ M↠W vW W⊢)
    | Ψ′ , wfΣ″ , Wup⊢ =
  result-value wfΣ″ (up-↠ M↠W) (vW up vp) Wup⊢
up-value-resultᵢ wfΣ vp outer⊢ (result-blame M↠blame) =
  result-blame (up-blame-↠ M↠blame)

down-value-resultᵢ :
  ∀ {Ψ Σ M A B p} →
  StoreWf 0 Ψ Σ →
  DownValue p →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (M down p) ⦂ B →
  Resultᵢ Σ M A →
  Resultᵢ Σ (M down p) B
down-value-resultᵢ wfΣ vp outer⊢
    (result-value wfΣ′ M↠W vW W⊢)
    with preservation-↠ wfΣ outer⊢ (down-↠ M↠W)
down-value-resultᵢ wfΣ vp outer⊢
    (result-value wfΣ′ M↠W vW W⊢)
    | Ψ′ , wfΣ″ , Wdown⊢ =
  result-value wfΣ″ (down-↠ M↠W) (vW down vp) Wdown⊢
down-value-resultᵢ wfΣ vp outer⊢ (result-blame M↠blame) =
  result-blame (down-blame-↠ M↠blame)

up-result-bindᵢ :
  ∀ {Ψ Σ M A B p} →
  StoreWf 0 Ψ Σ →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (M up p) ⦂ B →
  Resultᵢ Σ M A →
  (∀ {Σ′ Ψ′ W} →
    StoreWf 0 Ψ′ Σ′ →
    Value W →
    0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (W up p) ⦂ B →
    Resultᵢ Σ′ (W up p) B) →
  Resultᵢ Σ (M up p) B
up-result-bindᵢ wfΣ outer⊢ (result-value wfΣ′ M↠W vW W⊢) k
    with preservation-↠ wfΣ outer⊢ (up-↠ M↠W)
up-result-bindᵢ wfΣ outer⊢ (result-value wfΣ′ M↠W vW W⊢) k
    | Ψ′ , wfΣ″ , Wup⊢ =
  prepend-resultᵢ (up-↠ M↠W) (k wfΣ″ vW Wup⊢)
up-result-bindᵢ wfΣ outer⊢ (result-blame M↠blame) k =
  result-blame (up-blame-↠ M↠blame)

down-result-bindᵢ :
  ∀ {Ψ Σ M A B p} →
  StoreWf 0 Ψ Σ →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (M down p) ⦂ B →
  Resultᵢ Σ M A →
  (∀ {Σ′ Ψ′ W} →
    StoreWf 0 Ψ′ Σ′ →
    Value W →
    0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (W down p) ⦂ B →
    Resultᵢ Σ′ (W down p) B) →
  Resultᵢ Σ (M down p) B
down-result-bindᵢ wfΣ outer⊢ (result-value wfΣ′ M↠W vW W⊢) k
    with preservation-↠ wfΣ outer⊢ (down-↠ M↠W)
down-result-bindᵢ wfΣ outer⊢ (result-value wfΣ′ M↠W vW W⊢) k
    | Ψ′ , wfΣ″ , Wdown⊢ =
  prepend-resultᵢ (down-↠ M↠W) (k wfΣ″ vW Wdown⊢)
down-result-bindᵢ wfΣ outer⊢ (result-blame M↠blame) k =
  result-blame (down-blame-↠ M↠blame)

tyapp-result-bindᵢ :
  ∀ {Ψ Σ M A B C T} →
  StoreWf 0 Ψ Σ →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (M ⦂∀ B [ T ]) ⦂ C →
  Resultᵢ Σ M A →
  (∀ {Σ′ Ψ′ W} →
    StoreWf 0 Ψ′ Σ′ →
    Value W →
    0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (W ⦂∀ B [ T ]) ⦂ C →
    Resultᵢ Σ′ (W ⦂∀ B [ T ]) C) →
  Resultᵢ Σ (M ⦂∀ B [ T ]) C
tyapp-result-bindᵢ wfΣ outer⊢ (result-value wfΣ′ M↠W vW W⊢) k
    with preservation-↠ wfΣ outer⊢ (tyapp-↠ M↠W)
tyapp-result-bindᵢ wfΣ outer⊢ (result-value wfΣ′ M↠W vW W⊢) k
    | Ψ′ , wfΣ″ , Wtyapp⊢ =
  prepend-resultᵢ (tyapp-↠ M↠W) (k wfΣ″ vW Wtyapp⊢)
tyapp-result-bindᵢ wfΣ outer⊢ (result-blame M↠blame) k =
  result-blame (tyapp-blame-↠ M↠blame)

up-immediate-resultᵢ :
  ∀ {Ψ Σ V B p} →
  StoreWf 0 Ψ Σ →
  Value V →
  UpValue p →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V up p) ⦂ B →
  Resultᵢ Σ (V up p) B
up-immediate-resultᵢ wfΣ vV vp outer⊢ =
  result-value wfΣ (( _ up _ ) ∎) (vV up vp) outer⊢

down-immediate-resultᵢ :
  ∀ {Ψ Σ V B p} →
  StoreWf 0 Ψ Σ →
  Value V →
  DownValue p →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V down p) ⦂ B →
  Resultᵢ Σ (V down p) B
down-immediate-resultᵢ wfΣ vV vp outer⊢ =
  result-value wfΣ (( _ down _ ) ∎) (vV down vp) outer⊢

up-id-resultᵢ :
  ∀ {Ψ Σ V A} →
  StoreWf 0 Ψ Σ →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V up id A) ⦂ A →
  Resultᵢ Σ (V up id A) A
up-id-resultᵢ wfΣ vV outer⊢
    with preservation-step wfΣ outer⊢ (id-step (id-up vV))
up-id-resultᵢ wfΣ vV outer⊢ | Ψ′ , eq , V⊢
    rewrite eq =
  result-value wfΣ
    (( _ up _ ) —→⟨ id-step (id-up vV) ⟩ _ ∎)
    vV V⊢

down-id-resultᵢ :
  ∀ {Ψ Σ V A} →
  StoreWf 0 Ψ Σ →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V down id A) ⦂ A →
  Resultᵢ Σ (V down id A) A
down-id-resultᵢ wfΣ vV outer⊢
    with preservation-step wfΣ outer⊢ (id-step (id-down vV))
down-id-resultᵢ wfΣ vV outer⊢ | Ψ′ , eq , V⊢
    rewrite eq =
  result-value wfΣ
    (( _ down _ ) —→⟨ id-step (id-down vV) ⟩ _ ∎)
    vV V⊢

up-unseal-resultᵢ :
  ∀ {Ψ Σ V A α} →
  StoreWf 0 Ψ Σ →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V up unseal α) ⦂ A →
  Resultᵢ Σ (V up unseal α) A
up-unseal-resultᵢ wfΣ vV
    outer⊢@(⊢up Φ lenΦ V⊢ (wt-unseal h α∈))
    with canonical-｀ vV V⊢
up-unseal-resultᵢ wfΣ vV
    outer⊢@(⊢up Φ lenΦ V⊢ (wt-unseal h α∈))
    | sv-down-seal {W = W} vW refl
    with preservation-step wfΣ outer⊢ (id-step (seal-unseal vW))
up-unseal-resultᵢ wfΣ vV
    outer⊢@(⊢up Φ lenΦ V⊢ (wt-unseal h α∈))
    | sv-down-seal {W = W} vW refl | Ψ′ , eq , W⊢
    rewrite eq =
  result-value wfΣ
    (( _ up _ ) —→⟨ id-step (seal-unseal vW) ⟩ W ∎)
    vW W⊢
up-unseal-resultᵢ wfΣ vV
    outer⊢@(⊢up Φ lenΦ V⊢ (wt-unseal★ h α∈))
    with canonical-｀ vV V⊢
up-unseal-resultᵢ wfΣ vV
    outer⊢@(⊢up Φ lenΦ V⊢ (wt-unseal★ h α∈))
    | sv-down-seal {W = W} vW refl
    with preservation-step wfΣ outer⊢ (id-step (seal-unseal vW))
up-unseal-resultᵢ wfΣ vV
    outer⊢@(⊢up Φ lenΦ V⊢ (wt-unseal★ h α∈))
    | sv-down-seal {W = W} vW refl | Ψ′ , eq , W⊢
    rewrite eq =
  result-value wfΣ
    (( _ up _ ) —→⟨ id-step (seal-unseal vW) ⟩ W ∎)
    vW W⊢

down-untag-resultᵢ :
  ∀ {Ψ Σ V G ℓ} →
  StoreWf 0 Ψ Σ →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V down untag G ℓ) ⦂ G →
  Resultᵢ Σ (V down untag G ℓ) G
down-untag-resultᵢ wfΣ vV outer⊢@(⊢down Φ lenΦ V⊢ (wt-untag g′ gok ℓ))
    with canonical-★ vV V⊢
down-untag-resultᵢ wfΣ vV outer⊢@(⊢down Φ lenΦ V⊢ (wt-untag g′ gok ℓ))
    | sv-up-tag {g = g} vW refl
    with g ≟Ground g′
down-untag-resultᵢ wfΣ vV outer⊢@(⊢down Φ lenΦ V⊢ (wt-untag g′ gok ℓ))
    | sv-up-tag {g = g} vW refl | yes refl
    with preservation-step wfΣ outer⊢ (id-step (tag-untag-ok vW))
down-untag-resultᵢ wfΣ vV outer⊢@(⊢down Φ lenΦ V⊢ (wt-untag g′ gok ℓ))
    | sv-up-tag {W = W} {g = g} vW refl | yes refl
    | Ψ′ , eq , W⊢
    rewrite eq =
  result-value wfΣ
    (( _ down _ ) —→⟨ id-step (tag-untag-ok vW) ⟩ W ∎)
    vW W⊢
down-untag-resultᵢ wfΣ vV outer⊢@(⊢down Φ lenΦ V⊢ (wt-untag g′ gok ℓ))
    | sv-up-tag {g = g} vW refl | no neq =
  result-blame
    (( _ down _ ) —→⟨ id-step (tag-untag-bad vW neq) ⟩ blame ℓ ∎)

up-compose-resultᵢ :
  ∀ {Ψ Σ V B C p q} →
  StoreWf 0 Ψ Σ →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V up (p ； q)) ⦂ C →
  Resultᵢ Σ (V up p) B →
  (∀ {Σ′ Ψ′ W} →
    StoreWf 0 Ψ′ Σ′ →
    Value W →
    0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (W up q) ⦂ C →
    Resultᵢ Σ′ (W up q) C) →
  Resultᵢ Σ (V up (p ； q)) C
up-compose-resultᵢ wfΣ vV
    outer⊢@(⊢up Φ lenΦ V⊢ (wt-； p⊢ q⊢)) first cont
    with preservation-step wfΣ outer⊢ (id-step (β-up-； vV))
up-compose-resultᵢ wfΣ vV
    outer⊢@(⊢up Φ lenΦ V⊢ (wt-； p⊢ q⊢)) first cont
    | Ψ′ , eq , step⊢
    rewrite eq =
  prepend-resultᵢ
    (( _ up _ ) —→⟨ id-step (β-up-； vV) ⟩ _ ∎)
    (up-result-bindᵢ wfΣ step⊢ first cont)

down-compose-resultᵢ :
  ∀ {Ψ Σ V B C p q} →
  StoreWf 0 Ψ Σ →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V down (p ； q)) ⦂ C →
  Resultᵢ Σ (V down p) B →
  (∀ {Σ′ Ψ′ W} →
    StoreWf 0 Ψ′ Σ′ →
    Value W →
    0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ (W down q) ⦂ C →
    Resultᵢ Σ′ (W down q) C) →
  Resultᵢ Σ (V down (p ； q)) C
down-compose-resultᵢ wfΣ vV
    outer⊢@(⊢down Φ lenΦ V⊢ (wt-； p⊢ q⊢)) first cont
    with preservation-step wfΣ outer⊢ (id-step (β-down-； vV))
down-compose-resultᵢ wfΣ vV
    outer⊢@(⊢down Φ lenΦ V⊢ (wt-； p⊢ q⊢)) first cont
    | Ψ′ , eq , step⊢
    rewrite eq =
  prepend-resultᵢ
    (( _ down _ ) —→⟨ id-step (β-down-； vV) ⟩ _ ∎)
    (down-result-bindᵢ wfΣ step⊢ first cont)

instCast⊑-top-↠value :
  ∀ {A B α Ψ Σ V} →
  WfTy (suc zero) Ψ B →
  StoreWf 0 (suc Ψ) Σ →
  Value V →
  0 ∣ suc Ψ ∣ Σ ∣ [] ⊢ V ⦂ B [ ｀ α ]ᵗ →
  0 ∣ suc Ψ ∣ Σ ∣ [] ⊢
    (V up instCast⊑ {A = A} {B = B} {α = α}) ⦂ B [ A ]ᵗ →
  Σ[ W ∈ Term ]
    (Σ ∣ (V up instCast⊑ {A = A} {B = B} {α = α}) —↠ Σ ∣ W) ×
    Value W ×
    (0 ∣ suc Ψ ∣ Σ ∣ [] ⊢ W ⦂ B [ A ]ᵗ)
instCast⊑-top-↠value {A = A} {B = ＇ zero} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    with canonical-｀ vV V⊢
instCast⊑-top-↠value {A = A} {B = ＇ zero} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    | sv-down-seal {W = W} vW refl
    with preservation-step wfΣ cast⊢ (id-step (seal-unseal vW))
instCast⊑-top-↠value {A = A} {B = ＇ zero} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    | sv-down-seal {W = W} vW refl | Ψ′ , eq , W⊢
    rewrite eq =
  W ,
  ((V up instCast⊑ {A = A} {B = ＇ zero} {α = α})
    —→⟨ id-step (seal-unseal vW) ⟩ W ∎) ,
  vW , W⊢
instCast⊑-top-↠value {B = ＇ (suc X)} (wfVar (s<s ())) wfΣ vV V⊢ cast⊢
instCast⊑-top-↠value {A = A} {B = ｀ β} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    with preservation-step wfΣ cast⊢ (id-step (id-up vV))
instCast⊑-top-↠value {A = A} {B = ｀ β} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    | Ψ′ , eq , W⊢
    rewrite eq =
  V ,
  ((V up instCast⊑ {A = A} {B = ｀ β} {α = α})
    —→⟨ id-step (id-up vV) ⟩ V ∎) ,
  vV , W⊢
instCast⊑-top-↠value {A = A} {B = ‵ ι} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    with preservation-step wfΣ cast⊢ (id-step (id-up vV))
instCast⊑-top-↠value {A = A} {B = ‵ ι} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    | Ψ′ , eq , W⊢
    rewrite eq =
  V ,
  ((V up instCast⊑ {A = A} {B = ‵ ι} {α = α})
    —→⟨ id-step (id-up vV) ⟩ V ∎) ,
  vV , W⊢
instCast⊑-top-↠value {A = A} {B = ★} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    with preservation-step wfΣ cast⊢ (id-step (id-up vV))
instCast⊑-top-↠value {A = A} {B = ★} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    | Ψ′ , eq , W⊢
    rewrite eq =
  V ,
  ((V up instCast⊑ {A = A} {B = ★} {α = α})
    —→⟨ id-step (id-up vV) ⟩ V ∎) ,
  vV , W⊢
instCast⊑-top-↠value {A = A} {B = B₁ ⇒ B₂} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢ =
  (V up instCast⊑ {A = A} {B = B₁ ⇒ B₂} {α = α}) ,
  ((V up instCast⊑ {A = A} {B = B₁ ⇒ B₂} {α = α}) ∎) ,
  (vV up _↦_) , cast⊢
instCast⊑-top-↠value {A = A} {B = `∀ B} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢ =
  (V up instCast⊑ {A = A} {B = `∀ B} {α = α}) ,
  ((V up instCast⊑ {A = A} {B = `∀ B} {α = α}) ∎) ,
  (vV up ∀ᵖ) , cast⊢

instCast⊑-top-resultᵢ :
  ∀ {A B α Ψ Σ V} →
  WfTy (suc zero) Ψ B →
  StoreWf 0 (suc Ψ) Σ →
  Value V →
  0 ∣ suc Ψ ∣ Σ ∣ [] ⊢ V ⦂ B [ ｀ α ]ᵗ →
  0 ∣ suc Ψ ∣ Σ ∣ [] ⊢
    (V up instCast⊑ {A = A} {B = B} {α = α}) ⦂ B [ A ]ᵗ →
  Resultᵢ Σ (V up instCast⊑ {A = A} {B = B} {α = α}) (B [ A ]ᵗ)
instCast⊑-top-resultᵢ {A = A} {B = B} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    with instCast⊑-top-↠value
      {A = A} {B = B} {α = α} hB wfΣ vV V⊢ cast⊢
instCast⊑-top-resultᵢ {A = A} {B = B} {α = α} {V = V}
    hB wfΣ vV V⊢ cast⊢
    | W , cast↠W , vW , W⊢ =
  result-value wfΣ cast↠W vW W⊢

tyapp-Λ-↠valueᵢ :
  ∀ {B T C w N} →
  WfTy 0 (Ψˡ w) T →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ (Λ N) ⦂ `∀ B →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ ((Λ N) ⦂∀ B [ T ]) ⦂ C →
  Σ[ Σ′ ∈ Store ] Σ[ Ψ′ ∈ SealCtx ] Σ[ wfΣ′ ∈ StoreWf 0 Ψ′ Σ′ ]
  Σ[ W ∈ Term ]
    (Σˡ w ∣ ((Λ N) ⦂∀ B [ T ]) —↠ Σ′ ∣ W) ×
    Value W ×
    (0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ W ⦂ C)
tyapp-Λ-↠valueᵢ {B = B} {T = T} {w = w} {N = N}
    hT V⊢ app⊢@(⊢• (⊢Λ vN N⊢) wfB wfT)
    with preservation-step (wfΣˡ w) app⊢ β-Λ
tyapp-Λ-↠valueᵢ {B = B} {T = T} {w = w} {N = N}
    hT V⊢ app⊢@(⊢• (⊢Λ vN N⊢) wfB wfT)
    | Ψ′ , eq , step⊢
    rewrite eq
    with instCast⊑-top-↠value
      {A = T} {B = B} {α = length (Σˡ w)}
      wfB
      (storeWf-fresh-extᴿ hT (wfΣˡ w))
      (substᵗᵐ-value (singleTyEnv (｀ length (Σˡ w))) vN)
      (wkΣ-term
        (drop ⊆ˢ-refl)
        ([]ᵀ-wt
          (wkΨ-term-suc N⊢)
          (｀ length (Σˡ w))
          (wfSeal (len<suc-StoreWf (wfΣˡ w)))))
      step⊢
tyapp-Λ-↠valueᵢ {B = B} {T = T} {w = w} {N = N}
    hT V⊢ app⊢@(⊢• (⊢Λ vN N⊢) wfB wfT)
    | Ψ′ , eq , step⊢
    | W , cast↠ , vW , W⊢
    rewrite eq =
  ((length (Σˡ w) , T) ∷ Σˡ w) ,
  suc (Ψˡ w) ,
  storeWf-fresh-extᴿ hT (wfΣˡ w) ,
  W ,
  (((Λ N) ⦂∀ B [ T ]) —→⟨ β-Λ ⟩ cast↠) ,
  vW , W⊢

tyapp-Λ-resultᵢ :
  ∀ {B T C w N} →
  WfTy 0 (Ψˡ w) T →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ (Λ N) ⦂ `∀ B →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ ((Λ N) ⦂∀ B [ T ]) ⦂ C →
  Resultᵢ (Σˡ w) ((Λ N) ⦂∀ B [ T ]) C
tyapp-Λ-resultᵢ {B = B} {T = T} {C = C} {w = w} {N = N}
    hT V⊢ app⊢
    with tyapp-Λ-↠valueᵢ {B = B} {T = T} {C = C} {w = w} {N = N}
      hT V⊢ app⊢
tyapp-Λ-resultᵢ {B = B} {T = T} {C = C} {w = w} {N = N}
    hT V⊢ app⊢
    | Σ′ , Ψ′ , wfΣ′ , W , app↠W , vW , W⊢ =
  result-value wfΣ′ app↠W vW W⊢

{-# TERMINATING #-}
mutual
  up-cast-value-resultᵢ :
    ∀ {Ψ Σ V B p} →
    StoreWf 0 Ψ Σ →
    Value V →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V up p) ⦂ B →
    Resultᵢ Σ (V up p) B
  up-cast-value-resultᵢ wfΣ vV outer⊢@(⊢up Φ lenΦ V⊢ (wt-tag g gok)) =
    up-immediate-resultᵢ wfΣ vV tag outer⊢
  up-cast-value-resultᵢ wfΣ vV outer⊢@(⊢up Φ lenΦ V⊢ (wt-unseal h α∈)) =
    up-unseal-resultᵢ wfΣ vV outer⊢
  up-cast-value-resultᵢ wfΣ vV outer⊢@(⊢up Φ lenΦ V⊢ (wt-unseal★ h α∈)) =
    up-unseal-resultᵢ wfΣ vV outer⊢
  up-cast-value-resultᵢ wfΣ vV outer⊢@(⊢up Φ lenΦ V⊢ (wt-↦ p⊢ q⊢)) =
    up-immediate-resultᵢ wfΣ vV _↦_ outer⊢
  up-cast-value-resultᵢ wfΣ vV outer⊢@(⊢up Φ lenΦ V⊢ (wt-∀ p⊢)) =
    up-immediate-resultᵢ wfΣ vV ∀ᵖ outer⊢
  up-cast-value-resultᵢ wfΣ vV outer⊢@(⊢up Φ lenΦ V⊢ (wt-ν p⊢)) =
    up-ν-value-resultᵢ-proof wfΣ vV outer⊢
  up-cast-value-resultᵢ wfΣ vV outer⊢@(⊢up Φ lenΦ V⊢ (wt-id wfA)) =
    up-id-resultᵢ wfΣ vV outer⊢
  up-cast-value-resultᵢ wfΣ vV
      outer⊢@(⊢up Φ lenΦ V⊢ (wt-； p⊢ q⊢)) =
    up-compose-resultᵢ wfΣ vV outer⊢
      (up-cast-value-resultᵢ wfΣ vV (⊢up Φ lenΦ V⊢ p⊢))
      (λ wfΣ′ vW Wupq⊢ → up-cast-value-resultᵢ wfΣ′ vW Wupq⊢)

  down-cast-value-resultᵢ :
    ∀ {Ψ Σ V B p} →
    StoreWf 0 Ψ Σ →
    Value V →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V down p) ⦂ B →
    Resultᵢ Σ (V down p) B
  down-cast-value-resultᵢ wfΣ vV
      outer⊢@(⊢down Φ lenΦ V⊢ (wt-untag g ℓok ℓ)) =
    down-untag-resultᵢ wfΣ vV outer⊢
  down-cast-value-resultᵢ wfΣ vV
      outer⊢@(⊢down Φ lenΦ V⊢ (wt-seal h α∈)) =
    down-immediate-resultᵢ wfΣ vV seal outer⊢
  down-cast-value-resultᵢ wfΣ vV
      outer⊢@(⊢down Φ lenΦ V⊢ (wt-seal★ h α∈)) =
    down-immediate-resultᵢ wfΣ vV seal outer⊢
  down-cast-value-resultᵢ wfΣ vV
      outer⊢@(⊢down Φ lenΦ V⊢ (wt-↦ p⊢ q⊢)) =
    down-immediate-resultᵢ wfΣ vV _↦_ outer⊢
  down-cast-value-resultᵢ wfΣ vV
      outer⊢@(⊢down Φ lenΦ V⊢ (wt-∀ p⊢)) =
    down-immediate-resultᵢ wfΣ vV ∀ᵖ outer⊢
  down-cast-value-resultᵢ wfΣ vV
      outer⊢@(⊢down Φ lenΦ V⊢ (wt-ν p⊢)) =
    down-immediate-resultᵢ wfΣ vV ν_ outer⊢
  down-cast-value-resultᵢ wfΣ vV
      outer⊢@(⊢down Φ lenΦ V⊢ (wt-id wfA)) =
    down-id-resultᵢ wfΣ vV outer⊢
  down-cast-value-resultᵢ wfΣ vV
      outer⊢@(⊢down Φ lenΦ V⊢ (wt-； p⊢ q⊢)) =
    down-compose-resultᵢ wfΣ vV outer⊢
      (down-cast-value-resultᵢ wfΣ vV (⊢down Φ lenΦ V⊢ p⊢))
      (λ wfΣ′ vW Wdownq⊢ → down-cast-value-resultᵢ wfΣ′ vW Wdownq⊢)

  tyapp-up∀-resultᵢ :
    ∀ {B T C w V p} →
    WfTy 0 (Ψˡ w) T →
    Value V →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ (V up ∀ᵖ p) ⦂ `∀ B →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ ((V up ∀ᵖ p) ⦂∀ B [ T ]) ⦂ C →
    (∀ {B′ C′} →
      0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ (V ⦂∀ B′ [ T ]) ⦂ C′ →
      Resultᵢ (Σˡ w) (V ⦂∀ B′ [ T ]) C′) →
    Resultᵢ (Σˡ w) ((V up ∀ᵖ p) ⦂∀ B [ T ]) C
  tyapp-up∀-resultᵢ {B = B} {T = T} {C = C} {w = w} {V = V} {p = p}
      hT vV V∀⊢@(⊢up Φ lenΦ V⊢ (wt-∀ p⊢)) app⊢ rec
      with preservation-step (wfΣˡ w) app⊢ (id-step (β-up-∀ vV))
  tyapp-up∀-resultᵢ {B = B} {T = T} {C = C} {w = w} {V = V} {p = p}
      hT vV V∀⊢@(⊢up Φ lenΦ V⊢ (wt-∀ p⊢)) app⊢ rec
      | Ψ′ , eq , step⊢
      rewrite eq
      with step⊢
  tyapp-up∀-resultᵢ {B = B} {T = T} {C = C} {w = w} {V = V} {p = p}
      hT vV V∀⊢@(⊢up Φ lenΦ V⊢ (wt-∀ p⊢)) app⊢ rec
      | Ψ′ , eq , step⊢
      | ⊢up Φ′ lenΦ′ innerApp⊢ pT⊢
      rewrite eq =
    prepend-resultᵢ
      (((V up ∀ᵖ p) ⦂∀ B [ T ])
        —→⟨ id-step (β-up-∀ vV) ⟩ _ ∎)
      (up-result-bindᵢ
        (wfΣˡ w)
        (⊢up Φ′ lenΦ′ innerApp⊢ pT⊢)
        (rec innerApp⊢)
        (λ wfΣ′ vW Wup⊢ → up-cast-value-resultᵢ wfΣ′ vW Wup⊢))

  tyapp-value-resultᵢ :
    ∀ {B T C w V} →
    WfTy 0 (Ψˡ w) T →
    Value V →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ (V ⦂∀ B [ T ]) ⦂ C →
    Resultᵢ (Σˡ w) (V ⦂∀ B [ T ]) C
  tyapp-value-resultᵢ {B = B} {T = T} {C = C} {w = w} {V = V}
      hT vV app⊢@(⊢• V⊢ wfB wfT)
      with canonical-∀ vV V⊢
  tyapp-value-resultᵢ {B = B} {T = T} {C = C} {w = w} {V = Λ N}
      hT vV app⊢@(⊢• V⊢ wfB wfT)
      | av-Λ refl =
    tyapp-Λ-resultᵢ {B = B} {T = T} {C = C} {w = w} {N = N}
      hT V⊢ app⊢
  tyapp-value-resultᵢ {B = B} {T = T} {C = C} {w = w}
      {V = V up ∀ᵖ p}
      hT (vInner up ∀ᵖ) app⊢@(⊢• V∀⊢ wfB wfT)
      | av-up-∀ vW refl =
    tyapp-up∀-resultᵢ {B = B} {T = T} {C = C} {w = w}
      {V = V} {p = p}
      hT vW V∀⊢ app⊢
      (λ innerApp⊢ → tyapp-value-resultᵢ {T = T} {w = w}
        hT vW innerApp⊢)
  tyapp-value-resultᵢ {B = B} {T = T} {C = C} {w = w}
      hT vV app⊢@(⊢• V⊢ wfB wfT)
      | av-down-∀ vW refl =
    tyapp-down∀-resultᵢ {B = B} {T = T} {C = C} {w = w}
      hT vW V⊢ app⊢
  tyapp-value-resultᵢ {B = B} {T = T} {C = C} {w = w}
      hT vV app⊢@(⊢• V⊢ wfB wfT)
      | av-down-ν vW refl =
    tyapp-downν-resultᵢ {B = B} {T = T} {C = C} {w = w}
      hT vW V⊢ app⊢

  tyapp-down∀-resultᵢ :
    ∀ {B T C w V p} →
    WfTy 0 (Ψˡ w) T →
    Value V →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ (V down ∀ᵖ p) ⦂ `∀ B →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ ((V down ∀ᵖ p) ⦂∀ B [ T ]) ⦂ C →
    Resultᵢ (Σˡ w) ((V down ∀ᵖ p) ⦂∀ B [ T ]) C
  tyapp-down∀-resultᵢ {B = B} {T = T} {C = C} {w = w}
      {V = V} {p = p}
      hT vV V∀⊢@(⊢down Φ lenΦ V⊢ (wt-∀ p⊢)) app⊢
      with preservation-step (wfΣˡ w) app⊢ (β-down-∀ vV)
  tyapp-down∀-resultᵢ {B = B} {T = T} {C = C} {w = w}
      {V = V} {p = p}
      hT vV V∀⊢@(⊢down Φ lenΦ V⊢ (wt-∀ p⊢)) app⊢
      | Ψ′ , eq , step⊢
      rewrite eq
      with step⊢
  tyapp-down∀-resultᵢ {B = B} {T = T} {C = C} {w = w}
      {V = V} {p = p}
      hT vV V∀⊢@(⊢down Φ lenΦ V⊢ (wt-∀ p⊢)) app⊢
      | Ψ′ , eq , step⊢
      | ⊢up Φup lenΦup down⊢ up⊢
      rewrite eq
      with down⊢
  tyapp-down∀-resultᵢ {B = B} {T = T} {C = C} {w = w}
      {V = V} {p = p}
      hT vV V∀⊢@(⊢down Φ lenΦ V⊢ (wt-∀ p⊢)) app⊢
      | Ψ′ , eq , step⊢
      | ⊢up Φup lenΦup down⊢ up⊢
      | ⊢down Φdown lenΦdown innerApp⊢ downCast⊢
      rewrite eq =
    prepend-resultᵢ
      (((V down ∀ᵖ p) ⦂∀ B [ T ])
        —→⟨ β-down-∀ vV ⟩ _ ∎)
      (up-result-bindᵢ
        wfΣfresh
        (⊢up Φup lenΦup down⊢ up⊢)
        (down-result-bindᵢ
          wfΣfresh
          down⊢
          (tyapp-value-resultᵢ {w = wfresh}
            (wfSeal (len<suc-StoreWf (wfΣˡ w)))
            vV
            innerApp⊢)
          (λ wfΣ′ vW Wdown⊢ →
            down-cast-value-resultᵢ wfΣ′ vW Wdown⊢))
        (λ wfΣ′ vW Wup⊢ → up-cast-value-resultᵢ wfΣ′ vW Wup⊢))
    where
    wfΣfresh : StoreWf 0 (suc (Ψˡ w))
      ((length (Σˡ w) , T) ∷ Σˡ w)
    wfΣfresh = storeWf-fresh-extᴿ hT (wfΣˡ w)

    wfresh : World
    wfresh =
      mkWorld (suc (Ψˡ w)) (Ψʳ w)
        ((length (Σˡ w) , T) ∷ Σˡ w)
        (Σʳ w)
        wfΣfresh
        (wfΣʳ w)
        (η w)

  tyapp-downν-resultᵢ :
    ∀ {B T C w V p} →
    WfTy 0 (Ψˡ w) T →
    Value V →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ (V down ν p) ⦂ `∀ B →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ ((V down ν p) ⦂∀ B [ T ]) ⦂ C →
    Resultᵢ (Σˡ w) ((V down ν p) ⦂∀ B [ T ]) C
  tyapp-downν-resultᵢ {B = B} {T = T} {C = C} {w = w}
      {V = V} {p = p}
      hT vV V∀⊢@(⊢down Φ lenΦ V⊢ (wt-ν p⊢)) app⊢
      with preservation-step (wfΣˡ w) app⊢ (β-down-ν vV)
  tyapp-downν-resultᵢ {B = B} {T = T} {C = C} {w = w}
      {V = V} {p = p}
      hT vV V∀⊢@(⊢down Φ lenΦ V⊢ (wt-ν p⊢)) app⊢
      | Ψ′ , eq , step⊢
      rewrite eq
      with step⊢
  tyapp-downν-resultᵢ {B = B} {T = T} {C = C} {w = w}
      {V = V} {p = p}
      hT vV V∀⊢@(⊢down Φ lenΦ V⊢ (wt-ν p⊢)) app⊢
      | Ψ′ , eq , step⊢
      | ⊢up Φup lenΦup down⊢ up⊢
      rewrite eq =
    prepend-resultᵢ
      (((V down ν p) ⦂∀ B [ T ])
        —→⟨ β-down-ν vV ⟩ _ ∎)
      (up-result-bindᵢ
        wfΣfresh
        (⊢up Φup lenΦup down⊢ up⊢)
        (down-cast-value-resultᵢ wfΣfresh vV down⊢)
        (λ wfΣ′ vW Wup⊢ → up-cast-value-resultᵢ wfΣ′ vW Wup⊢))
    where
    wfΣfresh : StoreWf 0 (suc (Ψˡ w))
      ((length (Σˡ w) , T) ∷ Σˡ w)
    wfΣfresh = storeWf-fresh-extᴿ hT (wfΣˡ w)

  up-ν-value-resultᵢ-proof :
    ∀ {Ψ Σ V B p} →
    StoreWf 0 Ψ Σ →
    Value V →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V up ν p) ⦂ B →
    Resultᵢ Σ (V up ν p) B
  up-ν-value-resultᵢ-proof {Ψ = Ψ} {Σ = Σ} {V = V} {B = B} {p = p}
      wfΣ vV outer⊢@(⊢up Φ lenΦ V⊢ (wt-ν p⊢))
      with preservation-step wfΣ outer⊢ (β-up-ν vV)
  up-ν-value-resultᵢ-proof {Ψ = Ψ} {Σ = Σ} {V = V} {B = B} {p = p}
      wfΣ vV outer⊢@(⊢up Φ lenΦ V⊢ (wt-ν p⊢))
      | Ψ′ , eq , step⊢
      rewrite eq
      with step⊢
  up-ν-value-resultᵢ-proof {Ψ = Ψ} {Σ = Σ} {V = V} {B = B} {p = p}
      wfΣ vV outer⊢@(⊢up Φ lenΦ V⊢ (wt-ν p⊢))
      | Ψ′ , eq , step⊢
      | ⊢up Φ′ lenΦ′ app⊢ pFresh⊢
      rewrite eq =
    prepend-resultᵢ
      ((V up ν p) —→⟨ β-up-ν vV ⟩ _ ∎)
      (up-result-bindᵢ
        wfΣfresh
        (⊢up Φ′ lenΦ′ app⊢ pFresh⊢)
        (tyapp-value-resultᵢ {w = wfresh}
          (wfSeal (len<suc-StoreWf wfΣ))
          vV
          app⊢)
        (λ wfΣ′ vW Wup⊢ → up-cast-value-resultᵢ wfΣ′ vW Wup⊢))
    where
    wfΣfresh : StoreWf 0 (suc Ψ) ((length Σ , ★) ∷ Σ)
    wfΣfresh = storeWf-fresh-extᴿ wf★ wfΣ

    wfresh : World
    wfresh = mkWorld (suc Ψ) Ψ ((length Σ , ★) ∷ Σ) Σ wfΣfresh wfΣ []

tyapp-value-stepᵢ :
  ∀ {B T C w V} →
  WfTy 0 (Ψˡ w) T →
  Value V →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ `∀ B →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ (V ⦂∀ B [ T ]) ⦂ C →
  Σ[ Σ′ ∈ Store ] Σ[ Ψ′ ∈ SealCtx ] Σ[ wfΣ′ ∈ StoreWf 0 Ψ′ Σ′ ]
  Σ[ M′ ∈ Term ]
    (Σˡ w ∣ (V ⦂∀ B [ T ]) —→ Σ′ ∣ M′) ×
    (0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ M′ ⦂ C)
tyapp-value-stepᵢ {T = T} {w = w} hT vV V⊢ app⊢
    with canonical-∀ vV V⊢
tyapp-value-stepᵢ {T = T} {w = w} hT vV V⊢ app⊢
    | av-Λ refl
    with preservation-step (wfΣˡ w) app⊢ β-Λ
tyapp-value-stepᵢ {T = T} {w = w} hT vV V⊢ app⊢
    | av-Λ refl | Ψ′ , eq , step⊢
    rewrite eq =
  _ , _ , storeWf-fresh-extᴿ hT (wfΣˡ w) , _ ,
  β-Λ , step⊢
tyapp-value-stepᵢ {w = w} hT vV V⊢ app⊢
    | av-up-∀ vW refl
    with preservation-step (wfΣˡ w) app⊢ (id-step (β-up-∀ vW))
tyapp-value-stepᵢ {w = w} hT vV V⊢ app⊢
    | av-up-∀ vW refl | Ψ′ , eq , step⊢
    rewrite eq =
  _ , _ , wfΣˡ w , _ ,
  id-step (β-up-∀ vW) , step⊢
tyapp-value-stepᵢ {T = T} {w = w} hT vV V⊢ app⊢
    | av-down-∀ vW refl
    with preservation-step (wfΣˡ w) app⊢ (β-down-∀ vW)
tyapp-value-stepᵢ {T = T} {w = w} hT vV V⊢ app⊢
    | av-down-∀ vW refl | Ψ′ , eq , step⊢
    rewrite eq =
  _ , _ , storeWf-fresh-extᴿ hT (wfΣˡ w) , _ ,
  β-down-∀ vW , step⊢
tyapp-value-stepᵢ {T = T} {w = w} hT vV V⊢ app⊢
    | av-down-ν vW refl
    with preservation-step (wfΣˡ w) app⊢ (β-down-ν vW)
tyapp-value-stepᵢ {T = T} {w = w} hT vV V⊢ app⊢
    | av-down-ν vW refl | Ψ′ , eq , step⊢
    rewrite eq =
  _ , _ , storeWf-fresh-extᴿ hT (wfΣˡ w) , _ ,
  β-down-ν vW , step⊢

ν-fresh-current-ℰbodyᵢ-≼0 :
  ∀ {Ξ A B T w V W} {ρ : RelSub Ξ}
    {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  (hTˡ : WfTy 0 (Ψˡ w) (leftᵢ ρ w T)) →
  Value V →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ leftᵢ ρ w (`∀ A) →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂ leftᵢ ρ w (A [ T ]ᵗ) →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w B →
  ℰbody ρ pT (suc zero) ≼ w
    (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ])
    W
ν-fresh-current-ℰbodyᵢ-≼0 {A = A} {T = T} {w = w} {V = V}
    {ρ = ρ} hTˡ vV V⊢ app⊢ W⊢
    with tyapp-value-stepᵢ
      {B = left∀ᵢ ρ w A}
      {T = leftᵢ ρ w T}
      {C = leftᵢ ρ w (A [ T ]ᵗ)}
      {w = w}
      {V = V}
      hTˡ vV V⊢ app⊢
ν-fresh-current-ℰbodyᵢ-≼0 {w = w} hTˡ vV V⊢ app⊢ W⊢
    | Σ′ , Ψ′ , wfΣ′ , M′ , step , M′⊢ =
  inj₁ (Σ′ , Ψ′ , wfΣ′ , M′ , step , (M′⊢ , W⊢) , lift tt)

left-result-value-ℰbodyᵢ-≽ :
  ∀ {Ξ A B k w M W} {ρ : RelSub Ξ} {p : Ξ ⊢ A ⊑ᵢ B} →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ M ⦂ leftᵢ ρ w A →
  Value W →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w B →
  Resultᵢ (Σˡ w) M (leftᵢ ρ w A) →
  (∀ {Σˡ′ Ψˡ′ Wˡ} {wfΣˡ′ : StoreWf 0 Ψˡ′ Σˡ′} →
    Value Wˡ →
    0 ∣ Ψˡ′ ∣ Σˡ′ ∣ [] ⊢ Wˡ ⦂
      leftᵢ ρ (mkWorldˡ w Σˡ′ wfΣˡ′) A →
    𝒱 ρ p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ W) →
  ℰbody ρ p (suc k) ≽ w M W
left-result-value-ℰbodyᵢ-≽ M⊢ vW W⊢
    (result-value wfΣˡ′ M↠Wˡ vWˡ Wˡ⊢) value-rel =
  inj₂ (inj₂ (vW , _ , _ , wfΣˡ′ , _ , M↠Wˡ , value-rel vWˡ Wˡ⊢))
left-result-value-ℰbodyᵢ-≽ {w = w} M⊢ vW W⊢
    (result-blame {Σ′ = Σˡ′} {ℓ = ℓ} M↠blame) value-rel
    with preservation-↠ (wfΣˡ w) M⊢ M↠blame
left-result-value-ℰbodyᵢ-≽ M⊢ vW W⊢
    (result-blame {Σ′ = Σˡ′} {ℓ = ℓ} M↠blame) value-rel
    | Ψˡ′ , wfΣˡ′ , blame⊢ =
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , M↠blame))

right-value-ℰbodyᵢ-≽-rest :
  ∀ {Ξ A B k w M W} {ρ : RelSub Ξ} {p : Ξ ⊢ A ⊑ᵢ B} →
  Value W →
  ℰbody ρ p (suc k) ≽ w M W →
  (Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ]
    Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ]
    Σ[ ℓ ∈ Label ]
    (Σˡ w ∣ M —↠ Σˡ′ ∣ blame ℓ))
  ⊎
  (Value W × Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ]
    Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ] Σ[ Wˡ ∈ Term ]
    (Σˡ w ∣ M —↠ Σˡ′ ∣ Wˡ) ×
    𝒱 ρ p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ W)
right-value-ℰbodyᵢ-≽-rest vW
    (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , W′ , W→W′ , rel)) =
  ⊥-elim (value-no-step vW W→W′)
right-value-ℰbodyᵢ-≽-rest vW (inj₂ rest) = rest

current-tyapp-value-ℰbodyᵢ-≽0 :
  ∀ {Ξ A B T w V W} {ρ : RelSub Ξ}
    {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  (hTˡ : WfTy 0 (Ψˡ w) (leftᵢ ρ w T)) →
  Value V →
  Value W →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂ leftᵢ ρ w (A [ T ]ᵗ) →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w B →
  ℰbody ρ pT (suc zero) ≽ w
    (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ])
    W
current-tyapp-value-ℰbodyᵢ-≽0 {A = A} {B = B} {T = T}
    {w = w} {V = V} {W = W} {ρ = ρ} {pT = pT}
    hTˡ vV vW app⊢ W⊢
  =
  left-result-value-ℰbodyᵢ-≽
    {A = A [ T ]ᵗ} {B = B} {k = zero} {w = w}
    {M = V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]} {W = W}
    {ρ = ρ} {p = pT}
    app⊢ vW W⊢
    (tyapp-value-resultᵢ
      {B = left∀ᵢ ρ w A}
      {T = leftᵢ ρ w T}
      {C = leftᵢ ρ w (A [ T ]ᵗ)}
      {w = w}
      {V = V}
      hTˡ vV app⊢)
    (λ vWˡ Wˡ⊢ → lift (vWˡ , vW , (Wˡ⊢ , W⊢)))

record SemanticRelAtᵢ {Ξ : ICtx} {A B : Ty}
    (ρ : RelSub Ξ)
    (p : Ξ ⊢ A ⊑ᵢ B)
    (w : World)
    (R : Rel) : Set₁ where
  field
    soundᵢ :
      ∀ {w′ k dir V W} →
      w′ ⪰ w →
      R k dir V W →
      𝒱 ρ p k dir w′ V W
    completeᵢ :
      ∀ {w′ k dir V W} →
      w′ ⪰ w →
      𝒱 ρ p k dir w′ V W →
      R k dir V W
    semantic-downᵢ : DownClosed R
open SemanticRelAtᵢ public

record SemanticRelKitᵢ {Ξ : ICtx} {A B : Ty}
    (ρ : RelSub Ξ)
    (p : Ξ ⊢ A ⊑ᵢ B)
    (w : World) : Set₁ where
  constructor semanticRelKitᵢ
  field
    relᵢ : Rel
    semanticᵢ : SemanticRelAtᵢ ρ p w relᵢ
open SemanticRelKitᵢ public

postulate
  semanticRelAtᵢ :
    ∀ {Ξ : ICtx} {A B : Ty} →
    (ρ : RelSub Ξ) →
    (p : Ξ ⊢ A ⊑ᵢ B) →
    (w : World) →
    SemanticRelKitᵢ ρ p w

  ν-fresh-current-ℰbodyᵢ-rest-≼ :
    ∀ {Ξ A B T k w V W} {ρ : RelSub Ξ}
      {pν : (ν-bound ∷ Ξ) ⊢ A ⊑ᵢ ⇑ᵗ B}
      {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B}
      {R : Rel}
      (inst : νClosedInstᵢ pν pT)
      (sem : SemanticRelAtᵢ ρ (⊑ᵢ-refl {Γ = Ξ} {A = T}) w R)
      (hTˡ : WfTy 0 (Ψˡ w) (leftᵢ ρ w T))
      (hTʳ : WfTy 0 (Ψʳ w) (rightᵢ ρ w T)) →
    Value V →
    Value W →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ leftᵢ ρ w (`∀ A) →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂ leftᵢ ρ w (A [ T ]ᵗ) →
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w B →
    ℰbody (extendνρ ρ
           (ηentry (length (Σˡ w)) (length (Σʳ w))
             R (semantic-downᵢ sem)))
      pν (suc k) ≼
      (extendWorldν w R (semantic-downᵢ sem)
        (leftᵢ ρ w T) (rightᵢ ρ w T) hTˡ hTʳ)
      (V ⦂∀ left∀ᵢ ρ w A [ ｀ length (Σˡ w) ])
      W →
    ℰbody ρ pT (suc (suc k)) ≼ w
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ])
      W

  ν-fresh-current-ℰbodyᵢ-rest-≽ :
    ∀ {Ξ A B T k w V W} {ρ : RelSub Ξ}
      {pν : (ν-bound ∷ Ξ) ⊢ A ⊑ᵢ ⇑ᵗ B}
      {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B}
      {R : Rel}
      (inst : νClosedInstᵢ pν pT)
      (sem : SemanticRelAtᵢ ρ (⊑ᵢ-refl {Γ = Ξ} {A = T}) w R)
      (hTˡ : WfTy 0 (Ψˡ w) (leftᵢ ρ w T))
      (hTʳ : WfTy 0 (Ψʳ w) (rightᵢ ρ w T)) →
    Value V →
    Value W →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ leftᵢ ρ w (`∀ A) →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂ leftᵢ ρ w (A [ T ]ᵗ) →
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w B →
    ℰbody (extendνρ ρ
           (ηentry (length (Σˡ w)) (length (Σʳ w))
             R (semantic-downᵢ sem)))
      pν (suc k) ≽
      (extendWorldν w R (semantic-downᵢ sem)
        (leftᵢ ρ w T) (rightᵢ ρ w T) hTˡ hTʳ)
      (V ⦂∀ left∀ᵢ ρ w A [ ｀ length (Σˡ w) ])
      W →
    ℰbody ρ pT (suc (suc k)) ≽ w
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ])
      W

ν-fresh-current-ℰbodyᵢ-rest :
    ∀ {Ξ A B T k dir w V W} {ρ : RelSub Ξ}
      {pν : (ν-bound ∷ Ξ) ⊢ A ⊑ᵢ ⇑ᵗ B}
      {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B}
      {R : Rel}
      (inst : νClosedInstᵢ pν pT)
      (sem : SemanticRelAtᵢ ρ (⊑ᵢ-refl {Γ = Ξ} {A = T}) w R)
      (hTˡ : WfTy 0 (Ψˡ w) (leftᵢ ρ w T))
      (hTʳ : WfTy 0 (Ψʳ w) (rightᵢ ρ w T)) →
    Value V →
    Value W →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ leftᵢ ρ w (`∀ A) →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂ leftᵢ ρ w (A [ T ]ᵗ) →
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w B →
    ℰbody (extendνρ ρ
           (ηentry (length (Σˡ w)) (length (Σʳ w))
             R (semantic-downᵢ sem)))
      pν k dir
      (extendWorldν w R (semantic-downᵢ sem)
        (leftᵢ ρ w T) (rightᵢ ρ w T) hTˡ hTʳ)
      (V ⦂∀ left∀ᵢ ρ w A [ ｀ length (Σˡ w) ])
      W →
    ℰbody ρ pT (suc k) dir w
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ])
      W
ν-fresh-current-ℰbodyᵢ-rest {A = A} {B = B} {T = T} {k = zero}
    {dir = ≼} {w = w} {V = V} {W = W} {ρ = ρ} {pT = pT}
    inst sem hTˡ hTʳ vV vW V⊢ app⊢ W⊢ fresh =
  ν-fresh-current-ℰbodyᵢ-≼0
    {A = A} {B = B} {T = T} {w = w} {V = V} {W = W}
    {ρ = ρ} {pT = pT}
    hTˡ vV V⊢ app⊢ W⊢
ν-fresh-current-ℰbodyᵢ-rest {A = A} {B = B} {T = T} {k = zero}
    {dir = ≽} {w = w} {V = V} {W = W} {ρ = ρ} {pT = pT}
    inst sem hTˡ hTʳ vV vW V⊢ app⊢ W⊢ fresh =
  current-tyapp-value-ℰbodyᵢ-≽0
    {A = A} {B = B} {T = T} {w = w} {V = V} {W = W}
    {ρ = ρ} {pT = pT}
    hTˡ vV vW app⊢ W⊢
ν-fresh-current-ℰbodyᵢ-rest {A = A} {B = B} {T = T} {k = suc k}
    {dir = ≼} {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν}
    {pT = pT} {R = R} inst sem hTˡ hTʳ vV vW V⊢ app⊢ W⊢ fresh =
  ν-fresh-current-ℰbodyᵢ-rest-≼
    {A = A} {B = B} {T = T} {k = k}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν} {pT = pT}
    {R = R}
    inst sem hTˡ hTʳ vV vW V⊢ app⊢ W⊢ fresh
ν-fresh-current-ℰbodyᵢ-rest {A = A} {B = B} {T = T} {k = suc k}
    {dir = ≽} {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν}
    {pT = pT} {R = R} inst sem hTˡ hTʳ vV vW V⊢ app⊢ W⊢ fresh =
  ν-fresh-current-ℰbodyᵢ-rest-≽
    {A = A} {B = B} {T = T} {k = k}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν} {pT = pT}
    {R = R}
    inst sem hTˡ hTʳ vV vW V⊢ app⊢ W⊢ fresh

ν-fresh-current-ℰbodyᵢ :
  ∀ {Ξ A B T k dir w V W} {ρ : RelSub Ξ}
    {pν : (ν-bound ∷ Ξ) ⊢ A ⊑ᵢ ⇑ᵗ B}
    {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B}
    {R : Rel}
    (inst : νClosedInstᵢ pν pT)
    (sem : SemanticRelAtᵢ ρ (⊑ᵢ-refl {Γ = Ξ} {A = T}) w R)
    (hTˡ : WfTy 0 (Ψˡ w) (leftᵢ ρ w T))
    (hTʳ : WfTy 0 (Ψʳ w) (rightᵢ ρ w T)) →
  Value V →
  Value W →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ leftᵢ ρ w (`∀ A) →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂ leftᵢ ρ w (A [ T ]ᵗ) →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w B →
  ℰbody (extendνρ ρ
         (ηentry (length (Σˡ w)) (length (Σʳ w))
           R (semantic-downᵢ sem)))
    pν k dir
    (extendWorldν w R (semantic-downᵢ sem)
      (leftᵢ ρ w T) (rightᵢ ρ w T) hTˡ hTʳ)
    (V ⦂∀ left∀ᵢ ρ w A [ ｀ length (Σˡ w) ])
    W →
  ℰbody ρ pT (suc k) dir w
    (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ])
    W
ν-fresh-current-ℰbodyᵢ {A = A} {B = B} {T = T} {k = zero}
    {dir = ≼} {w = w} {V = V} {W = W} {ρ = ρ} {pT = pT}
    inst sem hTˡ hTʳ vV vW V⊢ app⊢ W⊢ fresh =
  ν-fresh-current-ℰbodyᵢ-≼0
    {A = A} {B = B} {T = T} {w = w} {V = V} {W = W}
    {ρ = ρ} {pT = pT}
    hTˡ vV V⊢ app⊢ W⊢
ν-fresh-current-ℰbodyᵢ {A = A} {B = B} {T = T} {k = zero}
    {dir = ≽} {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν}
    {pT = pT} {R = R} inst sem hTˡ hTʳ vV vW V⊢ app⊢ W⊢ fresh =
  current-tyapp-value-ℰbodyᵢ-≽0
    {A = A} {B = B} {T = T} {w = w} {V = V} {W = W}
    {ρ = ρ} {pT = pT}
    hTˡ vV vW app⊢ W⊢
ν-fresh-current-ℰbodyᵢ {A = A} {B = B} {T = T} {k = suc k}
    {dir = dir} {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν}
    {pT = pT} {R = R} inst sem hTˡ hTʳ vV vW V⊢ app⊢ W⊢ fresh =
  ν-fresh-current-ℰbodyᵢ-rest
    {A = A} {B = B} {T = T} {k = suc k} {dir = dir}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν} {pT = pT}
    {R = R}
    inst sem hTˡ hTʳ vV vW V⊢ app⊢ W⊢ fresh

ν-payload-currentᵢ :
    ∀ {Ξ Δ Ψsrc A B T k dir w V W} {ρ : RelSub Ξ}
      {pν : (ν-bound ∷ Ξ) ⊢ A ⊑ᵢ ⇑ᵗ B}
      {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B} →
    νClosedInstᵢ pν pT →
    RelWf w ρ →
    InterpLRWfˡ (plain ∷ Ξ) (suc Δ) Ψsrc (Ψˡ w) (νenv ρ) →
    InterpLRWfˡ Ξ Δ Ψsrc (Ψˡ w) (νenv ρ) →
    WfTy (suc Δ) Ψsrc A →
    WfTy 0 Ψsrc T →
    Ψsrc ≤ Ψʳ w →
    𝒱 ρ (⊑ᵢ-ν A B pν) k dir w V W →
    ℰ ρ pT (suc k) dir w
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ])
      W
ν-payload-currentᵢ {Ξ = Ξ} {Δ = Δ} {Ψsrc = Ψsrc}
    {A = A} {B = B} {T = T} {k = zero} {dir = dir}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν} {pT = pT}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    (lift (vV , vW , (V⊢ , W⊢))) =
  (leftApp⊢ , W⊢) ,
  ν-fresh-current-ℰbodyᵢ
    {A = A} {B = B} {T = T} {k = zero} {dir = dir}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν} {pT = pT}
    {R = R}
    inst sem hTˡ hTʳ
    vV vW V⊢ leftApp⊢ W⊢ (lift tt)
  where
  kit : SemanticRelKitᵢ ρ (⊑ᵢ-refl {Γ = Ξ} {A = T}) w
  kit = semanticRelAtᵢ ρ (⊑ᵢ-refl {Γ = Ξ} {A = T}) w

  R : Rel
  R = relᵢ kit

  sem : SemanticRelAtᵢ ρ (⊑ᵢ-refl {Γ = Ξ} {A = T}) w R
  sem = semanticᵢ kit

  wfTΔ : WfTy Δ Ψsrc T
  wfTΔ = WfTy-weakenᵗ {Δ = 0} {Δ′ = Δ} wfT z≤n

  hTˡ : WfTy 0 (Ψˡ w) (leftᵢ ρ w T)
  hTˡ = leftᵢ-wf {Ξ = Ξ} {Δ = Δ} {Ψsrc = Ψsrc}
           {T = T} {w = w} ρ iwfT wfTΔ (leftᵗ-wf rwf)

  hTʳ : WfTy 0 (Ψʳ w) (rightᵢ ρ w T)
  hTʳ =
    subst
      (WfTy 0 (Ψʳ w))
      (sym (rightᵢ-closed-id {w = w} ρ wfT))
      (WfTy-weakenˢ wfT Ψsrc≤ʳ)

  leftApp⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂ leftᵢ ρ w (A [ T ]ᵗ)
  leftApp⊢ = tyappν-left-typedᵢ rwf iwfA iwfT wfA wfTΔ V⊢
ν-payload-currentᵢ {Ξ = Ξ} {Δ = Δ} {Ψsrc = Ψsrc}
    {A = A} {B = B} {T = T} {k = suc k} {dir = dir}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν} {pT = pT}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((vV , vW , (V⊢ , W⊢)) , payload) =
  (leftApp⊢ , W⊢) ,
  ν-fresh-current-ℰbodyᵢ {R = R} inst sem hTˡ hTʳ
    vV vW V⊢ leftApp⊢ W⊢ (proj₂ fresh)
  where
  kit : SemanticRelKitᵢ ρ (⊑ᵢ-refl {Γ = Ξ} {A = T}) w
  kit = semanticRelAtᵢ ρ (⊑ᵢ-refl {Γ = Ξ} {A = T}) w

  R : Rel
  R = relᵢ kit

  sem : SemanticRelAtᵢ ρ (⊑ᵢ-refl {Γ = Ξ} {A = T}) w R
  sem = semanticᵢ kit

  wfTΔ : WfTy Δ Ψsrc T
  wfTΔ = WfTy-weakenᵗ {Δ = 0} {Δ′ = Δ} wfT z≤n

  hTˡ : WfTy 0 (Ψˡ w) (leftᵢ ρ w T)
  hTˡ = leftᵢ-wf {Ξ = Ξ} {Δ = Δ} {Ψsrc = Ψsrc}
           {T = T} {w = w} ρ iwfT wfTΔ (leftᵗ-wf rwf)

  hTʳ : WfTy 0 (Ψʳ w) (rightᵢ ρ w T)
  hTʳ =
    subst
      (WfTy 0 (Ψʳ w))
      (sym (rightᵢ-closed-id {w = w} ρ wfT))
      (WfTy-weakenˢ wfT Ψsrc≤ʳ)

  leftApp⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂ leftᵢ ρ w (A [ T ]ᵗ)
  leftApp⊢ = tyappν-left-typedᵢ rwf iwfA iwfT wfA wfTΔ V⊢

  fresh :
    ℰ (extendνρ ρ
        (ηentry (length (Σˡ w)) (length (Σʳ w))
          R (semantic-downᵢ sem)))
      pν (suc k) dir
      (extendWorldν w R (semantic-downᵢ sem)
        (leftᵢ ρ w T) (rightᵢ ρ w T) hTˡ hTʳ)
      (V ⦂∀ left∀ᵢ ρ w A [ ｀ length (Σˡ w) ])
      W
  fresh =
    payload
      ⪰-refl
      R
      (semantic-downᵢ sem)
      (leftᵢ ρ w T)
      (rightᵢ ρ w T)
      hTˡ
      hTʳ
      (closed-inst-⊑ᵢ {w = w} ρ wfT)

tyappν-ℰᵢ :
  ∀ {Ξ Δ Ψsrc A B T n dir w L R} {ρ : RelSub Ξ}
    {pν : (ν-bound ∷ Ξ) ⊢ A ⊑ᵢ ⇑ᵗ B}
    {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  νClosedInstᵢ pν pT →
  RelWf w ρ →
  InterpLRWfˡ (plain ∷ Ξ) (suc Δ) Ψsrc (Ψˡ w) (νenv ρ) →
  InterpLRWfˡ Ξ Δ Ψsrc (Ψˡ w) (νenv ρ) →
  WfTy (suc Δ) Ψsrc A →
  WfTy 0 Ψsrc T →
  Ψsrc ≤ Ψʳ w →
  ℰ ρ (⊑ᵢ-ν A B pν) n dir w L R →
  ℰ ρ pT n dir w (L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) R
tyappν-ℰᵢ {Ξ} {Δ} {Ψsrc} {A} {B} {T} {zero} {dir}
    {w} {L} {R} {ρ} inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) , rel) =
  (tyappν-left-typedᵢ rwf iwfA iwfT wfA
     (WfTy-weakenᵗ wfT z≤n) L⊢ ,
   R⊢) ,
  lift tt
tyappν-ℰᵢ {A = A} {T = T} {n = suc k} {dir = ≼}
    {w = w} {L = L} {R = R} {ρ = ρ}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L→L′ , rel′)) =
  (L•⊢ , R⊢) ,
  inj₁
    (Σˡ′ , Ψˡ′ , wfΣˡ′ ,
      (L′ ⦂∀ left∀ᵢ ρ (mkWorldˡ w Σˡ′ wfΣˡ′) A
        [ leftᵢ ρ (mkWorldˡ w Σˡ′ wfΣˡ′) T ]) ,
      ξ-·α L→L′ ,
      tyappν-ℰᵢ
        inst
        (RelWf-⪰ grow rwf)
        (InterpLRWfˡ-weakenˢ (_⪰_.growΨˡ grow) iwfA)
        (InterpLRWfˡ-weakenˢ (_⪰_.growΨˡ grow) iwfT)
        wfA
        wfT
        Ψsrc≤ʳ
        rel′)
  where
  grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  grow = mkWorldˡ-⪰ (store-growth L→L′)

  L•⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂
      leftᵢ ρ w (A [ T ]ᵗ)
  L•⊢ = tyappν-left-typedᵢ rwf iwfA iwfT wfA
            (WfTy-weakenᵗ wfT z≤n) L⊢
tyappν-ℰᵢ {A = A} {T = T} {n = suc k} {dir = ≼}
    {w = w} {L = L} {R = R} {ρ = ρ}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , L↠blame))) =
  (tyappν-left-typedᵢ rwf iwfA iwfT wfA
     (WfTy-weakenᵗ wfT z≤n) L⊢ ,
   R⊢) ,
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , tyapp-blame-↠ L↠blame))
tyappν-ℰᵢ {Δ = Δ} {Ψsrc = Ψsrc} {A = A} {B = B} {T = T}
    {n = suc k} {dir = ≼} {w = w} {L = L} {R = R} {ρ = ρ}
    {pν = pν} {pT = pT}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) ,
      inj₂ (inj₂ (vL , Σʳ′ , Ψʳ′ , wfΣʳ′ , W , R↠W , Vrel))) =
  ℰ-pull-≼-right-↠
    {ρ = ρ}
    {p = pT}
    {k = suc k}
    {w = w}
    {Σʳ′ = Σʳ′} {Ψʳ′ = Ψʳ′} {wfΣʳ′ = wfΣʳ′}
    {Mˡ = L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]}
    {Mʳ = R}
    {Mʳ′ = W}
    (tyappν-left-typedᵢ rwf iwfA iwfT wfA
      (WfTy-weakenᵗ wfT z≤n) L⊢)
    R⊢
    R↠W
    (ν-payload-currentᵢ
      {Δ = Δ} {Ψsrc = Ψsrc} {A = A} {B = B} {T = T}
      {k = k} {dir = ≼}
      {w = mkWorldʳ w Σʳ′ wfΣʳ′} {V = L} {W = W}
      {ρ = ρ} {pν = pν} {pT = pT}
      inst
      (RelWf-⪰ grow rwf)
      iwfA
      iwfT
      wfA
      wfT
      (≤-trans Ψsrc≤ʳ (_⪰_.growΨʳ grow))
      Vrel)
  where
  grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  grow = mkWorldʳ-⪰ (multi-store-growth R↠W)
tyappν-ℰᵢ {A = A} {T = T} {n = suc k} {dir = ≽}
    {w = w} {L = L} {R = R} {ρ = ρ}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ , rel′)) =
  (L•⊢ , R⊢) ,
  inj₁
    (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ ,
      tyappν-ℰᵢ
        inst
        (RelWf-⪰ grow rwf)
        iwfA
        iwfT
        wfA
        wfT
        (≤-trans Ψsrc≤ʳ (_⪰_.growΨʳ grow))
        rel′)
  where
  grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  grow = mkWorldʳ-⪰ (store-growth R→R′)

  L•⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂
      leftᵢ ρ w (A [ T ]ᵗ)
  L•⊢ = tyappν-left-typedᵢ rwf iwfA iwfT wfA
            (WfTy-weakenᵗ wfT z≤n) L⊢
tyappν-ℰᵢ {A = A} {T = T} {n = suc k} {dir = ≽}
    {w = w} {L = L} {R = R} {ρ = ρ}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , L↠blame))) =
  (tyappν-left-typedᵢ rwf iwfA iwfT wfA
     (WfTy-weakenᵗ wfT z≤n) L⊢ ,
   R⊢) ,
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , tyapp-blame-↠ L↠blame))
tyappν-ℰᵢ {Δ = Δ} {Ψsrc = Ψsrc} {A = A} {B = B} {T = T}
    {n = suc k} {dir = ≽} {w = w} {L = L} {R = R} {ρ = ρ}
    {pν = pν} {pT = pT}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) ,
      inj₂ (inj₂ (vR , Σˡ′ , Ψˡ′ , wfΣˡ′ , W , L↠W , Vrel))) =
  ℰ-pull-≽-left-↠
    {ρ = ρ}
    {p = pT}
    {k = suc k}
    {w = w}
    {Σˡ′ = Σˡ′} {Ψˡ′ = Ψˡ′} {wfΣˡ′ = wfΣˡ′}
    {Mˡ = L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]}
    {Mˡ′ = W ⦂∀ left∀ᵢ ρ (mkWorldˡ w Σˡ′ wfΣˡ′) A
      [ leftᵢ ρ (mkWorldˡ w Σˡ′ wfΣˡ′) T ]}
    {Mʳ = R}
    (tyappν-left-typedᵢ rwf iwfA iwfT wfA
      (WfTy-weakenᵗ wfT z≤n) L⊢)
    R⊢
    (tyapp-↠ L↠W)
    (ν-payload-currentᵢ
      {Δ = Δ} {Ψsrc = Ψsrc} {A = A} {B = B} {T = T}
      {k = k} {dir = ≽}
      {w = mkWorldˡ w Σˡ′ wfΣˡ′} {V = W} {W = R}
      {ρ = ρ} {pν = pν} {pT = pT}
      inst
      (RelWf-⪰ grow rwf)
      (InterpLRWfˡ-weakenˢ (_⪰_.growΨˡ grow) iwfA)
      (InterpLRWfˡ-weakenˢ (_⪰_.growΨˡ grow) iwfT)
      wfA
      wfT
      Ψsrc≤ʳ
      Vrel)
  where
  grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  grow = mkWorldˡ-⪰ (multi-store-growth L↠W)

tyappν-ℰᵢ-suc :
  ∀ {Ξ Δ Ψsrc A B T n dir w L R} {ρ : RelSub Ξ}
    {pν : (ν-bound ∷ Ξ) ⊢ A ⊑ᵢ ⇑ᵗ B}
    {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  νClosedInstᵢ pν pT →
  RelWf w ρ →
  InterpLRWfˡ (plain ∷ Ξ) (suc Δ) Ψsrc (Ψˡ w) (νenv ρ) →
  InterpLRWfˡ Ξ Δ Ψsrc (Ψˡ w) (νenv ρ) →
  WfTy (suc Δ) Ψsrc A →
  WfTy 0 Ψsrc T →
  Ψsrc ≤ Ψʳ w →
  ℰ ρ (⊑ᵢ-ν A B pν) (suc n) dir w L R →
  ℰ ρ pT (suc n) dir w
    (L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) R
tyappν-ℰᵢ-suc inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ rel =
  tyappν-ℰᵢ inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ rel

compat-⦂∀-ν :
  ∀ (A B : Ty) {E dir M M′ T}
    (pν : (ν-bound ∷ TPEnv.Ξ E) ⊢ A ⊑ᵢ ⇑ᵗ B)
    {pT : TPEnv.Ξ E ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑ᵢ-ν A B pν) →
  WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
  (hT : WfTy 0 (TPEnv.Ψ E) T) →
  νClosedInstᵢ pν pT →
  E ∣ dir ⊨ (M ⦂∀ A [ T ]) ⊑ M′ ⦂ pT
compat-⦂∀-ν A B {E = E} {M = M} {M′ = M′} {T = T}
    pν M-rel wfA hT inst n w ρ γ rwf env =
  tyappν-ℰᵢ
    {Δ = TPEnv.Δ E} {Ψsrc = TPEnv.Ψ E}
    {A = A} {B = B} {T = T} {n = n}
    {L = closeLRˡᵐ ρ w (substˣ-term (leftˣ γ) M)}
    {R = closeLRʳᵐ ρ w (substˣ-term (rightˣ γ) M′)}
    inst
    (relWf rwf)
    (InterpLRWfˡ-plain (interpLRWfˡ rwf))
    (interpLRWfˡ rwf)
    wfA
    hT
    (Ψʳ≤ rwf)
    (M-rel n w ρ γ rwf env)
