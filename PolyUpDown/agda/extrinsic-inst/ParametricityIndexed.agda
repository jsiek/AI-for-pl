module ParametricityIndexed where

-- File Charter:
--   * First compatibility-proof probe for the indexed imprecision design.
--   * Defines the indexed open-term semantic judgment using `interp` before
--   * relational substitution, so `𝒱`/`ℰ` see the same indexed types as
--   * `LogicalRelationIndexed`.
--   * Starts with the ν type-application compatibility case, isolating the
--   * remaining operational bridge as an explicit theorem target.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
  using (ℕ; zero; suc; _<_; _≤_; z<s; s<s; z≤n)
open import Data.Nat.Properties
  using (≤-refl; <-≤-trans; ≤-trans; n≤1+n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Level using (Lift; 0ℓ; lift; lower) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Types
open import Store
  using
    ( _⊆ˢ_
    ; ⊆ˢ-refl
    ; ⊆ˢ-trans
    ; drop
    ; StoreWf
    ; Uniqueˢ
    ; lookup-unique
    ; storeWf-unique
    ; storeWf-dom<
    ; renameLookupᵗ
    ; renameStoreᵗ-ext-⟰ᵗ
    ; wkLookupˢ
    )
open import TypeCheckDec using (raiseVarFrom)
open import ImprecisionIndexed
open import Imprecision using (substᵗ-closed-id)
open import UpDown
open import Conversion
  using
    ( _∣_⊢_↑ˢ_
    ; _∣_⊢_↓ˢ_
    ; ↑ˢ-unseal
    ; ↑ˢ-⇒
    ; ↑ˢ-∀
    ; ↑ˢ-id
    ; _；↑ˢ_
    ; ↓ˢ-seal
    ; ↓ˢ-⇒
    ; ↓ˢ-∀
    ; ↓ˢ-id
    ; _；↓ˢ_
    )
open import Terms
open import TermImprecisionIndexed
open import TermProperties
  using (Substˣ; substˣ-term; singleVarEnv; []-wt; []ᵀ-wt)
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
    ; blame-·₂
    ; blame-·α
    ; β-up-↦
    ; β-down-↦
    ; β-Λ
    ; β-up-∀
    ; β-down-∀
    ; β-down-ν
    ; β-up-ν
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
open import ReductionFresh using () renaming (β to β-ƛ)
open import ProgressFresh
  using
    ( canonical-∀
    ; canonical-⇒
    ; canonical-｀
    ; canonical-★
    ; FunView
    ; fv-ƛ
    ; fv-up-↦
    ; fv-down-↦
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
    ; preservation
    ; preservation-step
    ; wkΨ-term-suc
    ; len<suc-StoreWf
    )
open import LogicalRelationIndexed

postulate
  preservation-step-storeWf :
    ∀ {Δ Ψ Σ Σ′ Γ A M M′} →
    (wfΣ : StoreWf Δ Ψ Σ) →
    (M⊢ : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A) →
    (red : Σ ∣ M —→ Σ′ ∣ M′) →
    StoreWf Δ (proj₁ (preservation-step wfΣ M⊢ red)) Σ′

------------------------------------------------------------------------
-- Interpreting indexed types inside terms and casts
------------------------------------------------------------------------

mutual
  interpUp : ICtx → Up → Up
  interpUp Ξ (tag p G) = tag (interpUp Ξ p) (interp Ξ G)
  interpUp Ξ (unseal α p) = unseal (interpSeal Ξ α) (interpUp Ξ p)
  interpUp Ξ (p ↦ q) = interpDown Ξ p ↦ interpUp Ξ q
  interpUp Ξ (∀ᵖ p) = ∀ᵖ (interpUp (plain ∷ Ξ) p)
  interpUp Ξ (ν p) = ν (interpUp (ν-bound ∷ Ξ) p)
  interpUp Ξ (id A) = id (interp Ξ A)

  interpDown : ICtx → Down → Down
  interpDown Ξ (untag G ℓ p) = untag (interp Ξ G) ℓ (interpDown Ξ p)
  interpDown Ξ (seal p α) = seal (interpDown Ξ p) (interpSeal Ξ α)
  interpDown Ξ (p ↦ q) = interpUp Ξ p ↦ interpDown Ξ q
  interpDown Ξ (∀ᵖ p) = ∀ᵖ (interpDown (plain ∷ Ξ) p)
  interpDown Ξ (ν p) = ν (interpDown (ν-bound ∷ Ξ) p)
  interpDown Ξ (id A) = id (interp Ξ A)

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
  interpUpLRˡ Ξ η (tag p G) = tag (interpUpLRˡ Ξ η p) (interpLRˡ Ξ η G)
  interpUpLRˡ Ξ η (unseal α p) = unseal α (interpUpLRˡ Ξ η p)
  interpUpLRˡ Ξ η (p ↦ q) = interpDownLRˡ Ξ η p ↦ interpUpLRˡ Ξ η q
  interpUpLRˡ Ξ η (∀ᵖ p) = ∀ᵖ (interpUpLRˡ (plain ∷ Ξ) η p)
  interpUpLRˡ Ξ η (ν p) = ν (interpUp (ν-bound ∷ Ξ) p)
  interpUpLRˡ Ξ η (id A) = id (interpLRˡ Ξ η A)

  interpDownLRˡ : ICtx → List SealRel → Down → Down
  interpDownLRˡ Ξ η (untag G ℓ p) = untag (interpLRˡ Ξ η G) ℓ (interpDownLRˡ Ξ η p)
  interpDownLRˡ Ξ η (seal p α) = seal (interpDownLRˡ Ξ η p) α
  interpDownLRˡ Ξ η (p ↦ q) = interpUpLRˡ Ξ η p ↦ interpDownLRˡ Ξ η q
  interpDownLRˡ Ξ η (∀ᵖ p) = ∀ᵖ (interpDownLRˡ (plain ∷ Ξ) η p)
  interpDownLRˡ Ξ η (ν p) = ν (interpDown (ν-bound ∷ Ξ) p)
  interpDownLRˡ Ξ η (id A) = id (interpLRˡ Ξ η A)

mutual
  interpUpLRʳ : ICtx → List SealRel → Up → Up
  interpUpLRʳ Ξ η (tag p G) = tag (interpUpLRʳ Ξ η p) (interpLRʳ Ξ η G)
  interpUpLRʳ Ξ η (unseal α p) = unseal α (interpUpLRʳ Ξ η p)
  interpUpLRʳ Ξ η (p ↦ q) = interpDownLRʳ Ξ η p ↦ interpUpLRʳ Ξ η q
  interpUpLRʳ Ξ η (∀ᵖ p) = ∀ᵖ (interpUpLRʳ (plain ∷ Ξ) η p)
  interpUpLRʳ Ξ η (ν p) = ν (interpUp (ν-bound ∷ Ξ) p)
  interpUpLRʳ Ξ η (id A) = id (interpLRʳ Ξ η A)

  interpDownLRʳ : ICtx → List SealRel → Down → Down
  interpDownLRʳ Ξ η (untag G ℓ p) = untag (interpLRʳ Ξ η G) ℓ (interpDownLRʳ Ξ η p)
  interpDownLRʳ Ξ η (seal p α) = seal (interpDownLRʳ Ξ η p) α
  interpDownLRʳ Ξ η (p ↦ q) = interpUpLRʳ Ξ η p ↦ interpDownLRʳ Ξ η q
  interpDownLRʳ Ξ η (∀ᵖ p) = ∀ᵖ (interpDownLRʳ (plain ∷ Ξ) η p)
  interpDownLRʳ Ξ η (ν p) = ν (interpDown (ν-bound ∷ Ξ) p)
  interpDownLRʳ Ξ η (id A) = id (interpLRʳ Ξ η A)

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
          (closed-reflᵢ hT)

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

extendPlainρ-left-openᵢ :
  ∀ {Ξ A Tˡ Tʳ Rrel} (ρ : RelSub Ξ) (w : World)
    {wfTˡ wfTʳ pT} {downR : DownClosed Rrel} →
  leftᵢ (extendPlainρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR) w A ≡
  (left∀ᵢ ρ w A) [ Tˡ ]ᵗ
extendPlainρ-left-openᵢ {Ξ = Ξ} {A = A} {Tˡ = Tˡ} ρ w =
  trans
    (substᵗ-cong env (interpLRˡ (plain ∷ Ξ) (νenv ρ) A))
    (sym
      (substᵗ-substᵗ
        (singleTyEnv Tˡ)
        (extsᵗ (leftᵗ ρ))
        (interpLRˡ (plain ∷ Ξ) (νenv ρ) A)))
  where
  env : (X : TyVar) →
    leftᵗ (extendPlainρ ρ Tˡ _ _ _ _ _ _) X ≡
    substᵗ (singleTyEnv Tˡ) (extsᵗ (leftᵗ ρ) X)
  env zero = refl
  env (suc X) = sym (open-renᵗ-suc (leftᵗ ρ X) Tˡ)

extendPlainρ-right-openᵢ :
  ∀ {Ξ A Tˡ Tʳ Rrel} (ρ : RelSub Ξ) (w : World)
    {wfTˡ wfTʳ pT} {downR : DownClosed Rrel} →
  rightᵢ (extendPlainρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR) w A ≡
  (right∀ᵢ ρ w A) [ Tʳ ]ᵗ
extendPlainρ-right-openᵢ {Ξ = Ξ} {A = A} {Tʳ = Tʳ} ρ w =
  trans
    (substᵗ-cong env (interpLRʳ (plain ∷ Ξ) (νenv ρ) A))
    (sym
      (substᵗ-substᵗ
        (singleTyEnv Tʳ)
        (extsᵗ (rightᵗ ρ))
        (interpLRʳ (plain ∷ Ξ) (νenv ρ) A)))
  where
  env : (X : TyVar) →
    rightᵗ (extendPlainρ ρ _ Tʳ _ _ _ _ _) X ≡
    substᵗ (singleTyEnv Tʳ) (extsᵗ (rightᵗ ρ) X)
  env zero = refl
  env (suc X) = sym (open-renᵗ-suc (rightᵗ ρ X) Tʳ)

interpLRVarˡ-ν-open-at :
  ∀ n Ξ η e X →
  interpLRVarˡ (plains n (ν-bound ∷ Ξ)) (e ∷ η) X ≡
  substᵗ (substVarFrom n (｀ (αˡ e)))
    (interpLRVarˡ (plains n (plain ∷ Ξ)) η X)
interpLRVarˡ-ν-open-at zero Ξ η e zero = refl
interpLRVarˡ-ν-open-at zero Ξ η e (suc X) =
  sym (open-renᵗ-suc (interpLRVarˡ Ξ η X) (｀ (αˡ e)))
interpLRVarˡ-ν-open-at (suc n) Ξ η e zero = refl
interpLRVarˡ-ν-open-at (suc n) Ξ η e (suc X) =
  trans
    (cong ⇑ᵗ (interpLRVarˡ-ν-open-at n Ξ η e X))
    (sym
      (substVarFrom-⇑ᵗ n (｀ (αˡ e))
        (interpLRVarˡ (plains n (plain ∷ Ξ)) η X)))

interpLRˡ-ν-open-at :
  ∀ n Ξ η e A →
  interpLRˡ (plains n (ν-bound ∷ Ξ)) (e ∷ η) A ≡
  substᵗ (substVarFrom n (｀ (αˡ e)))
    (interpLRˡ (plains n (plain ∷ Ξ)) η A)
interpLRˡ-ν-open-at n Ξ η e (＇ X) =
  interpLRVarˡ-ν-open-at n Ξ η e X
interpLRˡ-ν-open-at n Ξ η e (｀ α) = refl
interpLRˡ-ν-open-at n Ξ η e (‵ ι) = refl
interpLRˡ-ν-open-at n Ξ η e ★ = refl
interpLRˡ-ν-open-at n Ξ η e (A ⇒ B) =
  cong₂ _⇒_
    (interpLRˡ-ν-open-at n Ξ η e A)
    (interpLRˡ-ν-open-at n Ξ η e B)
interpLRˡ-ν-open-at n Ξ η e (`∀ A) =
  cong `∀ (interpLRˡ-ν-open-at (suc n) Ξ η e A)

interpLRˡ-ν-open :
  ∀ Ξ η e A →
  interpLRˡ (ν-bound ∷ Ξ) (e ∷ η) A ≡
  (interpLRˡ (plain ∷ Ξ) η A) [ ｀ (αˡ e) ]ᵗ
interpLRˡ-ν-open Ξ η e A = interpLRˡ-ν-open-at zero Ξ η e A

interpLRVarʳ-ν-open-at :
  ∀ n Ξ η e X →
  interpLRVarʳ (plains n (ν-bound ∷ Ξ)) (e ∷ η) X ≡
  substᵗ (substVarFrom n (｀ (αʳ e)))
    (interpLRVarʳ (plains n (plain ∷ Ξ)) η X)
interpLRVarʳ-ν-open-at zero Ξ η e zero = refl
interpLRVarʳ-ν-open-at zero Ξ η e (suc X) =
  sym (open-renᵗ-suc (interpLRVarʳ Ξ η X) (｀ (αʳ e)))
interpLRVarʳ-ν-open-at (suc n) Ξ η e zero = refl
interpLRVarʳ-ν-open-at (suc n) Ξ η e (suc X) =
  trans
    (cong ⇑ᵗ (interpLRVarʳ-ν-open-at n Ξ η e X))
    (sym
      (substVarFrom-⇑ᵗ n (｀ (αʳ e))
        (interpLRVarʳ (plains n (plain ∷ Ξ)) η X)))

interpLRʳ-ν-open-at :
  ∀ n Ξ η e A →
  interpLRʳ (plains n (ν-bound ∷ Ξ)) (e ∷ η) A ≡
  substᵗ (substVarFrom n (｀ (αʳ e)))
    (interpLRʳ (plains n (plain ∷ Ξ)) η A)
interpLRʳ-ν-open-at n Ξ η e (＇ X) =
  interpLRVarʳ-ν-open-at n Ξ η e X
interpLRʳ-ν-open-at n Ξ η e (｀ α) = refl
interpLRʳ-ν-open-at n Ξ η e (‵ ι) = refl
interpLRʳ-ν-open-at n Ξ η e ★ = refl
interpLRʳ-ν-open-at n Ξ η e (A ⇒ B) =
  cong₂ _⇒_
    (interpLRʳ-ν-open-at n Ξ η e A)
    (interpLRʳ-ν-open-at n Ξ η e B)
interpLRʳ-ν-open-at n Ξ η e (`∀ A) =
  cong `∀ (interpLRʳ-ν-open-at (suc n) Ξ η e A)

interpLRʳ-ν-open :
  ∀ Ξ η e A →
  interpLRʳ (ν-bound ∷ Ξ) (e ∷ η) A ≡
  (interpLRʳ (plain ∷ Ξ) η A) [ ｀ (αʳ e) ]ᵗ
interpLRʳ-ν-open Ξ η e A = interpLRʳ-ν-open-at zero Ξ η e A

extendνρ-left-openᵢ :
  ∀ {Ξ A αˡ αʳ Rrel} (ρ : RelSub Ξ) (w : World)
    {downR : DownClosed Rrel} →
  leftᵢ (extendνρ ρ (ηentry αˡ αʳ Rrel downR)) w A ≡
  (left∀ᵢ ρ w A) [ ｀ αˡ ]ᵗ
extendνρ-left-openᵢ {Ξ = Ξ} {A = A} {αˡ = αˡ} {αʳ = αʳ}
    {Rrel = Rrel} ρ w {downR = downR} =
  trans
    (cong (substᵗ (leftᵗ ρ))
      (interpLRˡ-ν-open Ξ (νenv ρ)
        (ηentry αˡ αʳ Rrel downR) A))
    (substᵗ-open
      (leftᵗ ρ)
      (interpLRˡ (plain ∷ Ξ) (νenv ρ) A)
      (｀ αˡ))

extendνρ-right-openᵢ :
  ∀ {Ξ A αˡ αʳ Rrel} (ρ : RelSub Ξ) (w : World)
    {downR : DownClosed Rrel} →
  rightᵢ (extendνρ ρ (ηentry αˡ αʳ Rrel downR)) w A ≡
  (right∀ᵢ ρ w A) [ ｀ αʳ ]ᵗ
extendνρ-right-openᵢ {Ξ = Ξ} {A = A} {αˡ = αˡ} {αʳ = αʳ}
    {Rrel = Rrel} ρ w {downR = downR} =
  trans
    (cong (substᵗ (rightᵗ ρ))
      (interpLRʳ-ν-open Ξ (νenv ρ)
        (ηentry αˡ αʳ Rrel downR) A))
    (substᵗ-open
      (rightᵗ ρ)
      (interpLRʳ (plain ∷ Ξ) (νenv ρ) A)
      (｀ αʳ))

interpLRʳ-ν-shift-at :
  ∀ n Ξ η e A →
  interpLRʳ (plains n (ν-bound ∷ Ξ)) (e ∷ η)
    (renameᵗ (raiseVarFrom n) A) ≡
  interpLRʳ (plains n Ξ) η A
interpLRʳ-ν-shift-at zero Ξ η e (＇ X) = refl
interpLRʳ-ν-shift-at zero Ξ η e (｀ α) = refl
interpLRʳ-ν-shift-at zero Ξ η e (‵ ι) = refl
interpLRʳ-ν-shift-at zero Ξ η e ★ = refl
interpLRʳ-ν-shift-at zero Ξ η e (A ⇒ B) =
  cong₂ _⇒_
    (interpLRʳ-ν-shift-at zero Ξ η e A)
    (interpLRʳ-ν-shift-at zero Ξ η e B)
interpLRʳ-ν-shift-at zero Ξ η e (`∀ A) =
  cong `∀
    (trans
      (cong (interpLRʳ (plain ∷ ν-bound ∷ Ξ) (e ∷ η))
        (renameᵗ-cong (raise-ext zero) A))
      (interpLRʳ-ν-shift-at (suc zero) Ξ η e A))
interpLRʳ-ν-shift-at (suc n) Ξ η e (＇ zero) = refl
interpLRʳ-ν-shift-at (suc n) Ξ η e (＇ (suc X)) =
  cong ⇑ᵗ (interpLRʳ-ν-shift-at n Ξ η e (＇ X))
interpLRʳ-ν-shift-at (suc n) Ξ η e (｀ α) = refl
interpLRʳ-ν-shift-at (suc n) Ξ η e (‵ ι) = refl
interpLRʳ-ν-shift-at (suc n) Ξ η e ★ = refl
interpLRʳ-ν-shift-at (suc n) Ξ η e (A ⇒ B) =
  cong₂ _⇒_
    (interpLRʳ-ν-shift-at (suc n) Ξ η e A)
    (interpLRʳ-ν-shift-at (suc n) Ξ η e B)
interpLRʳ-ν-shift-at (suc n) Ξ η e (`∀ A) =
  cong `∀
    (trans
      (cong (interpLRʳ (plains (suc (suc n)) (ν-bound ∷ Ξ)) (e ∷ η))
        (renameᵗ-cong (raise-ext (suc n)) A))
      (interpLRʳ-ν-shift-at (suc (suc n)) Ξ η e A))

extendνρ-right-shiftᵢ :
  ∀ {Ξ A αˡ αʳ Rrel} (ρ : RelSub Ξ) (w : World)
    {downR : DownClosed Rrel} →
  rightᵢ (extendνρ ρ (ηentry αˡ αʳ Rrel downR)) w (⇑ᵗ A) ≡
  rightᵢ ρ w A
extendνρ-right-shiftᵢ {Ξ = Ξ} {A = A} {αˡ = αˡ} {αʳ = αʳ}
    {Rrel = Rrel} ρ w {downR = downR} =
  cong (substᵗ (rightᵗ ρ))
    (interpLRʳ-ν-shift-at zero Ξ (νenv ρ)
      (ηentry αˡ αʳ Rrel downR) A)

instCast-up-left-typedᵢν :
  ∀ {Ξ A Tˡ Tʳ αˡ αʳ Rrel} {ρ : RelSub Ξ}
    {pT : [] ⊢ Tˡ ⊑ᵢ Tʳ}
    {wfTˡc : WfTyClosedᵗ Tˡ} {wfTʳc : WfTyClosedᵗ Tʳ}
    {downR : DownClosed Rrel}
    {w L} →
  (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
  (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
  (hAˡ : WfTy (suc 0) (Ψˡ w) (left∀ᵢ ρ w A)) →
  Σˡ w ∋ˢ αˡ ⦂ Tˡ →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂
    leftᵢ (extendνρ ρ (ηentry αˡ αʳ Rrel downR)) w A →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    L up (instCast⊑ {A = Tˡ} {B = left∀ᵢ ρ w A} {α = αˡ})
    ⦂ leftᵢ
        (extendPlainρ ρ Tˡ Tʳ
          wfTˡc wfTʳc pT Rrel downR)
        w A
instCast-up-left-typedᵢν
    {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
    {w = w} hTˡ hTʳ hAˡ αˡ∈ L⊢ =
  cong-⊢⦂ refl refl refl
    (sym (extendPlainρ-left-openᵢ {A = A} {Tˡ = Tˡ} ρ w))
    (⊢up (every (Ψˡ w)) (length-every (Ψˡ w))
      (cong-⊢⦂ refl refl refl
        (extendνρ-left-openᵢ {A = A} {αˡ = αˡ} {αʳ = αʳ}
          {Rrel = Rrel} ρ w)
        L⊢)
      (instCast⊑-wt hTˡ hAˡ αˡ∈
        (every-member-conv αˡ (storeWf-dom< (wfΣˡ w) αˡ∈))))

instCast-up-right-typedᵢν :
  ∀ {Ξ B Tˡ Tʳ αˡ αʳ Rrel} {ρ : RelSub Ξ}
    {pT : [] ⊢ Tˡ ⊑ᵢ Tʳ}
    {wfTˡc : WfTyClosedᵗ Tˡ} {wfTʳc : WfTyClosedᵗ Tʳ}
    {downR : DownClosed Rrel}
    {w R} →
  (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
  (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
  (hBʳ : WfTy (suc 0) (Ψʳ w) (right∀ᵢ ρ w B)) →
  Σʳ w ∋ˢ αʳ ⦂ Tʳ →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ R ⦂
    rightᵢ (extendνρ ρ (ηentry αˡ αʳ Rrel downR)) w B →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
    R up (instCast⊑ {A = Tʳ} {B = right∀ᵢ ρ w B} {α = αʳ})
    ⦂ rightᵢ
        (extendPlainρ ρ Tˡ Tʳ
          wfTˡc wfTʳc pT Rrel downR)
        w B
instCast-up-right-typedᵢν
    {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
    {w = w} hTˡ hTʳ hBʳ αʳ∈ R⊢ =
  cong-⊢⦂ refl refl refl
    (sym (extendPlainρ-right-openᵢ {A = B} {Tʳ = Tʳ} ρ w))
    (⊢up (every (Ψʳ w)) (length-every (Ψʳ w))
      (cong-⊢⦂ refl refl refl
        (extendνρ-right-openᵢ {A = B} {αˡ = αˡ} {αʳ = αʳ}
          {Rrel = Rrel} ρ w)
        R⊢)
      (instCast⊑-wt hTʳ hBʳ αʳ∈
        (every-member-conv αʳ (storeWf-dom< (wfΣʳ w) αʳ∈))))

instCast-down-left-typedᵢν :
  ∀ {Ξ A Tˡ Tʳ αˡ αʳ Rrel} {ρ : RelSub Ξ}
    {pT : [] ⊢ Tˡ ⊑ᵢ Tʳ}
    {wfTˡc : WfTyClosedᵗ Tˡ} {wfTʳc : WfTyClosedᵗ Tʳ}
    {downR : DownClosed Rrel}
    {w L} →
  (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
  (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
  (hAˡ : WfTy (suc 0) (Ψˡ w) (left∀ᵢ ρ w A)) →
  Σˡ w ∋ˢ αˡ ⦂ Tˡ →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ L ⦂
    leftᵢ
      (extendPlainρ ρ Tˡ Tʳ
        wfTˡc wfTʳc pT Rrel downR)
      w A →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
    L down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w A} {α = αˡ})
    ⦂ leftᵢ (extendνρ ρ (ηentry αˡ αʳ Rrel downR)) w A
instCast-down-left-typedᵢν
    {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
    {w = w} hTˡ hTʳ hAˡ αˡ∈ L⊢ =
  cong-⊢⦂ refl refl refl
    (sym
      (extendνρ-left-openᵢ {A = A} {αˡ = αˡ} {αʳ = αʳ}
        {Rrel = Rrel} ρ w))
    (⊢down (every (Ψˡ w)) (length-every (Ψˡ w))
      (cong-⊢⦂ refl refl refl
        (extendPlainρ-left-openᵢ {A = A} {Tˡ = Tˡ} ρ w)
        L⊢)
      (instCast⊒-wt hTˡ hAˡ αˡ∈
        (every-member-conv αˡ (storeWf-dom< (wfΣˡ w) αˡ∈))))

instCast-down-right-typedᵢν :
  ∀ {Ξ B Tˡ Tʳ αˡ αʳ Rrel} {ρ : RelSub Ξ}
    {pT : [] ⊢ Tˡ ⊑ᵢ Tʳ}
    {wfTˡc : WfTyClosedᵗ Tˡ} {wfTʳc : WfTyClosedᵗ Tʳ}
    {downR : DownClosed Rrel}
    {w R} →
  (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
  (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
  (hBʳ : WfTy (suc 0) (Ψʳ w) (right∀ᵢ ρ w B)) →
  Σʳ w ∋ˢ αʳ ⦂ Tʳ →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ R ⦂
    rightᵢ
      (extendPlainρ ρ Tˡ Tʳ
        wfTˡc wfTʳc pT Rrel downR)
      w B →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢
    R down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w B} {α = αʳ})
    ⦂ rightᵢ (extendνρ ρ (ηentry αˡ αʳ Rrel downR)) w B
instCast-down-right-typedᵢν
    {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
    {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
    {w = w} hTˡ hTʳ hBʳ αʳ∈ R⊢ =
  cong-⊢⦂ refl refl refl
    (sym
      (extendνρ-right-openᵢ {A = B} {αˡ = αˡ} {αʳ = αʳ}
        {Rrel = Rrel} ρ w))
    (⊢down (every (Ψʳ w)) (length-every (Ψʳ w))
      (cong-⊢⦂ refl refl refl
        (extendPlainρ-right-openᵢ {A = B} {Tʳ = Tʳ} ρ w)
        R⊢)
      (instCast⊒-wt hTʳ hBʳ αʳ∈
        (every-member-conv αʳ (storeWf-dom< (wfΣʳ w) αʳ∈))))

InstCastBridgeℰ⊑ᵢ : Set₁
InstCastBridgeℰ⊑ᵢ =
  ∀ {Ξ A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub Ξ}
    {p : plain ∷ Ξ ⊢ A ⊑ᵢ B}
    {pν : ν-bound ∷ Ξ ⊢ A ⊑ᵢ B}
    {pT : [] ⊢ Tˡ ⊑ᵢ Tʳ}
    {wfTˡ : WfTyClosedᵗ Tˡ} {wfTʳ : WfTyClosedᵗ Tʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (left∀ᵢ ρ w A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (right∀ᵢ ρ w B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (L R : Term) →
  ℰ (extendνρ ρ (ηentry αˡ αʳ Rrel downR))
    pν n dir w L R →
  ℰ (extendPlainρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p n dir w
    (L up (instCast⊑ {A = Tˡ} {B = left∀ᵢ ρ w A} {α = αˡ}))
    (R up (instCast⊑ {A = Tʳ} {B = right∀ᵢ ρ w B} {α = αʳ}))

InstCastBridgeℰ⊒ᵢ : Set₁
InstCastBridgeℰ⊒ᵢ =
  ∀ {Ξ A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub Ξ}
    {p : plain ∷ Ξ ⊢ A ⊑ᵢ B}
    {pν : ν-bound ∷ Ξ ⊢ A ⊑ᵢ B}
    {pT : [] ⊢ Tˡ ⊑ᵢ Tʳ}
    {wfTˡ : WfTyClosedᵗ Tˡ} {wfTʳ : WfTyClosedᵗ Tʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (left∀ᵢ ρ w A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (right∀ᵢ ρ w B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (L R : Term) →
  ℰ (extendPlainρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p n dir w L R →
  ℰ (extendνρ ρ (ηentry αˡ αʳ Rrel downR))
    pν n dir w
    (L down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w A} {α = αˡ}))
    (R down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w B} {α = αʳ}))

InstCastBridge𝒱⇒ℰ⊑ᵢ : Set₁
InstCastBridge𝒱⇒ℰ⊑ᵢ =
  ∀ {Ξ A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub Ξ}
    {p : plain ∷ Ξ ⊢ A ⊑ᵢ B}
    {pν : ν-bound ∷ Ξ ⊢ A ⊑ᵢ B}
    {pT : [] ⊢ Tˡ ⊑ᵢ Tʳ}
    {wfTˡ : WfTyClosedᵗ Tˡ} {wfTʳ : WfTyClosedᵗ Tʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (left∀ᵢ ρ w A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (right∀ᵢ ρ w B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (V W : Term) →
  𝒱 (extendνρ ρ (ηentry αˡ αʳ Rrel downR))
    pν n dir w V W →
  ℰ (extendPlainρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p (suc n) dir w
    (V up (instCast⊑ {A = Tˡ} {B = left∀ᵢ ρ w A} {α = αˡ}))
    (W up (instCast⊑ {A = Tʳ} {B = right∀ᵢ ρ w B} {α = αʳ}))

InstCastBridge𝒱⇒ℰ⊒ᵢ : Set₁
InstCastBridge𝒱⇒ℰ⊒ᵢ =
  ∀ {Ξ A B n dir w Tˡ Tʳ αˡ αʳ} {ρ : RelSub Ξ}
    {p : plain ∷ Ξ ⊢ A ⊑ᵢ B}
    {pν : ν-bound ∷ Ξ ⊢ A ⊑ᵢ B}
    {pT : [] ⊢ Tˡ ⊑ᵢ Tʳ}
    {wfTˡ : WfTyClosedᵗ Tˡ} {wfTʳ : WfTyClosedᵗ Tʳ} →
    (Rrel : Rel) →
    (downR : DownClosed Rrel) →
    (hTˡ : WfTy 0 (Ψˡ w) Tˡ) →
    (hTʳ : WfTy 0 (Ψʳ w) Tʳ) →
    (hAˡ : WfTy (suc 0) (Ψˡ w) (left∀ᵢ ρ w A)) →
    (hBʳ : WfTy (suc 0) (Ψʳ w) (right∀ᵢ ρ w B)) →
    (αˡ∈ : Σˡ w ∋ˢ αˡ ⦂ Tˡ) →
    (αʳ∈ : Σʳ w ∋ˢ αʳ ⦂ Tʳ) →
    (V W : Term) →
  𝒱 (extendPlainρ ρ Tˡ Tʳ wfTˡ wfTʳ pT Rrel downR)
    p n dir w V W →
  ℰ (extendνρ ρ (ηentry αˡ αʳ Rrel downR))
    pν (suc n) dir w
    (V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w A} {α = αˡ}))
    (W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w B} {α = αʳ}))

postulate
  instCast-bridge-𝒱⇒ℰ⊒ᵢ-fallback : InstCastBridge𝒱⇒ℰ⊒ᵢ

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

multi-store-growth :
  ∀ {Σ Σ′ L L′} →
  Σ ∣ L —↠ Σ′ ∣ L′ →
  Σ ⊆ˢ Σ′
multi-store-growth (L ∎) = ⊆ˢ-refl
multi-store-growth (L —→⟨ L→M ⟩ M↠N) =
  ⊆ˢ-trans (store-growth L→M) (multi-store-growth M↠N)

appR-blame-↠ :
  ∀ {Σ Σ′ V M ℓ} →
  Value V →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (V · M) —↠ Σ′ ∣ blame ℓ
appR-blame-↠ {V = V} {ℓ = ℓ} vV (_ ∎) =
  (V · blame ℓ) —→⟨ id-step (blame-·₂ vV) ⟩ blame ℓ ∎
appR-blame-↠ {V = V} vV (M —→⟨ M→M′ ⟩ M′↠blame) =
  (V · M) —→⟨ ξ-·₂ vV M→M′ ⟩ appR-blame-↠ vV M′↠blame

appR-↠ :
  ∀ {Σ Σ′ V M W} →
  Value V →
  Σ ∣ M —↠ Σ′ ∣ W →
  Σ ∣ (V · M) —↠ Σ′ ∣ (V · W)
appR-↠ {V = V} vV (M ∎) = (V · M) ∎
appR-↠ {V = V} vV (M —→⟨ M→M′ ⟩ M′↠W) =
  (V · M) —→⟨ ξ-·₂ vV M→M′ ⟩ appR-↠ vV M′↠W

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

mkWorldˡʳ-⪰ :
  ∀ {w Σˡ′ Ψˡ′ Σʳ′ Ψʳ′}
    {wfΣˡ′ : StoreWf 0 Ψˡ′ Σˡ′}
    {wfΣʳ′ : StoreWf 0 Ψʳ′ Σʳ′} →
  Σˡ w ⊆ˢ Σˡ′ →
  Σʳ w ⊆ˢ Σʳ′ →
  mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′ ⪰ w
mkWorldˡʳ-⪰ {w = w} {wfΣˡ′ = wfΣˡ′} growˡ growʳ ._⪰_.growΨˡ
  rewrite sym (StoreWf.len (wfΣˡ w)) | sym (StoreWf.len wfΣˡ′) =
  ⊆ˢ-length≤ growˡ
mkWorldˡʳ-⪰ {w = w} {wfΣʳ′ = wfΣʳ′} growˡ growʳ ._⪰_.growΨʳ
  rewrite sym (StoreWf.len (wfΣʳ w)) | sym (StoreWf.len wfΣʳ′) =
  ⊆ˢ-length≤ growʳ
mkWorldˡʳ-⪰ growˡ growʳ ._⪰_.growˡ = growˡ
mkWorldˡʳ-⪰ growˡ growʳ ._⪰_.growʳ = growʳ
mkWorldˡʳ-⪰ growˡ growʳ ._⪰_.growη = ⊆η-refl

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
    ((Mˡ⊢′ , Mʳ′⊢) ,
      inj₁
        (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ ,
         Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳ , Mʳ′↠Wʳ , rel)) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₁
    (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ ,
     Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳ ,
     multi-trans Mʳ↠Mʳ′ Mʳ′↠Wʳ , rel)
ℰ-pull-≼-right-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mʳ↠Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) ,
      inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , Mˡ↠blame))) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , Mˡ↠blame))
ℰ-pull-≼-right-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mʳ↠Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) ,
      inj₂ (inj₂
        (vMˡ , Σʳ″ , Ψʳ″ , wfΣʳ″ , Wʳ , Mʳ′↠Wʳ , rel))) =
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
    ((Mˡ′⊢ , Mʳ⊢′) ,
      inj₁
        (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , Mʳ→Mʳ′ ,
         Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡ , Mˡ′↠Wˡ , rel)) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₁
    (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , Mʳ→Mʳ′ ,
     Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡ ,
     multi-trans Mˡ↠Mˡ′ Mˡ′↠Wˡ , rel)
ℰ-pull-≽-left-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mˡ↠Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) ,
      inj₂ (inj₁ (Σˡ″ , Ψˡ″ , wfΣˡ″ , ℓ , Mˡ′↠blame))) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₂ (inj₁ (Σˡ″ , Ψˡ″ , wfΣˡ″ , ℓ ,
    multi-trans Mˡ↠Mˡ′ Mˡ′↠blame))
ℰ-pull-≽-left-↠ {k = suc k} Mˡ⊢ Mʳ⊢ Mˡ↠Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) ,
      inj₂ (inj₂
        (vMʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡ , Mˡ′↠Wˡ , rel))) =
  (Mˡ⊢ , Mʳ⊢) ,
  inj₂ (inj₂
    (vMʳ , Σˡ″ , Ψˡ″ , wfΣˡ″ , Wˡ ,
     multi-trans Mˡ↠Mˡ′ Mˡ′↠Wˡ , rel))

𝒱⇒ℰᵢ :
  ∀ {Ξ A B n dir w V W} {ρ : RelSub Ξ} {p : Ξ ⊢ A ⊑ᵢ B} →
  𝒱 ρ p n dir w V W →
  ℰ ρ p (suc n) dir w V W
𝒱⇒ℰᵢ {n = zero} {dir = ≼} {w = w}
    (lift (vV , vW , (V⊢ , W⊢))) =
  (V⊢ , W⊢) ,
  inj₂ (inj₂
    (vV , Σʳ w , Ψʳ w , wfΣʳ w , _ , (_ ∎) ,
     lift (vV , vW , (V⊢ , W⊢))))
𝒱⇒ℰᵢ {n = zero} {dir = ≽} {w = w}
    (lift (vV , vW , (V⊢ , W⊢))) =
  (V⊢ , W⊢) ,
  inj₂ (inj₂
    (vW , Σˡ w , Ψˡ w , wfΣˡ w , _ , (_ ∎) ,
     lift (vV , vW , (V⊢ , W⊢))))
𝒱⇒ℰᵢ {n = suc k} {dir = ≼} {w = w} {W = W}
    Vrel@((vV , vW , (V⊢ , W⊢)) , payload) =
  (V⊢ , W⊢) ,
  inj₂ (inj₂
    (vV , Σʳ w , Ψʳ w , wfΣʳ w , W , (W ∎) , Vrel))
𝒱⇒ℰᵢ {n = suc k} {dir = ≽} {w = w} {V = V}
    Vrel@((vV , vW , (V⊢ , W⊢)) , payload) =
  (V⊢ , W⊢) ,
  inj₂ (inj₂
    (vW , Σˡ w , Ψˡ w , wfΣˡ w , V , (V ∎) , Vrel))

𝒱⇒ℰ-sameᵢ :
  ∀ {Ξ A B n dir w V W} {ρ : RelSub Ξ} {p : Ξ ⊢ A ⊑ᵢ B} →
  𝒱 ρ p n dir w V W →
  ℰ ρ p n dir w V W
𝒱⇒ℰ-sameᵢ {n = zero} (lift (vV , vW , (V⊢ , W⊢))) =
  (V⊢ , W⊢) , lift tt
𝒱⇒ℰ-sameᵢ {n = suc k} {dir = dir} {w = w} {V = V} {W = W}
    {ρ = ρ} {p = p} Vrel =
  𝒱⇒ℰᵢ (𝒱-monotone ρ p k dir w V W Vrel)

𝒱-headerᵢ :
  ∀ {Ξ A B n dir w V W} {ρ : RelSub Ξ} {p : Ξ ⊢ A ⊑ᵢ B} →
  𝒱 ρ p n dir w V W →
  VHeader {A = A} {B = B} ρ w V W
𝒱-headerᵢ {n = zero} (lift header) = header
𝒱-headerᵢ {n = suc n} (header , body) = header

fun-app-ℰᵢ :
  ∀ {Ξ A A′ B B′ n dir w V W M N} {ρ : RelSub Ξ}
    {pA : Ξ ⊢ A ⊑ᵢ A′} {pB : Ξ ⊢ B ⊑ᵢ B′} →
  𝒱 ρ (⊑ᵢ-⇒ A A′ B B′ pA pB) n dir w V W →
  ℰ ρ pA (suc n) dir w M N →
  ℰ ρ pB (suc n) dir w (V · M) (W · N)
fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₁
        (Σˡ′ , Ψˡ′ , wfΣˡ′ , M′ , M→M′ ,
         Σʳ′ , Ψʳ′ , wfΣʳ′ , N′ , N↠N′ , rel′)) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₁
    (Σˡ′ , Ψˡ′ , wfΣˡ′ , V · M′ , ξ-·₂ vV M→M′ ,
     Σʳ′ , Ψʳ′ , wfΣʳ′ , W · N′ , appR-↠ vW N↠N′ ,
     ((⊢· V⊢′ (proj₁ (proj₁ rel′)) ,
       ⊢· W⊢′ (proj₂ (proj₁ rel′))) ,
      lift tt))
  where
  wstep : World
  wstep = mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′

  step-grow : wstep ⪰ w
  step-grow = mkWorldˡʳ-⪰ (store-growth M→M′) (multi-store-growth N↠N′)

  V⊢′ : 0 ∣ Ψˡ wstep ∣ Σˡ wstep ∣ [] ⊢ V ⦂ leftᵢ ρ wstep (A ⇒ B)
  V⊢′ = wk⪰ˡ step-grow V⊢

  W⊢′ : 0 ∣ Ψʳ wstep ∣ Σʳ wstep ∣ [] ⊢ W ⦂ rightᵢ ρ wstep (A′ ⇒ B′)
  W⊢′ = wk⪰ʳ step-grow W⊢
fun-app-ℰᵢ {n = zero} {dir = ≼} {w = w} {V = V} {W = W}
    {M = M} {N = N}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) , inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , M↠blame))) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , appR-blame-↠ vV M↠blame))
fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg , N↠Warg ,
        lift (vM′ , vWarg , (M⊢′ , Warg⊢)))))
    with canonical-⇒ vV V⊢
fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg , N↠Warg ,
        lift (vM′ , vWarg , (M⊢′ , Warg⊢)))))
    | fv-ƛ refl with V⊢
fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≼} {w = w} {V = V} {W = W}
    {M = M} {N = N} {ρ = ρ} {pA = pA}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg , N↠Warg ,
        lift (vM′ , vWarg , (M⊢′ , Warg⊢)))))
    | fv-ƛ refl | ⊢ƛ {M = Body} wfA Body⊢ =
  (⊢· (⊢ƛ {M = Body} wfA Body⊢) M⊢ , ⊢· W⊢ N⊢) ,
  inj₁
    (Σˡ w , Ψˡ w , wfΣˡ w , substˣ-term (singleVarEnv M) Body ,
     id-step (β-ƛ vM) ,
     Σʳ′ , Ψʳ′ , wfΣʳ′ , W · Warg , appR-↠ vW N↠Warg ,
     (([]-wt Body⊢ M⊢ , ⊢· W⊢′ Warg⊢) , lift tt))
  where
  growʳ : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  growʳ = mkWorldʳ-⪰ (multi-store-growth N↠Warg)

  W⊢′ :
    0 ∣ Ψʳ (mkWorldʳ w Σʳ′ wfΣʳ′) ∣ Σʳ′ ∣ [] ⊢
      W ⦂ rightᵢ ρ (mkWorldʳ w Σʳ′ wfΣʳ′) (A′ ⇒ B′)
  W⊢′ = wk⪰ʳ growʳ W⊢

fun-app-ℰᵢ {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg , N↠Warg ,
        lift (vM′ , vWarg , (M⊢′ , Warg⊢)))))
    | fv-up-↦ vU refl with V⊢
fun-app-ℰᵢ {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≼} {w = w} {V = .(U up (p ↦ q))}
    {W = W} {M = M} {N = N} {ρ = ρ} {pA = pA}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg , N↠Warg ,
        lift (vM′ , vWarg , (M⊢′ , Warg⊢)))))
    | fv-up-↦ {W = U} {p = p} {q = q} vU refl
    | ⊢up Φ lenΦ U⊢ (wt-↦ p⊢ q⊢) =
  (⊢· (⊢up Φ lenΦ U⊢ (wt-↦ p⊢ q⊢)) M⊢ , ⊢· W⊢ N⊢) ,
  inj₁
    (Σˡ w , Ψˡ w , wfΣˡ w , _ , id-step (β-up-↦ vU vM) ,
     Σʳ′ , Ψʳ′ , wfΣʳ′ , W · Warg , appR-↠ vW N↠Warg ,
     ((⊢up Φ lenΦ (⊢· U⊢ (⊢down Φ lenΦ M⊢ p⊢)) q⊢ ,
       ⊢· W⊢′ Warg⊢) , lift tt))
  where
  growʳ : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  growʳ = mkWorldʳ-⪰ (multi-store-growth N↠Warg)

  W⊢′ =
    wk⪰ʳ
      {w = w} {w′ = mkWorldʳ w Σʳ′ wfΣʳ′}
      {A = rightᵢ ρ w (A′ ⇒ B′)}
      growʳ W⊢

fun-app-ℰᵢ {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg , N↠Warg ,
        lift (vM′ , vWarg , (M⊢′ , Warg⊢)))))
    | fv-down-↦ vU refl with V⊢
fun-app-ℰᵢ {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≼} {w = w} {V = .(U down (p ↦ q))}
    {W = W} {M = M} {N = N} {ρ = ρ} {pA = pA}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg , N↠Warg ,
        lift (vM′ , vWarg , (M⊢′ , Warg⊢)))))
    | fv-down-↦ {W = U} {p = p} {q = q} vU refl
    | ⊢down Φ lenΦ U⊢ (wt-↦ p⊢ q⊢) =
  (⊢· (⊢down Φ lenΦ U⊢ (wt-↦ p⊢ q⊢)) M⊢ , ⊢· W⊢ N⊢) ,
  inj₁
    (Σˡ w , Ψˡ w , wfΣˡ w , _ , id-step (β-down-↦ vU vM) ,
     Σʳ′ , Ψʳ′ , wfΣʳ′ , W · Warg , appR-↠ vW N↠Warg ,
     ((⊢down Φ lenΦ (⊢· U⊢ (⊢up Φ lenΦ M⊢ p⊢)) q⊢ ,
       ⊢· W⊢′ Warg⊢) , lift tt))
  where
  growʳ : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  growʳ = mkWorldʳ-⪰ (multi-store-growth N↠Warg)

  W⊢′ =
    wk⪰ʳ
      {w = w} {w′ = mkWorldʳ w Σʳ′ wfΣʳ′}
      {A = rightᵢ ρ w (A′ ⇒ B′)}
      growʳ W⊢

fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≽} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₁
        (Σʳ′ , Ψʳ′ , wfΣʳ′ , N′ , N→N′ ,
         Σˡ′ , Ψˡ′ , wfΣˡ′ , M′ , M↠M′ , rel′)) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₁
    (Σʳ′ , Ψʳ′ , wfΣʳ′ , W · N′ , ξ-·₂ vW N→N′ ,
     Σˡ′ , Ψˡ′ , wfΣˡ′ , V · M′ , appR-↠ vV M↠M′ ,
     ((⊢· V⊢′ (proj₁ (proj₁ rel′)) ,
       ⊢· W⊢′ (proj₂ (proj₁ rel′))) ,
      lift tt))
  where
  wstep : World
  wstep = mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′

  step-grow : wstep ⪰ w
  step-grow = mkWorldˡʳ-⪰ (multi-store-growth M↠M′) (store-growth N→N′)

  V⊢′ : 0 ∣ Ψˡ wstep ∣ Σˡ wstep ∣ [] ⊢ V ⦂ leftᵢ ρ wstep (A ⇒ B)
  V⊢′ = wk⪰ˡ step-grow V⊢

  W⊢′ : 0 ∣ Ψʳ wstep ∣ Σʳ wstep ∣ [] ⊢ W ⦂ rightᵢ ρ wstep (A′ ⇒ B′)
  W⊢′ = wk⪰ʳ step-grow W⊢
fun-app-ℰᵢ {n = zero} {dir = ≽} {w = w} {V = V} {W = W}
    {M = M} {N = N}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) , inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , M↠blame))) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , appR-blame-↠ vV M↠blame))
fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≽} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg , M↠Warg ,
        lift (vWarg , vN′ , (Warg⊢ , N⊢′)))))
    with canonical-⇒ vW W⊢
fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≽} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg , M↠Warg ,
        lift (vWarg , vN′ , (Warg⊢ , N⊢′)))))
    | fv-ƛ refl with W⊢
fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = zero} {dir = ≽} {w = w} {V = V} {W = W}
    {M = M} {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg , M↠Warg ,
        lift (vWarg , vN′ , (Warg⊢ , N⊢′)))))
    | fv-ƛ refl | ⊢ƛ {M = Body} wfA Body⊢ =
  (⊢· V⊢ M⊢ , ⊢· (⊢ƛ {M = Body} wfA Body⊢) N⊢) ,
  inj₁
    (Σʳ w , Ψʳ w , wfΣʳ w , substˣ-term (singleVarEnv N) Body ,
     id-step (β-ƛ vN) ,
     Σˡ′ , Ψˡ′ , wfΣˡ′ , V · Warg , appR-↠ vV M↠Warg ,
     ((⊢· V⊢′ Warg⊢ , []-wt Body⊢ N⊢) , lift tt))
  where
  growˡ : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  growˡ = mkWorldˡ-⪰ (multi-store-growth M↠Warg)

  V⊢′ :
    0 ∣ Ψˡ (mkWorldˡ w Σˡ′ wfΣˡ′) ∣ Σˡ′ ∣ [] ⊢
      V ⦂ leftᵢ ρ (mkWorldˡ w Σˡ′ wfΣˡ′) (A ⇒ B)
  V⊢′ = wk⪰ˡ growˡ V⊢
fun-app-ℰᵢ {A = A} {B = B} {B′ = B′}
    {n = zero} {dir = ≽} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg , M↠Warg ,
        lift (vWarg , vN′ , (Warg⊢ , N⊢′)))))
    | fv-up-↦ vU refl with W⊢
fun-app-ℰᵢ {A = A} {B = B} {B′ = B′}
    {n = zero} {dir = ≽} {w = w} {V = V}
    {W = .(U up (p ↦ q))} {M = M} {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg , M↠Warg ,
        lift (vWarg , vN′ , (Warg⊢ , N⊢′)))))
    | fv-up-↦ {W = U} {p = p} {q = q} vU refl
    | ⊢up Φ lenΦ U⊢ (wt-↦ p⊢ q⊢) =
  (⊢· V⊢ M⊢ , ⊢· (⊢up Φ lenΦ U⊢ (wt-↦ p⊢ q⊢)) N⊢) ,
  inj₁
    (Σʳ w , Ψʳ w , wfΣʳ w , _ , id-step (β-up-↦ vU vN) ,
     Σˡ′ , Ψˡ′ , wfΣˡ′ , V · Warg , appR-↠ vV M↠Warg ,
     ((⊢· V⊢′ Warg⊢ ,
       ⊢up Φ lenΦ (⊢· U⊢ (⊢down Φ lenΦ N⊢ p⊢)) q⊢) ,
      lift tt))
  where
  growˡ : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  growˡ = mkWorldˡ-⪰ (multi-store-growth M↠Warg)

  V⊢′ =
    wk⪰ˡ
      {w = w} {w′ = mkWorldˡ w Σˡ′ wfΣˡ′}
      {A = leftᵢ ρ w (A ⇒ B)}
      growˡ V⊢
fun-app-ℰᵢ {A = A} {B = B} {B′ = B′}
    {n = zero} {dir = ≽} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg , M↠Warg ,
        lift (vWarg , vN′ , (Warg⊢ , N⊢′)))))
    | fv-down-↦ vU refl with W⊢
fun-app-ℰᵢ {A = A} {B = B} {B′ = B′}
    {n = zero} {dir = ≽} {w = w} {V = V}
    {W = .(U down (p ↦ q))} {M = M} {N = N} {ρ = ρ}
    (lift (vV , vW , (V⊢ , W⊢)))
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg , M↠Warg ,
        lift (vWarg , vN′ , (Warg⊢ , N⊢′)))))
    | fv-down-↦ {W = U} {p = p} {q = q} vU refl
    | ⊢down Φ lenΦ U⊢ (wt-↦ p⊢ q⊢) =
  (⊢· V⊢ M⊢ , ⊢· (⊢down Φ lenΦ U⊢ (wt-↦ p⊢ q⊢)) N⊢) ,
  inj₁
    (Σʳ w , Ψʳ w , wfΣʳ w , _ , id-step (β-down-↦ vU vN) ,
     Σˡ′ , Ψˡ′ , wfΣˡ′ , V · Warg , appR-↠ vV M↠Warg ,
     ((⊢· V⊢′ Warg⊢ ,
       ⊢down Φ lenΦ (⊢· U⊢ (⊢up Φ lenΦ N⊢ p⊢)) q⊢) ,
      lift tt))
  where
  growˡ : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  growˡ = mkWorldˡ-⪰ (multi-store-growth M↠Warg)

  V⊢′ =
    wk⪰ˡ
      {w = w} {w′ = mkWorldˡ w Σˡ′ wfΣˡ′}
      {A = leftᵢ ρ w (A ⇒ B)}
      growˡ V⊢

fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = suc k} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA} {pB = pB}
    Vfun@((vV , vW , (V⊢ , W⊢)) , funsuc)
    ((M⊢ , N⊢) ,
      inj₁
        (Σˡ′ , Ψˡ′ , wfΣˡ′ , M′ , M→M′ ,
         Σʳ′ , Ψʳ′ , wfΣʳ′ , N′ , N↠N′ , rel′)) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₁
    (Σˡ′ , Ψˡ′ , wfΣˡ′ , V · M′ , ξ-·₂ vV M→M′ ,
     Σʳ′ , Ψʳ′ , wfΣʳ′ , W · N′ , appR-↠ vW N↠N′ ,
     fun-app-ℰᵢ Vfun↓ rel′)
  where
  funp : _ ⊢ (A ⇒ B) ⊑ᵢ (A′ ⇒ B′)
  funp = ⊑ᵢ-⇒ A A′ B B′ pA pB

  wstep : World
  wstep = mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′

  step-grow : wstep ⪰ w
  step-grow = mkWorldˡʳ-⪰ (store-growth M→M′) (multi-store-growth N↠N′)

  Vfun↑ : 𝒱 ρ funp (suc k) ≼ wstep V W
  Vfun↑ = 𝒱⇒-⪰ ρ step-grow Vfun

  Vfun↓ : 𝒱 ρ funp k ≼ wstep V W
  Vfun↓ = 𝒱-monotone ρ funp k ≼ wstep V W Vfun↑
fun-app-ℰᵢ {n = suc k} {dir = ≼} {w = w} {V = V} {W = W}
    {M = M} {N = N}
    ((vV , vW , (V⊢ , W⊢)) , funsuc)
    ((M⊢ , N⊢) , inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , M↠blame))) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , appR-blame-↠ vV M↠blame))
fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = suc k} {dir = ≼} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA} {pB = pB}
    Vfun@((vV , vW , (V⊢ , W⊢)) , funsuc)
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vM , Σʳ′ , Ψʳ′ , wfΣʳ′ , Warg , N↠Warg , Varg))) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₁
    (Σˡ w , Ψˡ w , wfΣˡ w , Lβ , stepL ,
     Σʳ′ , Ψʳ′ , wfΣʳ′ , Rβ , right-path , body)
  where
  funp : _ ⊢ (A ⇒ B) ⊑ᵢ (A′ ⇒ B′)
  funp = ⊑ᵢ-⇒ A A′ B B′ pA pB

  growʳ : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  growʳ = mkWorldʳ-⪰ (multi-store-growth N↠Warg)

  Vfun↑ : 𝒱 ρ funp (suc k) ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) V W
  Vfun↑ = 𝒱⇒-⪰ ρ growʳ Vfun

  top-step :
    ∀ {w′} →
    w′ ⪰ (mkWorldʳ w Σʳ′ wfΣʳ′) →
    ∀ {V′ W′} →
    𝒱 ρ pA (suc k) ≼ w′ V′ W′ →
    Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
      (Σˡ w′ ∣ (V · V′) —→ Σˡ w′ ∣ Lβ) ×
      (Σʳ w′ ∣ (W · W′) —→ Σʳ w′ ∣ Rβ) ×
      ℰ ρ pB (suc k) ≼ w′ Lβ Rβ
  top-step = proj₁ (proj₂ Vfun↑)

  LβRβ :
    Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
      (Σˡ (mkWorldʳ w Σʳ′ wfΣʳ′) ∣ (V · M) —→
       Σˡ (mkWorldʳ w Σʳ′ wfΣʳ′) ∣ Lβ) ×
      (Σʳ (mkWorldʳ w Σʳ′ wfΣʳ′) ∣ (W · Warg) —→
       Σʳ (mkWorldʳ w Σʳ′ wfΣʳ′) ∣ Rβ) ×
      ℰ ρ pB (suc k) ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Lβ Rβ
  LβRβ = top-step ⪰-refl Varg

  Lβ : Term
  Lβ = proj₁ LβRβ

  Rβ : Term
  Rβ = proj₁ (proj₂ LβRβ)

  stepL : Σˡ w ∣ V · M —→ Σˡ w ∣ Lβ
  stepL = proj₁ (proj₂ (proj₂ LβRβ))

  stepR : Σʳ′ ∣ W · Warg —→ Σʳ′ ∣ Rβ
  stepR = proj₁ (proj₂ (proj₂ (proj₂ LβRβ)))

  body : ℰ ρ pB (suc k) ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Lβ Rβ
  body = proj₂ (proj₂ (proj₂ (proj₂ LβRβ)))

  right-path : Σʳ w ∣ W · N —↠ Σʳ′ ∣ Rβ
  right-path =
    multi-trans (appR-↠ vW N↠Warg)
      ((W · Warg) —→⟨ stepR ⟩ Rβ ∎)
fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = suc k} {dir = ≽} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA} {pB = pB}
    Vfun@((vV , vW , (V⊢ , W⊢)) , funsuc)
    ((M⊢ , N⊢) ,
      inj₁
        (Σʳ′ , Ψʳ′ , wfΣʳ′ , N′ , N→N′ ,
         Σˡ′ , Ψˡ′ , wfΣˡ′ , M′ , M↠M′ , rel′)) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₁
    (Σʳ′ , Ψʳ′ , wfΣʳ′ , W · N′ , ξ-·₂ vW N→N′ ,
     Σˡ′ , Ψˡ′ , wfΣˡ′ , V · M′ , appR-↠ vV M↠M′ ,
     fun-app-ℰᵢ Vfun↓ rel′)
  where
  funp : _ ⊢ (A ⇒ B) ⊑ᵢ (A′ ⇒ B′)
  funp = ⊑ᵢ-⇒ A A′ B B′ pA pB

  wstep : World
  wstep = mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′

  step-grow : wstep ⪰ w
  step-grow = mkWorldˡʳ-⪰ (multi-store-growth M↠M′) (store-growth N→N′)

  Vfun↑ : 𝒱 ρ funp (suc k) ≽ wstep V W
  Vfun↑ = 𝒱⇒-⪰ ρ step-grow Vfun

  Vfun↓ : 𝒱 ρ funp k ≽ wstep V W
  Vfun↓ = 𝒱-monotone ρ funp k ≽ wstep V W Vfun↑
fun-app-ℰᵢ {n = suc k} {dir = ≽} {w = w} {V = V} {W = W}
    {M = M} {N = N}
    ((vV , vW , (V⊢ , W⊢)) , funsuc)
    ((M⊢ , N⊢) , inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , M↠blame))) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , appR-blame-↠ vV M↠blame))
fun-app-ℰᵢ {A = A} {A′ = A′} {B = B} {B′ = B′}
    {n = suc k} {dir = ≽} {w = w} {V = V} {W = W} {M = M}
    {N = N} {ρ = ρ} {pA = pA} {pB = pB}
    Vfun@((vV , vW , (V⊢ , W⊢)) , funsuc)
    ((M⊢ , N⊢) ,
      inj₂ (inj₂ (vN , Σˡ′ , Ψˡ′ , wfΣˡ′ , Warg , M↠Warg , Varg))) =
  (⊢· V⊢ M⊢ , ⊢· W⊢ N⊢) ,
  inj₁
    (Σʳ w , Ψʳ w , wfΣʳ w , Rβ , stepR ,
     Σˡ′ , Ψˡ′ , wfΣˡ′ , Lβ , left-path , body)
  where
  funp : _ ⊢ (A ⇒ B) ⊑ᵢ (A′ ⇒ B′)
  funp = ⊑ᵢ-⇒ A A′ B B′ pA pB

  growˡ : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
  growˡ = mkWorldˡ-⪰ (multi-store-growth M↠Warg)

  Vfun↑ : 𝒱 ρ funp (suc k) ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) V W
  Vfun↑ = 𝒱⇒-⪰ ρ growˡ Vfun

  top-step :
    ∀ {w′} →
    w′ ⪰ (mkWorldˡ w Σˡ′ wfΣˡ′) →
    ∀ {V′ W′} →
    𝒱 ρ pA (suc k) ≽ w′ V′ W′ →
    Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
      (Σˡ w′ ∣ (V · V′) —→ Σˡ w′ ∣ Lβ) ×
      (Σʳ w′ ∣ (W · W′) —→ Σʳ w′ ∣ Rβ) ×
      ℰ ρ pB (suc k) ≽ w′ Lβ Rβ
  top-step = proj₁ (proj₂ Vfun↑)

  LβRβ :
    Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
      (Σˡ (mkWorldˡ w Σˡ′ wfΣˡ′) ∣ (V · Warg) —→
       Σˡ (mkWorldˡ w Σˡ′ wfΣˡ′) ∣ Lβ) ×
      (Σʳ (mkWorldˡ w Σˡ′ wfΣˡ′) ∣ (W · N) —→
       Σʳ (mkWorldˡ w Σˡ′ wfΣˡ′) ∣ Rβ) ×
      ℰ ρ pB (suc k) ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Lβ Rβ
  LβRβ = top-step ⪰-refl Varg

  Lβ : Term
  Lβ = proj₁ LβRβ

  Rβ : Term
  Rβ = proj₁ (proj₂ LβRβ)

  stepL : Σˡ′ ∣ V · Warg —→ Σˡ′ ∣ Lβ
  stepL = proj₁ (proj₂ (proj₂ LβRβ))

  stepR : Σʳ w ∣ W · N —→ Σʳ w ∣ Rβ
  stepR = proj₁ (proj₂ (proj₂ (proj₂ LβRβ)))

  body : ℰ ρ pB (suc k) ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Lβ Rβ
  body = proj₂ (proj₂ (proj₂ (proj₂ LβRβ)))

  left-path : Σˡ w ∣ V · M —↠ Σˡ′ ∣ Lβ
  left-path =
    multi-trans (appR-↠ vV M↠Warg)
      ((V · Warg) —→⟨ stepL ⟩ Lβ ∎)


seal-value-invᵢ :
  ∀ {V p α} →
  Value (V down seal p α) →
  Value V
seal-value-invᵢ (vV down seal) = vV

seal-typed-invᵢ :
  ∀ {Δ Ψ Σ Γ V α A} →
  Uniqueˢ Σ →
  Σ ∋ˢ α ⦂ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (V down seal (id A) α) ⦂ ｀ α →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ V ⦂ A
seal-typed-invᵢ uΣ α∈ (⊢down Φ lenΦ V⊢ (wt-seal (wt-id wfA) h α∈Φ)) =
  cong-⊢⦂ refl refl refl (lookup-unique uΣ h α∈) V⊢
seal-typed-invᵢ uΣ α∈ (⊢down Φ lenΦ V⊢ (wt-seal★ (wt-id wfA) h α∈Φ)) =
  cong-⊢⦂ refl refl refl (lookup-unique uΣ h α∈) V⊢

relᵗ-zero-𝒱ᵢ :
  ∀ {Ξ k dir w V W} {ρ : RelSub (plain ∷ Ξ)} →
  Value V →
  Value W →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ leftᵢ ρ w (＇ zero) →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w (＇ zero) →
  relᵗ ρ zero k dir V W →
  𝒱 ρ (⊑ᵢ-＇ here) k dir w V W
relᵗ-zero-𝒱ᵢ {k = zero} vV vW V⊢ W⊢ rel =
  lift (vV , vW , (V⊢ , W⊢))
relᵗ-zero-𝒱ᵢ {k = suc k} vV vW V⊢ W⊢ rel =
  (vV , vW , (V⊢ , W⊢)) , lift rel

ℕ-payload-𝒱ᵢ :
  ∀ {Ξ k dir w V W} {ρ : RelSub Ξ} →
  Value V →
  Value W →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ leftᵢ ρ w (‵ `ℕ) →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w (‵ `ℕ) →
  ℕ-payload V W →
  𝒱 ρ (⊑ᵢ-‵ `ℕ) k dir w V W
ℕ-payload-𝒱ᵢ {k = zero} vV vW V⊢ W⊢ payload =
  lift (vV , vW , (V⊢ , W⊢))
ℕ-payload-𝒱ᵢ {k = suc k} vV vW V⊢ W⊢ payload =
  (vV , vW , (V⊢ , W⊢)) , payload

wf∀-invᵢ : ∀ {Δ Ψ A} → WfTy Δ Ψ (`∀ A) → WfTy (suc Δ) Ψ A
wf∀-invᵢ (wf∀ hA) = hA

postulate
  instCast-bridge-𝒱⇒ℰ⊑ᵢ-fallback : InstCastBridge𝒱⇒ℰ⊑ᵢ

mutual
  instCast-bridge-𝒱⇒ℰ⊒ᵢ : InstCastBridge𝒱⇒ℰ⊒ᵢ
  instCast-bridge-𝒱⇒ℰ⊒ᵢ
      {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ} {n = zero}
      {dir = dir} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = ⊑ᵢ-⇒ Aˡ Aʳ Bˡ Bʳ pA pB}
      {pν = arrowν-p@(⊑ᵢ-⇒ .Aˡ .Aʳ .Bˡ .Bʳ pAν pBν)}
      {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ (wf⇒ hAˡ hBˡ) (wf⇒ hAʳ hBʳ)
      αˡ∈ αʳ∈ V W (lift (vV , vW , (V⊢ , W⊢))) =
    𝒱⇒ℰᵢ casted-𝒱
    where
    ρSeal : RelSub (ν-bound ∷ _)
    ρSeal = extendνρ ρ (ηentry αˡ αʳ Rrel downR)
  
    left-typed =
      instCast-down-left-typedᵢν
        {A = Aˡ ⇒ Bˡ} {Tˡ = Tˡ} {Tʳ = Tʳ}
        {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
        {pT = pT} {wfTˡc = wfTˡc} {wfTʳc = wfTʳc}
        {downR = downR} {w = w} {L = V}
        hTˡ hTʳ (wf⇒ hAˡ hBˡ) αˡ∈ V⊢
  
    right-typed =
      instCast-down-right-typedᵢν
        {B = Aʳ ⇒ Bʳ} {Tˡ = Tˡ} {Tʳ = Tʳ}
        {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
        {pT = pT} {wfTˡc = wfTˡc} {wfTʳc = wfTʳc}
        {downR = downR} {w = w} {R = W}
        hTˡ hTʳ (wf⇒ hAʳ hBʳ) αʳ∈ W⊢
  
    casted-𝒱 :
      𝒱 ρSeal arrowν-p zero dir w
        (V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w (Aˡ ⇒ Bˡ)}
          {α = αˡ}))
        (W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w (Aʳ ⇒ Bʳ)}
          {α = αʳ}))
    casted-𝒱 =
      lift ((vV down
          (_↦_
            {p = instCast⊑ {A = Tˡ} {B = left∀ᵢ ρ w Aˡ} {α = αˡ}}
            {q = instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w Bˡ} {α = αˡ}})) ,
        (vW down
          (_↦_
            {p = instCast⊑ {A = Tʳ} {B = right∀ᵢ ρ w Aʳ} {α = αʳ}}
            {q = instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w Bʳ} {α = αʳ}})) ,
        (left-typed , right-typed))
  instCast-bridge-𝒱⇒ℰ⊒ᵢ
      {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ} {n = suc k}
      {dir = dir} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = ⊑ᵢ-⇒ Aˡ Aʳ Bˡ Bʳ pA pB}
      {pν = arrowν-p@(⊑ᵢ-⇒ .Aˡ .Aʳ .Bˡ .Bʳ pAν pBν)}
      {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ (wf⇒ hAˡ hBˡ) (wf⇒ hAʳ hBʳ)
      αˡ∈ αʳ∈ V W Vrel@((vV , vW , (V⊢ , W⊢)) , fun-rel) =
    𝒱⇒ℰᵢ casted-𝒱
    where
    ρSeal : RelSub (ν-bound ∷ _)
    ρSeal = extendνρ ρ (ηentry αˡ αʳ Rrel downR)
  
    ρApp : RelSub (plain ∷ _)
    ρApp = extendPlainρ ρ Tˡ Tʳ wfTˡc wfTʳc pT Rrel downR
  
    arrow-p : plain ∷ _ ⊢ Aˡ ⇒ Bˡ ⊑ᵢ Aʳ ⇒ Bʳ
    arrow-p = ⊑ᵢ-⇒ Aˡ Aʳ Bˡ Bʳ pA pB
  
    left-typed =
      instCast-down-left-typedᵢν
        {A = Aˡ ⇒ Bˡ} {Tˡ = Tˡ} {Tʳ = Tʳ}
        {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
        {pT = pT} {wfTˡc = wfTˡc} {wfTʳc = wfTʳc}
        {downR = downR} {w = w} {L = V}
        hTˡ hTʳ (wf⇒ hAˡ hBˡ) αˡ∈ V⊢
  
    right-typed =
      instCast-down-right-typedᵢν
        {B = Aʳ ⇒ Bʳ} {Tˡ = Tˡ} {Tʳ = Tʳ}
        {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
        {pT = pT} {wfTˡc = wfTˡc} {wfTʳc = wfTʳc}
        {downR = downR} {w = w} {R = W}
        hTˡ hTʳ (wf⇒ hAʳ hBʳ) αʳ∈ W⊢
  
    casted-𝒱′ :
      (m : ℕ) →
      𝒱 ρApp arrow-p m dir w V W →
      𝒱 ρSeal arrowν-p m dir w
        (V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w (Aˡ ⇒ Bˡ)}
          {α = αˡ}))
        (W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w (Aʳ ⇒ Bʳ)}
          {α = αʳ}))
    casted-𝒱′ zero rel =
      lift ((proj₁ header₀ down
          (_↦_
            {p = instCast⊑ {A = Tˡ} {B = left∀ᵢ ρ w Aˡ} {α = αˡ}}
            {q = instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w Bˡ} {α = αˡ}})) ,
        (proj₁ (proj₂ header₀) down
          (_↦_
            {p = instCast⊑ {A = Tʳ} {B = right∀ᵢ ρ w Aʳ} {α = αʳ}}
            {q = instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w Bʳ} {α = αʳ}})) ,
        (left-typed , right-typed))
      where
      header₀ : VHeader {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ} ρApp w V W
      header₀ =
        𝒱-headerᵢ
          {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ} {n = zero}
          {dir = dir} {w = w} {V = V} {W = W}
          {ρ = ρApp} {p = arrow-p} rel
    casted-𝒱′ (suc j) rel =
      ((proj₁ header down
          (_↦_
            {p = instCast⊑ {A = Tˡ} {B = left∀ᵢ ρ w Aˡ} {α = αˡ}}
            {q = instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w Bˡ} {α = αˡ}})) ,
        (proj₁ (proj₂ header) down
          (_↦_
            {p = instCast⊑ {A = Tʳ} {B = right∀ᵢ ρ w Aʳ} {α = αʳ}}
            {q = instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w Bʳ} {α = αʳ}})) ,
        (left-typed , right-typed)) ,
      (app-top , rest)
      where
      header : VHeader {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ} ρApp w V W
      header = 𝒱-headerᵢ {p = arrow-p} rel
  
      rel↓ : 𝒱 ρApp arrow-p j dir w V W
      rel↓ = 𝒱-monotone ρApp arrow-p j dir w V W rel
  
      rest :
        𝒱′ ρSeal j dir pAν pBν w
          (V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w (Aˡ ⇒ Bˡ)}
            {α = αˡ}))
          (W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w (Aʳ ⇒ Bʳ)}
            {α = αʳ}))
      rest = casted-rest j rel↓
        where
        casted-rest :
          (m : ℕ) →
          𝒱 ρApp arrow-p m dir w V W →
          𝒱′ ρSeal m dir pAν pBν w
            (V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w (Aˡ ⇒ Bˡ)}
              {α = αˡ}))
            (W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w (Aʳ ⇒ Bʳ)}
              {α = αʳ}))
        casted-rest zero rel₀ = lift tt
        casted-rest (suc m) relₛ = proj₂ (casted-𝒱′ (suc m) relₛ)
  
      app-top :
        ∀ {w′} →
        w′ ⪰ w →
        ∀ {V′ W′} →
        𝒱 ρSeal pAν (suc j) dir w′ V′ W′ →
        Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
          (Σˡ w′ ∣
            ((V down (instCast⊒ {A = Tˡ}
              {B = left∀ᵢ ρ w (Aˡ ⇒ Bˡ)} {α = αˡ})) · V′)
            —→ Σˡ w′ ∣ Lβ) ×
          (Σʳ w′ ∣
            ((W down (instCast⊒ {A = Tʳ}
              {B = right∀ᵢ ρ w (Aʳ ⇒ Bʳ)} {α = αʳ})) · W′)
            —→ Σʳ w′ ∣ Rβ) ×
          ℰ ρSeal pBν (suc j) dir w′ Lβ Rβ
      app-top {w′ = w′} w′⪰ {V′ = V′} {W′ = W′} arg =
        Lβ , Rβ ,
        id-step (β-down-↦ (proj₁ header′)
          (proj₁ (𝒱-headerᵢ {p = pAν} arg))) ,
        id-step (β-down-↦ (proj₁ (proj₂ header′))
          (proj₁ (proj₂ (𝒱-headerᵢ {p = pAν} arg)))) ,
        cod-down
        where
        rel↑ : 𝒱 ρApp arrow-p (suc j) dir w′ V W
        rel↑ = 𝒱⇒-⪰ ρApp {pA = pA} {pB = pB} w′⪰ rel
  
        header′ : VHeader {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ} ρApp w′ V W
        header′ = 𝒱-headerᵢ {p = arrow-p} rel↑
  
        Lβ : Term
        Lβ =
          (V · (V′ up (instCast⊑ {A = Tˡ} {B = left∀ᵢ ρ w′ Aˡ}
            {α = αˡ})))
          down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w′ Bˡ} {α = αˡ})
  
        Rβ : Term
        Rβ =
          (W · (W′ up (instCast⊑ {A = Tʳ} {B = right∀ᵢ ρ w′ Aʳ}
            {α = αʳ})))
          down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w′ Bʳ} {α = αʳ})
  
        fun′ : 𝒱 ρApp arrow-p j dir w′ V W
        fun′ = 𝒱-monotone ρApp arrow-p j dir w′ V W rel↑
  
        arg-up :
          ℰ ρApp pA (suc j) dir w′
            (V′ up (instCast⊑ {A = Tˡ} {B = left∀ᵢ ρ w′ Aˡ}
              {α = αˡ}))
            (W′ up (instCast⊑ {A = Tʳ} {B = right∀ᵢ ρ w′ Aʳ}
              {α = αʳ}))
        arg-up =
          instCast-bridge-𝒱⇒ℰ⊑ᵢ
            {A = Aˡ} {B = Aʳ} {n = j} {dir = dir} {w = w′}
            {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
            {ρ = ρ} {p = pA} {pT = pT}
            {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
            Rrel downR
            (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ w′⪰))
            (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ w′⪰))
            (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ w′⪰))
            (WfTy-weakenˢ hAʳ (_⪰_.growΨʳ w′⪰))
            (wkLookupˢ (_⪰_.growˡ w′⪰) αˡ∈)
            (wkLookupˢ (_⪰_.growʳ w′⪰) αʳ∈)
            V′ W′
            (𝒱-monotone ρSeal pAν j dir w′ V′ W′ arg)
  
        app-rel :
          ℰ ρApp pB (suc j) dir w′
            (V · (V′ up (instCast⊑ {A = Tˡ} {B = left∀ᵢ ρ w′ Aˡ}
              {α = αˡ})))
            (W · (W′ up (instCast⊑ {A = Tʳ} {B = right∀ᵢ ρ w′ Aʳ}
              {α = αʳ})))
        app-rel = fun-app-ℰᵢ fun′ arg-up
  
        cod-down :
          ℰ ρSeal pBν (suc j) dir w′ Lβ Rβ
        cod-down =
          instCast-bridge-ℰ⊒ᵢ
            {A = Bˡ} {B = Bʳ} {n = suc j} {dir = dir} {w = w′}
            {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
            {ρ = ρ} {p = pB} {pT = pT}
            {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
            Rrel downR
            (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ w′⪰))
            (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ w′⪰))
            (WfTy-weakenˢ hBˡ (_⪰_.growΨˡ w′⪰))
            (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ w′⪰))
            (wkLookupˢ (_⪰_.growˡ w′⪰) αˡ∈)
            (wkLookupˢ (_⪰_.growʳ w′⪰) αʳ∈)
            (V · (V′ up (instCast⊑ {A = Tˡ}
              {B = left∀ᵢ ρ w′ Aˡ} {α = αˡ})))
            (W · (W′ up (instCast⊑ {A = Tʳ}
              {B = right∀ᵢ ρ w′ Aʳ} {α = αʳ})))
            app-rel
  
    casted-𝒱 :
      𝒱 ρSeal arrowν-p (suc k) dir w
        (V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w (Aˡ ⇒ Bˡ)}
          {α = αˡ}))
        (W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w (Aʳ ⇒ Bʳ)}
          {α = αʳ}))
    casted-𝒱 = casted-𝒱′ (suc k) Vrel
  instCast-bridge-𝒱⇒ℰ⊒ᵢ
      {A = `∀ Aˡ} {B = `∀ Aʳ} {n = zero}
      {dir = dir} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = ⊑ᵢ-∀ Aˡ Aʳ p}
      {pν = p∀ν@(⊑ᵢ-∀ .Aˡ .Aʳ pν)}
      {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ (wf∀ hAˡ) (wf∀ hAʳ)
      αˡ∈ αʳ∈ V W (lift (vV , vW , (V⊢ , W⊢))) =
    𝒱⇒ℰᵢ casted-𝒱
    where
    ρSeal : RelSub (ν-bound ∷ _)
    ρSeal = extendνρ ρ (ηentry αˡ αʳ Rrel downR)
  
    left-typed =
      instCast-down-left-typedᵢν
        {A = `∀ Aˡ} {Tˡ = Tˡ} {Tʳ = Tʳ}
        {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
        {pT = pT} {wfTˡc = wfTˡc} {wfTʳc = wfTʳc}
        {downR = downR} {w = w} {L = V}
        hTˡ hTʳ (wf∀ hAˡ) αˡ∈ V⊢
  
    right-typed =
      instCast-down-right-typedᵢν
        {B = `∀ Aʳ} {Tˡ = Tˡ} {Tʳ = Tʳ}
        {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
        {pT = pT} {wfTˡc = wfTˡc} {wfTʳc = wfTʳc}
        {downR = downR} {w = w} {R = W}
        hTˡ hTʳ (wf∀ hAʳ) αʳ∈ W⊢
  
    casted-𝒱 :
      𝒱 ρSeal p∀ν zero dir w
        (V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w (`∀ Aˡ)}
          {α = αˡ}))
        (W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w (`∀ Aʳ)}
          {α = αʳ}))
    casted-𝒱 =
      lift ((vV down ∀ᵖ) , (vW down ∀ᵖ) , (left-typed , right-typed))
  instCast-bridge-𝒱⇒ℰ⊒ᵢ
      {A = `∀ Aˡ} {B = `∀ Aʳ} {n = suc zero}
      {dir = dir} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = ⊑ᵢ-∀ Aˡ Aʳ p}
      {pν = p∀ν@(⊑ᵢ-∀ .Aˡ .Aʳ pν)}
      {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ (wf∀ hAˡ) (wf∀ hAʳ)
      αˡ∈ αʳ∈ V W ((vV , vW , (V⊢ , W⊢)) , payload) =
    𝒱⇒ℰᵢ casted-𝒱
    where
    ρSeal : RelSub (ν-bound ∷ _)
    ρSeal = extendνρ ρ (ηentry αˡ αʳ Rrel downR)

    left-cast-wt =
      instCast⊒-wt hTˡ (wf∀ hAˡ) αˡ∈
        (every-member-conv αˡ (storeWf-dom< (wfΣˡ w) αˡ∈))

    right-cast-wt =
      instCast⊒-wt hTʳ (wf∀ hAʳ) αʳ∈
        (every-member-conv αʳ (storeWf-dom< (wfΣʳ w) αʳ∈))

    left-whole-wf : WfTy 0 (Ψˡ w) (leftᵢ ρSeal w (`∀ Aˡ))
    left-whole-wf =
      subst (WfTy 0 (Ψˡ w))
        (sym
          (extendνρ-left-openᵢ {A = `∀ Aˡ}
            {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} ρ w))
        (⊒-tgt-wf (wfΣˡ w) (length-every (Ψˡ w)) left-cast-wt)

    left-body-wf : WfTy (suc 0) (Ψˡ w) (left∀ᵢ ρSeal w Aˡ)
    left-body-wf = wf∀-invᵢ left-whole-wf

    right-whole-wf : WfTy 0 (Ψʳ w) (rightᵢ ρSeal w (`∀ Aʳ))
    right-whole-wf =
      subst (WfTy 0 (Ψʳ w))
        (sym
          (extendνρ-right-openᵢ {A = `∀ Aʳ}
            {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} ρ w))
        (⊒-tgt-wf (wfΣʳ w) (length-every (Ψʳ w)) right-cast-wt)

    right-body-wf : WfTy (suc 0) (Ψʳ w) (right∀ᵢ ρSeal w Aʳ)
    right-body-wf = wf∀-invᵢ right-whole-wf

    left-typed =
      instCast-down-left-typedᵢν
        {A = `∀ Aˡ} {Tˡ = Tˡ} {Tʳ = Tʳ}
        {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
        {pT = pT} {wfTˡc = wfTˡc} {wfTʳc = wfTʳc}
        {downR = downR} {w = w} {L = V}
        hTˡ hTʳ (wf∀ hAˡ) αˡ∈ V⊢

    right-typed =
      instCast-down-right-typedᵢν
        {B = `∀ Aʳ} {Tˡ = Tˡ} {Tʳ = Tʳ}
        {αˡ = αˡ} {αʳ = αʳ} {Rrel = Rrel} {ρ = ρ}
        {pT = pT} {wfTˡc = wfTˡc} {wfTʳc = wfTʳc}
        {downR = downR} {w = w} {R = W}
        hTˡ hTʳ (wf∀ hAʳ) αʳ∈ W⊢

    typeapp-payload :
      𝒱body ρSeal p∀ν (suc zero) dir w
        (V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w (`∀ Aˡ)}
          {α = αˡ}))
        (W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w (`∀ Aʳ)}
          {α = αʳ}))
    typeapp-payload {w′ = w′} w′⪰ Srel downS Uˡ Uʳ hUˡ hUʳ pU =
      (left-app⊢ , right-app⊢) ,
      step-body
      where
      left-app⊢raw =
        ⊢• (wk⪰ˡ w′⪰ left-typed)
          (WfTy-weakenˢ left-body-wf (_⪰_.growΨˡ w′⪰))
          hUˡ

      left-app⊢ =
        cong-⊢⦂ refl refl refl
          (sym
            (extendPlainρ-left-openᵢ
              {A = Aˡ} {Tˡ = Uˡ} ρSeal w′))
          left-app⊢raw

      right-app⊢raw =
        ⊢• (wk⪰ʳ w′⪰ right-typed)
          (WfTy-weakenˢ right-body-wf (_⪰_.growΨʳ w′⪰))
          hUʳ

      right-app⊢ =
        cong-⊢⦂ refl refl refl
          (sym
            (extendPlainρ-right-openᵢ
              {A = Aʳ} {Tʳ = Uʳ} ρSeal w′))
          right-app⊢raw

      left-step = preservation-step
        (wfΣˡ w′) left-app⊢raw (β-down-∀ vV)

      right-step = preservation-step
        (wfΣʳ w′) right-app⊢raw (β-down-∀ vW)

      left-Ψ′ : SealCtx
      left-Ψ′ = proj₁ left-step

      right-Ψ′ : SealCtx
      right-Ψ′ = proj₁ right-step

      left-eq : StepCtxExact shape-suc (Ψˡ w′) left-Ψ′
      left-eq = proj₁ (proj₂ left-step)

      right-eq : StepCtxExact shape-suc (Ψʳ w′) right-Ψ′
      right-eq = proj₁ (proj₂ right-step)

      Lβ⊢raw = proj₂ (proj₂ left-step)

      Rβ⊢raw = proj₂ (proj₂ right-step)

      Lβ⊢ =
        cong-⊢⦂ refl refl refl
          (sym
            (extendPlainρ-left-openᵢ
              {A = Aˡ} {Tˡ = Uˡ} ρSeal w′))
          Lβ⊢raw

      Rβ⊢ =
        cong-⊢⦂ refl refl refl
          (sym
            (extendPlainρ-right-openᵢ
              {A = Aʳ} {Tʳ = Uʳ} ρSeal w′))
          Rβ⊢raw

      wfΣˡ′ : StoreWf 0 left-Ψ′
        ((length (Σˡ w′) , Uˡ) ∷ Σˡ w′)
      wfΣˡ′ =
        preservation-step-storeWf
          (wfΣˡ w′) left-app⊢raw (β-down-∀ vV)

      wfΣʳ′ : StoreWf 0 right-Ψ′
        ((length (Σʳ w′) , Uʳ) ∷ Σʳ w′)
      wfΣʳ′ =
        preservation-step-storeWf
          (wfΣʳ w′) right-app⊢raw (β-down-∀ vW)

      zero-cont =
        (Lβ⊢ , Rβ⊢) , lift tt

      step-body-dir :
        (d : Dir) →
        ℰbody
          (extendPlainρ ρSeal Uˡ Uʳ
            (Ψˡ w′ , hUˡ) (Ψʳ w′ , hUʳ) pU Srel downS)
          pν (suc zero) d w′
          ((V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w (`∀ Aˡ)}
            {α = αˡ})) ⦂∀ left∀ᵢ ρSeal w′ Aˡ [ Uˡ ])
          ((W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w (`∀ Aʳ)}
            {α = αʳ})) ⦂∀ right∀ᵢ ρSeal w′ Aʳ [ Uʳ ])
      step-body-dir ≼ =
        inj₁
          (((length (Σˡ w′) , Uˡ) ∷ Σˡ w′) , left-Ψ′ , wfΣˡ′ , _ ,
           β-down-∀ vV ,
           ((length (Σʳ w′) , Uʳ) ∷ Σʳ w′) , right-Ψ′ , wfΣʳ′ , _ ,
           (_ —→⟨ β-down-∀ vW ⟩ _ ∎) ,
           zero-cont)
      step-body-dir ≽ =
        inj₁
          (((length (Σʳ w′) , Uʳ) ∷ Σʳ w′) , right-Ψ′ , wfΣʳ′ , _ ,
           β-down-∀ vW ,
           ((length (Σˡ w′) , Uˡ) ∷ Σˡ w′) , left-Ψ′ , wfΣˡ′ , _ ,
           (_ —→⟨ β-down-∀ vV ⟩ _ ∎) ,
           zero-cont)

      step-body : ℰbody
        (extendPlainρ ρSeal Uˡ Uʳ
          (Ψˡ w′ , hUˡ) (Ψʳ w′ , hUʳ) pU Srel downS)
        pν (suc zero) dir w′
        ((V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w (`∀ Aˡ)}
          {α = αˡ})) ⦂∀ left∀ᵢ ρSeal w′ Aˡ [ Uˡ ])
        ((W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w (`∀ Aʳ)}
          {α = αʳ})) ⦂∀ right∀ᵢ ρSeal w′ Aʳ [ Uʳ ])
      step-body = step-body-dir dir

    casted-𝒱 :
      𝒱 ρSeal p∀ν (suc zero) dir w
        (V down (instCast⊒ {A = Tˡ} {B = left∀ᵢ ρ w (`∀ Aˡ)}
          {α = αˡ}))
        (W down (instCast⊒ {A = Tʳ} {B = right∀ᵢ ρ w (`∀ Aʳ)}
          {α = αʳ}))
    casted-𝒱 =
      ((vV down ∀ᵖ) , (vW down ∀ᵖ) , (left-typed , right-typed)) ,
      typeapp-payload
  instCast-bridge-𝒱⇒ℰ⊒ᵢ Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W Vrel =
    instCast-bridge-𝒱⇒ℰ⊒ᵢ-fallback
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W Vrel
  
  instCast-bridge-𝒱⇒ℰ⊑ᵢ : InstCastBridge𝒱⇒ℰ⊑ᵢ
  instCast-bridge-𝒱⇒ℰ⊑ᵢ Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W Vrel =
    instCast-bridge-𝒱⇒ℰ⊑ᵢ-fallback
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ V W Vrel
  
  instCast-bridge-ℰ⊑ᵢ : InstCastBridgeℰ⊑ᵢ
  instCast-bridge-ℰ⊑ᵢ
      {A = A} {B = B} {n = zero}
      {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {pT = pT} {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) , rel) =
    (instCast-up-left-typedᵢν
       {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {L = L}
       hTˡ hTʳ hAˡ αˡ∈ L⊢ ,
     instCast-up-right-typedᵢν
       {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {R = R}
       hTˡ hTʳ hBʳ αʳ∈ R⊢) ,
    lift tt
  instCast-bridge-ℰ⊑ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pν = pν} {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₁
          (Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L→L′ ,
           Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R↠R′ , rel′)) =
    (L↑⊢ , R↑⊢) ,
    inj₁
      (Σˡ′ , Ψˡ′ , wfΣˡ′ , _ , ξ-up L→L′ ,
       Σʳ′ , Ψʳ′ , wfΣʳ′ , _ , up-↠ R↠R′ ,
       instCast-bridge-ℰ⊑ᵢ
         {A = A} {B = B} {n = k} {dir = ≼}
         {w = mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′}
         {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
         {ρ = ρ} {p = p} {pT = pT}
         {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
         Rrel downR
         (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ grow))
         (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ grow))
         (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ grow))
         (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ grow))
         (wkLookupˢ (store-growth L→L′) αˡ∈)
         (wkLookupˢ (multi-store-growth R↠R′) αʳ∈)
         L′ R′ rel′)
    where
    grow : mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′ ⪰ w
    grow = mkWorldˡʳ-⪰ (store-growth L→L′) (multi-store-growth R↠R′)
  
    L↑⊢ = instCast-up-left-typedᵢν
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
      {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢
  
    R↑⊢ = instCast-up-right-typedᵢν
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
      {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢
  instCast-bridge-ℰ⊑ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {pT = pT} {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , L↠blame))) =
    (instCast-up-left-typedᵢν
       {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢ ,
     instCast-up-right-typedᵢν
       {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢) ,
    inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , up-blame-↠ L↠blame))
  instCast-bridge-ℰ⊑ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pν = pν} {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₂ (inj₂
          (vL , Σʳ′ , Ψʳ′ , wfΣʳ′ , W , R↠W , Vrel))) =
    ℰ-pull-≼-right-↠
      {ρ = extendPlainρ ρ Tˡ Tʳ wfTˡc wfTʳc pT Rrel downR}
      {p = p} {k = suc k} {w = w}
      {Σʳ′ = Σʳ′} {Ψʳ′ = Ψʳ′} {wfΣʳ′ = wfΣʳ′}
      (instCast-up-left-typedᵢν
        {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
        {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢)
      (instCast-up-right-typedᵢν
        {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
        {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢)
      (up-↠ R↠W)
      (instCast-bridge-𝒱⇒ℰ⊑ᵢ
        {A = A} {B = B} {n = k} {dir = ≼}
        {w = mkWorldʳ w Σʳ′ wfΣʳ′}
        {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {ρ = ρ} {p = p} {pT = pT}
        {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
        Rrel downR
        hTˡ
        (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ grow))
        hAˡ
        (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ grow))
        αˡ∈
        (wkLookupˢ (multi-store-growth R↠W) αʳ∈)
        L W Vrel)
    where
    grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
    grow = mkWorldʳ-⪰ (multi-store-growth R↠W)
  instCast-bridge-ℰ⊑ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pν = pν} {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₁
          (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ ,
           Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L↠L′ , rel′)) =
    (L↑⊢ , R↑⊢) ,
    inj₁
      (Σʳ′ , Ψʳ′ , wfΣʳ′ , _ , ξ-up R→R′ ,
       Σˡ′ , Ψˡ′ , wfΣˡ′ , _ , up-↠ L↠L′ ,
       instCast-bridge-ℰ⊑ᵢ
         {A = A} {B = B} {n = k} {dir = ≽}
         {w = mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′}
         {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
         {ρ = ρ} {p = p} {pT = pT}
         {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
         Rrel downR
         (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ grow))
         (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ grow))
         (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ grow))
         (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ grow))
         (wkLookupˢ (multi-store-growth L↠L′) αˡ∈)
         (wkLookupˢ (store-growth R→R′) αʳ∈)
         L′ R′ rel′)
    where
    grow : mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′ ⪰ w
    grow = mkWorldˡʳ-⪰ (multi-store-growth L↠L′) (store-growth R→R′)
  
    L↑⊢ = instCast-up-left-typedᵢν
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
      {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢
  
    R↑⊢ = instCast-up-right-typedᵢν
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
      {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢
  instCast-bridge-ℰ⊑ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {pT = pT} {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , L↠blame))) =
    (instCast-up-left-typedᵢν
       {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢ ,
     instCast-up-right-typedᵢν
       {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢) ,
    inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , up-blame-↠ L↠blame))
  instCast-bridge-ℰ⊑ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₂ (inj₂
          (vR , Σˡ′ , Ψˡ′ , wfΣˡ′ , W , L↠W , Vrel))) =
    ℰ-pull-≽-left-↠
      {ρ = extendPlainρ ρ Tˡ Tʳ wfTˡc wfTʳc pT Rrel downR}
      {p = p} {k = suc k} {w = w}
      {Σˡ′ = Σˡ′} {Ψˡ′ = Ψˡ′} {wfΣˡ′ = wfΣˡ′}
      (instCast-up-left-typedᵢν
        {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
        {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢)
      (instCast-up-right-typedᵢν
        {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
        {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢)
      (up-↠ L↠W)
      (instCast-bridge-𝒱⇒ℰ⊑ᵢ
        {A = A} {B = B} {n = k} {dir = ≽}
        {w = mkWorldˡ w Σˡ′ wfΣˡ′}
        {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {ρ = ρ} {p = p} {pT = pT}
        {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
        Rrel downR
        (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ grow))
        hTʳ
        (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ grow))
        hBʳ
        (wkLookupˢ (multi-store-growth L↠W) αˡ∈)
        αʳ∈
        W R Vrel)
    where
    grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
    grow = mkWorldˡ-⪰ (multi-store-growth L↠W)
  instCast-bridge-ℰ⊒ᵢ : InstCastBridgeℰ⊒ᵢ
  instCast-bridge-ℰ⊒ᵢ
      {A = A} {B = B} {n = zero}
      {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {pT = pT} {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) , rel) =
    (instCast-down-left-typedᵢν
       {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {L = L}
       hTˡ hTʳ hAˡ αˡ∈ L⊢ ,
     instCast-down-right-typedᵢν
       {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {R = R}
       hTˡ hTʳ hBʳ αʳ∈ R⊢) ,
    lift tt
  instCast-bridge-ℰ⊒ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₁
          (Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L→L′ ,
           Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R↠R′ , rel′)) =
    (L↓⊢ , R↓⊢) ,
    inj₁
      (Σˡ′ , Ψˡ′ , wfΣˡ′ , _ , ξ-down L→L′ ,
       Σʳ′ , Ψʳ′ , wfΣʳ′ , _ , down-↠ R↠R′ ,
       instCast-bridge-ℰ⊒ᵢ
         {A = A} {B = B} {n = k} {dir = ≼}
         {w = mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′}
         {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
         {ρ = ρ} {p = p} {pT = pT}
         {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
         Rrel downR
         (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ grow))
         (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ grow))
         (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ grow))
         (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ grow))
         (wkLookupˢ (store-growth L→L′) αˡ∈)
         (wkLookupˢ (multi-store-growth R↠R′) αʳ∈)
         L′ R′ rel′)
    where
    grow : mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′ ⪰ w
    grow = mkWorldˡʳ-⪰ (store-growth L→L′) (multi-store-growth R↠R′)
  
    L↓⊢ = instCast-down-left-typedᵢν
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
      {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢
  
    R↓⊢ = instCast-down-right-typedᵢν
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
      {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢
  instCast-bridge-ℰ⊒ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {pT = pT} {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , L↠blame))) =
    (instCast-down-left-typedᵢν
       {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢ ,
     instCast-down-right-typedᵢν
       {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢) ,
    inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , down-blame-↠ L↠blame))
  instCast-bridge-ℰ⊒ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≼} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pν = pν} {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₂ (inj₂
          (vL , Σʳ′ , Ψʳ′ , wfΣʳ′ , W , R↠W , Vrel))) =
    ℰ-pull-≼-right-↠
      {ρ = extendνρ ρ (ηentry αˡ αʳ Rrel downR)}
      {p = pν} {k = suc k} {w = w}
      {Σʳ′ = Σʳ′} {Ψʳ′ = Ψʳ′} {wfΣʳ′ = wfΣʳ′}
      (instCast-down-left-typedᵢν
        {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
        {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢)
      (instCast-down-right-typedᵢν
        {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
        {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢)
      (down-↠ R↠W)
      (instCast-bridge-𝒱⇒ℰ⊒ᵢ
        {A = A} {B = B} {n = k} {dir = ≼}
        {w = mkWorldʳ w Σʳ′ wfΣʳ′}
        {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {ρ = ρ} {p = p} {pT = pT}
        {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
          Rrel downR
          hTˡ
          (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ grow))
          hAˡ
          (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ grow))
          αˡ∈
          (wkLookupˢ (multi-store-growth R↠W) αʳ∈)
          L W Vrel)
      where
      grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
      grow = mkWorldʳ-⪰ (multi-store-growth R↠W)
  instCast-bridge-ℰ⊒ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pν = pν} {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₁
          (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ ,
           Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L↠L′ , rel′)) =
    (L↓⊢ , R↓⊢) ,
    inj₁
      (Σʳ′ , Ψʳ′ , wfΣʳ′ , _ , ξ-down R→R′ ,
       Σˡ′ , Ψˡ′ , wfΣˡ′ , _ , down-↠ L↠L′ ,
       instCast-bridge-ℰ⊒ᵢ
         {A = A} {B = B} {n = k} {dir = ≽}
         {w = mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′}
         {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
         {ρ = ρ} {p = p} {pT = pT}
         {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
         Rrel downR
         (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ grow))
         (WfTy-weakenˢ hTʳ (_⪰_.growΨʳ grow))
         (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ grow))
         (WfTy-weakenˢ hBʳ (_⪰_.growΨʳ grow))
         (wkLookupˢ (multi-store-growth L↠L′) αˡ∈)
         (wkLookupˢ (store-growth R→R′) αʳ∈)
         L′ R′ rel′)
    where
    grow : mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′ ⪰ w
    grow = mkWorldˡʳ-⪰ (multi-store-growth L↠L′) (store-growth R→R′)
  
    L↓⊢ = instCast-down-left-typedᵢν
      {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
      {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢
  
    R↓⊢ = instCast-down-right-typedᵢν
      {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
      {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢
  instCast-bridge-ℰ⊒ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {pT = pT} {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , L↠blame))) =
    (instCast-down-left-typedᵢν
       {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢ ,
     instCast-down-right-typedᵢν
       {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
       {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
       {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢) ,
    inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , down-blame-↠ L↠blame))
  instCast-bridge-ℰ⊒ᵢ
      {A = A} {B = B} {n = suc k} {dir = ≽} {w = w}
      {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
      {ρ = ρ} {p = p} {pν = pν} {pT = pT}
      {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
      Rrel downR hTˡ hTʳ hAˡ hBʳ αˡ∈ αʳ∈ L R
      ((L⊢ , R⊢) ,
        inj₂ (inj₂
          (vR , Σˡ′ , Ψˡ′ , wfΣˡ′ , W , L↠W , Vrel))) =
    ℰ-pull-≽-left-↠
      {ρ = extendνρ ρ (ηentry αˡ αʳ Rrel downR)}
      {p = pν} {k = suc k} {w = w}
      {Σˡ′ = Σˡ′} {Ψˡ′ = Ψˡ′} {wfΣˡ′ = wfΣˡ′}
      (instCast-down-left-typedᵢν
        {A = A} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
        {w = w} {L = L} hTˡ hTʳ hAˡ αˡ∈ L⊢)
      (instCast-down-right-typedᵢν
        {B = B} {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {Rrel = Rrel} {ρ = ρ} {pT = pT} {downR = downR}
        {w = w} {R = R} hTˡ hTʳ hBʳ αʳ∈ R⊢)
      (down-↠ L↠W)
      (instCast-bridge-𝒱⇒ℰ⊒ᵢ
        {A = A} {B = B} {n = k} {dir = ≽}
        {w = mkWorldˡ w Σˡ′ wfΣˡ′}
        {Tˡ = Tˡ} {Tʳ = Tʳ} {αˡ = αˡ} {αʳ = αʳ}
        {ρ = ρ} {p = p} {pT = pT}
        {wfTˡ = wfTˡc} {wfTʳ = wfTʳc}
        Rrel downR
        (WfTy-weakenˢ hTˡ (_⪰_.growΨˡ grow))
        hTʳ
        (WfTy-weakenˢ hAˡ (_⪰_.growΨˡ grow))
        hBʳ
        (wkLookupˢ (multi-store-growth L↠W) αˡ∈)
        αʳ∈
        W R Vrel)
    where
    grow : mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
    grow = mkWorldˡ-⪰ (multi-store-growth L↠W)
  
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

data ResultSameᵢ (Ψ : SealCtx) (Σ : Store) (M : Term) (A : Ty) : Set where
  result-same-value :
    ∀ {W} →
    (Σ ∣ M —↠ Σ ∣ W) →
    Value W →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ W ⦂ A →
    ResultSameᵢ Ψ Σ M A

  result-same-blame :
    ∀ {ℓ} →
    (Σ ∣ M —↠ Σ ∣ blame ℓ) →
    ResultSameᵢ Ψ Σ M A

same-to-resultᵢ :
  ∀ {Ψ Σ M A} →
  StoreWf 0 Ψ Σ →
  ResultSameᵢ Ψ Σ M A →
  Resultᵢ Σ M A
same-to-resultᵢ wfΣ (result-same-value M↠W vW W⊢) =
  result-value wfΣ M↠W vW W⊢
same-to-resultᵢ wfΣ (result-same-blame M↠blame) =
  result-blame M↠blame

prepend-sameᵢ :
  ∀ {Ψ Σ M M′ A} →
  (Σ ∣ M —↠ Σ ∣ M′) →
  ResultSameᵢ Ψ Σ M′ A →
  ResultSameᵢ Ψ Σ M A
prepend-sameᵢ M↠M′ (result-same-value M′↠W vW W⊢) =
  result-same-value (multi-trans M↠M′ M′↠W) vW W⊢
prepend-sameᵢ M↠M′ (result-same-blame M′↠blame) =
  result-same-blame (multi-trans M↠M′ M′↠blame)

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

postulate
  up-unseal-resultᵢ :
    ∀ {Ψ Σ V A α q} →
    StoreWf 0 Ψ Σ →
    Value V →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V up unseal α q) ⦂ A →
    Resultᵢ Σ (V up unseal α q) A

postulate
  down-untag-resultᵢ :
    ∀ {Ψ Σ V G ℓ} →
    StoreWf 0 Ψ Σ →
    Value V →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V down untag G ℓ (id G)) ⦂ G →
    Resultᵢ Σ (V down untag G ℓ (id G)) G

  down-cast-value-result-sameᵢ :
    ∀ {Ψ Σ V B p} →
    StoreWf 0 Ψ Σ →
    Value V →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V down p) ⦂ B →
    ResultSameᵢ Ψ Σ (V down p) B
mutual
  conv↑→up : ∀ {Σ Φ A B} → Σ ∣ Φ ⊢ A ↑ˢ B → Up
  conv↑→up (↑ˢ-unseal {α = α} {A = A} h α∈) = unseal α (id A)
  conv↑→up (↑ˢ-⇒ h↓ h↑) = conv↓→down h↓ ↦ conv↑→up h↑
  conv↑→up (↑ˢ-∀ h↑) = ∀ᵖ (conv↑→up h↑)
  conv↑→up (↑ˢ-id {A = A} wfA) = id A
  conv↑→up (h↑₁ ；↑ˢ h↑₂) = conv↑→up h↑₂

  conv↓→down : ∀ {Σ Φ A B} → Σ ∣ Φ ⊢ A ↓ˢ B → Down
  conv↓→down (↓ˢ-seal {α = α} {A = A} h α∈) = seal (id A) α
  conv↓→down (↓ˢ-⇒ h↑ h↓) = conv↑→up h↑ ↦ conv↓→down h↓
  conv↓→down (↓ˢ-∀ h↓) = ∀ᵖ (conv↓→down h↓)
  conv↓→down (↓ˢ-id {A = A} wfA) = id A
  conv↓→down (h↓₁ ；↓ˢ h↓₂) = conv↓→down h↓₂

conv↑→up-subst-store :
  ∀ {Σ Σ′ Φ A B} →
  (eq : Σ ≡ Σ′) →
  (h↑ : Σ ∣ Φ ⊢ A ↑ˢ B) →
  conv↑→up (subst (λ S → S ∣ Φ ⊢ A ↑ˢ B) eq h↑) ≡ conv↑→up h↑
conv↑→up-subst-store refl h↑ = refl

conv↓→down-subst-store :
  ∀ {Σ Σ′ Φ A B} →
  (eq : Σ ≡ Σ′) →
  (h↓ : Σ ∣ Φ ⊢ A ↓ˢ B) →
  conv↓→down (subst (λ S → S ∣ Φ ⊢ A ↓ˢ B) eq h↓) ≡ conv↓→down h↓
conv↓→down-subst-store refl h↓ = refl

mutual
  conv↑-renameᵗ :
    ∀ {Σ Φ A B} →
    (ρ : Renameᵗ) →
    Σ ∣ Φ ⊢ A ↑ˢ B →
    renameStoreᵗ ρ Σ ∣ Φ ⊢ renameᵗ ρ A ↑ˢ renameᵗ ρ B
  conv↑-renameᵗ ρ (↑ˢ-unseal h α∈) =
    ↑ˢ-unseal (renameLookupᵗ ρ h) α∈
  conv↑-renameᵗ ρ (↑ˢ-⇒ h↓ h↑) =
    ↑ˢ-⇒ (conv↓-renameᵗ ρ h↓) (conv↑-renameᵗ ρ h↑)
  conv↑-renameᵗ {Σ = Σ} ρ (↑ˢ-∀ {A = A} {B = B} h↑) =
    ↑ˢ-∀
      (subst
        (λ S → S ∣ _ ⊢ renameᵗ (extᵗ ρ) A ↑ˢ renameᵗ (extᵗ ρ) B)
        (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
        (conv↑-renameᵗ (extᵗ ρ) h↑))
  conv↑-renameᵗ ρ (↑ˢ-id {A = A} wfA) =
    ↑ˢ-id (wfTySome (renameᵗ ρ A))
  conv↑-renameᵗ ρ (h↑₁ ；↑ˢ h↑₂) =
    conv↑-renameᵗ ρ h↑₁ ；↑ˢ conv↑-renameᵗ ρ h↑₂

  conv↓-renameᵗ :
    ∀ {Σ Φ A B} →
    (ρ : Renameᵗ) →
    Σ ∣ Φ ⊢ A ↓ˢ B →
    renameStoreᵗ ρ Σ ∣ Φ ⊢ renameᵗ ρ A ↓ˢ renameᵗ ρ B
  conv↓-renameᵗ ρ (↓ˢ-seal h α∈) =
    ↓ˢ-seal (renameLookupᵗ ρ h) α∈
  conv↓-renameᵗ ρ (↓ˢ-⇒ h↑ h↓) =
    ↓ˢ-⇒ (conv↑-renameᵗ ρ h↑) (conv↓-renameᵗ ρ h↓)
  conv↓-renameᵗ {Σ = Σ} ρ (↓ˢ-∀ {A = A} {B = B} h↓) =
    ↓ˢ-∀
      (subst
        (λ S → S ∣ _ ⊢ renameᵗ (extᵗ ρ) A ↓ˢ renameᵗ (extᵗ ρ) B)
        (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
        (conv↓-renameᵗ (extᵗ ρ) h↓))
  conv↓-renameᵗ ρ (↓ˢ-id {A = A} wfA) =
    ↓ˢ-id (wfTySome (renameᵗ ρ A))
  conv↓-renameᵗ ρ (h↓₁ ；↓ˢ h↓₂) =
    conv↓-renameᵗ ρ h↓₁ ；↓ˢ conv↓-renameᵗ ρ h↓₂

mutual
  conv↑→up-renameᵗ :
    ∀ {Σ Φ A B} →
    (ρ : Renameᵗ) →
    (h↑ : Σ ∣ Φ ⊢ A ↑ˢ B) →
    conv↑→up (conv↑-renameᵗ ρ h↑) ≡ rename⊑ᵗ ρ (conv↑→up h↑)
  conv↑→up-renameᵗ ρ (↑ˢ-unseal h α∈) = refl
  conv↑→up-renameᵗ ρ (↑ˢ-⇒ h↓ h↑)
      rewrite conv↓→down-renameᵗ ρ h↓
            | conv↑→up-renameᵗ ρ h↑ =
    refl
  conv↑→up-renameᵗ {Σ = Σ} ρ (↑ˢ-∀ {A = A} {B = B} h↑)
      rewrite conv↑→up-subst-store
                (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
                (conv↑-renameᵗ (extᵗ ρ) h↑)
            | conv↑→up-renameᵗ (extᵗ ρ) h↑ =
    refl
  conv↑→up-renameᵗ ρ (↑ˢ-id wfA) = refl
  conv↑→up-renameᵗ ρ (h↑₁ ；↑ˢ h↑₂)
      rewrite conv↑→up-renameᵗ ρ h↑₂ =
    refl

  conv↓→down-renameᵗ :
    ∀ {Σ Φ A B} →
    (ρ : Renameᵗ) →
    (h↓ : Σ ∣ Φ ⊢ A ↓ˢ B) →
    conv↓→down (conv↓-renameᵗ ρ h↓) ≡
    rename⊒ᵗ ρ (conv↓→down h↓)
  conv↓→down-renameᵗ ρ (↓ˢ-seal h α∈) = refl
  conv↓→down-renameᵗ ρ (↓ˢ-⇒ h↑ h↓)
      rewrite conv↑→up-renameᵗ ρ h↑
            | conv↓→down-renameᵗ ρ h↓ =
    refl
  conv↓→down-renameᵗ {Σ = Σ} ρ (↓ˢ-∀ {A = A} {B = B} h↓)
      rewrite conv↓→down-subst-store
                (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
                (conv↓-renameᵗ (extᵗ ρ) h↓)
            | conv↓→down-renameᵗ (extᵗ ρ) h↓ =
    refl
  conv↓→down-renameᵗ ρ (↓ˢ-id wfA) = refl
  conv↓→down-renameᵗ ρ (h↓₁ ；↓ˢ h↓₂)
      rewrite conv↓→down-renameᵗ ρ h↓₂ =
    refl

instSubst↑ˢ-ext :
  ∀ {Δ} {Σ : Store} {Φ : List CastPerm} {σ τ : Substᵗ} →
  ((X : TyVar) → X < Δ → Σ ∣ Φ ⊢ σ X ↑ˢ τ X) →
  (X : TyVar) →
  X < suc Δ →
  ⟰ᵗ Σ ∣ Φ ⊢ extsᵗ σ X ↑ˢ extsᵗ τ X
instSubst↑ˢ-ext h↑ zero z<s = ↑ˢ-id (wfTySome X₀)
instSubst↑ˢ-ext h↑ (suc X) (s<s X<Δ) =
  conv↑-renameᵗ suc (h↑ X X<Δ)

instSubst↓ˢ-ext :
  ∀ {Δ} {Σ : Store} {Φ : List CastPerm} {σ τ : Substᵗ} →
  ((X : TyVar) → X < Δ → Σ ∣ Φ ⊢ τ X ↓ˢ σ X) →
  (X : TyVar) →
  X < suc Δ →
  ⟰ᵗ Σ ∣ Φ ⊢ extsᵗ τ X ↓ˢ extsᵗ σ X
instSubst↓ˢ-ext h↓ zero z<s = ↓ˢ-id (wfTySome X₀)
instSubst↓ˢ-ext h↓ (suc X) (s<s X<Δ) =
  conv↓-renameᵗ suc (h↓ X X<Δ)

mutual
  instSubst↑ˢ :
    ∀ {Δ Ψ Σ Φ} →
    (σ τ : Substᵗ) →
    ((X : TyVar) → X < Δ → Σ ∣ Φ ⊢ σ X ↑ˢ τ X) →
    ((X : TyVar) → X < Δ → Σ ∣ Φ ⊢ τ X ↓ˢ σ X) →
    (A : Ty) →
    WfTy Δ Ψ A →
    Σ ∣ Φ ⊢ substᵗ σ A ↑ˢ substᵗ τ A
  instSubst↑ˢ σ τ h↑ h↓ (＇ X) (wfVar X<Δ) = h↑ X X<Δ
  instSubst↑ˢ σ τ h↑ h↓ (｀ α) (wfSeal α<Ψ) =
    ↑ˢ-id (wfTySome (｀ α))
  instSubst↑ˢ σ τ h↑ h↓ (‵ ι) wfBase = ↑ˢ-id (wfTySome (‵ ι))
  instSubst↑ˢ σ τ h↑ h↓ ★ wf★ = ↑ˢ-id (wfTySome ★)
  instSubst↑ˢ σ τ h↑ h↓ (A ⇒ B) (wf⇒ wfA wfB) =
    ↑ˢ-⇒ (instSubst↓ˢ σ τ h↑ h↓ A wfA)
          (instSubst↑ˢ σ τ h↑ h↓ B wfB)
  instSubst↑ˢ σ τ h↑ h↓ (`∀ A) (wf∀ wfA) =
    ↑ˢ-∀
      (instSubst↑ˢ (extsᵗ σ) (extsᵗ τ)
        (instSubst↑ˢ-ext h↑) (instSubst↓ˢ-ext h↓) A wfA)

  instSubst↓ˢ :
    ∀ {Δ Ψ Σ Φ} →
    (σ τ : Substᵗ) →
    ((X : TyVar) → X < Δ → Σ ∣ Φ ⊢ σ X ↑ˢ τ X) →
    ((X : TyVar) → X < Δ → Σ ∣ Φ ⊢ τ X ↓ˢ σ X) →
    (A : Ty) →
    WfTy Δ Ψ A →
    Σ ∣ Φ ⊢ substᵗ τ A ↓ˢ substᵗ σ A
  instSubst↓ˢ σ τ h↑ h↓ (＇ X) (wfVar X<Δ) = h↓ X X<Δ
  instSubst↓ˢ σ τ h↑ h↓ (｀ α) (wfSeal α<Ψ) =
    ↓ˢ-id (wfTySome (｀ α))
  instSubst↓ˢ σ τ h↑ h↓ (‵ ι) wfBase = ↓ˢ-id (wfTySome (‵ ι))
  instSubst↓ˢ σ τ h↑ h↓ ★ wf★ = ↓ˢ-id (wfTySome ★)
  instSubst↓ˢ σ τ h↑ h↓ (A ⇒ B) (wf⇒ wfA wfB) =
    ↓ˢ-⇒ (instSubst↑ˢ σ τ h↑ h↓ A wfA)
          (instSubst↓ˢ σ τ h↑ h↓ B wfB)
  instSubst↓ˢ σ τ h↑ h↓ (`∀ A) (wf∀ wfA) =
    ↓ˢ-∀
      (instSubst↓ˢ (extsᵗ σ) (extsᵗ τ)
        (instSubst↑ˢ-ext h↑) (instSubst↓ˢ-ext h↓) A wfA)

instCast↑ˢ-var :
  ∀ {Δ Σ Φ A α} →
  Σ ∋ˢ α ⦂ A →
  α ∈conv Φ →
  (X : TyVar) →
  X < suc Δ →
  Σ ∣ Φ ⊢ singleTyEnv (｀ α) X ↑ˢ singleTyEnv A X
instCast↑ˢ-var h α∈ zero z<s = ↑ˢ-unseal h α∈
instCast↑ˢ-var h α∈ (suc X) (s<s X<Δ) =
  ↑ˢ-id (wfTySome (＇ X))

instCast↓ˢ-var :
  ∀ {Δ Σ Φ A α} →
  Σ ∋ˢ α ⦂ A →
  α ∈conv Φ →
  (X : TyVar) →
  X < suc Δ →
  Σ ∣ Φ ⊢ singleTyEnv A X ↓ˢ singleTyEnv (｀ α) X
instCast↓ˢ-var h α∈ zero z<s = ↓ˢ-seal h α∈
instCast↓ˢ-var h α∈ (suc X) (s<s X<Δ) =
  ↓ˢ-id (wfTySome (＇ X))

instCast↑ˢ-var-raw :
  ∀ {Δ Σ Φ A α} →
  (h : Σ ∋ˢ α ⦂ A) →
  (α∈ : α ∈conv Φ) →
  (X : TyVar) →
  (X<Δ : X < suc Δ) →
  conv↑→up (instCast↑ˢ-var h α∈ X X<Δ) ≡ instVar⊑ A α X
instCast↑ˢ-var-raw h α∈ zero z<s = refl
instCast↑ˢ-var-raw h α∈ (suc X) (s<s X<Δ) = refl

instCast↓ˢ-var-raw :
  ∀ {Δ Σ Φ A α} →
  (h : Σ ∋ˢ α ⦂ A) →
  (α∈ : α ∈conv Φ) →
  (X : TyVar) →
  (X<Δ : X < suc Δ) →
  conv↓→down (instCast↓ˢ-var h α∈ X X<Δ) ≡ instVar⊒ A α X
instCast↓ˢ-var-raw h α∈ zero z<s = refl
instCast↓ˢ-var-raw h α∈ (suc X) (s<s X<Δ) = refl

instCast⊑-conv :
  ∀ {Δ Ψ Σ Φ A B α} →
  WfTy Δ Ψ A →
  WfTy (suc Δ) Ψ B →
  Σ ∋ˢ α ⦂ A →
  α ∈conv Φ →
  Σ ∣ Φ ⊢ B [ ｀ α ]ᵗ ↑ˢ B [ A ]ᵗ
instCast⊑-conv {A = A} {B = B} {α = α} wfA wfB h α∈ =
  instSubst↑ˢ (singleTyEnv (｀ α)) (singleTyEnv A)
    (instCast↑ˢ-var h α∈) (instCast↓ˢ-var h α∈) B wfB

instCast⊒-conv :
  ∀ {Δ Ψ Σ Φ A B α} →
  WfTy Δ Ψ A →
  WfTy (suc Δ) Ψ B →
  Σ ∋ˢ α ⦂ A →
  α ∈conv Φ →
  Σ ∣ Φ ⊢ B [ A ]ᵗ ↓ˢ B [ ｀ α ]ᵗ
instCast⊒-conv {A = A} {B = B} {α = α} wfA wfB h α∈ =
  instSubst↓ˢ (singleTyEnv (｀ α)) (singleTyEnv A)
    (instCast↑ˢ-var h α∈) (instCast↓ˢ-var h α∈) B wfB

instSubst↑ˢ-raw-ext :
  ∀ {Δ} {Σ : Store} {Φ : List CastPerm}
    {σ τ : Substᵗ} {var⊑ : (X : TyVar) → Up}
    {h↑ : (X : TyVar) → X < Δ → Σ ∣ Φ ⊢ σ X ↑ˢ τ X} →
  ((X : TyVar) → (X<Δ : X < Δ) → conv↑→up (h↑ X X<Δ) ≡ var⊑ X) →
  (X : TyVar) →
  (X<Δ : X < suc Δ) →
  conv↑→up (instSubst↑ˢ-ext h↑ X X<Δ) ≡ instVarExt⊑ var⊑ X
instSubst↑ˢ-raw-ext raw↑ zero z<s = refl
instSubst↑ˢ-raw-ext {h↑ = h↑} raw↑ (suc X) (s<s X<Δ) =
  trans (conv↑→up-renameᵗ suc (h↑ X X<Δ))
        (cong (rename⊑ᵗ suc) (raw↑ X X<Δ))

instSubst↓ˢ-raw-ext :
  ∀ {Δ} {Σ : Store} {Φ : List CastPerm}
    {σ τ : Substᵗ} {var⊒ : (X : TyVar) → Down}
    {h↓ : (X : TyVar) → X < Δ → Σ ∣ Φ ⊢ τ X ↓ˢ σ X} →
  ((X : TyVar) → (X<Δ : X < Δ) → conv↓→down (h↓ X X<Δ) ≡ var⊒ X) →
  (X : TyVar) →
  (X<Δ : X < suc Δ) →
  conv↓→down (instSubst↓ˢ-ext h↓ X X<Δ) ≡
  instVarExt⊒ var⊒ X
instSubst↓ˢ-raw-ext raw↓ zero z<s = refl
instSubst↓ˢ-raw-ext {h↓ = h↓} raw↓ (suc X) (s<s X<Δ) =
  trans (conv↓→down-renameᵗ suc (h↓ X X<Δ))
        (cong (rename⊒ᵗ suc) (raw↓ X X<Δ))

mutual
  instSubst↑ˢ-raw :
    ∀ {Δ Ψ Σ Φ} →
    (σ τ : Substᵗ) →
    (var⊑ : (X : TyVar) → Up) →
    (var⊒ : (X : TyVar) → Down) →
    (h↑ : (X : TyVar) → X < Δ → Σ ∣ Φ ⊢ σ X ↑ˢ τ X) →
    (h↓ : (X : TyVar) → X < Δ → Σ ∣ Φ ⊢ τ X ↓ˢ σ X) →
    ((X : TyVar) → (X<Δ : X < Δ) → conv↑→up (h↑ X X<Δ) ≡ var⊑ X) →
    ((X : TyVar) → (X<Δ : X < Δ) → conv↓→down (h↓ X X<Δ) ≡ var⊒ X) →
    (A : Ty) →
    (wfA : WfTy Δ Ψ A) →
    conv↑→up (instSubst↑ˢ σ τ h↑ h↓ A wfA) ≡
    substᵗ-up var⊑ var⊒ A
  instSubst↑ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ (＇ X)
      (wfVar X<Δ) =
    raw↑ X X<Δ
  instSubst↑ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ (｀ α)
      (wfSeal α<Ψ) =
    refl
  instSubst↑ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ (‵ ι) wfBase =
    refl
  instSubst↑ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ ★ wf★ =
    refl
  instSubst↑ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ (A ⇒ B)
      (wf⇒ wfA wfB)
      rewrite instSubst↓ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ A wfA
            | instSubst↑ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ B wfB =
    refl
  instSubst↑ˢ-raw {Δ = Δ} {Σ = Σ} σ τ var⊑ var⊒ h↑ h↓ raw↑
      raw↓ (`∀ A) (wf∀ wfA)
      rewrite instSubst↑ˢ-raw
                (extsᵗ σ)
                (extsᵗ τ)
                (instVarExt⊑ var⊑)
                (instVarExt⊒ var⊒)
                (instSubst↑ˢ-ext h↑)
                (instSubst↓ˢ-ext h↓)
                (instSubst↑ˢ-raw-ext raw↑)
                (instSubst↓ˢ-raw-ext raw↓)
                A wfA =
    refl

  instSubst↓ˢ-raw :
    ∀ {Δ Ψ Σ Φ} →
    (σ τ : Substᵗ) →
    (var⊑ : (X : TyVar) → Up) →
    (var⊒ : (X : TyVar) → Down) →
    (h↑ : (X : TyVar) → X < Δ → Σ ∣ Φ ⊢ σ X ↑ˢ τ X) →
    (h↓ : (X : TyVar) → X < Δ → Σ ∣ Φ ⊢ τ X ↓ˢ σ X) →
    ((X : TyVar) → (X<Δ : X < Δ) → conv↑→up (h↑ X X<Δ) ≡ var⊑ X) →
    ((X : TyVar) → (X<Δ : X < Δ) → conv↓→down (h↓ X X<Δ) ≡ var⊒ X) →
    (A : Ty) →
    (wfA : WfTy Δ Ψ A) →
    conv↓→down (instSubst↓ˢ σ τ h↑ h↓ A wfA) ≡
    substᵗ-down var⊑ var⊒ A
  instSubst↓ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ (＇ X)
      (wfVar X<Δ) =
    raw↓ X X<Δ
  instSubst↓ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ (｀ α)
      (wfSeal α<Ψ) =
    refl
  instSubst↓ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ (‵ ι) wfBase =
    refl
  instSubst↓ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ ★ wf★ =
    refl
  instSubst↓ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ (A ⇒ B)
      (wf⇒ wfA wfB)
      rewrite instSubst↑ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ A wfA
            | instSubst↓ˢ-raw σ τ var⊑ var⊒ h↑ h↓ raw↑ raw↓ B wfB =
    refl
  instSubst↓ˢ-raw {Δ = Δ} {Σ = Σ} σ τ var⊑ var⊒ h↑ h↓ raw↑
      raw↓ (`∀ A) (wf∀ wfA)
      rewrite instSubst↓ˢ-raw
                (extsᵗ σ)
                (extsᵗ τ)
                (instVarExt⊑ var⊑)
                (instVarExt⊒ var⊒)
                (instSubst↑ˢ-ext h↑)
                (instSubst↓ˢ-ext h↓)
                (instSubst↑ˢ-raw-ext raw↑)
                (instSubst↓ˢ-raw-ext raw↓)
                A wfA =
    refl

instCast⊑-conv-raw :
  ∀ {Δ Ψ Σ Φ A B α} →
  (wfA : WfTy Δ Ψ A) →
  (wfB : WfTy (suc Δ) Ψ B) →
  (h : Σ ∋ˢ α ⦂ A) →
  (α∈ : α ∈conv Φ) →
  conv↑→up (instCast⊑-conv wfA wfB h α∈) ≡
  instCast⊑ {A = A} {B = B} {α = α}
instCast⊑-conv-raw {A = A} {B = B} {α = α} wfA wfB h α∈ =
  instSubst↑ˢ-raw (singleTyEnv (｀ α)) (singleTyEnv A)
    (instVar⊑ A α) (instVar⊒ A α)
    (instCast↑ˢ-var h α∈)
    (instCast↓ˢ-var h α∈)
    (instCast↑ˢ-var-raw h α∈)
    (instCast↓ˢ-var-raw h α∈)
    B wfB

instCast⊒-conv-raw :
  ∀ {Δ Ψ Σ Φ A B α} →
  (wfA : WfTy Δ Ψ A) →
  (wfB : WfTy (suc Δ) Ψ B) →
  (h : Σ ∋ˢ α ⦂ A) →
  (α∈ : α ∈conv Φ) →
  conv↓→down (instCast⊒-conv wfA wfB h α∈) ≡
  instCast⊒ {A = A} {B = B} {α = α}
instCast⊒-conv-raw {A = A} {B = B} {α = α} wfA wfB h α∈ =
  instSubst↓ˢ-raw (singleTyEnv (｀ α)) (singleTyEnv A)
    (instVar⊑ A α) (instVar⊒ A α)
    (instCast↑ˢ-var h α∈)
    (instCast↓ˢ-var h α∈)
    (instCast↑ˢ-var-raw h α∈)
    (instCast↓ˢ-var-raw h α∈)
    B wfB

postulate
  conv-up-value-result-sameᵢ :
    ∀ {Ψ Σ Φ V A B C}
      (h↑ : Σ ∣ Φ ⊢ A ↑ˢ B) →
    StoreWf 0 Ψ Σ →
    Value V →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V up conv↑→up h↑) ⦂ C →
    ResultSameᵢ Ψ Σ (V up conv↑→up h↑) C

  conv-down-value-result-sameᵢ :
    ∀ {Ψ Σ Φ V A B C}
      (h↓ : Σ ∣ Φ ⊢ A ↓ˢ B) →
    StoreWf 0 Ψ Σ →
    Value V →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V down conv↓→down h↓) ⦂ C →
    ResultSameᵢ Ψ Σ (V down conv↓→down h↓) C

conv-up-value-resultᵢ :
  ∀ {Ψ Σ Φ V A B C}
    (h↑ : Σ ∣ Φ ⊢ A ↑ˢ B) →
  StoreWf 0 Ψ Σ →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V up conv↑→up h↑) ⦂ C →
  Resultᵢ Σ (V up conv↑→up h↑) C
conv-up-value-resultᵢ h↑ wfΣ vV outer⊢ =
  same-to-resultᵢ wfΣ (conv-up-value-result-sameᵢ h↑ wfΣ vV outer⊢)

conv-down-value-resultᵢ :
  ∀ {Ψ Σ Φ V A B C}
    (h↓ : Σ ∣ Φ ⊢ A ↓ˢ B) →
  StoreWf 0 Ψ Σ →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ (V down conv↓→down h↓) ⦂ C →
  Resultᵢ Σ (V down conv↓→down h↓) C
conv-down-value-resultᵢ h↓ wfΣ vV outer⊢ =
  same-to-resultᵢ wfΣ (conv-down-value-result-sameᵢ h↓ wfΣ vV outer⊢)

instCast⊑-conv-value-resultᵢ :
  ∀ {Δ Ψ Σ V A B α C} →
  WfTy Δ Ψ A →
  WfTy (suc Δ) Ψ B →
  Σ ∋ˢ α ⦂ A →
  α ∈conv every Ψ →
  StoreWf 0 Ψ Σ →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢
    (V up instCast⊑ {A = A} {B = B} {α = α}) ⦂ C →
  Resultᵢ Σ (V up instCast⊑ {A = A} {B = B} {α = α}) C
instCast⊑-conv-value-resultᵢ {A = A} {B = B} {α = α}
    wfA wfB h α∈ wfΣ vV outer⊢
    rewrite sym (instCast⊑-conv-raw wfA wfB h α∈) =
  conv-up-value-resultᵢ (instCast⊑-conv wfA wfB h α∈) wfΣ vV outer⊢

instCast⊒-conv-value-resultᵢ :
  ∀ {Δ Ψ Σ V A B α C} →
  WfTy Δ Ψ A →
  WfTy (suc Δ) Ψ B →
  Σ ∋ˢ α ⦂ A →
  α ∈conv every Ψ →
  StoreWf 0 Ψ Σ →
  Value V →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢
    (V down instCast⊒ {A = A} {B = B} {α = α}) ⦂ C →
  Resultᵢ Σ (V down instCast⊒ {A = A} {B = B} {α = α}) C
instCast⊒-conv-value-resultᵢ {A = A} {B = B} {α = α}
    wfA wfB h α∈ wfΣ vV outer⊢
    rewrite sym (instCast⊒-conv-raw wfA wfB h α∈) =
  conv-down-value-resultᵢ (instCast⊒-conv wfA wfB h α∈) wfΣ vV outer⊢

postulate
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

postulate
  instCast⊑-value-resultᵢ :
    ∀ {A B α Ψ Σ V C} →
    StoreWf 0 Ψ Σ →
    Value V →
    0 ∣ Ψ ∣ Σ ∣ [] ⊢
      (V up instCast⊑ {A = A} {B = B} {α = α}) ⦂ C →
    Resultᵢ Σ (V up instCast⊑ {A = A} {B = B} {α = α}) C

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

upν-fresh-wfΣᵢ :
  ∀ {Ψ Σ} →
  StoreWf 0 Ψ Σ →
  StoreWf 0 (suc Ψ) ((length Σ , ★) ∷ Σ)
upν-fresh-wfΣᵢ = storeWf-fresh-extᴿ wf★

upν-fresh-worldᵢ :
  ∀ {Ψ Σ} →
  StoreWf 0 Ψ Σ →
  World
upν-fresh-worldᵢ {Ψ = Ψ} {Σ = Σ} wfΣ =
  mkWorld (suc Ψ) Ψ ((length Σ , ★) ∷ Σ) Σ
    (upν-fresh-wfΣᵢ wfΣ) wfΣ []

tyapp-fresh-wfΣᵢ :
  ∀ {T w} →
  WfTy 0 (Ψˡ w) T →
  StoreWf 0 (suc (Ψˡ w)) ((length (Σˡ w) , T) ∷ Σˡ w)
tyapp-fresh-wfΣᵢ {w = w} hT = storeWf-fresh-extᴿ hT (wfΣˡ w)

tyapp-not-valueᵢ : ∀ {V B T} → Value (V ⦂∀ B [ T ]) → ⊥
tyapp-not-valueᵢ ()

ℰbodyᵢ-≼-nonvalue :
  ∀ {Ξ A B k w M N} {ρ : RelSub Ξ} {p : Ξ ⊢ A ⊑ᵢ B} →
  (Value M → ⊥) →
  ℰbody ρ p (suc k) ≼ w M N →
  (Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ]
    Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ] Σ[ Mˡ′ ∈ Term ]
    (Σˡ w ∣ M —→ Σˡ′ ∣ Mˡ′) ×
    Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ]
    Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ] Σ[ N′ ∈ Term ]
    (Σʳ w ∣ N —↠ Σʳ′ ∣ N′) ×
    ℰ ρ p k ≼ (mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′) Mˡ′ N′)
  ⊎
  (Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ]
    Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ] Σ[ ℓ ∈ Label ]
    (Σˡ w ∣ M —↠ Σˡ′ ∣ blame ℓ))
ℰbodyᵢ-≼-nonvalue not-value (inj₁ step) = inj₁ step
ℰbodyᵢ-≼-nonvalue not-value (inj₂ (inj₁ bl)) = inj₂ bl
ℰbodyᵢ-≼-nonvalue not-value (inj₂ (inj₂ (vM , rest))) =
  ⊥-elim (not-value vM)

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

  ν-fresh-current-ℰᵢ-core :
    ∀ {Ξ A B T k dir w V W R} {ρ : RelSub Ξ}
      {pSelf : Ξ ⊢ T ⊑ᵢ T}
      {pν : (ν-bound ∷ Ξ) ⊢ A ⊑ᵢ ⇑ᵗ B}
      {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B} →
    (inst : νClosedInstᵢ pν pT) →
    (sem : SemanticRelAtᵢ ρ pSelf w R) →
    (hTˡ : WfTy 0 (Ψˡ w) (leftᵢ ρ w T)) →
    (hTʳ : WfTy 0 (Ψʳ w) (rightᵢ ρ w T)) →
    Value V →
    Value W →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ leftᵢ ρ w (`∀ A) →
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w B →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂
      leftᵢ ρ w (A [ T ]ᵗ) →
    ℰ (extendνρ ρ
        (ηentry (length (Σˡ w)) (length (Σʳ w))
          R (semantic-downᵢ sem)))
      pν k dir
      (extendWorldν w R (semantic-downᵢ sem)
        (leftᵢ ρ w T) (rightᵢ ρ w T) hTˡ hTʳ)
      (V ⦂∀ left∀ᵢ ρ w A [ ｀ length (Σˡ w) ])
      W →
    ℰ ρ pT (suc k) dir w
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ])
      W

ν-fresh-current-ℰᵢ :
  ∀ {Ξ Δ Ψsrc A B T k dir w V W} {ρ : RelSub Ξ}
    {pν : (ν-bound ∷ Ξ) ⊢ A ⊑ᵢ ⇑ᵗ B}
    {occ : occurs zero A ≡ true}
    {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  νClosedInstᵢ pν pT →
  RelWf w ρ →
  InterpLRWfˡ (plain ∷ Ξ) (suc Δ) Ψsrc (Ψˡ w) (νenv ρ) →
  InterpLRWfˡ Ξ Δ Ψsrc (Ψˡ w) (νenv ρ) →
  WfTy (suc Δ) Ψsrc A →
  WfTy 0 Ψsrc T →
  Ψsrc ≤ Ψʳ w →
  𝒱 ρ (⊑ᵢ-ν A B occ pν) k dir w V W →
  ℰ ρ pT (suc k) dir w
    (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ])
    W
ν-fresh-current-ℰᵢ {Ξ = Ξ} {Δ = Δ} {Ψsrc = Ψsrc}
    {A = A} {B = B} {T = T} {k = zero} {dir = ≼}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν} {pT = pT}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    (lift (vV , vW , (V⊢ , W⊢))) =
  ν-fresh-current-ℰᵢ-core {k = zero} {dir = ≼} {R = R}
    inst sem hTˡ hTʳ vV vW V⊢ W⊢ leftApp⊢ fresh
  where
  kit : SemanticRelKitᵢ ρ (closed-reflᵢ wfT) w
  kit = semanticRelAtᵢ ρ (closed-reflᵢ wfT) w

  R : Rel
  R = relᵢ kit

  sem : SemanticRelAtᵢ ρ (closed-reflᵢ wfT) w R
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
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂
      leftᵢ ρ w (A [ T ]ᵗ)
  leftApp⊢ = tyappν-left-typedᵢ rwf iwfA iwfT wfA wfTΔ V⊢

  wfresh : World
  wfresh =
    extendWorldν w R (semantic-downᵢ sem)
      (leftᵢ ρ w T) (rightᵢ ρ w T) hTˡ hTʳ

  e : SealRel
  e = ηentry (length (Σˡ w)) (length (Σʳ w))
        R (semantic-downᵢ sem)

  freshLeftApp⊢ :
    0 ∣ Ψˡ wfresh ∣ Σˡ wfresh ∣ [] ⊢
      (V ⦂∀ left∀ᵢ ρ w A [ ｀ length (Σˡ w) ]) ⦂
      leftᵢ (extendνρ ρ e) wfresh A
  freshLeftApp⊢ =
    cong-⊢⦂ refl refl refl
      (sym
        (extendνρ-left-openᵢ {A = A}
          {αˡ = length (Σˡ w)} {αʳ = length (Σʳ w)}
          ρ wfresh))
      (⊢•
        (wkΣ-term (drop ⊆ˢ-refl) (wkΨ-term-suc V⊢))
        (WfTy-weakenˢ
          (left∀ᵢ-wf {w = w} ρ iwfA wfA (leftᵗ-wf rwf))
          (n≤1+n _))
        (wfSeal (len<suc-StoreWf (wfΣˡ w))))

  freshW⊢ :
    0 ∣ Ψʳ wfresh ∣ Σʳ wfresh ∣ [] ⊢ W ⦂
      rightᵢ (extendνρ ρ e) wfresh (⇑ᵗ B)
  freshW⊢ =
    cong-⊢⦂ refl refl refl
      (sym
        (extendνρ-right-shiftᵢ {A = B}
          {αˡ = length (Σˡ w)} {αʳ = length (Σʳ w)}
          ρ wfresh))
      (wkΣ-term (drop ⊆ˢ-refl) (wkΨ-term-suc W⊢))

  fresh :
    ℰ (extendνρ ρ e) pν zero ≼ wfresh
      (V ⦂∀ left∀ᵢ ρ w A [ ｀ length (Σˡ w) ])
      W
  fresh = (freshLeftApp⊢ , freshW⊢) , lift tt
ν-fresh-current-ℰᵢ {Ξ = Ξ} {Δ = Δ} {Ψsrc = Ψsrc}
    {A = A} {B = B} {T = T} {k = zero} {dir = ≽}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν} {pT = pT}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    (lift (vV , vW , (V⊢ , W⊢))) =
  ν-fresh-current-ℰᵢ-core {k = zero} {dir = ≽} {R = R}
    inst sem hTˡ hTʳ vV vW V⊢ W⊢ leftApp⊢ fresh
  where
  kit : SemanticRelKitᵢ ρ (closed-reflᵢ wfT) w
  kit = semanticRelAtᵢ ρ (closed-reflᵢ wfT) w

  R : Rel
  R = relᵢ kit

  sem : SemanticRelAtᵢ ρ (closed-reflᵢ wfT) w R
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
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂
      leftᵢ ρ w (A [ T ]ᵗ)
  leftApp⊢ = tyappν-left-typedᵢ rwf iwfA iwfT wfA wfTΔ V⊢

  wfresh : World
  wfresh =
    extendWorldν w R (semantic-downᵢ sem)
      (leftᵢ ρ w T) (rightᵢ ρ w T) hTˡ hTʳ

  e : SealRel
  e = ηentry (length (Σˡ w)) (length (Σʳ w))
        R (semantic-downᵢ sem)

  freshLeftApp⊢ :
    0 ∣ Ψˡ wfresh ∣ Σˡ wfresh ∣ [] ⊢
      (V ⦂∀ left∀ᵢ ρ w A [ ｀ length (Σˡ w) ]) ⦂
      leftᵢ (extendνρ ρ e) wfresh A
  freshLeftApp⊢ =
    cong-⊢⦂ refl refl refl
      (sym
        (extendνρ-left-openᵢ {A = A}
          {αˡ = length (Σˡ w)} {αʳ = length (Σʳ w)}
          ρ wfresh))
      (⊢•
        (wkΣ-term (drop ⊆ˢ-refl) (wkΨ-term-suc V⊢))
        (WfTy-weakenˢ
          (left∀ᵢ-wf {w = w} ρ iwfA wfA (leftᵗ-wf rwf))
          (n≤1+n _))
        (wfSeal (len<suc-StoreWf (wfΣˡ w))))

  freshW⊢ :
    0 ∣ Ψʳ wfresh ∣ Σʳ wfresh ∣ [] ⊢ W ⦂
      rightᵢ (extendνρ ρ e) wfresh (⇑ᵗ B)
  freshW⊢ =
    cong-⊢⦂ refl refl refl
      (sym
        (extendνρ-right-shiftᵢ {A = B}
          {αˡ = length (Σˡ w)} {αʳ = length (Σʳ w)}
          ρ wfresh))
      (wkΣ-term (drop ⊆ˢ-refl) (wkΨ-term-suc W⊢))

  fresh :
    ℰ (extendνρ ρ e) pν zero ≽ wfresh
      (V ⦂∀ left∀ᵢ ρ w A [ ｀ length (Σˡ w) ])
      W
  fresh = (freshLeftApp⊢ , freshW⊢) , lift tt
ν-fresh-current-ℰᵢ {Ξ = Ξ} {Δ = Δ} {Ψsrc = Ψsrc}
    {A = A} {B = B} {T = T} {k = suc k} {dir = dir}
    {w = w} {V = V} {W = W} {ρ = ρ} {pν = pν} {pT = pT}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((vV , vW , (V⊢ , W⊢)) , payload) =
  ν-fresh-current-ℰᵢ-core {R = R}
    inst sem hTˡ hTʳ vV vW V⊢ W⊢ leftApp⊢ fresh
  where
  kit : SemanticRelKitᵢ ρ (closed-reflᵢ wfT) w
  kit = semanticRelAtᵢ ρ (closed-reflᵢ wfT) w

  R : Rel
  R = relᵢ kit

  sem : SemanticRelAtᵢ ρ (closed-reflᵢ wfT) w R
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
      (V ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂
      leftᵢ ρ w (A [ T ]ᵗ)
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
    {occ : occurs zero A ≡ true}
    {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  νClosedInstᵢ pν pT →
  RelWf w ρ →
  InterpLRWfˡ (plain ∷ Ξ) (suc Δ) Ψsrc (Ψˡ w) (νenv ρ) →
  InterpLRWfˡ Ξ Δ Ψsrc (Ψˡ w) (νenv ρ) →
  WfTy (suc Δ) Ψsrc A →
  WfTy 0 Ψsrc T →
  Ψsrc ≤ Ψʳ w →
  ℰ ρ (⊑ᵢ-ν A B occ pν) n dir w L R →
  ℰ ρ pT n dir w (L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) R
tyappν-ℰᵢ {Ξ} {Δ} {Ψsrc} {A} {B} {T} {zero} {dir}
    {w} {L} {R} {ρ} inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) , rel) =
  (tyappν-left-typedᵢ rwf iwfA iwfT wfA
     (WfTy-weakenᵗ wfT z≤n) L⊢ ,
   R⊢) ,
  lift tt
tyappν-ℰᵢ {A = A} {T = T} {n = suc k} {dir = ≼}
    {w = w} {L = L} {R = R} {ρ = ρ} {occ = occ}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) ,
      inj₁
        (Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L→L′ ,
         Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R↠R′ , rel′)) =
  (L•⊢ , R⊢) ,
  inj₁
    (Σˡ′ , Ψˡ′ , wfΣˡ′ ,
      (L′ ⦂∀ left∀ᵢ ρ wstep A [ leftᵢ ρ wstep T ]) ,
      ξ-·α L→L′ ,
      Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R↠R′ ,
      tyappν-ℰᵢ
        {occ = occ}
        inst
        (RelWf-⪰ step-grow rwf)
        (InterpLRWfˡ-weakenˢ (_⪰_.growΨˡ step-grow) iwfA)
        (InterpLRWfˡ-weakenˢ (_⪰_.growΨˡ step-grow) iwfT)
        wfA
        wfT
        (≤-trans Ψsrc≤ʳ (_⪰_.growΨʳ step-grow))
        rel′)
  where
  wstep : World
  wstep = mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′

  step-grow : mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′ ⪰ w
  step-grow = mkWorldˡʳ-⪰ (store-growth L→L′) (multi-store-growth R↠R′)

  L•⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂
      leftᵢ ρ w (A [ T ]ᵗ)
  L•⊢ = tyappν-left-typedᵢ rwf iwfA iwfT wfA
            (WfTy-weakenᵗ wfT z≤n) L⊢
tyappν-ℰᵢ {A = A} {T = T} {n = suc k} {dir = ≼}
    {w = w} {L = L} {R = R} {ρ = ρ} {occ = occ}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , L↠blame))) =
  (tyappν-left-typedᵢ rwf iwfA iwfT wfA
     (WfTy-weakenᵗ wfT z≤n) L⊢ ,
   R⊢) ,
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , tyapp-blame-↠ L↠blame))
tyappν-ℰᵢ {Δ = Δ} {Ψsrc = Ψsrc} {A = A} {B = B} {T = T}
    {n = suc k} {dir = ≼} {w = w} {L = L} {R = R} {ρ = ρ}
    {pν = pν} {occ = occ} {pT = pT}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) ,
      inj₂ (inj₂
        (vL , Σʳ′ , Ψʳ′ , wfΣʳ′ , W , R↠W , Vrel))) =
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
    (ν-fresh-current-ℰᵢ
      {Δ = Δ} {Ψsrc = Ψsrc} {A = A} {B = B} {T = T}
      {k = k} {dir = ≼}
      {w = mkWorldʳ w Σʳ′ wfΣʳ′} {V = L} {W = W}
      {ρ = ρ} {pν = pν} {occ = occ} {pT = pT}
      inst
      (RelWf-⪰ grow rwf)
      (InterpLRWfˡ-weakenˢ (_⪰_.growΨˡ grow) iwfA)
      (InterpLRWfˡ-weakenˢ (_⪰_.growΨˡ grow) iwfT)
      wfA
      wfT
      (≤-trans Ψsrc≤ʳ (_⪰_.growΨʳ grow))
      Vrel)
  where
  grow : mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
  grow = mkWorldʳ-⪰ (multi-store-growth R↠W)
tyappν-ℰᵢ {A = A} {T = T} {n = suc k} {dir = ≽}
    {w = w} {L = L} {R = R} {ρ = ρ} {occ = occ}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) ,
      inj₁
        (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ ,
         Σˡ′ , Ψˡ′ , wfΣˡ′ , L′ , L↠L′ , rel′)) =
  (L•⊢ , R⊢) ,
  inj₁
    (Σʳ′ , Ψʳ′ , wfΣʳ′ , R′ , R→R′ ,
      Σˡ′ , Ψˡ′ , wfΣˡ′ ,
      (L′ ⦂∀ left∀ᵢ ρ wstep A [ leftᵢ ρ wstep T ]) ,
      tyapp-↠ L↠L′ ,
      tyappν-ℰᵢ
        {occ = occ}
        inst
        (RelWf-⪰ step-grow rwf)
        (InterpLRWfˡ-weakenˢ (_⪰_.growΨˡ step-grow) iwfA)
        (InterpLRWfˡ-weakenˢ (_⪰_.growΨˡ step-grow) iwfT)
        wfA
        wfT
        (≤-trans Ψsrc≤ʳ (_⪰_.growΨʳ step-grow))
        rel′)
  where
  wstep : World
  wstep = mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′

  step-grow : mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′ ⪰ w
  step-grow = mkWorldˡʳ-⪰ (multi-store-growth L↠L′) (store-growth R→R′)

  L•⊢ :
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢
      (L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) ⦂
      leftᵢ ρ w (A [ T ]ᵗ)
  L•⊢ = tyappν-left-typedᵢ rwf iwfA iwfT wfA
            (WfTy-weakenᵗ wfT z≤n) L⊢
tyappν-ℰᵢ {A = A} {T = T} {n = suc k} {dir = ≽}
    {w = w} {L = L} {R = R} {ρ = ρ} {occ = occ}
    inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ
    ((L⊢ , R⊢) , inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , L↠blame))) =
  (tyappν-left-typedᵢ rwf iwfA iwfT wfA
     (WfTy-weakenᵗ wfT z≤n) L⊢ ,
   R⊢) ,
  inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , tyapp-blame-↠ L↠blame))
tyappν-ℰᵢ {Δ = Δ} {Ψsrc = Ψsrc} {A = A} {B = B} {T = T}
    {n = suc k} {dir = ≽} {w = w} {L = L} {R = R} {ρ = ρ}
    {pν = pν} {occ = occ} {pT = pT}
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
    (ν-fresh-current-ℰᵢ
      {Δ = Δ} {Ψsrc = Ψsrc} {A = A} {B = B} {T = T}
      {k = k} {dir = ≽}
      {w = mkWorldˡ w Σˡ′ wfΣˡ′} {V = W} {W = R}
      {ρ = ρ} {pν = pν} {occ = occ} {pT = pT}
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
    {occ : occurs zero A ≡ true}
    {pT : Ξ ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  νClosedInstᵢ pν pT →
  RelWf w ρ →
  InterpLRWfˡ (plain ∷ Ξ) (suc Δ) Ψsrc (Ψˡ w) (νenv ρ) →
  InterpLRWfˡ Ξ Δ Ψsrc (Ψˡ w) (νenv ρ) →
  WfTy (suc Δ) Ψsrc A →
  WfTy 0 Ψsrc T →
  Ψsrc ≤ Ψʳ w →
  ℰ ρ (⊑ᵢ-ν A B occ pν) (suc n) dir w L R →
  ℰ ρ pT (suc n) dir w
    (L ⦂∀ left∀ᵢ ρ w A [ leftᵢ ρ w T ]) R
tyappν-ℰᵢ-suc {occ = occ} inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ rel =
  tyappν-ℰᵢ {occ = occ} inst rwf iwfA iwfT wfA wfT Ψsrc≤ʳ rel

compat-⦂∀-ν :
  ∀ (A B : Ty) {E dir M M′ T}
    (pν : (ν-bound ∷ TPEnv.Ξ E) ⊢ A ⊑ᵢ ⇑ᵗ B)
    {occ : occurs zero A ≡ true}
    {pT : TPEnv.Ξ E ⊢ A [ T ]ᵗ ⊑ᵢ B} →
  E ∣ dir ⊨ M ⊑ M′ ⦂ (⊑ᵢ-ν A B occ pν) →
  WfTy (suc (TPEnv.Δ E)) (TPEnv.Ψ E) A →
  (hT : WfTy 0 (TPEnv.Ψ E) T) →
  νClosedInstᵢ pν pT →
  E ∣ dir ⊨ (M ⦂∀ A [ T ]) ⊑ M′ ⦂ pT
compat-⦂∀-ν A B {E = E} {dir = dir} {M = M} {M′ = M′} {T = T}
    pν {occ = occ} M-rel wfA hT inst n w ρ γ rwf env
    rewrite ν-inst-eqᵢ inst =
  tyappν-ℰᵢ
    {Ξ = TPEnv.Ξ E}
    {Δ = TPEnv.Δ E} {Ψsrc = TPEnv.Ψ E}
    {A = A} {B = B} {T = T} {n = n} {dir = dir} {w = w}
    {L = closeLRˡᵐ ρ w (substˣ-term (leftˣ γ) M)}
    {R = closeLRʳᵐ ρ w (substˣ-term (rightˣ γ) M′)}
    {ρ = ρ} {pν = pν} {occ = occ}
    {pT = ν-close-inst⊑ᵢ (ν-inst-wfTᵢ inst) pν}
    (ν-close-inst-evidenceᵢ (ν-inst-wfTᵢ inst) pν)
    (relWf rwf)
    (InterpLRWfˡ-plain (interpLRWfˡ rwf))
    (interpLRWfˡ rwf)
    wfA
    hT
    (Ψʳ≤ rwf)
    (M-rel n w ρ γ rwf env)
