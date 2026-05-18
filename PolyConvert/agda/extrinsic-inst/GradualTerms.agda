{-# OPTIONS --allow-unsolved-metas #-}
module GradualTerms where

-- File Charter:
--   * Extrinsic term syntax and typing judgment for Gradually Typed System F (GTSF).

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; zero; suc; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective; m<n⇒m<1+n)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision
  using
    ( plains
    ; ICtx
    ; plain
    ; ν-bound
    ; _∋_∶_
    ; _∣_⊢_⦂_⊑_
    ; _∣_⊢_⦂_⊒_
    ; Imp
    ; ★⊑★
    ; X⊑★
    ; A⊑★
    ; X⊑X
    ; α⊑α
    ; reflImp
    ; renameImp
    ; substImp
    ; ι⊑ι
    ; A⇒B⊑A′⇒B′
    ; `∀A⊑∀B
    ; `∀A⊑B
    ; ⊑-★★
    ; ⊑-★ν
    ; ⊑-★
    ; ⊑-＇
    ; ⊑-｀
    ; ⊑-⇒
    ; ⊑-∀
    ; ⊑-ν
    ; ⊑-‵
    ; ⊑-src-wf
    ; ⊑-tgt-wf
    )
open import Consistency
open import Terms using (Const; Prim; constTy; κℕ; constTy-renameᵗ; constTy-⇑ᵗ)
open import Terms
  using (Term)
  renaming
    ( `_ to `ᵀ_
    ; ƛ_⇒_ to ƛᵀ_⇒_
    ; _·_ to _·ᵀ_
    ; Λ_ to Λᵀ_
    ; _⦂∀_[_] to _⦂∀ᵀ_[_]
    ; $ to $ᵀ
    ; _⊕[_]_ to _⊕ᵀ[_]_
    ; _⇑_ to _⇑ᵀ_
    ; _⇓_ to _⇓ᵀ_
    ; blame to blameᵀ
    ; Value to Valueᵀ
    ; _∣_∣_∣_⊢_⦂_ to _∣_∣_∣_⊢ᵀ_⦂_
    ; ⊢` to ⊢ᵀ`
    ; ⊢ƛ to ⊢ᵀƛ
    ; ⊢· to ⊢ᵀ·
    ; ⊢Λ to ⊢ᵀΛ
    ; ⊢• to ⊢ᵀ•
    ; ⊢$ to ⊢ᵀ$
    ; ⊢⊕ to ⊢ᵀ⊕
    ; ⊢up to ⊢ᵀup
    ; ⊢down to ⊢ᵀdown
    ; ⊢blame to ⊢ᵀblame
    )
open import proof.ConsistencyCoerce using (coerce-wt; coerce-wt-plains)
open import proof.ConsistencyProperties using (cong-~)
open import proof.ImprecisionCompose using (⊑-trans)
open import proof.TypeProperties using (renameᵗ-ground-id)
open import proof.ImprecisionProperties
open import proof.ConsistencyProperties
open import proof.ImprecisionConsistent
open import proof.PreservationBetaUpNu
  using
    ( raiseVarFrom
    ; raise-ext
    ; rename-raise-ext
    ; rename-raise-⇑ᵗ
    ; cong-⊢⊑
    )
open import proof.PreservationImpSubst
  using
    ( ⊑-substᵗ-wt
    ; singleTyEnv-TySubstWf-plains
    ; singleTyEnv-ImpSubstWt
    ; reflImp-wt-plains
    )
open import proof.PreservationTermSubst
  using (renameᵗ-[]ᵗ; unmap∋-⤊ᵗ; wkImp-plains)

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _`[_]
infixl 6 _⊕[_]_
infix  9 `_

data GTerm : Set where
  `_      : Var → GTerm
  ƛ_⇒_    : Ty → GTerm → GTerm
  _·_     : GTerm → GTerm → GTerm
  Λ_      : GTerm → GTerm
  _`[_]   : GTerm → Ty → GTerm
  $       : Const → GTerm
  _⊕[_]_  : GTerm → Prim → GTerm → GTerm


------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : GTerm → Set where
  ƛ_⇒_ :
    (A : Ty) (N : GTerm) →
    Value (ƛ A ⇒ N)

  $ :
    (κ : Const) →
    Value ($ κ)

  Λ_ :
    (N : GTerm) →
    Value (Λ N)

renameᵗᴳ : Renameᵗ → GTerm → GTerm
renameᵗᴳ ρ (` x) = ` x
renameᵗᴳ ρ (ƛ A ⇒ M) = ƛ renameᵗ ρ A ⇒ renameᵗᴳ ρ M
renameᵗᴳ ρ (L · M) = renameᵗᴳ ρ L · renameᵗᴳ ρ M
renameᵗᴳ ρ (Λ M) = Λ (renameᵗᴳ (extᵗ ρ) M)
renameᵗᴳ ρ (M `[ T ]) = renameᵗᴳ ρ M `[ renameᵗ ρ T ]
renameᵗᴳ ρ ($ κ) = $ κ
renameᵗᴳ ρ (L ⊕[ op ] M) = renameᵗᴳ ρ L ⊕[ op ] renameᵗᴳ ρ M

renameCtxAt : ℕ → Ctx → Ctx
renameCtxAt k [] = []
renameCtxAt k (A ∷ Γ) =
  renameᵗ (raiseVarFrom k) A ∷ renameCtxAt k Γ

renameCtxAt-zero :
  ∀ Γ →
  renameCtxAt zero Γ ≡ ⤊ᵗ Γ
renameCtxAt-zero [] = refl
renameCtxAt-zero (A ∷ Γ) = cong (⇑ᵗ A ∷_) (renameCtxAt-zero Γ)

renameCtxAt-⤊ᵗ :
  ∀ k Γ →
  renameCtxAt (suc k) (⤊ᵗ Γ) ≡ ⤊ᵗ (renameCtxAt k Γ)
renameCtxAt-⤊ᵗ k [] = refl
renameCtxAt-⤊ᵗ k (A ∷ Γ) =
  cong₂ _∷_ (rename-raise-⇑ᵗ k A) (renameCtxAt-⤊ᵗ k Γ)

renameᵗᴳ-cong :
  ∀ {ρ ρ′} →
  (∀ X → ρ X ≡ ρ′ X) →
  (M : GTerm) →
  renameᵗᴳ ρ M ≡ renameᵗᴳ ρ′ M
renameᵗᴳ-cong h (` x) = refl
renameᵗᴳ-cong h (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_ (rename-cong h A) (renameᵗᴳ-cong h M)
renameᵗᴳ-cong h (L · M) =
  cong₂ _·_ (renameᵗᴳ-cong h L) (renameᵗᴳ-cong h M)
renameᵗᴳ-cong {ρ = ρ} {ρ′ = ρ′} h (Λ M) =
  cong Λ_ (renameᵗᴳ-cong h′ M)
  where
    h′ : ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
    h′ zero = refl
    h′ (suc X) = cong suc (h X)
renameᵗᴳ-cong h (M `[ T ]) =
  cong₂ _`[_] (renameᵗᴳ-cong h M) (rename-cong h T)
renameᵗᴳ-cong h ($ κ) = refl
renameᵗᴳ-cong h (L ⊕[ op ] M) =
  cong₂ (λ L M → L ⊕[ op ] M)
    (renameᵗᴳ-cong h L) (renameᵗᴳ-cong h M)

renameᵗᴳ-value-inv :
  ∀ {ρ M} →
  Value (renameᵗᴳ ρ M) →
  Value M
renameᵗᴳ-value-inv {M = ƛ A ⇒ M} (ƛ ._ ⇒ ._) = ƛ A ⇒ M
renameᵗᴳ-value-inv {M = Λ M} (Λ ._) = Λ M
renameᵗᴳ-value-inv {M = $ κ} ($ .κ) = $ κ

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix  4 _∣_⊢_⦂_

data _∣_⊢_⦂_ (Δ : TyCtx) (Γ : Ctx) : GTerm → Ty → Set where

  ⊢` : ∀ {x A}
     → Γ ∋ x ⦂ A
     → Δ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {M A B}
     → WfTy Δ 0 A
     → Δ ∣ (A ∷ Γ) ⊢ M ⦂ B
     → Δ ∣ Γ ⊢ (ƛ A ⇒ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {L M A A′ B}
     → Δ ∣ Γ ⊢ L ⦂ (A ⇒ B)
     → Δ ∣ Γ ⊢ M ⦂ A′
     → boths Δ [] ⊢ A ~ A′
     → Δ ∣ Γ ⊢ (L · M) ⦂ B

  ⊢·★ : ∀ {L M A′}
     → Δ ∣ Γ ⊢ L ⦂ ★
     → Δ ∣ Γ ⊢ M ⦂ A′
     → boths Δ [] ⊢ A′ ~ ★
     → Δ ∣ Γ ⊢ (L · M) ⦂ ★

  ⊢Λ : ∀ {M A}
     → Value M
     → (suc Δ) ∣ (⤊ᵗ Γ) ⊢ M ⦂ A
     → Δ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {M B T}
     → Δ ∣ Γ ⊢ M ⦂ (`∀ B)
     → WfTy (suc Δ) 0 B
     → WfTy Δ 0 T
     → Δ ∣ Γ ⊢ (M `[ T ]) ⦂ B [ T ]ᵗ
     
  ⊢•★ : ∀ {M T}
     → Δ ∣ Γ ⊢ M ⦂ ★
     → WfTy 0 0 T
     → Δ ∣ Γ ⊢ (M `[ T ]) ⦂ ★

  ⊢$ : ∀ (κ : Const)
     → Δ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M A B}
     → Δ ∣ Γ ⊢ L ⦂ A → boths Δ [] ⊢ A ~ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Γ ⊢ M ⦂ B → boths Δ [] ⊢ B ~ (‵ `ℕ)
     → Δ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

cong-⊢ᴳ⦂ :
  ∀ {Δ Δ′ Γ Γ′ M M′ A A′} →
  Δ ≡ Δ′ →
  Γ ≡ Γ′ →
  M ≡ M′ →
  A ≡ A′ →
  Δ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ Γ′ ⊢ M′ ⦂ A′
cong-⊢ᴳ⦂ refl refl refl refl M⊢ = M⊢

------------------------------------------------------------------------
-- Gradual-term imprecision
------------------------------------------------------------------------

infix 4 _⊢ᴳ_⊑_
data _⊢ᴳ_⊑_ (Δ : TyCtx) : GTerm → GTerm → Set where

  ⊑` : ∀ {x} →
    Δ ⊢ᴳ (` x) ⊑ (` x)

  ⊑ƛ : ∀ {A A′ M M′ pA} →
    0 ∣ plains Δ [] ⊢ pA ⦂ A ⊑ A′ →
    Δ ⊢ᴳ M ⊑ M′ →
    Δ ⊢ᴳ (ƛ A ⇒ M) ⊑ (ƛ A′ ⇒ M′)

  ⊑· : ∀ {L L′ M M′} →
    Δ ⊢ᴳ L ⊑ L′ →
    Δ ⊢ᴳ M ⊑ M′ →
    Δ ⊢ᴳ (L · M) ⊑ (L′ · M′)

  ⊑Λ : ∀ {M M′} →
    Value M →
    Value M′ →
    suc Δ ⊢ᴳ M ⊑ M′ →
    Δ ⊢ᴳ (Λ M) ⊑ (Λ M′)

  ⊑ΛL : ∀ {M M′} →
    Value M →
    suc Δ ⊢ᴳ M ⊑ renameᵗᴳ suc M′ →
    Δ ⊢ᴳ (Λ M) ⊑ M′

  ⊑`[] : ∀ {M M′ T T′ pT} →
    Δ ⊢ᴳ M ⊑ M′ →
    0 ∣ plains Δ [] ⊢ pT ⦂ T ⊑ T′ →
    Δ ⊢ᴳ (M `[ T ]) ⊑ (M′ `[ T′ ])

  ⊑`[]L : ∀ {M M′ T} →
    Δ ⊢ᴳ M ⊑ M′ →
    WfTy 0 0 T →
    Δ ⊢ᴳ (M `[ T ]) ⊑ M′

  ⊑$ : ∀ {n} →
    Δ ⊢ᴳ ($ (κℕ n)) ⊑ ($ (κℕ n))

  ⊑⊕ : ∀ {L L′ M M′ op} →
    Δ ⊢ᴳ L ⊑ L′ →
    Δ ⊢ᴳ M ⊑ M′ →
    Δ ⊢ᴳ (L ⊕[ op ] M) ⊑ (L′ ⊕[ op ] M′)

------------------------------------------------------------------------
-- Static gradual guarantee, first formulation
------------------------------------------------------------------------

GPrec : TyCtx → Set
GPrec Δ =
  Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    (0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B)

GPCtx : TyCtx → Set
GPCtx Δ = List (GPrec Δ)

leftGTy : ∀ {Δ} → GPrec Δ → Ty
leftGTy (A , B , p , p⊢) = A

rightGTy : ∀ {Δ} → GPrec Δ → Ty
rightGTy (A , B , p , p⊢) = B

leftGCtx : ∀ {Δ} → GPCtx Δ → Ctx
leftGCtx [] = []
leftGCtx (P ∷ Γ) = leftGTy P ∷ leftGCtx Γ

rightGCtx : ∀ {Δ} → GPCtx Δ → Ctx
rightGCtx [] = []
rightGCtx (P ∷ Γ) = rightGTy P ∷ rightGCtx Γ

infix 4 _∋ᴳ_⦂_
data _∋ᴳ_⦂_ {Δ : TyCtx} :
    GPCtx Δ → Var → GPrec Δ → Set where

  Zᴳ : ∀ {Γ P} →
    (P ∷ Γ) ∋ᴳ zero ⦂ P

  Sᴳ : ∀ {Γ P Q x} →
    Γ ∋ᴳ x ⦂ P →
    (Q ∷ Γ) ∋ᴳ suc x ⦂ P

lookup-leftᴳ :
  ∀ {Δ} {Γ : GPCtx Δ} {x A B p p⊢} →
  Γ ∋ᴳ x ⦂ (A , B , p , p⊢) →
  leftGCtx Γ ∋ x ⦂ A
lookup-leftᴳ Zᴳ = Z
lookup-leftᴳ (Sᴳ h) = S (lookup-leftᴳ h)

lookup-rightᴳ :
  ∀ {Δ} {Γ : GPCtx Δ} {x A B p p⊢} →
  Γ ∋ᴳ x ⦂ (A , B , p , p⊢) →
  rightGCtx Γ ∋ x ⦂ B
lookup-rightᴳ Zᴳ = Z
lookup-rightᴳ (Sᴳ h) = S (lookup-rightᴳ h)

lookup-leftᴳ-inv :
  ∀ {Δ} {Γ : GPCtx Δ} {x A} →
  leftGCtx Γ ∋ x ⦂ A →
  Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    Σ[ p⊢ ∈ 0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B ]
      Γ ∋ᴳ x ⦂ (A , B , p , p⊢)
lookup-leftᴳ-inv {Γ = (A , B , p , p⊢) ∷ Γ} Z =
  B , p , p⊢ , Zᴳ
lookup-leftᴳ-inv {Γ = P ∷ Γ} (S h)
    with lookup-leftᴳ-inv {Γ = Γ} h
lookup-leftᴳ-inv {Γ = P ∷ Γ} (S h) | B , p , p⊢ , hᴳ =
  B , p , p⊢ , Sᴳ hᴳ

⇑ᵗᴳPrec : ∀ {Δ} → GPrec Δ → GPrec (suc Δ)
⇑ᵗᴳPrec (A , B , p , p⊢) =
  ⇑ᵗ A , ⇑ᵗ B , renameImp suc p , wkImp-plains zero p⊢

⇑ᵗᴳPCtx : ∀ {Δ} → GPCtx Δ → GPCtx (suc Δ)
⇑ᵗᴳPCtx [] = []
⇑ᵗᴳPCtx (P ∷ Γ) = ⇑ᵗᴳPrec P ∷ ⇑ᵗᴳPCtx Γ

leftGCtx-⇑ᵗᴳPCtx :
  ∀ {Δ} → (Γ : GPCtx Δ) →
  leftGCtx (⇑ᵗᴳPCtx Γ) ≡ ⤊ᵗ (leftGCtx Γ)
leftGCtx-⇑ᵗᴳPCtx [] = refl
leftGCtx-⇑ᵗᴳPCtx ((A , B , p , p⊢) ∷ Γ) =
  cong (⇑ᵗ A ∷_) (leftGCtx-⇑ᵗᴳPCtx Γ)

rightGCtx-⇑ᵗᴳPCtx :
  ∀ {Δ} → (Γ : GPCtx Δ) →
  rightGCtx (⇑ᵗᴳPCtx Γ) ≡ ⤊ᵗ (rightGCtx Γ)
rightGCtx-⇑ᵗᴳPCtx [] = refl
rightGCtx-⇑ᵗᴳPCtx ((A , B , p , p⊢) ∷ Γ) =
  cong (⇑ᵗ B ∷_) (rightGCtx-⇑ᵗᴳPCtx Γ)

boths-length-split :
  (Φ Γ : CCtx) →
  boths (length (Φ ++ Γ)) [] ≡ boths (length Φ) [] ++ boths (length Γ) []
boths-length-split [] Γ = refl
boths-length-split (m ∷ Φ) Γ =
  cong (both ∷_) (boths-length-split Φ Γ)

length-boths-split :
  (Φ Γ : CCtx) →
  length (Φ ++ Γ) ≡ length (boths (length Φ) [] ++ boths (length Γ) [])
length-boths-split [] Γ = sym (length-boths[] (length Γ))
length-boths-split (m ∷ Φ) Γ = cong suc (length-boths-split Φ Γ)

rename-raise-length-boths :
  (Φ : CCtx) (A : Ty) →
  renameᵗ (raiseVarFrom (length Φ)) A ≡
  renameᵗ (raiseVarFrom (length (boths (length Φ) []))) A
rename-raise-length-boths Φ A =
  rename-cong
    (λ X → cong (λ n → raiseVarFrom n X)
      (sym (length-boths[] (length Φ))))
    A

⊑-src-wf-plains :
  ∀ {Δ p A B} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  WfTy Δ 0 A
⊑-src-wf-plains {Δ = Δ} p⊢ =
  subst (λ n → WfTy n 0 _) (length-plains[] Δ) (⊑-src-wf p⊢)

⊑-tgt-wf-plains :
  ∀ {Δ p A B} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  WfTy Δ 0 B
⊑-tgt-wf-plains {Δ = Δ} p⊢ =
  subst (λ n → WfTy n 0 _) (length-plains[] Δ) (⊑-tgt-wf p⊢)

SGGResult : (Δ : TyCtx) → GPCtx Δ → GTerm → Ty → Set
SGGResult Δ Γ M′ A =
  Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    ((Δ ∣ rightGCtx Γ ⊢ M′ ⦂ B) ×
     (0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B))

static-gradual-guarantee :
  ∀ {Δ Γ M M′ A} →
  Δ ⊢ᴳ M ⊑ M′ →
  Δ ∣ leftGCtx Γ ⊢ M ⦂ A →
  Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    (Δ ∣ rightGCtx Γ ⊢ M′ ⦂ B) × (0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B)
    
------------------------------------------------------------------------
-- Compilation to explicit casts
------------------------------------------------------------------------

<-weaken+ :
  ∀ Δ {X k} →
  X < k →
  X < k + Δ
<-weaken+ Δ {k = zero} ()
<-weaken+ Δ {X = zero} {k = suc k} z<s = z<s
<-weaken+ Δ {X = suc X} {k = suc k} (s<s X<k) =
  s<s (<-weaken+ Δ X<k)

WfTy-weakenᵗ :
  ∀ k Δ {Ψ A} →
  WfTy k Ψ A →
  WfTy (k + Δ) Ψ A
WfTy-weakenᵗ k Δ (wfVar X<k) = wfVar (<-weaken+ Δ X<k)
WfTy-weakenᵗ k Δ (wfSeal α<Ψ) = wfSeal α<Ψ
WfTy-weakenᵗ k Δ wfBase = wfBase
WfTy-weakenᵗ k Δ wf★ = wf★
WfTy-weakenᵗ k Δ (wf⇒ wfA wfB) =
  wf⇒ (WfTy-weakenᵗ k Δ wfA) (WfTy-weakenᵗ k Δ wfB)
WfTy-weakenᵗ k Δ (wf∀ wfA) = wf∀ (WfTy-weakenᵗ (suc k) Δ wfA)

WfTy-closed-weakenᵗ :
  ∀ Δ {Ψ A} →
  WfTy 0 Ψ A →
  WfTy Δ Ψ A
WfTy-closed-weakenᵗ Δ wfA = WfTy-weakenᵗ zero Δ wfA

renameᵗ-inv-WfTy :
  ∀ {Δ Ψ A ρ} →
  (∀ {X} → ρ X < Δ → X < Δ) →
  WfTy Δ Ψ (renameᵗ ρ A) →
  WfTy Δ Ψ A
renameᵗ-inv-WfTy {A = ＇ X} hρ (wfVar ρX<Δ) = wfVar (hρ ρX<Δ)
renameᵗ-inv-WfTy {A = ｀ α} hρ (wfSeal α<Ψ) = wfSeal α<Ψ
renameᵗ-inv-WfTy {A = ‵ ι} hρ wfBase = wfBase
renameᵗ-inv-WfTy {A = ★} hρ wf★ = wf★
renameᵗ-inv-WfTy {A = A ⇒ B} hρ (wf⇒ wfA wfB) =
  wf⇒ (renameᵗ-inv-WfTy hρ wfA) (renameᵗ-inv-WfTy hρ wfB)
renameᵗ-inv-WfTy {A = `∀ A} hρ (wf∀ wfA) =
  wf∀ (renameᵗ-inv-WfTy h-ext wfA)
  where
    h-ext : ∀ {X} → extᵗ _ X < _ → X < _
    h-ext {zero} z<s = z<s
    h-ext {suc X} (s<s ρX<Δ) = s<s (hρ ρX<Δ)

drop-mode-WfTy :
  ∀ {d Φ Γ A} →
  WfTy (length (Φ ++ d ∷ Γ)) 0
    (renameᵗ (raiseVarFrom (length Φ)) A) →
  WfTy (length (Φ ++ Γ)) 0 A
drop-mode-WfTy {Φ = Φ} {Γ = Γ} {A = ＇ X} (wfVar X<Γ) =
  wfVar (drop<-raise-mode {Φ = Φ} {Γ = Γ} {X = X} X<Γ)
drop-mode-WfTy {A = ｀ α} (wfSeal α<Ψ) = wfSeal α<Ψ
drop-mode-WfTy {A = ‵ ι} wfBase = wfBase
drop-mode-WfTy {A = ★} wf★ = wf★
drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = A ⇒ B} (wf⇒ wfA wfB) =
  wf⇒ (drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = A} wfA)
       (drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = B} wfB)
drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = `∀ A} (wf∀ wfA) =
  wf∀
    (drop-mode-WfTy {d = d} {Φ = both ∷ Φ} {Γ = Γ} {A = A}
      (subst (λ B → WfTy (length ((both ∷ Φ) ++ d ∷ Γ)) 0 B)
        (rename-raise-ext (length Φ) A)
        wfA))

drop-neither-WfTy :
  ∀ {Φ Γ A} →
  WfTy (length (Φ ++ neither ∷ Γ)) 0
    (renameᵗ (raiseVarFrom (length Φ)) A) →
  WfTy (length (Φ ++ Γ)) 0 A
drop-neither-WfTy {Φ = Φ} {Γ = Γ} {A = A} wfA =
  drop-mode-WfTy {d = neither} {Φ = Φ} {Γ = Γ} {A = A} wfA

var-var-~-inj :
  ∀ {Γ X Y} →
  Γ ⊢ ＇ X ~ ＇ Y →
  Σ[ eq ∈ X ≡ Y ] Γ ∋ᶜ X ∶ both
var-var-~-inj (X-~-X x∈) = refl , x∈

~-size :
  ∀ {Γ A B} →
  Γ ⊢ A ~ B →
  ℕ
~-size ★-~-★ = zero
~-size (X-~-X x∈) = zero
~-size ι-~-ι = zero
~-size (⇒-~-⇒ h₁ h₂) = suc (~-size h₁ + ~-size h₂)
~-size (∀-~-∀ h) = suc (~-size h)
~-size (A-~-★ g h) = suc (~-size h)
~-size (★-~-B hG h) = suc (~-size h)
~-size (νX-~-★ x∈) = zero
~-size (★-~-νX x∈) = zero
~-size (∀-~-B wfB h) = suc (~-size h)
~-size (A-~-∀ wfA h) = suc (~-size h)

≤refl : ∀ {n} → n ≤ n
≤refl {zero} = z≤n
≤refl {suc n} = s≤s ≤refl

≤step : ∀ {m n} → m ≤ n → m ≤ suc n
≤step z≤n = z≤n
≤step (s≤s m≤n) = s≤s (≤step m≤n)

≤trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤trans z≤n q = z≤n
≤trans (s≤s p) (s≤s q) = s≤s (≤trans p q)

≤left+ : ∀ m n → m ≤ m + n
≤left+ zero n = z≤n
≤left+ (suc m) n = s≤s (≤left+ m n)

≤right+ : ∀ m n → n ≤ m + n
≤right+ zero n = ≤refl
≤right+ (suc m) n = ≤step (≤right+ m n)

cong-~-size :
  ∀ {Γ A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (h : Γ ⊢ A ~ B) →
  ~-size (cong-~ eqA eqB h) ≡ ~-size h
cong-~-size refl refl h = refl

cong-~-≤ :
  ∀ {Γ A A′ B B′ gas} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (h : Γ ⊢ A ~ B) →
  ~-size h ≤ gas →
  ~-size (cong-~ eqA eqB h) ≤ gas
cong-~-≤ eqA eqB h p =
  subst (λ n → n ≤ _) (sym (cong-~-size eqA eqB h)) p

drop-mode-at-X-suc :
  ∀ {d m Φ Γ X Y} →
  (m ∷ Φ) ++ d ∷ Γ ⊢
    ＇ suc (raiseVarFrom (length Φ) X) ~
    ＇ suc (raiseVarFrom (length Φ) Y) →
  (m ∷ Φ) ++ Γ ⊢ ＇ suc X ~ ＇ suc Y
drop-mode-at-X-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
    with var-var-~-inj h
drop-mode-at-X-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
    | eq , x∈
    with raiseVarFrom-injective (length Φ) (suc-injective eq)
drop-mode-at-X-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
    | eq , x∈ | refl =
  X-~-X (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ}
           {X = suc X} x∈)

drop-mode-at-νL-suc :
  ∀ {d m Φ Γ X} →
  (m ∷ Φ) ++ d ∷ Γ ⊢
    ＇ suc (raiseVarFrom (length Φ) X) ~ ★ →
  (m ∷ Φ) ++ Γ ⊢ ＇ suc X ~ ★
drop-mode-at-νL-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X}
    (νX-~-★ x∈) =
  νX-~-★
    (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ} {X = suc X} x∈)
drop-mode-at-νL-suc (A-~-★ (｀ α) ())
drop-mode-at-νL-suc (A-~-★ (‵ ι) ())
drop-mode-at-νL-suc (A-~-★ ★⇒★ ())

drop-mode-at-νR-suc :
  ∀ {d m Φ Γ X} →
  (m ∷ Φ) ++ d ∷ Γ ⊢
    ★ ~ ＇ suc (raiseVarFrom (length Φ) X) →
  (m ∷ Φ) ++ Γ ⊢ ★ ~ ＇ suc X
drop-mode-at-νR-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X}
    (★-~-νX x∈) =
  ★-~-νX
    (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ} {X = suc X} x∈)
drop-mode-at-νR-suc (★-~-B (｀ α) ())
drop-mode-at-νR-suc (★-~-B (‵ ι) ())
drop-mode-at-νR-suc (★-~-B ★⇒★ ())

drop-mode-at-~-gas :
  (gas : ℕ) →
  ∀ {d Φ Γ B C}
    {h : Φ ++ d ∷ Γ ⊢ renameᵗ (raiseVarFrom (length Φ)) B
                         ~ renameᵗ (raiseVarFrom (length Φ)) C} →
  ~-size h ≤ gas →
  Φ ++ Γ ⊢ B ~ C
drop-mode-at-~-gas gas {B = ★} {C = ★} {h = ★-~-★} p = ★-~-★
drop-mode-at-~-gas gas {d = d} {Φ = []} {Γ = Γ}
    {B = ＇ X} {C = ＇ .X}
    {h = X-~-X {X = .(suc X)} x∈} p =
  X-~-X (drop∋ᶜ-mode {d = d} {Φ = []} {Γ = Γ} {X = X} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ zero}
    {C = ＇ zero}
    {h = X-~-X {X = zero} x∈} p =
  X-~-X (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ}
           {X = zero} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ suc X}
    {C = ＇ suc Y} {h = h} p =
  drop-mode-at-X-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ}
    {X = X} {Y = Y} h
drop-mode-at-~-gas gas {B = ‵ ι} {C = ‵ ι′} {h = ι-~-ι} p =
  ι-~-ι
drop-mode-at-~-gas zero {B = A ⇒ B} {C = A′ ⇒ B′}
    {h = ⇒-~-⇒ A~A′ B~B′} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = A ⇒ B}
    {C = A′ ⇒ B′} {h = ⇒-~-⇒ A~A′ B~B′} (s≤s p) =
  ⇒-~-⇒
    (drop-mode-at-~-gas gas
      {d = d} {Φ = Φ} {Γ = Γ} {B = A} {C = A′} {h = A~A′}
      (≤trans (≤left+ (~-size A~A′) (~-size B~B′)) p))
    (drop-mode-at-~-gas gas
      {d = d} {Φ = Φ} {Γ = Γ} {B = B} {C = B′} {h = B~B′}
      (≤trans (≤right+ (~-size A~A′) (~-size B~B′)) p))
drop-mode-at-~-gas zero {B = `∀ A} {C = `∀ B} {h = ∀-~-∀ A~B} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = `∀ A}
    {C = `∀ B} {h = ∀-~-∀ A~B} (s≤s p) =
  ∀-~-∀
    (drop-mode-at-~-gas gas
      {d = d} {Φ = both ∷ Φ} {Γ = Γ} {B = A} {C = B}
      {h = cong-~ (rename-raise-ext (length Φ) A)
                  (rename-raise-ext (length Φ) B)
                  A~B}
      (cong-~-≤ (rename-raise-ext (length Φ) A)
                (rename-raise-ext (length Φ) B)
                A~B p))
drop-mode-at-~-gas zero {B = A} {C = ★} {h = A-~-★ g A~G} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = A}
    {C = ★}
    {h = A-~-★ {G = G} g A~G} (s≤s p) =
  A-~-★ g
    (drop-mode-at-~-gas gas
      {d = d} {Φ = Φ} {Γ = Γ} {B = A} {C = G}
      {h = cong-~ refl (sym (renameᵗ-ground-id g)) A~G}
      (cong-~-≤ refl (sym (renameᵗ-ground-id g)) A~G p))
drop-mode-at-~-gas zero {B = ★} {C = B} {h = ★-~-B g H~B} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = ★}
    {C = B}
    {h = ★-~-B {H = H} g H~B} (s≤s p) =
  ★-~-B g
    (drop-mode-at-~-gas gas
      {d = d} {Φ = Φ} {Γ = Γ} {B = H} {C = B}
      {h = cong-~ (sym (renameᵗ-ground-id g)) refl H~B}
      (cong-~-≤ (sym (renameᵗ-ground-id g)) refl H~B p))
drop-mode-at-~-gas gas {d = d} {Φ = []} {Γ = Γ} {B = ＇ X}
    {C = ★}
    {h = νX-~-★ {X = .(suc X)} x∈} p =
  νX-~-★ (drop∋ᶜ-mode {d = d} {Φ = []} {Γ = Γ} {X = X} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ zero}
    {C = ★}
    {h = νX-~-★ {X = zero} x∈} p =
  νX-~-★ (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ}
            {X = zero} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ suc X}
    {C = ★} {h = h} p =
  drop-mode-at-νL-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
drop-mode-at-~-gas gas {d = d} {Φ = []} {Γ = Γ} {B = ★} {C = ＇ X}
    {h = ★-~-νX {X = .(suc X)} x∈} p =
  ★-~-νX (drop∋ᶜ-mode {d = d} {Φ = []} {Γ = Γ} {X = X} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ★}
    {C = ＇ zero}
    {h = ★-~-νX {X = zero} x∈} p =
  ★-~-νX (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ}
            {X = zero} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ★}
    {C = ＇ suc X} {h = h} p =
  drop-mode-at-νR-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
drop-mode-at-~-gas zero {B = `∀ A} {C = B} {h = ∀-~-B wfB A~⇑B} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = `∀ A}
    {C = B}
    {h = ∀-~-B wfB A~⇑B} (s≤s p) =
  ∀-~-B
    (drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = B} wfB)
    (drop-mode-at-~-gas gas
      {d = d} {Φ = left ∷ Φ} {Γ = Γ} {B = A} {C = ⇑ᵗ B}
      {h = cong-~ (rename-raise-ext (length Φ) A)
                  (sym (rename-raise-⇑ᵗ (length Φ) B))
                  A~⇑B}
      (cong-~-≤ (rename-raise-ext (length Φ) A)
                (sym (rename-raise-⇑ᵗ (length Φ) B))
                A~⇑B p))
drop-mode-at-~-gas zero {B = A} {C = `∀ B} {h = A-~-∀ wfA ⇑A~B} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = A}
    {C = `∀ B}
    {h = A-~-∀ wfA ⇑A~B} (s≤s p) =
  A-~-∀
    (drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = A} wfA)
    (drop-mode-at-~-gas gas
      {d = d} {Φ = right ∷ Φ} {Γ = Γ} {B = ⇑ᵗ A} {C = B}
      {h = cong-~ (sym (rename-raise-⇑ᵗ (length Φ) A))
                  (rename-raise-ext (length Φ) B)
                  ⇑A~B}
      (cong-~-≤ (sym (rename-raise-⇑ᵗ (length Φ) A))
                (rename-raise-ext (length Φ) B)
                ⇑A~B p))

drop-mode-at-~ :
  ∀ {d Φ Γ B C} →
  Φ ++ d ∷ Γ ⊢ renameᵗ (raiseVarFrom (length Φ)) B
                  ~ renameᵗ (raiseVarFrom (length Φ)) C →
  Φ ++ Γ ⊢ B ~ C
drop-mode-at-~ h = drop-mode-at-~-gas (~-size h) {h = h} ≤refl

drop-neither-at-~ :
  ∀ {Φ Γ B C} →
  Φ ++ neither ∷ Γ ⊢ renameᵗ (raiseVarFrom (length Φ)) B
                     ~ renameᵗ (raiseVarFrom (length Φ)) C →
  Φ ++ Γ ⊢ B ~ C
drop-neither-at-~ = drop-mode-at-~ {d = neither}

drop-mode-~ :
  ∀ {d Γ B C} →
  d ∷ Γ ⊢ ⇑ᵗ B ~ ⇑ᵗ C →
  Γ ⊢ B ~ C
drop-mode-~ = drop-mode-at-~ {Φ = []}

drop-both-~ :
  ∀ {Γ B C} →
  both ∷ Γ ⊢ ⇑ᵗ B ~ ⇑ᵗ C →
  Γ ⊢ B ~ C
drop-both-~ = drop-mode-~ {d = both}

drop-boths-at-~ :
  ∀ {d Φ Γ B C} →
  boths (length (Φ ++ d ∷ Γ)) [] ⊢
    renameᵗ (raiseVarFrom (length Φ)) B ~
    renameᵗ (raiseVarFrom (length Φ)) C →
  boths (length (Φ ++ Γ)) [] ⊢ B ~ C
drop-boths-at-~ {d = d} {Φ = Φ} {Γ = Γ} {B = B} {C = C} h =
  subst (λ Ξ → Ξ ⊢ B ~ C) (sym (boths-length-split Φ Γ))
    (drop-mode-at-~ {d = both} {Φ = boths (length Φ) []}
      {Γ = boths (length Γ) []} {B = B} {C = C}
      (cong-~
        (rename-raise-length-boths Φ B)
        (rename-raise-length-boths Φ C)
        (subst
          (λ Ξ → Ξ ⊢ renameᵗ (raiseVarFrom (length Φ)) B
                     ~ renameᵗ (raiseVarFrom (length Φ)) C)
          (boths-length-split Φ (d ∷ Γ))
          h)))

drop-neither-~ :
  ∀ {Γ B C} →
  neither ∷ Γ ⊢ ⇑ᵗ B ~ ⇑ᵗ C →
  Γ ⊢ B ~ C
drop-neither-~ = drop-mode-~ {d = neither}

drop-boths-WfTy :
  ∀ {d Φ Γ A} →
  WfTy (length (Φ ++ d ∷ Γ)) 0
    (renameᵗ (raiseVarFrom (length Φ)) A) →
  WfTy (length (Φ ++ Γ)) 0 A
drop-boths-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = A} wfA =
  subst (λ n → WfTy n 0 A) (sym (length-boths-split Φ Γ))
    (drop-mode-WfTy {d = both} {Φ = boths (length Φ) []}
      {Γ = boths (length Γ) []} {A = A}
      (subst
        (λ n → WfTy n 0
          (renameᵗ (raiseVarFrom (length (boths (length Φ) []))) A))
        (length-boths-split Φ (d ∷ Γ))
        (subst
          (λ B → WfTy (length (Φ ++ d ∷ Γ)) 0 B)
          (rename-raise-length-boths Φ A)
          wfA)))

drop-⇑ᵗ-WfTy-plains :
  ∀ {Δ A} →
  WfTy (suc Δ) 0 (⇑ᵗ A) →
  WfTy Δ 0 A
drop-⇑ᵗ-WfTy-plains {Δ = Δ} {A = A} wfA =
  subst (λ n → WfTy n 0 A) (length-boths[] Δ)
    (drop-mode-WfTy {d = both} {Φ = []} {Γ = boths Δ []} {A = A}
      (subst (λ n → WfTy (suc n) 0 (⇑ᵗ A))
        (sym (length-boths[] Δ))
        wfA))

swap-boths[] :
  ∀ Δ →
  swapCCtx (boths Δ []) ≡ boths Δ []
swap-boths[] zero = refl
swap-boths[] (suc Δ) = cong (both ∷_) (swap-boths[] Δ)

boths-sym :
  ∀ {Δ A B} →
  boths Δ [] ⊢ A ~ B →
  boths Δ [] ⊢ B ~ A
boths-sym {Δ = Δ} {A = A} {B = B} A~B =
  subst (λ Γ → Γ ⊢ B ~ A) (swap-boths[] Δ) (~-sym A~B)

left-right-plain :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ plain →
  rightICtx Γ ∋ X ∶ plain →
  Γ ∋ᶜ X ∶ both
left-right-plain {Γ = left ∷ Γ} Imprecision.here ()
left-right-plain {Γ = left ∷ Γ} (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = right ∷ Γ} () Imprecision.here
left-right-plain {Γ = right ∷ Γ} (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = both ∷ Γ} Imprecision.here Imprecision.here = here
left-right-plain {Γ = both ∷ Γ} (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = neither ∷ Γ} {X = zero} () ()
left-right-plain {Γ = neither ∷ Γ} {X = suc X}
    (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-right-plain x∈ y∈)

left-ν-right-plain :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ ν-bound →
  rightICtx Γ ∋ X ∶ plain →
  Γ ∋ᶜ X ∶ right
left-ν-right-plain {Γ = left ∷ Γ} {X = zero} ()
left-ν-right-plain {Γ = left ∷ Γ} {X = suc X}
    (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = right ∷ Γ} Imprecision.here Imprecision.here = here
left-ν-right-plain {Γ = right ∷ Γ} (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = both ∷ Γ} {X = zero} () Imprecision.here
left-ν-right-plain {Γ = both ∷ Γ} {X = suc X}
    (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = neither ∷ Γ} {X = zero} Imprecision.here ()
left-ν-right-plain {Γ = neither ∷ Γ} {X = suc X}
    (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-ν-right-plain x∈ y∈)

left-plain-right-ν :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ plain →
  rightICtx Γ ∋ X ∶ ν-bound →
  Γ ∋ᶜ X ∶ left
left-plain-right-ν {Γ = left ∷ Γ} Imprecision.here Imprecision.here = here
left-plain-right-ν {Γ = left ∷ Γ} (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = right ∷ Γ} {X = zero} () ()
left-plain-right-ν {Γ = right ∷ Γ} {X = suc X}
    (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = both ∷ Γ} {X = zero} Imprecision.here ()
left-plain-right-ν {Γ = both ∷ Γ} {X = suc X}
    (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = neither ∷ Γ} {X = zero} () Imprecision.here
left-plain-right-ν {Γ = neither ∷ Γ} {X = suc X}
    (Imprecision.there x∈) (Imprecision.there y∈) =
  there (left-plain-right-ν x∈ y∈)

lower-bounds-consistentᶜ :
  ∀ {Γ A B C p q} →
  0 ∣ leftICtx Γ ⊢ p ⦂ A ⊑ B →
  0 ∣ rightICtx Γ ⊢ q ⦂ A ⊑ C →
  Γ ⊢ B ~ C
lower-bounds-consistentᶜ (⊑-★ g p⊢) q⊢ =
  ★-~-B g (lower-bounds-consistentᶜ p⊢ q⊢)
lower-bounds-consistentᶜ p⊢ (⊑-★ g q⊢) =
  A-~-★ g (lower-bounds-consistentᶜ p⊢ q⊢)
lower-bounds-consistentᶜ ⊑-★★ ⊑-★★ = ★-~-★
lower-bounds-consistentᶜ (⊑-★ν xν) (⊑-★ν yν) = ★-~-★
lower-bounds-consistentᶜ (⊑-★ν xν) (⊑-＇ y∈) =
  ★-~-νX (left-ν-right-plain xν y∈)
lower-bounds-consistentᶜ (⊑-＇ x∈) (⊑-★ν yν) =
  νX-~-★ (left-plain-right-ν x∈ yν)
lower-bounds-consistentᶜ (⊑-＇ x∈) (⊑-＇ y∈) =
  X-~-X (left-right-plain x∈ y∈)
lower-bounds-consistentᶜ (⊑-｀ (wfSeal ())) q⊢
lower-bounds-consistentᶜ ⊑-‵ ⊑-‵ = ι-~-ι
lower-bounds-consistentᶜ (⊑-⇒ p₁⊢ p₂⊢) (⊑-⇒ q₁⊢ q₂⊢) =
  ⇒-~-⇒ (lower-bounds-consistentᶜ p₁⊢ q₁⊢)
         (lower-bounds-consistentᶜ p₂⊢ q₂⊢)
lower-bounds-consistentᶜ {Γ = Γ} (⊑-∀ p⊢) (⊑-∀ q⊢) =
  ∀-~-∀ (lower-bounds-consistentᶜ {Γ = both ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} {C = C} (⊑-∀ p⊢) (⊑-ν wfC q⊢) =
  ∀-~-B
    (subst (λ n → WfTy n 0 C) (length-rightICtx Γ) wfC)
    (lower-bounds-consistentᶜ {Γ = left ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} {B = B} (⊑-ν wfB p⊢) (⊑-∀ q⊢) =
  A-~-∀
    (subst (λ n → WfTy n 0 B) (length-leftICtx Γ) wfB)
    (lower-bounds-consistentᶜ {Γ = right ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} (⊑-ν wfB p⊢) (⊑-ν wfC q⊢) =
  drop-neither-~ (lower-bounds-consistentᶜ {Γ = neither ∷ Γ} p⊢ q⊢)

lower-bounds-consistent :
  ∀ {Δ A B C p q} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  0 ∣ plains Δ [] ⊢ q ⦂ A ⊑ C →
  boths Δ [] ⊢ B ~ C
lower-bounds-consistent
    {Δ = Δ} {A = A} {B = B} {C = C} {p = p} {q = q} p⊢ q⊢ =
  lower-bounds-consistentᶜ {Γ = boths Δ []}
    (subst (λ Φ → 0 ∣ Φ ⊢ p ⦂ A ⊑ B) (sym (leftICtx-boths[] Δ)) p⊢)
    (subst (λ Φ → 0 ∣ Φ ⊢ q ⦂ A ⊑ C) (sym (rightICtx-boths[] Δ)) q⊢)

trans-⊑-plains :
  ∀ {Δ A B C p q} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  0 ∣ plains Δ [] ⊢ q ⦂ B ⊑ C →
  Σ[ r ∈ Imp ] 0 ∣ plains Δ [] ⊢ r ⦂ A ⊑ C
trans-⊑-plains = ⊑-trans

app-consistency :
  ∀ {Δ A A′ B B′ p q} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  boths Δ [] ⊢ A ~ A′ →
  0 ∣ plains Δ [] ⊢ q ⦂ A′ ⊑ B′ →
  boths Δ [] ⊢ B ~ B′
app-consistency p⊢ A~A′ q⊢ with coerce-wt-plains A~A′
app-consistency p⊢ A~A′ q⊢ | C , C⊑A , C⊑A′
    with trans-⊑-plains C⊑A p⊢ | trans-⊑-plains C⊑A′ q⊢
app-consistency p⊢ A~A′ q⊢ | C , C⊑A , C⊑A′
    | r , C⊑B | s , C⊑B′ =
  lower-bounds-consistent C⊑B C⊑B′

arrow-app-sgg :
  ∀ {Δ Γ L′ M′ A B A′ D C pF pArg} →
  Δ ∣ rightGCtx Γ ⊢ L′ ⦂ D →
  0 ∣ plains Δ [] ⊢ pF ⦂ (A ⇒ B) ⊑ D →
  Δ ∣ rightGCtx Γ ⊢ M′ ⦂ C →
  0 ∣ plains Δ [] ⊢ pArg ⦂ A′ ⊑ C →
  boths Δ [] ⊢ A ~ A′ →
  SGGResult Δ Γ (L′ · M′) B
arrow-app-sgg L′⊢ (⊑-⇒ pA⊢ pB⊢) M′⊢ pArg⊢ A~A′ =
  _ , _ ,
  ⊢· L′⊢ M′⊢ (app-consistency pA⊢ A~A′ pArg⊢) ,
  pB⊢
arrow-app-sgg L′⊢ (⊑-★ ★⇒★ (⊑-⇒ pA⊢ pB⊢)) M′⊢ pArg⊢ A~A′ =
  ★ , _ ,
  ⊢·★ L′⊢ M′⊢ (app-consistency pArg⊢ (boths-sym A~A′) pA⊢) ,
  pB⊢

star-app-sgg :
  ∀ {Δ Γ L′ M′ A′ D C pF pArg} →
  Δ ∣ rightGCtx Γ ⊢ L′ ⦂ D →
  0 ∣ plains Δ [] ⊢ pF ⦂ ★ ⊑ D →
  Δ ∣ rightGCtx Γ ⊢ M′ ⦂ C →
  0 ∣ plains Δ [] ⊢ pArg ⦂ A′ ⊑ C →
  boths Δ [] ⊢ A′ ~ ★ →
  SGGResult Δ Γ (L′ · M′) ★
star-app-sgg L′⊢ ⊑-★★ M′⊢ pArg⊢ A′~★ =
  ★ , ★⊑★ ,
  ⊢·★ L′⊢ M′⊢ (app-consistency pArg⊢ A′~★ ⊑-★★) ,
  ⊑-★★
star-app-sgg L′⊢ (⊑-★ (｀ α) ()) M′⊢ pArg⊢ A′~★
star-app-sgg L′⊢ (⊑-★ (‵ ι) ()) M′⊢ pArg⊢ A′~★
star-app-sgg L′⊢ (⊑-★ ★⇒★ ()) M′⊢ pArg⊢ A′~★

DropRenameGTypingResult : TyCtx → Ctx → GTerm → Ty → Set
DropRenameGTypingResult Δ Γ M B′ =
  Σ[ B ∈ Ty ] ((B′ ≡ ⇑ᵗ B) × (Δ ∣ Γ ⊢ M ⦂ B))

DropRenameGTypingAtResult : CCtx → CCtx → Ctx → GTerm → Ty → Set
DropRenameGTypingAtResult Φ Γᶜ Γ M B′ =
  Σ[ B ∈ Ty ]
    ((B′ ≡ renameᵗ (raiseVarFrom (length Φ)) B) ×
     (length (Φ ++ Γᶜ) ∣ Γ ⊢ M ⦂ B))

unmap∋-renameCtxAt :
  ∀ k {Γ x A′} →
  renameCtxAt k Γ ∋ x ⦂ A′ →
  Σ[ A ∈ Ty ] (A′ ≡ renameᵗ (raiseVarFrom k) A) × (Γ ∋ x ⦂ A)
unmap∋-renameCtxAt k {Γ = A ∷ Γ} Z = A , refl , Z
unmap∋-renameCtxAt k {Γ = A ∷ Γ} (S x∈)
    with unmap∋-renameCtxAt k x∈
unmap∋-renameCtxAt k {Γ = A ∷ Γ} (S x∈) | B , eq , x∈′ =
  B , eq , S x∈′

drop-renameᵗᴳ-at-wt :
  ∀ {d Φ Γᶜ Γ M B′} →
  length (Φ ++ d ∷ Γᶜ) ∣ renameCtxAt (length Φ) Γ ⊢
    renameᵗᴳ (raiseVarFrom (length Φ)) M ⦂ B′ →
  DropRenameGTypingAtResult Φ Γᶜ Γ M B′
drop-renameᵗᴳ-at-wt {Φ = Φ} {M = ` x} (⊢` x∈)
    with unmap∋-renameCtxAt (length Φ) x∈
drop-renameᵗᴳ-at-wt {Φ = Φ} {M = ` x} (⊢` x∈)
    | A , eq , x∈′ =
  A , eq , ⊢` x∈′
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = ƛ A ⇒ M} (⊢ƛ wfA M⊢)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = ƛ A ⇒ M} (⊢ƛ wfA M⊢)
    | B , refl , M⊢′ =
  A ⇒ B , refl ,
  ⊢ƛ (drop-boths-WfTy {d = d} {Φ = Φ} {Γ = Γᶜ} wfA) M⊢′
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢· L⊢ M⊢ A~A′)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} L⊢
       | drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢· L⊢ M⊢ A~A′)
    | A ⇒ B , refl , L⊢′ | A′ , refl , M⊢′ =
  B , refl ,
  ⊢· L⊢′ M⊢′ (drop-boths-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} A~A′)
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢·★ L⊢ M⊢ A~★)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} L⊢
       | drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L · M} (⊢·★ L⊢ M⊢ A~★)
    | ★ , refl , L⊢′ | A , refl , M⊢′ =
  ★ , refl ,
  ⊢·★ L⊢′ M⊢′ (drop-boths-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} A~★)
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} {Γ = Γ}
    {M = Λ M} (⊢Λ vM M⊢)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = both ∷ Φ} {Γᶜ = Γᶜ}
      {Γ = ⤊ᵗ Γ} {M = M}
      (subst
        (λ N → length ((both ∷ Φ) ++ d ∷ Γᶜ) ∣
          renameCtxAt (suc (length Φ)) (⤊ᵗ Γ) ⊢ N ⦂ _)
        (renameᵗᴳ-cong (raise-ext (length Φ)) M)
        (subst
          (λ Γ′ → length ((both ∷ Φ) ++ d ∷ Γᶜ) ∣ Γ′ ⊢
            renameᵗᴳ (extᵗ (raiseVarFrom (length Φ))) M ⦂ _)
          (sym (renameCtxAt-⤊ᵗ (length Φ) Γ))
          M⊢))
drop-renameᵗᴳ-at-wt {Φ = Φ} {M = Λ M} (⊢Λ vM M⊢)
    | B , eqB , M⊢′ =
  `∀ B ,
  cong `∀ (trans eqB (sym (rename-raise-ext (length Φ) B))) ,
  ⊢Λ (renameᵗᴳ-value-inv vM) M⊢′
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = M `[ T ]} (⊢• M⊢ wfB wfT)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = M `[ T ]} (⊢• M⊢ wfB wfT)
    | `∀ B , refl , M⊢′ =
  B [ T ]ᵗ ,
  sym (renameᵗ-[]ᵗ (raiseVarFrom (length Φ)) B T) ,
  ⊢• M⊢′
    (drop-boths-WfTy {d = d} {Φ = both ∷ Φ} {Γ = Γᶜ} {A = B}
      (subst (λ B′ → WfTy (suc (length (Φ ++ d ∷ Γᶜ))) 0 B′)
        (rename-raise-ext (length Φ) B)
        wfB))
    (drop-boths-WfTy {d = d} {Φ = Φ} {Γ = Γᶜ} wfT)
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = M `[ T ]} (⊢•★ M⊢ wfT)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = M `[ T ]} (⊢•★ M⊢ wfT)
    | ★ , refl , M⊢′ =
  ★ , refl ,
  ⊢•★ M⊢′
    (renameᵗ-inv-WfTy (raiseVarFrom-<-inv (length Φ)) wfT)
drop-renameᵗᴳ-at-wt {Φ = Φ} {M = $ κ} (⊢$ κ) =
  constTy κ , constTy-renameᵗ (raiseVarFrom (length Φ)) κ , ⊢$ κ
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L ⊕[ op ] M} (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} L⊢
       | drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ} M⊢
drop-renameᵗᴳ-at-wt {d = d} {Φ = Φ} {Γᶜ = Γᶜ}
    {M = L ⊕[ op ] M} (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | A , refl , L⊢′ | B , refl , M⊢′ =
  ‵ `ℕ , refl ,
  ⊢⊕ L⊢′ (drop-boths-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} A~ℕ) op
      M⊢′ (drop-boths-at-~ {d = d} {Φ = Φ} {Γ = Γᶜ} B~ℕ)

drop-renameᵗᴳ-wt :
  ∀ {Δ Γ M B′} →
  suc Δ ∣ ⤊ᵗ Γ ⊢ renameᵗᴳ suc M ⦂ B′ →
  DropRenameGTypingResult Δ Γ M B′
drop-renameᵗᴳ-wt {M = ` x} (⊢` x∈) with unmap∋-⤊ᵗ x∈
drop-renameᵗᴳ-wt {M = ` x} (⊢` x∈) | A , eq , x∈′ =
  A , eq , ⊢` x∈′
drop-renameᵗᴳ-wt {M = ƛ A ⇒ M} (⊢ƛ wfA M⊢)
    with drop-renameᵗᴳ-wt M⊢
drop-renameᵗᴳ-wt {M = ƛ A ⇒ M} (⊢ƛ wfA M⊢)
    | B , refl , M⊢′ =
  A ⇒ B , refl ,
  ⊢ƛ (drop-⇑ᵗ-WfTy-plains wfA) M⊢′
drop-renameᵗᴳ-wt {M = L · M} (⊢· L⊢ M⊢ A~A′)
    with drop-renameᵗᴳ-wt L⊢ | drop-renameᵗᴳ-wt M⊢
drop-renameᵗᴳ-wt {M = L · M} (⊢· L⊢ M⊢ A~A′)
    | A ⇒ B , refl , L⊢′ | A′ , refl , M⊢′ =
  B , refl , ⊢· L⊢′ M⊢′ (drop-both-~ A~A′)
drop-renameᵗᴳ-wt {M = L · M} (⊢·★ L⊢ M⊢ A~★)
    with drop-renameᵗᴳ-wt L⊢ | drop-renameᵗᴳ-wt M⊢
drop-renameᵗᴳ-wt {M = L · M} (⊢·★ L⊢ M⊢ A~★)
    | ★ , refl , L⊢′ | A , refl , M⊢′ =
  ★ , refl , ⊢·★ L⊢′ M⊢′ (drop-both-~ A~★)
drop-renameᵗᴳ-wt {Δ = Δ} {Γ = Γ} {M = Λ M} (⊢Λ vM M⊢)
    with drop-renameᵗᴳ-at-wt {d = both} {Φ = both ∷ []}
      {Γᶜ = boths Δ []} {Γ = ⤊ᵗ Γ} {M = M}
      (cong-⊢ᴳ⦂
        (cong suc (cong suc (sym (length-boths[] Δ))))
        (sym (trans (renameCtxAt-⤊ᵗ zero Γ)
                    (cong ⤊ᵗ (renameCtxAt-zero Γ))))
        (renameᵗᴳ-cong (raise-ext zero) M)
        refl
        M⊢)
drop-renameᵗᴳ-wt {M = Λ M} (⊢Λ vM M⊢) | B , eqB , M⊢′ =
  `∀ B , cong `∀ (trans eqB (sym (rename-raise-ext zero B))) ,
  ⊢Λ (renameᵗᴳ-value-inv vM)
    (cong-⊢ᴳ⦂ (cong suc (length-boths[] _)) refl refl refl M⊢′)
drop-renameᵗᴳ-wt {Δ = Δ} {Γ = Γ} {M = M `[ T ]} M[T]⊢
    with drop-renameᵗᴳ-at-wt {d = both} {Φ = []}
      {Γᶜ = boths Δ []} {Γ = Γ} {M = M `[ T ]}
      (cong-⊢ᴳ⦂
        (cong suc (sym (length-boths[] Δ)))
        (sym (renameCtxAt-zero Γ))
        refl
        refl
        M[T]⊢)
drop-renameᵗᴳ-wt {Δ = Δ} {M = M `[ T ]} M[T]⊢
    | B , eqB , M[T]⊢′ =
  B , eqB , cong-⊢ᴳ⦂ (length-boths[] Δ) refl refl refl M[T]⊢′
drop-renameᵗᴳ-wt {M = $ κ} (⊢$ κ) = constTy κ , constTy-⇑ᵗ κ , ⊢$ κ
drop-renameᵗᴳ-wt {M = L ⊕[ op ] M} (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with drop-renameᵗᴳ-wt L⊢ | drop-renameᵗᴳ-wt M⊢
drop-renameᵗᴳ-wt {M = L ⊕[ op ] M} (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | A , refl , L⊢′ | B , refl , M⊢′ =
  ‵ `ℕ , refl ,
  ⊢⊕ L⊢′ (drop-both-~ A~ℕ) op M⊢′ (drop-both-~ B~ℕ)

change-plain-to-ν-ν∋ :
  ∀ {Δ Φ X} →
  (Φ ++ (plain ∷ plains Δ [])) ∋ X ∶ ν-bound →
  (Φ ++ (ν-bound ∷ plains Δ [])) ∋ X ∶ ν-bound
change-plain-to-ν-ν∋ {Φ = []} {X = zero} ()
change-plain-to-ν-ν∋ {Φ = []} {X = suc X}
    (Imprecision.there x∈) =
  Imprecision.there x∈
change-plain-to-ν-ν∋ {Φ = plain ∷ Φ} {X = zero} ()
change-plain-to-ν-ν∋ {Φ = ν-bound ∷ Φ} {X = zero}
    Imprecision.here =
  Imprecision.here
change-plain-to-ν-ν∋ {Φ = m ∷ Φ} {X = suc X}
    (Imprecision.there x∈) =
  Imprecision.there (change-plain-to-ν-ν∋ {Φ = Φ} x∈)

change-plain-to-ν-raised∋ :
  ∀ {Δ Φ X m} →
  (Φ ++ (plain ∷ plains Δ [])) ∋
    raiseVarFrom (length Φ) X ∶ m →
  (Φ ++ (ν-bound ∷ plains Δ [])) ∋
    raiseVarFrom (length Φ) X ∶ m
change-plain-to-ν-raised∋ {Φ = []} (Imprecision.there x∈) =
  Imprecision.there x∈
change-plain-to-ν-raised∋ {Φ = m₀ ∷ Φ} {X = zero}
    Imprecision.here =
  Imprecision.here
change-plain-to-ν-raised∋ {Φ = m₀ ∷ Φ} {X = suc X}
    (Imprecision.there x∈) =
  Imprecision.there
    (change-plain-to-ν-raised∋ {Φ = Φ} {X = X} x∈)

length-plain-to-ν :
  ∀ Δ (Φ : ICtx) →
  length (Φ ++ (plain ∷ plains Δ [])) ≡
  length (Φ ++ (ν-bound ∷ plains Δ []))
length-plain-to-ν Δ [] = refl
length-plain-to-ν Δ (m ∷ Φ) = cong suc (length-plain-to-ν Δ Φ)

plain-to-ν-raised-at-⊑ :
  ∀ {Δ Φ A B p} →
  0 ∣ Φ ++ (plain ∷ plains Δ []) ⊢ p ⦂ A ⊑
    renameᵗ (raiseVarFrom (length Φ)) B →
  Σ[ q ∈ Imp ]
    0 ∣ Φ ++ (ν-bound ∷ plains Δ []) ⊢ q ⦂ A ⊑
      renameᵗ (raiseVarFrom (length Φ)) B
plain-to-ν-raised-at-⊑ {B = ★} ⊑-★★ = ★⊑★ , ⊑-★★
plain-to-ν-raised-at-⊑ {B = ★} (⊑-★ν xν) =
  X⊑★ _ , ⊑-★ν (change-plain-to-ν-ν∋ xν)
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = ★} (⊑-★ {G = G} g p⊢)
    with plain-to-ν-raised-at-⊑ {Φ = Φ} {B = G}
      (cong-⊢⊑ refl (sym (renameᵗ-ground-id g)) p⊢)
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = ★} (⊑-★ {G = G} g p⊢)
    | q , q⊢ =
  A⊑★ q , ⊑-★ g (cong-⊢⊑ refl (renameᵗ-ground-id g) q⊢)
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = ＇ X} (⊑-＇ x∈) =
  X⊑X (raiseVarFrom (length Φ) X) ,
  ⊑-＇ (change-plain-to-ν-raised∋ {Φ = Φ} x∈)
plain-to-ν-raised-at-⊑ {Δ = Δ} {Φ = Φ} {B = ｀ α} (⊑-｀ wfα) =
  α⊑α α ,
  ⊑-｀ (subst (λ n → WfTy n 0 (｀ α)) (length-plain-to-ν Δ Φ) wfα)
plain-to-ν-raised-at-⊑ {B = ‵ ι} ⊑-‵ = ι⊑ι ι , ⊑-‵
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = A ⇒ B} (⊑-⇒ p⊢ q⊢)
    with plain-to-ν-raised-at-⊑ {Φ = Φ} {B = A} p⊢
       | plain-to-ν-raised-at-⊑ {Φ = Φ} {B = B} q⊢
plain-to-ν-raised-at-⊑ {B = A ⇒ B} (⊑-⇒ p⊢ q⊢)
    | p , p⊢′ | q , q⊢′ =
  A⇒B⊑A′⇒B′ p q , ⊑-⇒ p⊢′ q⊢′
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = `∀ B} (⊑-∀ p⊢)
    with plain-to-ν-raised-at-⊑ {Φ = plain ∷ Φ} {B = B}
      (cong-⊢⊑ refl (rename-raise-ext (length Φ) B) p⊢)
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = `∀ B} (⊑-∀ p⊢)
    | q , q⊢ =
  `∀A⊑∀B q ,
  cong-⊢⊑ refl (cong `∀ (sym (rename-raise-ext (length Φ) B)))
    (⊑-∀ q⊢)
plain-to-ν-raised-at-⊑ {Δ = Δ} {Φ = Φ} {B = B}
    (⊑-ν {A = A} wfB p⊢)
    with plain-to-ν-raised-at-⊑ {Φ = ν-bound ∷ Φ} {B = ⇑ᵗ B}
      (cong-⊢⊑ refl (sym (rename-raise-⇑ᵗ (length Φ) B)) p⊢)
plain-to-ν-raised-at-⊑ {Δ = Δ} {Φ = Φ} {B = B}
    (⊑-ν {A = A} wfB p⊢)
    | q , q⊢ =
  `∀A⊑B (renameᵗ (raiseVarFrom (length Φ)) B) q ,
  ⊑-ν
    (subst (λ n → WfTy n 0 (renameᵗ (raiseVarFrom (length Φ)) B))
      (length-plain-to-ν Δ Φ) wfB)
    (cong-⊢⊑ refl (rename-raise-⇑ᵗ (length Φ) B) q⊢)

plain-to-ν-raised-⊑ :
  ∀ {Δ A B p} →
  0 ∣ plain ∷ plains Δ [] ⊢ p ⦂ A ⊑ ⇑ᵗ B →
  Σ[ q ∈ Imp ] 0 ∣ ν-bound ∷ plains Δ [] ⊢ q ⦂ A ⊑ ⇑ᵗ B
plain-to-ν-raised-⊑ p⊢ = plain-to-ν-raised-at-⊑ {Φ = []} p⊢

tysubst-right-at-⊑ :
  ∀ k {Δ A T T′ pT} →
  WfTy (suc (k + Δ)) 0 A →
  0 ∣ plains Δ [] ⊢ pT ⦂ T ⊑ T′ →
  Σ[ p ∈ Imp ]
    0 ∣ plains (k + Δ) [] ⊢ p ⦂
      substᵗ (plainSubstVarFrom k T) A ⊑
      substᵗ (plainSubstVarFrom k T′) A
tysubst-right-at-⊑ zero {A = ＇ zero} (wfVar z<s) pT⊢ =
  _ , pT⊢
tysubst-right-at-⊑ zero {A = ＇ suc X} (wfVar (s<s X<Δ)) pT⊢ =
  reflImp (＇ X) , reflImp-wt-plains (wfVar X<Δ)
tysubst-right-at-⊑ (suc k) {A = ＇ zero} (wfVar z<s) pT⊢ =
  reflImp (＇ zero) , reflImp-wt-plains (wfVar z<s)
tysubst-right-at-⊑ (suc k) {A = ＇ suc X} (wfVar (s<s X<Δ)) pT⊢
    with tysubst-right-at-⊑ k (wfVar X<Δ) pT⊢
tysubst-right-at-⊑ (suc k) {A = ＇ suc X} (wfVar (s<s X<Δ)) pT⊢
    | p , p⊢ =
  renameImp suc p , wkImp-plains zero p⊢
tysubst-right-at-⊑ k {A = ｀ α} (wfSeal ()) pT⊢
tysubst-right-at-⊑ k {A = ‵ ι} wfBase pT⊢ =
  reflImp (‵ ι) , reflImp-wt-plains wfBase
tysubst-right-at-⊑ k {A = ★} wf★ pT⊢ =
  reflImp ★ , reflImp-wt-plains wf★
tysubst-right-at-⊑ k {A = A ⇒ B} (wf⇒ wfA wfB) pT⊢
    with tysubst-right-at-⊑ k wfA pT⊢
       | tysubst-right-at-⊑ k wfB pT⊢
tysubst-right-at-⊑ k {A = A ⇒ B} (wf⇒ wfA wfB) pT⊢
    | p , p⊢ | q , q⊢ =
  A⇒B⊑A′⇒B′ p q , ⊑-⇒ p⊢ q⊢
tysubst-right-at-⊑ k {A = `∀ A} (wf∀ wfA) pT⊢
    with tysubst-right-at-⊑ (suc k) wfA pT⊢
tysubst-right-at-⊑ k {A = `∀ A} (wf∀ wfA) pT⊢
    | p , p⊢ =
  `∀A⊑∀B p , ⊑-∀ p⊢

tysubst-right-⊑ :
  ∀ {Δ A T T′ pT} →
  WfTy (suc Δ) 0 A →
  0 ∣ plains Δ [] ⊢ pT ⦂ T ⊑ T′ →
  Σ[ p ∈ Imp ] 0 ∣ plains Δ [] ⊢ p ⦂ A [ T ]ᵗ ⊑ A [ T′ ]ᵗ
tysubst-right-⊑ wfA pT⊢ = tysubst-right-at-⊑ zero wfA pT⊢

⊑-tgt-wf-prefix :
  ∀ {Δ Φ A B p} →
  WfTy (length Φ) 0 A →
  0 ∣ Φ ++ plains Δ [] ⊢ p ⦂ A ⊑ B →
  WfTy (length Φ) 0 B
⊑-tgt-wf-prefix wf★ ⊑-★★ = wf★
⊑-tgt-wf-prefix wfA (⊑-★ν xν) = wf★
⊑-tgt-wf-prefix wfA (⊑-★ g p⊢) = wf★
⊑-tgt-wf-prefix (wfVar X<Φ) (⊑-＇ x∈) = wfVar X<Φ
⊑-tgt-wf-prefix (wfSeal ()) (⊑-｀ wfα)
⊑-tgt-wf-prefix wfBase ⊑-‵ = wfBase
⊑-tgt-wf-prefix {Δ = Δ} {Φ = Φ} (wf⇒ wfA wfB) (⊑-⇒ p⊢ q⊢) =
  wf⇒ (⊑-tgt-wf-prefix {Δ = Δ} {Φ = Φ} wfA p⊢)
       (⊑-tgt-wf-prefix {Δ = Δ} {Φ = Φ} wfB q⊢)
⊑-tgt-wf-prefix {Δ = Δ} {Φ = Φ} (wf∀ wfA) (⊑-∀ p⊢) =
  wf∀ (⊑-tgt-wf-prefix {Δ = Δ} {Φ = plain ∷ Φ} wfA p⊢)
⊑-tgt-wf-prefix {Δ = Δ} {Φ = Φ} (wf∀ wfA) (⊑-ν wfB p⊢) =
  drop-⇑ᵗ-WfTy-plains {Δ = length Φ}
    (⊑-tgt-wf-prefix {Δ = Δ} {Φ = ν-bound ∷ Φ} wfA p⊢)

⊑-tgt-wf-closed-plains :
  ∀ {Δ A B p} →
  WfTy 0 0 A →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  WfTy 0 0 B
⊑-tgt-wf-closed-plains wfA p⊢ =
  ⊑-tgt-wf-prefix {Φ = []} wfA p⊢

static-gradual-guarantee ⊑` (⊢` x∈) with lookup-leftᴳ-inv x∈
static-gradual-guarantee ⊑` (⊢` x∈) | B , p , p⊢ , hᴳ =
  B , p , ⊢` (lookup-rightᴳ hᴳ) , p⊢
static-gradual-guarantee {Γ = Γ}
    (⊑ƛ {A = A} {A′ = A′} {pA = pA} pA⊢ M⊑M′)
    (⊢ƛ wfA M⊢)
    with static-gradual-guarantee
      {Γ = (A , A′ , pA , pA⊢) ∷ Γ}
      M⊑M′ M⊢
static-gradual-guarantee
    (⊑ƛ {A′ = A′} {pA = pA} pA⊢ M⊑M′) (⊢ƛ wfA M⊢)
    | B′ , pB , M′⊢ , pB⊢ =
  A′ ⇒ B′ , A⇒B⊑A′⇒B′ pA pB ,
  ⊢ƛ (⊑-tgt-wf-plains pA⊢) M′⊢ ,
  ⊑-⇒ pA⊢ pB⊢
static-gradual-guarantee
    (⊑· L⊑L′ M⊑M′) (⊢· L⊢ M⊢ A~A′)
    with static-gradual-guarantee L⊑L′ L⊢
       | static-gradual-guarantee M⊑M′ M⊢
static-gradual-guarantee
    (⊑· L⊑L′ M⊑M′) (⊢· L⊢ M⊢ A~A′)
    | D , pF , L′⊢ , pF⊢ | C , pArg , M′⊢ , pArg⊢ =
  arrow-app-sgg L′⊢ pF⊢ M′⊢ pArg⊢ A~A′
static-gradual-guarantee
    (⊑· L⊑L′ M⊑M′) (⊢·★ L⊢ M⊢ A′~★)
    with static-gradual-guarantee L⊑L′ L⊢
       | static-gradual-guarantee M⊑M′ M⊢
static-gradual-guarantee
    (⊑· L⊑L′ M⊑M′) (⊢·★ L⊢ M⊢ A′~★)
    | D , pF , L′⊢ , pF⊢ | C , pArg , M′⊢ , pArg⊢ =
  star-app-sgg L′⊢ pF⊢ M′⊢ pArg⊢ A′~★
static-gradual-guarantee {Γ = Γ}
    (⊑Λ vM vM′ M⊑M′) (⊢Λ vM₀ M⊢)
    with static-gradual-guarantee
      {Γ = ⇑ᵗᴳPCtx Γ}
      M⊑M′
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (sym (leftGCtx-⇑ᵗᴳPCtx Γ)) M⊢)
static-gradual-guarantee {Γ = Γ} (⊑Λ vM vM′ M⊑M′) (⊢Λ vM₀ M⊢)
    | B′ , pB , M′⊢ , pB⊢ =
  `∀ B′ , `∀A⊑∀B pB ,
  ⊢Λ vM′
    (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
      (rightGCtx-⇑ᵗᴳPCtx Γ) M′⊢) ,
  ⊑-∀ pB⊢
static-gradual-guarantee {Γ = Γ}
    (⊑ΛL vM M⊑M′) (⊢Λ vM₀ M⊢)
    with static-gradual-guarantee
      {Γ = ⇑ᵗᴳPCtx Γ}
      M⊑M′
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (sym (leftGCtx-⇑ᵗᴳPCtx Γ)) M⊢)
static-gradual-guarantee {Δ = Δ} {Γ = Γ}
    (⊑ΛL vM M⊑M′) (⊢Λ vM₀ M⊢)
    | B′ , pB , M′↑⊢ , pB⊢
    with drop-renameᵗᴳ-wt
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
        (rightGCtx-⇑ᵗᴳPCtx Γ) M′↑⊢)
static-gradual-guarantee {Δ = Δ} {Γ = Γ}
    (⊑ΛL vM M⊑M′) (⊢Λ vM₀ M⊢)
    | B′ , pB , M′↑⊢ , pB⊢ | B , refl , M′⊢
    with plain-to-ν-raised-⊑ pB⊢
static-gradual-guarantee {Δ = Δ} {Γ = Γ}
    (⊑ΛL vM M⊑M′) (⊢Λ vM₀ M⊢)
    | B′ , pB , M′↑⊢ , pB⊢ | B , refl , M′⊢ | q , q⊢ =
  B , `∀A⊑B B q , M′⊢ ,
  ⊑-ν
    (subst (λ n → WfTy n 0 B) (sym (length-plains[] Δ))
      (drop-⇑ᵗ-WfTy-plains
        (subst (λ n → WfTy n 0 (⇑ᵗ B))
          (cong suc (length-plains[] Δ))
          (⊑-tgt-wf q⊢))))
    q⊢
static-gradual-guarantee {Δ = Δ}
    (⊑`[] {T′ = T′} M⊑M′ pT⊢) (⊢• {B = B} {T = T} M⊢ wfB wfT)
    with static-gradual-guarantee M⊑M′ M⊢
static-gradual-guarantee {Δ = Δ}
    (⊑`[] {T′ = T′} M⊑M′ pT⊢) (⊢• {B = B} {T = T} M⊢ wfB wfT)
    | ★ , A⊑★ p , M′⊢ , ⊑-★ g p⊢ =
  ★ , A⊑★ {!!} , ⊢•★ M′⊢ {!!} , ⊑-★ g {!!}
static-gradual-guarantee {Δ = Δ}
    (⊑`[] {T′ = T′} M⊑M′ pT⊢) (⊢• {B = B} {T = T} M⊢ wfB wfT)
    | `∀ C , `∀A⊑∀B p , M′⊢ , ⊑-∀ p⊢
    with ⊑-substᵗ-wt
           (singleTyEnv-TySubstWf-plains wfT)
           (singleTyEnv-ImpSubstWt wfT)
           p⊢
       | tysubst-right-⊑
           (subst (λ n → WfTy n 0 C) (cong suc (length-plains[] Δ))
             (⊑-tgt-wf p⊢))
           pT⊢
static-gradual-guarantee {Δ = Δ}
    (⊑`[] {T′ = T′} M⊑M′ pT⊢) (⊢• {B = B} {T = T} M⊢ wfB wfT)
    | `∀ C , `∀A⊑∀B p , M′⊢ , ⊑-∀ p⊢ | pBT⊢ | q , q⊢
    with trans-⊑-plains pBT⊢ q⊢
static-gradual-guarantee {Δ = Δ}
    (⊑`[] {T′ = T′} M⊑M′ pT⊢) (⊢• {B = B} {T = T} M⊢ wfB wfT)
    | `∀ C , `∀A⊑∀B p , M′⊢ , ⊑-∀ p⊢ | pBT⊢ | q , q⊢
    | r , r⊢ =
  C [ T′ ]ᵗ , r ,
  ⊢• M′⊢
    (subst (λ n → WfTy n 0 C) (cong suc (length-plains[] Δ))
      (⊑-tgt-wf p⊢))
    (⊑-tgt-wf-plains pT⊢) ,
  r⊢
static-gradual-guarantee {Δ = Δ}
    (⊑`[] {T′ = T′} M⊑M′ pT⊢) (⊢• {B = B} {T = T} M⊢ wfB wfT)
    | D , `∀A⊑B .D p , M′⊢ , ⊑-ν wfD p⊢ =
  D , {!!} , {!!} , {!!}
static-gradual-guarantee (⊑`[] M⊑M′ pT⊢) (⊢•★ M⊢ wfT)
    with static-gradual-guarantee M⊑M′ M⊢
static-gradual-guarantee (⊑`[] M⊑M′ pT⊢) (⊢•★ M⊢ wfT)
    | ★ , ★⊑★ , M′⊢ , ⊑-★★ =
  ★ , ★⊑★ , ⊢•★ M′⊢ (⊑-tgt-wf-closed-plains wfT pT⊢) ,
  ⊑-★★
static-gradual-guarantee (⊑`[] M⊑M′ pT⊢) (⊢•★ M⊢ wfT)
    | ★ , A⊑★ p , M′⊢ , ⊑-★ g p⊢ =
  ★ , ★⊑★ , ⊢•★ M′⊢ (⊑-tgt-wf-closed-plains wfT pT⊢) ,
  ⊑-★★
static-gradual-guarantee
    (⊑`[]L M⊑M′ wfT) (⊢• {B = B} {T = T} M⊢ wfB wfT′)
    with static-gradual-guarantee M⊑M′ M⊢
static-gradual-guarantee
    (⊑`[]L M⊑M′ wfT) (⊢• {B = B} {T = T} M⊢ wfB wfT′)
    | ★ , A⊑★ p , M′⊢ , ⊑-★ g p⊢ =
  ★ , A⊑★ {!!} , M′⊢ , ⊑-★ g {!!}
static-gradual-guarantee
    (⊑`[]L M⊑M′ wfT) (⊢• {B = B} {T = T} M⊢ wfB wfT′)
    | `∀ C , `∀A⊑∀B p , M′⊢ , ⊑-∀ p⊢ =
  `∀ C , {!!} , M′⊢ , {!!}
static-gradual-guarantee
    (⊑`[]L M⊑M′ wfT) (⊢• {B = B} {T = T} M⊢ wfB wfT′)
    | D , `∀A⊑B .D p , M′⊢ , ⊑-ν wfD p⊢ =
  D , {!!} , M′⊢ , {!!}
static-gradual-guarantee (⊑`[]L M⊑M′ wfT) (⊢•★ M⊢ wfT′) =
  static-gradual-guarantee M⊑M′ M⊢
static-gradual-guarantee ⊑$ (⊢$ (κℕ n)) =
  ‵ `ℕ , ι⊑ι `ℕ , ⊢$ (κℕ n) , ⊑-‵
static-gradual-guarantee
    (⊑⊕ L⊑L′ M⊑M′) (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with static-gradual-guarantee L⊑L′ L⊢
       | static-gradual-guarantee M⊑M′ M⊢
static-gradual-guarantee
    (⊑⊕ L⊑L′ M⊑M′) (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | C , pL , L′⊢ , pL⊢ | D , pM , M′⊢ , pM⊢ =
  ‵ `ℕ , ι⊑ι `ℕ ,
  ⊢⊕ L′⊢ (app-consistency pL⊢ A~ℕ ⊑-‵) op
      M′⊢ (app-consistency pM⊢ B~ℕ ⊑-‵) ,
  ⊑-‵

∀★-~-★ :
  ∀ {Δ} →
  boths Δ [] ⊢ `∀ ★ ~ ★
∀★-~-★ {Δ = Δ} = ∀-~-B {Γ = boths Δ []} wf★ ★-~-★

compile :
  ∀ {Δ Γ M A} →
  Δ ∣ Γ ⊢ M ⦂ A →
  Σ[ N ∈ Term ] Δ ∣ 0 ∣ [] ∣ Γ ⊢ᵀ N ⦂ A

compile-value :
  ∀ {Δ Γ M A} →
  (vM : Value M) →
  (M⊢ : Δ ∣ Γ ⊢ M ⦂ A) →
  Valueᵀ (proj₁ (compile M⊢))

compile (⊢` x∈) =
  `ᵀ _ , ⊢ᵀ` x∈
compile (⊢ƛ wfA M⊢) with compile M⊢
compile (⊢ƛ wfA M⊢) | N , N⊢ =
  ƛᵀ _ ⇒ N , ⊢ᵀƛ wfA N⊢
compile (⊢· L⊢ M⊢ A~A′)
    with compile L⊢ | compile M⊢ | coerce-wt-plains A~A′
compile (⊢· L⊢ M⊢ A~A′)
    | L′ , L′⊢ | M′ , M′⊢ | B , p⊒⊢ , p⊑⊢ =
  L′ ·ᵀ ((M′ ⇓ᵀ coerce-⊑ A~A′) ⇑ᵀ coerce-⊒ A~A′) ,
  ⊢ᵀ· L′⊢ (⊢ᵀup p⊒⊢ (⊢ᵀdown p⊑⊢ M′⊢))
compile (⊢·★ L⊢ M⊢ A′~★)
    with compile L⊢ | compile M⊢
       | coerce-wt-plains (A-~-★ ★⇒★ (⇒-~-⇒ A′~★ ★-~-★))
compile (⊢·★ L⊢ M⊢ A′~★)
    | L′ , L′⊢ | M′ , M′⊢ | B , p⊒⊢ , p⊑⊢ =
  ((L′ ⇓ᵀ coerce-⊑ (A-~-★ ★⇒★ (⇒-~-⇒ A′~★ ★-~-★)))
    ⇑ᵀ coerce-⊒ (A-~-★ ★⇒★ (⇒-~-⇒ A′~★ ★-~-★))) ·ᵀ M′ ,
  ⊢ᵀ· (⊢ᵀup p⊒⊢ (⊢ᵀdown p⊑⊢ L′⊢)) M′⊢
compile (⊢Λ vM M⊢) with compile M⊢ | compile-value vM M⊢
compile (⊢Λ vM M⊢) | N , N⊢ | vN =
  Λᵀ N , ⊢ᵀΛ vN N⊢
compile (⊢• M⊢ wfB wfT) with compile M⊢
compile (⊢• {B = B} {T = T} M⊢ wfB wfT) | M′ , M′⊢ =
  M′ ⦂∀ᵀ B [ T ] , ⊢ᵀ• M′⊢ wfB wfT
compile {Δ = Δ} (⊢•★ M⊢ wfT)
    with compile M⊢ | coerce-wt-plains (∀★-~-★ {Δ = Δ})
compile {Δ = Δ} (⊢•★ {T = T} M⊢ wfT)
    | M′ , M′⊢ | B , p⊒⊢ , p⊑⊢ =
  ((M′ ⇓ᵀ coerce-⊑ (∀★-~-★ {Δ = Δ}))
    ⇑ᵀ coerce-⊒ (∀★-~-★ {Δ = Δ})) ⦂∀ᵀ ★ [ T ] ,
  ⊢ᵀ• (⊢ᵀup p⊒⊢ (⊢ᵀdown p⊑⊢ M′⊢)) wf★
    (WfTy-closed-weakenᵗ Δ wfT)
compile (⊢$ κ) =
  $ᵀ κ , ⊢ᵀ$ κ
compile (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with compile L⊢ | compile M⊢ | coerce-wt-plains A~ℕ
       | coerce-wt-plains B~ℕ
compile (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L′ , L′⊢ | M′ , M′⊢ | BL , pL⊒⊢ , pL⊑⊢
    | BM , pM⊒⊢ , pM⊑⊢ =
  ((L′ ⇓ᵀ coerce-⊒ A~ℕ) ⇑ᵀ coerce-⊑ A~ℕ) ⊕ᵀ[ op ]
    ((M′ ⇓ᵀ coerce-⊒ B~ℕ) ⇑ᵀ coerce-⊑ B~ℕ) ,
  ⊢ᵀ⊕ (⊢ᵀup pL⊑⊢ (⊢ᵀdown pL⊒⊢ L′⊢)) op
       (⊢ᵀup pM⊑⊢ (⊢ᵀdown pM⊒⊢ M′⊢))

compile-value (ƛ A ⇒ M) (⊢ƛ wfA M⊢) = ƛᵀ A ⇒ proj₁ (compile M⊢)
compile-value ($ κ) (⊢$ .κ) = $ᵀ κ
compile-value (Λ M) (⊢Λ vM M⊢) = Λᵀ proj₁ (compile M⊢)
