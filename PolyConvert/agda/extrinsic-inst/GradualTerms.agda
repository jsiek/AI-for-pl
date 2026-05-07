module GradualTerms where

-- File Charter:
--   * Extrinsic term syntax and typing judgment for Gradually Typed System F (GTSF).

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; zero; suc; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision
  using
    ( plains
    ; plain
    ; ν-bound
    ; _∋_∶_
    ; _∣_⊢_⦂_⊑_
    ; _∣_⊢_⦂_⊒_
    ; Imp
    ; ★⊑★
    ; renameImp
    ; ι⊑ι
    ; A⇒B⊑A′⇒B′
    ; `∀A⊑∀B
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
open import Terms using (Const; Prim; constTy; κℕ)
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
open import proof.ConsistencyCoerce using (coerce-⊒; coerce-⊑; coerce-wt)
open import proof.ImprecisionCompose using (⊑-trans)
open import proof.PreservationBetaUpNu
  using (raiseVarFrom; rename-raise-ext; rename-raise-⇑ᵗ)
open import proof.PreservationTermSubst using (wkImp-plains)

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
     → WfTy Δ 0 T
     → Δ ∣ Γ ⊢ (M `[ T ]) ⦂ ★

  ⊢$ : ∀ (κ : Const)
     → Δ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M A B}
     → Δ ∣ Γ ⊢ L ⦂ A → boths Δ [] ⊢ A ~ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Γ ⊢ M ⦂ B → boths Δ [] ⊢ B ~ (‵ `ℕ)
     → Δ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

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

length-plains[] :
  ∀ Δ →
  length (plains Δ []) ≡ Δ
length-plains[] zero = refl
length-plains[] (suc Δ) = cong suc (length-plains[] Δ)

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
  SGGResult Δ Γ M′ A

------------------------------------------------------------------------
-- Compilation to explicit casts
------------------------------------------------------------------------

coerce-wt-plains :
  ∀ {Δ A C} →
  (A~C : boths Δ [] ⊢ A ~ C) →
  ∃[ B ]
    ((0 ∣ plains Δ [] ⊢ coerce-⊒ A~C ⦂ A ⊒ B) ×
     (0 ∣ plains Δ [] ⊢ coerce-⊑ A~C ⦂ B ⊑ C))
coerce-wt-plains {Δ = Δ} A~C with coerce-wt A~C
coerce-wt-plains {Δ = Δ} A~C | B , p⊒⊢ , p⊑⊢
  rewrite leftICtx-boths[] Δ | rightICtx-boths[] Δ =
  B , p⊒⊢ , p⊑⊢

cong-~ :
  ∀ {Γ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Γ ⊢ A ~ B →
  Γ ⊢ A′ ~ B′
cong-~ refl refl h = h

renameᵗ-ground-id :
  ∀ {ρ G} →
  Ground G →
  renameᵗ ρ G ≡ G
renameᵗ-ground-id (｀ α) = refl
renameᵗ-ground-id (‵ ι) = refl
renameᵗ-ground-id ★⇒★ = refl

drop∋ᶜ-neither :
  ∀ {Φ Γ X m} →
  (Φ ++ neither ∷ Γ) ∋ᶜ raiseVarFrom (length Φ) X ∶ m →
  (Φ ++ Γ) ∋ᶜ X ∶ m
drop∋ᶜ-neither {Φ = []} (there x∈) = x∈
drop∋ᶜ-neither {Φ = m₀ ∷ Φ} {X = zero} here = here
drop∋ᶜ-neither {Φ = m₀ ∷ Φ} {X = suc X} (there x∈) =
  there (drop∋ᶜ-neither {Φ = Φ} x∈)

drop<-raise :
  ∀ {Φ Γ X} →
  raiseVarFrom (length Φ) X < length (Φ ++ neither ∷ Γ) →
  X < length (Φ ++ Γ)
drop<-raise {Φ = []} (s<s X<Γ) = X<Γ
drop<-raise {Φ = m ∷ Φ} {X = zero} z<s = z<s
drop<-raise {Φ = m ∷ Φ} {X = suc X} (s<s X<Γ) =
  s<s (drop<-raise {Φ = Φ} X<Γ)

raiseVarFrom-injective :
  ∀ k {X Y} →
  raiseVarFrom k X ≡ raiseVarFrom k Y →
  X ≡ Y
raiseVarFrom-injective zero eq = suc-injective eq
raiseVarFrom-injective (suc k) {zero} {zero} eq = refl
raiseVarFrom-injective (suc k) {zero} {suc Y} ()
raiseVarFrom-injective (suc k) {suc X} {zero} ()
raiseVarFrom-injective (suc k) {suc X} {suc Y} eq =
  cong suc (raiseVarFrom-injective k (suc-injective eq))

drop-neither-WfTy :
  ∀ {Φ Γ A} →
  WfTy (length (Φ ++ neither ∷ Γ)) 0
    (renameᵗ (raiseVarFrom (length Φ)) A) →
  WfTy (length (Φ ++ Γ)) 0 A
drop-neither-WfTy {Φ = Φ} {Γ = Γ} {A = ＇ X} (wfVar X<Γ) =
  wfVar (drop<-raise {Φ = Φ} {Γ = Γ} {X = X} X<Γ)
drop-neither-WfTy {A = ｀ α} (wfSeal α<Ψ) = wfSeal α<Ψ
drop-neither-WfTy {A = ‵ ι} wfBase = wfBase
drop-neither-WfTy {A = ★} wf★ = wf★
drop-neither-WfTy {Φ = Φ} {Γ = Γ} {A = A ⇒ B} (wf⇒ wfA wfB) =
  wf⇒ (drop-neither-WfTy {Φ = Φ} {Γ = Γ} {A = A} wfA)
       (drop-neither-WfTy {Φ = Φ} {Γ = Γ} {A = B} wfB)
drop-neither-WfTy {Φ = Φ} {Γ = Γ} {A = `∀ A} (wf∀ wfA) =
  wf∀
    (drop-neither-WfTy {Φ = both ∷ Φ} {Γ = Γ} {A = A}
      (subst (λ B → WfTy (length ((both ∷ Φ) ++ neither ∷ Γ)) 0 B)
        (rename-raise-ext (length Φ) A)
        wfA))

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

drop-neither-at-X-suc :
  ∀ {m Φ Γ X Y} →
  (m ∷ Φ) ++ neither ∷ Γ ⊢
    ＇ suc (raiseVarFrom (length Φ) X) ~
    ＇ suc (raiseVarFrom (length Φ) Y) →
  (m ∷ Φ) ++ Γ ⊢ ＇ suc X ~ ＇ suc Y
drop-neither-at-X-suc {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
    with var-var-~-inj h
drop-neither-at-X-suc {m = m} {Φ = Φ} {Γ = Γ} {X = X} h | eq , x∈
    with raiseVarFrom-injective (length Φ) (suc-injective eq)
drop-neither-at-X-suc {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
    | eq , x∈ | refl =
  X-~-X (drop∋ᶜ-neither {Φ = m ∷ Φ} {Γ = Γ} {X = suc X} x∈)

drop-neither-at-νL-suc :
  ∀ {m Φ Γ X} →
  (m ∷ Φ) ++ neither ∷ Γ ⊢
    ＇ suc (raiseVarFrom (length Φ) X) ~ ★ →
  (m ∷ Φ) ++ Γ ⊢ ＇ suc X ~ ★
drop-neither-at-νL-suc {m = m} {Φ = Φ} {Γ = Γ} {X = X} (νX-~-★ x∈) =
  νX-~-★
    (drop∋ᶜ-neither {Φ = m ∷ Φ} {Γ = Γ} {X = suc X} x∈)
drop-neither-at-νL-suc (A-~-★ (｀ α) ())
drop-neither-at-νL-suc (A-~-★ (‵ ι) ())
drop-neither-at-νL-suc (A-~-★ ★⇒★ ())

drop-neither-at-νR-suc :
  ∀ {m Φ Γ X} →
  (m ∷ Φ) ++ neither ∷ Γ ⊢
    ★ ~ ＇ suc (raiseVarFrom (length Φ) X) →
  (m ∷ Φ) ++ Γ ⊢ ★ ~ ＇ suc X
drop-neither-at-νR-suc {m = m} {Φ = Φ} {Γ = Γ} {X = X} (★-~-νX x∈) =
  ★-~-νX
    (drop∋ᶜ-neither {Φ = m ∷ Φ} {Γ = Γ} {X = suc X} x∈)
drop-neither-at-νR-suc (★-~-B (｀ α) ())
drop-neither-at-νR-suc (★-~-B (‵ ι) ())
drop-neither-at-νR-suc (★-~-B ★⇒★ ())

drop-neither-at-~-gas :
  (gas : ℕ) →
  ∀ {Φ Γ B C}
    {h : Φ ++ neither ∷ Γ ⊢ renameᵗ (raiseVarFrom (length Φ)) B
                            ~ renameᵗ (raiseVarFrom (length Φ)) C} →
  ~-size h ≤ gas →
  Φ ++ Γ ⊢ B ~ C
drop-neither-at-~-gas gas {B = ★} {C = ★} {h = ★-~-★} p = ★-~-★
drop-neither-at-~-gas gas {Φ = []} {Γ = Γ} {B = ＇ X} {C = ＇ .X}
    {h = X-~-X {X = .(suc X)} x∈} p =
  X-~-X (drop∋ᶜ-neither {Φ = []} {Γ = Γ} {X = X} x∈)
drop-neither-at-~-gas gas {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ zero}
    {C = ＇ zero}
    {h = X-~-X {X = zero} x∈} p =
  X-~-X (drop∋ᶜ-neither {Φ = m ∷ Φ} {Γ = Γ} {X = zero} x∈)
drop-neither-at-~-gas gas {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ suc X}
    {C = ＇ suc Y} {h = h} p =
  drop-neither-at-X-suc {m = m} {Φ = Φ} {Γ = Γ} {X = X} {Y = Y} h
drop-neither-at-~-gas gas {B = ‵ ι} {C = ‵ ι′} {h = ι-~-ι} p =
  ι-~-ι
drop-neither-at-~-gas zero {B = A ⇒ B} {C = A′ ⇒ B′}
    {h = ⇒-~-⇒ A~A′ B~B′} ()
drop-neither-at-~-gas (suc gas) {Φ = Φ} {Γ = Γ} {B = A ⇒ B}
    {C = A′ ⇒ B′} {h = ⇒-~-⇒ A~A′ B~B′} (s≤s p) =
  ⇒-~-⇒
    (drop-neither-at-~-gas gas
      {Φ = Φ} {Γ = Γ} {B = A} {C = A′} {h = A~A′}
      (≤trans (≤left+ (~-size A~A′) (~-size B~B′)) p))
    (drop-neither-at-~-gas gas
      {Φ = Φ} {Γ = Γ} {B = B} {C = B′} {h = B~B′}
      (≤trans (≤right+ (~-size A~A′) (~-size B~B′)) p))
drop-neither-at-~-gas zero {B = `∀ A} {C = `∀ B} {h = ∀-~-∀ A~B} ()
drop-neither-at-~-gas (suc gas) {Φ = Φ} {Γ = Γ} {B = `∀ A}
    {C = `∀ B} {h = ∀-~-∀ A~B} (s≤s p) =
  ∀-~-∀
    (drop-neither-at-~-gas gas
      {Φ = both ∷ Φ} {Γ = Γ} {B = A} {C = B}
      {h = cong-~ (rename-raise-ext (length Φ) A)
                  (rename-raise-ext (length Φ) B)
                  A~B}
      (cong-~-≤ (rename-raise-ext (length Φ) A)
                (rename-raise-ext (length Φ) B)
                A~B p))
drop-neither-at-~-gas zero {B = A} {C = ★} {h = A-~-★ g A~G} ()
drop-neither-at-~-gas (suc gas) {Φ = Φ} {Γ = Γ} {B = A} {C = ★}
    {h = A-~-★ {G = G} g A~G} (s≤s p) =
  A-~-★ g
    (drop-neither-at-~-gas gas
      {Φ = Φ} {Γ = Γ} {B = A} {C = G}
      {h = cong-~ refl (sym (renameᵗ-ground-id g)) A~G}
      (cong-~-≤ refl (sym (renameᵗ-ground-id g)) A~G p))
drop-neither-at-~-gas zero {B = ★} {C = B} {h = ★-~-B g H~B} ()
drop-neither-at-~-gas (suc gas) {Φ = Φ} {Γ = Γ} {B = ★} {C = B}
    {h = ★-~-B {H = H} g H~B} (s≤s p) =
  ★-~-B g
    (drop-neither-at-~-gas gas
      {Φ = Φ} {Γ = Γ} {B = H} {C = B}
      {h = cong-~ (sym (renameᵗ-ground-id g)) refl H~B}
      (cong-~-≤ (sym (renameᵗ-ground-id g)) refl H~B p))
drop-neither-at-~-gas gas {Φ = []} {Γ = Γ} {B = ＇ X} {C = ★}
    {h = νX-~-★ {X = .(suc X)} x∈} p =
  νX-~-★ (drop∋ᶜ-neither {Φ = []} {Γ = Γ} {X = X} x∈)
drop-neither-at-~-gas gas {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ zero}
    {C = ★}
    {h = νX-~-★ {X = zero} x∈} p =
  νX-~-★ (drop∋ᶜ-neither {Φ = m ∷ Φ} {Γ = Γ} {X = zero} x∈)
drop-neither-at-~-gas gas {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ suc X} {C = ★}
    {h = h} p =
  drop-neither-at-νL-suc {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
drop-neither-at-~-gas gas {Φ = []} {Γ = Γ} {B = ★} {C = ＇ X}
    {h = ★-~-νX {X = .(suc X)} x∈} p =
  ★-~-νX (drop∋ᶜ-neither {Φ = []} {Γ = Γ} {X = X} x∈)
drop-neither-at-~-gas gas {Φ = m ∷ Φ} {Γ = Γ} {B = ★}
    {C = ＇ zero}
    {h = ★-~-νX {X = zero} x∈} p =
  ★-~-νX (drop∋ᶜ-neither {Φ = m ∷ Φ} {Γ = Γ} {X = zero} x∈)
drop-neither-at-~-gas gas {Φ = m ∷ Φ} {Γ = Γ} {B = ★} {C = ＇ suc X}
    {h = h} p =
  drop-neither-at-νR-suc {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
drop-neither-at-~-gas zero {B = `∀ A} {C = B} {h = ∀-~-B wfB A~⇑B} ()
drop-neither-at-~-gas (suc gas) {Φ = Φ} {Γ = Γ} {B = `∀ A} {C = B}
    {h = ∀-~-B wfB A~⇑B} (s≤s p) =
  ∀-~-B
    (drop-neither-WfTy {Φ = Φ} {Γ = Γ} {A = B} wfB)
    (drop-neither-at-~-gas gas
      {Φ = left ∷ Φ} {Γ = Γ} {B = A} {C = ⇑ᵗ B}
      {h = cong-~ (rename-raise-ext (length Φ) A)
                  (sym (rename-raise-⇑ᵗ (length Φ) B))
                  A~⇑B}
      (cong-~-≤ (rename-raise-ext (length Φ) A)
                (sym (rename-raise-⇑ᵗ (length Φ) B))
                A~⇑B p))
drop-neither-at-~-gas zero {B = A} {C = `∀ B} {h = A-~-∀ wfA ⇑A~B} ()
drop-neither-at-~-gas (suc gas) {Φ = Φ} {Γ = Γ} {B = A} {C = `∀ B}
    {h = A-~-∀ wfA ⇑A~B} (s≤s p) =
  A-~-∀
    (drop-neither-WfTy {Φ = Φ} {Γ = Γ} {A = A} wfA)
    (drop-neither-at-~-gas gas
      {Φ = right ∷ Φ} {Γ = Γ} {B = ⇑ᵗ A} {C = B}
      {h = cong-~ (sym (rename-raise-⇑ᵗ (length Φ) A))
                  (rename-raise-ext (length Φ) B)
                  ⇑A~B}
      (cong-~-≤ (sym (rename-raise-⇑ᵗ (length Φ) A))
                (rename-raise-ext (length Φ) B)
                ⇑A~B p))

drop-neither-at-~ :
  ∀ {Φ Γ B C} →
  Φ ++ neither ∷ Γ ⊢ renameᵗ (raiseVarFrom (length Φ)) B
                     ~ renameᵗ (raiseVarFrom (length Φ)) C →
  Φ ++ Γ ⊢ B ~ C
drop-neither-at-~ h = drop-neither-at-~-gas (~-size h) {h = h} ≤refl

drop-neither-~ :
  ∀ {Γ B C} →
  neither ∷ Γ ⊢ ⇑ᵗ B ~ ⇑ᵗ C →
  Γ ⊢ B ~ C
drop-neither-~ = drop-neither-at-~ {Φ = []}

swapMode : CMode → CMode
swapMode left = right
swapMode right = left
swapMode both = both
swapMode neither = neither

swapCCtx : CCtx → CCtx
swapCCtx [] = []
swapCCtx (m ∷ Γ) = swapMode m ∷ swapCCtx Γ

length-swapCCtx :
  ∀ Γ →
  length (swapCCtx Γ) ≡ length Γ
length-swapCCtx [] = refl
length-swapCCtx (m ∷ Γ) = cong suc (length-swapCCtx Γ)

swap∋ᶜ :
  ∀ {Γ X m} →
  Γ ∋ᶜ X ∶ m →
  swapCCtx Γ ∋ᶜ X ∶ swapMode m
swap∋ᶜ here = here
swap∋ᶜ (there x∈) = there (swap∋ᶜ x∈)

swap-boths[] :
  ∀ Δ →
  swapCCtx (boths Δ []) ≡ boths Δ []
swap-boths[] zero = refl
swap-boths[] (suc Δ) = cong (both ∷_) (swap-boths[] Δ)

~-swap :
  ∀ {Γ A B} →
  Γ ⊢ A ~ B →
  swapCCtx Γ ⊢ B ~ A
~-swap ★-~-★ = ★-~-★
~-swap (X-~-X x∈) = X-~-X (swap∋ᶜ x∈)
~-swap ι-~-ι = ι-~-ι
~-swap (⇒-~-⇒ A~A′ B~B′) =
  ⇒-~-⇒ (~-swap A~A′) (~-swap B~B′)
~-swap (∀-~-∀ A~B) = ∀-~-∀ (~-swap A~B)
~-swap (A-~-★ g A~G) = ★-~-B g (~-swap A~G)
~-swap (★-~-B h H~B) = A-~-★ h (~-swap H~B)
~-swap (νX-~-★ x∈) = ★-~-νX (swap∋ᶜ x∈)
~-swap (★-~-νX x∈) = νX-~-★ (swap∋ᶜ x∈)
~-swap {Γ = Γ} (∀-~-B {B = B} wfB A~⇑B) =
  A-~-∀
    (subst (λ n → WfTy n 0 B) (sym (length-swapCCtx Γ)) wfB)
    (~-swap A~⇑B)
~-swap {Γ = Γ} (A-~-∀ {A = A} wfA ⇑A~B) =
  ∀-~-B
    (subst (λ n → WfTy n 0 A) (sym (length-swapCCtx Γ)) wfA)
    (~-swap ⇑A~B)

boths-sym :
  ∀ {Δ A B} →
  boths Δ [] ⊢ A ~ B →
  boths Δ [] ⊢ B ~ A
boths-sym {Δ = Δ} {A = A} {B = B} A~B =
  subst (λ Γ → Γ ⊢ B ~ A) (swap-boths[] Δ) (~-swap A~B)

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
lower-bounds-consistentᶜ p⊢ (⊑-｀ (wfSeal ()))
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
static-gradual-guarantee (⊑ΛL vM M⊑M′) (⊢Λ vM₀ M⊢) = {!!}
static-gradual-guarantee (⊑`[] M⊑M′ pT⊢) (⊢• M⊢ wfB wfT) = {!!}
static-gradual-guarantee (⊑`[] M⊑M′ pT⊢) (⊢•★ M⊢ wfT) = {!!}
static-gradual-guarantee ⊑$ (⊢$ (κℕ n)) =
  ‵ `ℕ , ι⊑ι `ℕ , ⊢$ (κℕ n) , ⊑-‵
static-gradual-guarantee (⊑⊕ L⊑L′ M⊑M′) (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ) =
  {!!}

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
  ⊢ᵀ• (⊢ᵀup p⊒⊢ (⊢ᵀdown p⊑⊢ M′⊢)) wf★ wfT
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
