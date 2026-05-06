module GradualTerms where

-- File Charter:
--   * Extrinsic term syntax and typing judgment for Gradually Typed System F (GTSF).

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision
  using
    ( plains
    ; _∣_⊢_⦂_⊑_
    ; _∣_⊢_⦂_⊒_
    ; Imp
    ; renameImp
    ; ι⊑ι
    ; A⇒B⊑A′⇒B′
    ; `∀A⊑∀B
    ; ⊑-⇒
    ; ⊑-∀
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
static-gradual-guarantee (⊑· L⊑L′ M⊑M′) (⊢· L⊢ M⊢ A~A′) = {!!}
static-gradual-guarantee (⊑· L⊑L′ M⊑M′) (⊢·★ L⊢ M⊢ A′~★) = {!!}
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

lower-bounds-consistent :
  ∀ {Δ A B C p q} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  0 ∣ plains Δ [] ⊢ q ⦂ A ⊑ C →
  boths Δ [] ⊢ B ~ C
lower-bounds-consistent p⊢ q⊢ = {!!}

trans-⊑-plains :
  ∀ {Δ A B C p q} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  0 ∣ plains Δ [] ⊢ q ⦂ B ⊑ C →
  Σ[ r ∈ Imp ] 0 ∣ plains Δ [] ⊢ r ⦂ A ⊑ C
trans-⊑-plains p⊢ q⊢ = {!!}

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
