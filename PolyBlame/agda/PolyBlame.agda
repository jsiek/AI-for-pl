module PolyBlame where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using (_∷_; map)
open import Data.Nat using (ℕ; _+_; _<_; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Data.Unit using (⊤; tt)
open import Types public

open import TypeImprecision public
------------------------------------------------------------------------
-- Constants and primitive operators (κ and ⊕)
------------------------------------------------------------------------

data Const : Set where
  κℕ : ℕ → Const

constTy : Const → Ty
constTy (κℕ n) = ‵ `ℕ

data Prim : Set where
  addℕ : Prim

primTy : Prim → Ty
primTy addℕ = ‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ

data δ : Prim → Const → Const → Const → Set where
  δ-add : {m n : ℕ} →
          δ addℕ (κℕ m) (κℕ n) (κℕ (m + n))

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _·α_
infix  5 ν:=_∙_
infixl 6 _⊕[_]_
infix  8 _at_
infix  9 `_

data Cast : Set where
  up_   : Imp → Cast
  down_ : Imp → Cast

data Term : Set where
  `_       : Var → Term
  ƛ_⇒_     : Ty → Term → Term
  _·_      : Term → Term → Term
  Λ_       : Term → Term
  _·α_     : Term → Seal → Term
  ν:=_∙_   : Ty → Term → Term
  $        : Const → Term
  _⊕[_]_   : Term → Prim → Term → Term
  _at_     : Term → Cast → Term
  blame    : Term

------------------------------------------------------------------------
-- Parallel substitution: replace free X's with types in terms
--
-- Note: we only use this to replace X's with seals, so
-- the codomain of these substitutions are seals and X's
-- (because of extsᵗ), so they satisfy IsVar.
------------------------------------------------------------------------

renameᵀ : Renameᵗ → Term → Term
renameᵀ ρ (` x)              = ` x
renameᵀ ρ (ƛ A ⇒ N)          = ƛ (renameᵗ ρ A) ⇒ (renameᵀ ρ N)
renameᵀ ρ (L · M)            = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ (Λ N)              = Λ (renameᵀ (extᵗ ρ) N)
renameᵀ ρ (L ·α α)           = renameᵀ ρ L ·α α
renameᵀ ρ (ν:= A ∙ N)        = ν:= renameᵗ ρ A ∙ renameᵀ ρ N
renameᵀ ρ ($ κ)              = $ κ
renameᵀ ρ (M ⊕[ op ] N)      = renameᵀ ρ M ⊕[ op ] renameᵀ ρ N
renameᵀ ρ (M at up p)            = renameᵀ ρ M at up (renameImpᵗ ρ p)
renameᵀ ρ (M at down p)          = renameᵀ ρ M at down (renameImpᵗ ρ p)
renameᵀ ρ blame              = blame

renameˢᵀ : Renameˢ → Term → Term

liftSealSubstᵗ : Substᵗ → Substᵗ
liftSealSubstᵗ σ X = ⇑ˢ (σ X)

substᵀ : Substᵗ → Term → Term
substᵀ σ (` x)              = ` x
substᵀ σ (ƛ A ⇒ N)          = ƛ (substᵗ σ A) ⇒ (substᵀ σ N)
substᵀ σ (L · M)            = substᵀ σ L · substᵀ σ M
substᵀ σ (Λ N)              = Λ (substᵀ (extsᵗ σ) N)
substᵀ σ (L ·α α)           = substᵀ σ L ·α α
substᵀ σ (ν:= A ∙ N)        = ν:= substᵗ σ A ∙ substᵀ (liftSealSubstᵗ σ) N
substᵀ σ ($ κ)              = $ κ
substᵀ σ (M ⊕[ op ] N)      = substᵀ σ M ⊕[ op ] substᵀ σ N
substᵀ σ (M at up p)             = substᵀ σ M at up (substImpᵗ σ p)
substᵀ σ (M at down p)           = substᵀ σ M at down (substImpᵗ σ p)
substᵀ σ blame              = blame

_[_]ᵀ : Term → Ty → Term
M [ A ]ᵀ = substᵀ (singleTyEnv A) M

------------------------------------------------------------------------
-- Parallel substitution: replace free x's with terms in terms
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

Subst : Set
Subst = Var → Term

ext : Rename → Rename
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Term → Term
rename ρ (` x)              = ` (ρ x)
rename ρ (ƛ A ⇒ N)          = ƛ A ⇒ rename (ext ρ) N
rename ρ (L · M)            = rename ρ L · rename ρ M
rename ρ (Λ N)              = Λ (rename ρ N)
rename ρ (L ·α α)           = rename ρ L ·α α
rename ρ (ν:= A ∙ N)        = ν:= A ∙ rename ρ N
rename ρ ($ κ)              = $ κ
rename ρ (M ⊕[ op ] N)      = rename ρ M ⊕[ op ] rename ρ N
rename ρ (M at up p)           = rename ρ M at up p
rename ρ (M at down p)           = rename ρ M at down p
rename ρ blame              = blame

exts : Subst → Subst
exts σ zero    = ` zero
exts σ (suc x) = rename suc (σ x)

⇑ : Subst → Subst
⇑ σ x = renameᵀ suc (σ x)

liftSealSubst : Subst → Subst
liftSealSubst σ x = renameˢᵀ suc (σ x)

subst : Subst → Term → Term
subst σ (` x)              = σ x
subst σ (ƛ A ⇒ N)          = ƛ A ⇒ subst (exts σ) N
subst σ (L · M)            = subst σ L · subst σ M
subst σ (Λ N)              = Λ (subst (⇑ σ) N)
subst σ (L ·α α)           = subst σ L ·α α
subst σ (ν:= A ∙ N)        = ν:= A ∙ subst (liftSealSubst σ) N
subst σ ($ κ)              = $ κ
subst σ (M ⊕[ op ] N)      = subst σ M ⊕[ op ] subst σ N
subst σ (M at up p)           = subst σ M at up p
subst σ (M at down p)           = subst σ M at down p
subst σ blame              = blame

singleEnv : Term → Subst
singleEnv V zero    = V
singleEnv V (suc x) = ` x

_[_] : Term → Term → Term
N [ V ] = subst (singleEnv V) N

------------------------------------------------------------------------
-- Parallel renaming: replace seals (α's) with seals in terms
------------------------------------------------------------------------

renameˢᵀ ρ (` x)              = ` x
renameˢᵀ ρ (ƛ A ⇒ N)          = ƛ (renameˢ ρ A) ⇒ (renameˢᵀ ρ N)
renameˢᵀ ρ (L · M)            = renameˢᵀ ρ L · renameˢᵀ ρ M
renameˢᵀ ρ (Λ N)              = Λ (renameˢᵀ ρ N)
renameˢᵀ ρ (L ·α α)           = renameˢᵀ ρ L ·α (ρ α)
renameˢᵀ ρ (ν:= A ∙ N)        = ν:= renameˢ ρ A ∙ renameˢᵀ (extˢ ρ) N
renameˢᵀ ρ ($ κ)              = $ κ
renameˢᵀ ρ (M ⊕[ op ] N)      = renameˢᵀ ρ M ⊕[ op ] renameˢᵀ ρ N
renameˢᵀ ρ (M at up p)        = renameˢᵀ ρ M at up (renameImpˢ ρ p)
renameˢᵀ ρ (M at down p)      = renameˢᵀ ρ M at down (renameImpˢ ρ p)
renameˢᵀ ρ blame              = blame

------------------------------------------------------------------------
-- Typing: terms
------------------------------------------------------------------------

infix 4 _∣_⊢_⊢_⦂_

data _∣_⊢_⊢_⦂_ : TyCtx → Store → Ctx → Term → Ty → Set where
  ⊢` : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {x : Var} {A : Ty} →
       Γ ∋ x ⦂ A →
       Δ ∣ Σ ⊢ Γ ⊢ (` x) ⦂ A

  ⊢ƛ : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {A B : Ty} {N : Term} →
       WfTy Δ Σ A →
       Δ ∣ Σ ⊢ (A ∷ Γ) ⊢ N ⦂ B →
       Δ ∣ Σ ⊢ Γ ⊢ (ƛ A ⇒ N) ⦂ (A ⇒ B)

  ⊢· : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {A B : Ty} {L M : Term} →
       Δ ∣ Σ ⊢ Γ ⊢ L ⦂ (A ⇒ B) →
       Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
       Δ ∣ Σ ⊢ Γ ⊢ (L · M) ⦂ B

  ⊢Λ : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {N : Term} {A : Ty} →
       (suc Δ) ∣ (renameStoreᵗ suc Σ) ⊢ (⤊ Γ) ⊢ N ⦂ A →
       Δ ∣ Σ ⊢ Γ ⊢ (Λ N) ⦂ `∀ A

  ⊢·α : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {L : Term} {A B : Ty} {α : Seal} →
        Δ ∣ Σ ⊢ Γ ⊢ L ⦂ `∀ A →
        Σ ∋ˢ α ⦂ B →
        Δ ∣ Σ ⊢ Γ ⊢ (L ·α α) ⦂ A [ ｀ α ]ᵗ

  ⊢ν : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {A B : Ty} {N : Term} →
       WfTy Δ Σ A →
       Δ ∣ (A ∷ ⟰ˢ Σ) ⊢ ⤊ˢ Γ ⊢ N ⦂ ⇑ˢ B →
       WfTy Δ Σ B →
       Δ ∣ Σ ⊢ Γ ⊢ (ν:= A ∙ N) ⦂ B

  ⊢$ : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {κ : Const} →
       Δ ∣ Σ ⊢ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {M N : Term} {op : Prim} →
       Δ ∣ Σ ⊢ Γ ⊢ M ⦂ ‵ `ℕ →
       Δ ∣ Σ ⊢ Γ ⊢ N ⦂ ‵ `ℕ →
       Δ ∣ Σ ⊢ Γ ⊢ (M ⊕[ op ] N) ⦂ ‵ `ℕ

  ⊢cast-up : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {M : Term} {p : Imp} {A B : Ty} →
        Δ ∣ Σ ⊢ Γ ⊢ M ⦂ A →
        Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
        Δ ∣ Σ ⊢ Γ ⊢ (M at up p) ⦂ B

  ⊢cast-down : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {M : Term} {p : Imp} {A B : Ty} →
        Δ ∣ Σ ⊢ Γ ⊢ M ⦂ B →
        Δ ∣ Σ ⊢ᵖ p ⦂ A ⊑ B →
        Δ ∣ Σ ⊢ Γ ⊢ (M at down p) ⦂ A

  ⊢blame : {Δ : TyCtx} {Σ : Store} {Γ : Ctx} {A : Ty} →
           WfTy Δ Σ A →
           Δ ∣ Σ ⊢ Γ ⊢ blame ⦂ A

------------------------------------------------------------------------
-- Values and frames
------------------------------------------------------------------------

data Value : Term → Set where
  vƛ        : {A : Ty} {N : Term} → Value (ƛ A ⇒ N)
  vΛ        : {N : Term} → Value (Λ N)
  vκ        : {κ : Const} → Value ($ κ)
  v+tag     : {V : Term} {g : CImp} {G : Ground} →
              Value V →
              Value (V at up (injTag g G))
  v-seal    : {V : Term} {α : Seal} {p : Imp} →
              Value V →
              Value (V at down (sealImp α p))
  v→+       : {V : Term} {s t : Imp} →
              Value V →
              Value (V at up ⌈ s →ᵖ t ⌉)
  v→-       : {V : Term} {s t : Imp} →
              Value V →
              Value (V at down ⌈ s →ᵖ t ⌉)
  v∀+       : {V : Term} {p : Imp} →
              Value V →
              Value (V at up ⌈ ∀ᵖ p ⌉)
  v∀-       : {V : Term} {p : Imp} →
              Value V →
              Value (V at down ⌈ ∀ᵖ p ⌉)
  vν-       : {V : Term} {p : Imp} →
              Value V →
              Value (V at down (nuImp p))

data Frame : Set where
  □·_      : Term → Frame
  _·□_     : (V : Term) → Value V → Frame
  □·α_     : Seal → Frame
  □⊕[_]_   : Prim → Term → Frame
  _⊕[_]□_  : (V : Term) → Prim → Value V → Frame
  □at-up_  : Imp → Frame
  □at-down_ : Imp → Frame

plug : Frame → Term → Term
plug (□· M) L            = L · M
plug (V ·□ vV) M         = V · M
plug (□·α α) M           = M ·α α
plug (□⊕[ op ] M) L      = L ⊕[ op ] M
plug (V ⊕[ op ]□ vV) M   = V ⊕[ op ] M
plug (□at-up p) M         = M at up p
plug (□at-down p) M       = M at down p

infix 1 _⊲_
data Config : Set where
  _⊲_ : Store → Term → Config

mutual
  sealToTagC : Seal → CImp → CImp
  sealToTagC α (idα β) = idα β
  sealToTagC α (idX X) = idX X
  sealToTagC α (idι ι) = idι ι
  sealToTagC α (p →ᵖ q) = sealToTag α p →ᵖ sealToTag α q
  sealToTagC α (∀ᵖ p) = ∀ᵖ (sealToTag α p)

  sealToTag : Seal → Imp → Imp
  sealToTag α ⌈ g ⌉ = ⌈ sealToTagC α g ⌉
  sealToTag α id★ = id★
  sealToTag α (injTag g G) = injTag (sealToTagC α g) G
  sealToTag α (sealImp β id★) with α ≟ β
  ... | yes _ = injTag (idα α) (G-α α)
  ... | no _ = sealImp β id★
  sealToTag α (sealImp β p) = sealImp β (sealToTag α p)
  sealToTag α (nuImp p) = nuImp (sealToTag (suc α) p)

IsId : Imp → Set
IsId id★          = ⊤
IsId ⌈ idα α ⌉    = ⊤
IsId ⌈ idX X ⌉    = ⊤
IsId ⌈ idι ι ⌉    = ⊤
IsId _            = ⊥

------------------------------------------------------------------------
-- Reduction
------------------------------------------------------------------------

infix 4 _—→_
data _—→_ : Config → Config → Set where
  β-δ : {Σ : Store} {op : Prim} {κ₁ κ₂ κ₃ : Const} →
        δ op κ₁ κ₂ κ₃ →
        (Σ ⊲ (($ κ₁) ⊕[ op ] ($ κ₂))) —→ (Σ ⊲ ($ κ₃))

  β-ƛ : {Σ : Store} {A : Ty} {N V : Term} →
        Value V →
        (Σ ⊲ ((ƛ A ⇒ N) · V)) —→ (Σ ⊲ (N [ V ]))

  β-Λ : {Σ : Store} {N : Term} {α : Seal} →
        (Σ ⊲ ((Λ N) ·α α)) —→ (Σ ⊲ (N [ ｀ α ]ᵀ))

  β-id+ : {Σ : Store} {V : Term} {p : Imp} →
          Value V →
          IsId p →
          (Σ ⊲ (V at up p)) —→ (Σ ⊲ V)

  β-id- : {Σ : Store} {V : Term} {p : Imp} →
          Value V →
          IsId p →
          (Σ ⊲ (V at down p)) —→ (Σ ⊲ V)

  β-→+ : {Σ : Store} {V W : Term} {s t : Imp} →
         Value V →
         Value W →
         (Σ ⊲ ((V at up ⌈ s →ᵖ t ⌉) · W)) —→ (Σ ⊲ ((V · (W at down s)) at up t))

  β-→- : {Σ : Store} {V W : Term} {s t : Imp} →
         Value V →
         Value W →
         (Σ ⊲ ((V at down ⌈ s →ᵖ t ⌉) · W)) —→ (Σ ⊲ ((V · (W at up s)) at down t))

  β-∀+ : {Σ : Store} {V : Term} {p : Imp} {α : Seal} →
         Value V →
         (Σ ⊲ ((V at up ⌈ ∀ᵖ p ⌉) ·α α)) —→ (Σ ⊲ ((V ·α α) at up (p [ α ]ᴾα)))

  β-∀- : {Σ : Store} {V : Term} {p : Imp} {α : Seal} →
         Value V →
         (Σ ⊲ ((V at down ⌈ ∀ᵖ p ⌉) ·α α)) —→ (Σ ⊲ ((V ·α α) at down (p [ α ]ᴾα)))

  β-ν+ : {Σ : Store} {V : Term} {p : Imp} →
         Value V →
         (Σ ⊲ (V at up (nuImp p))) —→
         (Σ ⊲ (ν:= `★ ∙ (((renameˢᵀ suc V) ·α zero) at up ((renameImpˢ suc p) [ zero ]ᴾα))))

  β-ν- : {Σ : Store} {V : Term} {α : Seal} {p : Imp} →
         Value V →
         (Σ ⊲ ((V at down (nuImp p)) ·α α)) —→
         (Σ ⊲ (V at down (sealToTag α (openImpˢ α p))))

  β-tag-ok : {Σ : Store} {V : Term} {g h : CImp} {G : Ground} →
             Value V →
             (Σ ⊲ ((V at up (injTag g G)) at down (injTag h G)))
             —→
             (Σ ⊲ ((V at up ⌈ g ⌉) at down ⌈ h ⌉))

  β-tag-bad : {Σ : Store} {V : Term} {g h : CImp} {G H : Ground} →
              Value V →
              (G ≡ H → ⊥) →
              (Σ ⊲ ((V at up (injTag g G)) at down (injTag h H)))
              —→
              (Σ ⊲ blame)

  β-seal : {Σ : Store} {V : Term} {α : Seal} {p q : Imp} →
           Value V →
           (Σ ⊲ ((V at down (sealImp α p)) at up (sealImp α q)))
           —→
           (Σ ⊲ ((V at down p) at up q))

  -- extendStore appends to the end so that the store is stable under extension
  ξν : {Σ : Store} {A : Ty} {N : Term} →
       (Σ ⊲ (ν:= A ∙ N)) —→ (extendStore Σ A ⊲ renameˢᵀ (singleSealEnv (fresh Σ)) N)

  ξξ : {Σ Π : Store} {F : Frame} {M N M' N' : Term} →
       M' ≡ plug F M →
       N' ≡ plug F N →
       (Σ ⊲ M) —→ (Π ⊲ N) →
       (Σ ⊲ M') —→ (Π ⊲ N')

  ξξ-blame : {Σ : Store} {F : Frame} {M' : Term} →
             M' ≡ plug F blame →
             (Σ ⊲ M') —→ (Σ ⊲ blame)

infix 3 _∎
infixr 2 _—→⟨_⟩_
infix 2 _—↠_
data _—↠_ : Config → Config → Set where
  _∎ : (c : Config) → c —↠ c
  _—→⟨_⟩_ : (c₁ : Config) {c₂ c₃ : Config} → c₁ —→ c₂ → c₂ —↠ c₃ → c₁ —↠ c₃

multi-trans : {c₁ c₂ c₃ : Config} → c₁ —↠ c₂ → c₂ —↠ c₃ → c₁ —↠ c₃
multi-trans (_ ∎) ms2         = ms2
multi-trans (_ —→⟨ s ⟩ ms1) ms2 = _ —→⟨ s ⟩ (multi-trans ms1 ms2)
