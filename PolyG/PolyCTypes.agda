module PolyCTypes where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Base using (z<s; s<s)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Type variables, runtime seals, and PolyC types
------------------------------------------------------------------------

Var : Set
Var = ℕ

Seal : Set
Seal = ℕ

data TyName : Set where
  tvar  : Var → TyName
  tseal : Seal → TyName

infixr 7 _⇒_
infixr 6 _×_

data Ty : Set where
  nameTy : TyName → Ty
  TBool  : Ty
  TDyn   : Ty
  _×_    : Ty → Ty → Ty
  _⇒_    : Ty → Ty → Ty
  Exists : Ty → Ty
  Forall : Ty → Ty

data Ground : Set where
  GName   : TyName → Ground
  GBool   : Ground
  GProd   : Ground
  GFun    : Ground
  GExists : Ground
  GForall : Ground

groundTy : Ground → Ty
groundTy (GName α) = nameTy α
groundTy GBool     = TBool
groundTy GProd     = TDyn × TDyn
groundTy GFun      = TDyn ⇒ TDyn
groundTy GExists   = Exists TDyn
groundTy GForall   = Forall TDyn

infixr 6 _×⊑_
infixr 7 _⇒⊑_

data Prec : Set where
  pDyn    : Prec
  pTag    : Ground → Prec → Prec
  pName   : TyName → Prec
  pBool   : Prec
  _×⊑_    : Prec → Prec → Prec
  _⇒⊑_    : Prec → Prec → Prec
  pExists : Prec → Prec
  pForall : Prec → Prec

leftTy : Prec → Ty
leftTy pDyn         = TDyn
leftTy (pTag G p)   = leftTy p
leftTy (pName α)    = nameTy α
leftTy pBool        = TBool
leftTy (p ×⊑ q)     = leftTy p × leftTy q
leftTy (p ⇒⊑ q)     = leftTy p ⇒ leftTy q
leftTy (pExists p)  = Exists (leftTy p)
leftTy (pForall p)  = Forall (leftTy p)

rightTy : Prec → Ty
rightTy pDyn         = TDyn
rightTy (pTag G p)   = TDyn
rightTy (pName α)    = nameTy α
rightTy pBool        = TBool
rightTy (p ×⊑ q)     = rightTy p × rightTy q
rightTy (p ⇒⊑ q)     = rightTy p ⇒ rightTy q
rightTy (pExists p)  = Exists (rightTy p)
rightTy (pForall p)  = Forall (rightTy p)

Ctx : Set
Ctx = List Ty

------------------------------------------------------------------------
-- Parallel renaming and substitution on PolyC types
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = Var → Var

Substᵗ : Set
Substᵗ = Var → Ty

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ zero    = zero
extᵗ ρ (suc i) = suc (ρ i)

renameName : Renameᵗ → TyName → TyName
renameName ρ (tvar i)  = tvar (ρ i)
renameName ρ (tseal σ) = tseal σ

renameGround : Renameᵗ → Ground → Ground
renameGround ρ (GName α) = GName (renameName ρ α)
renameGround ρ GBool     = GBool
renameGround ρ GProd     = GProd
renameGround ρ GFun      = GFun
renameGround ρ GExists   = GExists
renameGround ρ GForall   = GForall

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (nameTy α)  = nameTy (renameName ρ α)
renameᵗ ρ TBool       = TBool
renameᵗ ρ TDyn        = TDyn
renameᵗ ρ (A × B)     = renameᵗ ρ A × renameᵗ ρ B
renameᵗ ρ (A ⇒ B)     = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (Exists A)  = Exists (renameᵗ (extᵗ ρ) A)
renameᵗ ρ (Forall A)  = Forall (renameᵗ (extᵗ ρ) A)

renamePrec : Renameᵗ → Prec → Prec
renamePrec ρ pDyn         = pDyn
renamePrec ρ (pTag G p)   = pTag (renameGround ρ G) (renamePrec ρ p)
renamePrec ρ (pName α)    = pName (renameName ρ α)
renamePrec ρ pBool        = pBool
renamePrec ρ (p ×⊑ q)     = renamePrec ρ p ×⊑ renamePrec ρ q
renamePrec ρ (p ⇒⊑ q)     = renamePrec ρ p ⇒⊑ renamePrec ρ q
renamePrec ρ (pExists p)  = pExists (renamePrec (extᵗ ρ) p)
renamePrec ρ (pForall p)  = pForall (renamePrec (extᵗ ρ) p)

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ zero    = nameTy (tvar zero)
extsᵗ σ (suc i) = renameᵗ suc (σ i)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (nameTy (tvar i))  = σ i
substᵗ σ (nameTy (tseal s)) = nameTy (tseal s)
substᵗ σ TBool              = TBool
substᵗ σ TDyn               = TDyn
substᵗ σ (A × B)            = substᵗ σ A × substᵗ σ B
substᵗ σ (A ⇒ B)            = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (Exists A)         = Exists (substᵗ (extsᵗ σ) A)
substᵗ σ (Forall A)         = Forall (substᵗ (extsᵗ σ) A)

substGround : Substᵗ → Ground → Ground
substGround σ (GName (tvar i)) with σ i
... | nameTy α = GName α
... | _        = GName (tvar zero)
substGround σ (GName (tseal s)) = GName (tseal s)
substGround σ GBool             = GBool
substGround σ GProd             = GProd
substGround σ GFun              = GFun
substGround σ GExists           = GExists
substGround σ GForall           = GForall

substPrec : Substᵗ → Prec → Prec
substPrec σ pDyn         = pDyn
substPrec σ (pTag G p)   = pTag (substGround σ G) (substPrec σ p)
substPrec σ (pName (tvar i)) with σ i
... | nameTy α = pName α
... | _        = pName (tvar zero)
substPrec σ (pName (tseal s)) = pName (tseal s)
substPrec σ pBool             = pBool
substPrec σ (p ×⊑ q)          = substPrec σ p ×⊑ substPrec σ q
substPrec σ (p ⇒⊑ q)          = substPrec σ p ⇒⊑ substPrec σ q
substPrec σ (pExists p)       = pExists (substPrec (extsᵗ σ) p)
substPrec σ (pForall p)       = pForall (substPrec (extsᵗ σ) p)

singleTyEnv : Ty → Substᵗ
singleTyEnv B zero    = B
singleTyEnv B (suc i) = nameTy (tvar i)

_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

_[_]ᴾ : Prec → Ty → Prec
p [ B ]ᴾ = substPrec (singleTyEnv B) p

⤊ : Ctx → Ctx
⤊ Γ = map (renameᵗ suc) Γ

------------------------------------------------------------------------
-- Well-formed names, types, grounds, and precision derivations
------------------------------------------------------------------------

TyCtx : Set
TyCtx = ℕ

WfName : TyCtx → TyName → Set
WfName Δ (tvar X)  = X < Δ
WfName Δ (tseal σ) = ⊤

lt-weaken :
  {i n : ℕ} →
  i < n →
  i < suc n
lt-weaken {i = zero} z<s = z<s
lt-weaken {i = suc i} (s<s h) = s<s (lt-weaken {i = i} h)

wfName-weaken :
  {n : TyCtx} {α : TyName} →
  WfName n α →
  WfName (suc n) α
wfName-weaken {α = tvar i} h = lt-weaken h
wfName-weaken {α = tseal s} h = h

data WfTy : TyCtx → Ty → Set where
  wf-name   : {Δ : TyCtx} {α : TyName} →
              WfName Δ α →
              WfTy Δ (nameTy α)
  wf-bool   : {Δ : TyCtx} →
              WfTy Δ TBool
  wf-dyn    : {Δ : TyCtx} →
              WfTy Δ TDyn
  wf-prod   : {Δ : TyCtx} {A B : Ty} →
              WfTy Δ A →
              WfTy Δ B →
              WfTy Δ (A × B)
  wf-arr    : {Δ : TyCtx} {A B : Ty} →
              WfTy Δ A →
              WfTy Δ B →
              WfTy Δ (A ⇒ B)
  wf-exists : {Δ : TyCtx} {A : Ty} →
              WfTy (suc Δ) A →
              WfTy Δ (Exists A)
  wf-forall : {Δ : TyCtx} {A : Ty} →
              WfTy (suc Δ) A →
              WfTy Δ (Forall A)

wfTy-weaken :
  {n : TyCtx} {A : Ty} →
  WfTy n A →
  WfTy (suc n) A
wfTy-weaken (wf-name h) = wf-name (wfName-weaken h)
wfTy-weaken wf-bool = wf-bool
wfTy-weaken wf-dyn = wf-dyn
wfTy-weaken (wf-prod hA hB) = wf-prod (wfTy-weaken hA) (wfTy-weaken hB)
wfTy-weaken (wf-arr hA hB) = wf-arr (wfTy-weaken hA) (wfTy-weaken hB)
wfTy-weaken (wf-exists hA) = wf-exists (wfTy-weaken hA)
wfTy-weaken (wf-forall hA) = wf-forall (wfTy-weaken hA)

data WfGround : TyCtx → Ground → Set where
  wf-gname   : {Δ : TyCtx} {α : TyName} →
               WfName Δ α →
               WfGround Δ (GName α)
  wf-gbool   : {Δ : TyCtx} →
               WfGround Δ GBool
  wf-gprod   : {Δ : TyCtx} →
               WfGround Δ GProd
  wf-gfun    : {Δ : TyCtx} →
               WfGround Δ GFun
  wf-gexists : {Δ : TyCtx} →
               WfGround Δ GExists
  wf-gforall : {Δ : TyCtx} →
               WfGround Δ GForall

data WfPrec : TyCtx → Prec → Set where
  wf-pdyn    : {Δ : TyCtx} →
               WfPrec Δ pDyn
  wf-ptag    : {Δ : TyCtx} {G : Ground} {p : Prec} →
               WfGround Δ G →
               WfPrec Δ p →
               WfPrec Δ (pTag G p)
  wf-pname   : {Δ : TyCtx} {α : TyName} →
               WfName Δ α →
               WfPrec Δ (pName α)
  wf-pbool   : {Δ : TyCtx} →
               WfPrec Δ pBool
  wf-pprod   : {Δ : TyCtx} {p q : Prec} →
               WfPrec Δ p →
               WfPrec Δ q →
               WfPrec Δ (p ×⊑ q)
  wf-parr    : {Δ : TyCtx} {p q : Prec} →
               WfPrec Δ p →
               WfPrec Δ q →
               WfPrec Δ (p ⇒⊑ q)
  wf-pexists : {Δ : TyCtx} {p : Prec} →
               WfPrec (suc Δ) p →
               WfPrec Δ (pExists p)
  wf-pforall : {Δ : TyCtx} {p : Prec} →
               WfPrec (suc Δ) p →
               WfPrec Δ (pForall p)

------------------------------------------------------------------------
-- Well-formed contexts, renamings, and substitutions
------------------------------------------------------------------------

data WfCtx : TyCtx → Ctx → Set where
  wfΓ[] : {n : TyCtx} →
          WfCtx n []
  wfΓ∷ : {n : TyCtx} {Γ : Ctx} {A : Ty} →
          WfCtx n Γ →
          WfTy n A →
          WfCtx n (A ∷ Γ)

wfty-conv :
  {n : TyCtx} {A B : Ty} →
  A ≡ B →
  WfTy n A →
  WfTy n B
wfty-conv refl h = h

TyRenameWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameWf Δ Δ' ρ = ∀ {X} → X < Δ → ρ X < Δ'

TyRenameWf-ext :
  {Δ Δ' : TyCtx} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  TyRenameWf (suc Δ) (suc Δ') (extᵗ ρ)
TyRenameWf-ext hρ {zero} z<s = z<s
TyRenameWf-ext hρ {suc X} (s<s x<Δ) = s<s (hρ {X} x<Δ)

wfName-rename :
  {Δ Δ' : TyCtx} {α : TyName} {ρ : Renameᵗ} →
  WfName Δ α →
  TyRenameWf Δ Δ' ρ →
  WfName Δ' (renameName ρ α)
wfName-rename {α = tvar i} h hρ = hρ h
wfName-rename {α = tseal s} h hρ = h

renameᵗ-preserves-WfTy :
  {Δ Δ' : TyCtx} {A : Ty} {ρ : Renameᵗ} →
  WfTy Δ A →
  TyRenameWf Δ Δ' ρ →
  WfTy Δ' (renameᵗ ρ A)
renameᵗ-preserves-WfTy (wf-name h) hρ = wf-name (wfName-rename h hρ)
renameᵗ-preserves-WfTy wf-bool hρ = wf-bool
renameᵗ-preserves-WfTy wf-dyn hρ = wf-dyn
renameᵗ-preserves-WfTy (wf-prod hA hB) hρ =
  wf-prod (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-preserves-WfTy hB hρ)
renameᵗ-preserves-WfTy (wf-arr hA hB) hρ =
  wf-arr (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-preserves-WfTy hB hρ)
renameᵗ-preserves-WfTy (wf-exists hA) hρ =
  wf-exists (renameᵗ-preserves-WfTy hA (TyRenameWf-ext hρ))
renameᵗ-preserves-WfTy (wf-forall hA) hρ =
  wf-forall (renameᵗ-preserves-WfTy hA (TyRenameWf-ext hρ))

TySubstWf : TyCtx → TyCtx → Substᵗ → Set
TySubstWf Δ Δ' σ = ∀ {X} → X < Δ → WfTy Δ' (σ X)

TySubstWf-exts :
  {Δ Δ' : TyCtx} {σ : Substᵗ} →
  TySubstWf Δ Δ' σ →
  TySubstWf (suc Δ) (suc Δ') (extsᵗ σ)
TySubstWf-exts hσ {zero} z<s = wf-name z<s
TySubstWf-exts hσ {suc X} (s<s x<Δ) =
  renameᵗ-preserves-WfTy
    (hσ {X} x<Δ)
    (λ {i} i<Δ' → s<s i<Δ')

substᵗ-preserves-WfTy :
  {Δ Δ' : TyCtx} {A : Ty} {σ : Substᵗ} →
  WfTy Δ A →
  TySubstWf Δ Δ' σ →
  WfTy Δ' (substᵗ σ A)
substᵗ-preserves-WfTy (wf-name {α = tvar X} x<Δ) hσ = hσ x<Δ
substᵗ-preserves-WfTy (wf-name {α = tseal s} h) hσ = wf-name h
substᵗ-preserves-WfTy wf-bool hσ = wf-bool
substᵗ-preserves-WfTy wf-dyn hσ = wf-dyn
substᵗ-preserves-WfTy (wf-prod hA hB) hσ =
  wf-prod (substᵗ-preserves-WfTy hA hσ) (substᵗ-preserves-WfTy hB hσ)
substᵗ-preserves-WfTy (wf-arr hA hB) hσ =
  wf-arr (substᵗ-preserves-WfTy hA hσ) (substᵗ-preserves-WfTy hB hσ)
substᵗ-preserves-WfTy (wf-exists hA) hσ =
  wf-exists (substᵗ-preserves-WfTy hA (TySubstWf-exts hσ))
substᵗ-preserves-WfTy (wf-forall hA) hσ =
  wf-forall (substᵗ-preserves-WfTy hA (TySubstWf-exts hσ))

singleTySubstWf :
  {Δ : TyCtx} {B : Ty} →
  WfTy Δ B →
  TySubstWf (suc Δ) Δ (singleTyEnv B)
singleTySubstWf hB {zero} z<s = hB
singleTySubstWf hB {suc X} (s<s x<Δ) = wf-name x<Δ

substᵗ-renameᵗ-cancel-gen :
  {ρ : Renameᵗ} {σ : Substᵗ} →
  ((i : Var) → σ (ρ i) ≡ nameTy (tvar i)) →
  (A : Ty) →
  substᵗ σ (renameᵗ ρ A) ≡ A
substᵗ-renameᵗ-cancel-gen h (nameTy (tvar i)) = h i
substᵗ-renameᵗ-cancel-gen h (nameTy (tseal s)) = refl
substᵗ-renameᵗ-cancel-gen h TBool = refl
substᵗ-renameᵗ-cancel-gen h TDyn = refl
substᵗ-renameᵗ-cancel-gen h (A × B) =
  cong₂ _×_
    (substᵗ-renameᵗ-cancel-gen h A)
    (substᵗ-renameᵗ-cancel-gen h B)
substᵗ-renameᵗ-cancel-gen h (A ⇒ B) =
  cong₂ _⇒_
    (substᵗ-renameᵗ-cancel-gen h A)
    (substᵗ-renameᵗ-cancel-gen h B)
substᵗ-renameᵗ-cancel-gen {ρ = ρ} {σ = σ} h (Exists A) =
  cong Exists (substᵗ-renameᵗ-cancel-gen h-ext A)
  where
    h-ext : (i : Var) → extsᵗ σ (extᵗ ρ i) ≡ nameTy (tvar i)
    h-ext zero = refl
    h-ext (suc i) rewrite h i = refl
substᵗ-renameᵗ-cancel-gen {ρ = ρ} {σ = σ} h (Forall A) =
  cong Forall (substᵗ-renameᵗ-cancel-gen h-ext A)
  where
    h-ext : (i : Var) → extsᵗ σ (extᵗ ρ i) ≡ nameTy (tvar i)
    h-ext zero = refl
    h-ext (suc i) rewrite h i = refl

substᵗ-renameᵗ-cancel :
  (A B : Ty) →
  substᵗ (singleTyEnv B) (renameᵗ suc A) ≡ A
substᵗ-renameᵗ-cancel A B =
  substᵗ-renameᵗ-cancel-gen
    {ρ = suc}
    {σ = singleTyEnv B}
    (λ i → refl)
    A

wfCtx-lift :
  {n : TyCtx} {Γ : Ctx} →
  WfCtx n Γ →
  WfCtx (suc n) (⤊ Γ)
wfCtx-lift wfΓ[] = wfΓ[]
wfCtx-lift (wfΓ∷ hΓ hA) =
  wfΓ∷
    (wfCtx-lift hΓ)
    (renameᵗ-preserves-WfTy hA (λ {X} x<Δ → s<s x<Δ))

------------------------------------------------------------------------
-- Type precision typing (Fig. 4 style)
------------------------------------------------------------------------

infix 4 _⊢ᵖ_⦂_⊑_

data _⊢ᵖ_⦂_⊑_ : TyCtx → Prec → Ty → Ty → Set where
  ⊢ᵖ-dyn :
    {Δ : TyCtx} →
    Δ ⊢ᵖ pDyn ⦂ TDyn ⊑ TDyn

  ⊢ᵖ-tag :
    {Δ : TyCtx} {G : Ground} {p : Prec} {A : Ty} →
    WfGround Δ G →
    Δ ⊢ᵖ p ⦂ A ⊑ groundTy G →
    Δ ⊢ᵖ pTag G p ⦂ A ⊑ TDyn

  ⊢ᵖ-name :
    {Δ : TyCtx} {α : TyName} →
    WfName Δ α →
    Δ ⊢ᵖ pName α ⦂ nameTy α ⊑ nameTy α

  ⊢ᵖ-bool :
    {Δ : TyCtx} →
    Δ ⊢ᵖ pBool ⦂ TBool ⊑ TBool

  ⊢ᵖ-prod :
    {Δ : TyCtx} {p q : Prec} {A₁ A₂ B₁ B₂ : Ty} →
    Δ ⊢ᵖ p ⦂ A₁ ⊑ A₂ →
    Δ ⊢ᵖ q ⦂ B₁ ⊑ B₂ →
    Δ ⊢ᵖ (p ×⊑ q) ⦂ (A₁ × B₁) ⊑ (A₂ × B₂)

  ⊢ᵖ-arr :
    {Δ : TyCtx} {p q : Prec} {A₁ A₂ B₁ B₂ : Ty} →
    Δ ⊢ᵖ p ⦂ A₁ ⊑ A₂ →
    Δ ⊢ᵖ q ⦂ B₁ ⊑ B₂ →
    Δ ⊢ᵖ (p ⇒⊑ q) ⦂ (A₁ ⇒ B₁) ⊑ (A₂ ⇒ B₂)

  ⊢ᵖ-exists :
    {Δ : TyCtx} {p : Prec} {A B : Ty} →
    (suc Δ) ⊢ᵖ p ⦂ A ⊑ B →
    Δ ⊢ᵖ pExists p ⦂ Exists A ⊑ Exists B

  ⊢ᵖ-forall :
    {Δ : TyCtx} {p : Prec} {A B : Ty} →
    (suc Δ) ⊢ᵖ p ⦂ A ⊑ B →
    Δ ⊢ᵖ pForall p ⦂ Forall A ⊑ Forall B

-- Agreement of projections with precision typing

leftTy-agrees :
  {Δ : TyCtx} {p : Prec} {A B : Ty} →
  Δ ⊢ᵖ p ⦂ A ⊑ B →
  leftTy p ≡ A
leftTy-agrees ⊢ᵖ-dyn = refl
leftTy-agrees (⊢ᵖ-tag hG hp) rewrite leftTy-agrees hp = refl
leftTy-agrees (⊢ᵖ-name hα) = refl
leftTy-agrees ⊢ᵖ-bool = refl
leftTy-agrees (⊢ᵖ-prod hp hq)
  rewrite leftTy-agrees hp | leftTy-agrees hq = refl
leftTy-agrees (⊢ᵖ-arr hp hq)
  rewrite leftTy-agrees hp | leftTy-agrees hq = refl
leftTy-agrees (⊢ᵖ-exists hp)
  rewrite leftTy-agrees hp = refl
leftTy-agrees (⊢ᵖ-forall hp)
  rewrite leftTy-agrees hp = refl

rightTy-agrees :
  {Δ : TyCtx} {p : Prec} {A B : Ty} →
  Δ ⊢ᵖ p ⦂ A ⊑ B →
  rightTy p ≡ B
rightTy-agrees ⊢ᵖ-dyn = refl
rightTy-agrees (⊢ᵖ-tag hG hp) = refl
rightTy-agrees (⊢ᵖ-name hα) = refl
rightTy-agrees ⊢ᵖ-bool = refl
rightTy-agrees (⊢ᵖ-prod hp hq)
  rewrite rightTy-agrees hp | rightTy-agrees hq = refl
rightTy-agrees (⊢ᵖ-arr hp hq)
  rewrite rightTy-agrees hp | rightTy-agrees hq = refl
rightTy-agrees (⊢ᵖ-exists hp)
  rewrite rightTy-agrees hp = refl
rightTy-agrees (⊢ᵖ-forall hp)
  rewrite rightTy-agrees hp = refl
