module PolyCTypes where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _<_)
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
