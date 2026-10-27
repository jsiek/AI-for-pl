module PolyC where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Base using (z<s; s<s)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)

open import PolyCTypes public

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

data Dir : Set where
  up   : Dir
  down : Dir

flipDir : Dir → Dir
flipDir up   = down
flipDir down = up

data QCast : Set where
  qcast : Dir → Prec → QCast

CastStack : Set
CastStack = List QCast

data Term : Set where
  var     : Var → Term
  err     : Term
  true    : Term
  false   : Term
  letv    : Term → Term → Term
  seal    : TyName → Term → Term
  unseal  : TyName → Term → Term
  is      : Ground → Term → Term
  ifte    : Term → Term → Term → Term
  pair    : Term → Term → Term
  letpair : Term → Term → Term
  lam     : Ty → Term → Term
  app     : Term → Term → Term
  pack    : Ty → CastStack → Term → Term
  unpack  : Term → Term → Term
  tlam    : Term → Term
  tapp    : Term → TyName → Ty → Term
  hide    : Ty → Term → Term
  inj     : Ground → Term → Term
  cast    : Dir → Prec → Term → Term

------------------------------------------------------------------------
-- Type substitution on terms
------------------------------------------------------------------------

renameGroundᵀ = renameGround
renamePrecᵀ = renamePrec
substGroundᵀ = substGround
substPrecᵀ = substPrec

renameCastStack : Renameᵗ → CastStack → CastStack
renameCastStack ρ []                = []
renameCastStack ρ (qcast d p ∷ cs)  = qcast d (renamePrec ρ p) ∷ renameCastStack ρ cs

renameᵀ : Renameᵗ → Term → Term
renameᵀ ρ (var x)             = var x
renameᵀ ρ err                 = err
renameᵀ ρ true                = true
renameᵀ ρ false               = false
renameᵀ ρ (letv M N)          = letv (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (seal α M)          = seal (renameName ρ α) (renameᵀ ρ M)
renameᵀ ρ (unseal α M)        = unseal (renameName ρ α) (renameᵀ ρ M)
renameᵀ ρ (is G M)            = is (renameGroundᵀ ρ G) (renameᵀ ρ M)
renameᵀ ρ (ifte L M N)        = ifte (renameᵀ ρ L) (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (pair M N)          = pair (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (letpair M N)       = letpair (renameᵀ ρ M) (renameᵀ (extᵗ ρ) N)
renameᵀ ρ (lam A M)           = lam (renameᵗ ρ A) (renameᵀ ρ M)
renameᵀ ρ (app M N)           = app (renameᵀ ρ M) (renameᵀ ρ N)
renameᵀ ρ (pack A cs M)       = pack (renameᵗ ρ A) (renameCastStack ρ cs) (renameᵀ (extᵗ ρ) M)
renameᵀ ρ (unpack M N)        = unpack (renameᵀ ρ M) (renameᵀ (extᵗ ρ) N)
renameᵀ ρ (tlam M)            = tlam (renameᵀ (extᵗ ρ) M)
renameᵀ ρ (tapp M α A)        = tapp (renameᵀ ρ M) (renameName ρ α) (renameᵗ ρ A)
renameᵀ ρ (hide A M)          = hide (renameᵗ ρ A) (renameᵀ (extᵗ ρ) M)
renameᵀ ρ (inj G M)           = inj (renameGroundᵀ ρ G) (renameᵀ ρ M)
renameᵀ ρ (cast d p M)        = cast d (renamePrecᵀ ρ p) (renameᵀ ρ M)

substName : Substᵗ → TyName → TyName
substName σ (tvar i) with σ i
... | nameTy α = α
... | _        = tvar zero
substName σ (tseal s) = tseal s

substCastStack : Substᵗ → CastStack → CastStack
substCastStack σ []                = []
substCastStack σ (qcast d p ∷ cs)  = qcast d (substPrec σ p) ∷ substCastStack σ cs

substᵀ : Substᵗ → Term → Term
substᵀ σ (var x)             = var x
substᵀ σ err                 = err
substᵀ σ true                = true
substᵀ σ false               = false
substᵀ σ (letv M N)          = letv (substᵀ σ M) (substᵀ σ N)
substᵀ σ (seal α M)          = seal (substName σ α) (substᵀ σ M)
substᵀ σ (unseal α M)        = unseal (substName σ α) (substᵀ σ M)
substᵀ σ (is G M)            = is (substGroundᵀ σ G) (substᵀ σ M)
substᵀ σ (ifte L M N)        = ifte (substᵀ σ L) (substᵀ σ M) (substᵀ σ N)
substᵀ σ (pair M N)          = pair (substᵀ σ M) (substᵀ σ N)
substᵀ σ (letpair M N)       = letpair (substᵀ σ M) (substᵀ (extsᵗ σ) N)
substᵀ σ (lam A M)           = lam (substᵗ σ A) (substᵀ σ M)
substᵀ σ (app M N)           = app (substᵀ σ M) (substᵀ σ N)
substᵀ σ (pack A cs M)       = pack (substᵗ σ A) (substCastStack σ cs) (substᵀ (extsᵗ σ) M)
substᵀ σ (unpack M N)        = unpack (substᵀ σ M) (substᵀ (extsᵗ σ) N)
substᵀ σ (tlam M)            = tlam (substᵀ (extsᵗ σ) M)
substᵀ σ (tapp M α A)        = tapp (substᵀ σ M) (substName σ α) (substᵗ σ A)
substᵀ σ (hide A M)          = hide (substᵗ σ A) (substᵀ (extsᵗ σ) M)
substᵀ σ (inj G M)           = inj (substGroundᵀ σ G) (substᵀ σ M)
substᵀ σ (cast d p M)        = cast d (substPrecᵀ σ p) (substᵀ σ M)

_[_]ᵀ : Term → Ty → Term
M [ A ]ᵀ = substᵀ (singleTyEnv A) M

------------------------------------------------------------------------
-- Term renaming and substitution
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

Subst : Set
Subst = Var → Term

ext : Rename → Rename
ext ρ zero    = zero
ext ρ (suc i) = suc (ρ i)

rename : Rename → Term → Term
rename ρ (var x)             = var (ρ x)
rename ρ err                 = err
rename ρ true                = true
rename ρ false               = false
rename ρ (letv M N)          = letv (rename ρ M) (rename (ext ρ) N)
rename ρ (seal α M)          = seal α (rename ρ M)
rename ρ (unseal α M)        = unseal α (rename ρ M)
rename ρ (is G M)            = is G (rename ρ M)
rename ρ (ifte L M N)        = ifte (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (pair M N)          = pair (rename ρ M) (rename ρ N)
rename ρ (letpair M N)       = letpair (rename ρ M) (rename (ext (ext ρ)) N)
rename ρ (lam A M)           = lam A (rename (ext ρ) M)
rename ρ (app M N)           = app (rename ρ M) (rename ρ N)
rename ρ (pack A cs M)       = pack A cs (rename ρ M)
rename ρ (unpack M N)        = unpack (rename ρ M) (rename (ext ρ) N)
rename ρ (tlam M)            = tlam (rename ρ M)
rename ρ (tapp M α A)        = tapp (rename ρ M) α A
rename ρ (hide A M)          = hide A (rename ρ M)
rename ρ (inj G M)           = inj G (rename ρ M)
rename ρ (cast d p M)        = cast d p (rename ρ M)

exts : Subst → Subst
exts σ zero    = var zero
exts σ (suc i) = rename suc (σ i)

⇑ : Subst → Subst
⇑ σ i = renameᵀ suc (σ i)

subst : Subst → Term → Term
subst σ (var x)             = σ x
subst σ err                 = err
subst σ true                = true
subst σ false               = false
subst σ (letv M N)          = letv (subst σ M) (subst (exts σ) N)
subst σ (seal α M)          = seal α (subst σ M)
subst σ (unseal α M)        = unseal α (subst σ M)
subst σ (is G M)            = is G (subst σ M)
subst σ (ifte L M N)        = ifte (subst σ L) (subst σ M) (subst σ N)
subst σ (pair M N)          = pair (subst σ M) (subst σ N)
subst σ (letpair M N)       = letpair (subst σ M) (subst (exts (exts σ)) N)
subst σ (lam A M)           = lam A (subst (exts σ) M)
subst σ (app M N)           = app (subst σ M) (subst σ N)
subst σ (pack A cs M)       = pack A cs (subst (⇑ σ) M)
subst σ (unpack M N)        = unpack (subst σ M) (subst (exts (⇑ σ)) N)
subst σ (tlam M)            = tlam (subst (⇑ σ) M)
subst σ (tapp M α A)        = tapp (subst σ M) α A
subst σ (hide A M)          = hide A (subst (⇑ σ) M)
subst σ (inj G M)           = inj G (subst σ M)
subst σ (cast d p M)        = cast d p (subst σ M)

singleEnv : Term → Subst
singleEnv V zero    = V
singleEnv V (suc i) = var i

pairEnv : Term → Term → Subst
pairEnv V₁ V₂ zero            = V₁
pairEnv V₁ V₂ (suc zero)      = V₂
pairEnv V₁ V₂ (suc (suc i))   = var i

_[_] : Term → Term → Term
M [ V ] = subst (singleEnv V) M

_[_][_] : Term → Term → Term → Term
M [ V₁ ][ V₂ ] = subst (pairEnv V₁ V₂) M

------------------------------------------------------------------------
-- Typing contexts and lookup
------------------------------------------------------------------------

data TyInfo : Set where
  absTy : TyInfo
  known : Ty → TyInfo

TyEnv : Set
TyEnv = List TyInfo

tySize : TyEnv → ℕ
tySize []            = zero
tySize (_ ∷ Δ)       = suc (tySize Δ)

data WfTyEnv : TyEnv → Set where
  wfΔ[] : WfTyEnv []
  wfΔ-absTy : {Δ : TyEnv} →
              WfTyEnv Δ →
              WfTyEnv (absTy ∷ Δ)
  wfΔ-known : {Δ : TyEnv} {A : Ty} →
              WfTy (tySize Δ) A →
              WfTyEnv Δ →
              WfTyEnv (known A ∷ Δ)

infix 4 _∋_⦂_

data _∋_⦂_ : Ctx → Var → Ty → Set where
  Z : {Γ : Ctx} {A : Ty} →
      (A ∷ Γ) ∋ zero ⦂ A
  S : {Γ : Ctx} {A B : Ty} {x : Var} →
      Γ ∋ x ⦂ A →
      (B ∷ Γ) ∋ suc x ⦂ A

data TyMember : TyEnv → Var → Set where
  tz : {Δ : TyEnv} {I : TyInfo} →
       TyMember (I ∷ Δ) zero
  ts : {Δ : TyEnv} {I : TyInfo} {i : Var} →
       TyMember Δ i →
       TyMember (I ∷ Δ) (suc i)

data KnownMember : TyEnv → Var → Ty → Set where
  kz : {Δ : TyEnv} {A : Ty} →
       KnownMember (known A ∷ Δ) zero A
  ks-absTy : {Δ : TyEnv} {i : Var} {A : Ty} →
             KnownMember Δ i A →
             KnownMember (absTy ∷ Δ) (suc i) (renameᵗ suc A)
  ks-known : {Δ : TyEnv} {i : Var} {A B : Ty} →
             KnownMember Δ i A →
             KnownMember (known B ∷ Δ) (suc i) (renameᵗ suc A)

lookup-wf :
  {n : TyCtx} {Γ : Ctx} {x : Var} {A : Ty} →
  WfCtx n Γ →
  Γ ∋ x ⦂ A →
  WfTy n A
lookup-wf (wfΓ∷ hΓ hA) Z = hA
lookup-wf (wfΓ∷ hΓ hA) (S h) = lookup-wf hΓ h

knownMember-wf :
  {Δ : TyEnv} {i : Var} {A : Ty} →
  WfTyEnv Δ →
  KnownMember Δ i A →
  WfTy (tySize Δ) A
knownMember-wf (wfΔ-known hA wfΔ) kz = wfTy-weaken hA
knownMember-wf (wfΔ-absTy wfΔ) (ks-absTy h) =
  renameᵗ-preserves-WfTy
    (knownMember-wf wfΔ h)
    (λ {X} x<Δ → s<s x<Δ)
knownMember-wf (wfΔ-known hB wfΔ) (ks-known h) =
  renameᵗ-preserves-WfTy
    (knownMember-wf wfΔ h)
    (λ {X} x<Δ → s<s x<Δ)

knownMember-name :
  {Δ : TyEnv} {i : Var} {A : Ty} →
  KnownMember Δ i A →
  WfName (tySize Δ) (tvar i)
knownMember-name kz = z<s
knownMember-name (ks-absTy h) = s<s (knownMember-name h)
knownMember-name (ks-known h) = s<s (knownMember-name h)

knownMember-name-wf :
  {Δ : TyEnv} {i : Var} {A : Ty} →
  KnownMember Δ i A →
  WfTy (tySize Δ) (nameTy (tvar i))
knownMember-name-wf h = wf-name (knownMember-name h)

------------------------------------------------------------------------
-- Static typing
------------------------------------------------------------------------

infix 4 _⊢_⊢_⦂_

data _⊢_⊢_⦂_ : TyEnv → Ctx → Term → Ty → Set where
  ⊢var :
    {Δ : TyEnv} {Γ : Ctx} {x : Var} {A : Ty} →
    Γ ∋ x ⦂ A →
    Δ ⊢ Γ ⊢ var x ⦂ A

  ⊢err :
    {Δ : TyEnv} {Γ : Ctx} {A : Ty} →
    WfTy (tySize Δ) A →
    Δ ⊢ Γ ⊢ err ⦂ A

  ⊢true :
    {Δ : TyEnv} {Γ : Ctx} →
    Δ ⊢ Γ ⊢ true ⦂ TBool

  ⊢false :
    {Δ : TyEnv} {Γ : Ctx} →
    Δ ⊢ Γ ⊢ false ⦂ TBool

  ⊢let :
    {Δ : TyEnv} {Γ : Ctx} {M N : Term} {A B : Ty} →
    Δ ⊢ Γ ⊢ M ⦂ A →
    Δ ⊢ (A ∷ Γ) ⊢ N ⦂ B →
    Δ ⊢ Γ ⊢ letv M N ⦂ B

  ⊢seal :
    {Δ : TyEnv} {Γ : Ctx} {i : Var} {A : Ty} {M : Term} →
    KnownMember Δ i A →
    Δ ⊢ Γ ⊢ M ⦂ A →
    Δ ⊢ Γ ⊢ seal (tvar i) M ⦂ nameTy (tvar i)

  ⊢unseal :
    {Δ : TyEnv} {Γ : Ctx} {i : Var} {A : Ty} {M : Term} →
    KnownMember Δ i A →
    Δ ⊢ Γ ⊢ M ⦂ nameTy (tvar i) →
    Δ ⊢ Γ ⊢ unseal (tvar i) M ⦂ A

  ⊢is :
    {Δ : TyEnv} {Γ : Ctx} {G : Ground} {M : Term} →
    WfGround (tySize Δ) G →
    Δ ⊢ Γ ⊢ M ⦂ TDyn →
    Δ ⊢ Γ ⊢ is G M ⦂ TBool

  ⊢if :
    {Δ : TyEnv} {Γ : Ctx} {L M N : Term} {A : Ty} →
    Δ ⊢ Γ ⊢ L ⦂ TBool →
    Δ ⊢ Γ ⊢ M ⦂ A →
    Δ ⊢ Γ ⊢ N ⦂ A →
    Δ ⊢ Γ ⊢ ifte L M N ⦂ A

  ⊢pair :
    {Δ : TyEnv} {Γ : Ctx} {M N : Term} {A B : Ty} →
    Δ ⊢ Γ ⊢ M ⦂ A →
    Δ ⊢ Γ ⊢ N ⦂ B →
    Δ ⊢ Γ ⊢ pair M N ⦂ A × B

  ⊢letpair :
    {Δ : TyEnv} {Γ : Ctx} {M N : Term} {A B C : Ty} →
    Δ ⊢ Γ ⊢ M ⦂ A × B →
    Δ ⊢ (A ∷ B ∷ Γ) ⊢ N ⦂ C →
    Δ ⊢ Γ ⊢ letpair M N ⦂ C

  ⊢lam :
    {Δ : TyEnv} {Γ : Ctx} {A B : Ty} {M : Term} →
    WfTy (tySize Δ) A →
    Δ ⊢ (A ∷ Γ) ⊢ M ⦂ B →
    Δ ⊢ Γ ⊢ lam A M ⦂ A ⇒ B

  ⊢app :
    {Δ : TyEnv} {Γ : Ctx} {M N : Term} {A B : Ty} →
    Δ ⊢ Γ ⊢ M ⦂ A ⇒ B →
    Δ ⊢ Γ ⊢ N ⦂ A →
    Δ ⊢ Γ ⊢ app M N ⦂ B

  ⊢pack :
    {Δ : TyEnv} {Γ : Ctx} {A B : Ty} {M : Term} →
    WfTy (tySize Δ) A →
    (known A ∷ Δ) ⊢ ⤊ Γ ⊢ M ⦂ B →
    Δ ⊢ Γ ⊢ pack A [] M ⦂ Exists B

  ⊢unpack :
    {Δ : TyEnv} {Γ : Ctx} {M N : Term} {A B C : Ty} →
    Δ ⊢ Γ ⊢ M ⦂ Exists A →
    (absTy ∷ Δ) ⊢ (A ∷ ⤊ Γ) ⊢ N ⦂ renameᵗ suc C →
    Δ ⊢ Γ ⊢ unpack M N ⦂ C

  ⊢tlam :
    {Δ : TyEnv} {Γ : Ctx} {M : Term} {A : Ty} →
    (absTy ∷ Δ) ⊢ ⤊ Γ ⊢ M ⦂ A →
    Δ ⊢ Γ ⊢ tlam M ⦂ Forall A

  ⊢tapp :
    {Δ : TyEnv} {Γ : Ctx} {M : Term} {A B : Ty} {i : Var} →
    Δ ⊢ Γ ⊢ M ⦂ Forall A →
    KnownMember Δ i B →
    Δ ⊢ Γ ⊢ tapp M (tvar i) B ⦂ A [ nameTy (tvar i) ]ᵗ

  ⊢hide :
    {Δ : TyEnv} {Γ : Ctx} {A B : Ty} {M : Term} →
    WfTy (tySize Δ) A →
    (known A ∷ Δ) ⊢ ⤊ Γ ⊢ M ⦂ renameᵗ suc B →
    Δ ⊢ Γ ⊢ hide A M ⦂ B

  ⊢inj :
    {Δ : TyEnv} {Γ : Ctx} {G : Ground} {M : Term} →
    WfGround (tySize Δ) G →
    Δ ⊢ Γ ⊢ M ⦂ groundTy G →
    Δ ⊢ Γ ⊢ inj G M ⦂ TDyn

  ⊢cast-up :
    {Δ : TyEnv} {Γ : Ctx} {p : Prec} {M : Term} →
    WfPrec (tySize Δ) p →
    Δ ⊢ Γ ⊢ M ⦂ leftTy p →
    Δ ⊢ Γ ⊢ cast up p M ⦂ rightTy p

  ⊢cast-down :
    {Δ : TyEnv} {Γ : Ctx} {p : Prec} {M : Term} →
    WfPrec (tySize Δ) p →
    Δ ⊢ Γ ⊢ M ⦂ rightTy p →
    Δ ⊢ Γ ⊢ cast down p M ⦂ leftTy p

------------------------------------------------------------------------
-- Values, stores, evaluation contexts, and reduction
------------------------------------------------------------------------

data Value : Term → Set where
  vtrue   : Value true
  vfalse  : Value false
  vseal   : {α : TyName} {V : Term} →
            Value V →
            Value (seal α V)
  vpair   : {V W : Term} →
            Value V →
            Value W →
            Value (pair V W)
  vlam    : {A : Ty} {M : Term} →
            Value (lam A M)
  vtlam   : {M : Term} →
            Value (tlam M)
  vinj    : {G : Ground} {V : Term} →
            Value V →
            Value (inj G V)
  vcast-fun :
    {d : Dir} {p q : Prec} {V : Term} →
    Value V →
    Value (cast d (p ⇒⊑ q) V)
  vcast-forall :
    {d : Dir} {p : Prec} {V : Term} →
    Value V →
    Value (cast d (pForall p) V)
  vpack :
    {A : Ty} {cs : CastStack} {M : Term} →
    Value (pack A cs M)

Store : Set
Store = List Ty

fresh : Store → Seal
fresh = length

_∷ʳ_ : Store → Ty → Store
[] ∷ʳ A       = A ∷ []
(B ∷ Σ) ∷ʳ A  = B ∷ (Σ ∷ʳ A)

substSealTy : Seal → Ty → Ty
substSealTy σ A = A [ nameTy (tseal σ) ]ᵗ

substSealTerm : Seal → Term → Term
substSealTerm σ M = M [ nameTy (tseal σ) ]ᵀ

substSealPrec : Seal → Prec → Prec
substSealPrec σ p = p [ nameTy (tseal σ) ]ᴾ

applyCastStack : Seal → CastStack → Term → Term
applyCastStack σ [] M = substSealTerm σ M
applyCastStack σ (qcast d p ∷ cs) M =
  cast d (substSealPrec σ p) (applyCastStack σ cs M)

data Frame : Set where
  let□     : Term → Frame
  seal□    : TyName → Frame
  unseal□  : TyName → Frame
  is□      : Ground → Frame
  if□      : Term → Term → Frame
  pairL□   : Term → Frame
  pairR□   : Term → Frame
  letpair□ : Term → Frame
  appL□    : Term → Frame
  appR□    : Term → Frame
  unpack□  : Term → Frame
  tapp□    : TyName → Ty → Frame
  inj□     : Ground → Frame
  cast□    : Dir → Prec → Frame

plug : Frame → Term → Term
plug (let□ N) M       = letv M N
plug (seal□ α) M      = seal α M
plug (unseal□ α) M    = unseal α M
plug (is□ G) M        = is G M
plug (if□ N₁ N₂) M    = ifte M N₁ N₂
plug (pairL□ N) M     = pair M N
plug (pairR□ V) M     = pair V M
plug (letpair□ N) M   = letpair M N
plug (appL□ N) M      = app M N
plug (appR□ V) M      = app V M
plug (unpack□ N) M    = unpack M N
plug (tapp□ α A) M    = tapp M α A
plug (inj□ G) M       = inj G M
plug (cast□ d p) M    = cast d p M

infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

data Redex : Store → Term → Store → Term → Set where
  β-let :
    {Σ : Store} {V N : Term} →
    Value V →
    Redex Σ (letv V N) Σ (N [ V ])

  β-unseal :
    {Σ : Store} {α : TyName} {V : Term} →
    Value V →
    Redex Σ (unseal α (seal α V)) Σ V

  β-is-yes :
    {Σ : Store} {G : Ground} {V : Term} →
    Value V →
    Redex Σ (is G (inj G V)) Σ true

  β-is-no :
    {Σ : Store} {G H : Ground} {V : Term} →
    Value V →
    G ≢ H →
    Redex Σ (is G (inj H V)) Σ false

  β-if-true :
    {Σ : Store} {M N : Term} →
    Redex Σ (ifte true M N) Σ M

  β-if-false :
    {Σ : Store} {M N : Term} →
    Redex Σ (ifte false M N) Σ N

  β-letpair :
    {Σ : Store} {V W N : Term} →
    Value V →
    Value W →
    Redex Σ (letpair (pair V W) N) Σ (N [ V ][ W ])

  β-app :
    {Σ : Store} {A : Ty} {M V : Term} →
    Value V →
    Redex Σ (app (lam A M) V) Σ (M [ V ])

  β-hide :
    {Σ : Store} {A : Ty} {M : Term} →
    Redex Σ (hide A M) (Σ ∷ʳ A) (substSealTerm (fresh Σ) M)

  β-unpack :
    {Σ : Store} {A : Ty} {cs : CastStack} {M N : Term} →
    Redex Σ (unpack (pack A cs M) N)
            (Σ ∷ʳ A)
            (subst (singleEnv (applyCastStack (fresh Σ) cs M))
                   (substᵀ (singleTyEnv (nameTy (tseal (fresh Σ)))) N))

  β-tapp :
    {Σ : Store} {M : Term} {α : TyName} {A : Ty} →
    Redex Σ (tapp (tlam M) α A) Σ (substᵀ (singleTyEnv (nameTy α)) M)

  β-cast-id-name :
    {Σ : Store} {d : Dir} {α : TyName} {V : Term} →
    Value V →
    Redex Σ (cast d (pName α) V) Σ V

  β-cast-id-bool :
    {Σ : Store} {d : Dir} {V : Term} →
    Value V →
    Redex Σ (cast d pBool V) Σ V

  β-cast-id-dyn :
    {Σ : Store} {d : Dir} {V : Term} →
    Value V →
    Redex Σ (cast d pDyn V) Σ V

  β-cast-prod :
    {Σ : Store} {d : Dir} {p q : Prec} {V W : Term} →
    Value V →
    Value W →
    Redex Σ (cast d (p ×⊑ q) (pair V W))
            Σ
            (pair (cast d p V) (cast d q W))

  β-cast-fun :
    {Σ : Store} {d : Dir} {p q : Prec} {V W : Term} →
    Value V →
    Value W →
    Redex Σ (app (cast d (p ⇒⊑ q) V) W)
            Σ
            (cast d q (app V (cast (flipDir d) p W)))

  β-cast-exists :
    {Σ : Store} {d : Dir} {p : Prec} {A : Ty} {cs : CastStack} {M : Term} →
    Redex Σ (cast d (pExists p) (pack A cs M))
            Σ
            (pack A (qcast d p ∷ cs) M)

  β-cast-forall :
    {Σ : Store} {d : Dir} {p : Prec} {V : Term} {α : TyName} {A : Ty} →
    Value V →
    Redex Σ (tapp (cast d (pForall p) V) α A)
            Σ
            (cast d (substPrec (singleTyEnv (nameTy α)) p) (tapp V α A))

  β-cast-tag-up :
    {Σ : Store} {G : Ground} {p : Prec} {V : Term} →
    Value V →
    Redex Σ (cast up (pTag G p) V)
            Σ
            (inj G (cast up p V))

  β-cast-tag-down-yes :
    {Σ : Store} {G : Ground} {p : Prec} {V : Term} →
    Value V →
    Redex Σ (cast down (pTag G p) (inj G V))
            Σ
            (cast down p V)

  β-cast-tag-down-no :
    {Σ : Store} {G H : Ground} {p : Prec} {V : Term} →
    Value V →
    G ≢ H →
    Redex Σ (cast down (pTag G p) (inj H V))
            Σ
            err

infix 2 _⊢_↦_⊢_

data _⊢_↦_⊢_ : Store → Term → Store → Term → Set where
  β :
    {Σ Σ' : Store} {M M' : Term} →
    Redex Σ M Σ' M' →
    Σ ⊢ M ↦ Σ' ⊢ M'

  ξξ :
    {Σ Σ' : Store} {F : Frame} {M N M' N' : Term} →
    M' ≡ plug F M →
    N' ≡ plug F N →
    Σ ⊢ M ↦ Σ' ⊢ N →
    Σ ⊢ M' ↦ Σ' ⊢ N'

  ξξ-err :
    {Σ : Store} {F : Frame} {M' : Term} →
    M' ≡ plug F err →
    Σ ⊢ M' ↦ Σ ⊢ err

pattern ξ F M↦N = ξξ {F = F} refl refl M↦N
pattern ξ-err F = ξξ-err {F = F} refl
