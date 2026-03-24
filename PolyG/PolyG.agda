module PolyG where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; suc)

open import PolyC

------------------------------------------------------------------------
-- Surface PolyG syntax
------------------------------------------------------------------------

data GTerm : Set where
  gvar     : Var → GTerm
  gtrue    : GTerm
  gfalse   : GTerm
  glet     : GTerm → GTerm → GTerm
  gasc     : GTerm → Ty → GTerm
  gseal    : Var → GTerm → GTerm
  gunseal  : Var → GTerm → GTerm
  gis      : Ground → GTerm → GTerm
  gifte    : GTerm → GTerm → GTerm → GTerm
  gpair    : GTerm → GTerm → GTerm
  gletpair : GTerm → GTerm → GTerm
  glam     : Ty → GTerm → GTerm
  gapp     : GTerm → GTerm → GTerm
  gpack    : Ty → GTerm → GTerm
  gunpack  : GTerm → GTerm → GTerm
  gtlam    : GTerm → GTerm
  gtapp    : GTerm → Var → Ty → GTerm

------------------------------------------------------------------------
-- Surface consistency/meet and elimination-shape witnesses
------------------------------------------------------------------------

infix 4 _∼_

data _∼_ : Ty → Ty → Set where
  ∼-dynL   : {A : Ty} → TDyn ∼ A
  ∼-dynR   : {A : Ty} → A ∼ TDyn
  ∼-name   : {α : TyName} → nameTy α ∼ nameTy α
  ∼-bool   : TBool ∼ TBool
  ∼-prod   : {A₁ A₂ B₁ B₂ : Ty} →
             A₁ ∼ B₁ →
             A₂ ∼ B₂ →
             (A₁ × A₂) ∼ (B₁ × B₂)
  ∼-arr    : {A₁ A₂ B₁ B₂ : Ty} →
             A₁ ∼ B₁ →
             A₂ ∼ B₂ →
             (A₁ ⇒ A₂) ∼ (B₁ ⇒ B₂)
  ∼-exists : {A B : Ty} →
             A ∼ B →
             Exists A ∼ Exists B
  ∼-forall : {A B : Ty} →
             A ∼ B →
             Forall A ∼ Forall B

data Meet : Ty → Ty → Ty → Set where
  m-dynL   : {A : Ty} → Meet TDyn A A
  m-dynR   : {A : Ty} → Meet A TDyn A
  m-name   : {α : TyName} → Meet (nameTy α) (nameTy α) (nameTy α)
  m-bool   : Meet TBool TBool TBool
  m-prod   : {A₁ A₂ B₁ B₂ C₁ C₂ : Ty} →
             Meet A₁ B₁ C₁ →
             Meet A₂ B₂ C₂ →
             Meet (A₁ × A₂) (B₁ × B₂) (C₁ × C₂)
  m-arr    : {A₁ A₂ B₁ B₂ C₁ C₂ : Ty} →
             Meet A₁ B₁ C₁ →
             Meet A₂ B₂ C₂ →
             Meet (A₁ ⇒ A₂) (B₁ ⇒ B₂) (C₁ ⇒ C₂)
  m-exists : {A B C : Ty} →
             Meet A B C →
             Meet (Exists A) (Exists B) (Exists C)
  m-forall : {A B C : Ty} →
             Meet A B C →
             Meet (Forall A) (Forall B) (Forall C)

data AsProd : Ty → Ty → Ty → Set where
  as-prod     : {A B : Ty} → AsProd (A × B) A B
  as-prod-dyn : AsProd TDyn TDyn TDyn

data AsFun : Ty → Ty → Ty → Set where
  as-fun     : {A B : Ty} → AsFun (A ⇒ B) A B
  as-fun-dyn : AsFun TDyn TDyn TDyn

data AsExists : Ty → Ty → Set where
  as-exists     : {A : Ty} → AsExists (Exists A) A
  as-exists-dyn : AsExists TDyn TDyn

data AsForall : Ty → Ty → Set where
  as-forall     : {A : Ty} → AsForall (Forall A) A
  as-forall-dyn : AsForall TDyn TDyn

------------------------------------------------------------------------
-- PolyG typing
------------------------------------------------------------------------

infix 4 _⊢g_⊢_⦂_

data _⊢g_⊢_⦂_ : TyEnv → Ctx → GTerm → Ty → Set where
  ⊢gvar :
    {Δ : TyEnv} {Γ : Ctx} {x : Var} {A : Ty} →
    Γ ∋ x ⦂ A →
    Δ ⊢g Γ ⊢ gvar x ⦂ A

  ⊢gtrue :
    {Δ : TyEnv} {Γ : Ctx} →
    Δ ⊢g Γ ⊢ gtrue ⦂ TBool

  ⊢gfalse :
    {Δ : TyEnv} {Γ : Ctx} →
    Δ ⊢g Γ ⊢ gfalse ⦂ TBool

  ⊢glet :
    {Δ : TyEnv} {Γ : Ctx} {M N : GTerm} {A B : Ty} →
    Δ ⊢g Γ ⊢ M ⦂ A →
    Δ ⊢g (A ∷ Γ) ⊢ N ⦂ B →
    Δ ⊢g Γ ⊢ glet M N ⦂ B

  ⊢gasc :
    {Δ : TyEnv} {Γ : Ctx} {M : GTerm} {A B : Ty} →
    Δ ⊢g Γ ⊢ M ⦂ A →
    A ∼ B →
    WfTy (tySize Δ) B →
    Δ ⊢g Γ ⊢ gasc M B ⦂ B

  ⊢gseal :
    {Δ : TyEnv} {Γ : Ctx} {i : Var} {M : GTerm} {A B : Ty} →
    KnownMember Δ i A →
    Δ ⊢g Γ ⊢ M ⦂ B →
    B ∼ A →
    Δ ⊢g Γ ⊢ gseal i M ⦂ nameTy (tvar i)

  ⊢gunseal :
    {Δ : TyEnv} {Γ : Ctx} {i : Var} {M : GTerm} {A B : Ty} →
    KnownMember Δ i A →
    Δ ⊢g Γ ⊢ M ⦂ B →
    B ∼ nameTy (tvar i) →
    Δ ⊢g Γ ⊢ gunseal i M ⦂ A

  ⊢gis :
    {Δ : TyEnv} {Γ : Ctx} {G : Ground} {M : GTerm} {A : Ty} →
    WfGround (tySize Δ) G →
    Δ ⊢g Γ ⊢ M ⦂ A →
    Δ ⊢g Γ ⊢ gis G M ⦂ TBool

  ⊢gif :
    {Δ : TyEnv} {Γ : Ctx} {L M N : GTerm} {A Bt Bf B : Ty} →
    Δ ⊢g Γ ⊢ L ⦂ A →
    A ∼ TBool →
    Δ ⊢g Γ ⊢ M ⦂ Bt →
    Δ ⊢g Γ ⊢ N ⦂ Bf →
    Meet Bt Bf B →
    Δ ⊢g Γ ⊢ gifte L M N ⦂ B

  ⊢gpair :
    {Δ : TyEnv} {Γ : Ctx} {M N : GTerm} {A B : Ty} →
    Δ ⊢g Γ ⊢ M ⦂ A →
    Δ ⊢g Γ ⊢ N ⦂ B →
    Δ ⊢g Γ ⊢ gpair M N ⦂ A × B

  ⊢gletpair :
    {Δ : TyEnv} {Γ : Ctx} {M N : GTerm} {A A₁ A₂ B : Ty} →
    Δ ⊢g Γ ⊢ M ⦂ A →
    AsProd A A₁ A₂ →
    Δ ⊢g (A₁ ∷ A₂ ∷ Γ) ⊢ N ⦂ B →
    Δ ⊢g Γ ⊢ gletpair M N ⦂ B

  ⊢glam :
    {Δ : TyEnv} {Γ : Ctx} {A B : Ty} {M : GTerm} →
    WfTy (tySize Δ) A →
    Δ ⊢g (A ∷ Γ) ⊢ M ⦂ B →
    Δ ⊢g Γ ⊢ glam A M ⦂ A ⇒ B

  ⊢gapp :
    {Δ : TyEnv} {Γ : Ctx} {M N : GTerm} {A A₁ A₂ B : Ty} →
    Δ ⊢g Γ ⊢ M ⦂ A →
    AsFun A A₁ A₂ →
    Δ ⊢g Γ ⊢ N ⦂ B →
    B ∼ A₁ →
    WfTy (tySize Δ) A₁ →
    Δ ⊢g Γ ⊢ gapp M N ⦂ A₂

  ⊢gpack :
    {Δ : TyEnv} {Γ : Ctx} {A B : Ty} {M : GTerm} →
    WfTy (tySize Δ) A →
    (known A ∷ Δ) ⊢g ⤊ Γ ⊢ M ⦂ B →
    Δ ⊢g Γ ⊢ gpack A M ⦂ Exists B

  ⊢gunpack :
    {Δ : TyEnv} {Γ : Ctx} {M N : GTerm} {A A' C : Ty} →
    Δ ⊢g Γ ⊢ M ⦂ A →
    AsExists A A' →
    (absTy ∷ Δ) ⊢g (A' ∷ ⤊ Γ) ⊢ N ⦂ renameᵗ suc C →
    Δ ⊢g Γ ⊢ gunpack M N ⦂ C

  ⊢gtlam :
    {Δ : TyEnv} {Γ : Ctx} {M : GTerm} {A : Ty} →
    (absTy ∷ Δ) ⊢g ⤊ Γ ⊢ M ⦂ A →
    Δ ⊢g Γ ⊢ gtlam M ⦂ Forall A

  ⊢gtapp :
    {Δ : TyEnv} {Γ : Ctx} {M : GTerm} {A A' B : Ty} {i : Var} →
    Δ ⊢g Γ ⊢ M ⦂ A →
    AsForall A A' →
    KnownMember Δ i B →
    Δ ⊢g Γ ⊢ gtapp M i B ⦂ A' [ nameTy (tvar i) ]ᵗ

------------------------------------------------------------------------
-- Precision constructors used by elaboration
------------------------------------------------------------------------

idPrec : Ty → Prec
idPrec (nameTy α) = pName α
idPrec TBool      = pBool
idPrec TDyn       = pDyn
idPrec (A × B)    = idPrec A ×⊑ idPrec B
idPrec (A ⇒ B)    = idPrec A ⇒⊑ idPrec B
idPrec (Exists A) = pExists (idPrec A)
idPrec (Forall A) = pForall (idPrec A)

dynPrec : Ty → Prec
dynPrec (nameTy α) = pTag (GName α) (pName α)
dynPrec TBool      = pTag GBool pBool
dynPrec TDyn       = pDyn
dynPrec (A × B)    = pTag GProd (dynPrec A ×⊑ dynPrec B)
dynPrec (A ⇒ B)    = pTag GFun (dynPrec A ⇒⊑ dynPrec B)
dynPrec (Exists A) = pTag GExists (pExists (dynPrec A))
dynPrec (Forall A) = pTag GForall (pForall (dynPrec A))

left-idPrec : {A : Ty} → leftTy (idPrec A) ≡ A
left-idPrec {A = nameTy α} = refl
left-idPrec {A = TBool} = refl
left-idPrec {A = TDyn} = refl
left-idPrec {A = A × B} rewrite left-idPrec {A = A} | left-idPrec {A = B} = refl
left-idPrec {A = A ⇒ B} rewrite left-idPrec {A = A} | left-idPrec {A = B} = refl
left-idPrec {A = Exists A} rewrite left-idPrec {A = A} = refl
left-idPrec {A = Forall A} rewrite left-idPrec {A = A} = refl

right-idPrec : {A : Ty} → rightTy (idPrec A) ≡ A
right-idPrec {A = nameTy α} = refl
right-idPrec {A = TBool} = refl
right-idPrec {A = TDyn} = refl
right-idPrec {A = A × B} rewrite right-idPrec {A = A} | right-idPrec {A = B} = refl
right-idPrec {A = A ⇒ B} rewrite right-idPrec {A = A} | right-idPrec {A = B} = refl
right-idPrec {A = Exists A} rewrite right-idPrec {A = A} = refl
right-idPrec {A = Forall A} rewrite right-idPrec {A = A} = refl

left-dynPrec : {A : Ty} → leftTy (dynPrec A) ≡ A
left-dynPrec {A = nameTy α} = refl
left-dynPrec {A = TBool} = refl
left-dynPrec {A = TDyn} = refl
left-dynPrec {A = A × B} rewrite left-dynPrec {A = A} | left-dynPrec {A = B} = refl
left-dynPrec {A = A ⇒ B} rewrite left-dynPrec {A = A} | left-dynPrec {A = B} = refl
left-dynPrec {A = Exists A} rewrite left-dynPrec {A = A} = refl
left-dynPrec {A = Forall A} rewrite left-dynPrec {A = A} = refl

right-dynPrec : {A : Ty} → rightTy (dynPrec A) ≡ TDyn
right-dynPrec {A = nameTy α} = refl
right-dynPrec {A = TBool} = refl
right-dynPrec {A = TDyn} = refl
right-dynPrec {A = A × B} = refl
right-dynPrec {A = A ⇒ B} = refl
right-dynPrec {A = Exists A} = refl
right-dynPrec {A = Forall A} = refl

wf-idPrec : {n : ℕ} {A : Ty} → WfTy n A → WfPrec n (idPrec A)
wf-idPrec (wf-name h) = wf-pname h
wf-idPrec wf-bool = wf-pbool
wf-idPrec wf-dyn = wf-pdyn
wf-idPrec (wf-prod hA hB) = wf-pprod (wf-idPrec hA) (wf-idPrec hB)
wf-idPrec (wf-arr hA hB) = wf-parr (wf-idPrec hA) (wf-idPrec hB)
wf-idPrec (wf-exists hA) = wf-pexists (wf-idPrec hA)
wf-idPrec (wf-forall hA) = wf-pforall (wf-idPrec hA)

wf-dynPrec : {n : ℕ} {A : Ty} → WfTy n A → WfPrec n (dynPrec A)
wf-dynPrec (wf-name h) = wf-ptag (wf-gname h) (wf-pname h)
wf-dynPrec wf-bool = wf-ptag wf-gbool wf-pbool
wf-dynPrec wf-dyn = wf-pdyn
wf-dynPrec (wf-prod hA hB) = wf-ptag wf-gprod (wf-pprod (wf-dynPrec hA) (wf-dynPrec hB))
wf-dynPrec (wf-arr hA hB) = wf-ptag wf-gfun (wf-parr (wf-dynPrec hA) (wf-dynPrec hB))
wf-dynPrec (wf-exists hA) = wf-ptag wf-gexists (wf-pexists (wf-dynPrec hA))
wf-dynPrec (wf-forall hA) = wf-ptag wf-gforall (wf-pforall (wf-dynPrec hA))

meetLeftPrec : {A B C : Ty} → Meet A B C → Prec
meetLeftPrec {B = B} m-dynL = dynPrec B
meetLeftPrec {A = A} m-dynR = idPrec A
meetLeftPrec {A = nameTy α} m-name = pName α
meetLeftPrec m-bool = pBool
meetLeftPrec (m-prod m₁ m₂) = meetLeftPrec m₁ ×⊑ meetLeftPrec m₂
meetLeftPrec (m-arr m₁ m₂) = meetLeftPrec m₁ ⇒⊑ meetLeftPrec m₂
meetLeftPrec (m-exists m) = pExists (meetLeftPrec m)
meetLeftPrec (m-forall m) = pForall (meetLeftPrec m)

meetRightPrec : {A B C : Ty} → Meet A B C → Prec
meetRightPrec {B = B} m-dynL = idPrec B
meetRightPrec {A = A} m-dynR = dynPrec A
meetRightPrec {B = nameTy α} m-name = pName α
meetRightPrec m-bool = pBool
meetRightPrec (m-prod m₁ m₂) = meetRightPrec m₁ ×⊑ meetRightPrec m₂
meetRightPrec (m-arr m₁ m₂) = meetRightPrec m₁ ⇒⊑ meetRightPrec m₂
meetRightPrec (m-exists m) = pExists (meetRightPrec m)
meetRightPrec (m-forall m) = pForall (meetRightPrec m)

meetLeft-left : {A B C : Ty} {m : Meet A B C} → leftTy (meetLeftPrec m) ≡ C
meetLeft-left {m = m-dynL} = left-dynPrec
meetLeft-left {m = m-dynR} = left-idPrec
meetLeft-left {m = m-name} = refl
meetLeft-left {m = m-bool} = refl
meetLeft-left {m = m-prod m₁ m₂} rewrite meetLeft-left {m = m₁} | meetLeft-left {m = m₂} = refl
meetLeft-left {m = m-arr m₁ m₂} rewrite meetLeft-left {m = m₁} | meetLeft-left {m = m₂} = refl
meetLeft-left {m = m-exists m} rewrite meetLeft-left {m = m} = refl
meetLeft-left {m = m-forall m} rewrite meetLeft-left {m = m} = refl

meetLeft-right : {A B C : Ty} {m : Meet A B C} → rightTy (meetLeftPrec m) ≡ A
meetLeft-right {m = m-dynL} = right-dynPrec
meetLeft-right {m = m-dynR} = right-idPrec
meetLeft-right {m = m-name} = refl
meetLeft-right {m = m-bool} = refl
meetLeft-right {m = m-prod m₁ m₂} rewrite meetLeft-right {m = m₁} | meetLeft-right {m = m₂} = refl
meetLeft-right {m = m-arr m₁ m₂} rewrite meetLeft-right {m = m₁} | meetLeft-right {m = m₂} = refl
meetLeft-right {m = m-exists m} rewrite meetLeft-right {m = m} = refl
meetLeft-right {m = m-forall m} rewrite meetLeft-right {m = m} = refl

meetRight-left : {A B C : Ty} {m : Meet A B C} → leftTy (meetRightPrec m) ≡ C
meetRight-left {m = m-dynL} = left-idPrec
meetRight-left {m = m-dynR} = left-dynPrec
meetRight-left {m = m-name} = refl
meetRight-left {m = m-bool} = refl
meetRight-left {m = m-prod m₁ m₂} rewrite meetRight-left {m = m₁} | meetRight-left {m = m₂} = refl
meetRight-left {m = m-arr m₁ m₂} rewrite meetRight-left {m = m₁} | meetRight-left {m = m₂} = refl
meetRight-left {m = m-exists m} rewrite meetRight-left {m = m} = refl
meetRight-left {m = m-forall m} rewrite meetRight-left {m = m} = refl

meetRight-right : {A B C : Ty} {m : Meet A B C} → rightTy (meetRightPrec m) ≡ B
meetRight-right {m = m-dynL} = right-idPrec
meetRight-right {m = m-dynR} = right-dynPrec
meetRight-right {m = m-name} = refl
meetRight-right {m = m-bool} = refl
meetRight-right {m = m-prod m₁ m₂} rewrite meetRight-right {m = m₁} | meetRight-right {m = m₂} = refl
meetRight-right {m = m-arr m₁ m₂} rewrite meetRight-right {m = m₁} | meetRight-right {m = m₂} = refl
meetRight-right {m = m-exists m} rewrite meetRight-right {m = m} = refl
meetRight-right {m = m-forall m} rewrite meetRight-right {m = m} = refl

------------------------------------------------------------------------
-- Elaboration support
------------------------------------------------------------------------

postulate
  source-wf :
    {Δ : TyEnv} {Γ : Ctx} {M : GTerm} {A : Ty} →
    Δ ⊢g Γ ⊢ M ⦂ A →
    WfTy (tySize Δ) A

  knownMember-wf :
    {Δ : TyEnv} {i : Var} {A : Ty} →
    KnownMember Δ i A →
    WfTy (tySize Δ) A

  knownMember-name-wf :
    {Δ : TyEnv} {i : Var} {A : Ty} →
    KnownMember Δ i A →
    WfTy (tySize Δ) (nameTy (tvar i))

  wf-meet-left :
    {n : ℕ} {A B C : Ty} {m : Meet A B C} →
    WfTy n C →
    WfTy n A →
    WfPrec n (meetLeftPrec m)

  wf-meet-right :
    {n : ℕ} {A B C : Ty} {m : Meet A B C} →
    WfTy n C →
    WfTy n B →
    WfPrec n (meetRightPrec m)

  unpack-typing :
    {Δ : TyEnv} {Γ : Ctx} {M N : Term} {A C : Ty} →
    Δ ⊢ Γ ⊢ M ⦂ Exists A →
    (absTy ∷ Δ) ⊢ (A ∷ ⤊ Γ) ⊢ N ⦂ renameᵗ suc C →
    Δ ⊢ Γ ⊢ unpack M N ⦂ C

ty-conv :
  {Δ : TyEnv} {Γ : Ctx} {M : Term} {A B : Ty} →
  A ≡ B →
  Δ ⊢ Γ ⊢ M ⦂ A →
  Δ ⊢ Γ ⊢ M ⦂ B
ty-conv refl h = h

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

toDynTerm : Ty → Term → Term
toDynTerm A M = cast up (dynPrec A) M

fromDynTerm : Ty → Term → Term
fromDynTerm B M = cast down (dynPrec B) M

ascribeTerm : Ty → Ty → Term → Term
ascribeTerm A B M = fromDynTerm B (toDynTerm A M)

toDyn-pres :
  {Δ : TyEnv} {Γ : Ctx} {M : Term} {A : Ty} →
  WfTy (tySize Δ) A →
  Δ ⊢ Γ ⊢ M ⦂ A →
  Δ ⊢ Γ ⊢ toDynTerm A M ⦂ TDyn
toDyn-pres wfA hM =
  ty-conv right-dynPrec
    (⊢cast-up (wf-dynPrec wfA)
      (ty-conv (symm left-dynPrec) hM))

fromDyn-pres :
  {Δ : TyEnv} {Γ : Ctx} {M : Term} {B : Ty} →
  WfTy (tySize Δ) B →
  Δ ⊢ Γ ⊢ M ⦂ TDyn →
  Δ ⊢ Γ ⊢ fromDynTerm B M ⦂ B
fromDyn-pres wfB hM =
  ty-conv left-dynPrec
    (⊢cast-down (wf-dynPrec wfB)
      (ty-conv (symm right-dynPrec) hM))

ascribe-pres :
  {Δ : TyEnv} {Γ : Ctx} {M : Term} {A B : Ty} →
  WfTy (tySize Δ) A →
  WfTy (tySize Δ) B →
  Δ ⊢ Γ ⊢ M ⦂ A →
  Δ ⊢ Γ ⊢ ascribeTerm A B M ⦂ B
ascribe-pres wfA wfB hM = fromDyn-pres wfB (toDyn-pres wfA hM)

asProdTerm : {A A₁ A₂ : Ty} → AsProd A A₁ A₂ → Term → Term
asProdTerm as-prod M = M
asProdTerm as-prod-dyn M = fromDynTerm (TDyn × TDyn) M

asProd-pres :
  {Δ : TyEnv} {Γ : Ctx} {M : Term} {A A₁ A₂ : Ty} →
  (shp : AsProd A A₁ A₂) →
  Δ ⊢ Γ ⊢ M ⦂ A →
  Δ ⊢ Γ ⊢ asProdTerm shp M ⦂ A₁ × A₂
asProd-pres as-prod hM = hM
asProd-pres as-prod-dyn hM = fromDyn-pres (wf-prod wf-dyn wf-dyn) hM

asFunTerm : {A A₁ A₂ : Ty} → AsFun A A₁ A₂ → Term → Term
asFunTerm as-fun M = M
asFunTerm as-fun-dyn M = fromDynTerm (TDyn ⇒ TDyn) M

asFun-pres :
  {Δ : TyEnv} {Γ : Ctx} {M : Term} {A A₁ A₂ : Ty} →
  (shp : AsFun A A₁ A₂) →
  Δ ⊢ Γ ⊢ M ⦂ A →
  Δ ⊢ Γ ⊢ asFunTerm shp M ⦂ A₁ ⇒ A₂
asFun-pres as-fun hM = hM
asFun-pres as-fun-dyn hM = fromDyn-pres (wf-arr wf-dyn wf-dyn) hM

asExistsTerm : {A A' : Ty} → AsExists A A' → Term → Term
asExistsTerm as-exists M = M
asExistsTerm as-exists-dyn M = fromDynTerm (Exists TDyn) M

asExists-pres :
  {Δ : TyEnv} {Γ : Ctx} {M : Term} {A A' : Ty} →
  (shp : AsExists A A') →
  Δ ⊢ Γ ⊢ M ⦂ A →
  Δ ⊢ Γ ⊢ asExistsTerm shp M ⦂ Exists A'
asExists-pres as-exists hM = hM
asExists-pres as-exists-dyn hM = fromDyn-pres (wf-exists wf-dyn) hM

asForallTerm : {A A' : Ty} → AsForall A A' → Term → Term
asForallTerm as-forall M = M
asForallTerm as-forall-dyn M = fromDynTerm (Forall TDyn) M

asForall-pres :
  {Δ : TyEnv} {Γ : Ctx} {M : Term} {A A' : Ty} →
  (shp : AsForall A A') →
  Δ ⊢ Γ ⊢ M ⦂ A →
  Δ ⊢ Γ ⊢ asForallTerm shp M ⦂ Forall A'
asForall-pres as-forall hM = hM
asForall-pres as-forall-dyn hM = fromDyn-pres (wf-forall wf-dyn) hM

------------------------------------------------------------------------
-- Elaboration and type preservation
------------------------------------------------------------------------

elab :
  {Δ : TyEnv} {Γ : Ctx} {M : GTerm} {A : Ty} →
  Δ ⊢g Γ ⊢ M ⦂ A →
  Term
elab (⊢gvar {x = x} h) = var x
elab ⊢gtrue = true
elab ⊢gfalse = false
elab (⊢glet hM hN) = letv (elab hM) (elab hN)
elab (⊢gasc {A = A} {B = B} hM A∼B wfB) = ascribeTerm A B (elab hM)
elab (⊢gseal {i = i} {A = A} {B = B} hX hM B∼A) =
  seal (tvar i) (ascribeTerm B A (elab hM))
elab (⊢gunseal {i = i} {B = B} hX hM B∼X) =
  unseal (tvar i) (ascribeTerm B (nameTy (tvar i)) (elab hM))
elab (⊢gis {G = G} {A = A} hG hM) = is G (toDynTerm A (elab hM))
elab (⊢gif {A = A} hL A∼B hM hN m) =
  ifte (ascribeTerm A TBool (elab hL))
       (cast down (meetLeftPrec m) (elab hM))
       (cast down (meetRightPrec m) (elab hN))
elab (⊢gpair hM hN) = pair (elab hM) (elab hN)
elab (⊢gletpair hM shp hN) = letpair (asProdTerm shp (elab hM)) (elab hN)
elab (⊢glam {A = A} hA hM) = lam A (elab hM)
elab (⊢gapp {A₁ = A₁} {B = B} hM shp hN B∼A wfA) =
  app (asFunTerm shp (elab hM)) (ascribeTerm B A₁ (elab hN))
elab (⊢gpack {A = A} hA hM) = pack A [] (elab hM)
elab (⊢gunpack hM shp hN) = unpack (asExistsTerm shp (elab hM)) (elab hN)
elab (⊢gtlam hM) = tlam (elab hM)
elab {M = gtapp M i B} (⊢gtapp hM shp hB) = tapp (asForallTerm shp (elab hM)) (tvar i) B

elab-pres :
  {Δ : TyEnv} {Γ : Ctx} {M : GTerm} {A : Ty} →
  (h : Δ ⊢g Γ ⊢ M ⦂ A) →
  Δ ⊢ Γ ⊢ elab h ⦂ A
elab-pres (⊢gvar h) = ⊢var h
elab-pres ⊢gtrue = ⊢true
elab-pres ⊢gfalse = ⊢false
elab-pres (⊢glet hM hN) = ⊢let (elab-pres hM) (elab-pres hN)
elab-pres h@(⊢gasc {A = A} {B = B} hM A∼B wfB) =
  ascribe-pres (source-wf hM) wfB (elab-pres hM)
elab-pres (⊢gseal {i = i} {A = A} {B = B} hX hM B∼A) =
  ⊢seal hX (ascribe-pres (source-wf hM) (knownMember-wf hX) (elab-pres hM))
elab-pres (⊢gunseal {i = i} {B = B} hX hM B∼X) =
  ⊢unseal hX (ascribe-pres (source-wf hM) (knownMember-name-wf hX) (elab-pres hM))
elab-pres (⊢gis hG hM) =
  ⊢is hG (toDyn-pres (source-wf hM) (elab-pres hM))
elab-pres h@(⊢gif hL A∼B hM hN m) =
  ⊢if
    (ascribe-pres (source-wf hL) wf-bool (elab-pres hL))
    (ty-conv (meetLeft-left {m = m})
      (⊢cast-down (wf-meet-left {m = m} (source-wf h) (source-wf hM))
        (ty-conv (symm (meetLeft-right {m = m})) (elab-pres hM))))
    (ty-conv (meetRight-left {m = m})
      (⊢cast-down (wf-meet-right {m = m} (source-wf h) (source-wf hN))
        (ty-conv (symm (meetRight-right {m = m})) (elab-pres hN))))
elab-pres (⊢gpair hM hN) = ⊢pair (elab-pres hM) (elab-pres hN)
elab-pres (⊢gletpair hM shp hN) = ⊢letpair (asProd-pres shp (elab-pres hM)) (elab-pres hN)
elab-pres (⊢glam hA hM) = ⊢lam hA (elab-pres hM)
elab-pres (⊢gapp {B = B} hM shp hN B∼A wfA) =
  ⊢app (asFun-pres shp (elab-pres hM))
       (ascribe-pres (source-wf hN) wfA (elab-pres hN))
elab-pres (⊢gpack hA hM) = ⊢pack hA (elab-pres hM)
elab-pres (⊢gunpack {A = Exists A'} {A' = A'} {C = C} hM as-exists hN) =
  unpack-typing {A = A'} {C = C}
    (elab-pres hM)
    (elab-pres hN)
elab-pres (⊢gunpack {A = TDyn} {A' = TDyn} {C = C} hM as-exists-dyn hN) =
  unpack-typing {A = TDyn} {C = C}
    (fromDyn-pres (wf-exists wf-dyn) (elab-pres hM))
    (elab-pres hN)
elab-pres (⊢gtlam hM) = ⊢tlam (elab-pres hM)
elab-pres (⊢gtapp hM shp hB) = ⊢tapp (asForall-pres shp (elab-pres hM)) hB

elab-type-preserving :
  {Δ : TyEnv} {Γ : Ctx} {M : GTerm} {A : Ty} →
  (h : Δ ⊢g Γ ⊢ M ⦂ A) →
  Δ ⊢ Γ ⊢ elab h ⦂ A
elab-type-preserving = elab-pres
