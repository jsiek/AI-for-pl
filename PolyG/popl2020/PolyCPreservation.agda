module PolyCPreservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product renaming (_×_ to _×ᵖ_) using (_,_; proj₁; proj₂)

open import PolyC

------------------------------------------------------------------------
-- Store lookup and extension
------------------------------------------------------------------------

infix 4 _∋σ_⦂_

data _∋σ_⦂_ : Store → Seal → Ty → Set where
  Zσ : {Σ : Store} {A : Ty} →
       (A ∷ Σ) ∋σ zero ⦂ A
  Sσ : {Σ : Store} {A B : Ty} {s : Seal} →
       Σ ∋σ s ⦂ A →
       (B ∷ Σ) ∋σ suc s ⦂ A

data StoreExt : Store → Store → Set where
  ext-refl : {Σ : Store} → StoreExt Σ Σ
  ext-snoc : {Σ Σ' : Store} {A : Ty} →
             StoreExt Σ Σ' →
             StoreExt Σ (Σ' ∷ʳ A)

lookup-snoc :
  {Σ : Store} {A B : Ty} {s : Seal} →
  Σ ∋σ s ⦂ A →
  (Σ ∷ʳ B) ∋σ s ⦂ A
lookup-snoc Zσ = Zσ
lookup-snoc (Sσ h) = Sσ (lookup-snoc h)

lookup-ext :
  {Σ Σ' : Store} {A : Ty} {s : Seal} →
  StoreExt Σ Σ' →
  Σ ∋σ s ⦂ A →
  Σ' ∋σ s ⦂ A
lookup-ext ext-refl h = h
lookup-ext (ext-snoc ext) h = lookup-snoc (lookup-ext ext h)

lookup-fresh :
  {Σ : Store} {A : Ty} →
  (Σ ∷ʳ A) ∋σ fresh Σ ⦂ A
lookup-fresh {Σ = []} {A = A} = Zσ
lookup-fresh {Σ = B ∷ Σ} {A = A} = Sσ lookup-fresh

ext-trans :
  {Σ₁ Σ₂ Σ₃ : Store} →
  StoreExt Σ₁ Σ₂ →
  StoreExt Σ₂ Σ₃ →
  StoreExt Σ₁ Σ₃
ext-trans ext ext-refl = ext
ext-trans ext (ext-snoc ext') = ext-snoc (ext-trans ext ext')

lookup-unique :
  {Σ : Store} {s : Seal} {A B : Ty} →
  Σ ∋σ s ⦂ A →
  Σ ∋σ s ⦂ B →
  A ≡ B
lookup-unique Zσ Zσ = refl
lookup-unique (Sσ hA) (Sσ hB) = lookup-unique hA hB

StoreUnique : Store → Set
StoreUnique Σ = ∀ {s : Seal} {A B : Ty} → Σ ∋σ s ⦂ A → Σ ∋σ s ⦂ B → A ≡ B

storeUnique-snoc :
  {Σ : Store} {A : Ty} →
  StoreUnique Σ →
  StoreUnique (Σ ∷ʳ A)
storeUnique-snoc su hA hB = lookup-unique hA hB

storeUnique-ext :
  {Σ Σ' : Store} →
  StoreExt Σ Σ' →
  StoreUnique Σ →
  StoreUnique Σ'
storeUnique-ext ext-refl su = su
storeUnique-ext (ext-snoc ext) su = storeUnique-snoc (storeUnique-ext ext su)

------------------------------------------------------------------------
-- Runtime name typing and typing judgment
------------------------------------------------------------------------

data NameTy (Δ : TyEnv) (Σ : Store) : TyName → Ty → Set where
  nt-var  : {i : Var} {A : Ty} →
            KnownMember Δ i A →
            NameTy Δ Σ (tvar i) A
  nt-seal : {s : Seal} {A : Ty} →
            Σ ∋σ s ⦂ A →
            NameTy Δ Σ (tseal s) A

nameTy-ext :
  {Δ : TyEnv} {Σ Σ' : Store} {α : TyName} {A : Ty} →
  StoreExt Σ Σ' →
  NameTy Δ Σ α A →
  NameTy Δ Σ' α A
nameTy-ext ext (nt-var h) = nt-var h
nameTy-ext ext (nt-seal h) = nt-seal (lookup-ext ext h)

knownMember-unique :
  {Δ : TyEnv} {i : Var} {A B : Ty} →
  KnownMember Δ i A →
  KnownMember Δ i B →
  A ≡ B
knownMember-unique kz kz = refl
knownMember-unique (ks-absTy hA) (ks-absTy hB) =
  cong (renameᵗ suc) (knownMember-unique hA hB)
knownMember-unique (ks-known hA) (ks-known hB) =
  cong (renameᵗ suc) (knownMember-unique hA hB)

nameTy-unique :
  {Δ : TyEnv} {Σ : Store} {α : TyName} {A B : Ty} →
  NameTy Δ Σ α A →
  NameTy Δ Σ α B →
  A ≡ B
nameTy-unique (nt-var hA) (nt-var hB) = knownMember-unique hA hB
nameTy-unique (nt-seal hA) (nt-seal hB) = lookup-unique hA hB

infix 4 _∣_⊢_⊢_⦂ʳ_

data _∣_⊢_⊢_⦂ʳ_ : TyEnv → Store → Ctx → Term → Ty → Set where
  ⊢ʳvar :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {x : Var} {A : Ty} →
    Γ ∋ x ⦂ A →
    Δ ∣ Σ ⊢ Γ ⊢ var x ⦂ʳ A

  ⊢ʳerr :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {A : Ty} →
    WfTy (tySize Δ) A →
    Δ ∣ Σ ⊢ Γ ⊢ err ⦂ʳ A

  ⊢ʳtrue :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} →
    Δ ∣ Σ ⊢ Γ ⊢ true ⦂ʳ TBool

  ⊢ʳfalse :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} →
    Δ ∣ Σ ⊢ Γ ⊢ false ⦂ʳ TBool

  ⊢ʳlet :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M N : Term} {A B : Ty} →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A →
    Δ ∣ Σ ⊢ (A ∷ Γ) ⊢ N ⦂ʳ B →
    Δ ∣ Σ ⊢ Γ ⊢ letv M N ⦂ʳ B

  ⊢ʳseal :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {α : TyName} {A : Ty} {M : Term} →
    NameTy Δ Σ α A →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A →
    Δ ∣ Σ ⊢ Γ ⊢ seal α M ⦂ʳ nameTy α

  ⊢ʳunseal :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {α : TyName} {A : Ty} {M : Term} →
    NameTy Δ Σ α A →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ nameTy α →
    Δ ∣ Σ ⊢ Γ ⊢ unseal α M ⦂ʳ A

  ⊢ʳis :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {G : Ground} {M : Term} →
    WfGround (tySize Δ) G →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ TDyn →
    Δ ∣ Σ ⊢ Γ ⊢ is G M ⦂ʳ TBool

  ⊢ʳif :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {L M N : Term} {A : Ty} →
    Δ ∣ Σ ⊢ Γ ⊢ L ⦂ʳ TBool →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A →
    Δ ∣ Σ ⊢ Γ ⊢ N ⦂ʳ A →
    Δ ∣ Σ ⊢ Γ ⊢ ifte L M N ⦂ʳ A

  ⊢ʳpair :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M N : Term} {A B : Ty} →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A →
    Δ ∣ Σ ⊢ Γ ⊢ N ⦂ʳ B →
    Δ ∣ Σ ⊢ Γ ⊢ pair M N ⦂ʳ A × B

  ⊢ʳletpair :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M N : Term} {A B C : Ty} →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A × B →
    Δ ∣ Σ ⊢ (A ∷ B ∷ Γ) ⊢ N ⦂ʳ C →
    Δ ∣ Σ ⊢ Γ ⊢ letpair M N ⦂ʳ C

  ⊢ʳlam :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {A B : Ty} {M : Term} →
    WfTy (tySize Δ) A →
    Δ ∣ Σ ⊢ (A ∷ Γ) ⊢ M ⦂ʳ B →
    Δ ∣ Σ ⊢ Γ ⊢ lam A M ⦂ʳ A ⇒ B

  ⊢ʳapp :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M N : Term} {A B : Ty} →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A ⇒ B →
    Δ ∣ Σ ⊢ Γ ⊢ N ⦂ʳ A →
    Δ ∣ Σ ⊢ Γ ⊢ app M N ⦂ʳ B

  ⊢ʳpack :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {A B C : Ty} {cs : CastStack} {M : Term} →
    WfTy (tySize Δ) A →
    (known A ∷ Δ) ∣ Σ ⊢ ⤊ Γ ⊢ M ⦂ʳ B →
    Δ ∣ Σ ⊢ Γ ⊢ pack A cs M ⦂ʳ Exists C

  ⊢ʳunpack :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M N : Term} {A C : Ty} →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ Exists A →
    (absTy ∷ Δ) ∣ Σ ⊢ (A ∷ ⤊ Γ) ⊢ N ⦂ʳ renameᵗ suc C →
    Δ ∣ Σ ⊢ Γ ⊢ unpack M N ⦂ʳ C

  ⊢ʳtlam :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M : Term} {A : Ty} →
    (absTy ∷ Δ) ∣ Σ ⊢ ⤊ Γ ⊢ M ⦂ʳ A →
    Δ ∣ Σ ⊢ Γ ⊢ tlam M ⦂ʳ Forall A

  ⊢ʳtapp :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M : Term} {A B : Ty} {α : TyName} →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ Forall A →
    NameTy Δ Σ α B →
    Δ ∣ Σ ⊢ Γ ⊢ tapp M α B ⦂ʳ A [ nameTy α ]ᵗ

  ⊢ʳhide :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {A B : Ty} {M : Term} →
    WfTy (tySize Δ) A →
    (known A ∷ Δ) ∣ Σ ⊢ ⤊ Γ ⊢ M ⦂ʳ renameᵗ suc B →
    Δ ∣ Σ ⊢ Γ ⊢ hide A M ⦂ʳ B

  ⊢ʳinj :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {G : Ground} {M : Term} →
    WfGround (tySize Δ) G →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ groundTy G →
    Δ ∣ Σ ⊢ Γ ⊢ inj G M ⦂ʳ TDyn

  ⊢ʳcast-up :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {p : Prec} {M : Term} →
    WfPrec (tySize Δ) p →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ leftTy p →
    Δ ∣ Σ ⊢ Γ ⊢ cast up p M ⦂ʳ rightTy p

  ⊢ʳcast-down :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {p : Prec} {M : Term} →
    WfPrec (tySize Δ) p →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ rightTy p →
    Δ ∣ Σ ⊢ Γ ⊢ cast down p M ⦂ʳ leftTy p

embed :
  {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M : Term} {A : Ty} →
  Δ ⊢ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A
embed (⊢var h) = ⊢ʳvar h
embed (⊢err hA) = ⊢ʳerr hA
embed ⊢true = ⊢ʳtrue
embed ⊢false = ⊢ʳfalse
embed (⊢let hM hN) = ⊢ʳlet (embed hM) (embed hN)
embed (⊢seal hX hM) = ⊢ʳseal (nt-var hX) (embed hM)
embed (⊢unseal hX hM) = ⊢ʳunseal (nt-var hX) (embed hM)
embed (⊢is hG hM) = ⊢ʳis hG (embed hM)
embed (⊢if hL hM hN) = ⊢ʳif (embed hL) (embed hM) (embed hN)
embed (⊢pair hM hN) = ⊢ʳpair (embed hM) (embed hN)
embed (⊢letpair hM hN) = ⊢ʳletpair (embed hM) (embed hN)
embed (⊢lam hA hM) = ⊢ʳlam hA (embed hM)
embed (⊢app hM hN) = ⊢ʳapp (embed hM) (embed hN)
embed (⊢pack hA hM) = ⊢ʳpack hA (embed hM)
embed (⊢unpack hM hN) = ⊢ʳunpack (embed hM) (embed hN)
embed (⊢tlam hM) = ⊢ʳtlam (embed hM)
embed (⊢tapp hM hB) = ⊢ʳtapp (embed hM) (nt-var hB)
embed (⊢hide hA hM) = ⊢ʳhide hA (embed hM)
embed (⊢inj hG hM) = ⊢ʳinj hG (embed hM)
embed (⊢cast-up hp hM) = ⊢ʳcast-up hp (embed hM)
embed (⊢cast-down hp hM) = ⊢ʳcast-down hp (embed hM)

------------------------------------------------------------------------
-- Store weakening and auxiliary lemmas
------------------------------------------------------------------------

store-weaken :
  {Δ : TyEnv} {Σ Σ' : Store} {Γ : Ctx} {M : Term} {A : Ty} →
  StoreExt Σ Σ' →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A →
  Δ ∣ Σ' ⊢ Γ ⊢ M ⦂ʳ A
store-weaken ext (⊢ʳvar h) = ⊢ʳvar h
store-weaken ext (⊢ʳerr hA) = ⊢ʳerr hA
store-weaken ext ⊢ʳtrue = ⊢ʳtrue
store-weaken ext ⊢ʳfalse = ⊢ʳfalse
store-weaken ext (⊢ʳlet hM hN) = ⊢ʳlet (store-weaken ext hM) (store-weaken ext hN)
store-weaken ext (⊢ʳseal nα hM) = ⊢ʳseal (nameTy-ext ext nα) (store-weaken ext hM)
store-weaken ext (⊢ʳunseal nα hM) = ⊢ʳunseal (nameTy-ext ext nα) (store-weaken ext hM)
store-weaken ext (⊢ʳis hG hM) = ⊢ʳis hG (store-weaken ext hM)
store-weaken ext (⊢ʳif hL hM hN) = ⊢ʳif (store-weaken ext hL) (store-weaken ext hM) (store-weaken ext hN)
store-weaken ext (⊢ʳpair hM hN) = ⊢ʳpair (store-weaken ext hM) (store-weaken ext hN)
store-weaken ext (⊢ʳletpair hM hN) = ⊢ʳletpair (store-weaken ext hM) (store-weaken ext hN)
store-weaken ext (⊢ʳlam hA hM) = ⊢ʳlam hA (store-weaken ext hM)
store-weaken ext (⊢ʳapp hM hN) = ⊢ʳapp (store-weaken ext hM) (store-weaken ext hN)
store-weaken ext (⊢ʳpack hA hM) = ⊢ʳpack hA (store-weaken ext hM)
store-weaken ext (⊢ʳunpack hM hN) = ⊢ʳunpack (store-weaken ext hM) (store-weaken ext hN)
store-weaken ext (⊢ʳtlam hM) = ⊢ʳtlam (store-weaken ext hM)
store-weaken ext (⊢ʳtapp hM nα) = ⊢ʳtapp (store-weaken ext hM) (nameTy-ext ext nα)
store-weaken ext (⊢ʳhide hA hM) = ⊢ʳhide hA (store-weaken ext hM)
store-weaken ext (⊢ʳinj hG hM) = ⊢ʳinj hG (store-weaken ext hM)
store-weaken ext (⊢ʳcast-up hp hM) = ⊢ʳcast-up hp (store-weaken ext hM)
store-weaken ext (⊢ʳcast-down hp hM) = ⊢ʳcast-down hp (store-weaken ext hM)

ty-conv :
  {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M : Term} {A B : Ty} →
  A ≡ B →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ B
ty-conv refl h = h

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl

wf-left : {n : ℕ} {p : Prec} → WfPrec n p → WfTy n (leftTy p)
wf-left wf-pdyn = wf-dyn
wf-left (wf-ptag hG hp) = wf-left hp
wf-left (wf-pname h) = wf-name h
wf-left wf-pbool = wf-bool
wf-left (wf-pprod hp hq) = wf-prod (wf-left hp) (wf-left hq)
wf-left (wf-parr hp hq) = wf-arr (wf-left hp) (wf-left hq)
wf-left (wf-pexists hp) = wf-exists (wf-left hp)
wf-left (wf-pforall hp) = wf-forall (wf-left hp)

------------------------------------------------------------------------
-- Context lookup under list maps
------------------------------------------------------------------------

lookup-map-renameᵗ :
  {Γ : Ctx} {x : Var} {A : Ty} {ρ : Renameᵗ} →
  Γ ∋ x ⦂ A →
  map (renameᵗ ρ) Γ ∋ x ⦂ renameᵗ ρ A
lookup-map-renameᵗ Z = Z
lookup-map-renameᵗ (S h) = S (lookup-map-renameᵗ h)

lookup-map-inv :
  {Γ : Ctx} {x : Var} {B : Ty} {f : Ty → Ty} →
  map f Γ ∋ x ⦂ B →
  Σ Ty (λ A → (Γ ∋ x ⦂ A) ×ᵖ (B ≡ f A))
lookup-map-inv {Γ = A ∷ Γ} {x = zero} Z = A , (Z , refl)
lookup-map-inv {Γ = A ∷ Γ} {x = suc x} (S h) with lookup-map-inv h
... | A' , (hA' , eq) = A' , (S hA' , eq)

------------------------------------------------------------------------
-- Renaming/substitution preserve runtime typing
------------------------------------------------------------------------

RenameWf : Ctx → Ctx → Rename → Set
RenameWf Γ Γ' ρ = ∀ {x A} → Γ ∋ x ⦂ A → Γ' ∋ ρ x ⦂ A

SubstWf : TyEnv → Store → Ctx → Ctx → Subst → Set
SubstWf Δ Σ Γ Γ' σ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Σ ⊢ Γ' ⊢ σ x ⦂ʳ A

RenameWf-ext :
  {Γ Γ' : Ctx} {B : Ty} {ρ : Rename} →
  RenameWf Γ Γ' ρ →
  RenameWf (B ∷ Γ) (B ∷ Γ') (ext ρ)
RenameWf-ext hρ Z = Z
RenameWf-ext hρ (S h) = S (hρ h)

RenameWf-ext2 :
  {Γ Γ' : Ctx} {A B : Ty} {ρ : Rename} →
  RenameWf Γ Γ' ρ →
  RenameWf (A ∷ B ∷ Γ) (A ∷ B ∷ Γ') (ext (ext ρ))
RenameWf-ext2 hρ = RenameWf-ext (RenameWf-ext hρ)

RenameWf-liftTy :
  {Γ Γ' : Ctx} {ρ : Rename} →
  RenameWf Γ Γ' ρ →
  RenameWf (⤊ Γ) (⤊ Γ') ρ
RenameWf-liftTy hρ h with lookup-map-inv h
... | A , (hA , eq)
  rewrite eq = lookup-map-renameᵗ (hρ hA)

typing-rename :
  {Δ : TyEnv} {Σ : Store} {Γ Γ' : Ctx} {M : Term} {A : Ty} {ρ : Rename} →
  RenameWf Γ Γ' ρ →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A →
  Δ ∣ Σ ⊢ Γ' ⊢ rename ρ M ⦂ʳ A
typing-rename hρ (⊢ʳvar h) = ⊢ʳvar (hρ h)
typing-rename hρ (⊢ʳerr hA) = ⊢ʳerr hA
typing-rename hρ ⊢ʳtrue = ⊢ʳtrue
typing-rename hρ ⊢ʳfalse = ⊢ʳfalse
typing-rename hρ (⊢ʳlet hM hN) =
  ⊢ʳlet
    (typing-rename hρ hM)
    (typing-rename (RenameWf-ext hρ) hN)
typing-rename hρ (⊢ʳseal nα hM) =
  ⊢ʳseal nα (typing-rename hρ hM)
typing-rename hρ (⊢ʳunseal nα hM) =
  ⊢ʳunseal nα (typing-rename hρ hM)
typing-rename hρ (⊢ʳis hG hM) =
  ⊢ʳis hG (typing-rename hρ hM)
typing-rename hρ (⊢ʳif hL hM hN) =
  ⊢ʳif
    (typing-rename hρ hL)
    (typing-rename hρ hM)
    (typing-rename hρ hN)
typing-rename hρ (⊢ʳpair hM hN) =
  ⊢ʳpair
    (typing-rename hρ hM)
    (typing-rename hρ hN)
typing-rename hρ (⊢ʳletpair hM hN) =
  ⊢ʳletpair
    (typing-rename hρ hM)
    (typing-rename (RenameWf-ext2 hρ) hN)
typing-rename hρ (⊢ʳlam hA hM) =
  ⊢ʳlam hA (typing-rename (RenameWf-ext hρ) hM)
typing-rename hρ (⊢ʳapp hM hN) =
  ⊢ʳapp
    (typing-rename hρ hM)
    (typing-rename hρ hN)
typing-rename hρ (⊢ʳpack hA hM) =
  ⊢ʳpack hA (typing-rename (RenameWf-liftTy hρ) hM)
typing-rename hρ (⊢ʳunpack hM hN) =
  ⊢ʳunpack
    (typing-rename hρ hM)
    (typing-rename (RenameWf-ext (RenameWf-liftTy hρ)) hN)
typing-rename hρ (⊢ʳtlam hM) =
  ⊢ʳtlam (typing-rename (RenameWf-liftTy hρ) hM)
typing-rename hρ (⊢ʳtapp hM nα) =
  ⊢ʳtapp (typing-rename hρ hM) nα
typing-rename hρ (⊢ʳhide hA hM) =
  ⊢ʳhide hA (typing-rename (RenameWf-liftTy hρ) hM)
typing-rename hρ (⊢ʳinj hG hM) =
  ⊢ʳinj hG (typing-rename hρ hM)
typing-rename hρ (⊢ʳcast-up hp hM) =
  ⊢ʳcast-up hp (typing-rename hρ hM)
typing-rename hρ (⊢ʳcast-down hp hM) =
  ⊢ʳcast-down hp (typing-rename hρ hM)

rename-shift :
  {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M : Term} {A B : Ty} →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A →
  Δ ∣ Σ ⊢ (B ∷ Γ) ⊢ rename suc M ⦂ʳ A
rename-shift hM =
  typing-rename (λ {x} {A} h → S h) hM

SubstWf-exts :
  {Δ : TyEnv} {Σ : Store} {Γ Γ' : Ctx} {B : Ty} {σ : Subst} →
  SubstWf Δ Σ Γ Γ' σ →
  SubstWf Δ Σ (B ∷ Γ) (B ∷ Γ') (exts σ)
SubstWf-exts hσ Z = ⊢ʳvar Z
SubstWf-exts hσ (S h) = rename-shift (hσ h)

SubstWf-exts-exts :
  {Δ : TyEnv} {Σ : Store} {Γ Γ' : Ctx} {A B : Ty} {σ : Subst} →
  SubstWf Δ Σ Γ Γ' σ →
  SubstWf Δ Σ (A ∷ B ∷ Γ) (A ∷ B ∷ Γ') (exts (exts σ))
SubstWf-exts-exts hσ Z = ⊢ʳvar Z
SubstWf-exts-exts hσ (S Z) = ⊢ʳvar (S Z)
SubstWf-exts-exts hσ (S (S h)) = rename-shift (rename-shift (hσ h))

postulate
  typing-renameᵀ :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {M : Term} {A : Ty} {I : TyInfo} →
    Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A →
    (I ∷ Δ) ∣ Σ ⊢ ⤊ Γ ⊢ renameᵀ suc M ⦂ʳ renameᵗ suc A

SubstWf-⇑ :
  {Δ : TyEnv} {Σ : Store} {Γ Γ' : Ctx} {I : TyInfo} {σ : Subst} →
  SubstWf Δ Σ Γ Γ' σ →
  SubstWf (I ∷ Δ) Σ (⤊ Γ) (⤊ Γ') (⇑ σ)
SubstWf-⇑ {I = I} hσ h with lookup-map-inv h
... | A , (hA , eq)
  rewrite eq = typing-renameᵀ {I = I} (hσ hA)

typing-subst :
  {Δ : TyEnv} {Σ : Store} {Γ Γ' : Ctx} {M : Term} {A : Ty} {σ : Subst} →
  SubstWf Δ Σ Γ Γ' σ →
  Δ ∣ Σ ⊢ Γ ⊢ M ⦂ʳ A →
  Δ ∣ Σ ⊢ Γ' ⊢ subst σ M ⦂ʳ A
typing-subst hσ (⊢ʳvar h) = hσ h
typing-subst hσ (⊢ʳerr hA) = ⊢ʳerr hA
typing-subst hσ ⊢ʳtrue = ⊢ʳtrue
typing-subst hσ ⊢ʳfalse = ⊢ʳfalse
typing-subst hσ (⊢ʳlet hM hN) =
  ⊢ʳlet
    (typing-subst hσ hM)
    (typing-subst (SubstWf-exts hσ) hN)
typing-subst hσ (⊢ʳseal nα hM) =
  ⊢ʳseal nα (typing-subst hσ hM)
typing-subst hσ (⊢ʳunseal nα hM) =
  ⊢ʳunseal nα (typing-subst hσ hM)
typing-subst hσ (⊢ʳis hG hM) =
  ⊢ʳis hG (typing-subst hσ hM)
typing-subst hσ (⊢ʳif hL hM hN) =
  ⊢ʳif
    (typing-subst hσ hL)
    (typing-subst hσ hM)
    (typing-subst hσ hN)
typing-subst hσ (⊢ʳpair hM hN) =
  ⊢ʳpair
    (typing-subst hσ hM)
    (typing-subst hσ hN)
typing-subst hσ (⊢ʳletpair hM hN) =
  ⊢ʳletpair
    (typing-subst hσ hM)
    (typing-subst (SubstWf-exts-exts hσ) hN)
typing-subst hσ (⊢ʳlam hA hM) =
  ⊢ʳlam hA (typing-subst (SubstWf-exts hσ) hM)
typing-subst hσ (⊢ʳapp hM hN) =
  ⊢ʳapp
    (typing-subst hσ hM)
    (typing-subst hσ hN)
typing-subst hσ (⊢ʳpack hA hM) =
  ⊢ʳpack hA (typing-subst (SubstWf-⇑ hσ) hM)
typing-subst hσ (⊢ʳunpack hM hN) =
  ⊢ʳunpack
    (typing-subst hσ hM)
    (typing-subst (SubstWf-exts (SubstWf-⇑ hσ)) hN)
typing-subst hσ (⊢ʳtlam hM) =
  ⊢ʳtlam (typing-subst (SubstWf-⇑ hσ) hM)
typing-subst hσ (⊢ʳtapp hM nα) =
  ⊢ʳtapp (typing-subst hσ hM) nα
typing-subst hσ (⊢ʳhide hA hM) =
  ⊢ʳhide hA (typing-subst (SubstWf-⇑ hσ) hM)
typing-subst hσ (⊢ʳinj hG hM) =
  ⊢ʳinj hG (typing-subst hσ hM)
typing-subst hσ (⊢ʳcast-up hp hM) =
  ⊢ʳcast-up hp (typing-subst hσ hM)
typing-subst hσ (⊢ʳcast-down hp hM) =
  ⊢ʳcast-down hp (typing-subst hσ hM)

singleSubstWf :
  {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {A : Ty} {V : Term} →
  Δ ∣ Σ ⊢ Γ ⊢ V ⦂ʳ A →
  SubstWf Δ Σ (A ∷ Γ) Γ (singleEnv V)
singleSubstWf hV Z = hV
singleSubstWf hV (S h) = ⊢ʳvar h

pairSubstWf :
  {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {A B : Ty} {V W : Term} →
  Δ ∣ Σ ⊢ Γ ⊢ V ⦂ʳ A →
  Δ ∣ Σ ⊢ Γ ⊢ W ⦂ʳ B →
  SubstWf Δ Σ (A ∷ B ∷ Γ) Γ (pairEnv V W)
pairSubstWf hV hW Z = hV
pairSubstWf hV hW (S Z) = hW
pairSubstWf hV hW (S (S h)) = ⊢ʳvar h

subst-preservation :
  {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {A B : Ty} {N V : Term} →
  Δ ∣ Σ ⊢ (A ∷ Γ) ⊢ N ⦂ʳ B →
  Δ ∣ Σ ⊢ Γ ⊢ V ⦂ʳ A →
  Δ ∣ Σ ⊢ Γ ⊢ N [ V ] ⦂ʳ B
subst-preservation hN hV =
  typing-subst (singleSubstWf hV) hN

subst2-preservation :
  {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {A B C : Ty} {N V W : Term} →
  Δ ∣ Σ ⊢ (A ∷ B ∷ Γ) ⊢ N ⦂ʳ C →
  Δ ∣ Σ ⊢ Γ ⊢ V ⦂ʳ A →
  Δ ∣ Σ ⊢ Γ ⊢ W ⦂ʳ B →
  Δ ∣ Σ ⊢ Γ ⊢ N [ V ][ W ] ⦂ʳ C
subst2-preservation hN hV hW =
  typing-subst (pairSubstWf hV hW) hN

------------------------------------------------------------------------
-- Postulated inversion/typing lemmas (used in β-cases)
------------------------------------------------------------------------

postulate
  substT-preservation-known :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {A B : Ty} {M : Term} {α : TyName} →
    NameTy Δ Σ α A →
    (known A ∷ Δ) ∣ Σ ⊢ ⤊ Γ ⊢ M ⦂ʳ B →
    Δ ∣ Σ ⊢ Γ ⊢ substᵀ (singleTyEnv (nameTy α)) M ⦂ʳ substᵗ (singleTyEnv (nameTy α)) B

  substT-preservation-abs :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {B : Ty} {M : Term} {α : TyName} →
    (absTy ∷ Δ) ∣ Σ ⊢ ⤊ Γ ⊢ M ⦂ʳ B →
    Δ ∣ Σ ⊢ Γ ⊢ substᵀ (singleTyEnv (nameTy α)) M ⦂ʳ substᵗ (singleTyEnv (nameTy α)) B

  hide-redex-preservation :
    {Δ : TyEnv} {Σ : Store} {A B : Ty} {M : Term} →
    (known A ∷ Δ) ∣ Σ ⊢ ⤊ [] ⊢ M ⦂ʳ renameᵗ suc B →
    Δ ∣ (Σ ∷ʳ A) ⊢ [] ⊢ substSealTerm (fresh Σ) M ⦂ʳ B

  unpack-redex-preservation :
    {Δ : TyEnv} {Σ : Store} {Γ : Ctx} {A C : Ty} {cs : CastStack} {M N : Term} →
    Δ ∣ Σ ⊢ Γ ⊢ unpack (pack A cs M) N ⦂ʳ C →
    Δ ∣ (Σ ∷ʳ A) ⊢ Γ ⊢
      subst (singleEnv (applyCastStack (fresh Σ) cs M))
            (substᵀ (singleTyEnv (nameTy (tseal (fresh Σ)))) N) ⦂ʳ C

  closed-wfty :
    {Δ : TyEnv} {Σ : Store} {M : Term} {A : Ty} →
    Δ ∣ Σ ⊢ [] ⊢ M ⦂ʳ A →
    WfTy (tySize Δ) A

  rightTy-subst-single :
    {p : Prec} {α : TyName} →
    rightTy (substPrec (singleTyEnv (nameTy α)) p) ≡
    (rightTy p [ nameTy α ]ᵗ)

  leftTy-subst-single :
    {p : Prec} {α : TyName} →
    leftTy (substPrec (singleTyEnv (nameTy α)) p) ≡
    (leftTy p [ nameTy α ]ᵗ)

  rightTy-ground :
    {n : ℕ} {G : Ground} {p : Prec} →
    WfGround n G →
    WfPrec n p →
    rightTy p ≡ groundTy G

  wfPrec-subst-single :
    {Δ : TyEnv} {Σ : Store} {α : TyName} {B : Ty} {p : Prec} →
    NameTy Δ Σ α B →
    WfPrec (suc (tySize Δ)) p →
    WfPrec (tySize Δ) (substPrec (singleTyEnv (nameTy α)) p)

------------------------------------------------------------------------
-- Preservation for redexes
------------------------------------------------------------------------

redex-preservation :
  {Δ : TyEnv} {Σ Σ' : Store} {A : Ty} {M N : Term} →
  Δ ∣ Σ ⊢ [] ⊢ M ⦂ʳ A →
  Redex Σ M Σ' N →
  StoreExt Σ Σ' ×ᵖ (Δ ∣ Σ' ⊢ [] ⊢ N ⦂ʳ A)
redex-preservation (⊢ʳlet hV hN) (β-let vV) =
  ext-refl , subst-preservation hN hV
redex-preservation (⊢ʳunseal nα (⊢ʳseal nα' hV)) (β-unseal vV) with nameTy-unique nα nα'
... | refl = ext-refl , hV
redex-preservation (⊢ʳis hG (⊢ʳinj hG' hV)) (β-is-yes vV) =
  ext-refl , ⊢ʳtrue
redex-preservation (⊢ʳis hG (⊢ʳinj hG' hV)) (β-is-no vV G≢H) =
  ext-refl , ⊢ʳfalse
redex-preservation (⊢ʳif hL hM hN) β-if-true =
  ext-refl , hM
redex-preservation (⊢ʳif hL hM hN) β-if-false =
  ext-refl , hN
redex-preservation (⊢ʳletpair (⊢ʳpair hV hW) hN) (β-letpair vV vW) =
  ext-refl , subst2-preservation hN hV hW
redex-preservation (⊢ʳapp (⊢ʳlam hA hM) hV) (β-app vV) =
  ext-refl , subst-preservation hM hV
redex-preservation (⊢ʳhide hA hM) β-hide =
  ext-snoc ext-refl , hide-redex-preservation hM
redex-preservation hM β-unpack =
  ext-snoc ext-refl , unpack-redex-preservation hM
redex-preservation (⊢ʳtapp (⊢ʳtlam hM) nα) β-tapp =
  ext-refl , substT-preservation-abs hM
redex-preservation (⊢ʳcast-up hp hV) (β-cast-id-name vV) =
  ext-refl , hV
redex-preservation (⊢ʳcast-down hp hV) (β-cast-id-name vV) =
  ext-refl , hV
redex-preservation (⊢ʳcast-up hp hV) (β-cast-id-bool vV) =
  ext-refl , hV
redex-preservation (⊢ʳcast-down hp hV) (β-cast-id-bool vV) =
  ext-refl , hV
redex-preservation (⊢ʳcast-up hp hV) (β-cast-id-dyn vV) =
  ext-refl , hV
redex-preservation (⊢ʳcast-down hp hV) (β-cast-id-dyn vV) =
  ext-refl , hV
redex-preservation (⊢ʳcast-up (wf-pprod hp hq) (⊢ʳpair hV hW)) (β-cast-prod vV vW) =
  ext-refl , ⊢ʳpair (⊢ʳcast-up hp hV) (⊢ʳcast-up hq hW)
redex-preservation (⊢ʳcast-down (wf-pprod hp hq) (⊢ʳpair hV hW)) (β-cast-prod vV vW) =
  ext-refl , ⊢ʳpair (⊢ʳcast-down hp hV) (⊢ʳcast-down hq hW)
redex-preservation (⊢ʳapp (⊢ʳcast-up (wf-parr hp hq) hV) hW) (β-cast-fun {d = up} vV vW) =
  ext-refl , ⊢ʳcast-up hq (⊢ʳapp hV (⊢ʳcast-down hp hW))
redex-preservation (⊢ʳapp (⊢ʳcast-down (wf-parr hp hq) hV) hW) (β-cast-fun {d = down} vV vW) =
  ext-refl , ⊢ʳcast-down hq (⊢ʳapp hV (⊢ʳcast-up hp hW))
redex-preservation (⊢ʳcast-up hp (⊢ʳpack hA hM)) β-cast-exists =
  ext-refl , ⊢ʳpack hA hM
redex-preservation (⊢ʳcast-down hp (⊢ʳpack hA hM)) β-cast-exists =
  ext-refl , ⊢ʳpack hA hM
redex-preservation
  (⊢ʳtapp {α = α} (⊢ʳcast-up {p = pForall p} (wf-pforall hp) hV) nα)
  (β-cast-forall {p = p} {α = α} vV)
  = ext-refl
  , ty-conv (rightTy-subst-single {p = p} {α = α})
            (⊢ʳcast-up (wfPrec-subst-single nα hp)
              (ty-conv (symm (leftTy-subst-single {p = p} {α = α}))
                (⊢ʳtapp hV nα)))
redex-preservation
  (⊢ʳtapp {α = α} (⊢ʳcast-down {p = pForall p} (wf-pforall hp) hV) nα)
  (β-cast-forall {p = p} {α = α} vV)
  = ext-refl
  , ty-conv (leftTy-subst-single {p = p} {α = α})
            (⊢ʳcast-down (wfPrec-subst-single nα hp)
              (ty-conv (symm (rightTy-subst-single {p = p} {α = α}))
                (⊢ʳtapp hV nα)))
redex-preservation (⊢ʳcast-up (wf-ptag hG hp) hV) (β-cast-tag-up vV) =
  ext-refl
  , ⊢ʳinj hG
      (ty-conv (rightTy-ground hG hp)
               (⊢ʳcast-up hp hV))
redex-preservation (⊢ʳcast-down (wf-ptag hG hp) (⊢ʳinj hG' hV)) (β-cast-tag-down-yes vV) =
  ext-refl
  , ⊢ʳcast-down hp
      (ty-conv (symm (rightTy-ground hG hp)) hV)
redex-preservation (⊢ʳcast-down hp hV) (β-cast-tag-down-no vV G≢H) =
  ext-refl , ⊢ʳerr (wf-left hp)

------------------------------------------------------------------------
-- Preservation under frames
------------------------------------------------------------------------

mutual

  frame-preservation-core :
    {Δ : TyEnv} {Σ Σ' : Store} {A : Ty} {F : Frame} {M N : Term} →
    Δ ∣ Σ ⊢ [] ⊢ plug F M ⦂ʳ A →
    Σ ⊢ M ↦ Σ' ⊢ N →
    StoreExt Σ Σ' ×ᵖ (Δ ∣ Σ' ⊢ [] ⊢ plug F N ⦂ʳ A)
  frame-preservation-core {F = let□ N₀} (⊢ʳlet hM hN) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳlet hM' (store-weaken ext hN)
  frame-preservation-core {F = seal□ α} (⊢ʳseal nα hM) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳseal (nameTy-ext ext nα) hM'
  frame-preservation-core {F = unseal□ α} (⊢ʳunseal nα hM) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳunseal (nameTy-ext ext nα) hM'
  frame-preservation-core {F = is□ G} (⊢ʳis hG hM) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳis hG hM'
  frame-preservation-core {F = if□ N₁ N₂} (⊢ʳif hM hN₁ hN₂) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳif hM' (store-weaken ext hN₁) (store-weaken ext hN₂)
  frame-preservation-core {F = pairL□ N₀} (⊢ʳpair hM hN) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳpair hM' (store-weaken ext hN)
  frame-preservation-core {F = pairR□ V} (⊢ʳpair hV hM) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳpair (store-weaken ext hV) hM'
  frame-preservation-core {F = letpair□ N₀} (⊢ʳletpair hM hN) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳletpair hM' (store-weaken ext hN)
  frame-preservation-core {F = appL□ N₀} (⊢ʳapp hM hN) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳapp hM' (store-weaken ext hN)
  frame-preservation-core {F = appR□ V} (⊢ʳapp hV hM) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳapp (store-weaken ext hV) hM'
  frame-preservation-core {F = unpack□ N₀} (⊢ʳunpack hM hN) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳunpack hM' (store-weaken ext hN)
  frame-preservation-core {F = tapp□ α B} (⊢ʳtapp hM nα) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳtapp hM' (nameTy-ext ext nα)
  frame-preservation-core {F = inj□ G} (⊢ʳinj hG hM) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳinj hG hM'
  frame-preservation-core {F = cast□ up p} (⊢ʳcast-up hp hM) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳcast-up hp hM'
  frame-preservation-core {F = cast□ down p} (⊢ʳcast-down hp hM) s with preservation-core hM s
  ... | ext , hM' = ext , ⊢ʳcast-down hp hM'

  ------------------------------------------------------------------------
  -- Preservation
  ------------------------------------------------------------------------

  preservation-core :
    {Δ : TyEnv} {Σ Σ' : Store} {M N : Term} {A : Ty} →
    Δ ∣ Σ ⊢ [] ⊢ M ⦂ʳ A →
    Σ ⊢ M ↦ Σ' ⊢ N →
    StoreExt Σ Σ' ×ᵖ (Δ ∣ Σ' ⊢ [] ⊢ N ⦂ʳ A)
  preservation-core hM (β r) = redex-preservation hM r
  preservation-core hM (ξξ refl refl s) = frame-preservation-core hM s
  preservation-core hM (ξξ-err refl) = ext-refl , ⊢ʳerr (closed-wfty hM)

------------------------------------------------------------------------
-- Preservation with store-uniqueness invariant
------------------------------------------------------------------------

preservation :
  {Δ : TyEnv} {Σ Σ' : Store} {M N : Term} {A : Ty} →
  StoreUnique Σ →
  Δ ∣ Σ ⊢ [] ⊢ M ⦂ʳ A →
  Σ ⊢ M ↦ Σ' ⊢ N →
  StoreUnique Σ' ×ᵖ (StoreExt Σ Σ' ×ᵖ (Δ ∣ Σ' ⊢ [] ⊢ N ⦂ʳ A))
preservation su hM s with preservation-core hM s
... | ext , hN = storeUnique-ext ext su , (ext , hN)
