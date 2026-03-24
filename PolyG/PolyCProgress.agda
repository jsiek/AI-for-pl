module PolyCProgress where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)

open import PolyC

------------------------------------------------------------------------
-- Progress witness
------------------------------------------------------------------------

data Progress (Σ : Store) (M : Term) : Set where
  done  : Value M → Progress Σ M
  step  : ∀ {Σ' N} → Σ ⊢ M ↦ Σ' ⊢ N → Progress Σ M
  crash : M ≡ err → Progress Σ M

------------------------------------------------------------------------
-- Decidable equality for names and ground tags
------------------------------------------------------------------------

infix 4 _≟TyName_
_≟TyName_ : (α₁ α₂ : TyName) → Dec (α₁ ≡ α₂)
tvar i ≟TyName tvar j with i ≟ j
... | yes refl = yes refl
... | no i≢j   = no (λ { refl → i≢j refl })
tvar i ≟TyName tseal j = no (λ ())
tseal i ≟TyName tvar j = no (λ ())
tseal i ≟TyName tseal j with i ≟ j
... | yes refl = yes refl
... | no i≢j   = no (λ { refl → i≢j refl })

infix 4 _≟Ground_
_≟Ground_ : (G H : Ground) → Dec (G ≡ H)
GName α ≟Ground GName α' with α ≟TyName α'
... | yes refl = yes refl
... | no α≢β   = no (λ { refl → α≢β refl })
GName α ≟Ground GBool   = no (λ ())
GName α ≟Ground GProd   = no (λ ())
GName α ≟Ground GFun    = no (λ ())
GName α ≟Ground GExists = no (λ ())
GName α ≟Ground GForall = no (λ ())
GBool ≟Ground GName α'  = no (λ ())
GBool ≟Ground GBool     = yes refl
GBool ≟Ground GProd     = no (λ ())
GBool ≟Ground GFun      = no (λ ())
GBool ≟Ground GExists   = no (λ ())
GBool ≟Ground GForall   = no (λ ())
GProd ≟Ground GName α'  = no (λ ())
GProd ≟Ground GBool     = no (λ ())
GProd ≟Ground GProd     = yes refl
GProd ≟Ground GFun      = no (λ ())
GProd ≟Ground GExists   = no (λ ())
GProd ≟Ground GForall   = no (λ ())
GFun ≟Ground GName α'   = no (λ ())
GFun ≟Ground GBool      = no (λ ())
GFun ≟Ground GProd      = no (λ ())
GFun ≟Ground GFun       = yes refl
GFun ≟Ground GExists    = no (λ ())
GFun ≟Ground GForall    = no (λ ())
GExists ≟Ground GName α' = no (λ ())
GExists ≟Ground GBool   = no (λ ())
GExists ≟Ground GProd   = no (λ ())
GExists ≟Ground GFun    = no (λ ())
GExists ≟Ground GExists = yes refl
GExists ≟Ground GForall = no (λ ())
GForall ≟Ground GName α' = no (λ ())
GForall ≟Ground GBool   = no (λ ())
GForall ≟Ground GProd   = no (λ ())
GForall ≟Ground GFun    = no (λ ())
GForall ≟Ground GExists = no (λ ())
GForall ≟Ground GForall = yes refl

------------------------------------------------------------------------
-- Canonical forms for closed values
------------------------------------------------------------------------

data BoolCanon (V : Term) : Set where
  ctrue  : V ≡ true → BoolCanon V
  cfalse : V ≡ false → BoolCanon V

canonical-bool :
  ∀ {Δ V} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ TBool →
  BoolCanon V
canonical-bool vtrue ⊢true = ctrue refl
canonical-bool vfalse ⊢false = cfalse refl
canonical-bool (vseal vV) ()
canonical-bool (vpair vV vW) ()
canonical-bool vlam ()
canonical-bool vtlam ()
canonical-bool (vinj vV) ()
canonical-bool (vcast-fun vV) ()
canonical-bool (vcast-forall vV) ()
canonical-bool vpack ()

data DynCanon (V : Term) : Set where
  cinj :
    {G : Ground} {W : Term} →
    Value W →
    V ≡ inj G W →
    DynCanon V

canonical-dyn :
  ∀ {Δ V} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ TDyn →
  DynCanon V
canonical-dyn (vinj vW) (⊢inj hG hW) = cinj vW refl
canonical-dyn vtrue ()
canonical-dyn vfalse ()
canonical-dyn (vseal vV) ()
canonical-dyn (vpair vV vW) ()
canonical-dyn vlam ()
canonical-dyn vtlam ()
canonical-dyn (vcast-fun vV) ()
canonical-dyn (vcast-forall vV) ()
canonical-dyn vpack ()

data ProdCanon (V : Term) : Set where
  cpair :
    {W₁ W₂ : Term} →
    Value W₁ →
    Value W₂ →
    V ≡ pair W₁ W₂ →
    ProdCanon V

canonical-prod :
  ∀ {Δ V A B} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ A × B →
  ProdCanon V
canonical-prod (vpair vW₁ vW₂) (⊢pair hW₁ hW₂) = cpair vW₁ vW₂ refl
canonical-prod vtrue ()
canonical-prod vfalse ()
canonical-prod (vseal vV) ()
canonical-prod vlam ()
canonical-prod vtlam ()
canonical-prod (vinj vV) ()
canonical-prod (vcast-fun vV) ()
canonical-prod (vcast-forall vV) ()
canonical-prod vpack ()

data NameCanon (α : TyName) (V : Term) : Set where
  cseal :
    {W : Term} →
    Value W →
    V ≡ seal α W →
    NameCanon α V

canonical-name :
  ∀ {Δ α V} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ nameTy α →
  NameCanon α V
canonical-name (vseal vW) (⊢seal hα hW) = cseal vW refl
canonical-name vtrue ()
canonical-name vfalse ()
canonical-name (vpair vV vW) ()
canonical-name vlam ()
canonical-name vtlam ()
canonical-name (vinj vV) ()
canonical-name (vcast-fun vV) ()
canonical-name (vcast-forall vV) ()
canonical-name vpack ()

data FunCanon (V : Term) : Set where
  clam :
    {A : Ty} {N : Term} →
    V ≡ lam A N →
    FunCanon V
  cfun-cast :
    {d : Dir} {p q : Prec} {W : Term} →
    Value W →
    V ≡ cast d (p ⇒⊑ q) W →
    FunCanon V

canonical-fun :
  ∀ {Δ V A B} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ A ⇒ B →
  FunCanon V
canonical-fun vlam (⊢lam hA hN) = clam refl
canonical-fun (vcast-fun vW) (⊢cast-up hp hW) = cfun-cast vW refl
canonical-fun (vcast-fun vW) (⊢cast-down hp hW) = cfun-cast vW refl
canonical-fun vtrue ()
canonical-fun vfalse ()
canonical-fun (vseal vV) ()
canonical-fun (vpair vV vW) ()
canonical-fun vtlam ()
canonical-fun (vinj vV) ()
canonical-fun (vcast-forall vV) ()
canonical-fun vpack ()

data ExistsCanon (V : Term) : Set where
  cpack :
    {A : Ty} {cs : CastStack} {M : Term} →
    V ≡ pack A cs M →
    ExistsCanon V

canonical-exists :
  ∀ {Δ V A} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ Exists A →
  ExistsCanon V
canonical-exists vpack (⊢pack hA hM) = cpack refl
canonical-exists vtrue ()
canonical-exists vfalse ()
canonical-exists (vseal vV) ()
canonical-exists (vpair vV vW) ()
canonical-exists vlam ()
canonical-exists vtlam ()
canonical-exists (vinj vV) ()
canonical-exists (vcast-fun vV) ()
canonical-exists (vcast-forall vV) ()

data ForallCanon (V : Term) : Set where
  ctlam :
    {M : Term} →
    V ≡ tlam M →
    ForallCanon V
  cforall-cast :
    {d : Dir} {p : Prec} {W : Term} →
    Value W →
    V ≡ cast d (pForall p) W →
    ForallCanon V

canonical-forall :
  ∀ {Δ V A} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ Forall A →
  ForallCanon V
canonical-forall vtlam (⊢tlam hM) = ctlam refl
canonical-forall (vcast-forall vW) (⊢cast-up hp hW) = cforall-cast vW refl
canonical-forall (vcast-forall vW) (⊢cast-down hp hW) = cforall-cast vW refl
canonical-forall vtrue ()
canonical-forall vfalse ()
canonical-forall (vseal vV) ()
canonical-forall (vpair vV vW) ()
canonical-forall vlam ()
canonical-forall (vinj vV) ()
canonical-forall (vcast-fun vV) ()
canonical-forall vpack ()

------------------------------------------------------------------------
-- Cast progress helpers
------------------------------------------------------------------------

cast-up-progress :
  ∀ {Σ Δ V p} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ leftTy p →
  Progress Σ (cast up p V)
cast-up-progress {p = pDyn} vV hV = step (β (β-cast-id-dyn vV))
cast-up-progress {p = pName α} vV hV = step (β (β-cast-id-name vV))
cast-up-progress {p = pBool} vV hV = step (β (β-cast-id-bool vV))
cast-up-progress {p = p ×⊑ q} vV hV with canonical-prod vV hV
... | cpair vW₁ vW₂ refl = step (β (β-cast-prod vW₁ vW₂))
cast-up-progress {p = p ⇒⊑ q} vV hV = done (vcast-fun vV)
cast-up-progress {p = pExists p} vV hV with canonical-exists vV hV
... | cpack refl = step (β β-cast-exists)
cast-up-progress {p = pForall p} vV hV = done (vcast-forall vV)
cast-up-progress {p = pTag G p} vV hV = step (β (β-cast-tag-up vV))

cast-down-progress :
  ∀ {Σ Δ V p} →
  Value V →
  Δ ⊢ [] ⊢ V ⦂ rightTy p →
  Progress Σ (cast down p V)
cast-down-progress {p = pDyn} vV hV = step (β (β-cast-id-dyn vV))
cast-down-progress {p = pName α} vV hV = step (β (β-cast-id-name vV))
cast-down-progress {p = pBool} vV hV = step (β (β-cast-id-bool vV))
cast-down-progress {p = p ×⊑ q} vV hV with canonical-prod vV hV
... | cpair vW₁ vW₂ refl = step (β (β-cast-prod vW₁ vW₂))
cast-down-progress {p = p ⇒⊑ q} vV hV = done (vcast-fun vV)
cast-down-progress {p = pExists p} vV hV with canonical-exists vV hV
... | cpack refl = step (β β-cast-exists)
cast-down-progress {p = pForall p} vV hV = done (vcast-forall vV)
cast-down-progress {p = pTag G p} vV hV with canonical-dyn vV hV
... | cinj {G = H} {W = W} vW refl with G ≟Ground H
...   | yes refl = step (β (β-cast-tag-down-yes vW))
...   | no G≢H   = step (β (β-cast-tag-down-no vW G≢H))

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress :
  ∀ {Δ M A} →
  (Σ : Store) →
  Δ ⊢ [] ⊢ M ⦂ A →
  Progress Σ M
progress Σ (⊢var ())
progress Σ (⊢err hA) = crash refl
progress Σ ⊢true = done vtrue
progress Σ ⊢false = done vfalse
progress Σ (⊢let {M = M} {N = N} hM hN) with progress Σ hM
... | step M↦M' = step (ξ (let□ N) M↦M')
... | crash refl = step (ξ-err (let□ N))
... | done vM = step (β (β-let vM))
progress Σ (⊢seal {i = i} hX hM) with progress Σ hM
... | step M↦M' = step (ξ (seal□ (tvar i)) M↦M')
... | crash refl = step (ξ-err (seal□ (tvar i)))
... | done vM = done (vseal vM)
progress Σ (⊢unseal {i = i} hX hM) with progress Σ hM
... | step M↦M' = step (ξ (unseal□ (tvar i)) M↦M')
... | crash refl = step (ξ-err (unseal□ (tvar i)))
... | done vM with canonical-name vM hM
...   | cseal vW refl = step (β (β-unseal vW))
progress Σ (⊢is {G = G} hG hM) with progress Σ hM
... | step M↦M' = step (ξ (is□ G) M↦M')
... | crash refl = step (ξ-err (is□ G))
... | done vM with canonical-dyn vM hM
...   | cinj {G = H} {W = W} vW refl with G ≟Ground H
...     | yes refl = step (β (β-is-yes vW))
...     | no G≢H   = step (β (β-is-no vW G≢H))
progress Σ (⊢if {M = M} {N = N} hL hM hN) with progress Σ hL
... | step L↦L' = step (ξ (if□ M N) L↦L')
... | crash refl = step (ξ-err (if□ M N))
... | done vL with canonical-bool vL hL
...   | ctrue refl = step (β β-if-true)
...   | cfalse refl = step (β β-if-false)
progress Σ (⊢pair {M = M} {N = N} hM hN) with progress Σ hM
... | step M↦M' = step (ξ (pairL□ N) M↦M')
... | crash refl = step (ξ-err (pairL□ N))
... | done vM with progress Σ hN
...   | step N↦N' = step (ξ (pairR□ M) N↦N')
...   | crash refl = step (ξ-err (pairR□ M))
...   | done vN = done (vpair vM vN)
progress Σ (⊢letpair {M = M} {N = N} hM hN) with progress Σ hM
... | step M↦M' = step (ξ (letpair□ N) M↦M')
... | crash refl = step (ξ-err (letpair□ N))
... | done vM with canonical-prod vM hM
...   | cpair vW₁ vW₂ refl = step (β (β-letpair vW₁ vW₂))
progress Σ (⊢lam hA hM) = done vlam
progress Σ (⊢app {M = M} {N = N} hM hN) with progress Σ hM
... | step M↦M' = step (ξ (appL□ N) M↦M')
... | crash refl = step (ξ-err (appL□ N))
... | done vM with progress Σ hN
...   | step N↦N' = step (ξ (appR□ M) N↦N')
...   | crash refl = step (ξ-err (appR□ M))
...   | done vN with canonical-fun vM hM
...     | clam refl = step (β (β-app vN))
...     | cfun-cast vW refl = step (β (β-cast-fun vW vN))
progress Σ (⊢pack hA hM) = done vpack
progress Σ (⊢unpack {M = M} {N = N} hM hN) with progress Σ hM
... | step M↦M' = step (ξ (unpack□ N) M↦M')
... | crash refl = step (ξ-err (unpack□ N))
... | done vM with canonical-exists vM hM
...   | cpack refl = step (β β-unpack)
progress Σ (⊢tlam hM) = done vtlam
progress Σ (⊢tapp {M = M} {B = B} {i = i} hM hB) with progress Σ hM
... | step M↦M' = step (ξ (tapp□ (tvar i) B) M↦M')
... | crash refl = step (ξ-err (tapp□ (tvar i) B))
... | done vM with canonical-forall vM hM
...   | ctlam refl = step (β β-tapp)
...   | cforall-cast vW refl = step (β (β-cast-forall vW))
progress Σ (⊢hide hA hM) = step (β β-hide)
progress Σ (⊢inj {G = G} hG hM) with progress Σ hM
... | step M↦M' = step (ξ (inj□ G) M↦M')
... | crash refl = step (ξ-err (inj□ G))
... | done vM = done (vinj vM)
progress Σ (⊢cast-up {p = p} hp hM) with progress Σ hM
... | step M↦M' = step (ξ (cast□ up p) M↦M')
... | crash refl = step (ξ-err (cast□ up p))
... | done vM = cast-up-progress vM hM
progress Σ (⊢cast-down {p = p} hp hM) with progress Σ hM
... | step M↦M' = step (ξ (cast□ down p) M↦M')
... | crash refl = step (ξ-err (cast□ down p))
... | done vM = cast-down-progress vM hM
