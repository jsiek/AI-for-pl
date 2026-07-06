module Mediation where

-- File Charter:
--   * Seal-correspondence mediation: renaming-style relations that
--     translate types and coercions between the two sides of a
--     `SealCorr`, via its matched entries.
--   * This is the real home of the design prototyped in
--     proof/MediatedNarrowingPrototype.agda (PR #45): the separated
--     term-narrowing coercion index is typed against one home store
--     and its opposite-side endpoint is mediated through these
--     relations.
--   * Everything here is proved; the store-typing crux lemma lives in
--     proof/MediationProperties.agda.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using
  (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import Coercions
open import StoreCorrespondence

------------------------------------------------------------------------
-- Variable correspondences
------------------------------------------------------------------------

-- A relation between the two sides' type-variable/seal name spaces.
VarCorr : Set₁
VarCorr = TyVar → TyVar → Set

-- Extension under a type binder: both sides gain the same bound
-- variable at zero.  This is also the shape of the lockstep context
-- extension used by the α⊒αᵗ/⊒αᵗ/ν⊒νᵗ/⊒νᵗ constructors
-- (`mv-lockstep` below).
data ExtVar (V : VarCorr) : TyVar → TyVar → Set where
  ev-zero : ExtVar V zero zero
  ev-suc : ∀ {α β} → V α β → ExtVar V (suc α) (suc β)

-- The correspondence induced by the matched entries of a seal
-- correspondence.  Entries carry absolute indices, so no shifting
-- happens at lookup time.
data MatchedVar : SealCorr → TyVar → TyVar → Set where
  mv-here : ∀ {ρ α A β B} →
    MatchedVar (matched α A β B ∷ ρ) α β
  mv-there : ∀ {ρ e α β} →
    MatchedVar ρ α β →
    MatchedVar (e ∷ ρ) α β

------------------------------------------------------------------------
-- Mediated types and coercions
------------------------------------------------------------------------

data MedTy (V : VarCorr) : Ty → Ty → Set where
  med-var : ∀ {α β} →
    V α β →
    MedTy V (＇ α) (＇ β)
  med-base : ∀ {ι} →
    MedTy V (‵ ι) (‵ ι)
  med-★ :
    MedTy V ★ ★
  med-⇒ : ∀ {A A′ B B′} →
    MedTy V A A′ →
    MedTy V B B′ →
    MedTy V (A ⇒ B) (A′ ⇒ B′)
  med-∀ : ∀ {A A′} →
    MedTy (ExtVar V) A A′ →
    MedTy V (`∀ A) (`∀ A′)

data MedCo (V : VarCorr) : Coercion → Coercion → Set where
  medc-id : ∀ {A A′} →
    MedTy V A A′ →
    MedCo V (id A) (id A′)
  medc-seq : ∀ {s s′ t t′} →
    MedCo V s s′ →
    MedCo V t t′ →
    MedCo V (s ︔ t) (s′ ︔ t′)
  medc-fun : ∀ {s s′ t t′} →
    MedCo V s s′ →
    MedCo V t t′ →
    MedCo V (s ↦ t) (s′ ↦ t′)
  medc-all : ∀ {s s′} →
    MedCo (ExtVar V) s s′ →
    MedCo V (`∀ s) (`∀ s′)
  medc-tag : ∀ {G G′} →
    MedTy V G G′ →
    MedCo V (G !) (G′ !)
  medc-untag : ∀ {H H′} →
    MedTy V H H′ →
    MedCo V (H ？) (H′ ？)
  medc-seal : ∀ {α β A A′} →
    V α β →
    MedTy V A A′ →
    MedCo V (seal A α) (seal A′ β)
  medc-unseal : ∀ {α β A A′} →
    V α β →
    MedTy V A A′ →
    MedCo V (unseal α A) (unseal β A′)
  medc-gen : ∀ {A A′ s s′} →
    MedTy V A A′ →
    MedCo (ExtVar V) s s′ →
    MedCo V (gen A s) (gen A′ s′)
  medc-inst : ∀ {B B′ s s′} →
    MedTy V B B′ →
    MedCo (ExtVar V) s s′ →
    MedCo V (inst B s) (inst B′ s′)

------------------------------------------------------------------------
-- Functionality
------------------------------------------------------------------------

Functional : VarCorr → Set
Functional V = ∀ {α β β′} → V α β → V α β′ → β ≡ β′

extVar-functional : ∀ {V} → Functional V → Functional (ExtVar V)
extVar-functional f ev-zero ev-zero = refl
extVar-functional f (ev-suc u) (ev-suc v) = cong suc (f u v)

medTy-functional :
  ∀ {V} → Functional V →
  ∀ {A B B′} → MedTy V A B → MedTy V A B′ → B ≡ B′
medTy-functional f (med-var u) (med-var v)
  with f u v
... | refl = refl
medTy-functional f med-base med-base = refl
medTy-functional f med-★ med-★ = refl
medTy-functional f (med-⇒ a b) (med-⇒ a′ b′)
  with medTy-functional f a a′ | medTy-functional f b b′
... | refl | refl = refl
medTy-functional f (med-∀ a) (med-∀ a′)
  with medTy-functional (extVar-functional f) a a′
... | refl = refl

------------------------------------------------------------------------
-- Renaming a mediation on one side (the transport engine)
------------------------------------------------------------------------

medTy-mapˡ :
  ∀ {V W : VarCorr} (r : Renameᵗ) →
  (∀ {α β} → V α β → W (r α) β) →
  ∀ {A B} → MedTy V A B → MedTy W (renameᵗ r A) B
medTy-mapˡ r f (med-var v) = med-var (f v)
medTy-mapˡ r f med-base = med-base
medTy-mapˡ r f med-★ = med-★
medTy-mapˡ r f (med-⇒ a b) =
  med-⇒ (medTy-mapˡ r f a) (medTy-mapˡ r f b)
medTy-mapˡ {V} {W} r f (med-∀ a) =
  med-∀ (medTy-mapˡ (extᵗ r) f′ a)
  where
  f′ : ∀ {α β} → ExtVar V α β → ExtVar W (extᵗ r α) β
  f′ ev-zero = ev-zero
  f′ (ev-suc v) = ev-suc (f v)

medTy-mapʳ :
  ∀ {V W : VarCorr} (r : Renameᵗ) →
  (∀ {α β} → V α β → W α (r β)) →
  ∀ {A B} → MedTy V A B → MedTy W A (renameᵗ r B)
medTy-mapʳ r f (med-var v) = med-var (f v)
medTy-mapʳ r f med-base = med-base
medTy-mapʳ r f med-★ = med-★
medTy-mapʳ r f (med-⇒ a b) =
  med-⇒ (medTy-mapʳ r f a) (medTy-mapʳ r f b)
medTy-mapʳ {V} {W} r f (med-∀ a) =
  med-∀ (medTy-mapʳ (extᵗ r) f′ a)
  where
  f′ : ∀ {α β} → ExtVar V α β → ExtVar W α (extᵗ r β)
  f′ ev-zero = ev-zero
  f′ (ev-suc v) = ev-suc (f v)

medTy-map² :
  ∀ {V W : VarCorr} (rˡ rʳ : Renameᵗ) →
  (∀ {α β} → V α β → W (rˡ α) (rʳ β)) →
  ∀ {A B} → MedTy V A B → MedTy W (renameᵗ rˡ A) (renameᵗ rʳ B)
medTy-map² rˡ rʳ f (med-var v) = med-var (f v)
medTy-map² rˡ rʳ f med-base = med-base
medTy-map² rˡ rʳ f med-★ = med-★
medTy-map² rˡ rʳ f (med-⇒ a b) =
  med-⇒ (medTy-map² rˡ rʳ f a) (medTy-map² rˡ rʳ f b)
medTy-map² {V} {W} rˡ rʳ f (med-∀ a) =
  med-∀ (medTy-map² (extᵗ rˡ) (extᵗ rʳ) f′ a)
  where
  f′ : ∀ {α β} → ExtVar V α β → ExtVar W (extᵗ rˡ α) (extᵗ rʳ β)
  f′ ev-zero = ev-zero
  f′ (ev-suc v) = ev-suc (f v)

-- The shift of a mediation under a shared binder.
medTy-⇑ :
  ∀ {V A B} → MedTy V A B → MedTy (ExtVar V) (⇑ᵗ A) (⇑ᵗ B)
medTy-⇑ = medTy-map² suc suc ev-suc

-- The binder extension of a left-sided variable-correspondence map,
-- hoisted from the `where` blocks above for reuse by `medCo-mapˡ`.
extVar-mapˡ :
  ∀ {V W : VarCorr} (r : Renameᵗ) →
  (∀ {α β} → V α β → W (r α) β) →
  ∀ {α β} → ExtVar V α β → ExtVar W (extᵗ r α) β
extVar-mapˡ r f ev-zero = ev-zero
extVar-mapˡ r f (ev-suc v) = ev-suc (f v)

-- The coercion sibling of `medTy-mapˡ`: renaming the left raw of a
-- mediated coercion pair along a variable-correspondence map.
medCo-mapˡ :
  ∀ {V W : VarCorr} (r : Renameᵗ) →
  (∀ {α β} → V α β → W (r α) β) →
  ∀ {c c′} → MedCo V c c′ → MedCo W (renameᶜ r c) c′
medCo-mapˡ r f (medc-id med) = medc-id (medTy-mapˡ r f med)
medCo-mapˡ r f (medc-seq ms mt) =
  medc-seq (medCo-mapˡ r f ms) (medCo-mapˡ r f mt)
medCo-mapˡ r f (medc-fun ms mt) =
  medc-fun (medCo-mapˡ r f ms) (medCo-mapˡ r f mt)
medCo-mapˡ {V} {W} r f (medc-all ms) =
  medc-all (medCo-mapˡ (extᵗ r) (extVar-mapˡ {V} {W} r f) ms)
medCo-mapˡ r f (medc-tag med) = medc-tag (medTy-mapˡ r f med)
medCo-mapˡ r f (medc-untag med) = medc-untag (medTy-mapˡ r f med)
medCo-mapˡ r f (medc-seal v med) =
  medc-seal (f v) (medTy-mapˡ r f med)
medCo-mapˡ r f (medc-unseal v med) =
  medc-unseal (f v) (medTy-mapˡ r f med)
medCo-mapˡ {V} {W} r f (medc-gen med ms) =
  medc-gen
    (medTy-mapˡ r f med)
    (medCo-mapˡ (extᵗ r) (extVar-mapˡ {V} {W} r f) ms)
medCo-mapˡ {V} {W} r f (medc-inst med ms) =
  medc-inst
    (medTy-mapˡ r f med)
    (medCo-mapˡ (extᵗ r) (extVar-mapˡ {V} {W} r f) ms)

------------------------------------------------------------------------
-- Allocation-shaped inclusions on MatchedVar
------------------------------------------------------------------------

mv-shiftˡ :
  ∀ {ρ α β} → MatchedVar ρ α β → MatchedVar (⇑ˡᶜorr ρ) (suc α) β
mv-shiftˡ mv-here = mv-here
mv-shiftˡ (mv-there v) = mv-there (mv-shiftˡ v)

mv-left-alloc :
  ∀ {ρ X α β} →
  MatchedVar ρ α β →
  MatchedVar (left-only zero X ∷ ⇑ˡᶜorr ρ) (suc α) β
mv-left-alloc v = mv-there (mv-shiftˡ v)

mv-shiftʳ :
  ∀ {ρ α β} → MatchedVar ρ α β → MatchedVar (⇑ʳᶜorr ρ) α (suc β)
mv-shiftʳ mv-here = mv-here
mv-shiftʳ (mv-there v) = mv-there (mv-shiftʳ v)

mv-right-alloc :
  ∀ {ρ X α β} →
  MatchedVar ρ α β →
  MatchedVar (right-only zero X ∷ ⇑ʳᶜorr ρ) α (suc β)
mv-right-alloc v = mv-there (mv-shiftʳ v)

-- Lockstep allocation: the correspondence induced by the
-- `matched zero _ zero _ ∷ ⇑ᶜorr ρ` extension of the α⊒αᵗ/ν⊒νᵗ
-- constructors is precisely the binder extension of the old one.
mv-shiftᵇ :
  ∀ {ρ α β} → MatchedVar ρ α β → MatchedVar (⇑ᶜorr ρ) (suc α) (suc β)
mv-shiftᵇ mv-here = mv-here
mv-shiftᵇ (mv-there v) = mv-there (mv-shiftᵇ v)

mv-lockstep :
  ∀ {ρ A B α β} →
  ExtVar (MatchedVar ρ) α β →
  MatchedVar (matched zero A zero B ∷ ⇑ᶜorr ρ) α β
mv-lockstep ev-zero = mv-here
mv-lockstep (ev-suc v) = mv-there (mv-shiftᵇ v)

------------------------------------------------------------------------
-- Mode correspondence
------------------------------------------------------------------------

ModeCorr : VarCorr → ModeEnv → ModeEnv → Set
ModeCorr V μL μR = ∀ {α β} → V α β → μL α ≡ μR β

modeCorr-ext :
  ∀ {V μL μR} → ModeCorr V μL μR →
  ModeCorr (ExtVar V) (extᵈ μL) (extᵈ μR)
modeCorr-ext mc ev-zero = refl
modeCorr-ext mc (ev-suc v) = mc v

modeCorr-gen :
  ∀ {V μL μR} → ModeCorr V μL μR →
  ModeCorr (ExtVar V) (genᵈ μL) (genᵈ μR)
modeCorr-gen mc ev-zero = refl
modeCorr-gen mc (ev-suc v) = mc v

modeCorr-inst :
  ∀ {V μL μR} → ModeCorr V μL μR →
  ModeCorr (ExtVar V) (instᵈ μL) (instᵈ μR)
modeCorr-inst mc ev-zero = refl
modeCorr-inst mc (ev-suc v) = mc v

------------------------------------------------------------------------
-- Store mediation
------------------------------------------------------------------------

-- Corresponding names have mediating store payloads: the payload half
-- of what `matched α A β B` entries record.
StoreMed : VarCorr → Store → Store → Set
StoreMed V ΣL ΣR =
  ∀ {α β A} → V α β → (α , A) ∈ ΣL →
  Σ[ B ∈ Ty ] ((β , B) ∈ ΣR) × MedTy V A B

-- Membership in a shifted store.
∈-⟰ᵗ :
  ∀ {Σ α A} → (α , A) ∈ Σ → (suc α , ⇑ᵗ A) ∈ ⟰ᵗ Σ
∈-⟰ᵗ {(_ , _) ∷ Σ} (here refl) = here refl
∈-⟰ᵗ {(_ , _) ∷ Σ} (there m) = there (∈-⟰ᵗ m)

⟰ᵗ-∈-inv :
  ∀ {Σ x C} → (x , C) ∈ ⟰ᵗ Σ →
  Σ[ y ∈ TyVar ] Σ[ B ∈ Ty ]
    (x ≡ suc y) × (C ≡ ⇑ᵗ B) × ((y , B) ∈ Σ)
⟰ᵗ-∈-inv {(α , A) ∷ Σ} (here refl) = α , A , refl , refl , here refl
⟰ᵗ-∈-inv {(α , A) ∷ Σ} (there m)
  with ⟰ᵗ-∈-inv m
... | y , B , eq₁ , eq₂ , m′ = y , B , eq₁ , eq₂ , there m′

storeMed-⟰ :
  ∀ {V ΣL ΣR} →
  StoreMed V ΣL ΣR →
  StoreMed (ExtVar V) (⟰ᵗ ΣL) (⟰ᵗ ΣR)
storeMed-⟰ sm ev-zero m
  with ⟰ᵗ-∈-inv m
... | y , B , () , _ , _
storeMed-⟰ sm (ev-suc v) m
  with ⟰ᵗ-∈-inv m
... | y , B , refl , refl , m′
  with sm v m′
... | C , mR , med =
  ⇑ᵗ C , ∈-⟰ᵗ mR , medTy-⇑ med

storeMed-inst :
  ∀ {V ΣL ΣR} →
  StoreMed V ΣL ΣR →
  StoreMed (ExtVar V) ((0 , ★) ∷ ⟰ᵗ ΣL) ((0 , ★) ∷ ⟰ᵗ ΣR)
storeMed-inst sm ev-zero (here refl) = ★ , here refl , med-★
storeMed-inst sm ev-zero (there m)
  with ⟰ᵗ-∈-inv m
... | y , B , () , _ , _
storeMed-inst sm (ev-suc v) (here ())
storeMed-inst sm (ev-suc v) (there m)
  with storeMed-⟰ sm (ev-suc v) m
... | C , mR , med = C , there mR , med

------------------------------------------------------------------------
-- Scoping
------------------------------------------------------------------------

VarScopedʳ : VarCorr → TyCtx → Set
VarScopedʳ V ΔR = ∀ {α β} → V α β → β < ΔR

varScopedʳ-ext :
  ∀ {V ΔR} → VarScopedʳ V ΔR → VarScopedʳ (ExtVar V) (suc ΔR)
varScopedʳ-ext sc ev-zero = s≤s z≤n
varScopedʳ-ext sc (ev-suc v) = s≤s (sc v)

med-wf :
  ∀ {V ΔR A A′} →
  VarScopedʳ V ΔR →
  MedTy V A A′ →
  WfTy ΔR A′
med-wf sc (med-var v) = wfVar (sc v)
med-wf sc med-base = wfBase
med-wf sc med-★ = wf★
med-wf sc (med-⇒ a b) = wf⇒ (med-wf sc a) (med-wf sc b)
med-wf sc (med-∀ a) = wf∀ (med-wf (varScopedʳ-ext sc) a)

------------------------------------------------------------------------
-- Boolean side-condition transport
------------------------------------------------------------------------

∧-split :
  ∀ {a b : Bool} → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-split {true} {b} eq = refl , eq
∧-split {false} {b} ()

∨-split :
  ∀ {a b : Bool} → a ∨ b ≡ true → (a ≡ true) ⊎ (b ≡ true)
∨-split {true} {b} eq = inj₁ refl
∨-split {false} {b} eq = inj₂ eq

∨-introˡ : ∀ {a b : Bool} → a ≡ true → a ∨ b ≡ true
∨-introˡ refl = refl

∨-introʳ : ∀ {a b : Bool} → b ≡ true → a ∨ b ≡ true
∨-introʳ {true} eq = refl
∨-introʳ {false} eq = eq

med-ground :
  ∀ {V G G′} → MedTy V G G′ → Ground G → Ground G′
med-ground (med-var {β = β} v) (＇ α) = ＇ β
med-ground (med-base {ι = ι}) (‵ .ι) = ‵ ι
med-ground (med-⇒ med-★ med-★) ★⇒★ = ★⇒★

med-idTyAllowed :
  ∀ {V μL μR A A′} →
  ModeCorr V μL μR →
  MedTy V A A′ →
  idTyAllowed μL A ≡ true →
  idTyAllowed μR A′ ≡ true
med-idTyAllowed mc (med-var v) ok =
  trans (sym (cong idModeAllowed (mc v))) ok
med-idTyAllowed mc med-base ok = refl
med-idTyAllowed mc med-★ ok = refl
med-idTyAllowed mc (med-⇒ a b) ok
  with ∧-split ok
... | okA , okB
  rewrite med-idTyAllowed mc a okA | med-idTyAllowed mc b okB = refl
med-idTyAllowed mc (med-∀ a) ok =
  med-idTyAllowed (modeCorr-ext mc) a ok

med-tagTyAllowed :
  ∀ {V μL μR G G′} →
  ModeCorr V μL μR →
  MedTy V G G′ →
  tagTyAllowed μL G ≡ true →
  tagTyAllowed μR G′ ≡ true
med-tagTyAllowed mc (med-var v) ok =
  trans (sym (cong tagModeAllowed (mc v))) ok
med-tagTyAllowed mc med-base ok = refl
med-tagTyAllowed mc med-★ ok = refl
med-tagTyAllowed mc (med-⇒ a b) ok = refl
med-tagTyAllowed mc (med-∀ a) ok = refl

------------------------------------------------------------------------
-- Occurrence transport
------------------------------------------------------------------------

-- Forward pivot: the mediation maps the pivot variable to the pivot.
PivotFwd : VarCorr → TyVar → TyVar → Set
PivotFwd V n m = ∀ {α β} → V α β → α ≡ n → β ≡ m

pivotFwd-ext :
  ∀ {V n m} → PivotFwd V n m →
  PivotFwd (ExtVar V) (suc n) (suc m)
pivotFwd-ext pf ev-zero ()
pivotFwd-ext pf (ev-suc v) refl = cong suc (pf v refl)

pivotFwd-zero : ∀ {V} → PivotFwd (ExtVar V) zero zero
pivotFwd-zero ev-zero eq = refl
pivotFwd-zero (ev-suc v) ()

occurs-var-true :
  ∀ n α → occurs n (＇ α) ≡ true → n ≡ α
occurs-var-true n α eq with n ≟ α
occurs-var-true n α eq | yes p = p
occurs-var-true n α () | no ¬p

occurs-var-refl :
  ∀ m → occurs m (＇ m) ≡ true
occurs-var-refl m with m ≟ m
occurs-var-refl m | yes p = refl
occurs-var-refl m | no ¬p = ⊥-elim (¬p refl)

med-occursᵖ :
  ∀ {V n m A A′} →
  PivotFwd V n m →
  MedTy V A A′ →
  occurs n A ≡ true →
  occurs m A′ ≡ true
med-occursᵖ {n = n} {m = m} pf (med-var {α} {β} v) oc =
  subst
    (λ x → occurs m (＇ x) ≡ true)
    (sym (pf v (sym (occurs-var-true n α oc))))
    (occurs-var-refl m)
med-occursᵖ pf med-base ()
med-occursᵖ pf med-★ ()
med-occursᵖ pf (med-⇒ a b) oc
  with ∨-split oc
... | inj₁ ocA = ∨-introˡ (med-occursᵖ pf a ocA)
... | inj₂ ocB = ∨-introʳ (med-occursᵖ pf b ocB)
med-occursᵖ pf (med-∀ a) oc =
  med-occursᵖ (pivotFwd-ext pf) a oc

-- The instance the cast-gen/cast-inst cases need: under one binder
-- extension the pivot is zero on both sides.
med-occurs :
  ∀ {V A A′} →
  MedTy (ExtVar V) A A′ →
  occurs zero A ≡ true →
  occurs zero A′ ≡ true
med-occurs = med-occursᵖ pivotFwd-zero
