module Mediation where

-- File Charter:
--   * Seal-correspondence mediation: renaming-style relations that
--     translate types between the two sides of a `SealCorr`, via its
--     matched entries.  (Coercions are never mediated: the mediated
--     judgment types its raw against the home store only, and the
--     composition records glue one-store factors to it on the nose.)
--   * This is the real home of the design prototyped in
--     proof/MediatedNarrowingPrototype.agda (PR #45): the separated
--     term-narrowing coercion index is typed against one home store
--     and its opposite-side endpoint is mediated through these
--     relations.
--   * Everything here is proved; the store-change transports live in
--     proof/MediationProperties.agda.

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_)

open import Types
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
-- Mediated types
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
