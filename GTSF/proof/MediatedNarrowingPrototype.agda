{-# OPTIONS --allow-unsolved-metas #-}

module proof.MediatedNarrowingPrototype where

-- File Charter:
--   * Prototype of the ρ-mediated, single-home-store coercion index for
--     the separated term-narrowing relation (design discussion
--     2026-07-06; see "Right store changes and shared coercion raws" in
--     SeparatedStoresDGGChecklist.md).
--   * The idea: the relation's coercion index is typed against ONE store
--     (home = right/target here); the seal correspondence ρ mediates the
--     source-side endpoint through a matched-seal renaming.  Store
--     changes on the non-home side then transport the judgment without
--     touching the raw — the shared-raw/one-sided-shift tension
--     dissolves (demo lemmas at the bottom).
--   * Nothing in the live development consumes this module yet.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using
  (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import Types
open import Coercions
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_; Narrowing)
open import StoreCorrespondence

------------------------------------------------------------------------
-- Variable correspondences
------------------------------------------------------------------------

-- A relation between the two sides' type-variable/seal name spaces.
VarCorr : Set₁
VarCorr = TyVar → TyVar → Set

-- Extension under a type binder: both sides gain the same bound
-- variable at zero.  Note this is exactly the shape of the lockstep
-- context extension used by the α⊒αᵗ/⊒αᵗ/ν⊒νᵗ/⊒νᵗ constructors.
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

-- Rename the left side of a mediation.  Instantiated with `suc` and
-- the allocation-shaped inclusions below, this is what moves the
-- source endpoint of the reshaped judgment across a left store change
-- while the home raw stays put.
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

-- Rename the right side.
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

-- Rename both sides (used under gen/inst binders in the crux lemma).
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
  ∀ {V} {A B} → MedTy V A B → MedTy (ExtVar V) (⇑ᵗ A) (⇑ᵗ B)
medTy-⇑ = medTy-map² suc suc ev-suc

------------------------------------------------------------------------
-- Allocation-shaped inclusions on MatchedVar
------------------------------------------------------------------------

-- Left allocation (`left-only zero X ∷ ⇑ˡᶜorr ρ`, the shape of
-- `applyLeftChanges` on a bind): matched pairs survive with the left
-- index bumped.
mv-shiftˡ :
  ∀ {ρ α β} → MatchedVar ρ α β → MatchedVar (⇑ˡᶜorr ρ) (suc α) β
mv-shiftˡ mv-here = mv-here
mv-shiftˡ (mv-there v) = mv-there (mv-shiftˡ v)

mv-left-alloc :
  ∀ {ρ X α β} →
  MatchedVar ρ α β →
  MatchedVar (left-only zero X ∷ ⇑ˡᶜorr ρ) (suc α) β
mv-left-alloc v = mv-there (mv-shiftˡ v)

-- Right allocation (`right-only zero X ∷ ⇑ʳᶜorr ρ`, the shape of
-- `applyRightChange` on a bind): matched pairs survive with the right
-- index bumped.
mv-shiftʳ :
  ∀ {ρ α β} → MatchedVar ρ α β → MatchedVar (⇑ʳᶜorr ρ) α (suc β)
mv-shiftʳ mv-here = mv-here
mv-shiftʳ (mv-there v) = mv-there (mv-shiftʳ v)

mv-right-alloc :
  ∀ {ρ X α β} →
  MatchedVar ρ α β →
  MatchedVar (right-only zero X ∷ ⇑ʳᶜorr ρ) α (suc β)
mv-right-alloc v = mv-there (mv-shiftʳ v)

-- Lockstep allocation (`matched zero A zero B ∷ ⇑ᶜorr ρ`, the shape
-- used by the α⊒αᵗ/ν⊒νᵗ constructors): the induced correspondence is
-- precisely the binder extension of the old one.  This is the formal
-- sense in which the six lockstep constructors and the one-sided
-- theorem formulas become reconcilable under mediation.
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
-- Side conditions for the crux lemma
------------------------------------------------------------------------

-- Modes agree across the correspondence.
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

-- Corresponding names have mediating store payloads.  This is the
-- payload half of what `matched α A β B` entries are meant to record;
-- in the real development it would be maintained by `StoreCorr` (or a
-- widening of it).
StoreMed : VarCorr → Store → Store → Set
StoreMed V ΣL ΣR =
  ∀ {α β A} → V α β → (α , A) ∈ ΣL →
  Σ[ B ∈ Ty ] ((β , B) ∈ ΣR) × MedTy V A B

-- The right image of the correspondence is in scope.
VarScopedʳ : VarCorr → TyCtx → Set
VarScopedʳ V ΔR = ∀ {α β} → V α β → β < ΔR

varScopedʳ-ext :
  ∀ {V ΔR} → VarScopedʳ V ΔR → VarScopedʳ (ExtVar V) (suc ΔR)
varScopedʳ-ext sc ev-zero = s≤s z≤n
varScopedʳ-ext sc (ev-suc v) = s≤s (sc v)

-- StoreMed transport under the binder-crossing store shifts of
-- cast-all / cast-gen / cast-inst.  Structural (⟰ᵗ bumps every key
-- and payload in both stores at once); membership plumbing left as
-- holes in the prototype.
storeMed-⟰ :
  ∀ {V ΣL ΣR} →
  StoreMed V ΣL ΣR →
  StoreMed (ExtVar V) (⟰ᵗ ΣL) (⟰ᵗ ΣR)
storeMed-⟰ sm = {! storeMed-shift !}

storeMed-inst :
  ∀ {V ΣL ΣR} →
  StoreMed V ΣL ΣR →
  StoreMed (ExtVar V) ((0 , ★) ∷ ⟰ᵗ ΣL) ((0 , ★) ∷ ⟰ᵗ ΣR)
storeMed-inst sm = {! storeMed-shift-inst !}

------------------------------------------------------------------------
-- Boolean side-condition transport
------------------------------------------------------------------------

∧-split :
  ∀ {a b : Bool} → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-split {true} {b} eq = refl , eq
∧-split {false} {b} ()

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
med-idTyAllowed mc (med-var v) ok = trans (sym (cong idModeAllowed (mc v))) ok
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

-- `occurs zero` is stable under a mediation that fixes zero (ExtVar
-- shape).  Needed by the cast-gen / cast-inst cases; boolean plumbing
-- left as a hole in the prototype.
med-occurs :
  ∀ {V A A′} →
  MedTy (ExtVar V) A A′ →
  occurs zero A ≡ true →
  occurs zero A′ ≡ true
med-occurs med ok = {! med-occurs-zero !}

------------------------------------------------------------------------
-- The crux lemma: mediation preserves coercion typing across stores
------------------------------------------------------------------------

-- Given corresponding modes, mediating store payloads, and a mediated
-- raw, a typing in the left store yields a typing of the mediated raw
-- in the right store, at mediated endpoints.  This is the lemma that
-- replaces the shared-raw demand of the current 7-tuple judgment.
med-cast-typing :
  ∀ {V μL μR ΔR ΣL ΣR c c′ A B} {ΔL : TyCtx} →
  Functional V →
  ModeCorr V μL μR →
  StoreMed V ΣL ΣR →
  VarScopedʳ V ΔR →
  MedCo V c c′ →
  μL ∣ ΔL ∣ ΣL ⊢ c ∶ A =⇒ B →
  Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ]
    MedTy V A A′ × MedTy V B B′ ×
    (μR ∣ ΔR ∣ ΣR ⊢ c′ ∶ A′ =⇒ B′)
med-cast-typing f mc sm sc (medc-id med) (cast-id wfA ok) =
  _ , _ , med , med ,
  cast-id (med-wf sc med) (med-idTyAllowed mc med ok)
med-cast-typing f mc sm sc (medc-seal v med) (cast-seal wfA α∈ mok)
  with sm v α∈
... | P , β∈ , medP
  with medTy-functional f med medP
... | refl =
  _ , _ , med , med-var v ,
  cast-seal (med-wf sc med) β∈
    (trans (sym (cong sealModeAllowed (mc v))) mok)
med-cast-typing f mc sm sc (medc-unseal v med) (cast-unseal wfA α∈ mok)
  with sm v α∈
... | P , β∈ , medP
  with medTy-functional f med medP
... | refl =
  _ , _ , med-var v , med ,
  cast-unseal (med-wf sc med) β∈
    (trans (sym (cong sealModeAllowed (mc v))) mok)
med-cast-typing f mc sm sc (medc-seq ms mt) (cast-seq s⊢ t⊢)
  with med-cast-typing f mc sm sc ms s⊢
... | A′ , B₁ , medA , medB₁ , s⊢′
  with med-cast-typing f mc sm sc mt t⊢
... | B₂ , C′ , medB₂ , medC , t⊢′
  with medTy-functional f medB₂ medB₁
... | refl =
  A′ , C′ , medA , medC , cast-seq s⊢′ t⊢′
med-cast-typing f mc sm sc (medc-tag med) (cast-tag wfG gG tok) =
  _ , _ , med , med-★ ,
  cast-tag (med-wf sc med) (med-ground med gG)
    (med-tagTyAllowed mc med tok)
med-cast-typing f mc sm sc (medc-untag med) (cast-untag wfH gH tok) =
  _ , _ , med-★ , med ,
  cast-untag (med-wf sc med) (med-ground med gH)
    (med-tagTyAllowed mc med tok)
med-cast-typing f mc sm sc (medc-fun ms mt) (cast-fun s⊢ t⊢)
  with med-cast-typing f mc sm sc ms s⊢
     | med-cast-typing f mc sm sc mt t⊢
... | A′₁ , A₁ , medA′ , medA , s⊢′
    | B₁ , B′₁ , medB , medB′ , t⊢′ =
  _ , _ , med-⇒ medA medB , med-⇒ medA′ medB′ ,
  cast-fun s⊢′ t⊢′
med-cast-typing f mc sm sc (medc-all ms) (cast-all s⊢)
  with med-cast-typing (extVar-functional f) (modeCorr-ext mc)
         (storeMed-⟰ sm) (varScopedʳ-ext sc) ms s⊢
... | A₁ , B₁ , medA , medB , s⊢′ =
  _ , _ , med-∀ medA , med-∀ medB , cast-all s⊢′
med-cast-typing f mc sm sc (medc-gen medA ms) (cast-gen wfA occ s⊢)
  with med-cast-typing (extVar-functional f) (modeCorr-gen mc)
         (storeMed-⟰ sm) (varScopedʳ-ext sc) ms s⊢
... | A₁ , B₁ , medA₁ , medB , s⊢′
  with medTy-functional (extVar-functional f) medA₁ (medTy-⇑ medA)
... | refl =
  _ , _ , medA , med-∀ medB ,
  cast-gen (med-wf sc medA) (med-occurs medB occ) s⊢′
med-cast-typing f mc sm sc (medc-inst medB ms) (cast-inst wfB occ s⊢)
  with med-cast-typing (extVar-functional f) (modeCorr-inst mc)
         (storeMed-inst sm) (varScopedʳ-ext sc) ms s⊢
... | A₁ , B₁ , medA , medB₁ , s⊢′
  with medTy-functional (extVar-functional f) medB₁ (medTy-⇑ medB)
... | refl =
  _ , _ , med-∀ medA , medB ,
  cast-inst (med-wf sc medB) (med-occurs medA occ) s⊢′

-- The structural Narrowing witness only inspects the shape of the raw,
-- which mediation preserves; transport left as a hole in the
-- prototype (large mutual data, no conceptual content).
med-narrowing-witness :
  ∀ {V c c′} → MedCo V c c′ → Narrowing c → Narrowing c′
med-narrowing-witness med w = {! med-narrowing-witness !}

------------------------------------------------------------------------
-- The reshaped judgment (home = right)
------------------------------------------------------------------------

-- The coercion index is typed against the right (target) store only;
-- ρ mediates the source-side endpoint.  Compare with the current
-- 7-tuple in TermNarrowingSeparated, whose two store typings share one
-- raw and one pair of endpoints.
_∣_∣_∣_⊢ᵐ_∶_⊒_ :
  ModeEnv → TyCtx → TyCtx → SealCorr → Coercion → Ty → Ty → Set₁
μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ᵐ r ∶ A ⊒ B =
  StoreCorr ΔL ΔR ρ ×
  WfTy ΔL A ×
  WfTy ΔR B ×
  Σ[ Aʳ ∈ Ty ]
    MedTy (MatchedVar ρ) A Aʳ ×
    (μ ∣ ΔR ∣ rightStore ρ ⊢ r ∶ Aʳ ⊒ B)

------------------------------------------------------------------------
-- Transport demos
------------------------------------------------------------------------

-- WfTy weakening under one fresh variable (local; the development has
-- store-indexed versions, this keeps the prototype self-contained).
wfTy-⇑ : ∀ {Δ A} → WfTy Δ A → WfTy (suc Δ) (⇑ᵗ A)
wfTy-⇑ = go suc (λ x<Δ → s≤s x<Δ)
  where
  go :
    ∀ {Δ Δ′} (r : Renameᵗ) →
    (∀ {X} → X < Δ → r X < Δ′) →
    ∀ {A} → WfTy Δ A → WfTy Δ′ (renameᵗ r A)
  go r k (wfVar lt) = wfVar (k lt)
  go r k wfBase = wfBase
  go r k wf★ = wf★
  go r k (wf⇒ a b) = wf⇒ (go r k a) (go r k b)
  go r k (wf∀ a) =
    wf∀ (go (extᵗ r) k′ a)
    where
    k′ : ∀ {X} → X < _ → extᵗ r X < _
    k′ {zero} lt = s≤s z≤n
    k′ {suc X} (s≤s lt) = s≤s (k lt)

-- Demo 1 (the previously impossible transport): a LEFT store
-- allocation moves the source endpoint and the mediation, and the home
-- raw, its typing, and its endpoints are untouched.  This is the
-- statement whose shared-raw analogue is false today.
left-alloc-transport :
  ∀ {μ ΔL ΔR ρ r A B X} →
  StoreCorr (suc ΔL) ΔR (left-only zero (⇑ᵗ X) ∷ ⇑ˡᶜorr ρ) →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ᵐ r ∶ A ⊒ B →
  μ ∣ suc ΔL ∣ ΔR ∣ (left-only zero (⇑ᵗ X) ∷ ⇑ˡᶜorr ρ)
    ⊢ᵐ r ∶ ⇑ᵗ A ⊒ B
left-alloc-transport {ρ = ρ} {r = r} {B = B} {X = X}
    corr′ (corr , wfA , wfB , Aʳ , med , r⊒) =
  corr′ ,
  wfTy-⇑ wfA ,
  wfB ,
  Aʳ ,
  medTy-mapˡ suc mv-left-alloc med ,
  subst
    (λ Σ → _ ∣ _ ∣ Σ ⊢ r ∶ Aʳ ⊒ B)
    (sym (rightStore-⇑ˡᶜorr ρ))
    r⊒

-- Demo 2: a RIGHT store allocation shifts the home raw and its
-- endpoints together with the home store — exactly what ξ-⟨⟩ does to
-- the coercion it steps under.  The single-store weakening of the
-- home typing is ordinary base-language weakening (hole here); the
-- mediation side is proved.
right-alloc-transport :
  ∀ {μ ΔL ΔR ρ r A B X} →
  StoreCorr ΔL (suc ΔR) (right-only zero (⇑ᵗ X) ∷ ⇑ʳᶜorr ρ) →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ᵐ r ∶ A ⊒ B →
  instᵈ μ ∣ ΔL ∣ suc ΔR ∣ (right-only zero (⇑ᵗ X) ∷ ⇑ʳᶜorr ρ)
    ⊢ᵐ ⇑ᶜ r ∶ A ⊒ ⇑ᵗ B
right-alloc-transport {μ = μ} {ρ = ρ} {r = r} {A = A} {B = B} {X = X}
    corr′ (corr , wfA , wfB , Aʳ , med , r⊒) =
  corr′ ,
  wfA ,
  wfTy-⇑ wfB ,
  ⇑ᵗ Aʳ ,
  medTy-mapʳ suc mv-right-alloc med ,
  {! right-store-shift-weakening !}
  -- needed:
  --   instᵈ μ ∣ suc ΔR ∣ (0 , ⇑ᵗ X) ∷ ⟰ᵗ (rightStore ρ)
  --     ⊢ ⇑ᶜ r ∶ ⇑ᵗ Aʳ ⊒ ⇑ᵗ B
  -- from r⊒ : μ ∣ ΔR ∣ rightStore ρ ⊢ r ∶ Aʳ ⊒ B, modulo
  -- rightStore (right-only zero (⇑ᵗ X) ∷ ⇑ʳᶜorr ρ) ≡
  --   (0 , ⇑ᵗ X) ∷ ⟰ᵗ (rightStore ρ)  (rightStore-⇑ʳᶜorr).
  -- This is one-store weakening in the base language, independent of
  -- the mediation design.
