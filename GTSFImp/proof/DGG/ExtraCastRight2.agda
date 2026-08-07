module proof.DGG.ExtraCastRight2 where

-- File Charter:
--   * Ports the extra-cast-on-the-right development to the version-2
--     cast-term imprecision relation, in stages.
--   * Stage 1: the statements of extra-cast-right and its inst
--     catch-up companion as Set-level definitions, together with the
--     world-extension interface their conclusions need.  Compared with
--     version 1 the statement carries no transport function for the
--     source type: A : Ty Δᴸ is untouched by target-side allocation,
--     and only the world and the target types evolve.
--     The identity and inert-cast cases are proved directly with reusable
--     zero-change and one-keep world extensions.
--   * The former right-injection inversion and OpenStrata adapter have
--     moved to `proof.DGG.Inversion`; this file is intentionally only
--     the Stage-1 extra-cast-right surface consumed by later milestones.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong)
  renaming (subst to subst≡)

open import Types
open import Consistency using (Env∼; _⊢_∼_; id; inst_)
import Consistency as C
open import Imprecision
open import CastTerms
open import Reduction
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open CTI2 using
  (World; sourceStoreʷ; targetStoreʷ; _⊑ᵂ⟨_⟩_;
   CtxImp; ctx-imp; _∣_⊢²_⊑_∶_)
import proof.Imprecision as PI

------------------------------------------------------------------------
-- Stage 1: statements
------------------------------------------------------------------------

-- A right-side world extension: the source store is untouched, the
-- target store follows the machine's store changes, and every type
-- obligation transports with the change.

record WorldExtendᴿ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    (χs : StoreChanges Δᴿ Δᴿ′) (W : World Δᴸ Δᴿ Δ)
    (W′ : World Δᴸ Δᴿ′ Δ′) : Set where
  field
    sourceStore-kept : sourceStoreʷ W′ ≡ sourceStoreʷ W
    targetStore-follows : targetStoreʷ W′ ≡ (χs ▶ˢ targetStoreʷ W)
    transport⊑ᵂ : ∀ {A : Ty Δᴸ} {C : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ C
      → A ⊑ᵂ⟨ W′ ⟩ (χs ▶ᵗ C)

open WorldExtendᴿ public

sameWorldExtendᴿ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → WorldExtendᴿ [] W W
sameWorldExtendᴿ = record
  { sourceStore-kept = refl
  ; targetStore-follows = refl
  ; transport⊑ᵂ = λ p → p
  }

sameWorldKeepExtendᴿ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → WorldExtendᴿ (Reduction.keep ∷ []) W W
sameWorldKeepExtendᴿ = record
  { sourceStore-kept = refl
  ; targetStore-follows = refl
  ; transport⊑ᵂ = λ p → p
  }

mapCtxᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → WorldExtendᴿ χs W W′
  → CtxImp W
  → CtxImp W′
mapCtxᴿ ext [] = []
mapCtxᴿ {χs = χs} ext (ctx-imp A B p ∷ γ) =
  ctx-imp A (χs ▶ᵗ B) (transport⊑ᵂ ext p) ∷ mapCtxᴿ ext γ

mapCtxᴿ-same : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    (γ : CtxImp W)
  → mapCtxᴿ sameWorldExtendᴿ γ ≡ γ
mapCtxᴿ-same [] = refl
mapCtxᴿ-same (ctx-imp A B p ∷ γ) = cong (_ ∷_) (mapCtxᴿ-same γ)

mapCtxᴿ-keep : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    (γ : CtxImp W)
  → mapCtxᴿ sameWorldKeepExtendᴿ γ ≡ γ
mapCtxᴿ-keep [] = refl
mapCtxᴿ-keep (ctx-imp A B p ∷ γ) = cong (_ ∷_) (mapCtxᴿ-keep γ)

-- Extra cast on the right: if related values face an extra target
-- cast, the target alone reduces to a value in an extended world that
-- still relates them.

ExtraCastRight² : Set
ExtraCastRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (c′ : ν ⊢ B ∼ B′)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ c′ ⟩ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            transport⊑ᵂ ext q))

-- The inst catch-up companion: instantiating a polymorphic target
-- value allocates on the right and reduces to a value related in the
-- extended world.

InstCatchupRight² : Set
InstCatchupRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → AllValueView M′
  → (c′ : C.instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            transport⊑ᵂ ext q))

-- Inert target casts are already values, so this direct case of
-- extra-cast-right neither changes the target store nor the world.

inert-extra-cast-right² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → (vM′ : Value M′)
  → (c′ : ν ⊢ B ∼ B′)
  → Inert c′
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ c′ ⟩ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            transport⊑ᵂ ext q))
inert-extra-cast-right² {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ c′ inert q =
  Δᴿ , [] , Δ , W , sameWorldExtendᴿ , M′ ⟨ c′ ⟩ ,
  vM′ 《 inert 》 ,
  (M′ ⟨ c′ ⟩ ∎[]) ,
  subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q)
    (sym (mapCtxᴿ-same γ)) (CTI2.⊑cast² c′ M⊑M′ q)

-- An identity cast takes one pure keep step and leaves the original target
-- value.  The input and requested obligations coincide propositionally.

id-extra-cast-right² : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → (vM′ : Value M′)
  → (a : Atom B)
  → (q : A ⊑ᵂ⟨ W ⟩ B)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ id {μ = ν} a ⟩ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            transport⊑ᵂ ext q))
id-extra-cast-right² {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    {M = M} {M′ = M′} {p = p} M⊑M′ vM vM′ a q =
  Δᴿ , Reduction.keep ∷ [] , Δ , W , sameWorldKeepExtendᴿ , M′ ,
  vM′ ,
  (M′ ⟨ id a ⟩
    —→[ Reduction.keep ]⟨ pure-step (β-id vM′) ⟩
  M′ ∎[]) ,
  subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ M′ ∶ q)
    (sym (mapCtxᴿ-keep γ))
    (subst≡ (λ r → W ∣ γ ⊢² M ⊑ M′ ∶ r)
      (PI.⊑-unique p q) M⊑M′)
