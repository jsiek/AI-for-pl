module proof.DGG.Catchup.StructuralSpineTypingDef where

-- File Charter:
--   * Defines target-store typing evidence for pending instantiation spines.
--   * Supplies store-change transports for `mapInstantiationSpine`.
--   * Builds the typed generated/root spines consumed by NS-4 workers.

import Data.Fin as Fin
open import Data.Nat using (ℕ; suc; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
  renaming (subst to subst≡)

open import Types using (Ty; TyVar; ★; ＇_; `∀; ⇑ᵗ; _[_]ᵗ)
open import TyStore using (TyStore; store-bind; Z∋)
open import Imprecision using (X⊑★)
open import Consistency using
  (Env∼; extᵐ; instᵐ; _⊢_∼_; ↑ᶜ_; close-instᶜ; _[_]ᶜ)
open import CastTerms using (Inert; GenSafe)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑_; _⊢↓_; replaceTy; rename↑; rename↓; 〖_,_↑_〗)
open import Reduction using
  (StoreChange; keep; bind; applyStores; applyTy; applyBody;
   applyConsistency; _∷_; [])
open import proof.Reduction using (applyStoreChange-Inert)
open import proof.TypeInTermSubst using
  (StoreRename-suc-bind; reveal-renameᵗ; conceal-renameᵗ;
   reveal-rename-id; conceal-rename-id; renameᵗ-id; renameᵗ-wk-eq)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open; structural-reveal-typing)
import proof.Consistency as PC
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
open import proof.DGG.Catchup.ValueCatchupRightDef using (castSize)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
import proof.DGG.Catchup.StructuralGeneratedFrameGeometryDef as GFG


data CastFrameClass {fuel : ℕ} {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
    (c : μ ⊢ A ∼ B) : Set where

  cast-inert : Inert c → CastFrameClass {fuel = fuel} c

  cast-safe : GenSafe c → CastFrameClass {fuel = fuel} c

  cast-residual : suc (castSize c) < fuel
    → CastFrameClass {fuel = fuel} c


cast-frame-class-map : ∀ {fuel Δ Δ′ μ A B}
    (χ : StoreChange Δ Δ′) {c : μ ⊢ A ∼ B}
  → CastFrameClass {fuel = fuel} c
  → CastFrameClass {fuel = fuel} (applyConsistency χ c)
cast-frame-class-map {fuel = fuel} keep cls = cls
cast-frame-class-map {fuel = fuel} (bind R) (cast-inert inert) =
  cast-inert {fuel = fuel} (applyStoreChange-Inert (bind R) inert)
cast-frame-class-map {fuel = fuel} (bind R) (cast-safe safe) =
  cast-safe {fuel = fuel} (PC.renameGenSafe Fin.suc (λ X → refl) safe)
cast-frame-class-map {fuel = fuel} (bind R) (cast-residual c<fuel) =
  cast-residual {fuel = fuel}
    (subst≡ (λ n → suc n < _)
      (sym (PC.castSize-renameEnvᶜ Fin.suc (λ X → refl) _))
      c<fuel)


data SpineTyped {fuel : ℕ} {Δ} (Σ : TyStore Δ) :
    ∀ {A B : Ty Δ}
    → InstantiationSpine A B
    → Set where

  st-[] : ∀ {A}
    → SpineTyped {fuel = fuel} Σ ([]ⁱ {A = A})

  st-type : ∀ {A B C}
      {eq : A ≡ B} {spine : InstantiationSpine B C}
    → SpineTyped {fuel = fuel} Σ spine
    → SpineTyped {fuel = fuel} Σ (type-transport-frame eq ▻ⁱ spine)

  st-name : ∀ {A C E X}
      {B : Ty (suc Δ)} {eqA : A ≡ `∀ B}
      {eqC : C ≡ B [ ＇ X ]ᵗ}
      {spine : InstantiationSpine C E}
    → SpineTyped {fuel = fuel} Σ spine
    → SpineTyped {fuel = fuel} Σ
        (name-type-app-frame B X eqA eqC ▻ⁱ spine)

  st-cast : ∀ {A B E μ}
      {c : μ ⊢ A ∼ B} {spine : InstantiationSpine B E}
    → CastFrameClass {fuel = fuel} c
    → SpineTyped {fuel = fuel} Σ spine
    → SpineTyped {fuel = fuel} Σ (cast-frame c ▻ⁱ spine)

  st-reveal : ∀ {A B E}
      {c : Conv↑ Δ A B} {spine : InstantiationSpine B E}
    → Σ ⊢↑ c
    → SpineTyped {fuel = fuel} Σ spine
    → SpineTyped {fuel = fuel} Σ (reveal-frame c ▻ⁱ spine)

  st-conceal : ∀ {A B E}
      {c : Conv↓ Δ A B} {spine : InstantiationSpine B E}
    → Σ ⊢↓ c
    → SpineTyped {fuel = fuel} Σ spine
    → SpineTyped {fuel = fuel} Σ (conceal-frame c ▻ⁱ spine)


SpineTypedʷ : ∀ {fuel Δᴸ Δᴿ Δ} {A B : Ty Δᴿ}
  → CTI2.World Δᴸ Δᴿ Δ
  → InstantiationSpine A B
  → Set
SpineTypedʷ {fuel = fuel} W spine =
  SpineTyped {fuel = fuel} (CTI2.targetStoreʷ W) spine


spine-typed-store-eq : ∀ {fuel Δ} {Σ Σ′ : TyStore Δ}
    {A B : Ty Δ} {spine : InstantiationSpine A B}
  → Σ′ ≡ Σ
  → SpineTyped {fuel = fuel} Σ spine
  → SpineTyped {fuel = fuel} Σ′ spine
spine-typed-store-eq refl typed = typed


normalize-renamed↑-typed : ∀ {Δ} {Σ : TyStore Δ} {A B}
    {c : Conv↑ Δ A B}
  → Σ ⊢↑ c
  → Σ ⊢↑ normalize-renamed↑ c
normalize-renamed↑-typed {A = A} {B = B} {c = c} c⊢ =
  reveal-typing-subst (renameᵗ-id A) (renameᵗ-id B)
    (reveal-rename-id c⊢)
  where
  reveal-typing-subst : ∀ {A₀ A₁ B₀ B₁ : Ty _}
      {d : Conv↑ _ A₀ B₀}
    → (eqA : A₀ ≡ A₁) → (eqB : B₀ ≡ B₁)
    → _ ⊢↑ d
    → _ ⊢↑ subst≡ (Conv↑ _ A₁) eqB
        (subst≡ (λ A′ → Conv↑ _ A′ B₀) eqA d)
  reveal-typing-subst refl refl d⊢ = d⊢


normalize-renamed↓-typed : ∀ {Δ} {Σ : TyStore Δ} {A B}
    {c : Conv↓ Δ A B}
  → Σ ⊢↓ c
  → Σ ⊢↓ normalize-renamed↓ c
normalize-renamed↓-typed {A = A} {B = B} {c = c} c⊢ =
  conceal-typing-subst (renameᵗ-id A) (renameᵗ-id B)
    (conceal-rename-id c⊢)
  where
  conceal-typing-subst : ∀ {A₀ A₁ B₀ B₁ : Ty _}
      {d : Conv↓ _ A₀ B₀}
    → (eqA : A₀ ≡ A₁) → (eqB : B₀ ≡ B₁)
    → _ ⊢↓ d
    → _ ⊢↓ subst≡ (Conv↓ _ A₁) eqB
        (subst≡ (λ A′ → Conv↓ _ A′ B₀) eqA d)
  conceal-typing-subst refl refl d⊢ = d⊢


spine-typed-map-keep : ∀ {fuel Δ} {Σ : TyStore Δ} {A B}
    {spine : InstantiationSpine A B}
  → SpineTyped {fuel = fuel} Σ spine
  → SpineTyped {fuel = fuel} Σ (mapInstantiationSpine keep spine)
spine-typed-map-keep st-[] = st-[]
spine-typed-map-keep (st-type typed) =
  st-type (spine-typed-map-keep typed)
spine-typed-map-keep (st-name typed) =
  st-name (spine-typed-map-keep typed)
spine-typed-map-keep (st-cast cls typed) =
  st-cast (cast-frame-class-map keep cls) (spine-typed-map-keep typed)
spine-typed-map-keep (st-reveal c⊢ typed) =
  st-reveal (normalize-renamed↑-typed c⊢)
    (spine-typed-map-keep typed)
spine-typed-map-keep (st-conceal c⊢ typed) =
  st-conceal (normalize-renamed↓-typed c⊢)
    (spine-typed-map-keep typed)


spine-typed-map-bind : ∀ {fuel Δ} {Σ : TyStore Δ} {A B}
    (R : Ty Δ) {spine : InstantiationSpine A B}
  → SpineTyped {fuel = fuel} Σ spine
  → SpineTyped {fuel = fuel} (store-bind Σ R)
      (mapInstantiationSpine (bind R) spine)
spine-typed-map-bind R st-[] = st-[]
spine-typed-map-bind R (st-type typed) =
  st-type (spine-typed-map-bind R typed)
spine-typed-map-bind R (st-name typed) =
  st-name (spine-typed-map-bind R typed)
spine-typed-map-bind R (st-cast cls typed) =
  st-cast (cast-frame-class-map (bind R) cls)
    (spine-typed-map-bind R typed)
spine-typed-map-bind R (st-reveal c⊢ typed) =
  st-reveal (reveal-renameᵗ StoreRename-suc-bind c⊢)
    (spine-typed-map-bind R typed)
spine-typed-map-bind R (st-conceal c⊢ typed) =
  st-conceal (conceal-renameᵗ StoreRename-suc-bind c⊢)
    (spine-typed-map-bind R typed)


spine-typed-map-bindʷ : ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {A B : Ty Δᴿ} {spine : InstantiationSpine A B}
    (R : Ty Δᴿ)
  → CTI2.targetStoreʷ W₁ ≡
      applyStores (bind R ∷ []) (CTI2.targetStoreʷ W)
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} W₁
      (mapInstantiationSpine (bind R) spine)
spine-typed-map-bindʷ R follows typed =
  spine-typed-store-eq follows (spine-typed-map-bind R typed)


spine-typed-rebase-left : ∀ {fuel Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {A B : Ty Δᴿ} {spine : InstantiationSpine A B} {Xᴸ?}
  → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} Wᵖ spine
spine-typed-rebase-left rb =
  spine-typed-store-eq (CTI2T.rebaseᴸ-target-store rb)


spine-typed-tag-rebase-left : ∀ {fuel Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {A B : Ty Δᴿ} {spine : InstantiationSpine A B} {Xᴸ? Xᴿ?}
  → CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} Wᵖ spine
spine-typed-tag-rebase-left rb =
  spine-typed-store-eq
    (sym (CTI2T.rebaseᴸ-target-store (CTI2.forgetTagRebaseᴸ rb)))


spine-typed-lift-left : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A B : Ty Δᴿ} {spine : InstantiationSpine A B}
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} (CTI2.liftWorldLeft X⊑★ W) spine
spine-typed-lift-left typed = typed


spine-typed-all-child : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {μ : Env∼ Δᴿ}
    {d : extᵐ μ ⊢ B ∼ C}
    {spine : InstantiationSpine (C [ ＇ X ]ᵗ) E}
  → GFG.StructuralAllGeneratedFrameGeometry W Aₛ C X
  → CastFrameClass {fuel = fuel} (d [ ＇ X ]ᶜ)
  → SpineTypedʷ {fuel = fuel} W (mapInstantiationSpine keep spine)
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine)
spine-typed-all-child geom cls typed =
  st-name (st-cast cls typed)


spine-typed-Λ-child : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {B : Ty (suc Δᴿ)} {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} (CTI2.rightOnlyWorld W (＇ X))
      (reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
spine-typed-Λ-child {W = W} {B = B} {X = X} typed =
  st-reveal (structural-reveal-typing B (Z∋ refl))
    (st-type
      (spine-typed-map-bindʷ
        {W = W} {W₁ = CTI2.rightOnlyWorld W (＇ X)}
        (＇ X) refl typed))


spine-typed-reveal-child : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ (suc Δᴿ) Δ}
    {γ : CTI2.CtxImp W}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {c : Conv↑ (suc Δᴿ) C B}
    {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
  → GFG.StructuralRevealGeneratedFrameGeometry W γ Aₛ B C X c
  → SpineTypedʷ {fuel = fuel} W
      (mapInstantiationSpine (bind (＇ X)) spine)
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame (applyBody (bind (＇ X)) C)
          Fin.zero refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        reveal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
spine-typed-reveal-child geom typed =
  st-name (st-type
    (st-reveal (CTI2T.erase-⊢↑ (RG.targetConversion₁ geom))
      (st-reveal (CTI2T.erase-⊢↑ (RG.targetConversion₂ geom))
        (st-type typed))))
  where
  module RG = GFG.StructuralRevealGeneratedFrameGeometry


spine-typed-conceal-child : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ (suc Δᴿ) Δ}
    {γ : CTI2.CtxImp W}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {c : Conv↓ (suc Δᴿ) C B}
    {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
  → GFG.StructuralConcealGeneratedFrameGeometry W γ Aₛ B C X c
  → SpineTypedʷ {fuel = fuel} W
      (mapInstantiationSpine (bind (＇ X)) spine)
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame (applyBody (bind (＇ X)) C)
          Fin.zero refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        conceal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
spine-typed-conceal-child geom typed =
  st-name (st-type
    (st-conceal (CTI2T.erase-⊢↓ (CG.targetConversion₁ geom))
      (st-reveal (CTI2T.erase-⊢↑ (CG.targetConversion₂ geom))
        (st-type typed))))
  where
  module CG = GFG.StructuralConcealGeneratedFrameGeometry


spine-typed-inst-child : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴿ)} {B E : Ty Δᴿ}
    {μ : Env∼ Δᴿ} {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    {spine : InstantiationSpine B E}
  → suc (castSize (↑ᶜ (close-instᶜ c))) < fuel
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} (CTI2.rightOnlyWorld W ★)
      (name-type-app-frame (applyBody (bind ★) A) Fin.zero
          refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero A) ▻ⁱ
        reveal-frame (〖 Fin.zero , ★ ↑ A 〗) ▻ⁱ
        type-transport-frame
          (trans (replace-zero-open A ★)
            (sym (renameᵗ-wk-eq (A [ ★ ]ᵗ)))) ▻ⁱ
        cast-frame (↑ᶜ (close-instᶜ c)) ▻ⁱ
        type-transport-frame (renameᵗ-wk-eq B) ▻ⁱ
        mapInstantiationSpine (bind ★) spine)
spine-typed-inst-child {W = W} {A = A} {B = B} residual<fuel typed =
  st-name (st-type
    (st-reveal (structural-reveal-typing A (Z∋ refl))
      (st-type
        (st-cast (cast-residual residual<fuel)
          (st-type
            (spine-typed-map-bindʷ
              {W = W} {W₁ = CTI2.rightOnlyWorld W ★}
              ★ refl typed))))))


root-value-instantiation-spine-typed : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ (suc Δᴿ) Δ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {R : Ty Δᴿ}
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame (applyBody (bind R) B)
        Fin.zero refl refl ▻ⁱ []ⁱ)
root-value-instantiation-spine-typed = st-name st-[]
