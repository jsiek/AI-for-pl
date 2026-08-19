module proof.DGG.Catchup.StructuralSpineTypingDef where

-- File Charter:
--   * Defines target-store typing evidence for pending instantiation spines.
--   * Supplies store-change transports for `mapInstantiationSpine`.
--   * Builds the typed generated/root spines consumed by NS-4 workers.

import Data.Fin as Fin
open import Data.Nat using (ℕ; suc; _<_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyCtx; TyVar; NonVar; nonvar-base; nonvar-star;
   nonvar-fun; nonvar-all; NonStar; nonstar-X; nonstar-ι;
   nonstar-⇒; nonstar-∀; ★; ＇_; ‵_; `∀; ⇑ᵗ; _[_]ᵗ;
   _∈ᵗ_; var-∈; singleSubᵗ; substNonVar)
open import TyStore using (TyStore; store-bind; Z∋)
open import Imprecision using (X⊑★)
open import Consistency using
  (Env∼; X∼X; extᵐ; instᵐ; id; _↦_; ∀ᶜ_; _!; ？_;
   inst_; gen_; bot-elim; bot-intro; _⊢_∼_; ↑ᶜ_; close-instᶜ;
   _[_]ᶜ; subst-∈ᵗ; renameNonStar; toRenameᵗ; wk↪ᵗ)
import CastTerms as CT
open import CastTerms using
  (Inert; GenSafe; safe-⇒; safe-∀; safe-inst; safe-gen; _⟨_⟩)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑_; _⊢↓_; replaceTy; rename↑; rename↓; 〖_,_↑_〗)
open import Reduction using
  (StoreChange; keep; bind; applyStores; applyTy; applyBody;
   applyTys; applyConsistency; applyConsistencies; StoreChanges;
   _∷_; [])
open import proof.Reduction using (applyStoreChange-Inert)
open import proof.TypeInTermSubst using
  (StoreRename-suc-bind; reveal-renameᵗ; conceal-renameᵗ;
   reveal-rename-id; conceal-rename-id; renameᵗ-id; renameᵗ-wk-eq)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open; structural-reveal-typing)
import proof.Consistency as PC
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision2Typing as CTI2T
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (castSize)
open import proof.ImprecisionConsistency using (nonstar-from-≢★)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
import proof.DGG.Catchup.StructuralGeneratedFrameGeometryDef as GFG


ResidualFrameProvenance : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
  → μ ⊢ A ∼ B
  → Set
ResidualFrameProvenance {Δ = Δ} {A = A} {B = B} c =
  ∀ {Δᴸ Δ′ Δᵂ} {χs : StoreChanges Δ Δ′}
    {W : CTX.World Δᴸ Δ′ Δᵂ}
    {Aₛ : Ty Δᴸ}
    {p : Aₛ CTX.⊑ᵂ⟨ W ⟩ applyTys χs A}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ applyTys χs B}
    {γ : CTX.CtxImp W}
    {M : CT.Term Δᴸ} {V : CT.Term Δ′}
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → W CTI2.∣ γ ⊢² M ⊑ (V ⟨ applyConsistencies χs c ⟩) ∶ q


residual-provenance-map-bind : ∀ {Δ : TyCtx} {μ : Env∼ Δ}
    {A B : Ty Δ}
    (R : Ty Δ) {c : μ ⊢ A ∼ B}
  → ResidualFrameProvenance c
  → ResidualFrameProvenance (applyConsistency (bind R) c)
residual-provenance-map-bind R prov {χs = χs} =
  prov {χs = bind R ∷ χs}


applyTys-nonstar : ∀ {Δ Δ′} {A : Ty Δ}
  → (χs : StoreChanges Δ Δ′)
  → NonStar A
  → NonStar (applyTys χs A)
applyTys-nonstar [] Ans = Ans
applyTys-nonstar (keep ∷ χs) Ans = applyTys-nonstar χs Ans
applyTys-nonstar (bind R ∷ χs) Ans =
  applyTys-nonstar χs (renameNonStar Fin.suc Ans)


residual-frame-cast-local : ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
    {Aₛ : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : Aₛ CTX.⊑ᵂ⟨ W ⟩ B}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ B′}
    {γ : CTX.CtxImp W}
    {M : CT.Term Δᴸ} {V : CT.Term Δᴿ}
  → NonStar B
  → NonStar B′
  → (c : ν ⊢ B ∼ B′)
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → W CTI2.∣ γ ⊢² M ⊑ (V ⟨ c ⟩) ∶ q
residual-frame-cast-local Bns B′ns c rel = CTI2.⊑cast² c rel _


inst-residual-source-nonstar-local : ∀ {Δ} {B : Ty (suc Δ)}
  → NonVar B
  → Fin.zero ∈ᵗ B
  → NonStar (B [ ★ ]ᵗ)
inst-residual-source-nonstar-local nonvar-base ()
inst-residual-source-nonstar-local nonvar-star ()
inst-residual-source-nonstar-local nonvar-fun zero∈B = nonstar-⇒
inst-residual-source-nonstar-local nonvar-all zero∈B = nonstar-∀


inst-frame-provenance : ∀ {Δ : TyCtx} {μ : Env∼ Δ}
    {A : Ty (suc Δ)} {B : Ty Δ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
  → (B≢★ : B ≢ ★)
  → ResidualFrameProvenance ((inst c) B≢★)
inst-frame-provenance {c = c} B≢★ {χs = χs} =
  residual-frame-cast-local
    (applyTys-nonstar χs nonstar-∀)
    (applyTys-nonstar χs (nonstar-from-≢★ B≢★))
    (applyConsistencies χs ((inst c) B≢★))


inst-residual-frame-provenance : ∀ {Δ : TyCtx} {μ : Env∼ Δ}
    {A : Ty (suc Δ)} {B : Ty Δ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
  → (B≢★ : B ≢ ★)
  → ResidualFrameProvenance (↑ᶜ (close-instᶜ c))
inst-residual-frame-provenance {A = A} {B = B} {c = c}
    ⦃ Anv ⦄ ⦃ z∈A ⦄ B≢★ {χs = χs} =
  residual-frame-cast-local
    (applyTys-nonstar χs
      (renameNonStar (toRenameᵗ wk↪ᵗ)
        (inst-residual-source-nonstar-local Anv z∈A)))
    (applyTys-nonstar χs
      (renameNonStar (toRenameᵗ wk↪ᵗ) (nonstar-from-≢★ B≢★)))
    (applyConsistencies χs (↑ᶜ (close-instᶜ c)))


data CastFrameClass {fuel : ℕ} {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
    (c : μ ⊢ A ∼ B) : Set where

  cast-inert : Inert c → CastFrameClass {fuel = fuel} c

  cast-safe :
      GenSafe c
    → castSize c < fuel
    → ResidualFrameProvenance c
    → CastFrameClass {fuel = fuel} c

  cast-residual :
      suc (castSize c) < fuel
    → ResidualFrameProvenance c
    → CastFrameClass {fuel = fuel} c


cast-frame-class-map : ∀ {fuel Δ Δ′ μ A B}
    (χ : StoreChange Δ Δ′) {c : μ ⊢ A ∼ B}
  → CastFrameClass {fuel = fuel} c
  → CastFrameClass {fuel = fuel} (applyConsistency χ c)
cast-frame-class-map {fuel = fuel} keep cls = cls
cast-frame-class-map {fuel = fuel} (bind R) (cast-inert inert) =
  cast-inert {fuel = fuel} (applyStoreChange-Inert (bind R) inert)
cast-frame-class-map {fuel = fuel} (bind R) {c = c}
    (cast-safe safe c<fuel prov) =
  cast-safe {fuel = fuel}
    (PC.renameGenSafe Fin.suc (λ X → refl) safe)
    (subst≡ (λ n → n < _)
      (sym (PC.castSize-renameEnvᶜ Fin.suc (λ X → refl) _))
      c<fuel)
    (λ {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ} {χs = χs}
       {W = W} {Aₛ = Aₛ} {p = p} {q = q} →
       prov {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ}
         {χs = bind R ∷ χs} {W = W} {Aₛ = Aₛ}
         {p = p} {q = q})
cast-frame-class-map {fuel = fuel} (bind R) {c = c}
    (cast-residual c<fuel prov) =
  cast-residual {fuel = fuel}
    (subst≡ (λ n → suc n < _)
      (sym (PC.castSize-renameEnvᶜ Fin.suc (λ X → refl) _))
      c<fuel)
    (λ {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ} {χs = χs}
       {W = W} {Aₛ = Aₛ} {p = p} {q = q} →
       prov {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ}
         {χs = bind R ∷ χs} {W = W} {Aₛ = Aₛ}
         {p = p} {q = q})


cast-frame-class-from-gen-safe-view : ∀ {fuel : ℕ} {Δ : TyCtx}
    {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (safe : GenSafe c)
  → PC.GenSafeView safe
  → castSize c < fuel
  → ResidualFrameProvenance c
  → CastFrameClass {fuel = fuel} c
cast-frame-class-from-gen-safe-view safe-⇒ (PC.gen-safe-inert inert)
    c<fuel prov =
  cast-inert inert
cast-frame-class-from-gen-safe-view safe-∀ (PC.gen-safe-inert inert)
    c<fuel prov =
  cast-inert inert
cast-frame-class-from-gen-safe-view (safe-inst B≢★)
    (PC.gen-safe-inert ()) c<fuel prov
cast-frame-class-from-gen-safe-view (safe-inst B≢★)
    (PC.gen-safe-inst _) c<fuel prov =
  cast-safe (safe-inst B≢★) c<fuel
    (λ {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ} {χs = χs}
       {W = W} {Aₛ = Aₛ} {p = p} {q = q} →
       prov {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ} {χs = χs}
         {W = W} {Aₛ = Aₛ} {p = p} {q = q})
cast-frame-class-from-gen-safe-view (safe-gen A≢★ safe)
    (PC.gen-safe-inert inert) c<fuel prov =
  cast-inert inert


opened-all-cast-frame-class : ∀ {fuel : ℕ} {Δ : TyCtx} {μ : Env∼ Δ}
    {B C : Ty (suc Δ)} {X : TyVar Δ}
    {d : extᵐ μ ⊢ B ∼ C}
  → μ X ≡ X∼X
  → NonVar C
  → Fin.zero ∈ᵗ C
  → castSize (d [ ＇ X ]ᶜ) < fuel
  → ResidualFrameProvenance (d [ ＇ X ]ᶜ)
  → CastFrameClass {fuel = fuel} (d [ ＇ X ]ᶜ)
opened-all-cast-frame-class {C = C} {X = X} {d = d} strict Cnv zero∈C
    opened<fuel opened-prov =
  cast-frame-class-from-gen-safe-view safe (PC.gen-safe-view safe)
    opened<fuel
    (λ {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ} {χs = χs}
       {W = W} {Aₛ = Aₛ} {p = p} {q = q} →
       opened-prov {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ}
         {χs = χs} {W = W} {Aₛ = Aₛ} {p = p} {q = q})
  where
  opened-nonvar : NonVar (C [ ＇ X ]ᵗ)
  opened-nonvar = substNonVar (singleSubᵗ (＇ X)) Cnv

  opened-occurs : X ∈ᵗ C [ ＇ X ]ᵗ
  opened-occurs = subst-∈ᵗ zero∈C var-∈

  safe : GenSafe (d [ ＇ X ]ᶜ)
  safe = PC.strict-safe strict (d [ ＇ X ]ᶜ)
    opened-nonvar opened-occurs


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
  → CTX.World Δᴸ Δᴿ Δ
  → InstantiationSpine A B
  → Set
SpineTypedʷ {fuel = fuel} W spine =
  SpineTyped {fuel = fuel} (CTX.targetStoreʷ W) spine


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
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W₁ : CTX.World Δᴸ (suc Δᴿ) Δ₁}
    {A B : Ty Δᴿ} {spine : InstantiationSpine A B}
    (R : Ty Δᴿ)
  → CTX.targetStoreʷ W₁ ≡
      applyStores (bind R ∷ []) (CTX.targetStoreʷ W)
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} W₁
      (mapInstantiationSpine (bind R) spine)
spine-typed-map-bindʷ R follows typed =
  spine-typed-store-eq follows (spine-typed-map-bind R typed)


spine-typed-rebase-left : ∀ {fuel Δᴸ Δᴿ Δ}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {A B : Ty Δᴿ} {spine : InstantiationSpine A B} {Xᴸ?}
  → CTX.RebaseAtᴸ W Wᵖ Xᴸ?
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} Wᵖ spine
spine-typed-rebase-left rb =
  spine-typed-store-eq (CTI2T.rebaseᴸ-target-store rb)


spine-typed-tag-rebase-left : ∀ {fuel Δᴸ Δᴿ Δ}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {A B : Ty Δᴿ} {spine : InstantiationSpine A B} {Xᴸ? Xᴿ?}
  → CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} Wᵖ spine
spine-typed-tag-rebase-left rb =
  spine-typed-store-eq
    (sym (CTI2T.rebaseᴸ-target-store (CTX.forgetTagRebaseᴸ rb)))


spine-typed-lift-left : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {A B : Ty Δᴿ} {spine : InstantiationSpine A B}
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} (CTX.liftWorldLeft X⊑★ W) spine
spine-typed-lift-left typed = typed


spine-typed-all-child : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {μ : Env∼ Δᴿ}
    {d : extᵐ μ ⊢ B ∼ C}
    {spine : InstantiationSpine (C [ ＇ X ]ᵗ) E}
  → GFG.StructuralAllGeneratedFrameGeometry W Aₛ C X
  → μ X ≡ X∼X
  → NonVar C
  → Fin.zero ∈ᵗ C
  → castSize (d [ ＇ X ]ᶜ) < fuel
  → ResidualFrameProvenance (d [ ＇ X ]ᶜ)
  → SpineTypedʷ {fuel = fuel} W (mapInstantiationSpine keep spine)
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine)
spine-typed-all-child {fuel = fuel} {Δᴿ = Δᴿ} {B = B} {C = C}
    {X = X} {μ = μ} {d = d} geom strict Cnv zero∈C
    opened<fuel opened-prov typed =
  st-name
    (st-cast
      (opened-all-cast-frame-class
        {fuel = fuel} {Δ = Δᴿ} {μ = μ} {B = B} {C = C}
        {X = X} {d = d} strict Cnv zero∈C opened<fuel
        (λ {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ} {χs = χs}
           {W = W′} {Aₛ = Aₛ} {p = p} {q = q} →
           opened-prov {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ}
             {χs = χs} {W = W′} {Aₛ = Aₛ} {p = p} {q = q}))
      typed)


spine-typed-Λ-child : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {B : Ty (suc Δᴿ)} {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} (CTX.rightOnlyWorld W (＇ X))
      (reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
spine-typed-Λ-child {W = W} {B = B} {X = X} typed =
  st-reveal (structural-reveal-typing B (Z∋ refl))
    (st-type
      (spine-typed-map-bindʷ
        {W = W} {W₁ = CTX.rightOnlyWorld W (＇ X)}
        (＇ X) refl typed))


spine-typed-reveal-child : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ (suc Δᴿ) Δ}
    {γ : CTX.CtxImp W}
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
    {W : CTX.World Δᴸ (suc Δᴿ) Δ}
    {γ : CTX.CtxImp W}
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
    {W : CTX.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴿ)} {B E : Ty Δᴿ}
    {μ : Env∼ Δᴿ} {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    {spine : InstantiationSpine B E}
  → suc (castSize (↑ᶜ (close-instᶜ c))) < fuel
  → ResidualFrameProvenance (↑ᶜ (close-instᶜ c))
  → SpineTypedʷ {fuel = fuel} W spine
  → SpineTypedʷ {fuel = fuel} (CTX.rightOnlyWorld W ★)
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
spine-typed-inst-child {W = W} {A = A} {B = B} {c = c}
    residual<fuel residual-prov typed =
  st-name (st-type
    (st-reveal (structural-reveal-typing A (Z∋ refl))
      (st-type
        (st-cast (cast-residual residual<fuel
          (λ {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ} {χs = χs}
             {W = W′} {Aₛ = Aₛ} {p = p} {q = q} →
             residual-prov {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ}
               {χs = χs} {W = W′} {Aₛ = Aₛ}
               {p = p} {q = q}))
          (st-type
            (spine-typed-map-bindʷ
              {W = W} {W₁ = CTX.rightOnlyWorld W ★}
              ★ refl typed))))))


root-value-instantiation-spine-typed : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ (suc Δᴿ) Δ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {R : Ty Δᴿ}
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame (applyBody (bind R) B)
        Fin.zero refl refl ▻ⁱ []ⁱ)
root-value-instantiation-spine-typed = st-name st-[]
