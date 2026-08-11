module proof.DGG.TargetExtend where

-- File Charter:
--   * Transports version-2 cast-term-imprecision derivations across
--     right-only target store extension.
--   * Provides the target-side weakening helpers for indexed conversions,
--     partner predicates, and derivation-level target extension.
--   * The public theorem specializes to the parked single right bind used by
--     the DGG instantiation cases; internal helpers keep target weakening
--     separate from source-side structure.

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
import Data.Fin as Fin
import Data.Fin.Properties as FinP
import Data.Nat as Nat
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore; store-lift)
open import Imprecision
open import Primitives using
  (Prim; addℕ; and𝔹; constTy; primArgTy; primResultTy;
   constTy-renameᵗ)
import TermCtx as T
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; toRenameᵗ; id↪ᵗ; wk↪ᵗ;
   renameᵐᶜ)
import Conversion
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; renameᵗᵐ)
import Reduction
open import Reduction using (bind; _∷_; [])
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.TypeInTermSubst using
  (StoreRename; StoreRename-ext; StoreRename-keep; StoreRename-wk-bind;
   renameᵗᵐ-preserves-Value; renameᵗ-wk-eq; toRename-id-eq;
   toRename-keep-eq; toRename-wk-eq; typing-renameᵗ; rename-openᵗ)
open import proof.ImprecisionConsistency using
  (fin-suc-injective; rename-⊑; toRenameᵗ-injective)
open import proof.DGG.Parked.ParkedWorldProof using (right-bind-⊑ᵂ)
open import proof.DGG.CenterRename using
  (_∘↪_; toRenameᵗ-∘; sucMaybe; preimage?; sucMaybe-nothing;
   renameEnv; renameEnv-image; renameEnv-off)
import proof.Imprecision as PI

open CTI2 using
  ( World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_
  ; PivotJoin; _⊢↑[_]_; _⊢↓[_]_
  )

------------------------------------------------------------------------
-- Optional target pivots and indexed conversion typing
------------------------------------------------------------------------

mapPivot : ∀ {Δ Δ′}
  → (TyVar Δ → TyVar Δ′)
  → Maybe (TyVar Δ)
  → Maybe (TyVar Δ′)
mapPivot ρ (just X) = just (ρ X)
mapPivot ρ nothing = nothing

record TargetInsert {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    (ρ : Δᴿ ↪ᵗ Δᴿ′)
    (π : Δ ↪ᵗ Δ′)
    (W : World Δᴸ Δᴿ Δ)
    (W′ : World Δᴸ Δᴿ′ Δ′) : Set₁ where
  field
    sourceStore-kept : CTI2.sourceStoreʷ W′ ≡ CTI2.sourceStoreʷ W

    transport⊑ᵂ : ∀ {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B
      → A ⊑ᵂ⟨ W′ ⟩ renameᵗ (toRenameᵗ ρ) B

    targetStore-rename :
      StoreRename (toRenameᵗ ρ) (CTI2.targetStoreʷ W)
        (CTI2.targetStoreʷ W′)

    source-resolve : ∀ Xᴸ
      → CTI2.resolveVar (CTI2.sourceStoreʷ W′) Xᴸ
          ≡ CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ

    target-resolve : ∀ Xᴿ
      → CTI2.resolveVar (CTI2.targetStoreʷ W′) (toRenameᵗ ρ Xᴿ)
          ≡ renameᵗ (toRenameᵗ ρ)
              (CTI2.resolveVar (CTI2.targetStoreʷ W) Xᴿ)

    align-insert : ∀ {Xᴸ Xᴿ}
      → CTI2.CenterAligned W Xᴸ Xᴿ
      → CTI2.CenterAligned W′ Xᴸ (toRenameᵗ ρ Xᴿ)

    source-insert : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ W′) Xᴸ
          ≡ toRenameᵗ π (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)

    target-insert : ∀ Xᴿ
      → toRenameᵗ (CTI2.ηᴿʷ W′) (toRenameᵗ ρ Xᴿ)
          ≡ toRenameᵗ π (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)

    impEnv-insert : ∀ Z
      → CTI2.impEnvʷ W′ (toRenameᵗ π Z) ≡ CTI2.impEnvʷ W Z

    impEnv-off-insert : ∀ {Z′}
      → preimage? π Z′ ≡ nothing
      → CTI2.impEnvʷ W′ Z′ ≡ X⊑★

    target-center-reflect : ∀ {Y′ Z}
      → toRenameᵗ (CTI2.ηᴿʷ W′) Y′ ≡ toRenameᵗ π Z
      → Σ[ Y ∈ TyVar Δᴿ ]
          Y′ ≡ toRenameᵗ ρ Y ×
          toRenameᵗ (CTI2.ηᴿʷ W) Y ≡ Z

    target-source-reflect : ∀ {Xᴸ Y′}
      → CTI2.CenterAligned W′ Xᴸ Y′
      → Σ[ Y ∈ TyVar Δᴿ ]
          Y′ ≡ toRenameᵗ ρ Y × CTI2.CenterAligned W Xᴸ Y

open TargetInsert public

target-source-reflect-from-center : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ Y′}
  → (ins : TargetInsert ρ π W W′)
  → CTI2.CenterAligned W′ Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y × CTI2.CenterAligned W Xᴸ Y
target-source-reflect-from-center {π = π} {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y′ = Y′} ins aligned
    with target-center-reflect ins target-image
  where
  target-image : toRenameᵗ (CTI2.ηᴿʷ W′) Y′
      ≡ toRenameᵗ π (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
  target-image = trans (sym aligned) (source-insert ins Xᴸ)
target-source-reflect-from-center ins aligned
    | Y , y′-eq , target-eq =
  Y , y′-eq , sym target-eq

mapCtxᵀ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → TargetInsert ρ π W W′
  → CtxImp W
  → CtxImp W′
mapCtxᵀ ins [] = []
mapCtxᵀ {ρ = ρ} ins (CTI2.ctx-imp A B p ∷ γ) =
  CTI2.ctx-imp A (renameᵗ (toRenameᵗ ρ) B) (transport⊑ᵂ ins p) ∷
    mapCtxᵀ ins γ

mapCtxᵀ-∋ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {x A B}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ins : TargetInsert ρ π W W′)
  → γ CTI2.∋ʷ x ⦂ CTI2.ctx-imp A B p
  → mapCtxᵀ ins γ CTI2.∋ʷ x ⦂
      CTI2.ctx-imp A (renameᵗ (toRenameᵗ ρ) B) (transport⊑ᵂ ins p)
mapCtxᵀ-∋ ins CTI2.Zʷ = CTI2.Zʷ
mapCtxᵀ-∋ ins (CTI2.Sʷ x∈) = CTI2.Sʷ (mapCtxᵀ-∋ ins x∈)

mapCtxᵀ-same : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
  → (ins : TargetInsert ρ π W W⁺)
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTI2.SameCtx γ γᵖ
  → CTI2.SameCtx (mapCtxᵀ ins γ) (mapCtxᵀ insᵖ γᵖ)
mapCtxᵀ-same ins insᵖ CTI2.same-[] = CTI2.same-[]
mapCtxᵀ-same ins insᵖ (CTI2.same-∷ sc) =
  CTI2.same-∷ (mapCtxᵀ-same ins insᵖ sc)

mapCtxᵀ-tgt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W′)
  → (γ : CtxImp W)
  → CTI2.tgtCtxʷ (mapCtxᵀ ins γ)
      ≡ T.renameCtx (toRenameᵗ ρ) (CTI2.tgtCtxʷ γ)
mapCtxᵀ-tgt ins [] = refl
mapCtxᵀ-tgt ins (CTI2.ctx-imp A B p ∷ γ) =
  cong (renameᵗ _ B ∷_) (mapCtxᵀ-tgt ins γ)

source-embed-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W′)
  → (A : Ty Δᴸ)
  → CTI2.embedᴸ W′ A
      ≡ renameᵗ (toRenameᵗ π) (CTI2.embedᴸ W A)
source-embed-insert {π = π} {W = W} ins A =
  trans (renameᵗ-cong A (source-insert ins))
    (sym (renameᵗ-comp (toRenameᵗ (CTI2.ηᴸʷ W)) (toRenameᵗ π) A))

target-embed-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W′)
  → (B : Ty Δᴿ)
  → CTI2.embedᴿ W′ (renameᵗ (toRenameᵗ ρ) B)
      ≡ renameᵗ (toRenameᵗ π) (CTI2.embedᴿ W B)
target-embed-insert {ρ = ρ} {π = π} {W = W} {W′ = W′} ins B =
  trans (renameᵗ-comp (toRenameᵗ ρ) (toRenameᵗ (CTI2.ηᴿʷ W′)) B)
    (trans (renameᵗ-cong B (target-insert ins))
      (sym (renameᵗ-comp (toRenameᵗ (CTI2.ηᴿʷ W))
        (toRenameᵗ π) B)))

transport⊑ᵂ-from-geometry : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (∀ C → CTI2.embedᴸ W′ C
      ≡ renameᵗ (toRenameᵗ π) (CTI2.embedᴸ W C))
  → (∀ C → CTI2.embedᴿ W′ (renameᵗ (toRenameᵗ ρ) C)
      ≡ renameᵗ (toRenameᵗ π) (CTI2.embedᴿ W C))
  → (∀ Z → CTI2.impEnvʷ W Z ≡ X⊑★
      → CTI2.impEnvʷ W′ (toRenameᵗ π Z) ≡ X⊑★)
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ W′ ⟩ renameᵗ (toRenameᵗ ρ) B
transport⊑ᵂ-from-geometry {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {A = A} {B = B} source-eq target-eq env-star p =
  subst≡
    (λ L → CTI2.impEnvʷ W′ ⊢
      L ⊑ CTI2.embedᴿ W′ (renameᵗ (toRenameᵗ ρ) B))
    (sym (source-eq A))
    (subst≡
      (λ R → CTI2.impEnvʷ W′ ⊢
        renameᵗ (toRenameᵗ π) (CTI2.embedᴸ W A) ⊑ R)
      (sym (target-eq B))
      (rename-⊑ (toRenameᵗ π) (toRenameᵗ-injective π)
        env-star p))

transport⊑ᵂ-geometry : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ W′ ⟩ renameᵗ (toRenameᵗ ρ) B
transport⊑ᵂ-geometry {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {A = A} {B = B} ins p =
  transport⊑ᵂ-from-geometry {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {A = A} {B = B} (source-embed-insert ins)
    (target-embed-insert ins)
    (λ Z eq → trans (impEnv-insert ins Z) eq)
    p

storeRep-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → CTI2.StoreRepImp W Xᴸ Xᴿ
  → CTI2.StoreRepImp W′ Xᴸ (toRenameᵗ ρ Xᴿ)
storeRep-insert {ρ = ρ} {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} ins
    (CTI2.store-rep-imp represented) =
  CTI2.store-rep-imp
    (subst≡
      (λ A → A ⊑ᵂ⟨ W′ ⟩
        CTI2.resolveVar (CTI2.targetStoreʷ W′) (toRenameᵗ ρ Xᴿ))
      (sym (source-resolve ins Xᴸ))
      (subst≡
        (λ B → CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ
          ⊑ᵂ⟨ W′ ⟩ B)
        (sym (target-resolve ins Xᴿ))
        (transport⊑ᵂ ins represented)))

renameᵗ-keep-shift : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ρ) A)
renameᵗ-keep-shift ρ A =
  trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
    (renameᵗ-shift (toRenameᵗ ρ) A)

ctx-imp-target-eq : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → B ≡ B′
  → CTI2.ctx-imp {W = W} A B p ≡ CTI2.ctx-imp {W = W} A B′ q
ctx-imp-target-eq {W = W} {A = A} {B = B} {p = p} {q = q} refl =
  cong (λ r → CTI2.ctx-imp {W = W} A B r) (PI.⊑-unique p q)

just≢nothing : ∀ {A : Set} {x : A} → just x ≢ nothing
just≢nothing ()

zero≢suc : ∀ {Δ} {X : TyVar Δ}
  → Fin.zero ≢ Fin.suc X
zero≢suc ()

suc≢zero : ∀ {Δ} {X : TyVar Δ}
  → Fin.suc X ≢ Fin.zero
suc≢zero ()

sucMaybe-just-suc : ∀ {Δ} {m : Maybe (TyVar Δ)} {Z}
  → sucMaybe m ≡ just (Fin.suc Z)
  → m ≡ just Z
sucMaybe-just-suc {m = just Z} refl = refl
sucMaybe-just-suc {m = nothing} ()

preimage?-sound : ∀ {Δ Δ′} (π : Δ ↪ᵗ Δ′) {Z′ Z}
  → preimage? π Z′ ≡ just Z
  → Z′ ≡ toRenameᵗ π Z
preimage?-sound empty ()
preimage?-sound (keep π) {Z′ = Fin.zero} {Z = Fin.zero} refl =
  refl
preimage?-sound (keep π) {Z′ = Fin.zero} {Z = Fin.suc Z} ()
preimage?-sound (keep π) {Z′ = Fin.suc Z′} {Z = Fin.zero} eq
    with preimage? π Z′
preimage?-sound (keep π) {Z′ = Fin.suc Z′} {Z = Fin.zero} ()
    | just Y
preimage?-sound (keep π) {Z′ = Fin.suc Z′} {Z = Fin.zero} ()
    | nothing
preimage?-sound (keep π) {Z′ = Fin.suc Z′} {Z = Fin.suc Z} eq =
  cong Fin.suc (preimage?-sound π (sucMaybe-just-suc eq))
preimage?-sound (skip π) {Z′ = Fin.zero} ()
preimage?-sound (skip π) {Z′ = Fin.suc Z′} eq =
  cong Fin.suc (preimage?-sound π eq)

preimage-id↪ : ∀ {Δ} (Z : TyVar Δ)
  → preimage? id↪ᵗ Z ≡ just Z
preimage-id↪ {Nat.zero} ()
preimage-id↪ {Nat.suc Δ} Fin.zero = refl
preimage-id↪ {Nat.suc Δ} (Fin.suc Z)
    rewrite preimage-id↪ Z =
  refl

liftBoth-source-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldBoth v W′)) X
      ≡ toRenameᵗ (keep π)
          (toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldBoth v W)) X)
liftBoth-source-insert ins Fin.zero = refl
liftBoth-source-insert ins (Fin.suc X) =
  cong Fin.suc (source-insert ins X)

liftBoth-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldBoth v W′))
      (toRenameᵗ (keep ρ) X)
      ≡ toRenameᵗ (keep π)
          (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldBoth v W)) X)
liftBoth-target-insert ins Fin.zero = refl
liftBoth-target-insert ins (Fin.suc X) =
  cong Fin.suc (target-insert ins X)

liftBoth-target-center-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Y′ : TyVar (Nat.suc Δᴿ′)}
    {Z : TyVar (Nat.suc Δ)}
  → (ins : TargetInsert ρ π W W′)
  → toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldBoth v W′)) Y′
      ≡ toRenameᵗ (keep π) Z
  → Σ[ Y ∈ TyVar (Nat.suc Δᴿ) ]
      Y′ ≡ toRenameᵗ (keep ρ) Y ×
      toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldBoth v W)) Y ≡ Z
liftBoth-target-center-reflect {Y′ = Fin.zero} {Z = Fin.zero}
    ins eq =
  Fin.zero , refl , refl
liftBoth-target-center-reflect {Y′ = Fin.zero} {Z = Fin.suc Z}
    ins eq =
  ⊥-elim (zero≢suc eq)
liftBoth-target-center-reflect {Y′ = Fin.suc Y′} {Z = Fin.zero}
    ins eq =
  ⊥-elim (suc≢zero eq)
liftBoth-target-center-reflect {Y′ = Fin.suc Y′} {Z = Fin.suc Z}
    ins eq with target-center-reflect ins (fin-suc-injective eq)
liftBoth-target-center-reflect {Y′ = Fin.suc Y′} {Z = Fin.suc Z}
    ins eq | Y , y′-eq , target-eq =
  Fin.suc Y , cong Fin.suc y′-eq , cong Fin.suc target-eq

liftBoth-impEnv-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ Z
  → CTI2.impEnvʷ (CTI2.liftWorldBoth v W′) (toRenameᵗ (keep π) Z)
      ≡ CTI2.impEnvʷ (CTI2.liftWorldBoth v W) Z
liftBoth-impEnv-insert ins Fin.zero = refl
liftBoth-impEnv-insert ins (Fin.suc Z) =
  impEnv-insert ins Z

liftBoth-impEnv-off-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Z′ : TyVar (Nat.suc Δ′)}
  → (ins : TargetInsert ρ π W W′)
  → preimage? (keep π) Z′ ≡ nothing
  → CTI2.impEnvʷ (CTI2.liftWorldBoth v W′) Z′ ≡ X⊑★
liftBoth-impEnv-off-insert {Z′ = Fin.zero} ins ()
liftBoth-impEnv-off-insert {π = π} {Z′ = Fin.suc Z′} ins eq =
  impEnv-off-insert ins (sucMaybe-nothing (preimage? π Z′) eq)

liftBoth-source-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → CTI2.resolveVar (CTI2.sourceStoreʷ (CTI2.liftWorldBoth v W′)) X
      ≡ CTI2.resolveVar (CTI2.sourceStoreʷ (CTI2.liftWorldBoth v W)) X
liftBoth-source-resolve ins Fin.zero = refl
liftBoth-source-resolve ins (Fin.suc X) =
  cong ⇑ᵗ (source-resolve ins X)

liftBoth-target-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → CTI2.resolveVar (CTI2.targetStoreʷ (CTI2.liftWorldBoth v W′))
      (toRenameᵗ (keep ρ) X)
      ≡ renameᵗ (toRenameᵗ (keep ρ))
          (CTI2.resolveVar
            (CTI2.targetStoreʷ (CTI2.liftWorldBoth v W)) X)
liftBoth-target-resolve ins Fin.zero = refl
liftBoth-target-resolve {ρ = ρ} {W = W} ins (Fin.suc X) =
  trans (cong ⇑ᵗ (target-resolve ins X))
    (sym (renameᵗ-keep-shift ρ
      (CTI2.resolveVar (CTI2.targetStoreʷ W) X)))

liftBoth-align-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Xᴸ : TyVar (Nat.suc Δᴸ)}
    {Xᴿ : TyVar (Nat.suc Δᴿ)}
  → (ins : TargetInsert ρ π W W′)
  → CTI2.CenterAligned (CTI2.liftWorldBoth v W) Xᴸ Xᴿ
  → CTI2.CenterAligned (CTI2.liftWorldBoth v W′) Xᴸ
      (toRenameᵗ (keep ρ) Xᴿ)
liftBoth-align-insert {Xᴸ = Fin.zero} {Xᴿ = Fin.zero} ins aligned =
  refl
liftBoth-align-insert {Xᴸ = Fin.zero} {Xᴿ = Fin.suc Xᴿ} ins ()
liftBoth-align-insert {Xᴸ = Fin.suc Xᴸ} {Xᴿ = Fin.zero} ins ()
liftBoth-align-insert {Xᴸ = Fin.suc Xᴸ} {Xᴿ = Fin.suc Xᴿ} ins aligned =
  cong Fin.suc (align-insert ins (fin-suc-injective aligned))

liftBoth-target-source-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Xᴸ : TyVar (Nat.suc Δᴸ)}
    {Y′ : TyVar (Nat.suc Δᴿ′)}
  → (ins : TargetInsert ρ π W W′)
  → CTI2.CenterAligned (CTI2.liftWorldBoth v W′) Xᴸ Y′
  → Σ[ Y ∈ TyVar (Nat.suc Δᴿ) ]
      Y′ ≡ toRenameᵗ (keep ρ) Y ×
      CTI2.CenterAligned (CTI2.liftWorldBoth v W) Xᴸ Y
liftBoth-target-source-reflect {Xᴸ = Fin.zero} {Y′ = Fin.zero}
    ins aligned =
  Fin.zero , refl , refl
liftBoth-target-source-reflect {Xᴸ = Fin.zero} {Y′ = Fin.suc Y′}
    ins ()
liftBoth-target-source-reflect {Xᴸ = Fin.suc Xᴸ} {Y′ = Fin.zero}
    ins ()
liftBoth-target-source-reflect {Xᴸ = Fin.suc Xᴸ} {Y′ = Fin.suc Y′}
    ins
    aligned with target-source-reflect ins (fin-suc-injective aligned)
liftBoth-target-source-reflect {Xᴸ = Fin.suc Xᴸ} {Y′ = Fin.suc Y′}
    ins aligned | Y , y′-eq , aligned₀ =
  Fin.suc Y , cong Fin.suc y′-eq , cong Fin.suc aligned₀

liftBothTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → TargetInsert ρ π W W′
  → TargetInsert (keep ρ) (keep π)
      (CTI2.liftWorldBoth v W) (CTI2.liftWorldBoth v W′)
liftBothTargetInsert {ρ = ρ} {π = π} {W = W} {W′ = W′} {v = v} ins =
  record
    { sourceStore-kept = cong store-lift (sourceStore-kept ins)
    ; transport⊑ᵂ = λ {A = A} {B = B} p →
        transport⊑ᵂ-from-geometry {ρ = keep ρ} {π = keep π}
          {W = CTI2.liftWorldBoth v W}
          {W′ = CTI2.liftWorldBoth v W′}
          {A = A} {B = B}
          (λ C → trans
            (renameᵗ-cong C (liftBoth-source-insert {v = v} ins))
            (sym (renameᵗ-comp
              (toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldBoth v W)))
              (toRenameᵗ (keep π)) C)))
          (λ C → trans
            (renameᵗ-comp (toRenameᵗ (keep ρ))
              (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldBoth v W′))) C)
            (trans
              (renameᵗ-cong C (liftBoth-target-insert {v = v} ins))
              (sym (renameᵗ-comp
                (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldBoth v W)))
                (toRenameᵗ (keep π)) C))))
          (λ Z eq → trans (liftBoth-impEnv-insert {v = v} ins Z) eq)
          p
    ; targetStore-rename = StoreRename-keep (targetStore-rename ins)
    ; source-resolve = liftBoth-source-resolve {v = v} ins
    ; target-resolve = liftBoth-target-resolve {v = v} ins
    ; align-insert = liftBoth-align-insert {v = v} ins
    ; source-insert = liftBoth-source-insert {v = v} ins
    ; target-insert = liftBoth-target-insert {v = v} ins
    ; impEnv-insert = liftBoth-impEnv-insert {v = v} ins
    ; impEnv-off-insert =
        λ {Z′} eq →
          liftBoth-impEnv-off-insert {v = v} {Z′ = Z′} ins eq
    ; target-center-reflect =
        liftBoth-target-center-reflect {v = v} ins
    ; target-source-reflect = liftBoth-target-source-reflect {v = v} ins
    }

liftLeft-source-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldLeft v W′)) X
      ≡ toRenameᵗ (keep π)
          (toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldLeft v W)) X)
liftLeft-source-insert ins Fin.zero = refl
liftLeft-source-insert ins (Fin.suc X) =
  cong Fin.suc (source-insert ins X)

liftLeft-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft v W′))
      (toRenameᵗ ρ X)
      ≡ toRenameᵗ (keep π)
      (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft v W)) X)
liftLeft-target-insert ins X = cong Fin.suc (target-insert ins X)

liftLeft-target-center-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Y′ : TyVar Δᴿ′} {Z : TyVar (Nat.suc Δ)}
  → (ins : TargetInsert ρ π W W′)
  → toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft v W′)) Y′
      ≡ toRenameᵗ (keep π) Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft v W)) Y ≡ Z
liftLeft-target-center-reflect {Z = Fin.zero} ins eq =
  ⊥-elim (suc≢zero eq)
liftLeft-target-center-reflect {Z = Fin.suc Z} ins eq
    with target-center-reflect ins (fin-suc-injective eq)
liftLeft-target-center-reflect {Z = Fin.suc Z} ins eq
    | Y , y′-eq , target-eq =
  Y , y′-eq , cong Fin.suc target-eq

liftLeft-impEnv-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ Z
  → CTI2.impEnvʷ (CTI2.liftWorldLeft v W′) (toRenameᵗ (keep π) Z)
      ≡ CTI2.impEnvʷ (CTI2.liftWorldLeft v W) Z
liftLeft-impEnv-insert ins Fin.zero = refl
liftLeft-impEnv-insert ins (Fin.suc Z) =
  impEnv-insert ins Z

liftLeft-impEnv-off-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Z′ : TyVar (Nat.suc Δ′)}
  → (ins : TargetInsert ρ π W W′)
  → preimage? (keep π) Z′ ≡ nothing
  → CTI2.impEnvʷ (CTI2.liftWorldLeft v W′) Z′ ≡ X⊑★
liftLeft-impEnv-off-insert {Z′ = Fin.zero} ins ()
liftLeft-impEnv-off-insert {π = π} {Z′ = Fin.suc Z′} ins eq =
  impEnv-off-insert ins (sucMaybe-nothing (preimage? π Z′) eq)

liftLeft-source-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → CTI2.resolveVar (CTI2.sourceStoreʷ (CTI2.liftWorldLeft v W′)) X
      ≡ CTI2.resolveVar (CTI2.sourceStoreʷ (CTI2.liftWorldLeft v W)) X
liftLeft-source-resolve ins Fin.zero = refl
liftLeft-source-resolve ins (Fin.suc X) =
  cong ⇑ᵗ (source-resolve ins X)

liftLeft-align-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Xᴸ : TyVar (Nat.suc Δᴸ)}
    {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → CTI2.CenterAligned (CTI2.liftWorldLeft v W) Xᴸ Xᴿ
  → CTI2.CenterAligned (CTI2.liftWorldLeft v W′) Xᴸ
      (toRenameᵗ ρ Xᴿ)
liftLeft-align-insert {Xᴸ = Fin.zero} ins ()
liftLeft-align-insert {Xᴸ = Fin.suc Xᴸ} ins aligned =
  cong Fin.suc (align-insert ins (fin-suc-injective aligned))

liftLeft-target-source-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Xᴸ : TyVar (Nat.suc Δᴸ)}
    {Y′ : TyVar Δᴿ′}
  → (ins : TargetInsert ρ π W W′)
  → CTI2.CenterAligned (CTI2.liftWorldLeft v W′) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      CTI2.CenterAligned (CTI2.liftWorldLeft v W) Xᴸ Y
liftLeft-target-source-reflect {Xᴸ = Fin.zero} ins ()
liftLeft-target-source-reflect {Xᴸ = Fin.suc Xᴸ} ins aligned
    with target-source-reflect ins (fin-suc-injective aligned)
liftLeft-target-source-reflect {Xᴸ = Fin.suc Xᴸ} ins aligned
    | Y , y′-eq , aligned₀ =
  Y , y′-eq , cong Fin.suc aligned₀

liftLeftTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → TargetInsert ρ π W W′
  → TargetInsert ρ (keep π)
      (CTI2.liftWorldLeft v W) (CTI2.liftWorldLeft v W′)
liftLeftTargetInsert {ρ = ρ} {π = π} {W = W} {W′ = W′} {v = v} ins =
  record
    { sourceStore-kept = cong store-lift (sourceStore-kept ins)
    ; transport⊑ᵂ = λ {A = A} {B = B} p →
        transport⊑ᵂ-from-geometry {ρ = ρ} {π = keep π}
          {W = CTI2.liftWorldLeft v W}
          {W′ = CTI2.liftWorldLeft v W′}
          {A = A} {B = B}
          (λ C → trans
            (renameᵗ-cong C (liftLeft-source-insert {v = v} ins))
            (sym (renameᵗ-comp
              (toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldLeft v W)))
              (toRenameᵗ (keep π)) C)))
          (λ C → trans
            (renameᵗ-comp (toRenameᵗ ρ)
              (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft v W′))) C)
            (trans
              (renameᵗ-cong C (liftLeft-target-insert {v = v} ins))
              (sym (renameᵗ-comp
                (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft v W)))
                (toRenameᵗ (keep π)) C))))
          (λ Z eq → trans (liftLeft-impEnv-insert {v = v} ins Z) eq)
          p
    ; targetStore-rename = targetStore-rename ins
    ; source-resolve = liftLeft-source-resolve {v = v} ins
    ; target-resolve = target-resolve ins
    ; align-insert = liftLeft-align-insert {v = v} ins
    ; source-insert = liftLeft-source-insert {v = v} ins
    ; target-insert = liftLeft-target-insert {v = v} ins
    ; impEnv-insert = liftLeft-impEnv-insert {v = v} ins
    ; impEnv-off-insert =
        λ {Z′} eq →
          liftLeft-impEnv-off-insert {v = v} {Z′ = Z′} ins eq
    ; target-center-reflect =
        liftLeft-target-center-reflect {v = v} ins
    ; target-source-reflect = liftLeft-target-source-reflect {v = v} ins
    }

targetLiftCtxBoth : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {γ : CtxImp W}
    {γ′ : CtxImp (CTI2.liftWorldBoth v W)}
  → (ins : TargetInsert ρ π W W′)
  → CTI2.LiftCtx v γ γ′
  → CTI2.LiftCtx v (mapCtxᵀ ins γ)
      (mapCtxᵀ (liftBothTargetInsert {v = v} ins) γ′)
targetLiftCtxBoth ins CTI2.lift-[] = CTI2.lift-[]
targetLiftCtxBoth {ρ = ρ} {W′ = W′} {v = v} ins
    (CTI2.lift-∷ {γ = γ} {γ′ = γ′} {A = A} {B = B}
      {p = p} {p′ = p′} liftγ) =
  subst≡
    (λ e → CTI2.LiftCtx v
      (mapCtxᵀ ins (CTI2.ctx-imp A B p ∷ γ))
      (e ∷ mapCtxᵀ (liftBothTargetInsert {v = v} ins) γ′))
    entry-eq
    (CTI2.lift-∷ (targetLiftCtxBoth ins liftγ))
  where
  insBoth = liftBothTargetInsert {v = v} ins

  shift-eq :
      renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ B)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ρ) B)
  shift-eq = renameᵗ-keep-shift ρ B

  p-trans :
      ⇑ᵗ A ⊑ᵂ⟨ CTI2.liftWorldBoth v W′ ⟩
        renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ B)
  p-trans = transport⊑ᵂ insBoth p′

  p-shift :
      ⇑ᵗ A ⊑ᵂ⟨ CTI2.liftWorldBoth v W′ ⟩
        ⇑ᵗ (renameᵗ (toRenameᵗ ρ) B)
  p-shift = subst≡
    (λ T → ⇑ᵗ A ⊑ᵂ⟨ CTI2.liftWorldBoth v W′ ⟩ T)
    shift-eq p-trans

  entry-eq =
    ctx-imp-target-eq {W = CTI2.liftWorldBoth v W′}
      {A = ⇑ᵗ A} {B = ⇑ᵗ (renameᵗ (toRenameᵗ ρ) B)}
      {B′ = renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ B)}
      {p = p-shift} {q = p-trans}
      (sym (renameᵗ-keep-shift ρ B))

targetLiftCtxLeft : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {γ : CtxImp W}
    {γ′ : CtxImp (CTI2.liftWorldLeft v W)}
  → (ins : TargetInsert ρ π W W′)
  → CTI2.LiftCtxᴸ v γ γ′
  → CTI2.LiftCtxᴸ v (mapCtxᵀ ins γ)
      (mapCtxᵀ (liftLeftTargetInsert {v = v} ins) γ′)
targetLiftCtxLeft ins CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
targetLiftCtxLeft ins (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (targetLiftCtxLeft ins liftγ)

insertRebaseWorld : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → TargetInsert ρ π W W⁺
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ′ Δ′
insertRebaseWorld {π = π} {W⁺ = W⁺} ins Wᵖ =
  CTI2.world (π ∘↪ CTI2.ηᴸʷ Wᵖ) (CTI2.ηᴿʷ W⁺)
    (renameEnv π (CTI2.impEnvʷ Wᵖ))
    (CTI2.sourceStoreʷ Wᵖ) (CTI2.targetStoreʷ W⁺)

insertRebase-source : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → ∀ Xᴸ
  → toRenameᵗ
      (CTI2.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Xᴸ
      ≡ toRenameᵗ π (toRenameᵗ (CTI2.ηᴸʷ Wᵖ) Xᴸ)
insertRebase-source {π = π} {Wᵖ = Wᵖ} ins Xᴸ =
  toRenameᵗ-∘ π (CTI2.ηᴸʷ Wᵖ) Xᴸ

insertRebase-target : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ
  → ∀ Y
  → toRenameᵗ
      (CTI2.ηᴿʷ (insertRebaseWorld ins Wᵖ)) (toRenameᵗ ρ Y)
      ≡ toRenameᵗ π (toRenameᵗ (CTI2.ηᴿʷ Wᵖ) Y)
insertRebase-target {π = π} ins rb Y =
  trans (target-insert ins Y)
    (cong (toRenameᵗ π) (sym (CTI2.RebaseAt.ηᴿ-frozen rb Y)))

insertRebase-impEnv : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → ∀ Z
  → CTI2.impEnvʷ (insertRebaseWorld ins Wᵖ) (toRenameᵗ π Z)
      ≡ CTI2.impEnvʷ Wᵖ Z
insertRebase-impEnv {π = π} {Wᵖ = Wᵖ} ins Z =
  renameEnv-image π (CTI2.impEnvʷ Wᵖ) Z

insertRebase-target-center-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {Y′ Z}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → toRenameᵗ (CTI2.ηᴿʷ (insertRebaseWorld ins Wᵖ)) Y′
      ≡ toRenameᵗ π Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      toRenameᵗ (CTI2.ηᴿʷ Wᵖ) Y ≡ Z
insertRebase-target-center-reflect ins rb eq
    with target-center-reflect ins eq
insertRebase-target-center-reflect ins rb eq
    | Y , y′-eq , target-eq =
  Y , y′-eq , trans (CTI2.RebaseAt.ηᴿ-frozen rb Y) target-eq

insertRebase-target-source-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᵖ : TyVar Δᴸ} {Yᵖ : TyVar Δᴿ} {Xᴸ Y′}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt W Wᵖ Xᵖ Yᵖ)
  → CTI2.CenterAligned (insertRebaseWorld ins Wᵖ) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y × CTI2.CenterAligned Wᵖ Xᴸ Y
insertRebase-target-source-reflect {ρ = ρ} {π = π}
    {W = W} {Wᵖ = Wᵖ} {W⁺ = W⁺} {Xᵖ = Xᵖ} {Yᵖ = Yᵖ}
    {Xᴸ = Xᴸ} {Y′ = Y′} ins rb aligned
    with FinP._≟_ Xᴸ Xᵖ
insertRebase-target-source-reflect {ρ = ρ} {π = π}
    {Wᵖ = Wᵖ} {W⁺ = W⁺} {Xᵖ = Xᵖ} {Yᵖ = Yᵖ}
    {.Xᵖ} {Y′} ins rb aligned | yes refl =
  Yᵖ , y′-eq , CTI2.RebaseAt.pivotAligned rb
  where
  pivot-target : toRenameᵗ
      (CTI2.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Xᵖ
      ≡ toRenameᵗ (CTI2.ηᴿʷ W⁺) (toRenameᵗ ρ Yᵖ)
  pivot-target =
    trans (insertRebase-source {Wᵖ = Wᵖ} ins Xᵖ)
      (trans (cong (toRenameᵗ π) (CTI2.RebaseAt.pivotAligned rb))
        (trans (cong (toRenameᵗ π) (CTI2.RebaseAt.ηᴿ-frozen rb Yᵖ))
          (sym (target-insert ins Yᵖ))))

  y′-eq : Y′ ≡ toRenameᵗ ρ Yᵖ
  y′-eq =
    toRenameᵗ-injective (CTI2.ηᴿʷ W⁺)
      (trans (sym aligned) pivot-target)
insertRebase-target-source-reflect {ρ = ρ} {π = π}
    {W = W} {Wᵖ = Wᵖ} {W⁺ = W⁺} {Xᵖ = Xᵖ}
    {Xᴸ = Xᴸ} {Y′ = Y′} ins rb aligned | no Xᴸ≢Xᵖ
    with target-source-reflect ins aligned⁺
  where
  source-shift : toRenameᵗ
      (CTI2.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Xᴸ
      ≡ toRenameᵗ π (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
  source-shift =
    trans (insertRebase-source {Wᵖ = Wᵖ} ins Xᴸ)
      (cong (toRenameᵗ π) (CTI2.RebaseAt.ηᴸ-off-pivot rb Xᴸ≢Xᵖ))

  aligned⁺ : CTI2.CenterAligned W⁺ Xᴸ Y′
  aligned⁺ =
    trans (source-insert ins Xᴸ) (trans (sym source-shift) aligned)
insertRebase-target-source-reflect {Wᵖ = Wᵖ}
    {Xᴸ = Xᴸ} ins rb aligned | no Xᴸ≢Xᵖ
    | Y , y′-eq , aligned₀ =
  Y , y′-eq , alignedᵖ
  where
  alignedᵖ : CTI2.CenterAligned Wᵖ Xᴸ Y
  alignedᵖ =
    trans (CTI2.RebaseAt.ηᴸ-off-pivot rb Xᴸ≢Xᵖ)
      (trans aligned₀ (sym (CTI2.RebaseAt.ηᴿ-frozen rb Y)))

insertRebase-source-embed : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (A : Ty Δᴸ)
  → CTI2.embedᴸ (insertRebaseWorld ins Wᵖ) A
      ≡ renameᵗ (toRenameᵗ π) (CTI2.embedᴸ Wᵖ A)
insertRebase-source-embed {π = π} {Wᵖ = Wᵖ} ins A =
  trans (renameᵗ-cong A (insertRebase-source {Wᵖ = Wᵖ} ins))
    (sym (renameᵗ-comp (toRenameᵗ (CTI2.ηᴸʷ Wᵖ)) (toRenameᵗ π) A))

insertRebase-target-embed : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → (B : Ty Δᴿ)
  → CTI2.embedᴿ (insertRebaseWorld ins Wᵖ)
      (renameᵗ (toRenameᵗ ρ) B)
      ≡ renameᵗ (toRenameᵗ π) (CTI2.embedᴿ Wᵖ B)
insertRebase-target-embed {ρ = ρ} {π = π} {Wᵖ = Wᵖ} ins rb B =
  trans
    (renameᵗ-comp (toRenameᵗ ρ)
      (toRenameᵗ (CTI2.ηᴿʷ (insertRebaseWorld ins Wᵖ))) B)
    (trans (renameᵗ-cong B (insertRebase-target ins rb))
      (sym (renameᵗ-comp (toRenameᵗ (CTI2.ηᴿʷ Wᵖ))
        (toRenameᵗ π) B)))

insertRebase-targetStore-rename : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → StoreRename (toRenameᵗ ρ) (CTI2.targetStoreʷ Wᵖ)
      (CTI2.targetStoreʷ (insertRebaseWorld ins Wᵖ))
insertRebase-targetStore-rename {ρ = ρ} {W⁺ = W⁺} ins rb =
  subst≡
    (λ Σ → StoreRename (toRenameᵗ ρ) Σ (CTI2.targetStoreʷ W⁺))
    (sym (CTI2.SameRuntime.targetStore-same
      (CTI2.RebaseAt.sameRuntime rb)))
    (targetStore-rename ins)

insertRebase-target-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → ∀ Y
  → CTI2.resolveVar
      (CTI2.targetStoreʷ (insertRebaseWorld ins Wᵖ))
      (toRenameᵗ ρ Y)
      ≡ renameᵗ (toRenameᵗ ρ)
          (CTI2.resolveVar (CTI2.targetStoreʷ Wᵖ) Y)
insertRebase-target-resolve {ρ = ρ} {W = W} {Wᵖ = Wᵖ} ins rb Y =
  trans (target-resolve ins Y)
    (cong (renameᵗ (toRenameᵗ ρ)) (sym target-same))
  where
  target-same : CTI2.resolveVar (CTI2.targetStoreʷ Wᵖ) Y
      ≡ CTI2.resolveVar (CTI2.targetStoreʷ W) Y
  target-same =
    cong (λ Σ → CTI2.resolveVar Σ Y)
      (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb))

insertRebase-target-rev : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ
  → ∀ Y
  → toRenameᵗ
      (CTI2.ηᴿʷ (insertRebaseWorld ins Wᵖ)) (toRenameᵗ ρ Y)
      ≡ toRenameᵗ π (toRenameᵗ (CTI2.ηᴿʷ Wᵖ) Y)
insertRebase-target-rev {π = π} ins rb Y =
  trans (target-insert ins Y)
    (cong (toRenameᵗ π) (CTI2.RebaseAt.ηᴿ-frozen rb Y))

insertRebase-target-center-reflect-rev :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {W⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {Y′ Z}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → toRenameᵗ (CTI2.ηᴿʷ (insertRebaseWorld ins Wᵖ)) Y′
      ≡ toRenameᵗ π Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      toRenameᵗ (CTI2.ηᴿʷ Wᵖ) Y ≡ Z
insertRebase-target-center-reflect-rev ins rb eq
    with target-center-reflect ins eq
insertRebase-target-center-reflect-rev ins rb eq
    | Y , y′-eq , target-eq =
  Y , y′-eq , trans (sym (CTI2.RebaseAt.ηᴿ-frozen rb Y)) target-eq

insertRebase-target-source-reflect-rev :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {W⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᵖ : TyVar Δᴸ} {Yᵖ : TyVar Δᴿ} {Xᴸ Y′}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt Wᵖ W Xᵖ Yᵖ)
  → CTI2.CenterAligned (insertRebaseWorld ins Wᵖ) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y × CTI2.CenterAligned Wᵖ Xᴸ Y
insertRebase-target-source-reflect-rev {π = π} {Wᵖ = Wᵖ}
    {Xᴸ = Xᴸ} {Y′ = Y′} ins rb aligned
    with insertRebase-target-center-reflect-rev ins rb target-image
  where
  target-image : toRenameᵗ
      (CTI2.ηᴿʷ (insertRebaseWorld ins Wᵖ)) Y′
      ≡ toRenameᵗ π (toRenameᵗ (CTI2.ηᴸʷ Wᵖ) Xᴸ)
  target-image =
    trans (sym aligned) (insertRebase-source {Wᵖ = Wᵖ} ins Xᴸ)
insertRebase-target-source-reflect-rev ins rb aligned
    | Y , y′-eq , target-eq =
  Y , y′-eq , sym target-eq

insertRebase-target-embed-rev : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → (B : Ty Δᴿ)
  → CTI2.embedᴿ (insertRebaseWorld ins Wᵖ)
      (renameᵗ (toRenameᵗ ρ) B)
      ≡ renameᵗ (toRenameᵗ π) (CTI2.embedᴿ Wᵖ B)
insertRebase-target-embed-rev {ρ = ρ} {π = π} {Wᵖ = Wᵖ} ins rb B =
  trans
    (renameᵗ-comp (toRenameᵗ ρ)
      (toRenameᵗ (CTI2.ηᴿʷ (insertRebaseWorld ins Wᵖ))) B)
    (trans (renameᵗ-cong B (insertRebase-target-rev ins rb))
      (sym (renameᵗ-comp (toRenameᵗ (CTI2.ηᴿʷ Wᵖ))
        (toRenameᵗ π) B)))

insertRebase-targetStore-rename-rev :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {W⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → StoreRename (toRenameᵗ ρ) (CTI2.targetStoreʷ Wᵖ)
      (CTI2.targetStoreʷ (insertRebaseWorld ins Wᵖ))
insertRebase-targetStore-rename-rev {ρ = ρ} {W⁺ = W⁺} ins rb =
  subst≡
    (λ Σ → StoreRename (toRenameᵗ ρ) Σ (CTI2.targetStoreʷ W⁺))
    (CTI2.SameRuntime.targetStore-same
      (CTI2.RebaseAt.sameRuntime rb))
    (targetStore-rename ins)

insertRebase-target-resolve-rev :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {W⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → ∀ Y
  → CTI2.resolveVar
      (CTI2.targetStoreʷ (insertRebaseWorld ins Wᵖ))
      (toRenameᵗ ρ Y)
      ≡ renameᵗ (toRenameᵗ ρ)
          (CTI2.resolveVar (CTI2.targetStoreʷ Wᵖ) Y)
insertRebase-target-resolve-rev {ρ = ρ} {W = W} {Wᵖ = Wᵖ}
    ins rb Y =
  trans (target-resolve ins Y)
    (cong (renameᵗ (toRenameᵗ ρ)) target-same)
  where
  target-same : CTI2.resolveVar (CTI2.targetStoreʷ W) Y
      ≡ CTI2.resolveVar (CTI2.targetStoreʷ Wᵖ) Y
  target-same =
    cong (λ Σ → CTI2.resolveVar Σ Y)
      (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb))

insertRebaseTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → TargetInsert ρ π Wᵖ (insertRebaseWorld ins Wᵖ)
insertRebaseTargetInsert {ρ = ρ} {π = π} {Wᵖ = Wᵖ} ins rb = record
  { sourceStore-kept = refl
  ; transport⊑ᵂ = λ {A = A} {B = B} p →
      transport⊑ᵂ-from-geometry {ρ = ρ} {π = π} {W = Wᵖ}
        {W′ = insertRebaseWorld ins Wᵖ} {A = A} {B = B}
        (insertRebase-source-embed {Wᵖ = Wᵖ} ins)
        (insertRebase-target-embed {Wᵖ = Wᵖ} ins rb)
        (λ Z eq → trans (insertRebase-impEnv {Wᵖ = Wᵖ} ins Z) eq)
        p
  ; targetStore-rename = insertRebase-targetStore-rename ins rb
  ; source-resolve = λ X → refl
  ; target-resolve = insertRebase-target-resolve ins rb
  ; align-insert = λ {Xᴸ} {Xᴿ} aligned →
      trans (insertRebase-source {Wᵖ = Wᵖ} ins Xᴸ)
        (trans (cong (toRenameᵗ π) aligned)
          (sym (insertRebase-target {Wᵖ = Wᵖ} ins rb Xᴿ)))
  ; source-insert = λ X → insertRebase-source {Wᵖ = Wᵖ} ins X
  ; target-insert = λ Y → insertRebase-target {Wᵖ = Wᵖ} ins rb Y
  ; impEnv-insert = λ Z → insertRebase-impEnv {Wᵖ = Wᵖ} ins Z
  ; impEnv-off-insert =
      λ eq → renameEnv-off π (CTI2.impEnvʷ Wᵖ) eq
  ; target-center-reflect = insertRebase-target-center-reflect ins rb
  ; target-source-reflect = insertRebase-target-source-reflect ins rb
  }

insertRebaseTargetInsertRev : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → TargetInsert ρ π Wᵖ (insertRebaseWorld ins Wᵖ)
insertRebaseTargetInsertRev {ρ = ρ} {π = π} {Wᵖ = Wᵖ}
    ins rb = record
  { sourceStore-kept = refl
  ; transport⊑ᵂ = λ {A = A} {B = B} p →
      transport⊑ᵂ-from-geometry {ρ = ρ} {π = π} {W = Wᵖ}
        {W′ = insertRebaseWorld ins Wᵖ} {A = A} {B = B}
        (insertRebase-source-embed {Wᵖ = Wᵖ} ins)
        (insertRebase-target-embed-rev {Wᵖ = Wᵖ} ins rb)
        (λ Z eq → trans (insertRebase-impEnv {Wᵖ = Wᵖ} ins Z) eq)
        p
  ; targetStore-rename = insertRebase-targetStore-rename-rev ins rb
  ; source-resolve = λ X → refl
  ; target-resolve = insertRebase-target-resolve-rev ins rb
  ; align-insert = λ {Xᴸ} {Xᴿ} aligned →
      trans (insertRebase-source {Wᵖ = Wᵖ} ins Xᴸ)
        (trans (cong (toRenameᵗ π) aligned)
          (sym (insertRebase-target-rev {Wᵖ = Wᵖ} ins rb Xᴿ)))
  ; source-insert = λ X → insertRebase-source {Wᵖ = Wᵖ} ins X
  ; target-insert = λ Y → insertRebase-target-rev {Wᵖ = Wᵖ} ins rb Y
  ; impEnv-insert = λ Z → insertRebase-impEnv {Wᵖ = Wᵖ} ins Z
  ; impEnv-off-insert =
      λ eq → renameEnv-off π (CTI2.impEnvʷ Wᵖ) eq
  ; target-center-reflect = insertRebase-target-center-reflect-rev ins rb
  ; target-source-reflect = insertRebase-target-source-reflect-rev ins rb
  }

insertRebaseAt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTI2.RebaseAt W⁺ Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
insertRebaseAt {ρ = ρ} {π = π} {Wᵖ = Wᵖ} {W⁺ = W⁺}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} ins rb =
  insertRebaseWorld ins Wᵖ , insᵖ ,
    CTI2.rebase-at runtime off-left frozen-target aligned reps
  where
  insᵖ = insertRebaseTargetInsert ins rb

  runtime : CTI2.SameRuntime W⁺ (insertRebaseWorld ins Wᵖ)
  runtime =
    CTI2.same-runtime
      (trans
        (CTI2.SameRuntime.sourceStore-same
          (CTI2.RebaseAt.sameRuntime rb))
        (sym (sourceStore-kept ins)))
      refl

  off-left : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ
        (CTI2.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Y
      ≡ toRenameᵗ (CTI2.ηᴸʷ W⁺) Y
  off-left {Y} Y≢ =
    trans (insertRebase-source {Wᵖ = Wᵖ} ins Y)
      (trans
        (cong (toRenameᵗ π) (CTI2.RebaseAt.ηᴸ-off-pivot rb Y≢))
        (sym (source-insert ins Y)))

  frozen-target : ∀ Y
    → toRenameᵗ
        (CTI2.ηᴿʷ (insertRebaseWorld ins Wᵖ)) Y
      ≡ toRenameᵗ (CTI2.ηᴿʷ W⁺) Y
  frozen-target Y = refl

  aligned : toRenameᵗ
      (CTI2.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Xᴸ
      ≡ toRenameᵗ (CTI2.ηᴿʷ (insertRebaseWorld ins Wᵖ))
          (toRenameᵗ ρ Xᴿ)
  aligned =
    trans (insertRebase-source {Wᵖ = Wᵖ} ins Xᴸ)
      (trans (cong (toRenameᵗ π) (CTI2.RebaseAt.pivotAligned rb))
        (trans (cong (toRenameᵗ π) (CTI2.RebaseAt.ηᴿ-frozen rb Xᴿ))
          (sym (target-insert ins Xᴿ))))

  reps : CTI2.StoreRepImp (insertRebaseWorld ins Wᵖ)
      Xᴸ (toRenameᵗ ρ Xᴿ)
  reps =
    storeRep-insert insᵖ (CTI2.RebaseAt.storeRepresentations rb)

reverseRebaseAt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTI2.RebaseAt Wᵖ⁺ W⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
reverseRebaseAt {ρ = ρ} {π = π} {Wᵖ = Wᵖ} {W⁺ = W⁺}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} ins rb =
  insertRebaseWorld ins Wᵖ , insᵖ ,
    CTI2.rebase-at runtime off-left frozen-target aligned reps
  where
  insᵖ = insertRebaseTargetInsertRev ins rb

  runtime : CTI2.SameRuntime (insertRebaseWorld ins Wᵖ) W⁺
  runtime =
    CTI2.same-runtime
      (trans (sourceStore-kept ins)
        (CTI2.SameRuntime.sourceStore-same
          (CTI2.RebaseAt.sameRuntime rb)))
      refl

  off-left : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ (CTI2.ηᴸʷ W⁺) Y
      ≡ toRenameᵗ
          (CTI2.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Y
  off-left {Y} Y≢ =
    trans (source-insert ins Y)
      (trans
        (cong (toRenameᵗ π) (CTI2.RebaseAt.ηᴸ-off-pivot rb Y≢))
        (sym (insertRebase-source {Wᵖ = Wᵖ} ins Y)))

  frozen-target : ∀ Y
    → toRenameᵗ (CTI2.ηᴿʷ W⁺) Y
      ≡ toRenameᵗ
          (CTI2.ηᴿʷ (insertRebaseWorld ins Wᵖ)) Y
  frozen-target Y = refl

  aligned : toRenameᵗ (CTI2.ηᴸʷ W⁺) Xᴸ
      ≡ toRenameᵗ (CTI2.ηᴿʷ W⁺) (toRenameᵗ ρ Xᴿ)
  aligned =
    trans (source-insert ins Xᴸ)
      (trans (cong (toRenameᵗ π) (CTI2.RebaseAt.pivotAligned rb))
        (sym (target-insert ins Xᴿ)))

  reps : CTI2.StoreRepImp W⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
  reps =
    storeRep-insert ins (CTI2.RebaseAt.storeRepresentations rb)

TargetExtendOPEᵀ : Set₁
TargetExtendOPEᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ins : TargetInsert ρ π W W′)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W′ ∣ mapCtxᵀ ins γ
      ⊢² M ⊑ renameᵗᵐ ρ M′ ∶ transport⊑ᵂ ins p

RebaseAtᴿInsertCommuteᵀ : Set₁
RebaseAtᴿInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.RebaseAtᴿ W Wᵖ Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTI2.RebaseAtᴿ W⁺ Wᵖ⁺
        (mapPivot (toRenameᵗ ρ) Xᴿ?)

RebaseAtᴸInsertCommuteᵀ : Set₁
RebaseAtᴸInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTI2.RebaseAtᴸ W⁺ Wᵖ⁺ Xᴸ?

TagRebaseAtᴸInsertCommuteᵀ : Set₁
TagRebaseAtᴸInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTI2.TagRebaseAtᴸ W⁺ Wᵖ⁺ Xᴸ?
        (mapPivot (toRenameᵗ ρ) Xᴿ?)

RebaseAtInsertCommuteᵀ : Set₁
RebaseAtInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTI2.RebaseAt W⁺ Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)

ImpEnvMonoInsertCommuteᵀ : Set₁
ImpEnvMonoInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
  → TargetInsert ρ π W W⁺
  → TargetInsert ρ π Wᵖ Wᵖ⁺
  → CTI2.ImpEnvMono W Wᵖ
  → CTI2.ImpEnvMono W⁺ Wᵖ⁺

insert-to-starᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) ≡ X⊑★
  → CTI2.impEnvʷ W⁺ (toRenameᵗ (CTI2.ηᴸʷ W⁺) Xᴸ) ≡ X⊑★
insert-to-starᴸ {W = W} {W⁺ = W⁺} {Xᴸ = Xᴸ} ins to-star =
  trans (cong (CTI2.impEnvʷ W⁺) (source-insert ins Xᴸ))
    (trans (impEnv-insert ins (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ))
      to-star)

insert-disalignedᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ}
  → (ins : TargetInsert ρ π W W⁺)
  → (∀ Xᴿ → toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
      ≢ toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ′ → toRenameᵗ (CTI2.ηᴿʷ W⁺) Xᴿ′
      ≢ toRenameᵗ (CTI2.ηᴸʷ W⁺) Xᴸ
insert-disalignedᴸ ins disaligned Xᴿ′ eq
    with target-source-reflect ins (sym eq)
insert-disalignedᴸ ins disaligned Xᴿ′ eq
    | Xᴿ , xᴿ′-eq , aligned =
  disaligned Xᴿ (sym aligned)

insert-represented★ᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ ⊑ᵂ⟨ W ⟩ ★
  → CTI2.resolveVar (CTI2.sourceStoreʷ W⁺) Xᴸ ⊑ᵂ⟨ W⁺ ⟩ ★
insert-represented★ᴸ {W⁺ = W⁺} {Xᴸ = Xᴸ} ins represented =
  subst≡ (λ A → A ⊑ᵂ⟨ W⁺ ⟩ ★)
    (sym (source-resolve ins Xᴸ))
    (transport⊑ᵂ ins represented)

insertRebaseAtᴿ : RebaseAtᴿInsertCommuteᵀ
insertRebaseAtᴿ ins CTI2.rebase-idᴿ =
  _ , ins , CTI2.rebase-idᴿ
insertRebaseAtᴿ ins (CTI2.rebase-varᴿ rb)
    with insertRebaseAt ins rb
insertRebaseAtᴿ ins (CTI2.rebase-varᴿ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTI2.rebase-varᴿ rb⁺

insertRebaseAtᴸ : RebaseAtᴸInsertCommuteᵀ
insertRebaseAtᴸ ins CTI2.rebase-idᴸ =
  _ , ins , CTI2.rebase-idᴸ
insertRebaseAtᴸ ins (CTI2.rebase-varᴸ rb)
    with insertRebaseAt ins rb
insertRebaseAtᴸ ins (CTI2.rebase-varᴸ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTI2.rebase-varᴸ rb⁺
insertRebaseAtᴸ {W⁺ = W⁺} ins
    (CTI2.rebase-onlyᴸ {Xᴸ = Xᴸ}
      to-star disaligned represented) =
  W⁺ , ins ,
    CTI2.rebase-onlyᴸ
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (insert-represented★ᴸ ins represented)

insertTagRebaseAtᴸ : TagRebaseAtᴸInsertCommuteᵀ
insertTagRebaseAtᴸ ins CTI2.tag-rebase-idᴸ =
  _ , ins , CTI2.tag-rebase-idᴸ
insertTagRebaseAtᴸ ins (CTI2.tag-rebase-varᴸ rb)
    with insertRebaseAt ins rb
insertTagRebaseAtᴸ ins (CTI2.tag-rebase-varᴸ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTI2.tag-rebase-varᴸ rb⁺
insertTagRebaseAtᴸ {W⁺ = W⁺} ins
    (CTI2.tag-rebase-onlyᴸ {Xᴸ = Xᴸ}
      to-star disaligned represented) =
  W⁺ , ins ,
    CTI2.tag-rebase-onlyᴸ
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (insert-represented★ᴸ ins represented)

reverseRebaseAtᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.RebaseAtᴿ Wᵖ W Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTI2.RebaseAtᴿ Wᵖ⁺ W⁺ (mapPivot (toRenameᵗ ρ) Xᴿ?)
reverseRebaseAtᴿ ins CTI2.rebase-idᴿ =
  _ , ins , CTI2.rebase-idᴿ
reverseRebaseAtᴿ ins (CTI2.rebase-varᴿ rb)
    with reverseRebaseAt ins rb
reverseRebaseAtᴿ ins (CTI2.rebase-varᴿ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTI2.rebase-varᴿ rb⁺

reverseRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.RebaseAtᴸ Wᵖ W Xᴸ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTI2.RebaseAtᴸ Wᵖ⁺ W⁺ Xᴸ?
reverseRebaseAtᴸ ins CTI2.rebase-idᴸ =
  _ , ins , CTI2.rebase-idᴸ
reverseRebaseAtᴸ ins (CTI2.rebase-varᴸ rb)
    with reverseRebaseAt ins rb
reverseRebaseAtᴸ ins (CTI2.rebase-varᴸ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTI2.rebase-varᴸ rb⁺
reverseRebaseAtᴸ {W⁺ = W⁺} ins
    (CTI2.rebase-onlyᴸ {Xᴸ = Xᴸ}
      to-star disaligned represented) =
  W⁺ , ins ,
    CTI2.rebase-onlyᴸ
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (insert-represented★ᴸ ins represented)

reverseTagRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTI2.TagRebaseAtᴸ Wᵖ⁺ W⁺ Xᴸ?
        (mapPivot (toRenameᵗ ρ) Xᴿ?)
reverseTagRebaseAtᴸ ins CTI2.tag-rebase-idᴸ =
  _ , ins , CTI2.tag-rebase-idᴸ
reverseTagRebaseAtᴸ ins (CTI2.tag-rebase-varᴸ rb)
    with reverseRebaseAt ins rb
reverseTagRebaseAtᴸ ins (CTI2.tag-rebase-varᴸ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTI2.tag-rebase-varᴸ rb⁺
reverseTagRebaseAtᴸ {W⁺ = W⁺} ins
    (CTI2.tag-rebase-onlyᴸ {Xᴸ = Xᴸ}
      to-star disaligned represented) =
  W⁺ , ins ,
    CTI2.tag-rebase-onlyᴸ
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (insert-represented★ᴸ ins represented)

impEnvMono-insert-pre : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTI2.ImpEnvMono W Wᵖ
  → (Z′ : TyVar Δ′)
  → CTI2.impEnvʷ W⁺ Z′ ≡ X⊑★
  → (m : Maybe (TyVar Δ))
  → preimage? π Z′ ≡ m
  → CTI2.impEnvʷ Wᵖ⁺ Z′ ≡ X⊑★
impEnvMono-insert-pre {π = π} {W = W} {W⁺ = W⁺} {Wᵖ⁺ = Wᵖ⁺}
    ins insᵖ mono Z′ star (just Z) pre =
  trans (cong (CTI2.impEnvʷ Wᵖ⁺) image-eq)
    (trans (impEnv-insert insᵖ Z) (mono Z old-star))
  where
  image-eq : Z′ ≡ toRenameᵗ π Z
  image-eq = preimage?-sound π pre

  image-star : CTI2.impEnvʷ W⁺ (toRenameᵗ π Z) ≡ X⊑★
  image-star =
    trans (sym (cong (CTI2.impEnvʷ W⁺) image-eq)) star

  old-star : CTI2.impEnvʷ W Z ≡ X⊑★
  old-star =
    trans (sym (impEnv-insert ins Z)) image-star
impEnvMono-insert-pre ins insᵖ mono Z′ star nothing pre =
  impEnv-off-insert insᵖ pre

impEnvMono-insert : ImpEnvMonoInsertCommuteᵀ
impEnvMono-insert {π = π} ins insᵖ mono Z′ star =
  impEnvMono-insert-pre ins insᵖ mono Z′ star (preimage? π Z′) refl

renamePivotJoin : ∀ {Δ Δ′} {p q r : Maybe (TyVar Δ)}
  → (ρ : TyVar Δ → TyVar Δ′)
  → PivotJoin p q r
  → PivotJoin (mapPivot ρ p) (mapPivot ρ q) (mapPivot ρ r)
renamePivotJoin ρ CTI2.join-none = CTI2.join-none
renamePivotJoin ρ CTI2.join-left = CTI2.join-left
renamePivotJoin ρ CTI2.join-right = CTI2.join-right
renamePivotJoin ρ CTI2.join-both = CTI2.join-both

mutual
  reveal-renameˣ : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
      {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {X? A B}
      {c : Conversion.Conv↑ Δ A B}
    → StoreRename ρ Σ Σ′
    → Σ ⊢↑[ X? ] c
    → Σ′ ⊢↑[ mapPivot ρ X? ] rename↑ ρ c
  reveal-renameˣ hΣ (CTI2.⊢↑-unsealˣ X∈) =
    CTI2.⊢↑-unsealˣ (hΣ X∈)
  reveal-renameˣ hΣ (CTI2.⊢↑-⇒ˣ join c⊢ d⊢) =
    CTI2.⊢↑-⇒ˣ (renamePivotJoin _ join)
      (conceal-renameˣ hΣ c⊢) (reveal-renameˣ hΣ d⊢)
  reveal-renameˣ {ρ = ρ} hΣ (CTI2.⊢↑-∀ˣ c⊢) =
    CTI2.⊢↑-∀ˣ (reveal-renameˣ (StoreRename-ext hΣ) c⊢)
  reveal-renameˣ {ρ = ρ} hΣ (CTI2.⊢↑-∀-idˣ c⊢) =
    CTI2.⊢↑-∀-idˣ (reveal-renameˣ (StoreRename-ext hΣ) c⊢)
  reveal-renameˣ hΣ CTI2.⊢↑-idˣ = CTI2.⊢↑-idˣ

  conceal-renameˣ : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
      {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {X? A B}
      {c : Conversion.Conv↓ Δ A B}
    → StoreRename ρ Σ Σ′
    → Σ ⊢↓[ X? ] c
    → Σ′ ⊢↓[ mapPivot ρ X? ] rename↓ ρ c
  conceal-renameˣ hΣ (CTI2.⊢↓-sealˣ X∈) =
    CTI2.⊢↓-sealˣ (hΣ X∈)
  conceal-renameˣ hΣ (CTI2.⊢↓-⇒ˣ join c⊢ d⊢) =
    CTI2.⊢↓-⇒ˣ (renamePivotJoin _ join)
      (reveal-renameˣ hΣ c⊢) (conceal-renameˣ hΣ d⊢)
  conceal-renameˣ {ρ = ρ} hΣ (CTI2.⊢↓-∀ˣ c⊢) =
    CTI2.⊢↓-∀ˣ (conceal-renameˣ (StoreRename-ext hΣ) c⊢)
  conceal-renameˣ {ρ = ρ} hΣ (CTI2.⊢↓-∀-idˣ c⊢) =
    CTI2.⊢↓-∀-idˣ (conceal-renameˣ (StoreRename-ext hΣ) c⊢)
  conceal-renameˣ hΣ CTI2.⊢↓-idˣ = CTI2.⊢↓-idˣ

------------------------------------------------------------------------
-- Target-term syntactic side conditions
------------------------------------------------------------------------

notTopTag-rename : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) {M : Term Δ}
  → CTI2.NotTopTag M
  → CTI2.NotTopTag (renameᵗᵐ ρ M)
notTopTag-rename ρ (CTI2.not-` x) = CTI2.not-` x
notTopTag-rename ρ CTI2.not-ƛ = CTI2.not-ƛ
notTopTag-rename ρ CTI2.not-· = CTI2.not-·
notTopTag-rename ρ CTI2.not-Λ = CTI2.not-Λ
notTopTag-rename ρ CTI2.not-⦂∀ = CTI2.not-⦂∀
notTopTag-rename ρ (CTI2.not-$ κ) = CTI2.not-$ κ
notTopTag-rename ρ (CTI2.not-⊕ op) = CTI2.not-⊕ op
notTopTag-rename ρ CTI2.not-↑ = CTI2.not-↑
notTopTag-rename ρ CTI2.not-↓ = CTI2.not-↓
notTopTag-rename ρ CTI2.not-blame = CTI2.not-blame

renameRep★PartnerOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {X : TyVar Δᴸ} {P Xᴿ? M′}
  → (∀ {X₀ Y₀}
      → CTI2.CenterAligned W X₀ Y₀
      → CTI2.CenterAligned W′ X₀ (toRenameᵗ ρ Y₀))
  → CTI2.Rep★PartnerOK W X P Xᴿ? M′
  → CTI2.Rep★PartnerOK W′ X P
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameRep★PartnerOK align (CTI2.rep★-untagged nt) =
  CTI2.rep★-untagged (notTopTag-rename _ nt)
renameRep★PartnerOK align (CTI2.rep★-nonvar-tag Gnv) =
  CTI2.rep★-nonvar-tag (renameNonVar _ Gnv)
renameRep★PartnerOK align (CTI2.rep★-var-tag aligned) =
  CTI2.rep★-var-tag (align aligned)
renameRep★PartnerOK align
    (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
  CTI2.rep★-matched-inner-tags X₂≢X (align aligned)
renameRep★PartnerOK align (CTI2.rep★-round-trip ok) =
  CTI2.rep★-round-trip (renameRep★PartnerOK align ok)

renameSealPartnerOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {X : TyVar Δᴸ} {P R Xᴿ? M′}
  → (∀ {X₀ Y₀}
      → CTI2.CenterAligned W X₀ Y₀
      → CTI2.CenterAligned W′ X₀ (toRenameᵗ ρ Y₀))
  → CTI2.SealPartnerOK W X P R Xᴿ? M′
  → CTI2.SealPartnerOK W′ X P R
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameSealPartnerOK align (CTI2.star-rep-target ok) =
  CTI2.star-rep-target (renameRep★PartnerOK align ok)
renameSealPartnerOK align (CTI2.plain-target nt) =
  CTI2.plain-target (notTopTag-rename _ nt)
renameSealPartnerOK align CTI2.name-protected-target =
  CTI2.name-protected-target

renameSourceConcealPartnerOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → (∀ {X₀ Y₀}
      → CTI2.CenterAligned W X₀ Y₀
      → CTI2.CenterAligned W′ X₀ (toRenameᵗ ρ Y₀))
  → CTI2.SourceConcealPartnerOK W M c Xᴿ? M′
  → CTI2.SourceConcealPartnerOK W′ M c
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameSourceConcealPartnerOK align (CTI2.seal-partner-ok ok) =
  CTI2.seal-partner-ok (renameSealPartnerOK align ok)
renameSourceConcealPartnerOK align CTI2.fun-conceal-target =
  CTI2.fun-conceal-target
renameSourceConcealPartnerOK align CTI2.all-conceal-target =
  CTI2.all-conceal-target
renameSourceConcealPartnerOK align CTI2.id-conceal-target =
  CTI2.id-conceal-target

renameMatchedConcealPartnerOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → (∀ {X₀ Y₀}
      → CTI2.CenterAligned W X₀ Y₀
      → CTI2.CenterAligned W′ X₀ (toRenameᵗ ρ Y₀))
  → CTI2.MatchedConcealPartnerOK W M c Xᴿ? M′
  → CTI2.MatchedConcealPartnerOK W′ M c
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameMatchedConcealPartnerOK align
    (CTI2.matched-seal-star-partner ok) =
  CTI2.matched-seal-star-partner (renameRep★PartnerOK align ok)
renameMatchedConcealPartnerOK align
    (CTI2.matched-seal-nonstar Rns) =
  CTI2.matched-seal-nonstar Rns
renameMatchedConcealPartnerOK align CTI2.matched-fun-conceal-target =
  CTI2.matched-fun-conceal-target
renameMatchedConcealPartnerOK align CTI2.matched-all-conceal-target =
  CTI2.matched-all-conceal-target
renameMatchedConcealPartnerOK align CTI2.matched-id-conceal-target =
  CTI2.matched-id-conceal-target

------------------------------------------------------------------------
-- Rebasing evidence across one root right bind
------------------------------------------------------------------------

right-target-map : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ)
  → ∀ Y
  → toRenameᵗ (keep η) (toRenameᵗ wk↪ᵗ Y)
      ≡ Fin.suc (toRenameᵗ η Y)
right-target-map η Y =
  cong (toRenameᵗ (keep η)) (toRename-wk-eq Y)

right-bind-transport⊑ᵂᵀ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ CTI2.rightOnlyWorld W B′ ⟩
      renameᵗ (toRenameᵗ wk↪ᵗ) B
right-bind-transport⊑ᵂᵀ {W = W} {B′ = B′} {A = A} {B = B} p =
  subst≡ (λ C → A ⊑ᵂ⟨ CTI2.rightOnlyWorld W B′ ⟩ C)
    (sym (renameᵗ-wk-eq B))
    (right-bind-⊑ᵂ {W = W} {B′ = B′} p)

right-bind-align : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → CTI2.CenterAligned W Xᴸ Xᴿ
  → CTI2.CenterAligned (CTI2.rightOnlyWorld W B)
      Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
right-bind-align {W = W} {Xᴿ = Xᴿ} aligned =
  trans (cong Fin.suc aligned)
    (sym (right-target-map (CTI2.ηᴿʷ W) Xᴿ))

right-bind-source-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ∀ Xᴸ
  → toRenameᵗ (CTI2.ηᴸʷ (CTI2.rightOnlyWorld W B)) Xᴸ
      ≡ toRenameᵗ wk↪ᵗ (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
right-bind-source-insert {W = W} Xᴸ =
  sym (toRename-wk-eq (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ))

right-bind-target-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ∀ Xᴿ
  → toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B))
      (toRenameᵗ wk↪ᵗ Xᴿ)
      ≡ toRenameᵗ wk↪ᵗ (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)
right-bind-target-insert {W = W} Xᴿ =
  trans (right-target-map (CTI2.ηᴿʷ W) Xᴿ)
    (sym (toRename-wk-eq (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)))

right-bind-impEnv-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ∀ Z
  → CTI2.impEnvʷ (CTI2.rightOnlyWorld W B) (toRenameᵗ wk↪ᵗ Z)
      ≡ CTI2.impEnvʷ W Z
right-bind-impEnv-insert Z
    rewrite toRename-wk-eq Z | toRename-id-eq Z =
  refl

right-bind-impEnv-off-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Z′ : TyVar (Nat.suc Δ)}
  → preimage? wk↪ᵗ Z′ ≡ nothing
  → CTI2.impEnvʷ (CTI2.rightOnlyWorld W B) Z′ ≡ X⊑★
right-bind-impEnv-off-insert {Z′ = Fin.zero} eq = refl
right-bind-impEnv-off-insert {Z′ = Fin.suc Z′} eq
    rewrite preimage-id↪ Z′ =
  ⊥-elim (just≢nothing eq)

right-bind-target-center-reflect : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Y′ Z}
  → toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)) Y′
      ≡ toRenameᵗ wk↪ᵗ Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ wk↪ᵗ Y ×
      toRenameᵗ (CTI2.ηᴿʷ W) Y ≡ Z
right-bind-target-center-reflect {Y′ = Fin.zero} {Z = Z} eq =
  ⊥-elim (zero≢suc (trans eq (toRename-wk-eq Z)))
right-bind-target-center-reflect {Y′ = Fin.suc Y} {Z = Z} eq =
  Y , sym (toRename-wk-eq Y) ,
    fin-suc-injective (trans eq (toRename-wk-eq Z))

right-bind-target-source-reflect : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Y′}
  → CTI2.CenterAligned (CTI2.rightOnlyWorld W B) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ wk↪ᵗ Y × CTI2.CenterAligned W Xᴸ Y
right-bind-target-source-reflect {Y′ = Fin.zero} ()
right-bind-target-source-reflect {Y′ = Fin.suc Y} aligned =
  Y , sym (toRename-wk-eq Y) , fin-suc-injective aligned

right-resolveVar-map : ∀ {Δ} (Σ : TyStore Δ) (B : Ty Δ)
  → ∀ Y
  → CTI2.resolveVar (TyStore.store-bind Σ B) (toRenameᵗ wk↪ᵗ Y)
      ≡ ⇑ᵗ (CTI2.resolveVar Σ Y)
right-resolveVar-map Σ B Y =
  cong (CTI2.resolveVar (TyStore.store-bind Σ B)) (toRename-wk-eq Y)

right-bind-source-resolve : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ∀ Xᴸ
  → CTI2.resolveVar
      (CTI2.sourceStoreʷ (CTI2.rightOnlyWorld W B)) Xᴸ
      ≡ CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ
right-bind-source-resolve Xᴸ = refl

right-bind-target-resolve : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ∀ Xᴿ
  → CTI2.resolveVar
      (CTI2.targetStoreʷ (CTI2.rightOnlyWorld W B))
      (toRenameᵗ wk↪ᵗ Xᴿ)
      ≡ renameᵗ (toRenameᵗ wk↪ᵗ)
          (CTI2.resolveVar (CTI2.targetStoreʷ W) Xᴿ)
right-bind-target-resolve {W = W} {B = B} Xᴿ =
  trans (right-resolveVar-map (CTI2.targetStoreʷ W) B Xᴿ)
    (sym (renameᵗ-wk-eq (CTI2.resolveVar (CTI2.targetStoreʷ W) Xᴿ)))

rightBindTargetInsert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → TargetInsert wk↪ᵗ wk↪ᵗ W (CTI2.rightOnlyWorld W B)
rightBindTargetInsert {W = W} {B = B} = record
  { sourceStore-kept = refl
  ; transport⊑ᵂ = λ p →
      right-bind-transport⊑ᵂᵀ {W = W} {B′ = B} p
  ; targetStore-rename = StoreRename-wk-bind {C = B}
  ; source-resolve = right-bind-source-resolve {W = W} {B = B}
  ; target-resolve = right-bind-target-resolve {W = W} {B = B}
  ; align-insert = λ aligned → right-bind-align {W = W} {B = B} aligned
  ; source-insert = right-bind-source-insert {W = W} {B = B}
  ; target-insert = right-bind-target-insert {W = W} {B = B}
  ; impEnv-insert = right-bind-impEnv-insert {W = W} {B = B}
  ; impEnv-off-insert =
      λ {Z′} eq →
        right-bind-impEnv-off-insert {W = W} {B = B} {Z′ = Z′} eq
  ; target-center-reflect =
      right-bind-target-center-reflect {W = W} {B = B}
  ; target-source-reflect =
      right-bind-target-source-reflect {W = W} {B = B}
  }

keepRightBindTargetInsert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {v : VarImp}
  → TargetInsert (keep wk↪ᵗ) (keep wk↪ᵗ)
      (CTI2.liftWorldBoth v W)
      (CTI2.liftWorldBoth v (CTI2.rightOnlyWorld W B))
keepRightBindTargetInsert {W = W} {B = B} {v = v} =
  liftBothTargetInsert {v = v} (rightBindTargetInsert {W = W} {B = B})

right-storeRep : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → CTI2.StoreRepImp W Xᴸ Xᴿ
  → CTI2.StoreRepImp (CTI2.rightOnlyWorld W B)
      Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
right-storeRep {W = W} {B = B} {Xᴿ = Xᴿ}
    (CTI2.store-rep-imp represented) =
  CTI2.store-rep-imp
    (subst≡
      (λ R → CTI2.resolveVar (CTI2.sourceStoreʷ W) _
        ⊑ᵂ⟨ CTI2.rightOnlyWorld W B ⟩ R)
      (sym (right-resolveVar-map (CTI2.targetStoreʷ W) B Xᴿ))
      (right-bind-⊑ᵂ {W = W} {B′ = B} represented))

rightRebaseAt : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.RebaseAt (CTI2.rightOnlyWorld W B)
      (CTI2.rightOnlyWorld W′ B) Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
rightRebaseAt {W = W} {W′ = W′} {B = B} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    (CTI2.rebase-at
      (CTI2.same-runtime source-eq target-eq)
      offL frozenR aligned reps) =
  CTI2.rebase-at
    (CTI2.same-runtime source-eq
      (cong (λ Σ → TyStore.store-bind Σ B) target-eq))
    (λ Y≢ → cong Fin.suc (offL Y≢))
    frozenR′
    (trans (cong Fin.suc aligned)
      (sym (right-target-map (CTI2.ηᴿʷ W′) Xᴿ)))
    (right-storeRep reps)
  where
  frozenR′ : ∀ Y
    → toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W′ B)) Y
      ≡ toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)) Y
  frozenR′ Fin.zero = refl
  frozenR′ (Fin.suc Y) = cong Fin.suc (frozenR Y)

right-disaligned : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) {B : Ty Δᴿ} {Xᴸ : TyVar Δᴸ}
  → (∀ Xᴿ → toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
      ≢ toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ → toRenameᵗ
      (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)) Xᴿ
        ≢ toRenameᵗ
          (CTI2.ηᴸʷ (CTI2.rightOnlyWorld W B)) Xᴸ
right-disaligned W disaligned Fin.zero ()
right-disaligned W disaligned (Fin.suc Xᴿ) eq =
  disaligned Xᴿ (fin-suc-injective eq)

rightRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ?}
  → CTI2.RebaseAtᴸ W W′ Xᴸ?
  → CTI2.RebaseAtᴸ (CTI2.rightOnlyWorld W B)
      (CTI2.rightOnlyWorld W′ B) Xᴸ?
rightRebaseAtᴸ CTI2.rebase-idᴸ = CTI2.rebase-idᴸ
rightRebaseAtᴸ (CTI2.rebase-varᴸ rb) =
  CTI2.rebase-varᴸ (rightRebaseAt rb)
rightRebaseAtᴸ {W = W} {B = B}
    (CTI2.rebase-onlyᴸ to-star disaligned represented) =
  CTI2.rebase-onlyᴸ to-star (right-disaligned W {B = B} disaligned)
    (right-bind-⊑ᵂ {W = W} {B′ = B} represented)

rightTagRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
  → CTI2.TagRebaseAtᴸ W W′ Xᴸ? Xᴿ?
  → CTI2.TagRebaseAtᴸ (CTI2.rightOnlyWorld W B)
      (CTI2.rightOnlyWorld W′ B) Xᴸ?
      (mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
rightTagRebaseAtᴸ CTI2.tag-rebase-idᴸ = CTI2.tag-rebase-idᴸ
rightTagRebaseAtᴸ (CTI2.tag-rebase-varᴸ rb) =
  CTI2.tag-rebase-varᴸ (rightRebaseAt rb)
rightTagRebaseAtᴸ {W = W} {B = B}
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented) =
  CTI2.tag-rebase-onlyᴸ to-star
    (right-disaligned W {B = B} disaligned)
    (right-bind-⊑ᵂ {W = W} {B′ = B} represented)

rightRebaseAtᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴿ?}
  → CTI2.RebaseAtᴿ W W′ Xᴿ?
  → CTI2.RebaseAtᴿ (CTI2.rightOnlyWorld W B)
      (CTI2.rightOnlyWorld W′ B)
      (mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
rightRebaseAtᴿ CTI2.rebase-idᴿ = CTI2.rebase-idᴿ
rightRebaseAtᴿ (CTI2.rebase-varᴿ rb) =
  CTI2.rebase-varᴿ (rightRebaseAt rb)

rightRebaseAtInsert : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ
  → Σ[ Wᵖ⁺ ∈ World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ) ]
      TargetInsert wk↪ᵗ wk↪ᵗ Wᵖ Wᵖ⁺ ×
      CTI2.RebaseAt (CTI2.rightOnlyWorld W B) Wᵖ⁺
        Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
rightRebaseAtInsert {Wᵖ = Wᵖ} {B = B} rb =
  CTI2.rightOnlyWorld Wᵖ B , rightBindTargetInsert , rightRebaseAt rb

rightRebaseAtᴸInsert : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ?}
  → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ) ]
      TargetInsert wk↪ᵗ wk↪ᵗ Wᵖ Wᵖ⁺ ×
      CTI2.RebaseAtᴸ (CTI2.rightOnlyWorld W B) Wᵖ⁺ Xᴸ?
rightRebaseAtᴸInsert {Wᵖ = Wᵖ} {B = B} rb =
  CTI2.rightOnlyWorld Wᵖ B , rightBindTargetInsert , rightRebaseAtᴸ rb

rightTagRebaseAtᴸInsert : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
  → CTI2.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ) ]
      TargetInsert wk↪ᵗ wk↪ᵗ Wᵖ Wᵖ⁺ ×
      CTI2.TagRebaseAtᴸ (CTI2.rightOnlyWorld W B) Wᵖ⁺ Xᴸ?
        (mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
rightTagRebaseAtᴸInsert {Wᵖ = Wᵖ} {B = B} rb =
  CTI2.rightOnlyWorld Wᵖ B , rightBindTargetInsert ,
    rightTagRebaseAtᴸ rb

rightRebaseAtᴿInsert : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴿ?}
  → CTI2.RebaseAtᴿ W Wᵖ Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ) ]
      TargetInsert wk↪ᵗ wk↪ᵗ Wᵖ Wᵖ⁺ ×
      CTI2.RebaseAtᴿ (CTI2.rightOnlyWorld W B) Wᵖ⁺
        (mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
rightRebaseAtᴿInsert {Wᵖ = Wᵖ} {B = B} rb =
  CTI2.rightOnlyWorld Wᵖ B , rightBindTargetInsert , rightRebaseAtᴿ rb

------------------------------------------------------------------------
-- Retargeting derivations
------------------------------------------------------------------------

mapCtxᴿ-∋ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : Reduction.StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {x A B}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → γ CTI2.∋ʷ x ⦂ CTI2.ctx-imp A B p
  → ECR.mapCtxᴿ ext γ CTI2.∋ʷ x ⦂
      CTI2.ctx-imp A (χs Reduction.▶ᵗ B) (ECR.transport⊑ᵂ ext p)
mapCtxᴿ-∋ ext CTI2.Zʷ = CTI2.Zʷ
mapCtxᴿ-∋ ext (CTI2.Sʷ x∈) = CTI2.Sʷ (mapCtxᴿ-∋ ext x∈)

⊢²-retarget : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ q
⊢²-retarget {W = W} {γ = γ} {M = M} {N = N} {p = p} {q = q} d =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ N ∶ r) (PI.⊑-unique p q) d

⊢²-retargetᴿ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B C : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ C}
  → B ≡ C
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ q
⊢²-retargetᴿ refl d = ⊢²-retarget d

source-reveal-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴸ)} {A B : Ty Δᴸ}
    {c : Conv↑ Δᴸ A B}
  → (ins : TargetInsert ρ π W W′)
  → CTI2.sourceStoreʷ W ⊢↑[ X? ] c
  → CTI2.sourceStoreʷ W′ ⊢↑[ X? ] c
source-reveal-insert ins c⊢ =
  subst≡ (λ Σ → Σ ⊢↑[ _ ] _) (sym (sourceStore-kept ins)) c⊢

source-conceal-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴸ)} {A B : Ty Δᴸ}
    {c : Conv↓ Δᴸ A B}
  → (ins : TargetInsert ρ π W W′)
  → CTI2.sourceStoreʷ W ⊢↓[ X? ] c
  → CTI2.sourceStoreʷ W′ ⊢↓[ X? ] c
source-conceal-insert ins c⊢ =
  subst≡ (λ Σ → Σ ⊢↓[ _ ] _) (sym (sourceStore-kept ins)) c⊢

target-typing-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {M : Term Δᴿ} {B : Ty Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩ ⊢ M ⦂ B
  → ⟨ Δᴿ′ , CTI2.targetStoreʷ W′ ,
        CTI2.tgtCtxʷ (mapCtxᵀ ins γ) ⟩
      ⊢ renameᵗᵐ ρ M ⦂ renameᵗ (toRenameᵗ ρ) B
target-typing-insert {ρ = ρ} {γ = γ} ins M⊢ =
  subst≡
    (λ Γ → ⟨ _ , _ , Γ ⟩
      ⊢ renameᵗᵐ ρ _ ⦂ renameᵗ (toRenameᵗ ρ) _)
    (sym (mapCtxᵀ-tgt ins γ))
    (typing-renameᵗ (targetStore-rename ins) M⊢)

rename-open↪ᵗ : ∀ {Δ Δ′}
    (ρ : Δ ↪ᵗ Δ′) (C : Ty (Nat.suc Δ)) (A : Ty Δ)
  → renameᵗ (toRenameᵗ ρ) (C [ A ]ᵗ)
      ≡ renameᵗ (toRenameᵗ (keep ρ)) C
          [ renameᵗ (toRenameᵗ ρ) A ]ᵗ
rename-open↪ᵗ ρ C A =
  trans (rename-openᵗ (toRenameᵗ ρ) C A)
    (cong (λ T → T [ renameᵗ (toRenameᵗ ρ) A ]ᵗ)
      (renameᵗ-cong C (λ X → sym (toRename-keep-eq ρ X))))

primArgTy-renameᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) op
  → primArgTy {Δ′} op ≡ renameᵗ ρ (primArgTy {Δ} op)
primArgTy-renameᵗ ρ addℕ = refl
primArgTy-renameᵗ ρ and𝔹 = refl

primResultTy-renameᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) op
  → primResultTy {Δ′} op ≡ renameᵗ ρ (primResultTy {Δ} op)
primResultTy-renameᵗ ρ addℕ = refl
primResultTy-renameᵗ ρ and𝔹 = refl

⊢²-target-insert : TargetExtendOPEᵀ
⊢²-target-insert ins (CTI2.x⊑x² x∈) =
  CTI2.x⊑x² (mapCtxᵀ-∋ ins x∈)
⊢²-target-insert {W = W} ins
    (CTI2.ƛ⊑ƛ² {pA = pA} {pB = pB} M⊑M′) =
  ⊢²-retarget
    (CTI2.ƛ⊑ƛ²
      (⊢²-target-insert ins M⊑M′))
⊢²-target-insert {W = W} ins
    (CTI2.·⊑·² {pA = pA} {pB = pB} L⊑L′ M⊑M′) =
  CTI2.·⊑·²
    (⊢²-retarget (⊢²-target-insert ins L⊑L′))
    (⊢²-target-insert ins M⊑M′)
⊢²-target-insert {ρ = ρ} {W′ = W′} ins
    (CTI2.Λ⊑Λ² {A = A} {B = B} {p = p}
      liftγ vV vV′ V⊑V′ q) =
  ⊢²-retargetᴿ (cong `∀ body-eq)
    (CTI2.Λ⊑Λ² (targetLiftCtxBoth ins liftγ) vV
      (renameᵗᵐ-preserves-Value _ vV′)
      (⊢²-target-insert (liftBothTargetInsert {v = X⊑X} ins) V⊑V′)
      q-keep)
  where
  body-eq : renameᵗ (toRenameᵗ (keep ρ)) B
      ≡ renameᵗ (extᵗ (toRenameᵗ ρ)) B
  body-eq = renameᵗ-cong B (toRename-keep-eq ρ)

  q-keep : `∀ A ⊑ᵂ⟨ W′ ⟩ `∀ (renameᵗ (toRenameᵗ (keep ρ)) B)
  q-keep =
    subst≡ (λ T → `∀ A ⊑ᵂ⟨ W′ ⟩ `∀ T)
      (sym body-eq) (transport⊑ᵂ ins q)
⊢²-target-insert {W = W} {γ = γ} ins
    (CTI2.Λ⊑² {p = p} Anv zero∈A liftγ vV M′⊢ V⊑M′ q) =
  CTI2.Λ⊑² Anv zero∈A (targetLiftCtxLeft ins liftγ) vV
    (target-typing-insert ins M′⊢)
    (⊢²-target-insert (liftLeftTargetInsert {v = X⊑★} ins) V⊑M′)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} {W′ = W′} ins
    (CTI2.•⊑•² {C = C} {C′ = C′} {A = A} {A′ = A′}
      p∀ M⊑M′ q r) =
  ⊢²-retargetᴿ (sym open-eq)
    (CTI2.•⊑•² p∀-keep
      (⊢²-retargetᴿ (sym (cong `∀ body-eq))
        (⊢²-target-insert ins M⊑M′))
      (transport⊑ᵂ ins q) r-open)
  where
  body-eq : renameᵗ (toRenameᵗ (keep ρ)) C′
      ≡ renameᵗ (extᵗ (toRenameᵗ ρ)) C′
  body-eq = renameᵗ-cong C′ (toRename-keep-eq ρ)

  open-eq = rename-open↪ᵗ ρ C′ A′

  p∀-keep : `∀ C ⊑ᵂ⟨ W′ ⟩
      `∀ (renameᵗ (toRenameᵗ (keep ρ)) C′)
  p∀-keep =
    subst≡ (λ T → `∀ C ⊑ᵂ⟨ W′ ⟩ `∀ T)
      (sym body-eq) (transport⊑ᵂ ins p∀)

  r-open : (C [ A ]ᵗ) ⊑ᵂ⟨ W′ ⟩
      (renameᵗ (toRenameᵗ (keep ρ)) C′
        [ renameᵗ (toRenameᵗ ρ) A′ ]ᵗ)
  r-open =
    subst≡
      (λ T → (C [ A ]ᵗ) ⊑ᵂ⟨ W′ ⟩ T)
      open-eq
      (transport⊑ᵂ ins r)
⊢²-target-insert {W = W} ins
    (CTI2.•⊑² p∀ M⊑M′ q r) =
  CTI2.•⊑² (transport⊑ᵂ ins p∀)
    (⊢²-target-insert ins M⊑M′)
    (transport⊑ᵂ ins q) (transport⊑ᵂ ins r)
⊢²-target-insert {ρ = ρ} {W′ = W′} ins (CTI2.κ⊑κ² κ p) =
  ⊢²-retargetᴿ const-eq (CTI2.κ⊑κ² κ p-const)
  where
  const-eq = constTy-renameᵗ (toRenameᵗ ρ) κ

  p-const =
    subst≡
      (λ T → constTy κ ⊑ᵂ⟨ W′ ⟩ T)
      (sym const-eq)
      (transport⊑ᵂ ins p)
⊢²-target-insert {ρ = ρ} ins
    (CTI2.cast⊑cast² {p = p} c c′ M⊑M′ q) =
  CTI2.cast⊑cast² c (renameᵐᶜ ρ c′)
    (⊢²-target-insert ins M⊑M′) (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} ins
    (CTI2.⊑cast² {p = p} c′ M⊑M′ q) =
  CTI2.⊑cast² (renameᵐᶜ ρ c′)
    (⊢²-target-insert ins M⊑M′) (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} ins
    (CTI2.⊑reveal² {W′ = W′} {p = p}
      mono rb sc c′⊢ M⊑M′ q)
    with insertRebaseAtᴿ ins rb
⊢²-target-insert {ρ = ρ} ins
    (CTI2.⊑reveal² {W′ = W′} {p = p}
      mono rb sc c′⊢ M⊑M′ q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  CTI2.⊑reveal²
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (reveal-renameˣ (targetStore-rename ins) c′⊢)
    (⊢²-target-insert insᵖ M⊑M′)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} ins
    (CTI2.⊑conceal² {W′ = W′} {p = p}
      mono rb sc c′⊢ M⊑M′ q)
    with reverseRebaseAtᴿ ins rb
⊢²-target-insert {ρ = ρ} ins
    (CTI2.⊑conceal² {W′ = W′} {p = p}
      mono rb sc c′⊢ M⊑M′ q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  CTI2.⊑conceal²
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (conceal-renameˣ (targetStore-rename ins) c′⊢)
    (⊢²-target-insert insᵖ M⊑M′)
    (transport⊑ᵂ ins q)
⊢²-target-insert ins
    (CTI2.cast⊑² {p = p} c M⊑M′ q) =
  CTI2.cast⊑² c
    (⊢²-target-insert ins M⊑M′) (transport⊑ᵂ ins q)
⊢²-target-insert ins
    (CTI2.reveal⊑² {W′ = W′} {p = p}
      mono rb sc c⊢ M⊑M′ q)
    with insertRebaseAtᴸ ins rb
⊢²-target-insert ins
    (CTI2.reveal⊑² {W′ = W′} {p = p}
      mono rb sc c⊢ M⊑M′ q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  CTI2.reveal⊑²
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (source-reveal-insert ins c⊢)
    (⊢²-target-insert insᵖ M⊑M′)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} ins
    (CTI2.conceal⊑² {W′ = W′} {p = p}
      ok mono rb sc c⊢ M⊑M′ q)
    with reverseTagRebaseAtᴸ ins rb
⊢²-target-insert {ρ = ρ} ins
    (CTI2.conceal⊑² {W′ = W′} {p = p}
      ok mono rb sc c⊢ M⊑M′ q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  CTI2.conceal⊑²
    (renameSourceConcealPartnerOK (align-insert insᵖ) ok)
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (source-conceal-insert ins c⊢)
    (⊢²-target-insert insᵖ M⊑M′)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} ins
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} {p = p}
      mono rb sc c⊢ c′⊢ M⊑M′ q)
    with insertRebaseAt ins rb
⊢²-target-insert {ρ = ρ} ins
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} {p = p}
      mono rb sc c⊢ c′⊢ M⊑M′ q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  CTI2.reveal⊑reveal²
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (source-reveal-insert ins c⊢)
    (reveal-renameˣ (targetStore-rename ins) c′⊢)
    (⊢²-target-insert insᵖ M⊑M′)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} ins
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      ok mono rb sc c⊢ c′⊢ M⊑M′ q)
    with reverseRebaseAt ins rb
⊢²-target-insert {ρ = ρ} ins
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      ok mono rb sc c⊢ c′⊢ M⊑M′ q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  CTI2.conceal⊑conceal²
    (renameMatchedConcealPartnerOK (align-insert insᵖ) ok)
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (source-conceal-insert ins c⊢)
    (conceal-renameˣ (targetStore-rename ins) c′⊢)
    (⊢²-target-insert insᵖ M⊑M′)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} ins
    (CTI2.packaged-seal-star² {Wᵖ = Wᵖ}
      {p★ = p★} {qᵖ = qᵖ}
      ok mono rb sc c⊢ c′⊢ M⊑M′ sourcePrem q)
    with reverseRebaseAt ins rb
⊢²-target-insert {ρ = ρ} ins
    (CTI2.packaged-seal-star² {Wᵖ = Wᵖ}
      {p★ = p★} {qᵖ = qᵖ}
      ok mono rb sc c⊢ c′⊢ M⊑M′ sourcePrem q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  CTI2.packaged-seal-star²
    (renameMatchedConcealPartnerOK (align-insert insᵖ) ok)
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (source-conceal-insert ins c⊢)
    (conceal-renameˣ (targetStore-rename ins) c′⊢)
    (⊢²-target-insert insᵖ M⊑M′)
    (⊢²-target-insert insᵖ sourcePrem)
    (transport⊑ᵂ ins q)
⊢²-target-insert {W = W} {γ = γ} ins
    (CTI2.blame⊑² M′⊢ p) =
  CTI2.blame⊑²
    (target-typing-insert ins M′⊢)
    (transport⊑ᵂ ins p)
⊢²-target-insert {Δᴿ = Δᴿ} {Δᴿ′ = Δᴿ′} {ρ = ρ}
    {W′ = W′} {γ = γ} ins
    (CTI2.⊕⊑⊕² op {L = L} {L′ = L′} {M = M} {M′ = M′}
      {p = p} {q = q} L⊑L′ M⊑M′ r) =
  ⊢²-retargetᴿ result-eq
    (CTI2.⊕⊑⊕² op
      L-arg
      M-arg
      r-result)
  where
  arg-eq : primArgTy {Δᴿ′} op
      ≡ renameᵗ (toRenameᵗ ρ) (primArgTy {Δᴿ} op)
  arg-eq = primArgTy-renameᵗ (toRenameᵗ ρ) op

  result-eq : primResultTy {Δᴿ′} op
      ≡ renameᵗ (toRenameᵗ ρ) (primResultTy {Δᴿ} op)
  result-eq = primResultTy-renameᵗ (toRenameᵗ ρ) op

  p-arg : primArgTy op ⊑ᵂ⟨ W′ ⟩ primArgTy op
  p-arg =
    subst≡
      (λ T → primArgTy op ⊑ᵂ⟨ W′ ⟩ T)
      (sym arg-eq)
      (transport⊑ᵂ ins p)

  q-arg : primArgTy op ⊑ᵂ⟨ W′ ⟩ primArgTy op
  q-arg =
    subst≡
      (λ T → primArgTy op ⊑ᵂ⟨ W′ ⟩ T)
      (sym arg-eq)
      (transport⊑ᵂ ins q)

  L-arg : W′ ∣ mapCtxᵀ ins γ
      ⊢² L ⊑ renameᵗᵐ ρ L′ ∶ p-arg
  L-arg =
    ⊢²-retargetᴿ {q = p-arg}
      (sym arg-eq) (⊢²-target-insert ins L⊑L′)

  M-arg : W′ ∣ mapCtxᵀ ins γ
      ⊢² M ⊑ renameᵗᵐ ρ M′ ∶ q-arg
  M-arg =
    ⊢²-retargetᴿ {q = q-arg}
      (sym arg-eq) (⊢²-target-insert ins M⊑M′)

  r-result =
    subst≡
      (λ T → primResultTy op ⊑ᵂ⟨ W′ ⟩ T)
      (sym result-eq)
      (transport⊑ᵂ ins r)

------------------------------------------------------------------------
-- Public single-bind surface
------------------------------------------------------------------------

TargetExtendBindᵀ : Set
TargetExtendBindᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ext : ECR.WorldExtendᴿ (bind B′ ∷ []) W
      (CTI2.rightOnlyWorld W B′))
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → CTI2.rightOnlyWorld W B′
      ∣ ECR.mapCtxᴿ ext γ
      ⊢² M ⊑ renameᵗᵐ wk↪ᵗ M′ ∶ ECR.transport⊑ᵂ ext p

mapCtx-rightBind-ECR : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
    (ext : ECR.WorldExtendᴿ (bind B′ ∷ []) W
      (CTI2.rightOnlyWorld W B′))
    (γ : CtxImp W)
  → ECR.mapCtxᴿ ext γ ≡ mapCtxᵀ rightBindTargetInsert γ
mapCtx-rightBind-ECR ext [] = refl
mapCtx-rightBind-ECR {W = W} {B′ = B′} ext
    (CTI2.ctx-imp A B p ∷ γ) =
  cong₂ _∷_ entry-eq (mapCtx-rightBind-ECR ext γ)
  where
  entry-eq :
      CTI2.ctx-imp A (⇑ᵗ B) (ECR.transport⊑ᵂ ext p)
      ≡ CTI2.ctx-imp A (renameᵗ (toRenameᵗ wk↪ᵗ) B)
          (transport⊑ᵂ (rightBindTargetInsert {W = W} {B = B′}) p)
  entry-eq =
    ctx-imp-target-eq {W = CTI2.rightOnlyWorld W B′}
      {A = A} {B = ⇑ᵗ B}
      {B′ = renameᵗ (toRenameᵗ wk↪ᵗ) B}
      {p = ECR.transport⊑ᵂ ext p}
      {q = transport⊑ᵂ (rightBindTargetInsert {W = W} {B = B′}) p}
      (sym (renameᵗ-wk-eq B))

⊢²-target-extend-bind : TargetExtendBindᵀ
⊢²-target-extend-bind {W = W} {γ = γ} {M = M} {M′ = M′}
    {B = B} {B′ = B′} {p = p} ext M⊑M′ =
  subst≡
    (λ γ′ → CTI2.rightOnlyWorld W B′ ∣ γ′
      ⊢² M ⊑ renameᵗᵐ wk↪ᵗ M′ ∶ ECR.transport⊑ᵂ ext p)
    (sym (mapCtx-rightBind-ECR ext γ))
    (⊢²-retargetᴿ {q = ECR.transport⊑ᵂ ext p}
      (renameᵗ-wk-eq B)
      (⊢²-target-insert
        (rightBindTargetInsert {W = W} {B = B′}) M⊑M′))
