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
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
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
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.ExtraCastRight2 as ECR
open import proof.TypeInTermSubst using
  (StoreRename; StoreRename-ext; StoreRename-keep; StoreRename-wk-bind;
   renameᵗᵐ-preserves-Value; renameᵗ-wk-eq; toRename-id-eq;
   toRename-keep-eq; toRename-wk-eq; typing-renameᵗ; rename-openᵗ)
open import proof.ImprecisionConsistency using
  (fin-suc-injective; rename-⊑; subst-⊑; toRenameᵗ-injective)
open import proof.DGG.Parked.ParkedBindImprecisionProof using (right-bind-⊑ᵂ)
open import proof.DGG.CenterRename using
  (_∘↪_; toRenameᵗ-∘; sucMaybe; preimage?; sucMaybe-nothing;
   preimage?-image; EmbeddingPair; pair; embeddingPair; EmbeddingPushout;
   pushout; embeddingPushout; EmbeddingWindow; window-here;
   pushout-window; embeddingPushoutWindow;
   pushout-old-off-premise; renameEnv;
   renameEnv-image; renameEnv-off)
import proof.Imprecision as PI

open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)

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
    (W′ : World Δᴸ Δᴿ′ Δ′) : Set where
  field
    sourceStore-kept : CTX.sourceStoreʷ W′ ≡ CTX.sourceStoreʷ W

    transport⊑ᵂ : ∀ {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B
      → A ⊑ᵂ⟨ W′ ⟩ renameᵗ (toRenameᵗ ρ) B

    targetStore-rename :
      StoreRename (toRenameᵗ ρ) (CTX.targetStoreʷ W)
        (CTX.targetStoreʷ W′)

    source-resolve : ∀ Xᴸ
      → CTX.resolveVar (CTX.sourceStoreʷ W′) Xᴸ
          ≡ CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ

    target-resolve : ∀ Xᴿ
      → CTX.resolveVar (CTX.targetStoreʷ W′) (toRenameᵗ ρ Xᴿ)
          ≡ renameᵗ (toRenameᵗ ρ)
              (CTX.resolveVar (CTX.targetStoreʷ W) Xᴿ)

    align-insert : ∀ {Xᴸ Xᴿ}
      → CTX.CenterAligned W Xᴸ Xᴿ
      → CTX.CenterAligned W′ Xᴸ (toRenameᵗ ρ Xᴿ)

    source-insert : ∀ Xᴸ
      → toRenameᵗ (CTX.ηᴸʷ W′) Xᴸ
          ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)

    target-insert : ∀ Xᴿ
      → toRenameᵗ (CTX.ηᴿʷ W′) (toRenameᵗ ρ Xᴿ)
          ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)

    impEnv-insert : ∀ Z
      → CTX.impEnvʷ W′ (toRenameᵗ π Z) ≡ CTX.impEnvʷ W Z

    impEnv-off-insert : ∀ {Z′}
      → preimage? π Z′ ≡ nothing
      → CTX.impEnvʷ W′ Z′ ≡ X⊑★

    target-center-reflect : ∀ {Y′ Z}
      → toRenameᵗ (CTX.ηᴿʷ W′) Y′ ≡ toRenameᵗ π Z
      → Σ[ Y ∈ TyVar Δᴿ ]
          Y′ ≡ toRenameᵗ ρ Y ×
          toRenameᵗ (CTX.ηᴿʷ W) Y ≡ Z

    target-source-reflect : ∀ {Xᴸ Y′}
      → CTX.CenterAligned W′ Xᴸ Y′
      → Σ[ Y ∈ TyVar Δᴿ ]
          Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned W Xᴸ Y

open TargetInsert public


record TargetWindowInsert {Δᴸ Δᴿ Δ Δ′}
    {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ (Nat.suc Δᴿ) Δ′}
    (ins : TargetInsert wk↪ᵗ π W W′)
    (κ : Nat.suc Δ ↪ᵗ Δ′) : Set where
  field
    windowEmbedding : EmbeddingWindow π κ
    window-zero :
      toRenameᵗ (CTX.ηᴿʷ W′) Fin.zero ≡ toRenameᵗ κ Fin.zero
    window-old : ∀ Z
      → toRenameᵗ π Z ≡ toRenameᵗ κ (Fin.suc Z)

open TargetWindowInsert public


target-source-reflect-from-center : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ Y′}
  → (ins : TargetInsert ρ π W W′)
  → CTX.CenterAligned W′ Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned W Xᴸ Y
target-source-reflect-from-center {π = π} {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Y′ = Y′} ins aligned
    with target-center-reflect ins target-image
  where
  target-image : toRenameᵗ (CTX.ηᴿʷ W′) Y′
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
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
mapCtxᵀ {ρ = ρ} ins (CTX.ctx-imp A B p ∷ γ) =
  CTX.ctx-imp A (renameᵗ (toRenameᵗ ρ) B) (transport⊑ᵂ ins p) ∷
    mapCtxᵀ ins γ

mapCtxᵀ-∋ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {x A B}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ins : TargetInsert ρ π W W′)
  → γ CTX.∋ʷ x ⦂ CTX.ctx-imp A B p
  → mapCtxᵀ ins γ CTX.∋ʷ x ⦂
      CTX.ctx-imp A (renameᵗ (toRenameᵗ ρ) B) (transport⊑ᵂ ins p)
mapCtxᵀ-∋ ins CTX.Zʷ = CTX.Zʷ
mapCtxᵀ-∋ ins (CTX.Sʷ x∈) = CTX.Sʷ (mapCtxᵀ-∋ ins x∈)

mapCtxᵀ-same : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
  → (ins : TargetInsert ρ π W W⁺)
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.SameCtx γ γᵖ
  → CTX.SameCtx (mapCtxᵀ ins γ) (mapCtxᵀ insᵖ γᵖ)
mapCtxᵀ-same ins insᵖ CTX.same-[] = CTX.same-[]
mapCtxᵀ-same ins insᵖ (CTX.same-∷ sc) =
  CTX.same-∷ (mapCtxᵀ-same ins insᵖ sc)

mapCtxᵀ-tgt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W′)
  → (γ : CtxImp W)
  → CTX.tgtCtxʷ (mapCtxᵀ ins γ)
      ≡ T.renameCtx (toRenameᵗ ρ) (CTX.tgtCtxʷ γ)
mapCtxᵀ-tgt ins [] = refl
mapCtxᵀ-tgt ins (CTX.ctx-imp A B p ∷ γ) =
  cong (renameᵗ _ B ∷_) (mapCtxᵀ-tgt ins γ)

source-embed-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W′)
  → (A : Ty Δᴸ)
  → CTX.embedᴸ W′ A
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴸ W A)
source-embed-insert {π = π} {W = W} ins A =
  trans (renameᵗ-cong A (source-insert ins))
    (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴸʷ W)) (toRenameᵗ π) A))

target-embed-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W′)
  → (B : Ty Δᴿ)
  → CTX.embedᴿ W′ (renameᵗ (toRenameᵗ ρ) B)
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴿ W B)
target-embed-insert {ρ = ρ} {π = π} {W = W} {W′ = W′} ins B =
  trans (renameᵗ-comp (toRenameᵗ ρ) (toRenameᵗ (CTX.ηᴿʷ W′)) B)
    (trans (renameᵗ-cong B (target-insert ins))
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ W))
        (toRenameᵗ π) B)))

transport⊑ᵂ-from-geometry : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (∀ C → CTX.embedᴸ W′ C
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴸ W C))
  → (∀ C → CTX.embedᴿ W′ (renameᵗ (toRenameᵗ ρ) C)
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴿ W C))
  → (∀ Z → CTX.impEnvʷ W Z ≡ X⊑★
      → CTX.impEnvʷ W′ (toRenameᵗ π Z) ≡ X⊑★)
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ W′ ⟩ renameᵗ (toRenameᵗ ρ) B
transport⊑ᵂ-from-geometry {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {A = A} {B = B} source-eq target-eq env-star p =
  subst≡
    (λ L → CTX.impEnvʷ W′ ⊢
      L ⊑ CTX.embedᴿ W′ (renameᵗ (toRenameᵗ ρ) B))
    (sym (source-eq A))
    (subst≡
      (λ R → CTX.impEnvʷ W′ ⊢
        renameᵗ (toRenameᵗ π) (CTX.embedᴸ W A) ⊑ R)
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

rename-as-subst : ∀ {Δ Δ′}
  → (ρ : Δ ⇒ʳ Δ′)
  → (A : Ty Δ)
  → substᵗ (λ X → ＇ ρ X) A ≡ renameᵗ ρ A
rename-as-subst ρ (＇ X) = refl
rename-as-subst ρ (‵ ι) = refl
rename-as-subst ρ ★ = refl
rename-as-subst ρ (A ⇒ B)
    rewrite rename-as-subst ρ A | rename-as-subst ρ B =
  refl
rename-as-subst ρ (`∀ A) =
  cong `∀
    (trans (substᵗ-cong A exts-eq)
      (rename-as-subst (extᵗ ρ) A))
  where
  exts-eq : ∀ X
    → extsᵗ (λ Y → ＇ ρ Y) X ≡ ＇ extᵗ ρ X
  exts-eq Fin.zero = refl
  exts-eq (Fin.suc X) = refl

transport⊑ᵂ-by-subst : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (σ : Δ ⇒ˢ Δ′)
  → (∀ Z → CTX.impEnvʷ W Z ≡ X⊑★
      → CTX.impEnvʷ W′ ⊢ σ Z ⊑ ★)
  → (∀ C → substᵗ σ (CTX.embedᴸ W C) ≡ CTX.embedᴸ W′ C)
  → (∀ C → substᵗ σ (CTX.embedᴿ W C) ≡ CTX.embedᴿ W′ C)
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ W′ ⟩ B
transport⊑ᵂ-by-subst {W = W} {W′ = W′} {A = A} {B = B}
    σ star-map source-eq target-eq p =
  subst≡
    (λ L → CTX.impEnvʷ W′ ⊢ L ⊑ CTX.embedᴿ W′ B)
    (source-eq A)
    (subst≡
      (λ R → CTX.impEnvʷ W′ ⊢ substᵗ σ (CTX.embedᴸ W A) ⊑ R)
      (target-eq B)
      (subst-⊑ star-map p))

storeRep-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → CTX.StoreRepImp W′ Xᴸ (toRenameᵗ ρ Xᴿ)
storeRep-insert {ρ = ρ} {W = W} {W′ = W′}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} ins
    (CTX.store-rep-imp represented) =
  CTX.store-rep-imp
    (subst≡
      (λ A → A ⊑ᵂ⟨ W′ ⟩
        CTX.resolveVar (CTX.targetStoreʷ W′) (toRenameᵗ ρ Xᴿ))
      (sym (source-resolve ins Xᴸ))
      (subst≡
        (λ B → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ
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
  → CTX.ctx-imp {W = W} A B p ≡ CTX.ctx-imp {W = W} A B′ q
ctx-imp-target-eq {W = W} {A = A} {B = B} {p = p} {q = q} refl =
  cong (λ r → CTX.ctx-imp {W = W} A B r) (PI.⊑-unique p q)

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

embeddingPair-disjoint : ∀ Δ₁ Δ₂
    {Z₁ : TyVar Δ₁} {Z₂ : TyVar Δ₂}
  → toRenameᵗ (EmbeddingPair.right (embeddingPair Δ₁ Δ₂)) Z₂
    ≢ toRenameᵗ (EmbeddingPair.left (embeddingPair Δ₁ Δ₂)) Z₁
embeddingPair-disjoint Nat.zero Δ₂ {Z₁ = ()}
embeddingPair-disjoint (Nat.suc Δ₁) Δ₂ {Z₁ = Fin.zero} eq =
  suc≢zero eq
embeddingPair-disjoint (Nat.suc Δ₁) Δ₂ {Z₁ = Fin.suc Z₁} eq =
  embeddingPair-disjoint Δ₁ Δ₂ (fin-suc-injective eq)

pushout-off-image-disjoint : ∀ {Δ Δ′ Δᵐ}
  → (π : Δ ↪ᵗ Δ′)
  → (old : Δ ↪ᵗ Δᵐ)
  → {Z′ : TyVar Δ′} {Zᵐ : TyVar Δᵐ}
  → preimage? π Z′ ≡ nothing
  → toRenameᵗ (EmbeddingPushout.old′ (embeddingPushout π old)) Z′
    ≢ toRenameᵗ (EmbeddingPushout.premise (embeddingPushout π old)) Zᵐ
pushout-off-image-disjoint {Δ′ = Δ′} {Δᵐ = Δᵐ} empty empty pre eq =
  embeddingPair-disjoint Δᵐ Δ′ eq
pushout-off-image-disjoint empty (skip old)
    {Zᵐ = Fin.zero} pre eq =
  suc≢zero eq
pushout-off-image-disjoint empty (skip old)
    {Zᵐ = Fin.suc Zᵐ} pre eq =
  pushout-off-image-disjoint empty old pre (fin-suc-injective eq)
pushout-off-image-disjoint (skip π) old
    {Z′ = Fin.zero} pre eq =
  zero≢suc eq
pushout-off-image-disjoint (skip π) old
    {Z′ = Fin.suc Z′} pre eq =
  pushout-off-image-disjoint π old pre (fin-suc-injective eq)
pushout-off-image-disjoint (keep π) (skip old)
    {Z′ = Fin.zero} pre eq =
  just≢nothing pre
pushout-off-image-disjoint (keep π) (skip old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.zero} pre eq =
  suc≢zero eq
pushout-off-image-disjoint (keep π) (skip old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.suc Zᵐ} pre eq =
  pushout-off-image-disjoint (keep π) old pre
    (fin-suc-injective eq)
pushout-off-image-disjoint (keep π) (keep old)
    {Z′ = Fin.zero} pre eq =
  just≢nothing pre
pushout-off-image-disjoint (keep π) (keep old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.zero} pre eq =
  suc≢zero eq
pushout-off-image-disjoint (keep π) (keep old)
    {Z′ = Fin.suc Z′} {Zᵐ = Fin.suc Zᵐ} pre eq =
  pushout-off-image-disjoint π old
    (sucMaybe-nothing (preimage? π Z′) pre)
    (fin-suc-injective eq)

target-insert-off-image-center : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Y′ : TyVar Δᴿ′}
  → (ins : TargetInsert ρ π W W′)
  → preimage? ρ Y′ ≡ nothing
  → preimage? π (toRenameᵗ (CTX.ηᴿʷ W′) Y′) ≡ nothing
target-insert-off-image-center {ρ = ρ} {π = π} {W′ = W′} {Y′ = Y′}
    ins off
    with preimage? π (toRenameᵗ (CTX.ηᴿʷ W′) Y′) in pre
target-insert-off-image-center {ρ = ρ} {π = π} {Y′ = Y′} ins off
    | nothing = refl
target-insert-off-image-center {ρ = ρ} {π = π} {Y′ = Y′} ins off
    | just Z with target-center-reflect ins (preimage?-sound π pre)
target-insert-off-image-center {ρ = ρ} {π = π} {Y′ = Y′} ins off
    | just Z | Y , y′-eq , target-eq =
  ⊥-elim (just≢nothing just-eq)
  where
  just-eq : just Y ≡ nothing
  just-eq =
    trans (sym (preimage?-image ρ Y))
      (trans (sym (cong (preimage? ρ) y′-eq)) off)

liftBoth-source-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldBoth v W′)) X
      ≡ toRenameᵗ (keep π)
          (toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldBoth v W)) X)
liftBoth-source-insert ins Fin.zero = refl
liftBoth-source-insert ins (Fin.suc X) =
  cong Fin.suc (source-insert ins X)

liftBoth-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W′))
      (toRenameᵗ (keep ρ) X)
      ≡ toRenameᵗ (keep π)
          (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W)) X)
liftBoth-target-insert ins Fin.zero = refl
liftBoth-target-insert ins (Fin.suc X) =
  cong Fin.suc (target-insert ins X)

liftBoth-target-center-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Y′ : TyVar (Nat.suc Δᴿ′)}
    {Z : TyVar (Nat.suc Δ)}
  → (ins : TargetInsert ρ π W W′)
  → toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W′)) Y′
      ≡ toRenameᵗ (keep π) Z
  → Σ[ Y ∈ TyVar (Nat.suc Δᴿ) ]
      Y′ ≡ toRenameᵗ (keep ρ) Y ×
      toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W)) Y ≡ Z
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
  → CTX.impEnvʷ (CTX.liftWorldBoth v W′) (toRenameᵗ (keep π) Z)
      ≡ CTX.impEnvʷ (CTX.liftWorldBoth v W) Z
liftBoth-impEnv-insert ins Fin.zero = refl
liftBoth-impEnv-insert ins (Fin.suc Z) =
  impEnv-insert ins Z

liftBoth-impEnv-off-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Z′ : TyVar (Nat.suc Δ′)}
  → (ins : TargetInsert ρ π W W′)
  → preimage? (keep π) Z′ ≡ nothing
  → CTX.impEnvʷ (CTX.liftWorldBoth v W′) Z′ ≡ X⊑★
liftBoth-impEnv-off-insert {Z′ = Fin.zero} ins ()
liftBoth-impEnv-off-insert {π = π} {Z′ = Fin.suc Z′} ins eq =
  impEnv-off-insert ins (sucMaybe-nothing (preimage? π Z′) eq)

liftBoth-source-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → CTX.resolveVar (CTX.sourceStoreʷ (CTX.liftWorldBoth v W′)) X
      ≡ CTX.resolveVar (CTX.sourceStoreʷ (CTX.liftWorldBoth v W)) X
liftBoth-source-resolve ins Fin.zero = refl
liftBoth-source-resolve ins (Fin.suc X) =
  cong ⇑ᵗ (source-resolve ins X)

liftBoth-target-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → CTX.resolveVar (CTX.targetStoreʷ (CTX.liftWorldBoth v W′))
      (toRenameᵗ (keep ρ) X)
      ≡ renameᵗ (toRenameᵗ (keep ρ))
          (CTX.resolveVar
            (CTX.targetStoreʷ (CTX.liftWorldBoth v W)) X)
liftBoth-target-resolve ins Fin.zero = refl
liftBoth-target-resolve {ρ = ρ} {W = W} ins (Fin.suc X) =
  trans (cong ⇑ᵗ (target-resolve ins X))
    (sym (renameᵗ-keep-shift ρ
      (CTX.resolveVar (CTX.targetStoreʷ W) X)))

liftBoth-align-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Xᴸ : TyVar (Nat.suc Δᴸ)}
    {Xᴿ : TyVar (Nat.suc Δᴿ)}
  → (ins : TargetInsert ρ π W W′)
  → CTX.CenterAligned (CTX.liftWorldBoth v W) Xᴸ Xᴿ
  → CTX.CenterAligned (CTX.liftWorldBoth v W′) Xᴸ
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
  → CTX.CenterAligned (CTX.liftWorldBoth v W′) Xᴸ Y′
  → Σ[ Y ∈ TyVar (Nat.suc Δᴿ) ]
      Y′ ≡ toRenameᵗ (keep ρ) Y ×
      CTX.CenterAligned (CTX.liftWorldBoth v W) Xᴸ Y
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
      (CTX.liftWorldBoth v W) (CTX.liftWorldBoth v W′)
liftBothTargetInsert {ρ = ρ} {π = π} {W = W} {W′ = W′} {v = v} ins =
  record
    { sourceStore-kept = cong store-lift (sourceStore-kept ins)
    ; transport⊑ᵂ = λ {A = A} {B = B} p →
        transport⊑ᵂ-from-geometry {ρ = keep ρ} {π = keep π}
          {W = CTX.liftWorldBoth v W}
          {W′ = CTX.liftWorldBoth v W′}
          {A = A} {B = B}
          (λ C → trans
            (renameᵗ-cong C (liftBoth-source-insert {v = v} ins))
            (sym (renameᵗ-comp
              (toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldBoth v W)))
              (toRenameᵗ (keep π)) C)))
          (λ C → trans
            (renameᵗ-comp (toRenameᵗ (keep ρ))
              (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W′))) C)
            (trans
              (renameᵗ-cong C (liftBoth-target-insert {v = v} ins))
              (sym (renameᵗ-comp
                (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldBoth v W)))
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
  → toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldLeft v W′)) X
      ≡ toRenameᵗ (keep π)
          (toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldLeft v W)) X)
liftLeft-source-insert ins Fin.zero = refl
liftLeft-source-insert ins (Fin.suc X) =
  cong Fin.suc (source-insert ins X)

liftLeft-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft v W′))
      (toRenameᵗ ρ X)
      ≡ toRenameᵗ (keep π)
      (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft v W)) X)
liftLeft-target-insert ins X = cong Fin.suc (target-insert ins X)

liftLeft-target-center-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Y′ : TyVar Δᴿ′} {Z : TyVar (Nat.suc Δ)}
  → (ins : TargetInsert ρ π W W′)
  → toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft v W′)) Y′
      ≡ toRenameᵗ (keep π) Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft v W)) Y ≡ Z
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
  → CTX.impEnvʷ (CTX.liftWorldLeft v W′) (toRenameᵗ (keep π) Z)
      ≡ CTX.impEnvʷ (CTX.liftWorldLeft v W) Z
liftLeft-impEnv-insert ins Fin.zero = refl
liftLeft-impEnv-insert ins (Fin.suc Z) =
  impEnv-insert ins Z

liftLeft-impEnv-off-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Z′ : TyVar (Nat.suc Δ′)}
  → (ins : TargetInsert ρ π W W′)
  → preimage? (keep π) Z′ ≡ nothing
  → CTX.impEnvʷ (CTX.liftWorldLeft v W′) Z′ ≡ X⊑★
liftLeft-impEnv-off-insert {Z′ = Fin.zero} ins ()
liftLeft-impEnv-off-insert {π = π} {Z′ = Fin.suc Z′} ins eq =
  impEnv-off-insert ins (sucMaybe-nothing (preimage? π Z′) eq)

liftLeft-source-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp}
  → (ins : TargetInsert ρ π W W′)
  → ∀ X
  → CTX.resolveVar (CTX.sourceStoreʷ (CTX.liftWorldLeft v W′)) X
      ≡ CTX.resolveVar (CTX.sourceStoreʷ (CTX.liftWorldLeft v W)) X
liftLeft-source-resolve ins Fin.zero = refl
liftLeft-source-resolve ins (Fin.suc X) =
  cong ⇑ᵗ (source-resolve ins X)

liftLeft-align-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {Xᴸ : TyVar (Nat.suc Δᴸ)}
    {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → CTX.CenterAligned (CTX.liftWorldLeft v W) Xᴸ Xᴿ
  → CTX.CenterAligned (CTX.liftWorldLeft v W′) Xᴸ
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
  → CTX.CenterAligned (CTX.liftWorldLeft v W′) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      CTX.CenterAligned (CTX.liftWorldLeft v W) Xᴸ Y
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
      (CTX.liftWorldLeft v W) (CTX.liftWorldLeft v W′)
liftLeftTargetInsert {ρ = ρ} {π = π} {W = W} {W′ = W′} {v = v} ins =
  record
    { sourceStore-kept = cong store-lift (sourceStore-kept ins)
    ; transport⊑ᵂ = λ {A = A} {B = B} p →
        transport⊑ᵂ-from-geometry {ρ = ρ} {π = keep π}
          {W = CTX.liftWorldLeft v W}
          {W′ = CTX.liftWorldLeft v W′}
          {A = A} {B = B}
          (λ C → trans
            (renameᵗ-cong C (liftLeft-source-insert {v = v} ins))
            (sym (renameᵗ-comp
              (toRenameᵗ (CTX.ηᴸʷ (CTX.liftWorldLeft v W)))
              (toRenameᵗ (keep π)) C)))
          (λ C → trans
            (renameᵗ-comp (toRenameᵗ ρ)
              (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft v W′))) C)
            (trans
              (renameᵗ-cong C (liftLeft-target-insert {v = v} ins))
              (sym (renameᵗ-comp
                (toRenameᵗ (CTX.ηᴿʷ (CTX.liftWorldLeft v W)))
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
    {γ′ : CtxImp (CTX.liftWorldBoth v W)}
  → (ins : TargetInsert ρ π W W′)
  → CTX.LiftCtx v γ γ′
  → CTX.LiftCtx v (mapCtxᵀ ins γ)
      (mapCtxᵀ (liftBothTargetInsert {v = v} ins) γ′)
targetLiftCtxBoth ins CTX.lift-[] = CTX.lift-[]
targetLiftCtxBoth {ρ = ρ} {W′ = W′} {v = v} ins
    (CTX.lift-∷ {γ = γ} {γ′ = γ′} {A = A} {B = B}
      {p = p} {p′ = p′} liftγ) =
  subst≡
    (λ e → CTX.LiftCtx v
      (mapCtxᵀ ins (CTX.ctx-imp A B p ∷ γ))
      (e ∷ mapCtxᵀ (liftBothTargetInsert {v = v} ins) γ′))
    entry-eq
    (CTX.lift-∷ (targetLiftCtxBoth ins liftγ))
  where
  insBoth = liftBothTargetInsert {v = v} ins

  shift-eq :
      renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ B)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ρ) B)
  shift-eq = renameᵗ-keep-shift ρ B

  p-trans :
      ⇑ᵗ A ⊑ᵂ⟨ CTX.liftWorldBoth v W′ ⟩
        renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ B)
  p-trans = transport⊑ᵂ insBoth p′

  p-shift :
      ⇑ᵗ A ⊑ᵂ⟨ CTX.liftWorldBoth v W′ ⟩
        ⇑ᵗ (renameᵗ (toRenameᵗ ρ) B)
  p-shift = subst≡
    (λ T → ⇑ᵗ A ⊑ᵂ⟨ CTX.liftWorldBoth v W′ ⟩ T)
    shift-eq p-trans

  entry-eq =
    ctx-imp-target-eq {W = CTX.liftWorldBoth v W′}
      {A = ⇑ᵗ A} {B = ⇑ᵗ (renameᵗ (toRenameᵗ ρ) B)}
      {B′ = renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ B)}
      {p = p-shift} {q = p-trans}
      (sym (renameᵗ-keep-shift ρ B))

targetLiftCtxLeft : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {v : VarImp} {γ : CtxImp W}
    {γ′ : CtxImp (CTX.liftWorldLeft v W)}
  → (ins : TargetInsert ρ π W W′)
  → CTX.LiftCtxᴸ v γ γ′
  → CTX.LiftCtxᴸ v (mapCtxᵀ ins γ)
      (mapCtxᵀ (liftLeftTargetInsert {v = v} ins) γ′)
targetLiftCtxLeft ins CTX.liftᴸ-[] = CTX.liftᴸ-[]
targetLiftCtxLeft ins (CTX.liftᴸ-∷ liftγ) =
  CTX.liftᴸ-∷ (targetLiftCtxLeft ins liftγ)

targetSmartLiftCtxLeft : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ Δᵐ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′} {πᵐ : Δᵐ ↪ᵗ Δᵐ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    {Wᵐ′ : World (Nat.suc Δᴸ) Δᴿ′ Δᵐ′}
    {γ : CtxImp W} {γᵐ : CtxImp Wᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (insᵐ : TargetInsert ρ πᵐ Wᵐ Wᵐ′)
  → CTX.SmartLiftCtxᴸ γ γᵐ
  → CTX.SmartLiftCtxᴸ (mapCtxᵀ ins γ) (mapCtxᵀ insᵐ γᵐ)
targetSmartLiftCtxLeft ins insᵐ CTX.smart-lift-[] =
  CTX.smart-lift-[]
targetSmartLiftCtxLeft ins insᵐ (CTX.smart-lift-∷ liftγ) =
  CTX.smart-lift-∷ (targetSmartLiftCtxLeft ins insᵐ liftγ)

smartAliasInsertWorld : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → TargetInsert ρ π W W′
  → World (Nat.suc Δᴸ) Δᴿ Δ
  → World (Nat.suc Δᴸ) Δᴿ′ Δ′
smartAliasInsertWorld {π = π} {W′ = W′} ins Wᵐ =
  CTX.world (π ∘↪ CTX.ηᴸʷ Wᵐ) (CTX.ηᴿʷ W′)
    (renameEnv π (CTX.impEnvʷ Wᵐ))
    (CTX.sourceStoreʷ Wᵐ) (CTX.targetStoreʷ W′)

smartAlias-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → ∀ Y
  → toRenameᵗ (CTX.ηᴿʷ (smartAliasInsertWorld ins Wᵐ))
      (toRenameᵗ ρ Y)
    ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
smartAlias-target-insert {π = π} {W = W} ins guard Y =
  trans (target-insert ins Y)
    (cong (toRenameᵗ π)
      (sym (CTX.SmartAliasMergeGuard.target-frozen guard Y)))

smartAliasTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → TargetInsert ρ π Wᵐ (smartAliasInsertWorld ins Wᵐ)
smartAliasTargetInsert {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {Wᵐ = Wᵐ} ins guard =
  record
    { sourceStore-kept = refl
    ; transport⊑ᵂ = λ {A = A} {B = B} p →
        transport⊑ᵂ-from-geometry {ρ = ρ} {π = π}
          {W = Wᵐ} {W′ = smartAliasInsertWorld ins Wᵐ}
          {A = A} {B = B}
          (λ C → trans
            (renameᵗ-cong C (toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵐ)))
            (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴸʷ Wᵐ))
              (toRenameᵗ π) C)))
          (λ C → trans
            (renameᵗ-comp (toRenameᵗ ρ)
              (toRenameᵗ (CTX.ηᴿʷ
                (smartAliasInsertWorld ins Wᵐ))) C)
            (trans
              (renameᵗ-cong C (smartAlias-target-insert ins guard))
              (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ Wᵐ))
                (toRenameᵗ π) C))))
          (λ Z eq → trans (renameEnv-image π (CTX.impEnvʷ Wᵐ) Z) eq)
          p
    ; targetStore-rename =
        subst≡ (λ Σ → StoreRename (toRenameᵗ ρ) Σ
          (CTX.targetStoreʷ W′))
          (sym (CTX.SmartAliasMergeGuard.targetStore-same guard))
          (targetStore-rename ins)
    ; source-resolve = λ X → refl
    ; target-resolve = λ X →
        trans (target-resolve ins X)
          (cong (λ Σ → renameᵗ (toRenameᵗ ρ)
            (CTX.resolveVar Σ X))
            (sym (CTX.SmartAliasMergeGuard.targetStore-same guard)))
    ; align-insert = align′
    ; source-insert = toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵐ)
    ; target-insert = smartAlias-target-insert ins guard
    ; impEnv-insert = renameEnv-image π (CTX.impEnvʷ Wᵐ)
    ; impEnv-off-insert = renameEnv-off π (CTX.impEnvʷ Wᵐ)
    ; target-center-reflect = target-center-reflect′
    ; target-source-reflect = target-source-reflect′
    }
  where
  align′ : ∀ {Xᴸ Xᴿ}
    → CTX.CenterAligned Wᵐ Xᴸ Xᴿ
    → CTX.CenterAligned (smartAliasInsertWorld ins Wᵐ)
        Xᴸ (toRenameᵗ ρ Xᴿ)
  align′ {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} aligned =
    trans (toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵐ) Xᴸ)
      (trans (cong (toRenameᵗ π) aligned)
        (sym (smartAlias-target-insert ins guard Xᴿ)))

  target-center-reflect′ : ∀ {Y′ Z}
    → toRenameᵗ (CTX.ηᴿʷ (smartAliasInsertWorld ins Wᵐ)) Y′
        ≡ toRenameᵗ π Z
    → Σ[ Y ∈ TyVar _ ]
        Y′ ≡ toRenameᵗ ρ Y ×
        toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y ≡ Z
  target-center-reflect′ eq
      with target-center-reflect ins eq
  target-center-reflect′ eq | Y , y′-eq , target-eq =
    Y , y′-eq ,
      trans (CTX.SmartAliasMergeGuard.target-frozen guard Y) target-eq

  target-source-reflect′ : ∀ {Xᴸ Y′}
    → CTX.CenterAligned (smartAliasInsertWorld ins Wᵐ) Xᴸ Y′
    → Σ[ Y ∈ TyVar _ ]
        Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned Wᵐ Xᴸ Y
  target-source-reflect′ {Xᴸ = Xᴸ} {Y′ = Y′} aligned
      with target-center-reflect ins target-image
    where
    target-image : toRenameᵗ (CTX.ηᴿʷ W′) Y′
        ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Xᴸ)
    target-image =
      trans (sym aligned) (toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵐ) Xᴸ)
  target-source-reflect′ aligned | Y , y′-eq , target-eq =
    Y , y′-eq ,
      trans (sym target-eq)
        (sym (CTX.SmartAliasMergeGuard.target-frozen guard Y))


smartAliasTargetWindowInsert : ∀ {Δᴸ Δᴿ Δ Δ′}
    {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ (Nat.suc Δᴿ) Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
    {κ : Nat.suc Δ ↪ᵗ Δ′}
  → (ins : TargetInsert wk↪ᵗ π W W′)
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → TargetWindowInsert ins κ
  → TargetWindowInsert (smartAliasTargetInsert ins guard) κ
smartAliasTargetWindowInsert ins guard win = record
  { windowEmbedding = TargetWindowInsert.windowEmbedding win
  ; window-zero = TargetWindowInsert.window-zero win
  ; window-old = TargetWindowInsert.window-old win
  }

smartAliasGuardInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartAliasMergeGuard W Wᵐ β α)
  → CTX.SmartAliasMergeGuard W′ (smartAliasInsertWorld ins Wᵐ)
      (toRenameᵗ ρ β) (toRenameᵗ ρ α)
smartAliasGuardInsert {Δᴸ = Δᴸ} {Δᴿ′ = Δᴿ′} {Δ′ = Δ′}
    {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {Wᵐ = Wᵐ} {β = β} {α = α} ins guard =
  CTX.smart-alias-merge-guard
    (targetStore-rename ins
      (CTX.SmartAliasMergeGuard.β:=＇α guard))
    (targetStore-rename ins
      (CTX.SmartAliasMergeGuard.α:=★ guard))
    source-store target-store transport′ old-mark-mono′
    target-frozen′ pending-at-alias′ old-source-frozen′
    no-old-source-at-alias′ alias-mark′ name-mark′
    target-mark-off-footprint′
  where
  source-store : CTX.sourceStoreʷ (smartAliasInsertWorld ins Wᵐ)
      ≡ store-lift (CTX.sourceStoreʷ W′)
  source-store =
    trans (CTX.SmartAliasMergeGuard.sourceStore-lifted guard)
      (cong store-lift (sym (sourceStore-kept ins)))

  target-store : CTX.targetStoreʷ (smartAliasInsertWorld ins Wᵐ)
      ≡ CTX.targetStoreʷ W′
  target-store = refl

  target-frozen′ : ∀ Y′
    → toRenameᵗ (CTX.ηᴿʷ (smartAliasInsertWorld ins Wᵐ)) Y′
      ≡ toRenameᵗ (CTX.ηᴿʷ W′) Y′
  target-frozen′ Y′ = refl

  smartSubst : Nat.suc Δ′ ⇒ˢ Δ′
  smartSubst Fin.zero =
    ＇ (toRenameᵗ (CTX.ηᴿʷ W′) (toRenameᵗ ρ β))
  smartSubst (Fin.suc Z) = ＇ Z

  pending-at-alias′ :
    toRenameᵗ (CTX.ηᴸʷ (smartAliasInsertWorld ins Wᵐ)) Fin.zero
      ≡ toRenameᵗ (CTX.ηᴿʷ W′) (toRenameᵗ ρ β)
  pending-at-alias′ =
    trans (toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵐ) Fin.zero)
      (trans (cong (toRenameᵗ π)
        (CTX.SmartAliasMergeGuard.pending-at-alias guard))
        (sym (target-insert ins β)))

  old-source-frozen′ : ∀ Xᴸ
    → toRenameᵗ
        (CTX.ηᴸʷ (smartAliasInsertWorld ins Wᵐ)) (Fin.suc Xᴸ)
      ≡ toRenameᵗ (CTX.ηᴸʷ W′) Xᴸ
  old-source-frozen′ Xᴸ =
    trans (toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵐ) (Fin.suc Xᴸ))
      (trans (cong (toRenameᵗ π)
        (CTX.SmartAliasMergeGuard.old-source-frozen guard Xᴸ))
        (sym (source-insert ins Xᴸ)))

  old-mark-mono′ : ∀ Z′
    → CTX.impEnvʷ W′ Z′ ≡ X⊑★
    → CTX.impEnvʷ (smartAliasInsertWorld ins Wᵐ) Z′ ≡ X⊑★
  old-mark-mono′ Z′ star with preimage? π Z′ in pre
  old-mark-mono′ Z′ star | nothing =
    renameEnv-off π (CTX.impEnvʷ Wᵐ) pre
  old-mark-mono′ Z′ star | just Z =
    subst≡
      (λ C → CTX.impEnvʷ (smartAliasInsertWorld ins Wᵐ) C
        ≡ X⊑★)
      (sym image-eq)
      (trans (renameEnv-image π (CTX.impEnvʷ Wᵐ) Z)
        (CTX.SmartAliasMergeGuard.old-mark-mono guard Z old-star))
    where
    image-eq : Z′ ≡ toRenameᵗ π Z
    image-eq = preimage?-sound π pre

    old-star : CTX.impEnvʷ W Z ≡ X⊑★
    old-star =
      trans (sym (impEnv-insert ins Z))
        (subst≡ (λ C → CTX.impEnvʷ W′ C ≡ X⊑★)
          image-eq star)

  alias-mark′ :
    CTX.impEnvʷ (smartAliasInsertWorld ins Wᵐ)
      (toRenameᵗ (CTX.ηᴿʷ W′) (toRenameᵗ ρ β))
      ≡ X⊑★
  alias-mark′ =
    trans (cong (renameEnv π (CTX.impEnvʷ Wᵐ))
        (target-insert ins β))
      (trans (renameEnv-image π (CTX.impEnvʷ Wᵐ)
        (toRenameᵗ (CTX.ηᴿʷ W) β))
        (CTX.SmartAliasMergeGuard.alias-mark-dynamic guard))

  smartStar : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldLeft X⊑★ W′) Z ≡ X⊑★
    → CTX.impEnvʷ (smartAliasInsertWorld ins Wᵐ)
        ⊢ smartSubst Z ⊑ ★
  smartStar Fin.zero star = X⊑★ alias-mark′
  smartStar (Fin.suc Z) star = X⊑★ (old-mark-mono′ Z star)

  source-point : ∀ X
    → smartSubst (toRenameᵗ (keep (CTX.ηᴸʷ W′)) X)
      ≡ ＇ (toRenameᵗ (CTX.ηᴸʷ (smartAliasInsertWorld ins Wᵐ)) X)
  source-point Fin.zero = cong ＇_ (sym pending-at-alias′)
  source-point (Fin.suc X) = cong ＇_ (sym (old-source-frozen′ X))

  target-point : ∀ Y
    → smartSubst (toRenameᵗ (skip (CTX.ηᴿʷ W′)) Y)
      ≡ ＇ (toRenameᵗ (CTX.ηᴿʷ (smartAliasInsertWorld ins Wᵐ)) Y)
  target-point Y = refl

  source-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴸ (CTX.liftWorldLeft X⊑★ W′) C)
      ≡ CTX.embedᴸ (smartAliasInsertWorld ins Wᵐ) C
  source-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (keep (CTX.ηᴸʷ W′))) C)
      (trans (substᵗ-cong C source-point)
        (rename-as-subst
          (toRenameᵗ (CTX.ηᴸʷ (smartAliasInsertWorld ins Wᵐ))) C))

  target-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴿ (CTX.liftWorldLeft X⊑★ W′) C)
      ≡ CTX.embedᴿ (smartAliasInsertWorld ins Wᵐ) C
  target-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (skip (CTX.ηᴿʷ W′))) C)
      (trans (substᵗ-cong C target-point)
        (rename-as-subst
          (toRenameᵗ (CTX.ηᴿʷ (smartAliasInsertWorld ins Wᵐ))) C))

  transport′ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ′}
    → A ⊑ᵂ⟨ CTX.liftWorldLeft X⊑★ W′ ⟩ B
    → A ⊑ᵂ⟨ smartAliasInsertWorld ins Wᵐ ⟩ B
  transport′ =
    transport⊑ᵂ-by-subst
      {W = CTX.liftWorldLeft X⊑★ W′}
      {W′ = smartAliasInsertWorld ins Wᵐ}
      smartSubst smartStar source-eq target-eq

  no-old-source-at-alias′ : ∀ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ W′) Xᴸ
      ≢ toRenameᵗ (CTX.ηᴿʷ W′) (toRenameᵗ ρ β)
  no-old-source-at-alias′ Xᴸ eq =
    CTX.SmartAliasMergeGuard.no-old-source-at-alias guard Xᴸ
      (toRenameᵗ-injective π
        (trans (sym (source-insert ins Xᴸ))
          (trans eq (target-insert ins β))))

  name-mark′ :
    CTX.impEnvʷ (smartAliasInsertWorld ins Wᵐ)
      (toRenameᵗ (CTX.ηᴿʷ W′) (toRenameᵗ ρ α))
      ≡ X⊑★
  name-mark′ =
    trans (cong (renameEnv π (CTX.impEnvʷ Wᵐ))
        (target-insert ins α))
      (trans (renameEnv-image π (CTX.impEnvʷ Wᵐ)
        (toRenameᵗ (CTX.ηᴿʷ W) α))
        (CTX.SmartAliasMergeGuard.name-mark-dynamic guard))

  target-mark-off-footprint′ : ∀ Y′
    → Y′ ≢ toRenameᵗ ρ β
    → Y′ ≢ toRenameᵗ ρ α
    → CTX.impEnvʷ W′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′) ≡ X⊑★
    → CTX.impEnvʷ (smartAliasInsertWorld ins Wᵐ)
        (toRenameᵗ
          (CTX.ηᴿʷ (smartAliasInsertWorld ins Wᵐ)) Y′)
      ≡ X⊑★
  target-mark-off-footprint′ Y′ Y′≢β Y′≢α star
      with preimage? ρ Y′ in pre
  target-mark-off-footprint′ Y′ Y′≢β Y′≢α star
      | nothing =
    renameEnv-off π (CTX.impEnvʷ Wᵐ)
      (target-insert-off-image-center ins pre)
  target-mark-off-footprint′ Y′ Y′≢β Y′≢α star
      | just Y =
    subst≡
      (λ C → CTX.impEnvʷ (smartAliasInsertWorld ins Wᵐ) C
        ≡ X⊑★)
      (sym smart-image-eq)
      (trans (renameEnv-image π (CTX.impEnvʷ Wᵐ)
          (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y))
        (CTX.SmartAliasMergeGuard.target-mark-off-footprint guard
          Y Y≢β Y≢α old-star))
    where
    y′-eq : Y′ ≡ toRenameᵗ ρ Y
    y′-eq = preimage?-sound ρ pre

    Y≢β : Y ≢ β
    Y≢β eq = Y′≢β (trans y′-eq (cong (toRenameᵗ ρ) eq))

    Y≢α : Y ≢ α
    Y≢α eq = Y′≢α (trans y′-eq (cong (toRenameᵗ ρ) eq))

    old-center-eq :
      toRenameᵗ (CTX.ηᴿʷ W′) Y′
        ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ W) Y)
    old-center-eq =
      trans (cong (toRenameᵗ (CTX.ηᴿʷ W′)) y′-eq)
        (target-insert ins Y)

    old-star :
      CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴿʷ W) Y) ≡ X⊑★
    old-star =
      trans (sym (impEnv-insert ins
          (toRenameᵗ (CTX.ηᴿʷ W) Y)))
        (subst≡
          (λ C → CTX.impEnvʷ W′ C ≡ X⊑★)
          old-center-eq star)

    smart-image-eq :
      toRenameᵗ (CTX.ηᴿʷ W′) Y′
        ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
    smart-image-eq =
      trans old-center-eq
        (cong (toRenameᵗ π)
          (sym (CTX.SmartAliasMergeGuard.target-frozen guard Y)))

smartFreshInsertWorld : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → World (Nat.suc Δᴸ) Δᴿ′
      (EmbeddingPushout.Δᵐ′
        (embeddingPushout π
          (CTX.SmartFreshBehindGuard.oldCenters guard)))
smartFreshInsertWorld {π = π} {W′ = W′} {Wᵐ = Wᵐ} ins guard =
  CTX.world
    (EmbeddingPushout.premise po ∘↪ CTX.ηᴸʷ Wᵐ)
    (EmbeddingPushout.old′ po ∘↪ CTX.ηᴿʷ W′)
    (renameEnv (EmbeddingPushout.premise po) (CTX.impEnvʷ Wᵐ))
    (CTX.sourceStoreʷ Wᵐ) (CTX.targetStoreʷ W′)
  where
  po = embeddingPushout π (CTX.SmartFreshBehindGuard.oldCenters guard)

smartFresh-target-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → ∀ Y
  → toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard))
      (toRenameᵗ ρ Y)
    ≡ toRenameᵗ (EmbeddingPushout.premise
        (embeddingPushout π
          (CTX.SmartFreshBehindGuard.oldCenters guard)))
        (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
smartFresh-target-insert {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {Wᵐ = Wᵐ} ins guard Y =
  trans (toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′) (toRenameᵗ ρ Y))
    (trans (cong (toRenameᵗ old′) (target-insert ins Y))
      (trans (sym (commutes (toRenameᵗ (CTX.ηᴿʷ W) Y)))
        (cong (toRenameᵗ πᵐ)
          (sym (CTX.SmartFreshBehindGuard.target-frozen guard Y)))))
  where
  po = embeddingPushout π (CTX.SmartFreshBehindGuard.oldCenters guard)
  πᵐ = EmbeddingPushout.premise po
  old′ = EmbeddingPushout.old′ po
  commutes = EmbeddingPushout.commutes po

smartFreshTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → TargetInsert ρ (EmbeddingPushout.premise
      (embeddingPushout π
        (CTX.SmartFreshBehindGuard.oldCenters guard))) Wᵐ
      (smartFreshInsertWorld ins guard)
smartFreshTargetInsert {ρ = ρ} {π = π} {W = W} {W′ = W′}
    {Wᵐ = Wᵐ} ins guard =
  record
    { sourceStore-kept = refl
    ; transport⊑ᵂ = λ {A = A} {B = B} p →
        transport⊑ᵂ-from-geometry {ρ = ρ} {π = πᵐ}
          {W = Wᵐ} {W′ = smartFreshInsertWorld ins guard}
          {A = A} {B = B}
          (λ C → trans
            (renameᵗ-cong C (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ)))
            (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴸʷ Wᵐ))
              (toRenameᵗ πᵐ) C)))
          (λ C → trans
            (renameᵗ-comp (toRenameᵗ ρ)
              (toRenameᵗ (CTX.ηᴿʷ
                (smartFreshInsertWorld ins guard))) C)
            (trans
              (renameᵗ-cong C (smartFresh-target-insert ins guard))
              (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ Wᵐ))
                (toRenameᵗ πᵐ) C))))
          (λ Z eq → trans (renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ) Z) eq)
          p
    ; targetStore-rename =
        subst≡ (λ Σ → StoreRename (toRenameᵗ ρ) Σ
          (CTX.targetStoreʷ W′))
          (sym (CTX.SmartFreshBehindGuard.targetStore-same guard))
          (targetStore-rename ins)
    ; source-resolve = λ X → refl
    ; target-resolve = λ X →
        trans (target-resolve ins X)
          (cong (λ Σ → renameᵗ (toRenameᵗ ρ)
            (CTX.resolveVar Σ X))
            (sym (CTX.SmartFreshBehindGuard.targetStore-same guard)))
    ; align-insert = align′
    ; source-insert = toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ)
    ; target-insert = smartFresh-target-insert ins guard
    ; impEnv-insert = renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ)
    ; impEnv-off-insert = renameEnv-off πᵐ (CTX.impEnvʷ Wᵐ)
    ; target-center-reflect = target-center-reflect′
    ; target-source-reflect = target-source-reflect′
    }
  where
  po = embeddingPushout π (CTX.SmartFreshBehindGuard.oldCenters guard)
  πᵐ = EmbeddingPushout.premise po
  old = CTX.SmartFreshBehindGuard.oldCenters guard
  old′ = EmbeddingPushout.old′ po
  commutes = EmbeddingPushout.commutes po

  align′ : ∀ {Xᴸ Xᴿ}
    → CTX.CenterAligned Wᵐ Xᴸ Xᴿ
    → CTX.CenterAligned (smartFreshInsertWorld ins guard)
        Xᴸ (toRenameᵗ ρ Xᴿ)
  align′ {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} aligned =
    trans (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ) Xᴸ)
      (trans (cong (toRenameᵗ πᵐ) aligned)
        (sym (smartFresh-target-insert ins guard Xᴿ)))

  target-center-reflect′ : ∀ {Y′ Z}
    → toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
        ≡ toRenameᵗ πᵐ Z
    → Σ[ Y ∈ TyVar _ ]
        Y′ ≡ toRenameᵗ ρ Y ×
        toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y ≡ Z
  target-center-reflect′ {Y′ = Y′} {Z = Z} eq
      with preimage? ρ Y′ in pre
  target-center-reflect′ {Y′ = Y′} {Z = Z} eq
      | nothing =
    ⊥-elim (pushout-off-image-disjoint π old
      (target-insert-off-image-center ins pre) nested-eq)
    where
    nested-eq : toRenameᵗ old′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′)
      ≡ toRenameᵗ πᵐ Z
    nested-eq =
      trans (sym (toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′) Y′)) eq
  target-center-reflect′ {Y′ = Y′} {Z = Z} eq
      | just Y =
    Y , preimage?-sound ρ pre ,
      toRenameᵗ-injective πᵐ (trans (sym left-image) nested-eq)
    where
    y′-eq : Y′ ≡ toRenameᵗ ρ Y
    y′-eq = preimage?-sound ρ pre

    nested-eq : toRenameᵗ old′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′)
      ≡ toRenameᵗ πᵐ Z
    nested-eq =
      trans (sym (toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′) Y′)) eq

    left-image : toRenameᵗ old′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′)
      ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
    left-image =
      trans (cong (λ T →
          toRenameᵗ old′ (toRenameᵗ (CTX.ηᴿʷ W′) T)) y′-eq)
        (trans (cong (toRenameᵗ old′) (target-insert ins Y))
          (trans (sym (commutes (toRenameᵗ (CTX.ηᴿʷ W) Y)))
            (cong (toRenameᵗ πᵐ)
              (sym (CTX.SmartFreshBehindGuard.target-frozen guard Y)))))

  target-source-reflect′ : ∀ {Xᴸ Y′}
    → CTX.CenterAligned (smartFreshInsertWorld ins guard) Xᴸ Y′
    → Σ[ Y ∈ TyVar _ ]
        Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned Wᵐ Xᴸ Y
  target-source-reflect′ {Xᴸ = Xᴸ} {Y′ = Y′} aligned
      with target-center-reflect′ target-image
    where
    target-image :
      toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
        ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Xᴸ)
    target-image =
      trans (sym aligned) (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ) Xᴸ)
  target-source-reflect′ aligned | Y , y′-eq , target-eq =
    Y , y′-eq , sym target-eq

smartFreshGuardInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TargetInsert ρ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → CTX.SmartFreshBehindGuard W′ (smartFreshInsertWorld ins guard)
smartFreshGuardInsert {Δᴸ = Δᴸ} {Δᴿ′ = Δᴿ′} {Δ′ = Δ′}
    {ρ = ρ} {π = π} {W = W} {W′ = W′} {Wᵐ = Wᵐ}
    ins guard =
  CTX.smart-fresh-behind-guard old′
    source-store target-store transport′ old-mark-mono′
    target-frozen′ old-source-frozen′ fresh-not-target′ fresh-mark′
    target-mark-mono′
  where
  po = embeddingPushout π (CTX.SmartFreshBehindGuard.oldCenters guard)
  πᵐ = EmbeddingPushout.premise po
  old = CTX.SmartFreshBehindGuard.oldCenters guard
  old′ = EmbeddingPushout.old′ po
  commutes = EmbeddingPushout.commutes po

  source-store : CTX.sourceStoreʷ (smartFreshInsertWorld ins guard)
      ≡ store-lift (CTX.sourceStoreʷ W′)
  source-store =
    trans (CTX.SmartFreshBehindGuard.sourceStore-lifted guard)
      (cong store-lift (sym (sourceStore-kept ins)))

  target-store : CTX.targetStoreʷ (smartFreshInsertWorld ins guard)
      ≡ CTX.targetStoreʷ W′
  target-store = refl

  target-frozen′ : ∀ Y′
    → toRenameᵗ
        (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
      ≡ toRenameᵗ old′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′)
  target-frozen′ = toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′)

  smartSubst : Nat.suc Δ′ ⇒ˢ EmbeddingPushout.Δᵐ′ po
  smartSubst Fin.zero =
    ＇ (toRenameᵗ
      (CTX.ηᴸʷ (smartFreshInsertWorld ins guard)) Fin.zero)
  smartSubst (Fin.suc Z′) = ＇ (toRenameᵗ old′ Z′)

  old-source-frozen′ : ∀ Xᴸ
    → toRenameᵗ
        (CTX.ηᴸʷ (smartFreshInsertWorld ins guard)) (Fin.suc Xᴸ)
      ≡ toRenameᵗ old′ (toRenameᵗ (CTX.ηᴸʷ W′) Xᴸ)
  old-source-frozen′ Xᴸ =
    trans (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ) (Fin.suc Xᴸ))
      (trans (cong (toRenameᵗ πᵐ)
        (CTX.SmartFreshBehindGuard.old-source-frozen guard Xᴸ))
        (trans (commutes (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ))
          (cong (toRenameᵗ old′) (sym (source-insert ins Xᴸ)))))

  fresh-not-target′ : ∀ Y′
    → toRenameᵗ
        (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
      ≢ toRenameᵗ
        (CTX.ηᴸʷ (smartFreshInsertWorld ins guard)) Fin.zero
  fresh-not-target′ Y′ eq
      with target-center-reflect
        (smartFreshTargetInsert ins guard) target-image
    where
    target-image :
      toRenameᵗ
        (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
      ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero)
    target-image =
      trans eq (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ) Fin.zero)
  fresh-not-target′ Y′ eq | Y , y′-eq , target-eq =
    CTX.SmartFreshBehindGuard.fresh-not-target guard Y target-eq

  fresh-mark′ :
    CTX.impEnvʷ (smartFreshInsertWorld ins guard)
      (toRenameᵗ
        (CTX.ηᴸʷ (smartFreshInsertWorld ins guard)) Fin.zero)
      ≡ X⊑★
  fresh-mark′ =
    trans (cong (renameEnv πᵐ (CTX.impEnvʷ Wᵐ))
        (toRenameᵗ-∘ πᵐ (CTX.ηᴸʷ Wᵐ) Fin.zero))
      (trans (renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ)
        (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero))
        (CTX.SmartFreshBehindGuard.fresh-mark-dynamic guard))

  old-mark-mono′ : ∀ Z′
    → CTX.impEnvʷ W′ Z′ ≡ X⊑★
    → CTX.impEnvʷ (smartFreshInsertWorld ins guard)
        (toRenameᵗ old′ Z′) ≡ X⊑★
  old-mark-mono′ Z′ star with preimage? π Z′ in pre
  old-mark-mono′ Z′ star | nothing =
    renameEnv-off πᵐ (CTX.impEnvʷ Wᵐ)
      (pushout-old-off-premise π old pre)
  old-mark-mono′ Z′ star | just Z =
    subst≡
      (λ C → CTX.impEnvʷ (smartFreshInsertWorld ins guard) C
        ≡ X⊑★)
      (sym smart-image-eq)
      (trans (renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ)
          (toRenameᵗ old Z))
        (CTX.SmartFreshBehindGuard.old-mark-mono guard Z old-star))
    where
    image-eq : Z′ ≡ toRenameᵗ π Z
    image-eq = preimage?-sound π pre

    old-star : CTX.impEnvʷ W Z ≡ X⊑★
    old-star =
      trans (sym (impEnv-insert ins Z))
        (subst≡ (λ C → CTX.impEnvʷ W′ C ≡ X⊑★)
          image-eq star)

    smart-image-eq :
      toRenameᵗ old′ Z′ ≡ toRenameᵗ πᵐ (toRenameᵗ old Z)
    smart-image-eq =
      trans (cong (toRenameᵗ old′) image-eq) (sym (commutes Z))

  smartStar : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldLeft X⊑★ W′) Z ≡ X⊑★
    → CTX.impEnvʷ (smartFreshInsertWorld ins guard)
        ⊢ smartSubst Z ⊑ ★
  smartStar Fin.zero star = X⊑★ fresh-mark′
  smartStar (Fin.suc Z) star = X⊑★ (old-mark-mono′ Z star)

  source-point : ∀ X
    → smartSubst (toRenameᵗ (keep (CTX.ηᴸʷ W′)) X)
      ≡ ＇ (toRenameᵗ (CTX.ηᴸʷ (smartFreshInsertWorld ins guard)) X)
  source-point Fin.zero = refl
  source-point (Fin.suc X) = cong ＇_ (sym (old-source-frozen′ X))

  target-point : ∀ Y
    → smartSubst (toRenameᵗ (skip (CTX.ηᴿʷ W′)) Y)
      ≡ ＇ (toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y)
  target-point Y = cong ＇_ (sym (target-frozen′ Y))

  source-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴸ (CTX.liftWorldLeft X⊑★ W′) C)
      ≡ CTX.embedᴸ (smartFreshInsertWorld ins guard) C
  source-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (keep (CTX.ηᴸʷ W′))) C)
      (trans (substᵗ-cong C source-point)
        (rename-as-subst
          (toRenameᵗ (CTX.ηᴸʷ (smartFreshInsertWorld ins guard))) C))

  target-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴿ (CTX.liftWorldLeft X⊑★ W′) C)
      ≡ CTX.embedᴿ (smartFreshInsertWorld ins guard) C
  target-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (skip (CTX.ηᴿʷ W′))) C)
      (trans (substᵗ-cong C target-point)
        (rename-as-subst
          (toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard))) C))

  transport′ : ∀ {A : Ty (Nat.suc Δᴸ)} {B : Ty Δᴿ′}
    → A ⊑ᵂ⟨ CTX.liftWorldLeft X⊑★ W′ ⟩ B
    → A ⊑ᵂ⟨ smartFreshInsertWorld ins guard ⟩ B
  transport′ =
    transport⊑ᵂ-by-subst
      {W = CTX.liftWorldLeft X⊑★ W′}
      {W′ = smartFreshInsertWorld ins guard}
      smartSubst smartStar source-eq target-eq

  target-mark-mono′ : ∀ Y′
    → CTX.impEnvʷ W′ (toRenameᵗ (CTX.ηᴿʷ W′) Y′) ≡ X⊑★
    → CTX.impEnvʷ (smartFreshInsertWorld ins guard)
        (toRenameᵗ
          (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′)
      ≡ X⊑★
  target-mark-mono′ Y′ star with preimage? ρ Y′ in pre
  target-mark-mono′ Y′ star | nothing
      with preimage? πᵐ
        (toRenameᵗ
          (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′) in preᵐ
  target-mark-mono′ Y′ star | nothing | nothing =
    renameEnv-off πᵐ (CTX.impEnvʷ Wᵐ) preᵐ
  target-mark-mono′ Y′ star | nothing | just Z =
    ⊥-elim (just≢nothing just-eq)
    where
    reflected :
      Σ[ Y ∈ TyVar _ ]
        Y′ ≡ toRenameᵗ ρ Y ×
        toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y ≡ Z
    reflected =
      target-center-reflect (smartFreshTargetInsert ins guard)
        (preimage?-sound πᵐ preᵐ)

    Y = proj₁ reflected

    y′-eq : Y′ ≡ toRenameᵗ ρ Y
    y′-eq = proj₁ (proj₂ reflected)

    just-eq : just Y ≡ nothing
    just-eq =
      trans (sym (preimage?-image ρ Y))
        (trans (cong (preimage? ρ) (sym y′-eq)) pre)
  target-mark-mono′ Y′ star | just Y =
    subst≡
      (λ C → CTX.impEnvʷ (smartFreshInsertWorld ins guard) C
        ≡ X⊑★)
      (sym smart-image-eq)
      (trans (renameEnv-image πᵐ (CTX.impEnvʷ Wᵐ)
          (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y))
        (CTX.SmartFreshBehindGuard.target-mark-mono guard Y old-star))
    where
    y′-eq : Y′ ≡ toRenameᵗ ρ Y
    y′-eq = preimage?-sound ρ pre

    old-center-eq :
      toRenameᵗ (CTX.ηᴿʷ W′) Y′
        ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ W) Y)
    old-center-eq =
      trans (cong (toRenameᵗ (CTX.ηᴿʷ W′)) y′-eq)
        (target-insert ins Y)

    old-star :
      CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴿʷ W) Y) ≡ X⊑★
    old-star =
      trans (sym (impEnv-insert ins
          (toRenameᵗ (CTX.ηᴿʷ W) Y)))
        (subst≡
          (λ C → CTX.impEnvʷ W′ C ≡ X⊑★)
          old-center-eq star)

    smart-image-eq :
      toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)) Y′
        ≡ toRenameᵗ πᵐ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
    smart-image-eq =
      trans
        (cong
          (toRenameᵗ (CTX.ηᴿʷ (smartFreshInsertWorld ins guard)))
          y′-eq)
        (smartFresh-target-insert ins guard Y)


smartFreshTargetWindowInsert : ∀ {Δᴸ Δᴿ Δ Δ′ Δᵐ}
    {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ (Nat.suc Δᴿ) Δ′}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    {κ : Nat.suc Δ ↪ᵗ Δ′}
  → (ins : TargetInsert wk↪ᵗ π W W′)
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → TargetWindowInsert ins κ
  → Σ[ κᵐ ∈ Nat.suc Δᵐ ↪ᵗ
      EmbeddingPushout.Δᵐ′
        (embeddingPushout π
          (CTX.SmartFreshBehindGuard.oldCenters guard)) ]
      TargetWindowInsert (smartFreshTargetInsert ins guard) κᵐ
smartFreshTargetWindowInsert {π = π} {W′ = W′} ins guard win
    with embeddingPushoutWindow old (TargetWindowInsert.windowEmbedding win)
  where
  old = CTX.SmartFreshBehindGuard.oldCenters guard
smartFreshTargetWindowInsert {π = π} {W′ = W′} ins guard win
    | pushout-window κᵐ window-ok zero-commutes old-commutes =
  κᵐ , record
    { windowEmbedding = window-ok
    ; window-zero =
        trans (toRenameᵗ-∘ old′ (CTX.ηᴿʷ W′) Fin.zero)
          (trans
            (cong (toRenameᵗ old′)
              (TargetWindowInsert.window-zero win))
            zero-commutes)
    ; window-old = old-commutes
    }
  where
  old = CTX.SmartFreshBehindGuard.oldCenters guard
  old′ = EmbeddingPushout.old′ (embeddingPushout π old)


rightPushoutWindow : ∀ {Δ Δᵐ}
  → (old : Δ ↪ᵗ Δᵐ)
  → Nat.suc Δᵐ ↪ᵗ
      (EmbeddingPushout.Δᵐ′ (embeddingPushout wk↪ᵗ old))
rightPushoutWindow old =
  keep (EmbeddingPushout.premise (embeddingPushout id↪ᵗ old))

insertRebaseWorld : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → TargetInsert ρ π W W⁺
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ′ Δ′
insertRebaseWorld {π = π} {W⁺ = W⁺} ins Wᵖ =
  CTX.world (π ∘↪ CTX.ηᴸʷ Wᵖ) (CTX.ηᴿʷ W⁺)
    (renameEnv π (CTX.impEnvʷ Wᵖ))
    (CTX.sourceStoreʷ Wᵖ) (CTX.targetStoreʷ W⁺)

insertRebase-source : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → ∀ Xᴸ
  → toRenameᵗ
      (CTX.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Xᴸ
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ Wᵖ) Xᴸ)
insertRebase-source {π = π} {Wᵖ = Wᵖ} ins Xᴸ =
  toRenameᵗ-∘ π (CTX.ηᴸʷ Wᵖ) Xᴸ

insertRebase-target : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAt W Wᵖ Xᴸ Xᴿ
  → ∀ Y
  → toRenameᵗ
      (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ)) (toRenameᵗ ρ Y)
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ Wᵖ) Y)
insertRebase-target {π = π} ins rb Y =
  trans (target-insert ins Y)
    (cong (toRenameᵗ π) (sym (CTX.RebaseAt.ηᴿ-frozen rb Y)))

insertRebase-impEnv : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → ∀ Z
  → CTX.impEnvʷ (insertRebaseWorld ins Wᵖ) (toRenameᵗ π Z)
      ≡ CTX.impEnvʷ Wᵖ Z
insertRebase-impEnv {π = π} {Wᵖ = Wᵖ} ins Z =
  renameEnv-image π (CTX.impEnvʷ Wᵖ) Z

insertRebase-target-center-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {Y′ Z}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ)) Y′
      ≡ toRenameᵗ π Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      toRenameᵗ (CTX.ηᴿʷ Wᵖ) Y ≡ Z
insertRebase-target-center-reflect ins rb eq
    with target-center-reflect ins eq
insertRebase-target-center-reflect ins rb eq
    | Y , y′-eq , target-eq =
  Y , y′-eq , trans (CTX.RebaseAt.ηᴿ-frozen rb Y) target-eq

insertRebase-target-source-reflect : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᵖ : TyVar Δᴸ} {Yᵖ : TyVar Δᴿ} {Xᴸ Y′}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᵖ Yᵖ)
  → CTX.CenterAligned (insertRebaseWorld ins Wᵖ) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned Wᵖ Xᴸ Y
insertRebase-target-source-reflect {ρ = ρ} {π = π}
    {W = W} {Wᵖ = Wᵖ} {W⁺ = W⁺} {Xᵖ = Xᵖ} {Yᵖ = Yᵖ}
    {Xᴸ = Xᴸ} {Y′ = Y′} ins rb aligned
    with FinP._≟_ Xᴸ Xᵖ
insertRebase-target-source-reflect {ρ = ρ} {π = π}
    {Wᵖ = Wᵖ} {W⁺ = W⁺} {Xᵖ = Xᵖ} {Yᵖ = Yᵖ}
    {.Xᵖ} {Y′} ins rb aligned | yes refl =
  Yᵖ , y′-eq , CTX.RebaseAt.pivotAligned rb
  where
  pivot-target : toRenameᵗ
      (CTX.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Xᵖ
      ≡ toRenameᵗ (CTX.ηᴿʷ W⁺) (toRenameᵗ ρ Yᵖ)
  pivot-target =
    trans (insertRebase-source {Wᵖ = Wᵖ} ins Xᵖ)
      (trans (cong (toRenameᵗ π) (CTX.RebaseAt.pivotAligned rb))
        (trans (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴿ-frozen rb Yᵖ))
          (sym (target-insert ins Yᵖ))))

  y′-eq : Y′ ≡ toRenameᵗ ρ Yᵖ
  y′-eq =
    toRenameᵗ-injective (CTX.ηᴿʷ W⁺)
      (trans (sym aligned) pivot-target)
insertRebase-target-source-reflect {ρ = ρ} {π = π}
    {W = W} {Wᵖ = Wᵖ} {W⁺ = W⁺} {Xᵖ = Xᵖ}
    {Xᴸ = Xᴸ} {Y′ = Y′} ins rb aligned | no Xᴸ≢Xᵖ
    with target-source-reflect ins aligned⁺
  where
  source-shift : toRenameᵗ
      (CTX.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Xᴸ
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
  source-shift =
    trans (insertRebase-source {Wᵖ = Wᵖ} ins Xᴸ)
      (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴸ-off-pivot rb Xᴸ≢Xᵖ))

  aligned⁺ : CTX.CenterAligned W⁺ Xᴸ Y′
  aligned⁺ =
    trans (source-insert ins Xᴸ) (trans (sym source-shift) aligned)
insertRebase-target-source-reflect {Wᵖ = Wᵖ}
    {Xᴸ = Xᴸ} ins rb aligned | no Xᴸ≢Xᵖ
    | Y , y′-eq , aligned₀ =
  Y , y′-eq , alignedᵖ
  where
  alignedᵖ : CTX.CenterAligned Wᵖ Xᴸ Y
  alignedᵖ =
    trans (CTX.RebaseAt.ηᴸ-off-pivot rb Xᴸ≢Xᵖ)
      (trans aligned₀ (sym (CTX.RebaseAt.ηᴿ-frozen rb Y)))

insertRebase-source-embed : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (A : Ty Δᴸ)
  → CTX.embedᴸ (insertRebaseWorld ins Wᵖ) A
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴸ Wᵖ A)
insertRebase-source-embed {π = π} {Wᵖ = Wᵖ} ins A =
  trans (renameᵗ-cong A (insertRebase-source {Wᵖ = Wᵖ} ins))
    (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴸʷ Wᵖ)) (toRenameᵗ π) A))

insertRebase-target-embed : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → (B : Ty Δᴿ)
  → CTX.embedᴿ (insertRebaseWorld ins Wᵖ)
      (renameᵗ (toRenameᵗ ρ) B)
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴿ Wᵖ B)
insertRebase-target-embed {ρ = ρ} {π = π} {Wᵖ = Wᵖ} ins rb B =
  trans
    (renameᵗ-comp (toRenameᵗ ρ)
      (toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ))) B)
    (trans (renameᵗ-cong B (insertRebase-target ins rb))
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ Wᵖ))
        (toRenameᵗ π) B)))

insertRebase-targetStore-rename : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → StoreRename (toRenameᵗ ρ) (CTX.targetStoreʷ Wᵖ)
      (CTX.targetStoreʷ (insertRebaseWorld ins Wᵖ))
insertRebase-targetStore-rename {ρ = ρ} {W⁺ = W⁺} ins rb =
  subst≡
    (λ Σ → StoreRename (toRenameᵗ ρ) Σ (CTX.targetStoreʷ W⁺))
    (sym (CTX.SameRuntime.targetStore-same
      (CTX.RebaseAt.sameRuntime rb)))
    (targetStore-rename ins)

insertRebase-target-resolve : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → ∀ Y
  → CTX.resolveVar
      (CTX.targetStoreʷ (insertRebaseWorld ins Wᵖ))
      (toRenameᵗ ρ Y)
      ≡ renameᵗ (toRenameᵗ ρ)
          (CTX.resolveVar (CTX.targetStoreʷ Wᵖ) Y)
insertRebase-target-resolve {ρ = ρ} {W = W} {Wᵖ = Wᵖ} ins rb Y =
  trans (target-resolve ins Y)
    (cong (renameᵗ (toRenameᵗ ρ)) (sym target-same))
  where
  target-same : CTX.resolveVar (CTX.targetStoreʷ Wᵖ) Y
      ≡ CTX.resolveVar (CTX.targetStoreʷ W) Y
  target-same =
    cong (λ Σ → CTX.resolveVar Σ Y)
      (CTX.SameRuntime.targetStore-same
        (CTX.RebaseAt.sameRuntime rb))

insertRebase-target-rev : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAt Wᵖ W Xᴸ Xᴿ
  → ∀ Y
  → toRenameᵗ
      (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ)) (toRenameᵗ ρ Y)
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ Wᵖ) Y)
insertRebase-target-rev {π = π} ins rb Y =
  trans (target-insert ins Y)
    (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴿ-frozen rb Y))

insertRebase-target-center-reflect-rev :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {W⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {Y′ Z}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ)) Y′
      ≡ toRenameᵗ π Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      toRenameᵗ (CTX.ηᴿʷ Wᵖ) Y ≡ Z
insertRebase-target-center-reflect-rev ins rb eq
    with target-center-reflect ins eq
insertRebase-target-center-reflect-rev ins rb eq
    | Y , y′-eq , target-eq =
  Y , y′-eq , trans (sym (CTX.RebaseAt.ηᴿ-frozen rb Y)) target-eq

insertRebase-target-source-reflect-rev :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {W⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᵖ : TyVar Δᴸ} {Yᵖ : TyVar Δᴿ} {Xᴸ Y′}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt Wᵖ W Xᵖ Yᵖ)
  → CTX.CenterAligned (insertRebaseWorld ins Wᵖ) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned Wᵖ Xᴸ Y
insertRebase-target-source-reflect-rev {π = π} {Wᵖ = Wᵖ}
    {Xᴸ = Xᴸ} {Y′ = Y′} ins rb aligned
    with insertRebase-target-center-reflect-rev ins rb target-image
  where
  target-image : toRenameᵗ
      (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ)) Y′
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴸʷ Wᵖ) Xᴸ)
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
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → (B : Ty Δᴿ)
  → CTX.embedᴿ (insertRebaseWorld ins Wᵖ)
      (renameᵗ (toRenameᵗ ρ) B)
      ≡ renameᵗ (toRenameᵗ π) (CTX.embedᴿ Wᵖ B)
insertRebase-target-embed-rev {ρ = ρ} {π = π} {Wᵖ = Wᵖ} ins rb B =
  trans
    (renameᵗ-comp (toRenameᵗ ρ)
      (toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ))) B)
    (trans (renameᵗ-cong B (insertRebase-target-rev ins rb))
      (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ Wᵖ))
        (toRenameᵗ π) B)))

insertRebase-targetStore-rename-rev :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {W⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → StoreRename (toRenameᵗ ρ) (CTX.targetStoreʷ Wᵖ)
      (CTX.targetStoreʷ (insertRebaseWorld ins Wᵖ))
insertRebase-targetStore-rename-rev {ρ = ρ} {W⁺ = W⁺} ins rb =
  subst≡
    (λ Σ → StoreRename (toRenameᵗ ρ) Σ (CTX.targetStoreʷ W⁺))
    (CTX.SameRuntime.targetStore-same
      (CTX.RebaseAt.sameRuntime rb))
    (targetStore-rename ins)

insertRebase-target-resolve-rev :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {W⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → ∀ Y
  → CTX.resolveVar
      (CTX.targetStoreʷ (insertRebaseWorld ins Wᵖ))
      (toRenameᵗ ρ Y)
      ≡ renameᵗ (toRenameᵗ ρ)
          (CTX.resolveVar (CTX.targetStoreʷ Wᵖ) Y)
insertRebase-target-resolve-rev {ρ = ρ} {W = W} {Wᵖ = Wᵖ}
    ins rb Y =
  trans (target-resolve ins Y)
    (cong (renameᵗ (toRenameᵗ ρ)) target-same)
  where
  target-same : CTX.resolveVar (CTX.targetStoreʷ W) Y
      ≡ CTX.resolveVar (CTX.targetStoreʷ Wᵖ) Y
  target-same =
    cong (λ Σ → CTX.resolveVar Σ Y)
      (CTX.SameRuntime.targetStore-same
        (CTX.RebaseAt.sameRuntime rb))

insertRebaseTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
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
      λ eq → renameEnv-off π (CTX.impEnvʷ Wᵖ) eq
  ; target-center-reflect = insertRebase-target-center-reflect ins rb
  ; target-source-reflect = insertRebase-target-source-reflect ins rb
  }

insertRebaseTargetInsertRev : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
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
      λ eq → renameEnv-off π (CTX.impEnvʷ Wᵖ) eq
  ; target-center-reflect = insertRebase-target-center-reflect-rev ins rb
  ; target-source-reflect = insertRebase-target-source-reflect-rev ins rb
  }

insertRebaseAt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAt W Wᵖ Xᴸ Xᴿ
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAt W⁺ Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
insertRebaseAt {ρ = ρ} {π = π} {Wᵖ = Wᵖ} {W⁺ = W⁺}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} ins rb =
  insertRebaseWorld ins Wᵖ , insᵖ ,
    CTX.rebase-at runtime off-left frozen-target aligned reps
  where
  insᵖ = insertRebaseTargetInsert ins rb

  runtime : CTX.SameRuntime W⁺ (insertRebaseWorld ins Wᵖ)
  runtime =
    CTX.same-runtime
      (trans
        (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime rb))
        (sym (sourceStore-kept ins)))
      refl

  off-left : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ
        (CTX.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Y
      ≡ toRenameᵗ (CTX.ηᴸʷ W⁺) Y
  off-left {Y} Y≢ =
    trans (insertRebase-source {Wᵖ = Wᵖ} ins Y)
      (trans
        (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴸ-off-pivot rb Y≢))
        (sym (source-insert ins Y)))

  frozen-target : ∀ Y
    → toRenameᵗ
        (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ)) Y
      ≡ toRenameᵗ (CTX.ηᴿʷ W⁺) Y
  frozen-target Y = refl

  aligned : toRenameᵗ
      (CTX.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Xᴸ
      ≡ toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ))
          (toRenameᵗ ρ Xᴿ)
  aligned =
    trans (insertRebase-source {Wᵖ = Wᵖ} ins Xᴸ)
      (trans (cong (toRenameᵗ π) (CTX.RebaseAt.pivotAligned rb))
        (trans (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴿ-frozen rb Xᴿ))
          (sym (target-insert ins Xᴿ))))

  reps : CTX.StoreRepImp (insertRebaseWorld ins Wᵖ)
      Xᴸ (toRenameᵗ ρ Xᴿ)
  reps =
    storeRep-insert insᵖ (CTX.RebaseAt.storeRepresentations rb)

reverseRebaseAt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAt Wᵖ W Xᴸ Xᴿ
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAt Wᵖ⁺ W⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
reverseRebaseAt {ρ = ρ} {π = π} {Wᵖ = Wᵖ} {W⁺ = W⁺}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} ins rb =
  insertRebaseWorld ins Wᵖ , insᵖ ,
    CTX.rebase-at runtime off-left frozen-target aligned reps
  where
  insᵖ = insertRebaseTargetInsertRev ins rb

  runtime : CTX.SameRuntime (insertRebaseWorld ins Wᵖ) W⁺
  runtime =
    CTX.same-runtime
      (trans (sourceStore-kept ins)
        (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime rb)))
      refl

  off-left : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ W⁺) Y
      ≡ toRenameᵗ
          (CTX.ηᴸʷ (insertRebaseWorld ins Wᵖ)) Y
  off-left {Y} Y≢ =
    trans (source-insert ins Y)
      (trans
        (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴸ-off-pivot rb Y≢))
        (sym (insertRebase-source {Wᵖ = Wᵖ} ins Y)))

  frozen-target : ∀ Y
    → toRenameᵗ (CTX.ηᴿʷ W⁺) Y
      ≡ toRenameᵗ
          (CTX.ηᴿʷ (insertRebaseWorld ins Wᵖ)) Y
  frozen-target Y = refl

  aligned : toRenameᵗ (CTX.ηᴸʷ W⁺) Xᴸ
      ≡ toRenameᵗ (CTX.ηᴿʷ W⁺) (toRenameᵗ ρ Xᴿ)
  aligned =
    trans (source-insert ins Xᴸ)
      (trans (cong (toRenameᵗ π) (CTX.RebaseAt.pivotAligned rb))
        (sym (target-insert ins Xᴿ)))

  reps : CTX.StoreRepImp W⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
  reps =
    storeRep-insert ins (CTX.RebaseAt.storeRepresentations rb)

pullbackRebase-target : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.RebaseAt W Wᵖ Xᴸ Xᴿ
  → ∀ Y
  → toRenameᵗ
      (CTX.ηᴿʷ (insertRebaseWorld insᵖ W)) (toRenameᵗ ρ Y)
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ W) Y)
pullbackRebase-target {π = π} insᵖ rb Y =
  trans (target-insert insᵖ Y)
    (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴿ-frozen rb Y))

pullbackRebase-target-center-reflect :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {Y′ Z}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld insᵖ W)) Y′
      ≡ toRenameᵗ π Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      toRenameᵗ (CTX.ηᴿʷ W) Y ≡ Z
pullbackRebase-target-center-reflect insᵖ rb eq
    with target-center-reflect insᵖ eq
pullbackRebase-target-center-reflect insᵖ rb eq
    | Y , y′-eq , target-eq =
  Y , y′-eq , trans (sym (CTX.RebaseAt.ηᴿ-frozen rb Y)) target-eq

pullbackRebase-target-source-reflect :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᵖᴸ : TyVar Δᴸ} {Xᵖᴿ : TyVar Δᴿ} {Xᴸ Y′}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᵖᴸ Xᵖᴿ)
  → CTX.CenterAligned (insertRebaseWorld insᵖ W) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned W Xᴸ Y
pullbackRebase-target-source-reflect {W = W} insᵖ rb aligned
    with target-center-reflect insᵖ target-image
  where
  target-image : toRenameᵗ
      (CTX.ηᴿʷ (insertRebaseWorld insᵖ W)) _
      ≡ toRenameᵗ _ (toRenameᵗ (CTX.ηᴸʷ W) _)
  target-image =
    trans (sym aligned) (insertRebase-source {Wᵖ = W} insᵖ _)
pullbackRebase-target-source-reflect insᵖ rb aligned
    | Y , y′-eq , target-eq =
  Y , y′-eq , trans (sym target-eq)
    (CTX.RebaseAt.ηᴿ-frozen rb Y)

pullbackRebaseTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.RebaseAt W Wᵖ Xᴸ Xᴿ
  → TargetInsert ρ π W (insertRebaseWorld insᵖ W)
pullbackRebaseTargetInsert {ρ = ρ} {π = π} {W = W} {Wᵖ⁺ = Wᵖ⁺}
    insᵖ rb = record
  { sourceStore-kept = refl
  ; transport⊑ᵂ = λ {A = A} {B = B} p →
      transport⊑ᵂ-from-geometry {ρ = ρ} {π = π} {W = W}
        {W′ = insertRebaseWorld insᵖ W} {A = A} {B = B}
        (insertRebase-source-embed {Wᵖ = W} insᵖ)
        (λ B → trans
          (renameᵗ-comp (toRenameᵗ ρ)
            (toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld insᵖ W))) B)
          (trans (renameᵗ-cong B (pullbackRebase-target insᵖ rb))
            (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ W))
              (toRenameᵗ π) B))))
        (λ Z eq → trans (insertRebase-impEnv {Wᵖ = W} insᵖ Z) eq)
        p
  ; targetStore-rename =
      subst≡
        (λ Σ → StoreRename (toRenameᵗ ρ) Σ
          (CTX.targetStoreʷ Wᵖ⁺))
        (CTX.SameRuntime.targetStore-same
          (CTX.RebaseAt.sameRuntime rb))
        (targetStore-rename insᵖ)
  ; source-resolve = λ X → refl
  ; target-resolve = λ Y →
      trans (target-resolve insᵖ Y)
        (cong (renameᵗ (toRenameᵗ ρ))
          (cong (λ Σ → CTX.resolveVar Σ Y)
            (CTX.SameRuntime.targetStore-same
              (CTX.RebaseAt.sameRuntime rb))))
  ; align-insert = λ {Xᴸ} {Xᴿ} aligned →
      trans (insertRebase-source {Wᵖ = W} insᵖ Xᴸ)
        (trans (cong (toRenameᵗ π) aligned)
          (sym (pullbackRebase-target insᵖ rb Xᴿ)))
  ; source-insert = λ X → insertRebase-source {Wᵖ = W} insᵖ X
  ; target-insert = λ Y → pullbackRebase-target insᵖ rb Y
  ; impEnv-insert = λ Z → insertRebase-impEnv {Wᵖ = W} insᵖ Z
  ; impEnv-off-insert =
      λ eq → renameEnv-off π (CTX.impEnvʷ W) eq
  ; target-center-reflect = pullbackRebase-target-center-reflect insᵖ rb
  ; target-source-reflect = pullbackRebase-target-source-reflect insᵖ rb
  }

pullbackRebaseAt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → CTX.RebaseAt (insertRebaseWorld insᵖ W) Wᵖ⁺
      Xᴸ (toRenameᵗ ρ Xᴿ)
pullbackRebaseAt {ρ = ρ} {π = π} {W = W} {Wᵖ = Wᵖ}
    {Wᵖ⁺ = Wᵖ⁺} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} insᵖ rb =
  CTX.rebase-at runtime off-left frozen-target aligned reps
  where
  runtime : CTX.SameRuntime (insertRebaseWorld insᵖ W) Wᵖ⁺
  runtime =
    CTX.same-runtime
      (trans (sourceStore-kept insᵖ)
        (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime rb)))
      refl

  off-left : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ Wᵖ⁺) Y
      ≡ toRenameᵗ (CTX.ηᴸʷ (insertRebaseWorld insᵖ W)) Y
  off-left {Y} Y≢ =
    trans (source-insert insᵖ Y)
      (trans
        (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴸ-off-pivot rb Y≢))
        (sym (insertRebase-source {Wᵖ = W} insᵖ Y)))

  frozen-target : ∀ Y
    → toRenameᵗ (CTX.ηᴿʷ Wᵖ⁺) Y
      ≡ toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld insᵖ W)) Y
  frozen-target Y = refl

  aligned : toRenameᵗ (CTX.ηᴸʷ Wᵖ⁺) Xᴸ
      ≡ toRenameᵗ (CTX.ηᴿʷ Wᵖ⁺) (toRenameᵗ ρ Xᴿ)
  aligned =
    trans (source-insert insᵖ Xᴸ)
      (trans (cong (toRenameᵗ π) (CTX.RebaseAt.pivotAligned rb))
        (sym (target-insert insᵖ Xᴿ)))

  reps : CTX.StoreRepImp Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)
  reps =
    storeRep-insert insᵖ (CTX.RebaseAt.storeRepresentations rb)

pullbackReverseRebase-target : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.RebaseAt Wᵖ W Xᴸ Xᴿ
  → ∀ Y
  → toRenameᵗ
      (CTX.ηᴿʷ (insertRebaseWorld insᵖ W)) (toRenameᵗ ρ Y)
      ≡ toRenameᵗ π (toRenameᵗ (CTX.ηᴿʷ W) Y)
pullbackReverseRebase-target {π = π} insᵖ rb Y =
  trans (target-insert insᵖ Y)
    (cong (toRenameᵗ π) (sym (CTX.RebaseAt.ηᴿ-frozen rb Y)))

pullbackReverseRebase-target-center-reflect :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {Y′ Z}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld insᵖ W)) Y′
      ≡ toRenameᵗ π Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y ×
      toRenameᵗ (CTX.ηᴿʷ W) Y ≡ Z
pullbackReverseRebase-target-center-reflect insᵖ rb eq
    with target-center-reflect insᵖ eq
pullbackReverseRebase-target-center-reflect insᵖ rb eq
    | Y , y′-eq , target-eq =
  Y , y′-eq , trans (CTX.RebaseAt.ηᴿ-frozen rb Y) target-eq

pullbackReverseRebase-target-source-reflect :
    ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
      {W Wᵖ : World Δᴸ Δᴿ Δ}
      {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
      {Xᵖᴸ : TyVar Δᴸ} {Xᵖᴿ : TyVar Δᴿ} {Xᴸ Y′}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → (rb : CTX.RebaseAt Wᵖ W Xᵖᴸ Xᵖᴿ)
  → CTX.CenterAligned (insertRebaseWorld insᵖ W) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ ρ Y × CTX.CenterAligned W Xᴸ Y
pullbackReverseRebase-target-source-reflect {W = W} insᵖ rb aligned
    with target-center-reflect insᵖ target-image
  where
  target-image : toRenameᵗ
      (CTX.ηᴿʷ (insertRebaseWorld insᵖ W)) _
      ≡ toRenameᵗ _ (toRenameᵗ (CTX.ηᴸʷ W) _)
  target-image =
    trans (sym aligned) (insertRebase-source {Wᵖ = W} insᵖ _)
pullbackReverseRebase-target-source-reflect insᵖ rb aligned
    | Y , y′-eq , target-eq =
  Y , y′-eq , trans (sym target-eq)
    (sym (CTX.RebaseAt.ηᴿ-frozen rb Y))

pullbackReverseRebaseTargetInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.RebaseAt Wᵖ W Xᴸ Xᴿ
  → TargetInsert ρ π W (insertRebaseWorld insᵖ W)
pullbackReverseRebaseTargetInsert
    {ρ = ρ} {π = π} {W = W} {Wᵖ⁺ = Wᵖ⁺} insᵖ rb =
  record
    { sourceStore-kept = refl
    ; transport⊑ᵂ = λ {A = A} {B = B} p →
        transport⊑ᵂ-from-geometry {ρ = ρ} {π = π} {W = W}
          {W′ = insertRebaseWorld insᵖ W} {A = A} {B = B}
          (insertRebase-source-embed {Wᵖ = W} insᵖ)
          (λ B → trans
            (renameᵗ-comp (toRenameᵗ ρ)
              (toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld insᵖ W))) B)
            (trans
              (renameᵗ-cong B
                (pullbackReverseRebase-target insᵖ rb))
              (sym (renameᵗ-comp (toRenameᵗ (CTX.ηᴿʷ W))
                (toRenameᵗ π) B))))
          (λ Z eq → trans (insertRebase-impEnv {Wᵖ = W} insᵖ Z) eq)
          p
    ; targetStore-rename =
        subst≡
          (λ Σ → StoreRename (toRenameᵗ ρ) Σ
            (CTX.targetStoreʷ Wᵖ⁺))
          (sym (CTX.SameRuntime.targetStore-same
            (CTX.RebaseAt.sameRuntime rb)))
          (targetStore-rename insᵖ)
    ; source-resolve = λ X → refl
    ; target-resolve = λ Y →
        trans (target-resolve insᵖ Y)
          (cong (renameᵗ (toRenameᵗ ρ))
            (cong (λ Σ → CTX.resolveVar Σ Y)
              (sym (CTX.SameRuntime.targetStore-same
                (CTX.RebaseAt.sameRuntime rb)))))
    ; align-insert = λ {Xᴸ} {Xᴿ} aligned →
        trans (insertRebase-source {Wᵖ = W} insᵖ Xᴸ)
          (trans (cong (toRenameᵗ π) aligned)
            (sym (pullbackReverseRebase-target insᵖ rb Xᴿ)))
    ; source-insert = λ X → insertRebase-source {Wᵖ = W} insᵖ X
    ; target-insert = λ Y → pullbackReverseRebase-target insᵖ rb Y
    ; impEnv-insert = λ Z → insertRebase-impEnv {Wᵖ = W} insᵖ Z
    ; impEnv-off-insert =
        λ eq → renameEnv-off π (CTX.impEnvʷ W) eq
    ; target-center-reflect =
        pullbackReverseRebase-target-center-reflect insᵖ rb
    ; target-source-reflect =
        pullbackReverseRebase-target-source-reflect insᵖ rb
    }

pullbackReverseRebaseAt : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → CTX.RebaseAt Wᵖ⁺ (insertRebaseWorld insᵖ W)
      Xᴸ (toRenameᵗ ρ Xᴿ)
pullbackReverseRebaseAt
    {ρ = ρ} {π = π} {W = W} {Wᵖ = Wᵖ} {Wᵖ⁺ = Wᵖ⁺}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} insᵖ rb =
  CTX.rebase-at runtime off-left frozen-target aligned reps
  where
  ins = pullbackReverseRebaseTargetInsert insᵖ rb

  runtime : CTX.SameRuntime Wᵖ⁺ (insertRebaseWorld insᵖ W)
  runtime =
    CTX.same-runtime
      (trans
        (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime rb))
        (sym (sourceStore-kept insᵖ)))
      refl

  off-left : ∀ {Y} → Y ≢ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ (insertRebaseWorld insᵖ W)) Y
      ≡ toRenameᵗ (CTX.ηᴸʷ Wᵖ⁺) Y
  off-left {Y} Y≢ =
    trans (insertRebase-source {Wᵖ = W} insᵖ Y)
      (trans
        (cong (toRenameᵗ π) (CTX.RebaseAt.ηᴸ-off-pivot rb Y≢))
        (sym (source-insert insᵖ Y)))

  frozen-target : ∀ Y
    → toRenameᵗ (CTX.ηᴿʷ (insertRebaseWorld insᵖ W)) Y
      ≡ toRenameᵗ (CTX.ηᴿʷ Wᵖ⁺) Y
  frozen-target Y = refl

  aligned : toRenameᵗ (CTX.ηᴸʷ (insertRebaseWorld insᵖ W)) Xᴸ
      ≡ toRenameᵗ
          (CTX.ηᴿʷ (insertRebaseWorld insᵖ W))
          (toRenameᵗ ρ Xᴿ)
  aligned =
    trans (insertRebase-source {Wᵖ = W} insᵖ Xᴸ)
      (trans (cong (toRenameᵗ π) (CTX.RebaseAt.pivotAligned rb))
        (sym (pullbackReverseRebase-target insᵖ rb Xᴿ)))

  reps : CTX.StoreRepImp (insertRebaseWorld insᵖ W)
      Xᴸ (toRenameᵗ ρ Xᴿ)
  reps =
    storeRep-insert ins (CTX.RebaseAt.storeRepresentations rb)

TargetExtendOPEᵀ : Set
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

RebaseAtᴿInsertCommuteᵀ : Set
RebaseAtᴿInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAtᴿ W Wᵖ Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAtᴿ W⁺ Wᵖ⁺
        (mapPivot (toRenameᵗ ρ) Xᴿ?)

RebaseAtᴸInsertCommuteᵀ : Set
RebaseAtᴸInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAtᴸ W Wᵖ Xᴸ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAtᴸ W⁺ Wᵖ⁺ Xᴸ?

TagRebaseAtᴸInsertCommuteᵀ : Set
TagRebaseAtᴸInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.TagRebaseAtᴸ W⁺ Wᵖ⁺ Xᴸ?
        (mapPivot (toRenameᵗ ρ) Xᴿ?)

RebaseAtInsertCommuteᵀ : Set
RebaseAtInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAt W Wᵖ Xᴸ Xᴿ
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAt W⁺ Wᵖ⁺ Xᴸ (toRenameᵗ ρ Xᴿ)

ImpEnvMonoInsertCommuteᵀ : Set
ImpEnvMonoInsertCommuteᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
  → TargetInsert ρ π W W⁺
  → TargetInsert ρ π Wᵖ Wᵖ⁺
  → CTX.ImpEnvMono W Wᵖ
  → CTX.ImpEnvMono W⁺ Wᵖ⁺

insert-to-starᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
  → CTX.impEnvʷ W⁺ (toRenameᵗ (CTX.ηᴸʷ W⁺) Xᴸ) ≡ X⊑★
insert-to-starᴸ {W = W} {W⁺ = W⁺} {Xᴸ = Xᴸ} ins to-star =
  trans (cong (CTX.impEnvʷ W⁺) (source-insert ins Xᴸ))
    (trans (impEnv-insert ins (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ))
      to-star)

insert-disalignedᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ : TyVar Δᴸ}
  → (ins : TargetInsert ρ π W W⁺)
  → (∀ Xᴿ → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
      ≢ toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ′ → toRenameᵗ (CTX.ηᴿʷ W⁺) Xᴿ′
      ≢ toRenameᵗ (CTX.ηᴸʷ W⁺) Xᴸ
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
  → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ ⊑ᵂ⟨ W ⟩ ★
  → CTX.resolveVar (CTX.sourceStoreʷ W⁺) Xᴸ ⊑ᵂ⟨ W⁺ ⟩ ★
insert-represented★ᴸ {W⁺ = W⁺} {Xᴸ = Xᴸ} ins represented =
  subst≡ (λ A → A ⊑ᵂ⟨ W⁺ ⟩ ★)
    (sym (source-resolve ins Xᴸ))
    (transport⊑ᵂ ins represented)

insertRebaseAtᴿ : RebaseAtᴿInsertCommuteᵀ
insertRebaseAtᴿ ins CTX.rebase-idᴿ =
  _ , ins , CTX.rebase-idᴿ
insertRebaseAtᴿ ins (CTX.rebase-varᴿ rb)
    with insertRebaseAt ins rb
insertRebaseAtᴿ ins (CTX.rebase-varᴿ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTX.rebase-varᴿ rb⁺

insertRebaseAtᴸ : RebaseAtᴸInsertCommuteᵀ
insertRebaseAtᴸ ins CTX.rebase-idᴸ =
  _ , ins , CTX.rebase-idᴸ
insertRebaseAtᴸ ins (CTX.rebase-varᴸ rb)
    with insertRebaseAt ins rb
insertRebaseAtᴸ ins (CTX.rebase-varᴸ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTX.rebase-varᴸ rb⁺
insertRebaseAtᴸ {W⁺ = W⁺} ins
    (CTX.rebase-onlyᴸ {Xᴸ = Xᴸ}
      to-star disaligned represented) =
  W⁺ , ins ,
    CTX.rebase-onlyᴸ
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (insert-represented★ᴸ ins represented)

insertTagRebaseAtᴸ : TagRebaseAtᴸInsertCommuteᵀ
insertTagRebaseAtᴸ ins CTX.tag-rebase-idᴸ =
  _ , ins , CTX.tag-rebase-idᴸ
insertTagRebaseAtᴸ ins (CTX.tag-rebase-varᴸ rb)
    with insertRebaseAt ins rb
insertTagRebaseAtᴸ ins (CTX.tag-rebase-varᴸ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTX.tag-rebase-varᴸ rb⁺
insertTagRebaseAtᴸ {W⁺ = W⁺} ins
    (CTX.tag-rebase-onlyᴸ {Xᴸ = Xᴸ}
      to-star disaligned represented) =
  W⁺ , ins ,
    CTX.tag-rebase-onlyᴸ
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (insert-represented★ᴸ ins represented)

pullbackRebaseAtᴸInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.RebaseAtᴸ W Wᵖ Xᴸ?
  → Σ[ W⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π W W⁺ ×
      CTX.RebaseAtᴸ W⁺ Wᵖ⁺ Xᴸ?
pullbackRebaseAtᴸInsert insᵖ CTX.rebase-idᴸ =
  _ , insᵖ , CTX.rebase-idᴸ
pullbackRebaseAtᴸInsert {W = W} insᵖ (CTX.rebase-varᴸ rb) =
  insertRebaseWorld insᵖ W ,
  pullbackRebaseTargetInsert insᵖ rb ,
  CTX.rebase-varᴸ (pullbackRebaseAt insᵖ rb)
pullbackRebaseAtᴸInsert {Wᵖ⁺ = Wᵖ⁺} insᵖ
    (CTX.rebase-onlyᴸ {Xᴸ = Xᴸ}
      to-star disaligned represented) =
  Wᵖ⁺ , insᵖ ,
    CTX.rebase-onlyᴸ
      (insert-to-starᴸ insᵖ to-star)
      (insert-disalignedᴸ insᵖ disaligned)
      (insert-represented★ᴸ insᵖ represented)

pullbackTagRebaseAtᴸInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
  → Σ[ W⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π W W⁺ ×
      CTX.TagRebaseAtᴸ Wᵖ⁺ W⁺ Xᴸ?
        (mapPivot (toRenameᵗ ρ) Xᴿ?)
pullbackTagRebaseAtᴸInsert insᵖ CTX.tag-rebase-idᴸ =
  _ , insᵖ , CTX.tag-rebase-idᴸ
pullbackTagRebaseAtᴸInsert {W = W} insᵖ (CTX.tag-rebase-varᴸ rb) =
  insertRebaseWorld insᵖ W ,
  pullbackReverseRebaseTargetInsert insᵖ rb ,
  CTX.tag-rebase-varᴸ (pullbackReverseRebaseAt insᵖ rb)
pullbackTagRebaseAtᴸInsert {Wᵖ⁺ = Wᵖ⁺} insᵖ
    (CTX.tag-rebase-onlyᴸ {Xᴸ = Xᴸ}
      to-star disaligned represented) =
  Wᵖ⁺ , insᵖ ,
    CTX.tag-rebase-onlyᴸ
      (insert-to-starᴸ insᵖ to-star)
      (insert-disalignedᴸ insᵖ disaligned)
      (insert-represented★ᴸ insᵖ represented)

reverseRebaseAtᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAtᴿ Wᵖ W Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAtᴿ Wᵖ⁺ W⁺ (mapPivot (toRenameᵗ ρ) Xᴿ?)
reverseRebaseAtᴿ ins CTX.rebase-idᴿ =
  _ , ins , CTX.rebase-idᴿ
reverseRebaseAtᴿ ins (CTX.rebase-varᴿ rb)
    with reverseRebaseAt ins rb
reverseRebaseAtᴿ ins (CTX.rebase-varᴿ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTX.rebase-varᴿ rb⁺

reverseRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.RebaseAtᴸ Wᵖ W Xᴸ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.RebaseAtᴸ Wᵖ⁺ W⁺ Xᴸ?
reverseRebaseAtᴸ ins CTX.rebase-idᴸ =
  _ , ins , CTX.rebase-idᴸ
reverseRebaseAtᴸ ins (CTX.rebase-varᴸ rb)
    with reverseRebaseAt ins rb
reverseRebaseAtᴸ ins (CTX.rebase-varᴸ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTX.rebase-varᴸ rb⁺
reverseRebaseAtᴸ {W⁺ = W⁺} ins
    (CTX.rebase-onlyᴸ {Xᴸ = Xᴸ}
      to-star disaligned represented) =
  W⁺ , ins ,
    CTX.rebase-onlyᴸ
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (insert-represented★ᴸ ins represented)

reverseTagRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ : World Δᴸ Δᴿ′ Δ′}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
  → (ins : TargetInsert ρ π W W⁺)
  → CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ Δᴿ′ Δ′ ]
      TargetInsert ρ π Wᵖ Wᵖ⁺ ×
      CTX.TagRebaseAtᴸ Wᵖ⁺ W⁺ Xᴸ?
        (mapPivot (toRenameᵗ ρ) Xᴿ?)
reverseTagRebaseAtᴸ ins CTX.tag-rebase-idᴸ =
  _ , ins , CTX.tag-rebase-idᴸ
reverseTagRebaseAtᴸ ins (CTX.tag-rebase-varᴸ rb)
    with reverseRebaseAt ins rb
reverseTagRebaseAtᴸ ins (CTX.tag-rebase-varᴸ rb)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  Wᵖ⁺ , insᵖ , CTX.tag-rebase-varᴸ rb⁺
reverseTagRebaseAtᴸ {W⁺ = W⁺} ins
    (CTX.tag-rebase-onlyᴸ {Xᴸ = Xᴸ}
      to-star disaligned represented) =
  W⁺ , ins ,
    CTX.tag-rebase-onlyᴸ
      (insert-to-starᴸ ins to-star)
      (insert-disalignedᴸ ins disaligned)
      (insert-represented★ᴸ ins represented)

impEnvMono-insert-pre : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {W⁺ Wᵖ⁺ : World Δᴸ Δᴿ′ Δ′}
  → (ins : TargetInsert ρ π W W⁺)
  → (insᵖ : TargetInsert ρ π Wᵖ Wᵖ⁺)
  → CTX.ImpEnvMono W Wᵖ
  → (Z′ : TyVar Δ′)
  → CTX.impEnvʷ W⁺ Z′ ≡ X⊑★
  → (m : Maybe (TyVar Δ))
  → preimage? π Z′ ≡ m
  → CTX.impEnvʷ Wᵖ⁺ Z′ ≡ X⊑★
impEnvMono-insert-pre {π = π} {W = W} {W⁺ = W⁺} {Wᵖ⁺ = Wᵖ⁺}
    ins insᵖ mono Z′ star (just Z) pre =
  trans (cong (CTX.impEnvʷ Wᵖ⁺) image-eq)
    (trans (impEnv-insert insᵖ Z) (mono Z old-star))
  where
  image-eq : Z′ ≡ toRenameᵗ π Z
  image-eq = preimage?-sound π pre

  image-star : CTX.impEnvʷ W⁺ (toRenameᵗ π Z) ≡ X⊑★
  image-star =
    trans (sym (cong (CTX.impEnvʷ W⁺) image-eq)) star

  old-star : CTX.impEnvʷ W Z ≡ X⊑★
  old-star =
    trans (sym (impEnv-insert ins Z)) image-star
impEnvMono-insert-pre ins insᵖ mono Z′ star nothing pre =
  impEnv-off-insert insᵖ pre

impEnvMono-insert : ImpEnvMonoInsertCommuteᵀ
impEnvMono-insert {π = π} ins insᵖ mono Z′ star =
  impEnvMono-insert-pre ins insᵖ mono Z′ star (preimage? π Z′) refl

renamePivotJoin : ∀ {Δ Δ′} {p q r : Maybe (TyVar Δ)}
  → (ρ : TyVar Δ → TyVar Δ′)
  → Conv.PivotJoin p q r
  → Conv.PivotJoin (mapPivot ρ p) (mapPivot ρ q) (mapPivot ρ r)
renamePivotJoin ρ Conv.join-none = Conv.join-none
renamePivotJoin ρ Conv.join-left = Conv.join-left
renamePivotJoin ρ Conv.join-right = Conv.join-right
renamePivotJoin ρ Conv.join-both = Conv.join-both

mutual
  reveal-renameˣ : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
      {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {X? A B}
      {c : Conversion.Conv↑ Δ A B}
    → StoreRename ρ Σ Σ′
    → Σ Conv.⊢↑[ X? ] c
    → Σ′ Conv.⊢↑[ mapPivot ρ X? ] rename↑ ρ c
  reveal-renameˣ hΣ (Conv.⊢↑-unsealˣ X∈) =
    Conv.⊢↑-unsealˣ (hΣ X∈)
  reveal-renameˣ hΣ (Conv.⊢↑-⇒ˣ join c⊢ d⊢) =
    Conv.⊢↑-⇒ˣ (renamePivotJoin _ join)
      (conceal-renameˣ hΣ c⊢) (reveal-renameˣ hΣ d⊢)
  reveal-renameˣ {ρ = ρ} hΣ (Conv.⊢↑-∀ˣ c⊢) =
    Conv.⊢↑-∀ˣ (reveal-renameˣ (StoreRename-ext hΣ) c⊢)
  reveal-renameˣ {ρ = ρ} hΣ (Conv.⊢↑-∀-idˣ c⊢) =
    Conv.⊢↑-∀-idˣ (reveal-renameˣ (StoreRename-ext hΣ) c⊢)
  reveal-renameˣ hΣ Conv.⊢↑-idˣ = Conv.⊢↑-idˣ

  conceal-renameˣ : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
      {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {X? A B}
      {c : Conversion.Conv↓ Δ A B}
    → StoreRename ρ Σ Σ′
    → Σ Conv.⊢↓[ X? ] c
    → Σ′ Conv.⊢↓[ mapPivot ρ X? ] rename↓ ρ c
  conceal-renameˣ hΣ (Conv.⊢↓-sealˣ X∈) =
    Conv.⊢↓-sealˣ (hΣ X∈)
  conceal-renameˣ hΣ (Conv.⊢↓-⇒ˣ join c⊢ d⊢) =
    Conv.⊢↓-⇒ˣ (renamePivotJoin _ join)
      (reveal-renameˣ hΣ c⊢) (conceal-renameˣ hΣ d⊢)
  conceal-renameˣ {ρ = ρ} hΣ (Conv.⊢↓-∀ˣ c⊢) =
    Conv.⊢↓-∀ˣ (conceal-renameˣ (StoreRename-ext hΣ) c⊢)
  conceal-renameˣ {ρ = ρ} hΣ (Conv.⊢↓-∀-idˣ c⊢) =
    Conv.⊢↓-∀-idˣ (conceal-renameˣ (StoreRename-ext hΣ) c⊢)
  conceal-renameˣ hΣ Conv.⊢↓-idˣ = Conv.⊢↓-idˣ

------------------------------------------------------------------------
-- Target-term syntactic side conditions
------------------------------------------------------------------------

notTopTag-rename : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) {M : Term Δ}
  → CTX.NotTopTag M
  → CTX.NotTopTag (renameᵗᵐ ρ M)
notTopTag-rename ρ (CTX.not-` x) = CTX.not-` x
notTopTag-rename ρ CTX.not-ƛ = CTX.not-ƛ
notTopTag-rename ρ CTX.not-· = CTX.not-·
notTopTag-rename ρ CTX.not-Λ = CTX.not-Λ
notTopTag-rename ρ CTX.not-⦂∀ = CTX.not-⦂∀
notTopTag-rename ρ (CTX.not-$ κ) = CTX.not-$ κ
notTopTag-rename ρ (CTX.not-⊕ op) = CTX.not-⊕ op
notTopTag-rename ρ CTX.not-↑ = CTX.not-↑
notTopTag-rename ρ CTX.not-↓ = CTX.not-↓
notTopTag-rename ρ CTX.not-blame = CTX.not-blame

renameRep★PartnerOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {X : TyVar Δᴸ} {P Xᴿ? M′}
  → (∀ {X₀ Y₀}
      → CTX.CenterAligned W X₀ Y₀
      → CTX.CenterAligned W′ X₀ (toRenameᵗ ρ Y₀))
  → CTX.Rep★PartnerOK W X P Xᴿ? M′
  → CTX.Rep★PartnerOK W′ X P
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameRep★PartnerOK align (CTX.rep★-untagged nt) =
  CTX.rep★-untagged (notTopTag-rename _ nt)
renameRep★PartnerOK align (CTX.rep★-nonvar-tag Gnv) =
  CTX.rep★-nonvar-tag (renameNonVar _ Gnv)
renameRep★PartnerOK align (CTX.rep★-var-tag aligned) =
  CTX.rep★-var-tag (align aligned)
renameRep★PartnerOK align
    (CTX.rep★-matched-inner-tags X₂≢X aligned) =
  CTX.rep★-matched-inner-tags X₂≢X (align aligned)
renameRep★PartnerOK align (CTX.rep★-round-trip ok) =
  CTX.rep★-round-trip (renameRep★PartnerOK align ok)

targetInsertNoTargetAtSource : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ}
  → (ins : TargetInsert ρ π W W′)
  → CTX.NoTargetOccupantAtSource W X
  → CTX.NoTargetOccupantAtSource W′ X
targetInsertNoTargetAtSource {X = X} ins no-target (Y′ , eq)
    with target-center-reflect ins (trans eq (source-insert ins X))
targetInsertNoTargetAtSource {X = X} ins no-target (Y′ , eq)
    | Y , _ , target-eq =
  no-target (Y , target-eq)

renameSourceConcealOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
    {π : Δ ↪ᵗ Δ′}
  → TargetInsert ρ π W W′
  → CTX.SourceConcealOK W M c Xᴿ? M′
  → CTX.SourceConcealOK W′ M c
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameSourceConcealOK ins
    (CTX.seal-nonstar-unmatched-ok Rns no-target) =
  CTX.seal-nonstar-unmatched-ok Rns
    (targetInsertNoTargetAtSource ins no-target)
renameSourceConcealOK ins
    (CTX.seal-nonstar-name-protected-ok Rns aligned) =
  CTX.seal-nonstar-name-protected-ok Rns (align-insert ins aligned)
renameSourceConcealOK ins CTX.fun-conceal-ok =
  CTX.fun-conceal-ok
renameSourceConcealOK ins CTX.all-conceal-ok =
  CTX.all-conceal-ok
renameSourceConcealOK ins CTX.id-conceal-ok =
  CTX.id-conceal-ok

renameMatchedConcealPartnerOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → (∀ {X₀ Y₀}
      → CTX.CenterAligned W X₀ Y₀
      → CTX.CenterAligned W′ X₀ (toRenameᵗ ρ Y₀))
  → CTX.MatchedConcealPartnerOK W M c Xᴿ? M′
  → CTX.MatchedConcealPartnerOK W′ M c
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameMatchedConcealPartnerOK align
    (CTX.matched-seal-star-partner ok) =
  CTX.matched-seal-star-partner (renameRep★PartnerOK align ok)
renameMatchedConcealPartnerOK align
    (CTX.matched-seal-nonstar Rns) =
  CTX.matched-seal-nonstar Rns
renameMatchedConcealPartnerOK align CTX.matched-fun-conceal-target =
  CTX.matched-fun-conceal-target
renameMatchedConcealPartnerOK align CTX.matched-all-conceal-target =
  CTX.matched-all-conceal-target
renameMatchedConcealPartnerOK align CTX.matched-id-conceal-target =
  CTX.matched-id-conceal-target

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
  → A ⊑ᵂ⟨ CTX.rightOnlyWorld W B′ ⟩
      renameᵗ (toRenameᵗ wk↪ᵗ) B
right-bind-transport⊑ᵂᵀ {W = W} {B′ = B′} {A = A} {B = B} p =
  subst≡ (λ C → A ⊑ᵂ⟨ CTX.rightOnlyWorld W B′ ⟩ C)
    (sym (renameᵗ-wk-eq B))
    (right-bind-⊑ᵂ {W = W} {B′ = B′} p)

right-bind-align : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → CTX.CenterAligned W Xᴸ Xᴿ
  → CTX.CenterAligned (CTX.rightOnlyWorld W B)
      Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
right-bind-align {W = W} {Xᴿ = Xᴿ} aligned =
  trans (cong Fin.suc aligned)
    (sym (right-target-map (CTX.ηᴿʷ W) Xᴿ))

right-bind-source-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ∀ Xᴸ
  → toRenameᵗ (CTX.ηᴸʷ (CTX.rightOnlyWorld W B)) Xᴸ
      ≡ toRenameᵗ wk↪ᵗ (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
right-bind-source-insert {W = W} Xᴸ =
  sym (toRename-wk-eq (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ))

right-bind-target-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ∀ Xᴿ
  → toRenameᵗ (CTX.ηᴿʷ (CTX.rightOnlyWorld W B))
      (toRenameᵗ wk↪ᵗ Xᴿ)
      ≡ toRenameᵗ wk↪ᵗ (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)
right-bind-target-insert {W = W} Xᴿ =
  trans (right-target-map (CTX.ηᴿʷ W) Xᴿ)
    (sym (toRename-wk-eq (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ)))

right-bind-impEnv-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ∀ Z
  → CTX.impEnvʷ (CTX.rightOnlyWorld W B) (toRenameᵗ wk↪ᵗ Z)
      ≡ CTX.impEnvʷ W Z
right-bind-impEnv-insert Z
    rewrite toRename-wk-eq Z | toRename-id-eq Z =
  refl

right-bind-impEnv-off-insert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Z′ : TyVar (Nat.suc Δ)}
  → preimage? wk↪ᵗ Z′ ≡ nothing
  → CTX.impEnvʷ (CTX.rightOnlyWorld W B) Z′ ≡ X⊑★
right-bind-impEnv-off-insert {Z′ = Fin.zero} eq = refl
right-bind-impEnv-off-insert {Z′ = Fin.suc Z′} eq
    rewrite preimage-id↪ Z′ =
  ⊥-elim (just≢nothing eq)

right-bind-target-center-reflect : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Y′ Z}
  → toRenameᵗ (CTX.ηᴿʷ (CTX.rightOnlyWorld W B)) Y′
      ≡ toRenameᵗ wk↪ᵗ Z
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ wk↪ᵗ Y ×
      toRenameᵗ (CTX.ηᴿʷ W) Y ≡ Z
right-bind-target-center-reflect {Y′ = Fin.zero} {Z = Z} eq =
  ⊥-elim (zero≢suc (trans eq (toRename-wk-eq Z)))
right-bind-target-center-reflect {Y′ = Fin.suc Y} {Z = Z} eq =
  Y , sym (toRename-wk-eq Y) ,
    fin-suc-injective (trans eq (toRename-wk-eq Z))

right-bind-target-source-reflect : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Y′}
  → CTX.CenterAligned (CTX.rightOnlyWorld W B) Xᴸ Y′
  → Σ[ Y ∈ TyVar Δᴿ ]
      Y′ ≡ toRenameᵗ wk↪ᵗ Y × CTX.CenterAligned W Xᴸ Y
right-bind-target-source-reflect {Y′ = Fin.zero} ()
right-bind-target-source-reflect {Y′ = Fin.suc Y} aligned =
  Y , sym (toRename-wk-eq Y) , fin-suc-injective aligned

right-resolveVar-map : ∀ {Δ} (Σ : TyStore Δ) (B : Ty Δ)
  → ∀ Y
  → CTX.resolveVar (TyStore.store-bind Σ B) (toRenameᵗ wk↪ᵗ Y)
      ≡ ⇑ᵗ (CTX.resolveVar Σ Y)
right-resolveVar-map Σ B Y =
  cong (CTX.resolveVar (TyStore.store-bind Σ B)) (toRename-wk-eq Y)

right-bind-source-resolve : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ∀ Xᴸ
  → CTX.resolveVar
      (CTX.sourceStoreʷ (CTX.rightOnlyWorld W B)) Xᴸ
      ≡ CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ
right-bind-source-resolve Xᴸ = refl

right-bind-target-resolve : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ∀ Xᴿ
  → CTX.resolveVar
      (CTX.targetStoreʷ (CTX.rightOnlyWorld W B))
      (toRenameᵗ wk↪ᵗ Xᴿ)
      ≡ renameᵗ (toRenameᵗ wk↪ᵗ)
          (CTX.resolveVar (CTX.targetStoreʷ W) Xᴿ)
right-bind-target-resolve {W = W} {B = B} Xᴿ =
  trans (right-resolveVar-map (CTX.targetStoreʷ W) B Xᴿ)
    (sym (renameᵗ-wk-eq (CTX.resolveVar (CTX.targetStoreʷ W) Xᴿ)))

rightBindTargetInsert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → TargetInsert wk↪ᵗ wk↪ᵗ W (CTX.rightOnlyWorld W B)
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

rightBindTargetWindowInsert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → TargetWindowInsert (rightBindTargetInsert {W = W} {B = B}) id↪ᵗ
rightBindTargetWindowInsert = record
  { windowEmbedding = window-here
  ; window-zero = refl
  ; window-old = λ Z → refl
  }

smartFreshRightBindTargetWindowInsert : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : World Δᴸ Δᴿ Δ}
    {Wᵐ : World (Nat.suc Δᴸ) Δᴿ Δᵐ}
    {B : Ty Δᴿ}
  → (guard : CTX.SmartFreshBehindGuard W Wᵐ)
  → TargetWindowInsert
      (smartFreshTargetInsert
        (rightBindTargetInsert {W = W} {B = B}) guard)
      (rightPushoutWindow
        (CTX.SmartFreshBehindGuard.oldCenters guard))
smartFreshRightBindTargetWindowInsert guard =
  record
    { windowEmbedding = window-here
    ; window-zero = refl
    ; window-old = λ Z → refl
    }

keepRightBindTargetInsert : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {v : VarImp}
  → TargetInsert (keep wk↪ᵗ) (keep wk↪ᵗ)
      (CTX.liftWorldBoth v W)
      (CTX.liftWorldBoth v (CTX.rightOnlyWorld W B))
keepRightBindTargetInsert {W = W} {B = B} {v = v} =
  liftBothTargetInsert {v = v} (rightBindTargetInsert {W = W} {B = B})

right-storeRep : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → CTX.StoreRepImp (CTX.rightOnlyWorld W B)
      Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
right-storeRep {W = W} {B = B} {Xᴿ = Xᴿ}
    (CTX.store-rep-imp represented) =
  CTX.store-rep-imp
    (subst≡
      (λ R → CTX.resolveVar (CTX.sourceStoreʷ W) _
        ⊑ᵂ⟨ CTX.rightOnlyWorld W B ⟩ R)
      (sym (right-resolveVar-map (CTX.targetStoreʷ W) B Xᴿ))
      (right-bind-⊑ᵂ {W = W} {B′ = B} represented))

rightRebaseAt : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → CTX.RebaseAt W W′ Xᴸ Xᴿ
  → CTX.RebaseAt (CTX.rightOnlyWorld W B)
      (CTX.rightOnlyWorld W′ B) Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
rightRebaseAt {W = W} {W′ = W′} {B = B} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    (CTX.rebase-at
      (CTX.same-runtime source-eq target-eq)
      offL frozenR aligned reps) =
  CTX.rebase-at
    (CTX.same-runtime source-eq
      (cong (λ Σ → TyStore.store-bind Σ B) target-eq))
    (λ Y≢ → cong Fin.suc (offL Y≢))
    frozenR′
    (trans (cong Fin.suc aligned)
      (sym (right-target-map (CTX.ηᴿʷ W′) Xᴿ)))
    (right-storeRep reps)
  where
  frozenR′ : ∀ Y
    → toRenameᵗ (CTX.ηᴿʷ (CTX.rightOnlyWorld W′ B)) Y
      ≡ toRenameᵗ (CTX.ηᴿʷ (CTX.rightOnlyWorld W B)) Y
  frozenR′ Fin.zero = refl
  frozenR′ (Fin.suc Y) = cong Fin.suc (frozenR Y)

right-disaligned : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) {B : Ty Δᴿ} {Xᴸ : TyVar Δᴸ}
  → (∀ Xᴿ → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
      ≢ toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ → toRenameᵗ
      (CTX.ηᴿʷ (CTX.rightOnlyWorld W B)) Xᴿ
        ≢ toRenameᵗ
          (CTX.ηᴸʷ (CTX.rightOnlyWorld W B)) Xᴸ
right-disaligned W disaligned Fin.zero ()
right-disaligned W disaligned (Fin.suc Xᴿ) eq =
  disaligned Xᴿ (fin-suc-injective eq)

rightRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ?}
  → CTX.RebaseAtᴸ W W′ Xᴸ?
  → CTX.RebaseAtᴸ (CTX.rightOnlyWorld W B)
      (CTX.rightOnlyWorld W′ B) Xᴸ?
rightRebaseAtᴸ CTX.rebase-idᴸ = CTX.rebase-idᴸ
rightRebaseAtᴸ (CTX.rebase-varᴸ rb) =
  CTX.rebase-varᴸ (rightRebaseAt rb)
rightRebaseAtᴸ {W = W} {B = B}
    (CTX.rebase-onlyᴸ to-star disaligned represented) =
  CTX.rebase-onlyᴸ to-star (right-disaligned W {B = B} disaligned)
    (right-bind-⊑ᵂ {W = W} {B′ = B} represented)

rightTagRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
  → CTX.TagRebaseAtᴸ W W′ Xᴸ? Xᴿ?
  → CTX.TagRebaseAtᴸ (CTX.rightOnlyWorld W B)
      (CTX.rightOnlyWorld W′ B) Xᴸ?
      (mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
rightTagRebaseAtᴸ CTX.tag-rebase-idᴸ = CTX.tag-rebase-idᴸ
rightTagRebaseAtᴸ (CTX.tag-rebase-varᴸ rb) =
  CTX.tag-rebase-varᴸ (rightRebaseAt rb)
rightTagRebaseAtᴸ {W = W} {B = B}
    (CTX.tag-rebase-onlyᴸ to-star disaligned represented) =
  CTX.tag-rebase-onlyᴸ to-star
    (right-disaligned W {B = B} disaligned)
    (right-bind-⊑ᵂ {W = W} {B′ = B} represented)

rightRebaseAtᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴿ?}
  → CTX.RebaseAtᴿ W W′ Xᴿ?
  → CTX.RebaseAtᴿ (CTX.rightOnlyWorld W B)
      (CTX.rightOnlyWorld W′ B)
      (mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
rightRebaseAtᴿ CTX.rebase-idᴿ = CTX.rebase-idᴿ
rightRebaseAtᴿ (CTX.rebase-varᴿ rb) =
  CTX.rebase-varᴿ (rightRebaseAt rb)

rightRebaseAtInsert : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → CTX.RebaseAt W Wᵖ Xᴸ Xᴿ
  → Σ[ Wᵖ⁺ ∈ World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ) ]
      TargetInsert wk↪ᵗ wk↪ᵗ Wᵖ Wᵖ⁺ ×
      CTX.RebaseAt (CTX.rightOnlyWorld W B) Wᵖ⁺
        Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
rightRebaseAtInsert {Wᵖ = Wᵖ} {B = B} rb =
  CTX.rightOnlyWorld Wᵖ B , rightBindTargetInsert , rightRebaseAt rb

rightRebaseAtᴸInsert : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ?}
  → CTX.RebaseAtᴸ W Wᵖ Xᴸ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ) ]
      TargetInsert wk↪ᵗ wk↪ᵗ Wᵖ Wᵖ⁺ ×
      CTX.RebaseAtᴸ (CTX.rightOnlyWorld W B) Wᵖ⁺ Xᴸ?
rightRebaseAtᴸInsert {Wᵖ = Wᵖ} {B = B} rb =
  CTX.rightOnlyWorld Wᵖ B , rightBindTargetInsert , rightRebaseAtᴸ rb

rightTagRebaseAtᴸInsert : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
  → CTX.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ) ]
      TargetInsert wk↪ᵗ wk↪ᵗ Wᵖ Wᵖ⁺ ×
      CTX.TagRebaseAtᴸ (CTX.rightOnlyWorld W B) Wᵖ⁺ Xᴸ?
        (mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
rightTagRebaseAtᴸInsert {Wᵖ = Wᵖ} {B = B} rb =
  CTX.rightOnlyWorld Wᵖ B , rightBindTargetInsert ,
    rightTagRebaseAtᴸ rb

rightRebaseAtᴿInsert : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴿ?}
  → CTX.RebaseAtᴿ W Wᵖ Xᴿ?
  → Σ[ Wᵖ⁺ ∈ World Δᴸ (Nat.suc Δᴿ) (Nat.suc Δ) ]
      TargetInsert wk↪ᵗ wk↪ᵗ Wᵖ Wᵖ⁺ ×
      CTX.RebaseAtᴿ (CTX.rightOnlyWorld W B) Wᵖ⁺
        (mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
rightRebaseAtᴿInsert {Wᵖ = Wᵖ} {B = B} rb =
  CTX.rightOnlyWorld Wᵖ B , rightBindTargetInsert , rightRebaseAtᴿ rb

------------------------------------------------------------------------
-- Retargeting derivations
------------------------------------------------------------------------

mapCtxᴿ-∋ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : Reduction.StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {x A B}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → γ CTX.∋ʷ x ⦂ CTX.ctx-imp A B p
  → ECR.mapCtxᴿ ext γ CTX.∋ʷ x ⦂
      CTX.ctx-imp A (χs Reduction.▶ᵗ B) (ECR.transport⊑ᵂ ext p)
mapCtxᴿ-∋ ext CTX.Zʷ = CTX.Zʷ
mapCtxᴿ-∋ ext (CTX.Sʷ x∈) = CTX.Sʷ (mapCtxᴿ-∋ ext x∈)

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
  → CTX.sourceStoreʷ W Conv.⊢↑[ X? ] c
  → CTX.sourceStoreʷ W′ Conv.⊢↑[ X? ] c
source-reveal-insert ins c⊢ =
  subst≡ (λ Σ → Σ Conv.⊢↑[ _ ] _) (sym (sourceStore-kept ins)) c⊢

source-conceal-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴸ)} {A B : Ty Δᴸ}
    {c : Conv↓ Δᴸ A B}
  → (ins : TargetInsert ρ π W W′)
  → CTX.sourceStoreʷ W Conv.⊢↓[ X? ] c
  → CTX.sourceStoreʷ W′ Conv.⊢↓[ X? ] c
source-conceal-insert ins c⊢ =
  subst≡ (λ Σ → Σ Conv.⊢↓[ _ ] _) (sym (sourceStore-kept ins)) c⊢

target-typing-insert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {M : Term Δᴿ} {B : Ty Δᴿ}
  → (ins : TargetInsert ρ π W W′)
  → ⟨ Δᴿ , CTX.targetStoreʷ W , CTX.tgtCtxʷ γ ⟩ ⊢ M ⦂ B
  → ⟨ Δᴿ′ , CTX.targetStoreʷ W′ ,
        CTX.tgtCtxʷ (mapCtxᵀ ins γ) ⟩
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
⊢²-target-insert {W = W} {γ = γ} ins
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} {p = p}
      Anv zero∈A (CTX.smart-merge-alias guard) liftγ vV M′⊢
      V⊑M′ q) =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTX.smart-merge-alias (smartAliasGuardInsert ins guard))
    (targetSmartLiftCtxLeft ins (smartAliasTargetInsert ins guard) liftγ)
    vV (target-typing-insert ins M′⊢)
    (⊢²-target-insert (smartAliasTargetInsert ins guard) V⊑M′)
    (transport⊑ᵂ ins q)
⊢²-target-insert {W = W} {γ = γ} ins
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} {p = p}
      Anv zero∈A (CTX.smart-fresh-behind guard) liftγ vV M′⊢
      V⊑M′ q) =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTX.smart-fresh-behind (smartFreshGuardInsert ins guard))
    (targetSmartLiftCtxLeft ins (smartFreshTargetInsert ins guard) liftγ)
    vV (target-typing-insert ins M′⊢)
    (⊢²-target-insert (smartFreshTargetInsert ins guard) V⊑M′)
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
    (CTI2.conceal⊑²-seal-star-open {W′ = W′} {p = p}
      no-target mono rb sc c⊢ M⊑M′ q)
    with reverseTagRebaseAtᴸ ins rb
⊢²-target-insert {ρ = ρ} ins
    (CTI2.conceal⊑²-seal-star-open {W′ = W′} {p = p}
      no-target mono rb sc c⊢ M⊑M′ q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  CTI2.conceal⊑²-seal-star-open
    (targetInsertNoTargetAtSource insᵖ no-target)
    (impEnvMono-insert ins insᵖ mono)
    rb⁺
    (mapCtxᵀ-same ins insᵖ sc)
    (source-conceal-insert ins c⊢)
    (⊢²-target-insert insᵖ M⊑M′)
    (transport⊑ᵂ ins q)
⊢²-target-insert {ρ = ρ} ins
    (CTI2.conceal⊑²-source-ok {W′ = W′} {p = p}
      ok mono rb sc c⊢ M⊑M′ q)
    with reverseTagRebaseAtᴸ ins rb
⊢²-target-insert {ρ = ρ} ins
    (CTI2.conceal⊑²-source-ok {W′ = W′} {p = p}
      ok mono rb sc c⊢ M⊑M′ q)
    | Wᵖ⁺ , insᵖ , rb⁺ =
  CTI2.conceal⊑²-source-ok
    (renameSourceConcealOK insᵖ ok)
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
      (CTX.rightOnlyWorld W B′))
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → CTX.rightOnlyWorld W B′
      ∣ ECR.mapCtxᴿ ext γ
      ⊢² M ⊑ renameᵗᵐ wk↪ᵗ M′ ∶ ECR.transport⊑ᵂ ext p

mapCtx-rightBind-ECR : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
    (ext : ECR.WorldExtendᴿ (bind B′ ∷ []) W
      (CTX.rightOnlyWorld W B′))
    (γ : CtxImp W)
  → ECR.mapCtxᴿ ext γ ≡ mapCtxᵀ rightBindTargetInsert γ
mapCtx-rightBind-ECR ext [] = refl
mapCtx-rightBind-ECR {W = W} {B′ = B′} ext
    (CTX.ctx-imp A B p ∷ γ) =
  cong₂ _∷_ entry-eq (mapCtx-rightBind-ECR ext γ)
  where
  entry-eq :
      CTX.ctx-imp A (⇑ᵗ B) (ECR.transport⊑ᵂ ext p)
      ≡ CTX.ctx-imp A (renameᵗ (toRenameᵗ wk↪ᵗ) B)
          (transport⊑ᵂ (rightBindTargetInsert {W = W} {B = B′}) p)
  entry-eq =
    ctx-imp-target-eq {W = CTX.rightOnlyWorld W B′}
      {A = A} {B = ⇑ᵗ B}
      {B′ = renameᵗ (toRenameᵗ wk↪ᵗ) B}
      {p = ECR.transport⊑ᵂ ext p}
      {q = transport⊑ᵂ (rightBindTargetInsert {W = W} {B = B′}) p}
      (sym (renameᵗ-wk-eq B))

⊢²-target-extend-bind : TargetExtendBindᵀ
⊢²-target-extend-bind {W = W} {γ = γ} {M = M} {M′ = M′}
    {B = B} {B′ = B′} {p = p} ext M⊑M′ =
  subst≡
    (λ γ′ → CTX.rightOnlyWorld W B′ ∣ γ′
      ⊢² M ⊑ renameᵗᵐ wk↪ᵗ M′ ∶ ECR.transport⊑ᵂ ext p)
    (sym (mapCtx-rightBind-ECR ext γ))
    (⊢²-retargetᴿ {q = ECR.transport⊑ᵂ ext p}
      (renameᵗ-wk-eq B)
      (⊢²-target-insert
        (rightBindTargetInsert {W = W} {B = B′}) M⊑M′))
