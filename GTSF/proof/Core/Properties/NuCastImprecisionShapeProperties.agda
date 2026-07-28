module proof.Core.Properties.NuCastImprecisionShapeProperties where

-- File Charter:
--   * Proves that type-imprecision and coercion shapes are invariant under
--     type renaming.
--   * Exposes canonical erasure preservation for paired, source-only, and
--     target-only type lifting.
--   * Transports hereditary cast and composition shapes without rebuilding
--     store well-formedness or assumption-membership witnesses.
--   * Contains no term-imprecision or simulation proof.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Product using (_,_)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import Coercions using (genᵈ; instᵈ; renameᶜ)
import Coercions as C
open import ImprecisionWf using
  ( ImpAssm
  ; ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; id★
  ; idˣ
  ; idι
  ; _↦_
  ; ∀ⁱ_
  ; tag_
  ; tag_⇛_
  ; tagˣ
  ; ν
  ; renameNonVar
  )
open import CastImprecisionShape using
  ( _⊢ᶜ_⦂_
  ; narrowing
  ; widening
  ; shape-id-var
  ; shape-id-base
  ; shape-id-star
  ; shape-fun
  ; shape-all
  ; shape-tag-var
  ; shape-tag-base
  ; shape-tag-fun
  ; shape-untag-var
  ; shape-untag-base
  ; shape-untag-fun
  ; shape-seal
  ; shape-unseal
  ; shape-gen
  ; shape-inst
  ; shape-sequence-widening
  ; shape-sequence-narrowing
  )
import Types as T
open import Types using
  (Atom; Renameᵗ; WfTy; extᵗ; occurs; renameᵗ)
import NarrowWiden as NW
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
import NuStore as NS
open import NuReduction using (StoreChanges; bind; keep)
open import TermTyping using (SealModeStore★)
open import ImprecisionComposition using
  ( ⌊_⌋
  ; comp-id★
  ; comp-idˣ-idˣ
  ; comp-idˣ-tagˣ
  ; comp-idι-idι
  ; comp-idι-tag
  ; comp-↦-↦
  ; comp-↦-tag
  ; comp-∀-∀
  ; comp-∀-ν
  ; comp-tag-id★
  ; comp-tag-⇛-id★
  ; comp-tagˣ-id★
  ; comp-ν
  ; ∀ˢ_
  ; _↦ˢ_
  ; tag_⇛ˢ_
  ; νˢ_
  ; _；_≋_
  )
open import proof.Core.Properties.CastImprecision using
  ( ComposeCtx
  ; compose-∀∀
  ; compose-∀ν
  ; compose-νid
  ; compose-cast-left
  ; drop-target-∀
  ; drop-target-ν
  ; DropTargetCtx
  ; drop-targetᵢ
  ; left-castᵢ-compatible
  ; seal★-ext-shift
  ; seal★-gen-shift
  ; seal★-inst-shift
  ; ⊑-trans-compose
  )
open import proof.Core.Properties.NuCastImprecision using
  ( nu-narrowing-gen⇒⊑ᵢ
  ; nu-narrowing⇒⊑ᵢ
  ; nu-widening-inst⇒⊑ᵢ
  ; nu-widening⇒⊑ᵢ
  )
open import proof.Core.Properties.NuStoreProperties using
  (StoreWf-⟰ᵗ; StoreWf-bind)
open import proof.Core.Properties.ImprecisionCompositionProperties using
  (compose-result-unique)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyCoercionUnderTyBinders)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( DropAtᵢ
  ; drop-zeroᵢ
  ; drop-∀ᵢ
  ; drop-νᵢ
  ; open-unused-atᵢ
  ; open-unusedᵢ
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( rename-assm²ᵢ
  ; ∨-false-leftᵢ
  ; ∨-false-rightᵢ
  ; rename-assm²-∀ᵢ
  ; rename-assm²-source-νᵢ
  ; rename-assm²-target-rightᵢ
  ; rename-assm²-⇑ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; ∀ᵢᶜ
  ; νᵢᶜ
  ; ⊑-lift∀ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import proof.Core.Properties.TypeProperties using
  ( TyRenameWf
  ; TyRenameWf-ext
  ; occurs-zero-rename-ext
  ; rename-raise-ext
  ; renameᵗ-id
  )


shape-subst-source :
  ∀ {Φ Δᴸ Δᴿ A A′ B}
    (eq : A ≡ A′)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊
    (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑ B ⊣ Δᴿ) eq p)
  ⌋ ≡ ⌊ p ⌋
shape-subst-source refl p = refl


shape-subst-target :
  ∀ {Φ Δᴸ Δᴿ A B B′}
    (eq : B ≡ B′)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊
    (subst (λ T → Φ ∣ Δᴸ ⊢ A ⊑ T ⊣ Δᴿ) eq p)
  ⌋ ≡ ⌊ p ⌋
shape-subst-target refl p = refl


shape-rename :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ A B}
    (assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Θᴸ τ)
    (hσ : TyRenameWf Δᴿ Θᴿ σ)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-renameᵗ²ᵢ assm hτ hσ p ⌋ ≡ ⌊ p ⌋
shape-rename assm hτ hσ id★ = refl
shape-rename assm hτ hσ
    (idˣ x∈ X<Δᴸ Y<Δᴿ) = refl
shape-rename assm hτ hσ idι = refl
shape-rename assm hτ hσ (p ↦ q) =
  cong₂ _↦ˢ_
    (shape-rename assm hτ hσ p)
    (shape-rename assm hτ hσ q)
shape-rename assm hτ hσ (∀ⁱ p) =
  cong ∀ˢ_
    (shape-rename
      (rename-assm²-⇑ᵢ assm)
      (TyRenameWf-ext hτ)
      (TyRenameWf-ext hσ)
      p)
shape-rename assm hτ hσ (tag ι) = refl
shape-rename assm hτ hσ (tag_⇛_ p q) =
  cong₂ tag_⇛ˢ_
    (shape-rename assm hτ hσ p)
    (shape-rename assm hτ hσ q)
shape-rename assm hτ hσ (tagˣ x★∈ X<Δᴸ) = refl
shape-rename assm hτ hσ (ν safe occ p) =
  cong νˢ_
    (shape-rename
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ)
      hσ
      p)


shape-lift∀ᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-lift∀ᵢ p ⌋ ≡ ⌊ p ⌋
shape-lift∀ᵢ p =
  shape-rename
    rename-assm²-∀ᵢ
    (λ X<Δ → s<s X<Δ)
    (λ Y<Δ → s<s Y<Δ)
    p


shape-source-liftνᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-source-liftνᵢ p ⌋ ≡ ⌊ p ⌋
shape-source-liftνᵢ {B = B} p =
  trans
    (shape-subst-target
      (renameᵗ-id B)
      (⊑-renameᵗ²ᵢ
        rename-assm²-source-νᵢ
        (λ X<Δ → s<s X<Δ)
        id
        p))
    (shape-rename
      rename-assm²-source-νᵢ
      (λ X<Δ → s<s X<Δ)
      id
      p)


shape-target-lift-rightᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-target-lift-rightᵢ p ⌋ ≡ ⌊ p ⌋
shape-target-lift-rightᵢ {A = A} p =
  trans
    (shape-subst-source (renameᵗ-id A) renamed)
    (shape-rename
      rename-assm²-target-rightᵢ
      (λ X<Δ → X<Δ)
      (λ Y<Δ → s<s Y<Δ)
      p)
  where
  renamed =
    ⊑-renameᵗ²ᵢ rename-assm²-target-rightᵢ
      (λ X<Δ → X<Δ) (λ Y<Δ → s<s Y<Δ) p


shape-open-unused-atᵢ :
  ∀ {k Φ Ψ Δᴸ Δᴿ A B}
    (d : DropAtᵢ k Φ Ψ)
    (k<Δ : k < suc Δᴸ)
    (occ : occurs k A ≡ false)
    (p : Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ open-unused-atᵢ d k<Δ occ p ⌋ ≡ ⌊ p ⌋
shape-open-unused-atᵢ d k<Δ occ id★ = refl
shape-open-unused-atᵢ d k<Δ occ
    (idˣ x∈ X<Δᴸ Y<Δᴿ) = refl
shape-open-unused-atᵢ d k<Δ occ idι = refl
shape-open-unused-atᵢ d k<Δ occ (p ↦ q) =
  cong₂ _↦ˢ_
    (shape-open-unused-atᵢ
      d k<Δ (∨-false-leftᵢ occ) p)
    (shape-open-unused-atᵢ
      d k<Δ (∨-false-rightᵢ occ) q)
shape-open-unused-atᵢ d k<Δ occ (∀ⁱ p) =
  cong ∀ˢ_
    (shape-open-unused-atᵢ (drop-∀ᵢ d) (s<s k<Δ) occ p)
shape-open-unused-atᵢ d k<Δ occ (tag ι) = refl
shape-open-unused-atᵢ d k<Δ occ (tag p ⇛ q) =
  cong₂ tag_⇛ˢ_
    (shape-open-unused-atᵢ
      d k<Δ (∨-false-leftᵢ occ) p)
    (shape-open-unused-atᵢ
      d k<Δ (∨-false-rightᵢ occ) q)
shape-open-unused-atᵢ d k<Δ occ
    (tagˣ x∈ X<Δᴸ) = refl
shape-open-unused-atᵢ d k<Δ occ (ν safe occA p) =
  cong νˢ_
    (shape-open-unused-atᵢ (drop-νᵢ d) (s<s k<Δ) occ p)


shape-open-unusedᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (occ : occurs zero A ≡ false)
    (p : νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ open-unusedᵢ occ p ⌋ ≡ ⌊ p ⌋
shape-open-unusedᵢ occ p =
  shape-open-unused-atᵢ drop-zeroᵢ z<s occ p


rename-assm²-target-ext-idᵢ :
  ∀ {τ a} →
  rename-assm²ᵢ τ (extᵗ (λ X → X)) a
    ≡ rename-assm²ᵢ τ (λ X → X) a
rename-assm²-target-ext-idᵢ {a = X ˣ⊑★} = refl
rename-assm²-target-ext-idᵢ {a = X ˣ⊑ˣ zero} = refl
rename-assm²-target-ext-idᵢ {a = X ˣ⊑ˣ suc Y} = refl


rename-assm²-∀-leftᵢ :
  ∀ {Φ Ψ τ} →
  (∀ {a} → a ∈ Φ →
    rename-assm²ᵢ τ (λ X → X) a ∈ Ψ) →
  ∀ {a} → a ∈ ∀ᵢᶜ Φ →
  rename-assm²ᵢ (extᵗ τ) (λ X → X) a ∈ ∀ᵢᶜ Ψ
rename-assm²-∀-leftᵢ {Ψ = Ψ} assm {a = a} a∈ =
  subst
    (_∈ ∀ᵢᶜ Ψ)
    rename-assm²-target-ext-idᵢ
    (rename-assm²-⇑ᵢ assm a∈)


⊑-rename-leftᵢ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ A B}
    (τ : Renameᵗ) →
    (∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ) →
    TyRenameWf Δᴸ Δᴸ′ τ →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
    Ψ ∣ Δᴸ′ ⊢ renameᵗ τ A ⊑ B ⊣ Δᴿ
⊑-rename-leftᵢ τ assm hτ id★ = id★
⊑-rename-leftᵢ τ assm hτ (idˣ a∈ X<Δ Y<Δ) =
  idˣ (assm a∈) (hτ X<Δ) Y<Δ
⊑-rename-leftᵢ τ assm hτ idι = idι
⊑-rename-leftᵢ τ assm hτ (p ↦ q) =
  ⊑-rename-leftᵢ τ assm hτ p ↦
  ⊑-rename-leftᵢ τ assm hτ q
⊑-rename-leftᵢ τ assm hτ (∀ⁱ p) =
  ∀ⁱ (⊑-rename-leftᵢ
    (extᵗ τ)
    (rename-assm²-∀-leftᵢ assm)
    (TyRenameWf-ext hτ)
    p)
⊑-rename-leftᵢ τ assm hτ (tag ι) = tag ι
⊑-rename-leftᵢ τ assm hτ (tag p ⇛ q) =
  tag (⊑-rename-leftᵢ τ assm hτ p) ⇛
  ⊑-rename-leftᵢ τ assm hτ q
⊑-rename-leftᵢ τ assm hτ (tagˣ a∈ X<Δ) =
  tagˣ (assm a∈) (hτ X<Δ)
⊑-rename-leftᵢ {Φ = Φ} τ assm hτ
    (ν {A = A} safe occ p) =
  ν (renameNonVar (extᵗ τ) safe)
    (trans (occurs-zero-rename-ext τ A) occ)
    (⊑-rename-leftᵢ
      (extᵗ τ)
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ)
      p)


shape-rename-left :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ A B}
    (assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Δᴸ′ τ)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-rename-leftᵢ τ assm hτ p ⌋ ≡ ⌊ p ⌋
shape-rename-left assm hτ id★ = refl
shape-rename-left assm hτ (idˣ a∈ X<Δ Y<Δ) = refl
shape-rename-left assm hτ idι = refl
shape-rename-left assm hτ (p ↦ q) =
  cong₂ _↦ˢ_
    (shape-rename-left assm hτ p)
    (shape-rename-left assm hτ q)
shape-rename-left assm hτ (∀ⁱ p) =
  cong ∀ˢ_
    (shape-rename-left
      (rename-assm²-∀-leftᵢ assm)
      (TyRenameWf-ext hτ)
      p)
shape-rename-left assm hτ (tag ι) = refl
shape-rename-left assm hτ (tag p ⇛ q) =
  cong₂ tag_⇛ˢ_
    (shape-rename-left assm hτ p)
    (shape-rename-left assm hτ q)
shape-rename-left assm hτ (tagˣ a∈ X<Δ) = refl
shape-rename-left assm hτ (ν safe occ p) =
  cong νˢ_
    (shape-rename-left
      (rename-assm²-⇑ᴸᵢ assm)
      (TyRenameWf-ext hτ)
      p)


⊑-rename-left-atᵢ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ A A′ B}
    (τ : Renameᵗ)
    (assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Δᴸ′ τ) →
    A′ ≡ renameᵗ τ A →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
    Ψ ∣ Δᴸ′ ⊢ A′ ⊑ B ⊣ Δᴿ
⊑-rename-left-atᵢ τ assm hτ eqA p =
  subst (λ T → _ ∣ _ ⊢ T ⊑ _ ⊣ _) (sym eqA)
    (⊑-rename-leftᵢ τ assm hτ p)


shape-rename-left-atᵢ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ A A′ B}
    (τ : Renameᵗ)
    (assm : ∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Δᴸ′ τ)
    (eqA : A′ ≡ renameᵗ τ A)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-rename-left-atᵢ τ assm hτ eqA p ⌋ ≡ ⌊ p ⌋
shape-rename-left-atᵢ τ assm hτ eqA p =
  trans
    (shape-subst-source (sym eqA)
      (⊑-rename-leftᵢ τ assm hτ p))
    (shape-rename-left assm hτ p)


cast-shape-rename :
  ∀ {direction c s} →
  (τ : Renameᵗ) →
  direction ⊢ᶜ c ⦂ s →
  direction ⊢ᶜ renameᶜ τ c ⦂ s
cast-shape-rename τ shape-id-var =
  shape-id-var
cast-shape-rename τ shape-id-base =
  shape-id-base
cast-shape-rename τ shape-id-star =
  shape-id-star
cast-shape-rename τ (shape-fun c-shape d-shape) =
  shape-fun
    (cast-shape-rename τ c-shape)
    (cast-shape-rename τ d-shape)
cast-shape-rename τ (shape-all c-shape) =
  shape-all (cast-shape-rename (extᵗ τ) c-shape)
cast-shape-rename τ shape-tag-var =
  shape-tag-var
cast-shape-rename τ shape-tag-base =
  shape-tag-base
cast-shape-rename τ shape-tag-fun =
  shape-tag-fun
cast-shape-rename τ shape-untag-var =
  shape-untag-var
cast-shape-rename τ shape-untag-base =
  shape-untag-base
cast-shape-rename τ shape-untag-fun =
  shape-untag-fun
cast-shape-rename τ shape-seal =
  shape-seal
cast-shape-rename τ shape-unseal =
  shape-unseal
cast-shape-rename τ (shape-gen c-shape) =
  shape-gen (cast-shape-rename (extᵗ τ) c-shape)
cast-shape-rename τ (shape-inst c-shape) =
  shape-inst (cast-shape-rename (extᵗ τ) c-shape)
cast-shape-rename τ
    (shape-sequence-widening c-shape d-shape comp) =
  shape-sequence-widening
    (cast-shape-rename τ c-shape)
    (cast-shape-rename τ d-shape)
    comp
cast-shape-rename τ
    (shape-sequence-narrowing c-shape d-shape comp) =
  shape-sequence-narrowing
    (cast-shape-rename τ c-shape)
    (cast-shape-rename τ d-shape)
    comp


cast-shape-applyCoercions :
  ∀ (χs : StoreChanges) {direction c s} →
  direction ⊢ᶜ c ⦂ s →
  direction ⊢ᶜ applyCoercions χs c ⦂ s
cast-shape-applyCoercions [] c-shape = c-shape
cast-shape-applyCoercions (keep ∷ χs) c-shape =
  cast-shape-applyCoercions χs c-shape
cast-shape-applyCoercions (bind A ∷ χs) c-shape =
  cast-shape-applyCoercions χs
    (cast-shape-rename _ c-shape)


cast-shape-applyCoercionUnderTyBinders :
  ∀ (χs : StoreChanges) {direction c s} →
  direction ⊢ᶜ c ⦂ s →
  direction ⊢ᶜ applyCoercionUnderTyBinders χs c ⦂ s
cast-shape-applyCoercionUnderTyBinders [] c-shape = c-shape
cast-shape-applyCoercionUnderTyBinders (keep ∷ χs) c-shape =
  cast-shape-applyCoercionUnderTyBinders χs c-shape
cast-shape-applyCoercionUnderTyBinders (bind A ∷ χs) c-shape =
  cast-shape-applyCoercionUnderTyBinders χs
    (cast-shape-rename (extᵗ suc) c-shape)


imprecision-composition-shape-transport :
  ∀ {p q r p′ q′ r′} →
  p′ ≡ p →
  q′ ≡ q →
  r′ ≡ r →
  p ； q ≋ r →
  p′ ； q′ ≋ r′
imprecision-composition-shape-transport refl refl refl comp = comp


compose-source-ν-body :
  ∀ {p q r} →
  νˢ p ； q ≋ νˢ r →
  p ； q ≋ r
compose-source-ν-body (comp-ν comp) = comp


shape-⊑-trans-compose :
  ∀ {ρ Δᴸ Δᴹ Δᴿ Φᴸ Φᴿ Φᴼ A B C}
    (ctx : ComposeCtx ρ Δᴸ Φᴸ Φᴿ Φᴼ)
    (p : Φᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴹ)
    (q : Φᴿ ∣ Δᴹ ⊢ B ⊑ C ⊣ Δᴿ) →
  ⌊ p ⌋ ； ⌊ q ⌋ ≋ ⌊ ⊑-trans-compose ctx p q ⌋
shape-⊑-trans-compose ctx id★ id★ =
  comp-id★
shape-⊑-trans-compose ctx
    (idˣ x∈ X<Δᴸ Y<Δᴹ) (idˣ y∈ Y<Δᴹ′ Z<Δᴿ) =
  comp-idˣ-idˣ
shape-⊑-trans-compose ctx
    (idˣ x∈ X<Δᴸ Y<Δᴹ) (tagˣ y★∈ Y<Δᴹ′) =
  comp-idˣ-tagˣ
shape-⊑-trans-compose ctx idι idι =
  comp-idι-idι
shape-⊑-trans-compose ctx idι (tag ι) =
  comp-idι-tag
shape-⊑-trans-compose ctx (p₁ ↦ p₂) (q₁ ↦ q₂) =
  comp-↦-↦
    (shape-⊑-trans-compose ctx p₁ q₁)
    (shape-⊑-trans-compose ctx p₂ q₂)
shape-⊑-trans-compose ctx (p₁ ↦ p₂) (tag q₁ ⇛ q₂) =
  comp-↦-tag
    (shape-⊑-trans-compose ctx p₁ q₁)
    (shape-⊑-trans-compose ctx p₂ q₂)
shape-⊑-trans-compose ctx (∀ⁱ p) (∀ⁱ q) =
  comp-∀-∀
    (shape-⊑-trans-compose (compose-∀∀ ctx) p q)
shape-⊑-trans-compose ctx (∀ⁱ p) (ν safe occ q) =
  comp-∀-ν
    (shape-⊑-trans-compose (compose-∀ν ctx) p q)
shape-⊑-trans-compose ctx (tag ι) id★ =
  comp-tag-id★
shape-⊑-trans-compose ctx (tag p ⇛ q) id★ =
  comp-tag-⇛-id★
    (shape-⊑-trans-compose ctx p id★)
    (shape-⊑-trans-compose ctx q id★)
shape-⊑-trans-compose ctx (tagˣ x★∈ X<Δᴸ) id★ =
  comp-tagˣ-id★
shape-⊑-trans-compose ctx (ν safe occ p) q =
  comp-ν
    (shape-⊑-trans-compose (compose-νid ctx) p q)


shape-drop-targetᵢ :
  ∀ {k Φ Ψ Δᴸ Δᴿ A B}
    (hB : WfTy Δᴿ B)
    (drop : DropTargetCtx k Φ Ψ)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ renameᵗ (T.raiseVarFrom k) B ⊣
      suc Δᴿ) →
  ⌊ drop-targetᵢ hB drop p ⌋ ≡ ⌊ p ⌋
shape-drop-targetᵢ T.wf★ drop id★ =
  refl
shape-drop-targetᵢ (T.wfVar Y<Δ) drop
    (idˣ x∈ X<Δ Y<Δ′) =
  refl
shape-drop-targetᵢ T.wfBase drop idι =
  refl
shape-drop-targetᵢ (T.wf⇒ hA hB) drop (p ↦ q) =
  cong₂ _↦ˢ_
    (shape-drop-targetᵢ hA drop p)
    (shape-drop-targetᵢ hB drop q)
shape-drop-targetᵢ {k = k} (T.wf∀ {A = B} hB) drop
    (∀ⁱ p)
    rewrite rename-raise-ext k B =
  cong ∀ˢ_ (shape-drop-targetᵢ hB (drop-target-∀ drop) p)
shape-drop-targetᵢ T.wf★ drop (tag ι) =
  refl
shape-drop-targetᵢ T.wf★ drop (tag p ⇛ q) =
  cong₂ tag_⇛ˢ_
    (shape-drop-targetᵢ T.wf★ drop p)
    (shape-drop-targetᵢ T.wf★ drop q)
shape-drop-targetᵢ T.wf★ drop (tagˣ x∈ X<Δ) =
  refl
shape-drop-targetᵢ (T.wfVar X<Δ) drop (ν safe occ p) =
  cong νˢ_
    (shape-drop-targetᵢ (T.wfVar X<Δ) (drop-target-ν drop) p)
shape-drop-targetᵢ T.wfBase drop (ν safe occ p) =
  cong νˢ_ (shape-drop-targetᵢ T.wfBase (drop-target-ν drop) p)
shape-drop-targetᵢ T.wf★ drop (ν safe occ p) =
  cong νˢ_ (shape-drop-targetᵢ T.wf★ (drop-target-ν drop) p)
shape-drop-targetᵢ (T.wf⇒ hA hB) drop (ν safe occ p) =
  cong νˢ_
    (shape-drop-targetᵢ (T.wf⇒ hA hB) (drop-target-ν drop) p)
shape-drop-targetᵢ (T.wf∀ hB) drop (ν safe occ p) =
  cong νˢ_
    (shape-drop-targetᵢ (T.wf∀ hB) (drop-target-ν drop) p)


mutual
  nu-narrowing⇒⊑ᵢ-shape :
    ∀ {μ Δ Σ A B c s} →
    (wfΣ : NS.StoreWf Δ Σ) →
    (seal★ : SealModeStore★ μ Σ) →
    (c⊒ : μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B) →
    narrowing ⊢ᶜ c ⦂ s →
    ⌊ nu-narrowing⇒⊑ᵢ wfΣ seal★ c⊒ ⌋ ≡ s

  nu-widening⇒⊑ᵢ-shape :
    ∀ {μ Δ Σ A B c s} →
    (wfΣ : NS.StoreWf Δ Σ) →
    (seal★ : SealModeStore★ μ Σ) →
    (c⊑ : μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B) →
    widening ⊢ᶜ c ⦂ s →
    ⌊ nu-widening⇒⊑ᵢ wfΣ seal★ c⊑ ⌋ ≡ s

  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-id (T.wfVar X<Δ) ok ,
       NW.cross (NW.id-＇ X))
      shape-id-var =
    refl
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-id T.wfBase ok ,
       NW.cross (NW.id-‵ ι))
      shape-id-base =
    refl
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-id T.wf★ ok , NW.id★)
      shape-id-star =
    refl
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-fun c⊢ d⊢ ,
       NW.cross (cʷ NW.↦ dⁿ))
      (shape-fun c-shape d-shape) =
    cong₂ _↦ˢ_
      (nu-widening⇒⊑ᵢ-shape wfΣ seal★
        (c⊢ , cʷ) c-shape)
      (nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
        (d⊢ , dⁿ) d-shape)
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-all c⊢ ,
       NW.cross (NW.`∀ cⁿ))
      (shape-all c-shape) =
    cong ∀ˢ_
      (nu-narrowing⇒⊑ᵢ-shape
        (StoreWf-⟰ᵗ wfΣ)
        (seal★-ext-shift seal★)
        (c⊢ , cⁿ) c-shape)
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-gen hA occB c⊢ , NW.gen cⁿ)
      (shape-gen c-shape) =
    cong νˢ_
      (trans
        (shape-drop-targetᵢ hA _ inner)
        (nu-narrowing⇒⊑ᵢ-shape
          (StoreWf-⟰ᵗ wfΣ)
          (seal★-gen-shift seal★)
          (c⊢ , NW.genSafe→narrowing cⁿ)
          c-shape))
    where
    inner =
      nu-narrowing⇒⊑ᵢ
        (StoreWf-⟰ᵗ wfΣ)
        (seal★-gen-shift seal★)
        (c⊢ , NW.genSafe→narrowing cⁿ)
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-untag (T.wfVar {X = α} X<Δ) (T.＇ .α) ok ,
       NW.untag (T.＇ .α))
      shape-untag-var =
    refl
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-untag T.wfBase (T.‵ ι) ok ,
       NW.untag (T.‵ .ι))
      shape-untag-base =
    refl
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-untag (T.wf⇒ T.wf★ T.wf★) T.★⇒★ ok ,
       NW.untag T.★⇒★)
      shape-untag-fun =
    refl
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-seq c⊢ d⊢ ,
       G NW.？︔ dⁿ)
      (shape-sequence-narrowing
        c-shape d-shape sequence-comp) =
    compose-result-unique canonical′ sequence-comp
    where
    c-imp = nu-narrowing⇒⊑ᵢ wfΣ seal★
      (c⊢ , NW.untag G)
    d-imp = nu-narrowing⇒⊑ᵢ wfΣ seal★
      (d⊢ , NW.cross
        (proof.Core.Properties.CastImprecision.strictCrossNarrowing⇒crossNarrowing
          dⁿ))

    canonical =
      shape-⊑-trans-compose
        (compose-cast-left left-castᵢ-compatible)
        d-imp c-imp

    canonical′ =
      imprecision-composition-shape-transport
        (sym (nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
          (d⊢ , NW.cross
            (proof.Core.Properties.CastImprecision.strictCrossNarrowing⇒crossNarrowing
              dⁿ))
          d-shape))
        (sym (nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
          (c⊢ , NW.untag G) c-shape))
        refl canonical
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-seq c⊢
        (C.cast-gen hA occB d⊢) ,
       NW.fun-untag-gen safe)
      (shape-sequence-narrowing
        c-shape (shape-gen d-shape) sequence-comp) =
    compose-result-unique canonical′ sequence-comp
    where
    c-imp = nu-narrowing⇒⊑ᵢ wfΣ seal★
      (c⊢ , NW.untag T.★⇒★)
    d-imp = nu-narrowing-gen⇒⊑ᵢ wfΣ seal★
      hA occB (d⊢ , NW.genSafe→narrowing safe) safe

    d-inner =
      nu-narrowing⇒⊑ᵢ
        (StoreWf-⟰ᵗ wfΣ)
        (seal★-gen-shift seal★)
        (d⊢ , NW.genSafe→narrowing safe)

    canonical =
      shape-⊑-trans-compose
        (compose-cast-left left-castᵢ-compatible)
        d-imp c-imp

    canonical′ =
      imprecision-composition-shape-transport
        (sym
          (cong νˢ_
            (trans
              (shape-drop-targetᵢ hA _ d-inner)
              (nu-narrowing⇒⊑ᵢ-shape
                (StoreWf-⟰ᵗ wfΣ)
                (seal★-gen-shift seal★)
                (d⊢ , NW.genSafe→narrowing safe)
                d-shape))))
        (sym (nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
          (c⊢ , NW.untag T.★⇒★) c-shape))
        refl canonical
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-seal hA α∈Σ ok ,
       NW.sealⁿ A α)
      shape-seal
      with NS.unique wfΣ α∈Σ (seal★ α ok)
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-seal hA α∈Σ ok ,
       NW.sealⁿ A α)
      shape-seal | refl =
    refl
  nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-seq c⊢ d⊢ ,
       cⁿ NW.︔seal α)
      (shape-sequence-narrowing
        c-shape d-shape sequence-comp) =
    compose-result-unique canonical′ sequence-comp
    where
    c-imp = nu-narrowing⇒⊑ᵢ wfΣ seal★
      (c⊢ ,
       proof.Core.Properties.CastImprecision.strictNarrowing⇒narrowing
         cⁿ)
    d-imp = nu-narrowing⇒⊑ᵢ wfΣ seal★
      (d⊢ , NW.sealⁿ _ α)

    canonical =
      shape-⊑-trans-compose
        (compose-cast-left left-castᵢ-compatible)
        d-imp c-imp

    canonical′ =
      imprecision-composition-shape-transport
        (sym (nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
          (d⊢ , NW.sealⁿ _ α) d-shape))
        (sym (nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
          (c⊢ ,
           proof.Core.Properties.CastImprecision.strictNarrowing⇒narrowing
             cⁿ)
          c-shape))
        refl canonical

  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-id (T.wfVar X<Δ) ok ,
       NW.cross (NW.id-＇ X))
      shape-id-var =
    refl
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-id T.wfBase ok ,
       NW.cross (NW.id-‵ ι))
      shape-id-base =
    refl
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-id T.wf★ ok , NW.id★)
      shape-id-star =
    refl
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-fun c⊢ d⊢ ,
       NW.cross (cⁿ NW.↦ dʷ))
      (shape-fun c-shape d-shape) =
    cong₂ _↦ˢ_
      (nu-narrowing⇒⊑ᵢ-shape wfΣ seal★
        (c⊢ , cⁿ) c-shape)
      (nu-widening⇒⊑ᵢ-shape wfΣ seal★
        (d⊢ , dʷ) d-shape)
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-all c⊢ ,
       NW.cross (NW.`∀ cʷ))
      (shape-all c-shape) =
    cong ∀ˢ_
      (nu-widening⇒⊑ᵢ-shape
        (StoreWf-⟰ᵗ wfΣ)
        (seal★-ext-shift seal★)
        (c⊢ , cʷ) c-shape)
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-inst hB occA c⊢ , NW.inst cʷ)
      (shape-inst c-shape) =
    cong νˢ_
      (trans
        (shape-drop-targetᵢ hB _ inner)
        (nu-widening⇒⊑ᵢ-shape
          (StoreWf-bind wfΣ T.wf★)
          (seal★-inst-shift seal★)
          (c⊢ , NW.instSafe→widening cʷ)
          c-shape))
    where
    inner =
      nu-widening⇒⊑ᵢ
        (StoreWf-bind wfΣ T.wf★)
        (seal★-inst-shift seal★)
        (c⊢ , NW.instSafe→widening cʷ)
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-tag (T.wfVar {X = α} X<Δ) (T.＇ .α) ok ,
       NW.tag (T.＇ .α))
      shape-tag-var =
    refl
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-tag T.wfBase (T.‵ ι) ok ,
       NW.tag (T.‵ .ι))
      shape-tag-base =
    refl
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-tag (T.wf⇒ T.wf★ T.wf★) T.★⇒★ ok ,
       NW.tag T.★⇒★)
      shape-tag-fun =
    refl
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-seq c⊢ d⊢ ,
       cʷ NW.︔ G !)
      (shape-sequence-widening
        c-shape d-shape sequence-comp) =
    compose-result-unique canonical′ sequence-comp
    where
    c-imp = nu-widening⇒⊑ᵢ wfΣ seal★
      (c⊢ , NW.cross
        (proof.Core.Properties.CastImprecision.strictCrossWidening⇒crossWidening
          cʷ))
    d-imp = nu-widening⇒⊑ᵢ wfΣ seal★
      (d⊢ , NW.tag G)

    canonical =
      shape-⊑-trans-compose
        (compose-cast-left left-castᵢ-compatible)
        c-imp d-imp

    canonical′ =
      imprecision-composition-shape-transport
        (sym (nu-widening⇒⊑ᵢ-shape wfΣ seal★
          (c⊢ , NW.cross
            (proof.Core.Properties.CastImprecision.strictCrossWidening⇒crossWidening
              cʷ))
          c-shape))
        (sym (nu-widening⇒⊑ᵢ-shape wfΣ seal★
          (d⊢ , NW.tag G) d-shape))
        refl canonical
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-seq
        (C.cast-inst hB occA c⊢) d⊢ ,
       NW.inst-fun-tag safe)
      (shape-sequence-widening
        (shape-inst c-shape) d-shape sequence-comp) =
    compose-result-unique canonical′ sequence-comp
    where
    c-imp = nu-widening-inst⇒⊑ᵢ wfΣ seal★
      hB occA (c⊢ , NW.instSafe→widening safe) safe
    d-imp = nu-widening⇒⊑ᵢ wfΣ seal★
      (d⊢ , NW.tag T.★⇒★)

    c-inner =
      nu-widening⇒⊑ᵢ
        (StoreWf-bind wfΣ T.wf★)
        (seal★-inst-shift seal★)
        (c⊢ , NW.instSafe→widening safe)

    canonical =
      shape-⊑-trans-compose
        (compose-cast-left left-castᵢ-compatible)
        c-imp d-imp

    canonical′ =
      imprecision-composition-shape-transport
        (sym
          (cong νˢ_
            (trans
              (shape-drop-targetᵢ hB _ c-inner)
              (nu-widening⇒⊑ᵢ-shape
                (StoreWf-bind wfΣ T.wf★)
                (seal★-inst-shift seal★)
                (c⊢ , NW.instSafe→widening safe)
                c-shape))))
        (sym (nu-widening⇒⊑ᵢ-shape wfΣ seal★
          (d⊢ , NW.tag T.★⇒★) d-shape))
        refl canonical
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-unseal hA α∈Σ ok ,
       NW.unsealʷ α A)
      shape-unseal
      with NS.unique wfΣ α∈Σ (seal★ α ok)
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-unseal hA α∈Σ ok ,
       NW.unsealʷ α A)
      shape-unseal | refl =
    refl
  nu-widening⇒⊑ᵢ-shape wfΣ seal★
      (C.cast-seq c⊢ d⊢ ,
       NW.unseal︔_ α dʷ)
      (shape-sequence-widening
        c-shape d-shape sequence-comp) =
    compose-result-unique canonical′ sequence-comp
    where
    c-imp = nu-widening⇒⊑ᵢ wfΣ seal★
      (c⊢ , NW.unsealʷ α _)
    d-imp = nu-widening⇒⊑ᵢ wfΣ seal★
      (d⊢ ,
       proof.Core.Properties.CastImprecision.strictWidening⇒widening
         dʷ)

    canonical =
      shape-⊑-trans-compose
        (compose-cast-left left-castᵢ-compatible)
        c-imp d-imp

    canonical′ =
      imprecision-composition-shape-transport
        (sym (nu-widening⇒⊑ᵢ-shape wfΣ seal★
          (c⊢ , NW.unsealʷ α _) c-shape))
        (sym (nu-widening⇒⊑ᵢ-shape wfΣ seal★
          (d⊢ ,
           proof.Core.Properties.CastImprecision.strictWidening⇒widening
             dʷ)
          d-shape))
        refl canonical


target-atom-shape-unique :
  ∀ {Φ Δᴸ Δᴿ A B}
    (atom : Atom B)
    (p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ p ⌋ ≡ ⌊ q ⌋
target-atom-shape-unique (T.＇ β)
    (idˣ p α<Δᴸ β<Δᴿ) (idˣ q α<Δᴸ′ β<Δᴿ′) =
  refl
target-atom-shape-unique (T.‵ ι) idι idι =
  refl
target-atom-shape-unique T.★ id★ id★ =
  refl
target-atom-shape-unique T.★ (tag ι) (tag .ι) =
  refl
target-atom-shape-unique T.★
    (tag p₁ ⇛ p₂) (tag q₁ ⇛ q₂) =
  cong₂ tag_⇛ˢ_
    (target-atom-shape-unique T.★ p₁ q₁)
    (target-atom-shape-unique T.★ p₂ q₂)
target-atom-shape-unique T.★
    (tagˣ p α<Δᴸ) (tagˣ q α<Δᴸ′) =
  refl
target-atom-shape-unique atom
    (ν safe occ p) (ν safe′ occ′ q) =
  cong νˢ_ (target-atom-shape-unique atom p q)


source-atom-shape-unique :
  ∀ {Φ Δᴸ Δᴿ A B}
    (atom : Atom A)
    (p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ p ⌋ ≡ ⌊ q ⌋
source-atom-shape-unique (T.＇ α)
    (idˣ p α<Δᴸ β<Δᴿ) (idˣ q α<Δᴸ′ β<Δᴿ′) =
  refl
source-atom-shape-unique (T.＇ α)
    (tagˣ p α<Δᴸ) (tagˣ q α<Δᴸ′) =
  refl
source-atom-shape-unique (T.‵ ι) idι idι =
  refl
source-atom-shape-unique (T.‵ ι) (tag .ι) (tag .ι) =
  refl
source-atom-shape-unique T.★ id★ id★ =
  refl
