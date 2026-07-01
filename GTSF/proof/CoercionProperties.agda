module proof.CoercionProperties where

-- File Charter:
--   * Proof-only metatheory for GTSF coercion typing.
--   * Coercion weakening, type-renaming, dual endpoint flipping, endpoint
--     well-formedness, and reveal/conceal typing lemmas used by term
--     preservation.
--   * Store-specific lemmas belong in `proof.StoreProperties`.
--   * Term substitution/renaming lemmas belong in `proof.NuTermProperties`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Nat using (zero; suc; _<_; _≤_; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties
  using (_≟_; ≤-refl; n≤1+n; n<1+n; <-≤-trans; <-irrefl;
         m<n⇒m<1+n; suc-injective)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂; subst; sym; trans)

open import Types
open import Store
open import Coercions
open import proof.TypeProperties
open import proof.StoreProperties

------------------------------------------------------------------------
-- Inert coercions
------------------------------------------------------------------------

∧-trueˡ :
  ∀ {b c} →
  b ∧ c ≡ true →
  b ≡ true
∧-trueˡ {true} {true} refl = refl
∧-trueˡ {true} {false} ()
∧-trueˡ {false} {c} ()

∧-trueʳ :
  ∀ {b c} →
  b ∧ c ≡ true →
  c ≡ true
∧-trueʳ {true} {true} refl = refl
∧-trueʳ {true} {false} ()
∧-trueʳ {false} {c} ()

renameᶜ-preserves-Inert :
  ∀ ρ {c} →
  Inert c →
  Inert (renameᶜ ρ c)
renameᶜ-preserves-Inert ρ (G !) = renameᵗ ρ G !
renameᶜ-preserves-Inert ρ (seal A α) = seal (renameᵗ ρ A) (ρ α)
renameᶜ-preserves-Inert ρ (c ↦ d) = renameᶜ ρ c ↦ renameᶜ ρ d
renameᶜ-preserves-Inert ρ (`∀ c) = `∀ (renameᶜ (extᵗ ρ) c)
renameᶜ-preserves-Inert ρ (gen A c) =
  gen (renameᵗ ρ A) (renameᶜ (extᵗ ρ) c)

renameᶜ-reflects-Inert :
  ∀ ρ c →
  Inert (renameᶜ ρ c) →
  Inert c
renameᶜ-reflects-Inert ρ (id A) ()
renameᶜ-reflects-Inert ρ (c ︔ d) ()
renameᶜ-reflects-Inert ρ (c ↦ d) (c′ ↦ d′) = c ↦ d
renameᶜ-reflects-Inert ρ (`∀ c) (`∀ c′) = `∀ c
renameᶜ-reflects-Inert ρ (G !) i = G !
renameᶜ-reflects-Inert ρ (G ？) ()
renameᶜ-reflects-Inert ρ (seal A α) i = seal A α
renameᶜ-reflects-Inert ρ (unseal α A) ()
renameᶜ-reflects-Inert ρ (gen A c) i = gen A c
renameᶜ-reflects-Inert ρ (inst B c) ()

mutual
  src-renameᶜ :
    ∀ ρ c →
    src (renameᶜ ρ c) ≡ renameᵗ ρ (src c)
  src-renameᶜ ρ (id A) = refl
  src-renameᶜ ρ (c ︔ d) = src-renameᶜ ρ c
  src-renameᶜ ρ (c ↦ d) =
    cong₂ _⇒_ (tgt-renameᶜ ρ c) (src-renameᶜ ρ d)
  src-renameᶜ ρ (`∀ c) = cong `∀ (src-renameᶜ (extᵗ ρ) c)
  src-renameᶜ ρ (G !) = refl
  src-renameᶜ ρ (G ？) = refl
  src-renameᶜ ρ (seal A α) = refl
  src-renameᶜ ρ (unseal α A) = refl
  src-renameᶜ ρ (gen A c) = refl
  src-renameᶜ ρ (inst B c) = cong `∀ (src-renameᶜ (extᵗ ρ) c)

  tgt-renameᶜ :
    ∀ ρ c →
    tgt (renameᶜ ρ c) ≡ renameᵗ ρ (tgt c)
  tgt-renameᶜ ρ (id A) = refl
  tgt-renameᶜ ρ (c ︔ d) = tgt-renameᶜ ρ d
  tgt-renameᶜ ρ (c ↦ d) =
    cong₂ _⇒_ (src-renameᶜ ρ c) (tgt-renameᶜ ρ d)
  tgt-renameᶜ ρ (`∀ c) = cong `∀ (tgt-renameᶜ (extᵗ ρ) c)
  tgt-renameᶜ ρ (G !) = refl
  tgt-renameᶜ ρ (G ？) = refl
  tgt-renameᶜ ρ (seal A α) = refl
  tgt-renameᶜ ρ (unseal α A) = refl
  tgt-renameᶜ ρ (gen A c) = cong `∀ (tgt-renameᶜ (extᵗ ρ) c)
  tgt-renameᶜ ρ (inst B c) = refl

renameᶜ-cong :
  ∀ {ρ ρ′} →
  (∀ X → ρ X ≡ ρ′ X) →
  ∀ c → renameᶜ ρ c ≡ renameᶜ ρ′ c
renameᶜ-cong eq (id A) = cong id (rename-cong eq A)
renameᶜ-cong eq (c ︔ d) =
  cong₂ _︔_ (renameᶜ-cong eq c) (renameᶜ-cong eq d)
renameᶜ-cong eq (c ↦ d) =
  cong₂ _↦_ (renameᶜ-cong eq c) (renameᶜ-cong eq d)
renameᶜ-cong eq (`∀ c) =
  cong `∀ (renameᶜ-cong
    (λ { zero → refl ; (suc X) → cong suc (eq X) })
    c)
renameᶜ-cong eq (G !) = cong _! (rename-cong eq G)
renameᶜ-cong eq (G ？) = cong _？ (rename-cong eq G)
renameᶜ-cong eq (seal A α) = cong₂ seal (rename-cong eq A) (eq α)
renameᶜ-cong eq (unseal α A) =
  cong₂ unseal (eq α) (rename-cong eq A)
renameᶜ-cong eq (gen A c) =
  cong₂ gen (rename-cong eq A)
    (renameᶜ-cong
      (λ { zero → refl ; (suc X) → cong suc (eq X) })
      c)
renameᶜ-cong eq (inst B c) =
  cong₂ inst (rename-cong eq B)
    (renameᶜ-cong
      (λ { zero → refl ; (suc X) → cong suc (eq X) })
      c)

renameᶜ-compose :
  ∀ ρ τ c →
  renameᶜ τ (renameᶜ ρ c) ≡ renameᶜ (λ X → τ (ρ X)) c
renameᶜ-compose ρ τ (id A) = cong id (renameᵗ-compose ρ τ A)
renameᶜ-compose ρ τ (c ︔ d) =
  cong₂ _︔_ (renameᶜ-compose ρ τ c) (renameᶜ-compose ρ τ d)
renameᶜ-compose ρ τ (c ↦ d) =
  cong₂ _↦_ (renameᶜ-compose ρ τ c) (renameᶜ-compose ρ τ d)
renameᶜ-compose ρ τ (`∀ c) =
  cong `∀
    (trans
      (renameᶜ-compose (extᵗ ρ) (extᵗ τ) c)
      (renameᶜ-cong (λ { zero → refl ; (suc X) → refl }) c))
renameᶜ-compose ρ τ (G !) = cong _! (renameᵗ-compose ρ τ G)
renameᶜ-compose ρ τ (G ？) = cong _？ (renameᵗ-compose ρ τ G)
renameᶜ-compose ρ τ (seal A α) =
  cong₂ seal (renameᵗ-compose ρ τ A) refl
renameᶜ-compose ρ τ (unseal α A) =
  cong₂ unseal refl (renameᵗ-compose ρ τ A)
renameᶜ-compose ρ τ (gen A c) =
  cong₂ gen (renameᵗ-compose ρ τ A)
    (trans
      (renameᶜ-compose (extᵗ ρ) (extᵗ τ) c)
      (renameᶜ-cong (λ { zero → refl ; (suc X) → refl }) c))
renameᶜ-compose ρ τ (inst B c) =
  cong₂ inst (renameᵗ-compose ρ τ B)
    (trans
      (renameᶜ-compose (extᵗ ρ) (extᵗ τ) c)
      (renameᶜ-cong (λ { zero → refl ; (suc X) → refl }) c))

renameᶜ-left-inverse :
  ∀ {ρ ψ} →
  RenameLeftInverse ρ ψ →
  ∀ c →
  renameᶜ ψ (renameᶜ ρ c) ≡ c
renameᶜ-left-inverse inv (id A) =
  cong id (renameᵗ-left-inverse inv A)
renameᶜ-left-inverse inv (p ︔ q) =
  cong₂ _︔_ (renameᶜ-left-inverse inv p)
             (renameᶜ-left-inverse inv q)
renameᶜ-left-inverse inv (A !) =
  cong _! (renameᵗ-left-inverse inv A)
renameᶜ-left-inverse inv (A ？) =
  cong _？ (renameᵗ-left-inverse inv A)
renameᶜ-left-inverse inv (unseal α A) =
  cong₂ unseal (inv α) (renameᵗ-left-inverse inv A)
renameᶜ-left-inverse inv (seal A α) =
  cong₂ seal (renameᵗ-left-inverse inv A) (inv α)
renameᶜ-left-inverse inv (p ↦ q) =
  cong₂ _↦_ (renameᶜ-left-inverse inv p)
             (renameᶜ-left-inverse inv q)
renameᶜ-left-inverse inv (`∀ p) =
  cong `∀ (renameᶜ-left-inverse (RenameLeftInverse-ext inv) p)
renameᶜ-left-inverse inv (gen A p) =
  cong₂ gen (renameᵗ-left-inverse inv A)
             (renameᶜ-left-inverse (RenameLeftInverse-ext inv) p)
renameᶜ-left-inverse inv (inst B p) =
  cong₂ inst (renameᵗ-left-inverse inv B)
              (renameᶜ-left-inverse (RenameLeftInverse-ext inv) p)

open0-ext-suc-cancelᶜ :
  ∀ c →
  renameᶜ (singleRenameᵗ zero) (renameᶜ (extᵗ suc) c) ≡ c
open0-ext-suc-cancelᶜ = renameᶜ-left-inverse open0-ext-suc-inv

renameᶜ-pred-suc :
  ∀ c →
  renameᶜ predᵗ (⇑ᶜ c) ≡ c
renameᶜ-pred-suc = renameᶜ-left-inverse RenameLeftInverse-suc

renameᶜ-pred-ext-suc :
  ∀ c →
  renameᶜ predᵗ (renameᶜ (extᵗ suc) c) ≡ c
renameᶜ-pred-ext-suc =
  renameᶜ-left-inverse RenameLeftInverse-ext-suc-pred

renameᶜ-ext-suc-comm :
  ∀ ρ c →
  renameᶜ (extᵗ ρ) (⇑ᶜ c) ≡ ⇑ᶜ (renameᶜ ρ c)
renameᶜ-ext-suc-comm ρ c =
  trans (renameᶜ-compose suc (extᵗ ρ) c)
        (sym (renameᶜ-compose ρ suc c))

renameᶜ-ext-suc-suc :
  ∀ c →
  renameᶜ (extᵗ suc) (⇑ᶜ c) ≡ ⇑ᶜ (⇑ᶜ c)
renameᶜ-ext-suc-suc = renameᶜ-ext-suc-comm suc

renameᶜ-open-commute :
  ∀ ρ c α →
  renameᶜ ρ (c [ α ]ᶜ) ≡ renameᶜ (extᵗ ρ) c [ ρ α ]ᶜ
renameᶜ-open-commute ρ c α =
  trans (renameᶜ-compose (singleRenameᵗ α) ρ c)
    (trans
      (renameᶜ-cong env-eq c)
      (sym (renameᶜ-compose (extᵗ ρ) (singleRenameᵗ (ρ α)) c)))
  where
    env-eq :
      ∀ X →
      ρ (singleRenameᵗ α X) ≡ singleRenameᵗ (ρ α) (extᵗ ρ X)
    env-eq zero = refl
    env-eq (suc X) = refl

------------------------------------------------------------------------
-- Coercion typing under store/type-context weakening
------------------------------------------------------------------------

coercion-weakenᵐ :
  ∀ {μ Δ Δ′ Σ Σ′ c A B} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
  → μ ∣ Δ′ ∣ Σ′ ⊢ c ∶ A =⇒ B
coercion-weakenᵐ Δ≤Δ′ incl (cast-id hA ok) =
  cast-id (WfTy-weakenᵗ hA Δ≤Δ′) ok
coercion-weakenᵐ Δ≤Δ′ incl
    (cast-seal hA α∈Σ α-ok) =
  cast-seal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ) α-ok
coercion-weakenᵐ Δ≤Δ′ incl
    (cast-unseal hA α∈Σ α-ok) =
  cast-unseal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ) α-ok
coercion-weakenᵐ Δ≤Δ′ incl (cast-seq c⊢ d⊢) =
  cast-seq (coercion-weakenᵐ Δ≤Δ′ incl c⊢)
           (coercion-weakenᵐ Δ≤Δ′ incl d⊢)
coercion-weakenᵐ Δ≤Δ′ incl (cast-tag hG gG ok) =
  cast-tag (WfTy-weakenᵗ hG Δ≤Δ′) gG ok
coercion-weakenᵐ Δ≤Δ′ incl (cast-untag hH gH ok) =
  cast-untag (WfTy-weakenᵗ hH Δ≤Δ′) gH ok
coercion-weakenᵐ Δ≤Δ′ incl (cast-fun c⊢ d⊢) =
  cast-fun (coercion-weakenᵐ Δ≤Δ′ incl c⊢)
           (coercion-weakenᵐ Δ≤Δ′ incl d⊢)
coercion-weakenᵐ Δ≤Δ′ incl (cast-all c⊢) =
  cast-all
    (coercion-weakenᵐ
      (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc incl)
      c⊢)
coercion-weakenᵐ Δ≤Δ′ incl (cast-inst hB occ c⊢) =
  cast-inst
    (WfTy-weakenᵗ hB Δ≤Δ′)
    occ
    (coercion-weakenᵐ
      (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl))
      c⊢)
coercion-weakenᵐ Δ≤Δ′ incl (cast-gen hA occ c⊢) =
  cast-gen
    (WfTy-weakenᵗ hA Δ≤Δ′)
    occ
    (coercion-weakenᵐ
      (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc incl)
      c⊢)

coercion-weaken :
  ∀ {Δ Δ′ Σ Σ′ c A B} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ′ ∣ Σ′ ⊢ c ∶ A =⇒ B
coercion-weaken Δ≤Δ′ incl (μ , c⊢) =
  μ , coercion-weakenᵐ Δ≤Δ′ incl c⊢

coercion-weaken-suc :
  ∀ {Δ Σ c A B α C} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , C) ∷ Σ ⊢ c ∶ A =⇒ B
coercion-weaken-suc {Δ = Δ} c⊢ =
  coercion-weaken (n≤1+n Δ) StoreIncl-drop c⊢

------------------------------------------------------------------------
-- The inst/gen-bound dual swaps bound seals with bound tags
------------------------------------------------------------------------

dual-inst-example⊢ :
  zero ∣ [] ⊢ inst ★ (unseal zero ★) ∶ `∀ (＇ zero) =⇒ ★
dual-inst-example⊢ =
  tag-or-idᵈ ,
    cast-inst wf★ refl (cast-unseal wf★ (here refl) refl)

dual-inst-example-dual≡ :
  - inst ★ (unseal zero ★) ≡ gen ★ ((＇ zero) ？)
dual-inst-example-dual≡ = refl

dual-inst-example-dual⊢ :
  zero ∣ [] ⊢ - inst ★ (unseal zero ★) ∶ ★ =⇒ `∀ (＇ zero)
dual-inst-example-dual⊢ =
  tag-or-idᵈ ,
    cast-gen wf★ refl (cast-untag (wfVar z<s) (＇ zero) refl)

------------------------------------------------------------------------
-- Coercion duality under type renaming
------------------------------------------------------------------------

DualActionRename : Renameᵗ → DualActionEnv → DualActionEnv → Set
DualActionRename ρ η θ = ∀ X → θ (ρ X) ≡ η X

DualActionRename-ext :
  ∀ {ρ η θ} →
  DualActionRename ρ η θ →
  DualActionRename (extᵗ ρ) (extᵃ η) (extᵃ θ)
DualActionRename-ext rel zero = refl
DualActionRename-ext rel (suc X) = rel X

DualActionRename-gen :
  ∀ {ρ η θ} →
  DualActionRename ρ η θ →
  DualActionRename (extᵗ ρ) (genᵃ η) (genᵃ θ)
DualActionRename-gen rel zero = refl
DualActionRename-gen rel (suc X) = rel X

DualActionRename-inst :
  ∀ {ρ η θ} →
  DualActionRename ρ η θ →
  DualActionRename (extᵗ ρ) (instᵃ η) (instᵃ θ)
DualActionRename-inst rel zero = refl
DualActionRename-inst rel (suc X) = rel X

renameᶜ-dualTag :
  ∀ {ρ η θ} →
  DualActionRename ρ η θ →
  ∀ G → renameᶜ ρ (dualTag η G) ≡ dualTag θ (renameᵗ ρ G)
renameᶜ-dualTag {ρ = ρ} {η = η} {θ = θ} rel (＇ α)
    with η α | θ (ρ α) | rel α
renameᶜ-dualTag rel (＇ α) | normal | .normal | refl = refl
renameᶜ-dualTag rel (＇ α) | tag-to-seal | .tag-to-seal | refl = refl
renameᶜ-dualTag rel (＇ α) | seal-to-tag | .seal-to-tag | refl = refl
renameᶜ-dualTag rel (‵ ι) = refl
renameᶜ-dualTag rel ★ = refl
renameᶜ-dualTag rel (A ⇒ B) = refl
renameᶜ-dualTag rel (`∀ A) = refl

renameᶜ-dualUntag :
  ∀ {ρ η θ} →
  DualActionRename ρ η θ →
  ∀ G → renameᶜ ρ (dualUntag η G) ≡ dualUntag θ (renameᵗ ρ G)
renameᶜ-dualUntag {ρ = ρ} {η = η} {θ = θ} rel (＇ α)
    with η α | θ (ρ α) | rel α
renameᶜ-dualUntag rel (＇ α) | normal | .normal | refl = refl
renameᶜ-dualUntag rel (＇ α) | tag-to-seal | .tag-to-seal | refl = refl
renameᶜ-dualUntag rel (＇ α) | seal-to-tag | .seal-to-tag | refl = refl
renameᶜ-dualUntag rel (‵ ι) = refl
renameᶜ-dualUntag rel ★ = refl
renameᶜ-dualUntag rel (A ⇒ B) = refl
renameᶜ-dualUntag rel (`∀ A) = refl

renameᶜ-dualSeal :
  ∀ {ρ η θ} →
  DualActionRename ρ η θ →
  ∀ A α →
  renameᶜ ρ (dualSeal η A α) ≡
    dualSeal θ (renameᵗ ρ A) (ρ α)
renameᶜ-dualSeal {ρ = ρ} {η = η} {θ = θ} rel A α
    with η α | θ (ρ α) | rel α
renameᶜ-dualSeal rel A α | normal | .normal | refl = refl
renameᶜ-dualSeal rel A α | tag-to-seal | .tag-to-seal | refl = refl
renameᶜ-dualSeal rel A α | seal-to-tag | .seal-to-tag | refl = refl

renameᶜ-dualUnseal :
  ∀ {ρ η θ} →
  DualActionRename ρ η θ →
  ∀ α A →
  renameᶜ ρ (dualUnseal η α A) ≡
    dualUnseal θ (ρ α) (renameᵗ ρ A)
renameᶜ-dualUnseal {ρ = ρ} {η = η} {θ = θ} rel α A
    with η α | θ (ρ α) | rel α
renameᶜ-dualUnseal rel α A | normal | .normal | refl = refl
renameᶜ-dualUnseal rel α A | tag-to-seal | .tag-to-seal | refl = refl
renameᶜ-dualUnseal rel α A | seal-to-tag | .seal-to-tag | refl = refl

renameᶜ-dual :
  ∀ {ρ η θ} →
  DualActionRename ρ η θ →
  ∀ c → renameᶜ ρ (dual η c) ≡ dual θ (renameᶜ ρ c)
renameᶜ-dual rel (id A) = refl
renameᶜ-dual rel (c ︔ d) =
  cong₂ _︔_ (renameᶜ-dual rel d) (renameᶜ-dual rel c)
renameᶜ-dual rel (c ↦ d) =
  cong₂ _↦_ (renameᶜ-dual rel c) (renameᶜ-dual rel d)
renameᶜ-dual {ρ = ρ} {η = η} {θ = θ} rel (`∀ c) =
  cong `∀
    (renameᶜ-dual {ρ = extᵗ ρ} {η = extᵃ η} {θ = extᵃ θ}
      (DualActionRename-ext rel) c)
renameᶜ-dual {ρ = ρ} {η = η} {θ = θ} rel (G !) =
  renameᶜ-dualTag {ρ = ρ} {η = η} {θ = θ} rel G
renameᶜ-dual {ρ = ρ} {η = η} {θ = θ} rel (G ？) =
  renameᶜ-dualUntag {ρ = ρ} {η = η} {θ = θ} rel G
renameᶜ-dual {ρ = ρ} {η = η} {θ = θ} rel (seal A α) =
  renameᶜ-dualSeal {ρ = ρ} {η = η} {θ = θ} rel A α
renameᶜ-dual {ρ = ρ} {η = η} {θ = θ} rel (unseal α A) =
  renameᶜ-dualUnseal {ρ = ρ} {η = η} {θ = θ} rel α A
renameᶜ-dual {ρ = ρ} {η = η} {θ = θ} rel (gen A c) =
  cong (inst (renameᵗ ρ A))
    (renameᶜ-dual {ρ = extᵗ ρ} {η = genᵃ η} {θ = genᵃ θ}
      (DualActionRename-gen rel) c)
renameᶜ-dual {ρ = ρ} {η = η} {θ = θ} rel (inst B c) =
  cong (gen (renameᵗ ρ B))
    (renameᶜ-dual {ρ = extᵗ ρ} {η = instᵃ η} {θ = instᵃ θ}
      (DualActionRename-inst rel) c)

renameᶜ-dual-normal :
  ∀ ρ c →
  renameᶜ ρ (- c) ≡ - renameᶜ ρ c
renameᶜ-dual-normal ρ = renameᶜ-dual (λ X → refl)

------------------------------------------------------------------------
-- Coercion typing under type renaming
------------------------------------------------------------------------

ModeRename : Renameᵗ → ModeEnv → ModeEnv → Set
ModeRename ρ μ ν = ∀ X → mode≤ (μ X) (ν (ρ X)) ≡ true

ModeRename-ext :
  ∀ {ρ μ ν} →
  ModeRename ρ μ ν →
  ModeRename (extᵗ ρ) (extᵈ μ) (extᵈ ν)
ModeRename-ext rel zero = refl
ModeRename-ext rel (suc X) = rel X

ModeRename-gen :
  ∀ {ρ μ ν} →
  ModeRename ρ μ ν →
  ModeRename (extᵗ ρ) (genᵈ μ) (genᵈ ν)
ModeRename-gen rel zero = refl
ModeRename-gen rel (suc X) = rel X

ModeRename-inst :
  ∀ {ρ μ ν} →
  ModeRename ρ μ ν →
  ModeRename (extᵗ ρ) (instᵈ μ) (instᵈ ν)
ModeRename-inst rel zero = refl
ModeRename-inst rel (suc X) = rel X

ScopedModeRename : TyCtx → Renameᵗ → ModeEnv → ModeEnv → Set
ScopedModeRename Δ ρ μ ν =
  ∀ {X} → X < Δ → mode≤ (μ X) (ν (ρ X)) ≡ true

ScopedModeRename-ext :
  ∀ {Δ ρ μ ν} →
  ScopedModeRename Δ ρ μ ν →
  ScopedModeRename (suc Δ) (extᵗ ρ) (extᵈ μ) (extᵈ ν)
ScopedModeRename-ext rel {zero} z<s = refl
ScopedModeRename-ext rel {suc X} (s<s X<Δ) = rel X<Δ

ScopedModeRename-gen :
  ∀ {Δ ρ μ ν} →
  ScopedModeRename Δ ρ μ ν →
  ScopedModeRename (suc Δ) (extᵗ ρ) (genᵈ μ) (genᵈ ν)
ScopedModeRename-gen rel {zero} z<s = refl
ScopedModeRename-gen rel {suc X} (s<s X<Δ) = rel X<Δ

ScopedModeRename-inst :
  ∀ {Δ ρ μ ν} →
  ScopedModeRename Δ ρ μ ν →
  ScopedModeRename (suc Δ) (extᵗ ρ) (instᵈ μ) (instᵈ ν)
ScopedModeRename-inst rel {zero} z<s = refl
ScopedModeRename-inst rel {suc X} (s<s X<Δ) = rel X<Δ

mode≤-id :
  ∀ {m n} →
  mode≤ m n ≡ true →
  idModeAllowed m ≡ true →
  idModeAllowed n ≡ true
mode≤-id {id-only} {id-only} rel ok = refl
mode≤-id {id-only} {tag-or-id} rel ok = refl
mode≤-id {id-only} {seal-or-id} rel ok = refl
mode≤-id {tag-or-id} {id-only} () ok
mode≤-id {tag-or-id} {tag-or-id} rel ok = refl
mode≤-id {tag-or-id} {seal-or-id} () ok
mode≤-id {seal-or-id} {id-only} () ok
mode≤-id {seal-or-id} {tag-or-id} () ok
mode≤-id {seal-or-id} {seal-or-id} rel ok = refl

mode≤-tag :
  ∀ {m n} →
  mode≤ m n ≡ true →
  tagModeAllowed m ≡ true →
  tagModeAllowed n ≡ true
mode≤-tag {id-only} {id-only} rel ()
mode≤-tag {id-only} {tag-or-id} rel ()
mode≤-tag {id-only} {seal-or-id} rel ()
mode≤-tag {tag-or-id} {id-only} () ok
mode≤-tag {tag-or-id} {tag-or-id} rel ok = refl
mode≤-tag {tag-or-id} {seal-or-id} () ok
mode≤-tag {seal-or-id} {id-only} () ok
mode≤-tag {seal-or-id} {tag-or-id} () ok
mode≤-tag {seal-or-id} {seal-or-id} rel ()

mode≤-seal :
  ∀ {m n} →
  mode≤ m n ≡ true →
  sealModeAllowed m ≡ true →
  sealModeAllowed n ≡ true
mode≤-seal {id-only} {id-only} rel ()
mode≤-seal {id-only} {tag-or-id} rel ()
mode≤-seal {id-only} {seal-or-id} rel ()
mode≤-seal {tag-or-id} {id-only} () ok
mode≤-seal {tag-or-id} {tag-or-id} rel ()
mode≤-seal {tag-or-id} {seal-or-id} () ok
mode≤-seal {seal-or-id} {id-only} () ok
mode≤-seal {seal-or-id} {tag-or-id} () ok
mode≤-seal {seal-or-id} {seal-or-id} rel ok = refl

modeRename-idTyAllowed :
  ∀ {ρ μ ν A} →
  ModeRename ρ μ ν →
  idTyAllowed μ A ≡ true →
  idTyAllowed ν (renameᵗ ρ A) ≡ true
modeRename-idTyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = ＇ α} rel ok =
  mode≤-id (rel α) ok
modeRename-idTyAllowed {A = ‵ ι} rel ok = refl
modeRename-idTyAllowed {A = ★} rel ok = refl
modeRename-idTyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = A ⇒ B} rel ok
    rewrite modeRename-idTyAllowed {ρ = ρ} {μ = μ} {ν = ν}
              {A = A} rel (∧-trueˡ ok)
          | modeRename-idTyAllowed {ρ = ρ} {μ = μ} {ν = ν}
              {A = B} rel (∧-trueʳ ok) = refl
modeRename-idTyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = `∀ A} rel ok =
  modeRename-idTyAllowed
    {ρ = extᵗ ρ} {μ = extᵈ μ} {ν = extᵈ ν} {A = A}
    (ModeRename-ext rel) ok

modeRename-tagTyAllowed :
  ∀ {ρ μ ν G} →
  ModeRename ρ μ ν →
  tagTyAllowed μ G ≡ true →
  tagTyAllowed ν (renameᵗ ρ G) ≡ true
modeRename-tagTyAllowed {ρ = ρ} {μ = μ} {ν = ν} {G = ＇ α} rel ok =
  mode≤-tag (rel α) ok
modeRename-tagTyAllowed {G = ‵ ι} rel ok = refl
modeRename-tagTyAllowed {G = ★} rel ok = refl
modeRename-tagTyAllowed {G = A ⇒ B} rel ok = refl
modeRename-tagTyAllowed {ρ = ρ} {μ = μ} {ν = ν} {G = `∀ A} rel ok =
  refl

modeRename-sealModeAllowed :
  ∀ {ρ μ ν α} →
  ModeRename ρ μ ν →
  sealModeAllowed (μ α) ≡ true →
  sealModeAllowed (ν (ρ α)) ≡ true
modeRename-sealModeAllowed {α = α} rel ok =
  mode≤-seal (rel α) ok

scopedModeRename-idTyAllowed :
  ∀ {Δ ρ μ ν A} →
  WfTy Δ A →
  ScopedModeRename Δ ρ μ ν →
  idTyAllowed μ A ≡ true →
  idTyAllowed ν (renameᵗ ρ A) ≡ true
scopedModeRename-idTyAllowed (wfVar X<Δ) rel ok =
  mode≤-id (rel X<Δ) ok
scopedModeRename-idTyAllowed wfBase rel ok = refl
scopedModeRename-idTyAllowed wf★ rel ok = refl
scopedModeRename-idTyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = A ⇒ B}
    (wf⇒ hA hB) rel ok
    rewrite scopedModeRename-idTyAllowed
              {ρ = ρ} {μ = μ} {ν = ν} hA rel (∧-trueˡ ok)
          | scopedModeRename-idTyAllowed
              {ρ = ρ} {μ = μ} {ν = ν} hB rel (∧-trueʳ ok) = refl
scopedModeRename-idTyAllowed (wf∀ hA) rel ok =
  scopedModeRename-idTyAllowed hA (ScopedModeRename-ext rel) ok

scopedModeRename-tagTyAllowed :
  ∀ {Δ ρ μ ν G} →
  WfTy Δ G →
  ScopedModeRename Δ ρ μ ν →
  tagTyAllowed μ G ≡ true →
  tagTyAllowed ν (renameᵗ ρ G) ≡ true
scopedModeRename-tagTyAllowed (wfVar X<Δ) rel ok =
  mode≤-tag (rel X<Δ) ok
scopedModeRename-tagTyAllowed wfBase rel ok = refl
scopedModeRename-tagTyAllowed wf★ rel ok = refl
scopedModeRename-tagTyAllowed (wf⇒ hA hB) rel ok = refl
scopedModeRename-tagTyAllowed (wf∀ hA) rel ok = refl

scopedModeRename-sealModeAllowed :
  ∀ {Δ ρ μ ν α} →
  ScopedModeRename Δ ρ μ ν →
  α < Δ →
  sealModeAllowed (μ α) ≡ true →
  sealModeAllowed (ν (ρ α)) ≡ true
scopedModeRename-sealModeAllowed rel α<Δ ok =
  mode≤-seal (rel α<Δ) ok

ModeIncl-ext :
  ∀ {μ ν} →
  ModeIncl μ ν →
  ModeIncl (extᵈ μ) (extᵈ ν)
ModeIncl-ext incl zero = refl
ModeIncl-ext incl (suc X) = incl X

ModeIncl-gen :
  ∀ {μ ν} →
  ModeIncl μ ν →
  ModeIncl (genᵈ μ) (genᵈ ν)
ModeIncl-gen incl zero = refl
ModeIncl-gen incl (suc X) = incl X

ModeIncl-inst :
  ∀ {μ ν} →
  ModeIncl μ ν →
  ModeIncl (instᵈ μ) (instᵈ ν)
ModeIncl-inst incl zero = refl
ModeIncl-inst incl (suc X) = incl X

modeIncl-idTyAllowed :
  ∀ {μ ν A} →
  ModeIncl μ ν →
  idTyAllowed μ A ≡ true →
  idTyAllowed ν A ≡ true
modeIncl-idTyAllowed {μ = μ} {ν = ν} {A = A} incl ok =
  subst
    (λ T → idTyAllowed ν T ≡ true)
    (renameᵗ-id A)
    (modeRename-idTyAllowed
      {ρ = λ X → X} {μ = μ} {ν = ν} {A = A} incl ok)

modeIncl-tagTyAllowed :
  ∀ {μ ν G} →
  ModeIncl μ ν →
  tagTyAllowed μ G ≡ true →
  tagTyAllowed ν G ≡ true
modeIncl-tagTyAllowed {μ = μ} {ν = ν} {G = G} incl ok =
  subst
    (λ T → tagTyAllowed ν T ≡ true)
    (renameᵗ-id G)
    (modeRename-tagTyAllowed
      {ρ = λ X → X} {μ = μ} {ν = ν} {G = G} incl ok)

modeIncl-sealModeAllowed :
  ∀ {μ ν α} →
  ModeIncl μ ν →
  sealModeAllowed (μ α) ≡ true →
  sealModeAllowed (ν α) ≡ true
modeIncl-sealModeAllowed {μ = μ} {ν = ν} {α = α} incl ok =
  modeRename-sealModeAllowed
    {ρ = λ X → X} {μ = μ} {ν = ν} {α = α} incl ok

coercion-mode-relax :
  ∀ {μ ν Δ Σ c A B} →
  ModeIncl μ ν →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  ν ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
coercion-mode-relax incl (cast-id {A = A} hA ok) =
  cast-id hA (modeIncl-idTyAllowed {A = A} incl ok)
coercion-mode-relax incl
    (cast-seal {α = α} hA α∈Σ α-ok) =
  cast-seal hA α∈Σ
    (modeIncl-sealModeAllowed {α = α} incl α-ok)
coercion-mode-relax incl
    (cast-unseal {α = α} hA α∈Σ α-ok) =
  cast-unseal hA α∈Σ
    (modeIncl-sealModeAllowed {α = α} incl α-ok)
coercion-mode-relax incl (cast-seq c⊢ d⊢) =
  cast-seq (coercion-mode-relax incl c⊢)
           (coercion-mode-relax incl d⊢)
coercion-mode-relax incl (cast-tag {G = G} hG gG ok) =
  cast-tag hG gG (modeIncl-tagTyAllowed {G = G} incl ok)
coercion-mode-relax incl (cast-untag {H = H} hH gH ok) =
  cast-untag hH gH (modeIncl-tagTyAllowed {G = H} incl ok)
coercion-mode-relax incl (cast-fun c⊢ d⊢) =
  cast-fun (coercion-mode-relax incl c⊢)
           (coercion-mode-relax incl d⊢)
coercion-mode-relax incl (cast-all c⊢) =
  cast-all (coercion-mode-relax (ModeIncl-ext incl) c⊢)
coercion-mode-relax incl (cast-inst hB occ c⊢) =
  cast-inst hB occ
    (coercion-mode-relax (ModeIncl-inst incl) c⊢)
coercion-mode-relax incl (cast-gen hA occ c⊢) =
  cast-gen hA occ
    (coercion-mode-relax (ModeIncl-gen incl) c⊢)

coercion-renameᵗᵐ :
  ∀ {Δ Δ′ Σ c A B ρ μ ν} →
  TyRenameWf Δ Δ′ ρ →
  ModeRename ρ μ ν →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  ν ∣ Δ′ ∣ renameStoreᵗ ρ Σ ⊢ renameᶜ ρ c
    ∶ renameᵗ ρ A =⇒ renameᵗ ρ B
coercion-renameᵗᵐ hρ rel (cast-id {A = A} hA ok) =
  cast-id (renameᵗ-preserves-WfTy hA hρ)
    (modeRename-idTyAllowed {A = A} rel ok)
coercion-renameᵗᵐ {ρ = ρ} {μ = μ} {ν = ν} hρ rel
    (cast-seal {α = α} hA α∈Σ α-ok) =
  cast-seal
    (renameᵗ-preserves-WfTy hA hρ)
    (∈-renameStoreᵗ _ α∈Σ)
    (modeRename-sealModeAllowed
      {ρ = ρ} {μ = μ} {ν = ν} {α = α} rel α-ok)
coercion-renameᵗᵐ {ρ = ρ} {μ = μ} {ν = ν} hρ rel
    (cast-unseal {α = α} hA α∈Σ α-ok) =
  cast-unseal
    (renameᵗ-preserves-WfTy hA hρ)
    (∈-renameStoreᵗ _ α∈Σ)
    (modeRename-sealModeAllowed
      {ρ = ρ} {μ = μ} {ν = ν} {α = α} rel α-ok)
coercion-renameᵗᵐ hρ rel (cast-seq c⊢ d⊢) =
  cast-seq (coercion-renameᵗᵐ hρ rel c⊢)
           (coercion-renameᵗᵐ hρ rel d⊢)
coercion-renameᵗᵐ hρ rel (cast-tag {G = G} hG gG ok) =
  cast-tag
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-ground _ gG)
    (modeRename-tagTyAllowed {G = G} rel ok)
coercion-renameᵗᵐ hρ rel (cast-untag {H = H} hH gH ok) =
  cast-untag
    (renameᵗ-preserves-WfTy hH hρ)
    (renameᵗ-ground _ gH)
    (modeRename-tagTyAllowed {G = H} rel ok)
coercion-renameᵗᵐ hρ rel (cast-fun c⊢ d⊢) =
  cast-fun (coercion-renameᵗᵐ hρ rel c⊢)
           (coercion-renameᵗᵐ hρ rel d⊢)
coercion-renameᵗᵐ {ρ = ρ} hρ rel
    (cast-all {A = A} {B = B} c⊢) =
  cast-all
    (subst
      (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
      (renameStoreᵗ-ext-suc-comm ρ _)
      (coercion-renameᵗᵐ (TyRenameWf-ext hρ)
        (ModeRename-ext rel) c⊢))
coercion-renameᵗᵐ {ρ = ρ} hρ rel
    (cast-inst {A = A} {B = B} hB occ c⊢) =
  cast-inst
    (renameᵗ-preserves-WfTy hB hρ)
    (trans (occurs-zero-rename-ext ρ A) occ)
    (subst
      (λ T → _ ∣ _ ∣ _ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ T)
      (renameᵗ-ext-suc-comm ρ B)
      (subst
        (λ Σ′ → _ ∣ _ ∣ (0 , ★) ∷ Σ′
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (coercion-renameᵗᵐ (TyRenameWf-ext hρ)
          (ModeRename-inst rel) c⊢)))
coercion-renameᵗᵐ {ρ = ρ} hρ rel
    (cast-gen {A = A} {B = B} hA occ c⊢) =
  cast-gen
    (renameᵗ-preserves-WfTy hA hρ)
    (trans (occurs-zero-rename-ext ρ B) occ)
    (subst
      (λ T → _ ∣ _ ∣ _ ⊢ renameᶜ (extᵗ ρ) _ ∶ T =⇒ _)
      (renameᵗ-ext-suc-comm ρ A)
      (subst
        (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (coercion-renameᵗᵐ (TyRenameWf-ext hρ)
          (ModeRename-gen rel) c⊢)))

coercion-renameᵗᵐ-scoped :
  ∀ {Δ Δ′ Σ c A B ρ μ ν} →
  StoreWfAt Δ Σ →
  TyRenameWf Δ Δ′ ρ →
  ScopedModeRename Δ ρ μ ν →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  ν ∣ Δ′ ∣ renameStoreᵗ ρ Σ ⊢ renameᶜ ρ c
    ∶ renameᵗ ρ A =⇒ renameᵗ ρ B
coercion-renameᵗᵐ-scoped wfΣ hρ rel (cast-id {A = A} hA ok) =
  cast-id (renameᵗ-preserves-WfTy hA hρ)
    (scopedModeRename-idTyAllowed hA rel ok)
coercion-renameᵗᵐ-scoped {Δ = Δ} {ρ = ρ} {μ = μ} {ν = ν} wfΣ hρ rel
    (cast-seal {α = α} hA α∈Σ α-ok) =
  cast-seal
    (renameᵗ-preserves-WfTy hA hρ)
    (∈-renameStoreᵗ _ α∈Σ)
    (scopedModeRename-sealModeAllowed
      {Δ = Δ} {ρ = ρ} {μ = μ} {ν = ν} {α = α}
      rel (bound wfΣ α∈Σ) α-ok)
coercion-renameᵗᵐ-scoped {Δ = Δ} {ρ = ρ} {μ = μ} {ν = ν} wfΣ hρ rel
    (cast-unseal {α = α} hA α∈Σ α-ok) =
  cast-unseal
    (renameᵗ-preserves-WfTy hA hρ)
    (∈-renameStoreᵗ _ α∈Σ)
    (scopedModeRename-sealModeAllowed
      {Δ = Δ} {ρ = ρ} {μ = μ} {ν = ν} {α = α}
      rel (bound wfΣ α∈Σ) α-ok)
coercion-renameᵗᵐ-scoped wfΣ hρ rel (cast-seq c⊢ d⊢) =
  cast-seq (coercion-renameᵗᵐ-scoped wfΣ hρ rel c⊢)
           (coercion-renameᵗᵐ-scoped wfΣ hρ rel d⊢)
coercion-renameᵗᵐ-scoped wfΣ hρ rel (cast-tag {G = G} hG gG ok) =
  cast-tag
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-ground _ gG)
    (scopedModeRename-tagTyAllowed hG rel ok)
coercion-renameᵗᵐ-scoped wfΣ hρ rel (cast-untag {H = H} hH gH ok) =
  cast-untag
    (renameᵗ-preserves-WfTy hH hρ)
    (renameᵗ-ground _ gH)
    (scopedModeRename-tagTyAllowed hH rel ok)
coercion-renameᵗᵐ-scoped wfΣ hρ rel (cast-fun c⊢ d⊢) =
  cast-fun (coercion-renameᵗᵐ-scoped wfΣ hρ rel c⊢)
           (coercion-renameᵗᵐ-scoped wfΣ hρ rel d⊢)
coercion-renameᵗᵐ-scoped {ρ = ρ} wfΣ hρ rel
    (cast-all {A = A} {B = B} c⊢) =
  cast-all
    (subst
      (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
      (renameStoreᵗ-ext-suc-comm ρ _)
      (coercion-renameᵗᵐ-scoped
        (StoreWfAt-⟰ᵗ wfΣ)
        (TyRenameWf-ext hρ)
        (ScopedModeRename-ext rel)
        c⊢))
coercion-renameᵗᵐ-scoped {ρ = ρ} wfΣ hρ rel
    (cast-inst {A = A} {B = B} hB occ c⊢) =
  cast-inst
    (renameᵗ-preserves-WfTy hB hρ)
    (trans (occurs-zero-rename-ext ρ A) occ)
    (subst
      (λ T → _ ∣ _ ∣ _ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ T)
      (renameᵗ-ext-suc-comm ρ B)
      (subst
        (λ Σ′ → _ ∣ _ ∣ (0 , ★) ∷ Σ′
          ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (coercion-renameᵗᵐ-scoped
          (StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ wfΣ))
          (TyRenameWf-ext hρ)
          (ScopedModeRename-inst rel)
          c⊢)))
coercion-renameᵗᵐ-scoped {ρ = ρ} wfΣ hρ rel
    (cast-gen {A = A} {B = B} hA occ c⊢) =
  cast-gen
    (renameᵗ-preserves-WfTy hA hρ)
    (trans (occurs-zero-rename-ext ρ B) occ)
    (subst
      (λ T → _ ∣ _ ∣ _ ⊢ renameᶜ (extᵗ ρ) _ ∶ T =⇒ _)
      (renameᵗ-ext-suc-comm ρ A)
      (subst
        (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (coercion-renameᵗᵐ-scoped
          (StoreWfAt-⟰ᵗ wfΣ)
          (TyRenameWf-ext hρ)
          (ScopedModeRename-gen rel)
          c⊢)))

openᵈ : ModeEnv → TyVar → ModeEnv
openᵈ μ α X with X ≟ α
openᵈ μ α X | yes eq = μ zero
openᵈ μ α X | no neq = μ (suc X)

singleRenameᵗ-Wf≤ :
  ∀ {Δ Δ′ α} →
  Δ ≤ Δ′ →
  α < Δ′ →
  TyRenameWf (suc Δ) Δ′ (singleRenameᵗ α)
singleRenameᵗ-Wf≤ Δ≤Δ′ α<Δ′ {zero} z<s = α<Δ′
singleRenameᵗ-Wf≤ Δ≤Δ′ α<Δ′ {suc X} (s<s X<Δ) =
  <-≤-trans X<Δ Δ≤Δ′

openᵈ-scoped :
  ∀ {Δ α μ} →
  Δ ≤ α →
  ScopedModeRename (suc Δ) (singleRenameᵗ α) μ (openᵈ μ α)
openᵈ-scoped {α = α} {μ = μ} Δ≤α {zero} z<s
    with α ≟ α
openᵈ-scoped {α = α} {μ = μ} Δ≤α {zero} z<s
    | yes refl =
  modeIncl-refl {μ = μ} zero
openᵈ-scoped {α = α} Δ≤α {zero} z<s
    | no α≢α =
  ⊥-elim (α≢α refl)
openᵈ-scoped {Δ = Δ} {α = α} {μ = μ} Δ≤α {suc X} (s<s X<Δ)
    with X ≟ α
openᵈ-scoped {Δ = Δ} {α = α} {μ = μ} Δ≤α {suc X} (s<s X<Δ)
    | yes X≡α =
  ⊥-elim
    (<-irrefl refl
      (subst (λ Y → Y < α) X≡α (<-≤-trans X<Δ Δ≤α)))
openᵈ-scoped {Δ = Δ} {α = α} {μ = μ} Δ≤α {suc X} (s<s X<Δ)
    | no X≢α =
  modeIncl-refl {μ = μ} (suc X)

renameStoreᵗ-openν-cancel :
  ∀ α Σ A →
  renameStoreᵗ (singleRenameᵗ α) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ) ≡
  (α , A) ∷ Σ
renameStoreᵗ-openν-cancel α Σ A =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵗ-single-suc-cancel α A))
    (renameStoreᵗ-single-suc-cancel α Σ)

coercion-open-freshᵐ :
  ∀ {μ Δ Δ′ Σ c A C B α} →
  StoreWfAt Δ Σ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  α ∉ domˢ Σ →
  WfTy Δ A →
  μ ∣ suc Δ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ ⊢ c ∶ C =⇒ ⇑ᵗ B →
  openᵈ μ α ∣ Δ′ ∣ (α , A) ∷ Σ ⊢ c [ α ]ᶜ
    ∶ C [ α ]ᴿ =⇒ B
coercion-open-freshᵐ {μ = μ} {Δ = Δ} {Δ′ = Δ′} {Σ = Σ}
    {c = c} {A = A} {C = C} {B = B} {α = α}
    wfΣ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ hA c⊢ =
  subst
    (λ T → openᵈ μ α ∣ Δ′ ∣ (α , A) ∷ Σ ⊢ c [ α ]ᶜ
      ∶ C [ α ]ᴿ =⇒ T)
    (renameᵗ-single-suc-cancel α B)
    opened-store
  where
    sourceWf : StoreWfAt (suc Δ) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
    sourceWf =
      StoreWfAt-cons
        z<s
        (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
        (StoreWfAt-⟰ᵗ wfΣ)

    opened-renamed :
      openᵈ μ α ∣ Δ′
      ∣ renameStoreᵗ (singleRenameᵗ α) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
      ⊢ c [ α ]ᶜ ∶ C [ α ]ᴿ
      =⇒ renameᵗ (singleRenameᵗ α) (⇑ᵗ B)
    opened-renamed =
      coercion-renameᵗᵐ-scoped
        sourceWf
        (singleRenameᵗ-Wf≤ Δ≤Δ′ α<Δ′)
        (openᵈ-scoped Δ≤α)
        c⊢

    opened-store :
      openᵈ μ α ∣ Δ′ ∣ (α , A) ∷ Σ ⊢ c [ α ]ᶜ ∶ C [ α ]ᴿ
      =⇒ renameᵗ (singleRenameᵗ α) (⇑ᵗ B)
    opened-store =
      subst
        (λ Σ′ → openᵈ μ α ∣ Δ′ ∣ Σ′ ⊢ c [ α ]ᶜ
          ∶ C [ α ]ᴿ =⇒ renameᵗ (singleRenameᵗ α) (⇑ᵗ B))
        (renameStoreᵗ-openν-cancel α Σ A)
        opened-renamed

coercion-open-fresh :
  ∀ {μ Δ Δ′ Σ c A C B α} →
  StoreWfAt Δ Σ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  α ∉ domˢ Σ →
  WfTy Δ A →
  μ ∣ suc Δ ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ ⊢ c ∶ C =⇒ ⇑ᵗ B →
  Δ′ ∣ (α , A) ∷ Σ ⊢ c [ α ]ᶜ ∶ C [ α ]ᴿ =⇒ B
coercion-open-fresh {μ = μ} {α = α}
    wfΣ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ hA c⊢ =
  openᵈ μ α ,
    coercion-open-freshᵐ
      wfΣ Δ≤Δ′ Δ≤α α<Δ′ α∉Σ hA c⊢

coercion-open-store-freshᵐ :
  ∀ {μ Δ Δ′ Σ c A B α Aν} →
  StoreWfAt Δ Σ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  openᵈ μ α ∣ Δ′ ∣ (α , Aν) ∷ Σ ⊢ c [ α ]ᶜ
    ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open-store-freshᵐ {μ = μ} {Δ′ = Δ′} {Σ = Σ}
    {c = c} {A = A} {B = B} {α = α} {Aν = Aν}
    wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢ =
  coercion-weakenᵐ ≤-refl StoreIncl-drop opened-store
  where
    opened-renamed :
      openᵈ μ α ∣ Δ′ ∣ renameStoreᵗ (singleRenameᵗ α) (⟰ᵗ Σ)
      ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
    opened-renamed =
      coercion-renameᵗᵐ-scoped
        (StoreWfAt-⟰ᵗ wfΣ)
        (singleRenameᵗ-Wf≤ Δ≤Δ′ α<Δ′)
        (openᵈ-scoped Δ≤α)
        c⊢

    opened-store :
      openᵈ μ α ∣ Δ′ ∣ Σ
      ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
    opened-store =
      subst
        (λ Σ′ → openᵈ μ α ∣ Δ′ ∣ Σ′ ⊢ c [ α ]ᶜ
          ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ)
        (renameStoreᵗ-single-suc-cancel α Σ)
        opened-renamed

coercion-open-store-fresh :
  ∀ {μ Δ Δ′ Σ c A B α Aν} →
  StoreWfAt Δ Σ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  Δ′ ∣ (α , Aν) ∷ Σ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open-store-fresh {μ = μ} {α = α}
    wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢ =
  openᵈ μ α ,
    coercion-open-store-freshᵐ wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢

coercion-open-shift-freshᵐ :
  ∀ {μ Δ Δ′ Σ c A B α Aν} →
  StoreWfAt Δ Σ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′
  → μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ ⇑ᵗ A =⇒ B
  → openᵈ μ α ∣ Δ′ ∣ (α , Aν) ∷ Σ ⊢ c [ α ]ᶜ ∶ A =⇒ B [ α ]ᴿ
coercion-open-shift-freshᵐ {μ = μ} {Δ = Δ} {Δ′ = Δ′}
    {Σ = Σ} {c = c} {A = A} {B = B} {α = α} {Aν = Aν}
    wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢ =
  subst
    (λ T → openᵈ μ α ∣ Δ′ ∣ (α , Aν) ∷ Σ ⊢ c [ α ]ᶜ
      ∶ T =⇒ B [ α ]ᴿ)
    (renameᵗ-single-suc-cancel α A)
    (coercion-open-store-freshᵐ wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢)

coercion-open-shift-fresh :
  ∀ {μ Δ Δ′ Σ c A B α Aν} →
  StoreWfAt Δ Σ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ ⇑ᵗ A =⇒ B
    --------------------------------------------
  → Δ′ ∣ (α , Aν) ∷ Σ ⊢ c [ α ]ᶜ ∶ A =⇒ B [ α ]ᴿ
coercion-open-shift-fresh {μ = μ} {α = α}
    wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢ =
  openᵈ μ α ,
    coercion-open-shift-freshᵐ wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢

------------------------------------------------------------------------
-- Coercion duality flips typed endpoints
------------------------------------------------------------------------

data ModeAction : Mode → DualAction → Mode → Set where
  dma-id : ModeAction id-only normal id-only
  dma-tag : ModeAction tag-or-id normal tag-or-id
  dma-seal : ModeAction seal-or-id normal seal-or-id
  dma-tag-seal : ModeAction tag-or-id tag-to-seal seal-or-id
  dma-seal-tag : ModeAction seal-or-id seal-to-tag tag-or-id

DualActionOk : ModeEnv → DualActionEnv → ModeEnv → Set
DualActionOk μ η ν = ∀ X → ModeAction (μ X) (η X) (ν X)

dualActionModeᵈ : Mode → DualAction
dualActionModeᵈ id-only = normal
dualActionModeᵈ tag-or-id = normal
dualActionModeᵈ seal-or-id = normal

dualActionᵈ : ModeEnv → DualActionEnv
dualActionᵈ μ X = dualActionModeᵈ (μ X)

dualᵈ : ModeEnv → ModeEnv
dualᵈ μ X = μ X

dualActionOkᵈ : ∀ {μ} → DualActionOk μ (dualActionᵈ μ) (dualᵈ μ)
dualActionOkᵈ {μ} X with μ X
dualActionOkᵈ X | id-only = dma-id
dualActionOkᵈ X | tag-or-id = dma-tag
dualActionOkᵈ X | seal-or-id = dma-seal

dualActionOk-ext :
  ∀ {μ η ν} →
  DualActionOk μ η ν →
  DualActionOk (extᵈ μ) (extᵃ η) (extᵈ ν)
dualActionOk-ext rel zero = dma-id
dualActionOk-ext rel (suc X) = rel X

dualActionOk-gen-inst :
  ∀ {μ η ν} →
  DualActionOk μ η ν →
  DualActionOk (genᵈ μ) (genᵃ η) (instᵈ ν)
dualActionOk-gen-inst rel zero = dma-tag-seal
dualActionOk-gen-inst rel (suc X) = rel X

dualActionOk-inst-gen :
  ∀ {μ η ν} →
  DualActionOk μ η ν →
  DualActionOk (instᵈ μ) (instᵃ η) (genᵈ ν)
dualActionOk-inst-gen rel zero = dma-seal-tag
dualActionOk-inst-gen rel (suc X) = rel X

dualActionOk-idTyAllowed :
  ∀ {μ η ν A} →
  DualActionOk μ η ν →
  idTyAllowed μ A ≡ true →
  idTyAllowed ν A ≡ true
dualActionOk-idTyAllowed {μ = μ} {η = η} {ν = ν} {A = ＇ α}
    rel ok
    with μ α | η α | ν α | rel α | ok
dualActionOk-idTyAllowed rel ok
    | id-only | normal | id-only | dma-id | refl = refl
dualActionOk-idTyAllowed rel ok
    | tag-or-id | normal | tag-or-id | dma-tag | refl = refl
dualActionOk-idTyAllowed rel ok
    | seal-or-id | normal | seal-or-id | dma-seal | refl = refl
dualActionOk-idTyAllowed rel ok
    | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | refl = refl
dualActionOk-idTyAllowed rel ok
    | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | refl = refl
dualActionOk-idTyAllowed {A = ‵ ι} rel ok = refl
dualActionOk-idTyAllowed {A = ★} rel ok = refl
dualActionOk-idTyAllowed {A = A ⇒ B} rel ok
    rewrite dualActionOk-idTyAllowed {A = A} rel (∧-trueˡ ok)
          | dualActionOk-idTyAllowed {A = B} rel (∧-trueʳ ok) =
  refl
dualActionOk-idTyAllowed {A = `∀ A} rel ok =
  dualActionOk-idTyAllowed {A = A} (dualActionOk-ext rel) ok

tagModeAllowed-var-tag :
  ∀ {ν : ModeEnv}{α : TyVar} →
  ν α ≡ tag-or-id →
  tagModeAllowed (ν α) ≡ true
tagModeAllowed-var-tag eq =
  subst (λ (m : Mode) → tagModeAllowed m ≡ true) (sym eq) refl

sealModeAllowed-var-seal :
  ∀ {ν : ModeEnv}{α : TyVar} →
  ν α ≡ seal-or-id →
  sealModeAllowed (ν α) ≡ true
sealModeAllowed-var-seal eq =
  subst (λ (m : Mode) → sealModeAllowed m ≡ true) (sym eq) refl

zero∉-⟰ᵗ :
  ∀ {Σ A} →
  (zero , A) ∈ ⟰ᵗ Σ →
  ⊥
zero∉-⟰ᵗ {Σ = []} ()
zero∉-⟰ᵗ {Σ = (α , A) ∷ Σ} (here ())
zero∉-⟰ᵗ {Σ = (α , A) ∷ Σ} (there α∈Σ) =
  zero∉-⟰ᵗ α∈Σ

suc∈-cons-zero-tail :
  ∀ {Σ α A C} →
  (suc α , A) ∈ ((zero , C) ∷ ⟰ᵗ Σ) →
  (suc α , A) ∈ ⟰ᵗ Σ
suc∈-cons-zero-tail (here ())
suc∈-cons-zero-tail (there α∈Σ) = α∈Σ

∈-⟰ᵗ-inv :
  ∀ {Σ α A} →
  (suc α , A) ∈ ⟰ᵗ Σ →
  ∃[ B ] ((α , B) ∈ Σ × A ≡ renameᵗ suc B)
∈-⟰ᵗ-inv {Σ = []} ()
∈-⟰ᵗ-inv {Σ = (α , A) ∷ Σ} (here refl) =
  A , here refl , refl
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there α∈Σ)
    with ∈-⟰ᵗ-inv α∈Σ
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there α∈Σ)
    | A , αA∈Σ , eq =
  A , there αA∈Σ , eq

record DualStoreAt
    (Δ : TyCtx) (μ : ModeEnv) (η : DualActionEnv) (ν : ModeEnv)
    (Σ Π : Store) : Set where
  field
    tag★∈ :
      ∀ {α} →
      α < Δ →
      η α ≡ tag-to-seal →
      (α , ★) ∈ Π
    seal∈ :
      ∀ {α A} →
      μ α ≡ seal-or-id →
      η α ≡ normal →
      ν α ≡ seal-or-id →
      (α , A) ∈ Σ →
      (α , A) ∈ Π
    seal★ :
      ∀ {α A} →
      η α ≡ seal-to-tag →
      (α , A) ∈ Σ →
      A ≡ ★

open DualStoreAt

dualStoreAt-ext :
  ∀ {Δ μ η ν Σ Π} →
  DualStoreAt Δ μ η ν Σ Π →
  DualStoreAt (suc Δ) (extᵈ μ) (extᵃ η) (extᵈ ν) (⟰ᵗ Σ) (⟰ᵗ Π)
dualStoreAt-ext ds =
  record { tag★∈ = tag ; seal∈ = sealMember ; seal★ = sealStar }
  where
    tag :
      ∀ {α} →
      α < _ →
      extᵃ _ α ≡ tag-to-seal →
      (α , ★) ∈ ⟰ᵗ _
    tag {zero} z<s ()
    tag {suc α} (s<s α<Δ) eq =
      ∈-renameStoreᵗ suc (tag★∈ ds α<Δ eq)

    sealMember :
      ∀ {α A} →
      extᵈ _ α ≡ seal-or-id →
      extᵃ _ α ≡ normal →
      extᵈ _ α ≡ seal-or-id →
      (α , A) ∈ ⟰ᵗ _ →
      (α , A) ∈ ⟰ᵗ _
    sealMember {zero} () ηα να αA∈Σ
    sealMember {suc α} {A} μα ηα να αA∈Σ with ∈-⟰ᵗ-inv αA∈Σ
    sealMember {suc α} μα ηα να αA∈Σ | B , αB∈Σ , refl =
      ∈-renameStoreᵗ suc (seal∈ ds μα ηα να αB∈Σ)

    sealStar :
      ∀ {α A} →
      extᵃ _ α ≡ seal-to-tag →
      (α , A) ∈ ⟰ᵗ _ →
      A ≡ ★
    sealStar {zero} () αA∈Σ
    sealStar {suc α} {A} eq αA∈Σ with ∈-⟰ᵗ-inv αA∈Σ
    sealStar {suc α} eq αA∈Σ | B , αB∈Σ , refl
      rewrite seal★ ds eq αB∈Σ = refl

dualStoreAt-gen-inst :
  ∀ {Δ μ η ν Σ Π} →
  DualStoreAt Δ μ η ν Σ Π →
  DualStoreAt (suc Δ) (genᵈ μ) (genᵃ η) (instᵈ ν)
              (⟰ᵗ Σ) ((zero , ★) ∷ ⟰ᵗ Π)
dualStoreAt-gen-inst ds =
  record { tag★∈ = tag ; seal∈ = sealMember ; seal★ = sealStar }
  where
    tag :
      ∀ {α} →
      α < _ →
      genᵃ _ α ≡ tag-to-seal →
      (α , ★) ∈ ((zero , ★) ∷ ⟰ᵗ _)
    tag {zero} z<s eq = here refl
    tag {suc α} (s<s α<Δ) eq =
      there (∈-renameStoreᵗ suc (tag★∈ ds α<Δ eq))

    sealMember :
      ∀ {α A} →
      genᵈ _ α ≡ seal-or-id →
      genᵃ _ α ≡ normal →
      instᵈ _ α ≡ seal-or-id →
      (α , A) ∈ ⟰ᵗ _ →
      (α , A) ∈ ((zero , ★) ∷ ⟰ᵗ _)
    sealMember {zero} () ηα να αA∈Σ
    sealMember {suc α} {A} μα ηα να αA∈Σ with ∈-⟰ᵗ-inv αA∈Σ
    sealMember {suc α} μα ηα να αA∈Σ | B , αB∈Σ , refl =
      there (∈-renameStoreᵗ suc (seal∈ ds μα ηα να αB∈Σ))

    sealStar :
      ∀ {α A} →
      genᵃ _ α ≡ seal-to-tag →
      (α , A) ∈ ⟰ᵗ _ →
      A ≡ ★
    sealStar {zero} () αA∈Σ
    sealStar {suc α} {A} eq αA∈Σ with ∈-⟰ᵗ-inv αA∈Σ
    sealStar {suc α} eq αA∈Σ | B , αB∈Σ , refl
      rewrite seal★ ds eq αB∈Σ = refl

dualStoreAt-inst-gen :
  ∀ {Δ μ η ν Σ Π} →
  DualStoreAt Δ μ η ν Σ Π →
  DualStoreAt (suc Δ) (instᵈ μ) (instᵃ η) (genᵈ ν)
              ((zero , ★) ∷ ⟰ᵗ Σ) (⟰ᵗ Π)
dualStoreAt-inst-gen ds =
  record { tag★∈ = tag ; seal∈ = sealMember ; seal★ = sealStar }
  where
    tag :
      ∀ {α} →
      α < _ →
      instᵃ _ α ≡ tag-to-seal →
      (α , ★) ∈ ⟰ᵗ _
    tag {zero} z<s ()
    tag {suc α} (s<s α<Δ) eq =
      ∈-renameStoreᵗ suc (tag★∈ ds α<Δ eq)

    sealMember :
      ∀ {α A} →
      instᵈ _ α ≡ seal-or-id →
      instᵃ _ α ≡ normal →
      genᵈ _ α ≡ seal-or-id →
      (α , A) ∈ ((zero , ★) ∷ ⟰ᵗ _) →
      (α , A) ∈ ⟰ᵗ _
    sealMember {zero} μα () να αA∈Σ
    sealMember {suc α} {A} μα ηα να αA∈Σ
        with ∈-⟰ᵗ-inv (suc∈-cons-zero-tail αA∈Σ)
    sealMember {suc α} μα ηα να αA∈Σ | B , αB∈Σ , refl =
      ∈-renameStoreᵗ suc (seal∈ ds μα ηα να αB∈Σ)

    sealStar :
      ∀ {α A} →
      instᵃ _ α ≡ seal-to-tag →
      (α , A) ∈ ((zero , ★) ∷ ⟰ᵗ _) →
      A ≡ ★
    sealStar {zero} eq (here refl) = refl
    sealStar {zero} eq (there αA∈Σ) = ⊥-elim (zero∉-⟰ᵗ αA∈Σ)
    sealStar {suc α} {A} eq αA∈Σ
        with ∈-⟰ᵗ-inv (suc∈-cons-zero-tail αA∈Σ)
    sealStar {suc α} eq αA∈Σ | B , αB∈Σ , refl
      rewrite seal★ ds eq αB∈Σ = refl

dualTag-typing :
  ∀ {μ η ν Δ Σ Π G} →
  DualActionOk μ η ν →
  DualStoreAt Δ μ η ν Σ Π →
  WfTy Δ G →
  Ground G →
  tagTyAllowed μ G ≡ true →
  ν ∣ Δ ∣ Π ⊢ dualTag η G ∶ ★ =⇒ G
dualTag-typing {μ = μ} {η = η} {ν = ν} {G = ＇ α}
    rel ds (wfVar α<Δ) (＇ .α) ok
    with μ α in μα | η α in ηα | ν α in να | rel α | ok
dualTag-typing {G = ＇ α} rel ds (wfVar α<Δ) (＇ .α) ok
    | id-only | normal | id-only | dma-id | ()
dualTag-typing {ν = ν} {G = ＇ α} rel ds (wfVar α<Δ) (＇ .α) ok
    | tag-or-id | normal | tag-or-id | dma-tag | refl =
  cast-untag {μ = ν} (wfVar α<Δ) (＇ α)
    (tagModeAllowed-var-tag {ν = ν} {α = α} να)
dualTag-typing {G = ＇ α} rel ds (wfVar α<Δ) (＇ .α) ok
    | seal-or-id | normal | seal-or-id | dma-seal | ()
dualTag-typing {ν = ν} {G = ＇ α} rel ds (wfVar α<Δ) (＇ .α) ok
    | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | refl =
  cast-seal {μ = ν} wf★ (tag★∈ ds α<Δ ηα)
    (sealModeAllowed-var-seal {ν = ν} {α = α} να)
dualTag-typing {G = ＇ α} rel ds (wfVar α<Δ) (＇ .α) ok
    | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | ()
dualTag-typing {G = ‵ ι} rel ds hG gG ok =
  cast-untag hG gG refl
dualTag-typing {G = ★ ⇒ ★} rel ds hG gG ok =
  cast-untag hG gG refl

dualUntag-typing :
  ∀ {μ η ν Δ Σ Π G} →
  DualActionOk μ η ν →
  DualStoreAt Δ μ η ν Σ Π →
  WfTy Δ G →
  Ground G →
  tagTyAllowed μ G ≡ true →
  ν ∣ Δ ∣ Π ⊢ dualUntag η G ∶ G =⇒ ★
dualUntag-typing {μ = μ} {η = η} {ν = ν} {G = ＇ α}
    rel ds (wfVar α<Δ) (＇ .α) ok
    with μ α in μα | η α in ηα | ν α in να | rel α | ok
dualUntag-typing {G = ＇ α} rel ds (wfVar α<Δ) (＇ .α) ok
    | id-only | normal | id-only | dma-id | ()
dualUntag-typing {ν = ν} {G = ＇ α} rel ds (wfVar α<Δ) (＇ .α) ok
    | tag-or-id | normal | tag-or-id | dma-tag | refl =
  cast-tag {μ = ν} (wfVar α<Δ) (＇ α)
    (tagModeAllowed-var-tag {ν = ν} {α = α} να)
dualUntag-typing {G = ＇ α} rel ds (wfVar α<Δ) (＇ .α) ok
    | seal-or-id | normal | seal-or-id | dma-seal | ()
dualUntag-typing {ν = ν} {G = ＇ α} rel ds (wfVar α<Δ) (＇ .α) ok
    | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | refl =
  cast-unseal {μ = ν} wf★ (tag★∈ ds α<Δ ηα)
    (sealModeAllowed-var-seal {ν = ν} {α = α} να)
dualUntag-typing {G = ＇ α} rel ds (wfVar α<Δ) (＇ .α) ok
    | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | ()
dualUntag-typing {G = ‵ ι} rel ds hG gG ok =
  cast-tag hG gG refl
dualUntag-typing {G = ★ ⇒ ★} rel ds hG gG ok =
  cast-tag hG gG refl

dualSeal-typing :
  ∀ {μ η ν Δ Σ Π A α} →
  DualActionOk μ η ν →
  DualStoreAt Δ μ η ν Σ Π →
  StoreWfAt Δ Σ →
  WfTy Δ A →
  (α , A) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  ν ∣ Δ ∣ Π ⊢ dualSeal η A α ∶ ＇ α =⇒ A
dualSeal-typing {μ = μ} {η = η} {ν = ν} {A = A} {α = α}
    rel ds wfΣ hA αA∈Σ α-ok
    with μ α in μα | η α in ηα | ν α in να | rel α | α-ok
dualSeal-typing {α = α} rel ds wfΣ hA αA∈Σ α-ok
    | id-only | normal | id-only | dma-id | ()
dualSeal-typing {α = α} rel ds wfΣ hA αA∈Σ α-ok
    | tag-or-id | normal | tag-or-id | dma-tag | ()
dualSeal-typing {ν = ν} {α = α} rel ds wfΣ hA αA∈Σ α-ok
    | seal-or-id | normal | seal-or-id | dma-seal | refl =
  cast-unseal {μ = ν} hA (seal∈ ds μα ηα να αA∈Σ)
    (sealModeAllowed-var-seal {ν = ν} {α = α} να)
dualSeal-typing {α = α} rel ds wfΣ hA αA∈Σ α-ok
    | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | ()
dualSeal-typing {ν = ν} {α = α} rel ds wfΣ hA αA∈Σ α-ok
    | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | refl
    rewrite seal★ ds ηα αA∈Σ =
  cast-tag {μ = ν} (wfVar (bound wfΣ αA∈Σ)) (＇ α)
    (tagModeAllowed-var-tag {ν = ν} {α = α} να)

dualUnseal-typing :
  ∀ {μ η ν Δ Σ Π A α} →
  DualActionOk μ η ν →
  DualStoreAt Δ μ η ν Σ Π →
  StoreWfAt Δ Σ →
  WfTy Δ A →
  (α , A) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  ν ∣ Δ ∣ Π ⊢ dualUnseal η α A ∶ A =⇒ ＇ α
dualUnseal-typing {μ = μ} {η = η} {ν = ν} {A = A} {α = α}
    rel ds wfΣ hA αA∈Σ α-ok
    with μ α in μα | η α in ηα | ν α in να | rel α | α-ok
dualUnseal-typing {α = α} rel ds wfΣ hA αA∈Σ α-ok
    | id-only | normal | id-only | dma-id | ()
dualUnseal-typing {α = α} rel ds wfΣ hA αA∈Σ α-ok
    | tag-or-id | normal | tag-or-id | dma-tag | ()
dualUnseal-typing {ν = ν} {α = α} rel ds wfΣ hA αA∈Σ α-ok
    | seal-or-id | normal | seal-or-id | dma-seal | refl =
  cast-seal {μ = ν} hA (seal∈ ds μα ηα να αA∈Σ)
    (sealModeAllowed-var-seal {ν = ν} {α = α} να)
dualUnseal-typing {α = α} rel ds wfΣ hA αA∈Σ α-ok
    | tag-or-id | tag-to-seal | seal-or-id | dma-tag-seal | ()
dualUnseal-typing {ν = ν} {α = α} rel ds wfΣ hA αA∈Σ α-ok
    | seal-or-id | seal-to-tag | tag-or-id | dma-seal-tag | refl
    rewrite seal★ ds ηα αA∈Σ =
  cast-untag {μ = ν} (wfVar (bound wfΣ αA∈Σ)) (＇ α)
    (tagModeAllowed-var-tag {ν = ν} {α = α} να)

coercion-dual-flipᵐ :
  ∀ {μ η ν Δ Σ Π c A B} →
  DualActionOk μ η ν →
  DualStoreAt Δ μ η ν Σ Π →
  StoreWfAt Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  ν ∣ Δ ∣ Π ⊢ dual η c ∶ B =⇒ A
coercion-dual-flipᵐ {μ = μ} {η = η} {ν = ν} rel ds wfΣ
    (cast-id {A = A} hA ok) =
  cast-id hA
    (dualActionOk-idTyAllowed {μ = μ} {η = η} {ν = ν}
      {A = A} rel ok)
coercion-dual-flipᵐ rel ds wfΣ
    (cast-seal hA αA∈Σ α-ok) =
  dualSeal-typing rel ds wfΣ hA αA∈Σ α-ok
coercion-dual-flipᵐ rel ds wfΣ
    (cast-unseal hA αA∈Σ α-ok) =
  dualUnseal-typing rel ds wfΣ hA αA∈Σ α-ok
coercion-dual-flipᵐ rel ds wfΣ (cast-seq c⊢ d⊢) =
  cast-seq (coercion-dual-flipᵐ rel ds wfΣ d⊢)
           (coercion-dual-flipᵐ rel ds wfΣ c⊢)
coercion-dual-flipᵐ rel ds wfΣ (cast-tag hG gG ok) =
  dualTag-typing rel ds hG gG ok
coercion-dual-flipᵐ rel ds wfΣ (cast-untag hG gG ok) =
  dualUntag-typing rel ds hG gG ok
coercion-dual-flipᵐ rel ds wfΣ (cast-fun c⊢ d⊢) =
  cast-fun (coercion-dual-flipᵐ rel ds wfΣ c⊢)
           (coercion-dual-flipᵐ rel ds wfΣ d⊢)
coercion-dual-flipᵐ rel ds wfΣ (cast-all c⊢) =
  cast-all
    (coercion-dual-flipᵐ
      (dualActionOk-ext rel)
      (dualStoreAt-ext ds)
      (StoreWfAt-⟰ᵗ wfΣ)
      c⊢)
coercion-dual-flipᵐ rel ds wfΣ (cast-inst hB occ c⊢) =
  cast-gen hB occ
    (coercion-dual-flipᵐ
      (dualActionOk-inst-gen rel)
      (dualStoreAt-inst-gen ds)
      (StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ wfΣ))
      c⊢)
coercion-dual-flipᵐ rel ds wfΣ (cast-gen hA occ c⊢) =
  cast-inst hA occ
    (coercion-dual-flipᵐ
      (dualActionOk-gen-inst rel)
      (dualStoreAt-gen-inst ds)
      (StoreWfAt-⟰ᵗ wfΣ)
      c⊢)

coercion-dual-flip :
  ∀ {μ η ν Δ Σ Π c A B} →
  DualActionOk μ η ν →
  DualStoreAt Δ μ η ν Σ Π →
  StoreWfAt Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ ∣ Π ⊢ dual η c ∶ B =⇒ A
coercion-dual-flip {ν = ν} rel ds wfΣ c⊢ =
  ν , coercion-dual-flipᵐ rel ds wfΣ c⊢

dual-flips-typingᵐ :
  ∀ {μ Δ Σ Π c A B} →
  DualStoreAt Δ μ (dualActionᵈ μ) (dualᵈ μ) Σ Π →
  StoreWfAt Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  dualᵈ μ ∣ Δ ∣ Π ⊢ dual (dualActionᵈ μ) c ∶ B =⇒ A
dual-flips-typingᵐ {μ = μ} =
  coercion-dual-flipᵐ (dualActionOkᵈ {μ = μ})

------------------------------------------------------------------------
-- Coercion endpoint well-formedness
------------------------------------------------------------------------

coercion-wfᵐ :
  ∀ {μ Δ Σ c A B} →
  StoreWfAt Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  WfTy Δ A × WfTy Δ B
coercion-wfᵐ wfΣ (cast-id hA ok) = hA , hA
coercion-wfᵐ wfΣ (cast-seal hA α∈Σ _) =
  hA , wfVar (bound wfΣ α∈Σ)
coercion-wfᵐ wfΣ (cast-unseal hA α∈Σ _) =
  wfVar (bound wfΣ α∈Σ) , hA
coercion-wfᵐ wfΣ (cast-seq c⊢ d⊢)
    with coercion-wfᵐ wfΣ c⊢ | coercion-wfᵐ wfΣ d⊢
coercion-wfᵐ wfΣ (cast-seq c⊢ d⊢)
    | hA , hB | hB′ , hC =
  hA , hC
coercion-wfᵐ wfΣ (cast-tag hG gG _) = hG , wf★
coercion-wfᵐ wfΣ (cast-untag hH gH _) = wf★ , hH
coercion-wfᵐ wfΣ (cast-fun c⊢ d⊢)
    with coercion-wfᵐ wfΣ c⊢ | coercion-wfᵐ wfΣ d⊢
coercion-wfᵐ wfΣ (cast-fun c⊢ d⊢)
    | hA′ , hA | hB , hB′ =
  wf⇒ hA hB , wf⇒ hA′ hB′
coercion-wfᵐ wfΣ (cast-all c⊢)
    with coercion-wfᵐ (StoreWfAt-⟰ᵗ wfΣ) c⊢
coercion-wfᵐ wfΣ (cast-all c⊢) | hA , hB =
  wf∀ hA , wf∀ hB
coercion-wfᵐ wfΣ (cast-inst hB occ c⊢)
    with coercion-wfᵐ
      (StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ wfΣ))
      c⊢
coercion-wfᵐ wfΣ (cast-inst hB occ c⊢) | hA , hB′ =
  wf∀ hA , hB
coercion-wfᵐ wfΣ (cast-gen hA occ c⊢)
    with coercion-wfᵐ (StoreWfAt-⟰ᵗ wfΣ) c⊢
coercion-wfᵐ wfΣ (cast-gen hA occ c⊢) | hA′ , hB =
  hA , wf∀ hB

coercion-wf :
  ∀ {Δ Σ c A B} →
  StoreWfAt Δ Σ →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  WfTy Δ A × WfTy Δ B
coercion-wf wfΣ (μ , c⊢) = coercion-wfᵐ wfΣ c⊢

------------------------------------------------------------------------
-- Typing the reveal/conceal coercions generated after fresh allocation
------------------------------------------------------------------------

data RevealVar
    (α : TyVar) (C : Ty) (ρ : Renameᵗ) (σ : Substᵗ)
    (X : TyVar) : Set where
  rv-hit :
    ρ X ≡ α →
    σ X ≡ C →
    RevealVar α C ρ σ X

  rv-miss :
    ρ X ≢ α →
    σ X ≡ ＇ (ρ X) →
    RevealVar α C ρ σ X

RevealEnv : TyCtx → TyVar → Ty → Renameᵗ → Substᵗ → Set
RevealEnv Θ α C ρ σ = ∀ {X} → X < Θ → RevealVar α C ρ σ X

RevealEnv-ext :
  ∀ {Θ α C ρ σ} →
  RevealEnv Θ α C ρ σ →
  RevealEnv (suc Θ) (suc α) (⇑ᵗ C) (extᵗ ρ) (extsᵗ σ)
RevealEnv-ext env {X = zero} z<s =
  rv-miss (λ ()) refl
RevealEnv-ext env {X = suc X} (s<s X<Θ) with env X<Θ
RevealEnv-ext env {X = suc X} (s<s X<Θ)
    | rv-hit ρX≡α σX≡C =
  rv-hit (cong suc ρX≡α) (cong (renameᵗ suc) σX≡C)
RevealEnv-ext env {X = suc X} (s<s X<Θ)
    | rv-miss ρX≢α σX≡var =
  rv-miss
    (λ eq → ρX≢α (suc-injective eq))
    (cong (renameᵗ suc) σX≡var)

singleRevealEnv :
  ∀ {Δ C} →
  RevealEnv (suc Δ) Δ C (singleRenameᵗ Δ) (singleTyEnv C)
singleRevealEnv {Δ = Δ} {X = zero} z<s =
  rv-hit refl refl
singleRevealEnv {Δ = Δ} {X = suc X} (s<s X<Δ) =
  rv-miss X≢Δ refl
  where
    X≢Δ : X ≢ Δ
    X≢Δ X≡Δ =
      <-irrefl refl (subst (λ Y → Y < Δ) X≡Δ X<Δ)

RevealMode : ModeEnv → TyVar → Set
RevealMode μ α =
  sealModeAllowed (μ α) ≡ true ×
  (∀ {Y} → Y ≢ α → idModeAllowed (μ Y) ≡ true)

RevealMode-ext :
  ∀ {μ α} →
  RevealMode μ α →
  RevealMode (extᵈ μ) (suc α)
RevealMode-ext mode =
  proj₁ mode ,
  λ { {zero} zero≢sα → refl
    ; {suc Y} sY≢sα →
        proj₂ mode (λ Y≡α → sY≢sα (cong suc Y≡α))
    }

singleSealᵈ : TyVar → ModeEnv
singleSealᵈ α X with X ≟ α
singleSealᵈ α X | yes eq = seal-or-id
singleSealᵈ α X | no neq = id-only

singleSealMode :
  ∀ {α} →
  RevealMode (singleSealᵈ α) α
singleSealMode {α = α} with α ≟ α
singleSealMode {α = α} | yes refl =
  refl , λ {Y} Y≢α → miss Y Y≢α
  where
    miss : ∀ Y → Y ≢ α → idModeAllowed (singleSealᵈ α Y) ≡ true
    miss Y Y≢α with Y ≟ α
    miss Y Y≢α | yes Y≡α = ⊥-elim (Y≢α Y≡α)
    miss Y Y≢α | no Y≢α′ = refl
singleSealMode {α = α} | no α≢α =
  ⊥-elim (α≢α refl)

reveal-var-hit :
  ∀ {μ Δ Σ α C} →
  WfTy Δ C →
  (α , C) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ reveal (＇ α) α C ∶ ＇ α =⇒ C
reveal-var-hit {α = α} hC α∈Σ α-ok with α ≟ α
reveal-var-hit {α = α} {C = C} hC α∈Σ α-ok | yes refl =
  cast-unseal hC α∈Σ α-ok
reveal-var-hit {α = α} hC α∈Σ α-ok | no α≢α =
  ⊥-elim (α≢α refl)

conceal-var-hit :
  ∀ {μ Δ Σ α C} →
  WfTy Δ C →
  (α , C) ∈ Σ →
  sealModeAllowed (μ α) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ conceal (＇ α) α C ∶ C =⇒ ＇ α
conceal-var-hit {α = α} hC α∈Σ α-ok with α ≟ α
conceal-var-hit {α = α} {C = C} hC α∈Σ α-ok | yes refl =
  cast-seal hC α∈Σ α-ok
conceal-var-hit {α = α} hC α∈Σ α-ok | no α≢α =
  ⊥-elim (α≢α refl)

reveal-var-miss :
  ∀ {μ Δ Σ α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  idModeAllowed (μ Y) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ reveal (＇ Y) α C ∶ ＇ Y =⇒ ＇ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY Y-id with α ≟ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY Y-id | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
reveal-var-miss {α = α} {Y = Y} Y≢α hY Y-id | no α≢Y =
  cast-id hY Y-id

conceal-var-miss :
  ∀ {μ Δ Σ α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  idModeAllowed (μ Y) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ conceal (＇ Y) α C ∶ ＇ Y =⇒ ＇ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY Y-id with α ≟ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY Y-id | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
conceal-var-miss {α = α} {Y = Y} Y≢α hY Y-id | no α≢Y =
  cast-id hY Y-id

mutual
  reveal-typing-env :
    ∀ {μ Θ Δ Σ B α C ρ σ} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    RevealEnv Θ α C ρ σ →
    WfTy Δ C →
    (α , C) ∈ Σ →
    RevealMode μ α →
    μ ∣ Δ ∣ Σ ⊢ reveal (renameᵗ ρ B) α C
      ∶ renameᵗ ρ B =⇒ substᵗ σ B
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      with env X<Θ
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      | rv-hit ρX≡α σX≡C
      rewrite ρX≡α | σX≡C =
    reveal-var-hit hC α∈Σ (proj₁ mode)
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      | rv-miss ρX≢α σX≡var
      rewrite σX≡var =
    reveal-var-miss ρX≢α (wfVar (hρ X<Θ)) (proj₂ mode ρX≢α)
  reveal-typing-env wfBase hρ hσ env hC α∈Σ mode =
    cast-id wfBase refl
  reveal-typing-env wf★ hρ hσ env hC α∈Σ mode =
    cast-id wf★ refl
  reveal-typing-env (wf⇒ hA hB) hρ hσ env hC α∈Σ mode =
    cast-fun
      (conceal-typing-env hA hρ hσ env hC α∈Σ mode)
      (reveal-typing-env hB hρ hσ env hC α∈Σ mode)
  reveal-typing-env {B = `∀ B} {ρ = ρ} {σ = σ}
      (wf∀ hB) hρ hσ env hC α∈Σ mode =
    cast-all
      (reveal-typing-env
        hB
        (TyRenameWf-ext hρ)
        (TySubstWf-exts hσ)
        (RevealEnv-ext env)
        (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
        (∈-renameStoreᵗ suc α∈Σ)
        (RevealMode-ext mode))

  conceal-typing-env :
    ∀ {μ Θ Δ Σ B α C ρ σ} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    RevealEnv Θ α C ρ σ →
    WfTy Δ C →
    (α , C) ∈ Σ →
    RevealMode μ α →
    μ ∣ Δ ∣ Σ ⊢ conceal (renameᵗ ρ B) α C
      ∶ substᵗ σ B =⇒ renameᵗ ρ B
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      with env X<Θ
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      | rv-hit ρX≡α σX≡C
      rewrite ρX≡α | σX≡C =
    conceal-var-hit hC α∈Σ (proj₁ mode)
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ mode
      | rv-miss ρX≢α σX≡var
      rewrite σX≡var =
    conceal-var-miss ρX≢α (wfVar (hρ X<Θ)) (proj₂ mode ρX≢α)
  conceal-typing-env wfBase hρ hσ env hC α∈Σ mode =
    cast-id wfBase refl
  conceal-typing-env wf★ hρ hσ env hC α∈Σ mode =
    cast-id wf★ refl
  conceal-typing-env (wf⇒ hA hB) hρ hσ env hC α∈Σ mode =
    cast-fun
      (reveal-typing-env hA hρ hσ env hC α∈Σ mode)
      (conceal-typing-env hB hρ hσ env hC α∈Σ mode)
  conceal-typing-env {B = `∀ B} {ρ = ρ} {σ = σ}
      (wf∀ hB) hρ hσ env hC α∈Σ mode =
    cast-all
      (conceal-typing-env
        hB
        (TyRenameWf-ext hρ)
        (TySubstWf-exts hσ)
        (RevealEnv-ext env)
        (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
        (∈-renameStoreᵗ suc α∈Σ)
        (RevealMode-ext mode))

reveal-fresh-typing :
  ∀ {Δ Σ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  suc Δ ∣ (Δ , A) ∷ Σ ⊢ reveal (B [ Δ ]ᴿ) Δ A
    ∶ B [ Δ ]ᴿ =⇒ B [ A ]ᵗ
reveal-fresh-typing {Δ = Δ} hA hB =
  singleSealᵈ Δ ,
    reveal-typing-env
      hB
      (singleRenameᵗ-Wf (n<1+n Δ))
      singleTyEnv-Wf-suc
      singleRevealEnv
      (WfTy-weakenᵗ hA (n≤1+n Δ))
      (here refl)
      singleSealMode
  where
    singleTyEnv-Wf-suc :
      TySubstWf (suc Δ) (suc Δ) (singleTyEnv _)
    singleTyEnv-Wf-suc {zero} z<s =
      WfTy-weakenᵗ hA (n≤1+n Δ)
    singleTyEnv-Wf-suc {suc X} (s<s X<Δ) =
      wfVar (m<n⇒m<1+n X<Δ)

conceal-fresh-typing :
  ∀ {Δ Σ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  suc Δ ∣ (Δ , A) ∷ Σ ⊢ conceal (B [ Δ ]ᴿ) Δ A
    ∶ B [ A ]ᵗ =⇒ B [ Δ ]ᴿ
conceal-fresh-typing {Δ = Δ} hA hB =
  singleSealᵈ Δ ,
    conceal-typing-env
      hB
      (singleRenameᵗ-Wf (n<1+n Δ))
      singleTyEnv-Wf-suc
      singleRevealEnv
      (WfTy-weakenᵗ hA (n≤1+n Δ))
      (here refl)
      singleSealMode
  where
    singleTyEnv-Wf-suc :
      TySubstWf (suc Δ) (suc Δ) (singleTyEnv _)
    singleTyEnv-Wf-suc {zero} z<s =
      WfTy-weakenᵗ hA (n≤1+n Δ)
    singleTyEnv-Wf-suc {suc X} (s<s X<Δ) =
      wfVar (m<n⇒m<1+n X<Δ)

------------------------------------------------------------------------
-- Syntactic endpoints agree with typed endpoints
------------------------------------------------------------------------

coercion-src-tgtᵐ :
  ∀ {μ Δ Σ c A B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  src c ≡ A × tgt c ≡ B
coercion-src-tgtᵐ (cast-id hA ok) = refl , refl
coercion-src-tgtᵐ (cast-seal hA α∈Σ _) = refl , refl
coercion-src-tgtᵐ (cast-unseal hA α∈Σ _) = refl , refl
coercion-src-tgtᵐ (cast-seq c⊢ d⊢)
    with coercion-src-tgtᵐ c⊢ | coercion-src-tgtᵐ d⊢
coercion-src-tgtᵐ (cast-seq c⊢ d⊢)
    | src-c , tgt-c | src-d , tgt-d rewrite src-c | tgt-d =
  refl , refl
coercion-src-tgtᵐ (cast-tag hG gG _) = refl , refl
coercion-src-tgtᵐ (cast-untag hH gH _) = refl , refl
coercion-src-tgtᵐ (cast-fun c⊢ d⊢)
    with coercion-src-tgtᵐ c⊢ | coercion-src-tgtᵐ d⊢
coercion-src-tgtᵐ (cast-fun c⊢ d⊢)
    | src-c , tgt-c | src-d , tgt-d rewrite tgt-c | src-d | src-c | tgt-d =
  refl , refl
coercion-src-tgtᵐ (cast-all c⊢)
    with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-all c⊢) | src-c , tgt-c rewrite src-c | tgt-c =
  refl , refl
coercion-src-tgtᵐ (cast-inst hB occ c⊢)
    with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-inst hB occ c⊢) | src-c , tgt-c rewrite src-c =
  refl , refl
coercion-src-tgtᵐ (cast-gen hA occ c⊢)
    with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-gen hA occ c⊢) | src-c , tgt-c rewrite tgt-c =
  refl , refl

coercion-src-tgt :
  ∀ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  src c ≡ A × tgt c ≡ B
coercion-src-tgt (μ , c⊢) = coercion-src-tgtᵐ c⊢

coercion-endpoints-uniqueᵐ :
  ∀ {μ Δ Σ c A B A′ B′} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A′ =⇒ B′ →
  A ≡ A′ × B ≡ B′
coercion-endpoints-uniqueᵐ c⊢ c⊢′
    with coercion-src-tgtᵐ c⊢ | coercion-src-tgtᵐ c⊢′
... | src-c , tgt-c | src-c′ , tgt-c′ =
  trans (sym src-c) src-c′ , trans (sym tgt-c) tgt-c′

coercion-endpoints-unique :
  ∀ {Δ Σ c A B A′ B′} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ ∣ Σ ⊢ c ∶ A′ =⇒ B′ →
  A ≡ A′ × B ≡ B′
coercion-endpoints-unique (μ , c⊢) (ν , c⊢′)
    with coercion-src-tgtᵐ c⊢ | coercion-src-tgtᵐ c⊢′
... | src-c , tgt-c | src-c′ , tgt-c′ =
  trans (sym src-c) src-c′ , trans (sym tgt-c) tgt-c′
