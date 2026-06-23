module proof.CoercionProperties where

-- File Charter:
--   * Proof-only metatheory for GTSF coercion typing.
--   * Coercion weakening, type-renaming, endpoint well-formedness, and
--     reveal/conceal typing lemmas used by term preservation.
--   * Store-specific lemmas belong in `proof.StoreProperties`.
--   * Term substitution/renaming lemmas belong in `proof.TermProperties`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Nat using (zero; suc; _<_; _≤_; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties
  using (_≟_; ≤-refl; n≤1+n; n<1+n; <-≤-trans; <-irrefl;
         m<n⇒m<1+n; suc-injective)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
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

------------------------------------------------------------------------
-- Coercion typing under store/type-context weakening
------------------------------------------------------------------------

coercion-weakenᵐ :
  ∀ {μ Δ Δ′ Σ Σ′ c A B} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  μ ∣ Δ′ ∣ Σ′ ⊢ c ∶ A =⇒ B
coercion-weakenᵐ Δ≤Δ′ incl (cast-id hA) =
  cast-id (WfTy-weakenᵗ hA Δ≤Δ′)
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
coercion-weakenᵐ Δ≤Δ′ incl (cast-inst hB c⊢) =
  cast-inst
    (WfTy-weakenᵗ hB Δ≤Δ′)
    (coercion-weakenᵐ
      (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl))
      c⊢)
coercion-weakenᵐ Δ≤Δ′ incl (cast-gen hA c⊢) =
  cast-gen
    (WfTy-weakenᵗ hA Δ≤Δ′)
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
  zero ∣ [] ⊢ inst ★ (seal ★ zero ︔ unseal zero ★) ∶ `∀ ★ =⇒ ★
dual-inst-example⊢ =
  tag-to-sealᵈ ,
    cast-inst wf★
      (cast-seq (cast-seal wf★ (here refl) refl)
                (cast-unseal wf★ (here refl) refl))

dual-inst-example-dual≡ :
  - inst ★ (seal ★ zero ︔ unseal zero ★)
    ≡ gen ★ (((＇ zero) ？) ︔ ((＇ zero) !))
dual-inst-example-dual≡ = refl

dual-inst-example-dual⊢ :
  zero ∣ [] ⊢ - inst ★ (seal ★ zero ︔ unseal zero ★) ∶ ★ =⇒ `∀ ★
dual-inst-example-dual⊢ =
  tag-to-sealᵈ ,
    cast-gen wf★
      (cast-seq (cast-untag (wfVar z<s) (＇ zero) refl)
                (cast-tag (wfVar z<s) (＇ zero) refl))

dual-inst-tag-counterexample-not-typable :
  zero ∣ [] ⊢ inst ★ ((＇ zero) !) ∶ `∀ (＇ zero) =⇒ ★ →
  ⊥
dual-inst-tag-counterexample-not-typable
    (μ , cast-inst h★ (cast-tag hα (＇ zero) ()))

dual-inst-tag-counterexample-dual≡ :
  - inst ★ ((＇ zero) !) ≡ gen ★ (seal ★ zero)
dual-inst-tag-counterexample-dual≡ = refl

dual-inst-tag-counterexample-dual-not-typable :
  zero ∣ [] ⊢ - inst ★ ((＇ zero) !) ∶ ★ =⇒ `∀ (＇ zero) →
  ⊥
dual-inst-tag-counterexample-dual-not-typable
    (μ , cast-gen h★ (cast-seal hA () _))

------------------------------------------------------------------------
-- Coercion typing under type renaming
------------------------------------------------------------------------

ModeRename : Renameᵗ → DualEnv → DualEnv → Set
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

ScopedModeRename : TyCtx → Renameᵗ → DualEnv → DualEnv → Set
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

mode≤-tag :
  ∀ {m n} →
  mode≤ m n ≡ true →
  tagModeAllowed m ≡ true →
  tagModeAllowed n ≡ true
mode≤-tag {tag-to-seal} {tag-to-seal} rel ok = refl
mode≤-tag {tag-to-seal} {seal-to-tag} () ok
mode≤-tag {seal-to-tag} {tag-to-seal} () ok
mode≤-tag {seal-to-tag} {seal-to-tag} rel ()

mode≤-seal :
  ∀ {m n} →
  mode≤ m n ≡ true →
  sealModeAllowed m ≡ true →
  sealModeAllowed n ≡ true
mode≤-seal {tag-to-seal} {tag-to-seal} rel ()
mode≤-seal {tag-to-seal} {seal-to-tag} () ok
mode≤-seal {seal-to-tag} {tag-to-seal} () ok
mode≤-seal {seal-to-tag} {seal-to-tag} rel ok = refl

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
coercion-mode-relax incl (cast-id hA) =
  cast-id hA
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
coercion-mode-relax incl (cast-inst hB c⊢) =
  cast-inst hB
    (coercion-mode-relax (ModeIncl-inst incl) c⊢)
coercion-mode-relax incl (cast-gen hA c⊢) =
  cast-gen hA
    (coercion-mode-relax (ModeIncl-gen incl) c⊢)

coercion-renameᵗᵐ :
  ∀ {Δ Δ′ Σ c A B ρ μ ν} →
  TyRenameWf Δ Δ′ ρ →
  ModeRename ρ μ ν →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  ν ∣ Δ′ ∣ renameStoreᵗ ρ Σ ⊢ renameᶜ ρ c
    ∶ renameᵗ ρ A =⇒ renameᵗ ρ B
coercion-renameᵗᵐ hρ rel (cast-id hA) =
  cast-id (renameᵗ-preserves-WfTy hA hρ)
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
    (cast-inst {B = B} hB c⊢) =
  cast-inst
    (renameᵗ-preserves-WfTy hB hρ)
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
    (cast-gen {A = A} hA c⊢) =
  cast-gen
    (renameᵗ-preserves-WfTy hA hρ)
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
coercion-renameᵗᵐ-scoped wfΣ hρ rel (cast-id hA) =
  cast-id (renameᵗ-preserves-WfTy hA hρ)
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
    (cast-inst {B = B} hB c⊢) =
  cast-inst
    (renameᵗ-preserves-WfTy hB hρ)
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
    (cast-gen {A = A} hA c⊢) =
  cast-gen
    (renameᵗ-preserves-WfTy hA hρ)
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

openᵈ : DualEnv → TyVar → DualEnv
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
  α < Δ′ →
  μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ ⇑ᵗ A =⇒ B →
  openᵈ μ α ∣ Δ′ ∣ (α , Aν) ∷ Σ ⊢ c [ α ]ᶜ
    ∶ A =⇒ B [ α ]ᴿ
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
  μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ ⇑ᵗ A =⇒ B →
  Δ′ ∣ (α , Aν) ∷ Σ ⊢ c [ α ]ᶜ ∶ A =⇒ B [ α ]ᴿ
coercion-open-shift-fresh {μ = μ} {α = α}
    wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢ =
  openᵈ μ α ,
    coercion-open-shift-freshᵐ wfΣ Δ≤Δ′ Δ≤α α<Δ′ c⊢

------------------------------------------------------------------------
-- Coercion endpoint well-formedness
------------------------------------------------------------------------

coercion-wfᵐ :
  ∀ {μ Δ Σ c A B} →
  StoreWfAt Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  WfTy Δ A × WfTy Δ B
coercion-wfᵐ wfΣ (cast-id hA) = hA , hA
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
coercion-wfᵐ wfΣ (cast-inst hB c⊢)
    with coercion-wfᵐ
      (StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ wfΣ))
      c⊢
coercion-wfᵐ wfΣ (cast-inst hB c⊢) | hA , hB′ =
  wf∀ hA , hB
coercion-wfᵐ wfΣ (cast-gen hA c⊢)
    with coercion-wfᵐ (StoreWfAt-⟰ᵗ wfΣ) c⊢
coercion-wfᵐ wfΣ (cast-gen hA c⊢) | hA′ , hB =
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
  μ ∣ Δ ∣ Σ ⊢ reveal (＇ Y) α C ∶ ＇ Y =⇒ ＇ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY with α ≟ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
reveal-var-miss {α = α} {Y = Y} Y≢α hY | no α≢Y =
  cast-id hY

conceal-var-miss :
  ∀ {μ Δ Σ α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  μ ∣ Δ ∣ Σ ⊢ conceal (＇ Y) α C ∶ ＇ Y =⇒ ＇ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY with α ≟ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
conceal-var-miss {α = α} {Y = Y} Y≢α hY | no α≢Y =
  cast-id hY

mutual
  reveal-typing-env :
    ∀ {μ Θ Δ Σ B α C ρ σ} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    RevealEnv Θ α C ρ σ →
    WfTy Δ C →
    (α , C) ∈ Σ →
    sealModeAllowed (μ α) ≡ true →
    μ ∣ Δ ∣ Σ ⊢ reveal (renameᵗ ρ B) α C
      ∶ renameᵗ ρ B =⇒ substᵗ σ B
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ α-ok
      with env X<Θ
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ α-ok
      | rv-hit ρX≡α σX≡C
      rewrite ρX≡α | σX≡C =
    reveal-var-hit hC α∈Σ α-ok
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ α-ok
      | rv-miss ρX≢α σX≡var
      rewrite σX≡var =
    reveal-var-miss ρX≢α (wfVar (hρ X<Θ))
  reveal-typing-env wfBase hρ hσ env hC α∈Σ α-ok =
    cast-id wfBase
  reveal-typing-env wf★ hρ hσ env hC α∈Σ α-ok =
    cast-id wf★
  reveal-typing-env (wf⇒ hA hB) hρ hσ env hC α∈Σ α-ok =
    cast-fun
      (conceal-typing-env hA hρ hσ env hC α∈Σ α-ok)
      (reveal-typing-env hB hρ hσ env hC α∈Σ α-ok)
  reveal-typing-env {B = `∀ B} {ρ = ρ} {σ = σ}
      (wf∀ hB) hρ hσ env hC α∈Σ α-ok =
    cast-all
      (reveal-typing-env
        hB
        (TyRenameWf-ext hρ)
        (TySubstWf-exts hσ)
        (RevealEnv-ext env)
        (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
        (∈-renameStoreᵗ suc α∈Σ)
        α-ok)

  conceal-typing-env :
    ∀ {μ Θ Δ Σ B α C ρ σ} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    RevealEnv Θ α C ρ σ →
    WfTy Δ C →
    (α , C) ∈ Σ →
    sealModeAllowed (μ α) ≡ true →
    μ ∣ Δ ∣ Σ ⊢ conceal (renameᵗ ρ B) α C
      ∶ substᵗ σ B =⇒ renameᵗ ρ B
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ α-ok
      with env X<Θ
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ α-ok
      | rv-hit ρX≡α σX≡C
      rewrite ρX≡α | σX≡C =
    conceal-var-hit hC α∈Σ α-ok
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ α-ok
      | rv-miss ρX≢α σX≡var
      rewrite σX≡var =
    conceal-var-miss ρX≢α (wfVar (hρ X<Θ))
  conceal-typing-env wfBase hρ hσ env hC α∈Σ α-ok =
    cast-id wfBase
  conceal-typing-env wf★ hρ hσ env hC α∈Σ α-ok =
    cast-id wf★
  conceal-typing-env (wf⇒ hA hB) hρ hσ env hC α∈Σ α-ok =
    cast-fun
      (reveal-typing-env hA hρ hσ env hC α∈Σ α-ok)
      (conceal-typing-env hB hρ hσ env hC α∈Σ α-ok)
  conceal-typing-env {B = `∀ B} {ρ = ρ} {σ = σ}
      (wf∀ hB) hρ hσ env hC α∈Σ α-ok =
    cast-all
      (conceal-typing-env
        hB
        (TyRenameWf-ext hρ)
        (TySubstWf-exts hσ)
        (RevealEnv-ext env)
        (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
        (∈-renameStoreᵗ suc α∈Σ)
        α-ok)

reveal-fresh-typing :
  ∀ {Δ Σ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  suc Δ ∣ (Δ , A) ∷ Σ ⊢ reveal (B [ Δ ]ᴿ) Δ A
    ∶ B [ Δ ]ᴿ =⇒ B [ A ]ᵗ
reveal-fresh-typing {Δ = Δ} hA hB =
  seal-to-tagᵈ ,
    reveal-typing-env
      hB
      (singleRenameᵗ-Wf (n<1+n Δ))
      singleTyEnv-Wf-suc
      singleRevealEnv
      (WfTy-weakenᵗ hA (n≤1+n Δ))
      (here refl)
      refl
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
  seal-to-tagᵈ ,
    conceal-typing-env
      hB
      (singleRenameᵗ-Wf (n<1+n Δ))
      singleTyEnv-Wf-suc
      singleRevealEnv
      (WfTy-weakenᵗ hA (n≤1+n Δ))
      (here refl)
      refl
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
coercion-src-tgtᵐ (cast-id hA) = refl , refl
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
coercion-src-tgtᵐ (cast-inst hB c⊢)
    with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-inst hB c⊢) | src-c , tgt-c rewrite src-c =
  refl , refl
coercion-src-tgtᵐ (cast-gen hA c⊢)
    with coercion-src-tgtᵐ c⊢
coercion-src-tgtᵐ (cast-gen hA c⊢) | src-c , tgt-c rewrite tgt-c =
  refl , refl

coercion-src-tgt :
  ∀ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  src c ≡ A × tgt c ≡ B
coercion-src-tgt (μ , c⊢) = coercion-src-tgtᵐ c⊢
