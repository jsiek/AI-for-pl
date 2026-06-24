module proof.CoercionProperties where

-- File Charter:
--   * Proof-only metatheory for GTSF coercion typing.
--   * Coercion weakening, type-renaming, endpoint well-formedness, and
--     reveal/conceal typing lemmas used by term preservation.
--   * Store-specific lemmas belong in `proof.StoreProperties`.
--   * Term substitution/renaming lemmas belong in `proof.TermProperties`.

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

------------------------------------------------------------------------
-- Coercion typing under store/type-context weakening
------------------------------------------------------------------------

coercion-weakenᵐ :
  ∀ {μ Δ Δ′ Σ Σ′ c A B} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  μ ∣ Δ′ ∣ Σ′ ⊢ c ∶ A =⇒ B
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
  tag-onlyᵈ ,
    cast-inst wf★ refl (cast-unseal wf★ (here refl) refl)

dual-inst-example-dual≡ :
  - inst ★ (unseal zero ★) ≡ gen ★ ((＇ zero) ？)
dual-inst-example-dual≡ = refl

dual-inst-example-dual⊢ :
  zero ∣ [] ⊢ - inst ★ (unseal zero ★) ∶ ★ =⇒ `∀ (＇ zero)
dual-inst-example-dual⊢ =
  tag-onlyᵈ ,
    cast-gen wf★ refl (cast-untag (wfVar z<s) (＇ zero) refl)

dual-inst-tag-counterexample-not-typable :
  zero ∣ [] ⊢ inst ★ ((＇ zero) !) ∶ `∀ (＇ zero) =⇒ ★ →
  ⊥
dual-inst-tag-counterexample-not-typable
    (μ , cast-inst h★ occ (cast-tag hα (＇ zero) ()))

dual-inst-tag-counterexample-dual≡ :
  - inst ★ ((＇ zero) !) ≡ gen ★ (seal ★ zero)
dual-inst-tag-counterexample-dual≡ = refl

dual-inst-tag-counterexample-dual-not-typable :
  zero ∣ [] ⊢ - inst ★ ((＇ zero) !) ∶ ★ =⇒ `∀ (＇ zero) →
  ⊥
dual-inst-tag-counterexample-dual-not-typable
    (μ , cast-gen h★ occ (cast-seal hA () _))

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

mode≤-id :
  ∀ {m n} →
  mode≤ m n ≡ true →
  idModeAllowed m ≡ true →
  idModeAllowed n ≡ true
mode≤-id {id-only} {id-only} rel ok = refl
mode≤-id {id-only} {tag-only} () ok
mode≤-id {id-only} {seal-only} () ok
mode≤-id {tag-only} {id-only} () ok
mode≤-id {tag-only} {tag-only} rel ()
mode≤-id {tag-only} {seal-only} () ok
mode≤-id {seal-only} {id-only} () ok
mode≤-id {seal-only} {tag-only} () ok
mode≤-id {seal-only} {seal-only} rel ()

mode≤-tag :
  ∀ {m n} →
  mode≤ m n ≡ true →
  tagModeAllowed m ≡ true →
  tagModeAllowed n ≡ true
mode≤-tag {id-only} {id-only} rel ()
mode≤-tag {id-only} {tag-only} () ok
mode≤-tag {id-only} {seal-only} () ok
mode≤-tag {tag-only} {id-only} () ok
mode≤-tag {tag-only} {tag-only} rel ok = refl
mode≤-tag {tag-only} {seal-only} () ok
mode≤-tag {seal-only} {id-only} () ok
mode≤-tag {seal-only} {tag-only} () ok
mode≤-tag {seal-only} {seal-only} rel ()

mode≤-seal :
  ∀ {m n} →
  mode≤ m n ≡ true →
  sealModeAllowed m ≡ true →
  sealModeAllowed n ≡ true
mode≤-seal {id-only} {id-only} rel ()
mode≤-seal {id-only} {tag-only} () ok
mode≤-seal {id-only} {seal-only} () ok
mode≤-seal {tag-only} {id-only} () ok
mode≤-seal {tag-only} {tag-only} rel ()
mode≤-seal {tag-only} {seal-only} () ok
mode≤-seal {seal-only} {id-only} () ok
mode≤-seal {seal-only} {tag-only} () ok
mode≤-seal {seal-only} {seal-only} rel ok = refl

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

RevealMode : DualEnv → TyVar → Set
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

singleSealᵈ : TyVar → DualEnv
singleSealᵈ α X with X ≟ α
singleSealᵈ α X | yes eq = seal-only
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
