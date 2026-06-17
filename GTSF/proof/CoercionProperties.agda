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
open import Data.List.Membership.Propositional using (_∈_)
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
coercion-weakenᵐ Δ≤Δ′ incl (cast-id hA {ok = ok}) =
  cast-id (WfTy-weakenᵗ hA Δ≤Δ′) {ok = ok}
coercion-weakenᵐ Δ≤Δ′ incl
    (cast-seal hA α∈Σ {A-ok = A-ok} {α-ok = α-ok}) =
  cast-seal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
    {A-ok = A-ok} {α-ok = α-ok}
coercion-weakenᵐ Δ≤Δ′ incl
    (cast-unseal hA α∈Σ {A-ok = A-ok} {α-ok = α-ok}) =
  cast-unseal (WfTy-weakenᵗ hA Δ≤Δ′) (incl α∈Σ)
    {A-ok = A-ok} {α-ok = α-ok}
coercion-weakenᵐ Δ≤Δ′ incl (cast-seq c⊢ d⊢) =
  cast-seq (coercion-weakenᵐ Δ≤Δ′ incl c⊢)
           (coercion-weakenᵐ Δ≤Δ′ incl d⊢)
coercion-weakenᵐ Δ≤Δ′ incl (cast-tag hG gG {ok = ok}) =
  cast-tag (WfTy-weakenᵗ hG Δ≤Δ′) gG {ok = ok}
coercion-weakenᵐ Δ≤Δ′ incl (cast-untag hH gH {ok = ok}) =
  cast-untag (WfTy-weakenᵗ hH Δ≤Δ′) gH {ok = ok}
coercion-weakenᵐ Δ≤Δ′ incl (cast-fun c⊢ d⊢) =
  cast-fun (coercion-weakenᵐ Δ≤Δ′ incl c⊢)
           (coercion-weakenᵐ Δ≤Δ′ incl d⊢)
coercion-weakenᵐ Δ≤Δ′ incl (cast-all c⊢) =
  cast-all
    (coercion-weakenᵐ
      (s≤s Δ≤Δ′)
      (renameStoreᵗ-incl suc incl)
      c⊢)
coercion-weakenᵐ Δ≤Δ′ incl (cast-inst hB {B-ok = B-ok} c⊢) =
  cast-inst
    (WfTy-weakenᵗ hB Δ≤Δ′)
    {B-ok = B-ok}
    (coercion-weakenᵐ
      (s≤s Δ≤Δ′)
      (StoreIncl-cons (renameStoreᵗ-incl suc incl))
      c⊢)
coercion-weakenᵐ Δ≤Δ′ incl (cast-gen hA {A-ok = A-ok} c⊢) =
  cast-gen
    (WfTy-weakenᵗ hA Δ≤Δ′)
    {A-ok = A-ok}
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
coercion-weaken = coercion-weakenᵐ

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
  cast-inst wf★ {B-ok = refl}
    (cast-seq (cast-seal wf★ (here refl) {A-ok = refl} {α-ok = refl})
              (cast-unseal wf★ (here refl) {A-ok = refl} {α-ok = refl}))

dual-inst-example-dual≡ :
  - inst ★ (seal ★ zero ︔ unseal zero ★)
    ≡ gen ★ (((＇ zero) ？) ︔ ((＇ zero) !))
dual-inst-example-dual≡ = refl

dual-inst-example-dual⊢ :
  zero ∣ [] ⊢ - inst ★ (seal ★ zero ︔ unseal zero ★) ∶ ★ =⇒ `∀ ★
dual-inst-example-dual⊢ =
  cast-gen wf★ {A-ok = refl}
    (cast-seq (cast-untag (wfVar z<s) (＇ zero) {ok = refl})
              (cast-tag (wfVar z<s) (＇ zero) {ok = refl}))

dual-inst-tag-counterexample-not-typable :
  zero ∣ [] ⊢ inst ★ ((＇ zero) !) ∶ `∀ (＇ zero) =⇒ ★ →
  ⊥
dual-inst-tag-counterexample-not-typable
    (cast-inst h★ (cast-tag hα (＇ zero) {ok = ()}))

dual-inst-tag-counterexample-dual≡ :
  - inst ★ ((＇ zero) !) ≡ gen ★ (seal ★ zero)
dual-inst-tag-counterexample-dual≡ = refl

dual-inst-tag-counterexample-dual-not-typable :
  zero ∣ [] ⊢ - inst ★ ((＇ zero) !) ∶ ★ =⇒ `∀ (＇ zero) →
  ⊥
dual-inst-tag-counterexample-dual-not-typable (cast-gen h★ (cast-seal hA ()))

------------------------------------------------------------------------
-- Duality as an involution
------------------------------------------------------------------------

data OppMode : DualMode → DualMode → Set where
  opp-normal : OppMode normal normal
  opp-gen-inst : OppMode tag-to-seal seal-to-tag
  opp-inst-gen : OppMode seal-to-tag tag-to-seal

Oppᵈ : DualEnv → DualEnv → Set
Oppᵈ μ ν = ∀ X → OppMode (μ X) (ν X)

opp-normalᵈ : Oppᵈ normalᵈ normalᵈ
opp-normalᵈ X = opp-normal

opp-extᵈ :
  ∀ {μ ν} →
  Oppᵈ μ ν →
  Oppᵈ (extᵈ μ) (extᵈ ν)
opp-extᵈ opp zero = opp-normal
opp-extᵈ opp (suc X) = opp X

opp-gen-instᵈ :
  ∀ {μ ν} →
  Oppᵈ μ ν →
  Oppᵈ (genᵈ μ) (instᵈ ν)
opp-gen-instᵈ opp zero = opp-gen-inst
opp-gen-instᵈ opp (suc X) = opp X

opp-inst-genᵈ :
  ∀ {μ ν} →
  Oppᵈ μ ν →
  Oppᵈ (instᵈ μ) (genᵈ ν)
opp-inst-genᵈ opp zero = opp-inst-gen
opp-inst-genᵈ opp (suc X) = opp X

data SealOk (μ : DualEnv) (A : Ty) (α : TyVar) : Set where
  seal-ok-normal : μ α ≡ normal → SealOk μ A α
  seal-ok-★ : A ≡ ★ → SealOk μ A α

tag-to-seal≢normal : tag-to-seal ≢ normal
tag-to-seal≢normal ()

seal-to-tag≢normal : seal-to-tag ≢ normal
seal-to-tag≢normal ()

data DualSafe (μ : DualEnv) : Coercion → Set where
  safe-id : ∀ {A} → DualSafe μ (id A)
  safe-seq : ∀ {c d} → DualSafe μ c → DualSafe μ d →
    DualSafe μ (c ︔ d)
  safe-fun : ∀ {c d} → DualSafe μ c → DualSafe μ d →
    DualSafe μ (c ↦ d)
  safe-all : ∀ {c} → DualSafe (extᵈ μ) c → DualSafe μ (`∀ c)
  safe-tag : ∀ {G} → DualSafe μ (G !)
  safe-untag : ∀ {G} → DualSafe μ (G ？)
  safe-seal : ∀ {A α} → SealOk μ A α → DualSafe μ (seal A α)
  safe-unseal : ∀ {α A} → SealOk μ A α → DualSafe μ (unseal α A)
  safe-gen : ∀ {A c} → DualSafe (genᵈ μ) c →
    DualSafe μ (gen A c)
  safe-inst : ∀ {B c} → DualSafe (instᵈ μ) c →
    DualSafe μ (inst B c)

StoreDualSafe : DualEnv → Store → Set
StoreDualSafe μ Σ =
  ∀ {α A} →
  (α , A) ∈ Σ →
  SealOk μ A α

store-dual-safe-normal :
  ∀ {Σ} →
  StoreDualSafe normalᵈ Σ
store-dual-safe-normal α∈Σ = seal-ok-normal refl

seal-ok-extᵈ :
  ∀ {μ A α} →
  SealOk μ A α →
  SealOk (extᵈ μ) (renameᵗ suc A) (suc α)
seal-ok-extᵈ (seal-ok-normal eq) = seal-ok-normal eq
seal-ok-extᵈ (seal-ok-★ refl) = seal-ok-★ refl

seal-ok-genᵈ :
  ∀ {μ A α} →
  SealOk μ A α →
  SealOk (genᵈ μ) (renameᵗ suc A) (suc α)
seal-ok-genᵈ (seal-ok-normal eq) = seal-ok-normal eq
seal-ok-genᵈ (seal-ok-★ refl) = seal-ok-★ refl

seal-ok-instᵈ :
  ∀ {μ A α} →
  SealOk μ A α →
  SealOk (instᵈ μ) (renameᵗ suc A) (suc α)
seal-ok-instᵈ (seal-ok-normal eq) = seal-ok-normal eq
seal-ok-instᵈ (seal-ok-★ refl) = seal-ok-★ refl

store-dual-safe-⟰ᵗ-extᵈ :
  ∀ {μ Σ} →
  StoreDualSafe μ Σ →
  StoreDualSafe (extᵈ μ) (⟰ᵗ Σ)
store-dual-safe-⟰ᵗ-extᵈ {Σ = []} safeΣ ()
store-dual-safe-⟰ᵗ-extᵈ {Σ = (α , A) ∷ Σ} safeΣ (here refl) =
  seal-ok-extᵈ (safeΣ (here refl))
store-dual-safe-⟰ᵗ-extᵈ {Σ = (α , A) ∷ Σ} safeΣ (there α∈Σ) =
  store-dual-safe-⟰ᵗ-extᵈ (λ β∈Σ → safeΣ (there β∈Σ)) α∈Σ

store-dual-safe-⟰ᵗ-genᵈ :
  ∀ {μ Σ} →
  StoreDualSafe μ Σ →
  StoreDualSafe (genᵈ μ) (⟰ᵗ Σ)
store-dual-safe-⟰ᵗ-genᵈ {Σ = []} safeΣ ()
store-dual-safe-⟰ᵗ-genᵈ {Σ = (α , A) ∷ Σ} safeΣ (here refl) =
  seal-ok-genᵈ (safeΣ (here refl))
store-dual-safe-⟰ᵗ-genᵈ {Σ = (α , A) ∷ Σ} safeΣ (there α∈Σ) =
  store-dual-safe-⟰ᵗ-genᵈ (λ β∈Σ → safeΣ (there β∈Σ)) α∈Σ

store-dual-safe-⟰ᵗ-instᵈ :
  ∀ {μ Σ} →
  StoreDualSafe μ Σ →
  StoreDualSafe (instᵈ μ) (⟰ᵗ Σ)
store-dual-safe-⟰ᵗ-instᵈ {Σ = []} safeΣ ()
store-dual-safe-⟰ᵗ-instᵈ {Σ = (α , A) ∷ Σ} safeΣ (here refl) =
  seal-ok-instᵈ (safeΣ (here refl))
store-dual-safe-⟰ᵗ-instᵈ {Σ = (α , A) ∷ Σ} safeΣ (there α∈Σ) =
  store-dual-safe-⟰ᵗ-instᵈ (λ β∈Σ → safeΣ (there β∈Σ)) α∈Σ

store-dual-safe-instᵈ :
  ∀ {μ Σ} →
  StoreDualSafe μ Σ →
  StoreDualSafe (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ Σ)
store-dual-safe-instᵈ safeΣ (here refl) = seal-ok-★ refl
store-dual-safe-instᵈ safeΣ (there α∈Σ) =
  store-dual-safe-⟰ᵗ-instᵈ safeΣ α∈Σ

coercion-dual-safe :
  ∀ {Δ Σ c A B μ} →
  StoreDualSafe μ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  DualSafe μ c
coercion-dual-safe safeΣ (cast-id hA) = safe-id
coercion-dual-safe safeΣ (cast-seal hA α∈Σ) =
  safe-seal (safeΣ α∈Σ)
coercion-dual-safe safeΣ (cast-unseal hA α∈Σ) =
  safe-unseal (safeΣ α∈Σ)
coercion-dual-safe safeΣ (cast-seq c⊢ d⊢) =
  safe-seq (coercion-dual-safe safeΣ c⊢)
           (coercion-dual-safe safeΣ d⊢)
coercion-dual-safe safeΣ (cast-tag hG gG) = safe-tag
coercion-dual-safe safeΣ (cast-untag hH gH) = safe-untag
coercion-dual-safe safeΣ (cast-fun c⊢ d⊢) =
  safe-fun (coercion-dual-safe safeΣ c⊢)
           (coercion-dual-safe safeΣ d⊢)
coercion-dual-safe safeΣ (cast-all c⊢) =
  safe-all (coercion-dual-safe (store-dual-safe-⟰ᵗ-extᵈ safeΣ) c⊢)
coercion-dual-safe safeΣ (cast-inst hB c⊢) =
  safe-inst (coercion-dual-safe (store-dual-safe-instᵈ safeΣ) c⊢)
coercion-dual-safe safeΣ (cast-gen hA c⊢) =
  safe-gen (coercion-dual-safe (store-dual-safe-⟰ᵗ-genᵈ safeΣ) c⊢)

dualTag-involutive :
  ∀ {μ ν G} →
  Oppᵈ μ ν →
  dualWith ν (dualTag μ G) ≡ G !
dualTag-involutive {μ = μ} {ν = ν} {G = ＇ α} opp
    with μ α in μα | ν α in να | opp α
dualTag-involutive {G = ＇ α} opp | normal | normal | opp-normal
    rewrite μα | να = refl
dualTag-involutive {G = ＇ α} opp
    | tag-to-seal | seal-to-tag | opp-gen-inst
    rewrite μα | να = refl
dualTag-involutive {G = ＇ α} opp
    | seal-to-tag | tag-to-seal | opp-inst-gen
    rewrite μα | να = refl
dualTag-involutive {G = ‵ ι} opp = refl
dualTag-involutive {G = ★} opp = refl
dualTag-involutive {G = A ⇒ B} opp = refl
dualTag-involutive {G = `∀ A} opp = refl

dualUntag-involutive :
  ∀ {μ ν G} →
  Oppᵈ μ ν →
  dualWith ν (dualUntag μ G) ≡ G ？
dualUntag-involutive {μ = μ} {ν = ν} {G = ＇ α} opp
    with μ α in μα | ν α in να | opp α
dualUntag-involutive {G = ＇ α} opp | normal | normal | opp-normal
    rewrite μα | να = refl
dualUntag-involutive {G = ＇ α} opp
    | tag-to-seal | seal-to-tag | opp-gen-inst
    rewrite μα | να = refl
dualUntag-involutive {G = ＇ α} opp
    | seal-to-tag | tag-to-seal | opp-inst-gen
    rewrite μα | να = refl
dualUntag-involutive {G = ‵ ι} opp = refl
dualUntag-involutive {G = ★} opp = refl
dualUntag-involutive {G = A ⇒ B} opp = refl
dualUntag-involutive {G = `∀ A} opp = refl

dualSeal-involutive :
  ∀ {μ ν A α} →
  Oppᵈ μ ν →
  SealOk μ A α →
  dualWith ν (dualSeal μ A α) ≡ seal A α
dualSeal-involutive {μ = μ} {ν = ν} {A = A} {α = α} opp ok
    with μ α in μα | ν α in να | opp α | ok
dualSeal-involutive opp ok | normal | normal | opp-normal | _
    rewrite μα | να = refl
dualSeal-involutive opp ok
    | tag-to-seal | seal-to-tag | opp-gen-inst | seal-ok-normal eq =
  ⊥-elim (tag-to-seal≢normal (trans (sym μα) eq))
dualSeal-involutive opp ok
    | tag-to-seal | seal-to-tag | opp-gen-inst | seal-ok-★ refl
    rewrite μα | να = refl
dualSeal-involutive opp ok
    | seal-to-tag | tag-to-seal | opp-inst-gen | seal-ok-normal eq =
  ⊥-elim (seal-to-tag≢normal (trans (sym μα) eq))
dualSeal-involutive opp ok
    | seal-to-tag | tag-to-seal | opp-inst-gen | seal-ok-★ refl
    rewrite μα | να = refl

dualUnseal-involutive :
  ∀ {μ ν α A} →
  Oppᵈ μ ν →
  SealOk μ A α →
  dualWith ν (dualUnseal μ α A) ≡ unseal α A
dualUnseal-involutive {μ = μ} {ν = ν} {α = α} {A = A} opp ok
    with μ α in μα | ν α in να | opp α | ok
dualUnseal-involutive opp ok | normal | normal | opp-normal | _
    rewrite μα | να = refl
dualUnseal-involutive opp ok
    | tag-to-seal | seal-to-tag | opp-gen-inst | seal-ok-normal eq =
  ⊥-elim (tag-to-seal≢normal (trans (sym μα) eq))
dualUnseal-involutive opp ok
    | tag-to-seal | seal-to-tag | opp-gen-inst | seal-ok-★ refl
    rewrite μα | να = refl
dualUnseal-involutive opp ok
    | seal-to-tag | tag-to-seal | opp-inst-gen | seal-ok-normal eq =
  ⊥-elim (seal-to-tag≢normal (trans (sym μα) eq))
dualUnseal-involutive opp ok
    | seal-to-tag | tag-to-seal | opp-inst-gen | seal-ok-★ refl
    rewrite μα | να = refl

dualWith-involutive :
  ∀ {μ ν c} →
  Oppᵈ μ ν →
  DualSafe μ c →
  dualWith ν (dualWith μ c) ≡ c
dualWith-involutive opp safe-id = refl
dualWith-involutive opp (safe-seq safe-c safe-d) =
  cong₂ _︔_ (dualWith-involutive opp safe-c)
             (dualWith-involutive opp safe-d)
dualWith-involutive opp (safe-fun safe-c safe-d) =
  cong₂ _↦_ (dualWith-involutive opp safe-c)
             (dualWith-involutive opp safe-d)
dualWith-involutive opp (safe-all safe-c) =
  cong `∀ (dualWith-involutive (opp-extᵈ opp) safe-c)
dualWith-involutive opp safe-tag = dualTag-involutive opp
dualWith-involutive opp safe-untag = dualUntag-involutive opp
dualWith-involutive opp (safe-seal ok) = dualSeal-involutive opp ok
dualWith-involutive opp (safe-unseal ok) = dualUnseal-involutive opp ok
dualWith-involutive opp (safe-gen safe-c) =
  cong (gen _) (dualWith-involutive (opp-gen-instᵈ opp) safe-c)
dualWith-involutive opp (safe-inst safe-c) =
  cong (inst _) (dualWith-involutive (opp-inst-genᵈ opp) safe-c)

dual-involutive :
  ∀ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  - (- c) ≡ c
dual-involutive c⊢ =
  dualWith-involutive opp-normalᵈ
    (coercion-dual-safe store-dual-safe-normal c⊢)

dual-raw-involutive-counterexample :
  - (- gen ★ (seal (‵ `ℕ) zero)) ≡ gen ★ (seal (‵ `ℕ) zero) →
  ⊥
dual-raw-involutive-counterexample ()

dual-raw-involutive-counterexample-not-typable :
  ∀ {Δ Σ A B} →
  Δ ∣ Σ ⊢ gen ★ (seal (‵ `ℕ) zero) ∶ A =⇒ B →
  ⊥
dual-raw-involutive-counterexample-not-typable (cast-gen h★ ())

------------------------------------------------------------------------
-- Coercion typing under type renaming
------------------------------------------------------------------------

ModeRename : Renameᵗ → DualEnv → DualEnv → Set
ModeRename ρ μ ν = ∀ X → mode≤ (μ X) (ν (ρ X)) ≡ true

ModeRename-normal :
  ∀ {ρ} →
  ModeRename ρ normalᵈ normalᵈ
ModeRename-normal X = refl

ModeRename-to-normal :
  ∀ {ρ μ} →
  ModeRename ρ μ normalᵈ
ModeRename-to-normal {μ = μ} X with μ X
ModeRename-to-normal X | normal = refl
ModeRename-to-normal X | tag-to-seal = refl
ModeRename-to-normal X | seal-to-tag = refl

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

mode≤-tag :
  ∀ {m n} →
  mode≤ m n ≡ true →
  tagModeAllowed m ≡ true →
  tagModeAllowed n ≡ true
mode≤-tag {normal} {normal} rel ok = refl
mode≤-tag {normal} {tag-to-seal} () ok
mode≤-tag {normal} {seal-to-tag} () ok
mode≤-tag {tag-to-seal} {normal} rel ok = refl
mode≤-tag {tag-to-seal} {tag-to-seal} rel ok = refl
mode≤-tag {tag-to-seal} {seal-to-tag} () ok
mode≤-tag {seal-to-tag} {normal} rel ()
mode≤-tag {seal-to-tag} {tag-to-seal} () ok
mode≤-tag {seal-to-tag} {seal-to-tag} rel ()

mode≤-seal :
  ∀ {m n} →
  mode≤ m n ≡ true →
  sealModeAllowed m ≡ true →
  sealModeAllowed n ≡ true
mode≤-seal {normal} {normal} rel ok = refl
mode≤-seal {normal} {tag-to-seal} () ok
mode≤-seal {normal} {seal-to-tag} () ok
mode≤-seal {tag-to-seal} {normal} rel ()
mode≤-seal {tag-to-seal} {tag-to-seal} rel ()
mode≤-seal {tag-to-seal} {seal-to-tag} () ok
mode≤-seal {seal-to-tag} {normal} rel ok = refl
mode≤-seal {seal-to-tag} {tag-to-seal} () ok
mode≤-seal {seal-to-tag} {seal-to-tag} rel ok = refl

modeRename-tyAllowed :
  ∀ {ρ μ ν A} →
  ModeRename ρ μ ν →
  tyAllowed μ A ≡ true →
  tyAllowed ν (renameᵗ ρ A) ≡ true
modeRename-tyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = ＇ α} rel ok
    with μ α | ν (ρ α) | rel α | ok
modeRename-tyAllowed rel ok | normal | normal | relα | okα = refl
modeRename-tyAllowed rel ok | normal | tag-to-seal | () | okα
modeRename-tyAllowed rel ok | normal | seal-to-tag | () | okα
modeRename-tyAllowed rel ok | tag-to-seal | n | relα | ()
modeRename-tyAllowed rel ok | seal-to-tag | n | relα | ()
modeRename-tyAllowed {A = ‵ ι} rel ok = refl
modeRename-tyAllowed {A = ★} rel ok = refl
modeRename-tyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = A ⇒ B} rel ok
    with tyAllowed μ A in okA | tyAllowed μ B in okB
modeRename-tyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = A ⇒ B} rel ok
    | true | true
    with modeRename-tyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = A} rel okA
       | modeRename-tyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = B} rel okB
modeRename-tyAllowed {A = A ⇒ B} rel ok | true | true | okA′ | okB′
    rewrite okA′ | okB′ = refl
modeRename-tyAllowed rel () | false | b
modeRename-tyAllowed rel () | true | false
modeRename-tyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = `∀ A} rel ok =
  modeRename-tyAllowed
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
modeRename-tagTyAllowed {ρ = ρ} {μ = μ} {ν = ν} {G = A ⇒ B} rel ok
    with tyAllowed μ A in okA | tyAllowed μ B in okB
modeRename-tagTyAllowed {ρ = ρ} {μ = μ} {ν = ν} {G = A ⇒ B} rel ok
    | true | true
    with modeRename-tyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = A} rel okA
       | modeRename-tyAllowed {ρ = ρ} {μ = μ} {ν = ν} {A = B} rel okB
modeRename-tagTyAllowed {G = A ⇒ B} rel ok | true | true | okA′ | okB′
    rewrite okA′ | okB′ = refl
modeRename-tagTyAllowed rel () | false | b
modeRename-tagTyAllowed rel () | true | false
modeRename-tagTyAllowed {ρ = ρ} {μ = μ} {ν = ν} {G = `∀ A} rel ok =
  modeRename-tyAllowed
    {ρ = extᵗ ρ} {μ = extᵈ μ} {ν = extᵈ ν} {A = A}
    (ModeRename-ext rel) ok

modeRename-sealTyAllowed :
  ∀ {ρ μ ν α} →
  ModeRename ρ μ ν →
  sealTyAllowed μ α ≡ true →
  sealTyAllowed ν (ρ α) ≡ true
modeRename-sealTyAllowed {α = α} rel ok =
  mode≤-seal (rel α) ok

ModeAllNormal : DualEnv → Set
ModeAllNormal μ = ∀ X → μ X ≡ normal

ModeAllNormal-normal :
  ModeAllNormal normalᵈ
ModeAllNormal-normal X = refl

ModeAllNormal-ext :
  ∀ {μ} →
  ModeAllNormal μ →
  ModeAllNormal (extᵈ μ)
ModeAllNormal-ext all zero = refl
ModeAllNormal-ext all (suc X) = all X

tyAllowed-allNormal :
  ∀ {μ} →
  ModeAllNormal μ →
  ∀ A →
  tyAllowed μ A ≡ true
tyAllowed-allNormal all (＇ α) rewrite all α = refl
tyAllowed-allNormal all (‵ ι) = refl
tyAllowed-allNormal all ★ = refl
tyAllowed-allNormal all (A ⇒ B)
  rewrite tyAllowed-allNormal all A
        | tyAllowed-allNormal all B = refl
tyAllowed-allNormal all (`∀ A) =
  tyAllowed-allNormal (ModeAllNormal-ext all) A

tagTyAllowed-allNormal :
  ∀ {μ} →
  ModeAllNormal μ →
  ∀ G →
  tagTyAllowed μ G ≡ true
tagTyAllowed-allNormal all (＇ α) rewrite all α = refl
tagTyAllowed-allNormal all (‵ ι) = refl
tagTyAllowed-allNormal all ★ = refl
tagTyAllowed-allNormal all (A ⇒ B)
  rewrite tyAllowed-allNormal all A
        | tyAllowed-allNormal all B = refl
tagTyAllowed-allNormal all (`∀ A) =
  tyAllowed-allNormal (ModeAllNormal-ext all) A

tyAllowed-normal :
  ∀ A →
  tyAllowed normalᵈ A ≡ true
tyAllowed-normal = tyAllowed-allNormal ModeAllNormal-normal

tagTyAllowed-normal :
  ∀ G →
  tagTyAllowed normalᵈ G ≡ true
tagTyAllowed-normal = tagTyAllowed-allNormal ModeAllNormal-normal

sealTyAllowed-normal :
  ∀ α →
  sealTyAllowed normalᵈ α ≡ true
sealTyAllowed-normal α = refl

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

modeIncl-tyAllowed :
  ∀ {μ ν A} →
  ModeIncl μ ν →
  tyAllowed μ A ≡ true →
  tyAllowed ν A ≡ true
modeIncl-tyAllowed {μ = μ} {ν = ν} {A = A} incl ok =
  subst
    (λ T → tyAllowed ν T ≡ true)
    (renameᵗ-id A)
    (modeRename-tyAllowed
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

modeIncl-sealTyAllowed :
  ∀ {μ ν α} →
  ModeIncl μ ν →
  sealTyAllowed μ α ≡ true →
  sealTyAllowed ν α ≡ true
modeIncl-sealTyAllowed {μ = μ} {ν = ν} {α = α} incl ok =
  modeRename-sealTyAllowed
    {ρ = λ X → X} {μ = μ} {ν = ν} {α = α} incl ok

coercion-mode-relax :
  ∀ {μ ν Δ Σ c A B} →
  ModeIncl μ ν →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  ν ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
coercion-mode-relax incl (cast-id {A = A} hA {ok = ok}) =
  cast-id hA {ok = modeIncl-tyAllowed {A = A} incl ok}
coercion-mode-relax incl
    (cast-seal {α = α} {A = A} hA α∈Σ {A-ok = A-ok}
      {α-ok = α-ok}) =
  cast-seal hA α∈Σ
    {A-ok = modeIncl-tyAllowed {A = A} incl A-ok}
    {α-ok = modeIncl-sealTyAllowed {α = α} incl α-ok}
coercion-mode-relax incl
    (cast-unseal {α = α} {A = A} hA α∈Σ {A-ok = A-ok}
      {α-ok = α-ok}) =
  cast-unseal hA α∈Σ
    {A-ok = modeIncl-tyAllowed {A = A} incl A-ok}
    {α-ok = modeIncl-sealTyAllowed {α = α} incl α-ok}
coercion-mode-relax incl (cast-seq c⊢ d⊢) =
  cast-seq (coercion-mode-relax incl c⊢)
           (coercion-mode-relax incl d⊢)
coercion-mode-relax incl (cast-tag {G = G} hG gG {ok = ok}) =
  cast-tag hG gG {ok = modeIncl-tagTyAllowed {G = G} incl ok}
coercion-mode-relax incl (cast-untag {H = H} hH gH {ok = ok}) =
  cast-untag hH gH {ok = modeIncl-tagTyAllowed {G = H} incl ok}
coercion-mode-relax incl (cast-fun c⊢ d⊢) =
  cast-fun (coercion-mode-relax incl c⊢)
           (coercion-mode-relax incl d⊢)
coercion-mode-relax incl (cast-all c⊢) =
  cast-all (coercion-mode-relax (ModeIncl-ext incl) c⊢)
coercion-mode-relax incl (cast-inst {B = B} hB {B-ok = B-ok} c⊢) =
  cast-inst hB
    {B-ok = modeIncl-tyAllowed {A = B} incl B-ok}
    (coercion-mode-relax (ModeIncl-inst incl) c⊢)
coercion-mode-relax incl (cast-gen {A = A} hA {A-ok = A-ok} c⊢) =
  cast-gen hA
    {A-ok = modeIncl-tyAllowed {A = A} incl A-ok}
    (coercion-mode-relax (ModeIncl-gen incl) c⊢)

coercion-renameᵗᵐ :
  ∀ {Δ Δ′ Σ c A B ρ μ ν} →
  TyRenameWf Δ Δ′ ρ →
  ModeRename ρ μ ν →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  ν ∣ Δ′ ∣ renameStoreᵗ ρ Σ ⊢ renameᶜ ρ c
    ∶ renameᵗ ρ A =⇒ renameᵗ ρ B
coercion-renameᵗᵐ hρ rel (cast-id {A = A} hA {ok = ok}) =
  cast-id (renameᵗ-preserves-WfTy hA hρ)
    {ok = modeRename-tyAllowed {A = A} rel ok}
coercion-renameᵗᵐ {ρ = ρ} {μ = μ} {ν = ν} hρ rel
    (cast-seal {α = α} {A = A} hA α∈Σ {A-ok = A-ok}
      {α-ok = α-ok}) =
  cast-seal
    (renameᵗ-preserves-WfTy hA hρ)
    (∈-renameStoreᵗ _ α∈Σ)
    {A-ok = modeRename-tyAllowed
      {ρ = ρ} {μ = μ} {ν = ν} {A = A} rel A-ok}
    {α-ok = modeRename-sealTyAllowed
      {ρ = ρ} {μ = μ} {ν = ν} {α = α} rel α-ok}
coercion-renameᵗᵐ {ρ = ρ} {μ = μ} {ν = ν} hρ rel
    (cast-unseal {α = α} {A = A} hA α∈Σ {A-ok = A-ok}
      {α-ok = α-ok}) =
  cast-unseal
    (renameᵗ-preserves-WfTy hA hρ)
    (∈-renameStoreᵗ _ α∈Σ)
    {A-ok = modeRename-tyAllowed
      {ρ = ρ} {μ = μ} {ν = ν} {A = A} rel A-ok}
    {α-ok = modeRename-sealTyAllowed
      {ρ = ρ} {μ = μ} {ν = ν} {α = α} rel α-ok}
coercion-renameᵗᵐ hρ rel (cast-seq c⊢ d⊢) =
  cast-seq (coercion-renameᵗᵐ hρ rel c⊢)
           (coercion-renameᵗᵐ hρ rel d⊢)
coercion-renameᵗᵐ hρ rel (cast-tag {G = G} hG gG {ok = ok}) =
  cast-tag
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-ground _ gG)
    {ok = modeRename-tagTyAllowed {G = G} rel ok}
coercion-renameᵗᵐ hρ rel (cast-untag {H = H} hH gH {ok = ok}) =
  cast-untag
    (renameᵗ-preserves-WfTy hH hρ)
    (renameᵗ-ground _ gH)
    {ok = modeRename-tagTyAllowed {G = H} rel ok}
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
    (cast-inst {B = B} hB {B-ok = B-ok} c⊢) =
  cast-inst
    (renameᵗ-preserves-WfTy hB hρ)
    {B-ok = modeRename-tyAllowed {A = B} rel B-ok}
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
    (cast-gen {A = A} hA {A-ok = A-ok} c⊢) =
  cast-gen
    (renameᵗ-preserves-WfTy hA hρ)
    {A-ok = modeRename-tyAllowed {A = A} rel A-ok}
    (subst
      (λ T → _ ∣ _ ∣ _ ⊢ renameᶜ (extᵗ ρ) _ ∶ T =⇒ _)
      (renameᵗ-ext-suc-comm ρ A)
      (subst
        (λ Σ′ → _ ∣ _ ∣ Σ′ ⊢ renameᶜ (extᵗ ρ) _ ∶ _ =⇒ _)
        (renameStoreᵗ-ext-suc-comm ρ _)
        (coercion-renameᵗᵐ (TyRenameWf-ext hρ)
          (ModeRename-gen rel) c⊢)))

coercion-renameᵗ :
  ∀ {Δ Δ′ Σ c A B ρ} →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ′ ∣ renameStoreᵗ ρ Σ ⊢ renameᶜ ρ c
    ∶ renameᵗ ρ A =⇒ renameᵗ ρ B
coercion-renameᵗ {ρ = ρ} hρ c⊢ =
  coercion-renameᵗᵐ hρ (ModeRename-normal {ρ = ρ}) c⊢

coercion-openᵐ :
  ∀ {μ Δ Σ c A B α C} →
  α < suc Δ →
  μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , C) ∷ Σ ⊢ c [ α ]ᶜ
    ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-openᵐ {μ = μ} {Σ = Σ} {α = α} α<sucΔ c⊢ =
  coercion-weaken ≤-refl StoreIncl-drop
    (subst
      (λ Σ′ → _ ∣ Σ′ ⊢ _ ∶ _ =⇒ _)
      (renameStoreᵗ-single-suc-cancel α Σ)
      (coercion-renameᵗᵐ
        (singleRenameᵗ-Wf α<sucΔ)
        (ModeRename-to-normal {ρ = singleRenameᵗ α} {μ = μ})
        c⊢))

coercion-open :
  ∀ {Δ Σ c A B α C} →
  α < suc Δ →
  suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , C) ∷ Σ ⊢ c [ α ]ᶜ
    ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open = coercion-openᵐ

coercion-open-headᵐ :
  ∀ {μ Δ Σ c A B α C} →
  α < suc Δ →
  μ ∣ suc Δ ∣ (0 , C) ∷ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , renameᵗ (singleRenameᵗ α) C) ∷ Σ
    ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open-headᵐ
    {μ = μ} {Δ = Δ} {Σ = Σ} {c = c} {A = A} {B = B} {α = α}
    α<sucΔ c⊢ =
  subst
    (λ Σ′ → suc Δ ∣ Σ′ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ)
    (cong₂ _∷_ refl (renameStoreᵗ-single-suc-cancel α Σ))
    (coercion-renameᵗᵐ
      (singleRenameᵗ-Wf α<sucΔ)
      (ModeRename-to-normal {ρ = singleRenameᵗ α} {μ = μ})
      c⊢)

coercion-open-head :
  ∀ {Δ Σ c A B α C} →
  α < suc Δ →
  suc Δ ∣ (0 , C) ∷ ⟰ᵗ Σ ⊢ c ∶ A =⇒ B →
  suc Δ ∣ (α , renameᵗ (singleRenameᵗ α) C) ∷ Σ
    ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ =⇒ B [ α ]ᴿ
coercion-open-head = coercion-open-headᵐ

------------------------------------------------------------------------
-- Coercion duality flips typed endpoints
------------------------------------------------------------------------

zero∉-⟰ᵗ :
  ∀ {Σ A} →
  (zero , A) ∈ ⟰ᵗ Σ →
  ⊥
zero∉-⟰ᵗ {Σ = []} ()
zero∉-⟰ᵗ {Σ = (α , A) ∷ Σ} (here ())
zero∉-⟰ᵗ {Σ = (α , A) ∷ Σ} (there x∈) =
  zero∉-⟰ᵗ x∈

suc∈-cons-zero-tail :
  ∀ {Σ α A C} →
  (suc α , A) ∈ ((zero , C) ∷ ⟰ᵗ Σ) →
  (suc α , A) ∈ ⟰ᵗ Σ
suc∈-cons-zero-tail (here ())
suc∈-cons-zero-tail (there x∈) = x∈

∈-⟰ᵗ-inv :
  ∀ {Σ α A} →
  (suc α , A) ∈ ⟰ᵗ Σ →
  ∃[ B ] ((α , B) ∈ Σ × A ≡ renameᵗ suc B)
∈-⟰ᵗ-inv {Σ = []} ()
∈-⟰ᵗ-inv {Σ = (α , A) ∷ Σ} (here refl) =
  A , here refl , refl
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there x∈) with ∈-⟰ᵗ-inv x∈
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there x∈) | A , αA∈Σ , eq =
  A , there αA∈Σ , eq

record DualStore
    (μ : DualEnv) (Σ : Store) (ν : DualEnv) (Π : Store) : Set where
  field
    tagSeal∈ :
      ∀ {α} →
      μ α ≡ tag-to-seal →
      (α , ★) ∈ Π
    sealTag∈ :
      ∀ {α} →
      μ α ≡ seal-to-tag →
      (α , ★) ∈ Σ
    sealTag★ :
      ∀ {α A} →
      μ α ≡ seal-to-tag →
      (α , A) ∈ Σ →
      A ≡ ★
    normal∈ :
      ∀ {α A} →
      μ α ≡ normal →
      (α , A) ∈ Σ →
      (α , A) ∈ Π

open DualStore

dualStore-normal :
  ∀ {Σ} →
  DualStore normalᵈ Σ normalᵈ Σ
dualStore-normal =
  record
    { tagSeal∈ = λ ()
    ; sealTag∈ = λ ()
    ; sealTag★ = λ ()
    ; normal∈ = λ eq αA∈Σ → αA∈Σ
    }

dualStore-ext :
  ∀ {μ ν Σ Π} →
  DualStore μ Σ ν Π →
  DualStore (extᵈ μ) (⟰ᵗ Σ) (extᵈ ν) (⟰ᵗ Π)
dualStore-ext ds =
  record
    { tagSeal∈ = tag
    ; sealTag∈ = sealCase
    ; sealTag★ = seal★Case
    ; normal∈ = norm
    }
  where
    tag :
      ∀ {α} →
      extᵈ _ α ≡ tag-to-seal →
      (α , ★) ∈ ⟰ᵗ _
    tag {zero} ()
    tag {suc α} eq = ∈-renameStoreᵗ suc (tagSeal∈ ds eq)

    sealCase :
      ∀ {α} →
      extᵈ _ α ≡ seal-to-tag →
      (α , ★) ∈ ⟰ᵗ _
    sealCase {zero} ()
    sealCase {suc α} eq = ∈-renameStoreᵗ suc (sealTag∈ ds eq)

    seal★Case :
      ∀ {α A} →
      extᵈ _ α ≡ seal-to-tag →
      (α , A) ∈ ⟰ᵗ _ →
      A ≡ ★
    seal★Case {zero} () αA∈Σ
    seal★Case {suc α} {A} eq αA∈Σ with ∈-⟰ᵗ-inv αA∈Σ
    seal★Case {suc α} eq αA∈Σ | B , αB∈Σ , refl
      rewrite sealTag★ ds eq αB∈Σ = refl

    norm :
      ∀ {α A} →
      extᵈ _ α ≡ normal →
      (α , A) ∈ ⟰ᵗ _ →
      (α , A) ∈ ⟰ᵗ _
    norm {zero} eq αA∈Σ = ⊥-elim (zero∉-⟰ᵗ αA∈Σ)
    norm {suc α} {A} eq αA∈Σ with ∈-⟰ᵗ-inv αA∈Σ
    norm {suc α} eq αA∈Σ | B , αB∈Σ , refl =
      ∈-renameStoreᵗ suc (normal∈ ds eq αB∈Σ)

dualStore-gen-inst :
  ∀ {μ ν Σ Π} →
  DualStore μ Σ ν Π →
  DualStore (genᵈ μ) (⟰ᵗ Σ) (instᵈ ν) ((zero , ★) ∷ ⟰ᵗ Π)
dualStore-gen-inst ds =
  record
    { tagSeal∈ = tag
    ; sealTag∈ = sealCase
    ; sealTag★ = seal★Case
    ; normal∈ = norm
    }
  where
    tag :
      ∀ {α} →
      genᵈ _ α ≡ tag-to-seal →
      (α , ★) ∈ ((zero , ★) ∷ ⟰ᵗ _)
    tag {zero} eq = here refl
    tag {suc α} eq = there (∈-renameStoreᵗ suc (tagSeal∈ ds eq))

    sealCase :
      ∀ {α} →
      genᵈ _ α ≡ seal-to-tag →
      (α , ★) ∈ ⟰ᵗ _
    sealCase {zero} ()
    sealCase {suc α} eq = ∈-renameStoreᵗ suc (sealTag∈ ds eq)

    seal★Case :
      ∀ {α A} →
      genᵈ _ α ≡ seal-to-tag →
      (α , A) ∈ ⟰ᵗ _ →
      A ≡ ★
    seal★Case {zero} () αA∈Σ
    seal★Case {suc α} {A} eq αA∈Σ with ∈-⟰ᵗ-inv αA∈Σ
    seal★Case {suc α} eq αA∈Σ | B , αB∈Σ , refl
      rewrite sealTag★ ds eq αB∈Σ = refl

    norm :
      ∀ {α A} →
      genᵈ _ α ≡ normal →
      (α , A) ∈ ⟰ᵗ _ →
      (α , A) ∈ ((zero , ★) ∷ ⟰ᵗ _)
    norm {zero} () αA∈Σ
    norm {suc α} {A} eq αA∈Σ with ∈-⟰ᵗ-inv αA∈Σ
    norm {suc α} eq αA∈Σ | B , αB∈Σ , refl =
      there (∈-renameStoreᵗ suc (normal∈ ds eq αB∈Σ))

dualStore-inst-gen :
  ∀ {μ ν Σ Π} →
  DualStore μ Σ ν Π →
  DualStore (instᵈ μ) ((zero , ★) ∷ ⟰ᵗ Σ) (genᵈ ν) (⟰ᵗ Π)
dualStore-inst-gen ds =
  record
    { tagSeal∈ = tag
    ; sealTag∈ = sealCase
    ; sealTag★ = seal★Case
    ; normal∈ = norm
    }
  where
    tag :
      ∀ {α} →
      instᵈ _ α ≡ tag-to-seal →
      (α , ★) ∈ ⟰ᵗ _
    tag {zero} ()
    tag {suc α} eq = ∈-renameStoreᵗ suc (tagSeal∈ ds eq)

    sealCase :
      ∀ {α} →
      instᵈ _ α ≡ seal-to-tag →
      (α , ★) ∈ ((zero , ★) ∷ ⟰ᵗ _)
    sealCase {zero} eq = here refl
    sealCase {suc α} eq = there (∈-renameStoreᵗ suc (sealTag∈ ds eq))

    seal★Case :
      ∀ {α A} →
      instᵈ _ α ≡ seal-to-tag →
      (α , A) ∈ ((zero , ★) ∷ ⟰ᵗ _) →
      A ≡ ★
    seal★Case {zero} eq (here refl) = refl
    seal★Case {zero} eq (there αA∈Σ) = ⊥-elim (zero∉-⟰ᵗ αA∈Σ)
    seal★Case {suc α} {A} eq αA∈Σ
        with ∈-⟰ᵗ-inv (suc∈-cons-zero-tail αA∈Σ)
    seal★Case {suc α} eq αA∈Σ | B , αB∈Σ , refl
      rewrite sealTag★ ds eq αB∈Σ = refl

    norm :
      ∀ {α A} →
      instᵈ _ α ≡ normal →
      (α , A) ∈ ((zero , ★) ∷ ⟰ᵗ _) →
      (α , A) ∈ ⟰ᵗ _
    norm {zero} () αA∈Σ
    norm {suc α} {A} eq αA∈Σ
        with ∈-⟰ᵗ-inv (suc∈-cons-zero-tail αA∈Σ)
    norm {suc α} eq αA∈Σ | B , αB∈Σ , refl =
      ∈-renameStoreᵗ suc (normal∈ ds eq αB∈Σ)

opp-tyAllowed :
  ∀ {μ ν A} →
  Oppᵈ μ ν →
  tyAllowed μ A ≡ true →
  tyAllowed ν A ≡ true
opp-tyAllowed {μ = μ} {ν = ν} {A = ＇ α} opp ok
    with μ α | ν α | opp α | ok
opp-tyAllowed opp ok | normal | normal | opp-normal | okα = refl
opp-tyAllowed opp ok | tag-to-seal | seal-to-tag | opp-gen-inst | ()
opp-tyAllowed opp ok | seal-to-tag | tag-to-seal | opp-inst-gen | ()
opp-tyAllowed {A = ‵ ι} opp ok = refl
opp-tyAllowed {A = ★} opp ok = refl
opp-tyAllowed {μ = μ} {ν = ν} {A = A ⇒ B} opp ok
    with tyAllowed μ A in okA | tyAllowed μ B in okB
opp-tyAllowed {μ = μ} {ν = ν} {A = A ⇒ B} opp ok
    | true | true
    with opp-tyAllowed {μ = μ} {ν = ν} {A = A} opp okA
       | opp-tyAllowed {μ = μ} {ν = ν} {A = B} opp okB
opp-tyAllowed {A = A ⇒ B} opp ok | true | true | okA′ | okB′
    rewrite okA′ | okB′ = refl
opp-tyAllowed opp () | false | b
opp-tyAllowed opp () | true | false
opp-tyAllowed {A = `∀ A} opp ok =
  opp-tyAllowed {A = A} (opp-extᵈ opp) ok

tagTyAllowed-var-normal :
  ∀ {ν α} →
  ν α ≡ normal →
  tagTyAllowed ν (＇ α) ≡ true
tagTyAllowed-var-normal eq rewrite eq = refl

tagTyAllowed-var-tag :
  ∀ {ν α} →
  ν α ≡ tag-to-seal →
  tagTyAllowed ν (＇ α) ≡ true
tagTyAllowed-var-tag eq rewrite eq = refl

sealTyAllowed-var-normal :
  ∀ {ν α} →
  ν α ≡ normal →
  sealTyAllowed ν α ≡ true
sealTyAllowed-var-normal eq rewrite eq = refl

sealTyAllowed-var-seal :
  ∀ {ν α} →
  ν α ≡ seal-to-tag →
  sealTyAllowed ν α ≡ true
sealTyAllowed-var-seal eq rewrite eq = refl

dualTag-typing :
  ∀ {μ ν Δ Σ Π G} →
  Oppᵈ μ ν →
  DualStore μ Σ ν Π →
  WfTy Δ G →
  Ground G →
  tagTyAllowed μ G ≡ true →
  ν ∣ Δ ∣ Π ⊢ dualTag μ G ∶ ★ =⇒ G
dualTag-typing {μ = μ} {ν = ν} {G = ＇ α} opp ds hG gG ok
    with μ α in μα | ν α in να | opp α | ok
dualTag-typing {ν = ν} {G = ＇ α} opp ds hG gG ok
    | normal | normal | opp-normal | okα
    rewrite μα | να =
  cast-untag {μ = ν} hG gG
    {ok = tagTyAllowed-var-normal {ν = ν} {α = α} να}
dualTag-typing {ν = ν} {G = ＇ α} opp ds hG gG ok
    | tag-to-seal | seal-to-tag | opp-gen-inst | okα
    rewrite μα | να =
  cast-seal {μ = ν} wf★ (tagSeal∈ ds μα)
    {A-ok = refl}
    {α-ok = sealTyAllowed-var-seal {ν = ν} {α = α} να}
dualTag-typing {G = ＇ α} opp ds hG gG ok
    | seal-to-tag | tag-to-seal | opp-inst-gen | ()
dualTag-typing {ν = ν} {G = ‵ ι} opp ds hG gG ok =
  cast-untag {μ = ν} hG gG {ok = refl}
dualTag-typing {ν = ν} {G = ★ ⇒ ★} opp ds hG gG ok =
  cast-untag {μ = ν} hG gG {ok = refl}

dualUntag-typing :
  ∀ {μ ν Δ Σ Π G} →
  Oppᵈ μ ν →
  DualStore μ Σ ν Π →
  WfTy Δ G →
  Ground G →
  tagTyAllowed μ G ≡ true →
  ν ∣ Δ ∣ Π ⊢ dualUntag μ G ∶ G =⇒ ★
dualUntag-typing {μ = μ} {ν = ν} {G = ＇ α} opp ds hG gG ok
    with μ α in μα | ν α in να | opp α | ok
dualUntag-typing {ν = ν} {G = ＇ α} opp ds hG gG ok
    | normal | normal | opp-normal | okα
    rewrite μα | να =
  cast-tag {μ = ν} hG gG
    {ok = tagTyAllowed-var-normal {ν = ν} {α = α} να}
dualUntag-typing {ν = ν} {G = ＇ α} opp ds hG gG ok
    | tag-to-seal | seal-to-tag | opp-gen-inst | okα
    rewrite μα | να =
  cast-unseal {μ = ν} wf★ (tagSeal∈ ds μα)
    {A-ok = refl}
    {α-ok = sealTyAllowed-var-seal {ν = ν} {α = α} να}
dualUntag-typing {G = ＇ α} opp ds hG gG ok
    | seal-to-tag | tag-to-seal | opp-inst-gen | ()
dualUntag-typing {ν = ν} {G = ‵ ι} opp ds hG gG ok =
  cast-tag {μ = ν} hG gG {ok = refl}
dualUntag-typing {ν = ν} {G = ★ ⇒ ★} opp ds hG gG ok =
  cast-tag {μ = ν} hG gG {ok = refl}

dualSeal-typing :
  ∀ {μ ν Δ Σ Π A α} →
  Oppᵈ μ ν →
  DualStore μ Σ ν Π →
  StoreWfAt Δ Σ →
  WfTy Δ A →
  (α , A) ∈ Σ →
  tyAllowed μ A ≡ true →
  sealTyAllowed μ α ≡ true →
  ν ∣ Δ ∣ Π ⊢ dualSeal μ A α ∶ ＇ α =⇒ A
dualSeal-typing {μ = μ} {ν = ν} {A = A} {α = α}
    opp ds wfΣ hA αA∈Σ A-ok α-ok
    with μ α in μα | ν α in να | opp α | α-ok
dualSeal-typing {μ = μ} {ν = ν} {A = A} {α = α}
    opp ds wfΣ hA αA∈Σ A-ok α-ok
    | normal | normal | opp-normal | okα
    rewrite μα | να =
  cast-unseal {μ = ν} hA (normal∈ ds μα αA∈Σ)
    {A-ok = opp-tyAllowed {μ = μ} {ν = ν} {A = A} opp A-ok}
    {α-ok = sealTyAllowed-var-normal {ν = ν} {α = α} να}
dualSeal-typing {A = A} {α = α} opp ds wfΣ hA αA∈Σ A-ok α-ok
    | tag-to-seal | seal-to-tag | opp-gen-inst | ()
dualSeal-typing {ν = ν} {A = A} {α = α}
    opp ds wfΣ hA αA∈Σ A-ok α-ok
    | seal-to-tag | tag-to-seal | opp-inst-gen | okα
    rewrite sealTag★ ds μα αA∈Σ | μα | να =
  cast-tag {μ = ν} (wfVar (bound wfΣ αA∈Σ)) (＇ α)
    {ok = tagTyAllowed-var-tag {ν = ν} {α = α} να}

dualUnseal-typing :
  ∀ {μ ν Δ Σ Π A α} →
  Oppᵈ μ ν →
  DualStore μ Σ ν Π →
  StoreWfAt Δ Σ →
  WfTy Δ A →
  (α , A) ∈ Σ →
  tyAllowed μ A ≡ true →
  sealTyAllowed μ α ≡ true →
  ν ∣ Δ ∣ Π ⊢ dualUnseal μ α A ∶ A =⇒ ＇ α
dualUnseal-typing {μ = μ} {ν = ν} {A = A} {α = α}
    opp ds wfΣ hA αA∈Σ A-ok α-ok
    with μ α in μα | ν α in να | opp α | α-ok
dualUnseal-typing {μ = μ} {ν = ν} {A = A} {α = α}
    opp ds wfΣ hA αA∈Σ A-ok α-ok
    | normal | normal | opp-normal | okα
    rewrite μα | να =
  cast-seal {μ = ν} hA (normal∈ ds μα αA∈Σ)
    {A-ok = opp-tyAllowed {μ = μ} {ν = ν} {A = A} opp A-ok}
    {α-ok = sealTyAllowed-var-normal {ν = ν} {α = α} να}
dualUnseal-typing {A = A} {α = α} opp ds wfΣ hA αA∈Σ A-ok α-ok
    | tag-to-seal | seal-to-tag | opp-gen-inst | ()
dualUnseal-typing {ν = ν} {A = A} {α = α}
    opp ds wfΣ hA αA∈Σ A-ok α-ok
    | seal-to-tag | tag-to-seal | opp-inst-gen | okα
    rewrite sealTag★ ds μα αA∈Σ | μα | να =
  cast-untag {μ = ν} (wfVar (bound wfΣ αA∈Σ)) (＇ α)
    {ok = tagTyAllowed-var-tag {ν = ν} {α = α} να}

coercion-dual-flipᵐ :
  ∀ {μ ν Δ Σ Π c A B} →
  Oppᵈ μ ν →
  DualStore μ Σ ν Π →
  StoreWfAt Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  ν ∣ Δ ∣ Π ⊢ dualWith μ c ∶ B =⇒ A
coercion-dual-flipᵐ {μ = μ} {ν = ν} opp ds wfΣ
    (cast-id {A = A} hA {ok = ok}) =
  cast-id hA {ok = opp-tyAllowed {μ = μ} {ν = ν} {A = A} opp ok}
coercion-dual-flipᵐ opp ds wfΣ
    (cast-seal hA αA∈Σ {A-ok = A-ok} {α-ok = α-ok}) =
  dualSeal-typing opp ds wfΣ hA αA∈Σ A-ok α-ok
coercion-dual-flipᵐ opp ds wfΣ
    (cast-unseal hA αA∈Σ {A-ok = A-ok} {α-ok = α-ok}) =
  dualUnseal-typing opp ds wfΣ hA αA∈Σ A-ok α-ok
coercion-dual-flipᵐ opp ds wfΣ (cast-seq c⊢ d⊢) =
  cast-seq (coercion-dual-flipᵐ opp ds wfΣ d⊢)
           (coercion-dual-flipᵐ opp ds wfΣ c⊢)
coercion-dual-flipᵐ opp ds wfΣ (cast-tag hG gG {ok = ok}) =
  dualTag-typing opp ds hG gG ok
coercion-dual-flipᵐ opp ds wfΣ (cast-untag hG gG {ok = ok}) =
  dualUntag-typing opp ds hG gG ok
coercion-dual-flipᵐ opp ds wfΣ (cast-fun c⊢ d⊢) =
  cast-fun (coercion-dual-flipᵐ opp ds wfΣ c⊢)
           (coercion-dual-flipᵐ opp ds wfΣ d⊢)
coercion-dual-flipᵐ opp ds wfΣ (cast-all c⊢) =
  cast-all
    (coercion-dual-flipᵐ
      (opp-extᵈ opp)
      (dualStore-ext ds)
      (StoreWfAt-⟰ᵗ wfΣ)
      c⊢)
coercion-dual-flipᵐ {μ = μ} {ν = ν} opp ds wfΣ
    (cast-inst {B = B} hB {B-ok = B-ok} c⊢) =
  cast-gen hB
    {A-ok = opp-tyAllowed {μ = μ} {ν = ν} {A = B} opp B-ok}
    (coercion-dual-flipᵐ
      (opp-inst-genᵈ opp)
      (dualStore-inst-gen ds)
      (StoreWfAt-cons z<s wf★ (StoreWfAt-⟰ᵗ wfΣ))
      c⊢)
coercion-dual-flipᵐ {μ = μ} {ν = ν} opp ds wfΣ
    (cast-gen {A = A} hA {A-ok = A-ok} c⊢) =
  cast-inst hA
    {B-ok = opp-tyAllowed {μ = μ} {ν = ν} {A = A} opp A-ok}
    (coercion-dual-flipᵐ
      (opp-gen-instᵈ opp)
      (dualStore-gen-inst ds)
      (StoreWfAt-⟰ᵗ wfΣ)
      c⊢)

coercion-dual-flip :
  ∀ {Δ Σ c A B} →
  StoreWfAt Δ Σ →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ ∣ Σ ⊢ - c ∶ B =⇒ A
coercion-dual-flip wfΣ c⊢ =
  coercion-dual-flipᵐ opp-normalᵈ dualStore-normal wfΣ c⊢

dual-flips-typing :
  ∀ {Δ Σ c A B} →
  StoreWfAt Δ Σ →
  Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  Δ ∣ Σ ⊢ - c ∶ B =⇒ A
dual-flips-typing = coercion-dual-flip

------------------------------------------------------------------------
-- Coercion endpoint well-formedness
------------------------------------------------------------------------

coercion-wfᵐ :
  ∀ {μ Δ Σ c A B} →
  StoreWfAt Δ Σ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B →
  WfTy Δ A × WfTy Δ B
coercion-wfᵐ wfΣ (cast-id hA) = hA , hA
coercion-wfᵐ wfΣ (cast-seal hA α∈Σ) =
  hA , wfVar (bound wfΣ α∈Σ)
coercion-wfᵐ wfΣ (cast-unseal hA α∈Σ) =
  wfVar (bound wfΣ α∈Σ) , hA
coercion-wfᵐ wfΣ (cast-seq c⊢ d⊢)
    with coercion-wfᵐ wfΣ c⊢ | coercion-wfᵐ wfΣ d⊢
coercion-wfᵐ wfΣ (cast-seq c⊢ d⊢)
    | hA , hB | hB′ , hC =
  hA , hC
coercion-wfᵐ wfΣ (cast-tag hG gG) = hG , wf★
coercion-wfᵐ wfΣ (cast-untag hH gH) = wf★ , hH
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
coercion-wf = coercion-wfᵐ

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
  ∀ {Δ Σ α C} →
  WfTy Δ C →
  (α , C) ∈ Σ →
  Δ ∣ Σ ⊢ reveal (＇ α) α C ∶ ＇ α =⇒ C
reveal-var-hit {α = α} hC α∈Σ with α ≟ α
reveal-var-hit {α = α} {C = C} hC α∈Σ | yes refl =
  cast-unseal hC α∈Σ
    {A-ok = tyAllowed-normal C}
    {α-ok = sealTyAllowed-normal α}
reveal-var-hit {α = α} hC α∈Σ | no α≢α =
  ⊥-elim (α≢α refl)

conceal-var-hit :
  ∀ {Δ Σ α C} →
  WfTy Δ C →
  (α , C) ∈ Σ →
  Δ ∣ Σ ⊢ conceal (＇ α) α C ∶ C =⇒ ＇ α
conceal-var-hit {α = α} hC α∈Σ with α ≟ α
conceal-var-hit {α = α} {C = C} hC α∈Σ | yes refl =
  cast-seal hC α∈Σ
    {A-ok = tyAllowed-normal C}
    {α-ok = sealTyAllowed-normal α}
conceal-var-hit {α = α} hC α∈Σ | no α≢α =
  ⊥-elim (α≢α refl)

reveal-var-miss :
  ∀ {Δ Σ α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  Δ ∣ Σ ⊢ reveal (＇ Y) α C ∶ ＇ Y =⇒ ＇ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY with α ≟ Y
reveal-var-miss {α = α} {Y = Y} Y≢α hY | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
reveal-var-miss {α = α} {Y = Y} Y≢α hY | no α≢Y =
  cast-id hY {ok = refl}

conceal-var-miss :
  ∀ {Δ Σ α C Y} →
  Y ≢ α →
  WfTy Δ (＇ Y) →
  Δ ∣ Σ ⊢ conceal (＇ Y) α C ∶ ＇ Y =⇒ ＇ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY with α ≟ Y
conceal-var-miss {α = α} {Y = Y} Y≢α hY | yes α≡Y =
  ⊥-elim (Y≢α (sym α≡Y))
conceal-var-miss {α = α} {Y = Y} Y≢α hY | no α≢Y =
  cast-id hY {ok = refl}

mutual
  reveal-typing-env :
    ∀ {Θ Δ Σ B α C ρ σ} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    RevealEnv Θ α C ρ σ →
    WfTy Δ C →
    (α , C) ∈ Σ →
    Δ ∣ Σ ⊢ reveal (renameᵗ ρ B) α C
      ∶ renameᵗ ρ B =⇒ substᵗ σ B
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      with env X<Θ
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      | rv-hit ρX≡α σX≡C
      rewrite ρX≡α | σX≡C =
    reveal-var-hit hC α∈Σ
  reveal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      | rv-miss ρX≢α σX≡var
      rewrite σX≡var =
    reveal-var-miss ρX≢α (wfVar (hρ X<Θ))
  reveal-typing-env wfBase hρ hσ env hC α∈Σ =
    cast-id wfBase {ok = refl}
  reveal-typing-env wf★ hρ hσ env hC α∈Σ =
    cast-id wf★ {ok = refl}
  reveal-typing-env (wf⇒ hA hB) hρ hσ env hC α∈Σ =
    cast-fun
      (conceal-typing-env hA hρ hσ env hC α∈Σ)
      (reveal-typing-env hB hρ hσ env hC α∈Σ)
  reveal-typing-env {B = `∀ B} {ρ = ρ} {σ = σ}
      (wf∀ hB) hρ hσ env hC α∈Σ =
    cast-all
      (coercion-mode-relax
        (λ { zero → refl ; (suc X) → refl })
        (reveal-typing-env
          hB
          (TyRenameWf-ext hρ)
          (TySubstWf-exts hσ)
          (RevealEnv-ext env)
          (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
          (∈-renameStoreᵗ suc α∈Σ)))

  conceal-typing-env :
    ∀ {Θ Δ Σ B α C ρ σ} →
    WfTy Θ B →
    TyRenameWf Θ Δ ρ →
    TySubstWf Θ Δ σ →
    RevealEnv Θ α C ρ σ →
    WfTy Δ C →
    (α , C) ∈ Σ →
    Δ ∣ Σ ⊢ conceal (renameᵗ ρ B) α C
      ∶ substᵗ σ B =⇒ renameᵗ ρ B
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      with env X<Θ
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      | rv-hit ρX≡α σX≡C
      rewrite ρX≡α | σX≡C =
    conceal-var-hit hC α∈Σ
  conceal-typing-env {B = ＇ X} (wfVar X<Θ) hρ hσ env hC α∈Σ
      | rv-miss ρX≢α σX≡var
      rewrite σX≡var =
    conceal-var-miss ρX≢α (wfVar (hρ X<Θ))
  conceal-typing-env wfBase hρ hσ env hC α∈Σ =
    cast-id wfBase {ok = refl}
  conceal-typing-env wf★ hρ hσ env hC α∈Σ =
    cast-id wf★ {ok = refl}
  conceal-typing-env (wf⇒ hA hB) hρ hσ env hC α∈Σ =
    cast-fun
      (reveal-typing-env hA hρ hσ env hC α∈Σ)
      (conceal-typing-env hB hρ hσ env hC α∈Σ)
  conceal-typing-env {B = `∀ B} {ρ = ρ} {σ = σ}
      (wf∀ hB) hρ hσ env hC α∈Σ =
    cast-all
      (coercion-mode-relax
        (λ { zero → refl ; (suc X) → refl })
        (conceal-typing-env
          hB
          (TyRenameWf-ext hρ)
          (TySubstWf-exts hσ)
          (RevealEnv-ext env)
          (renameᵗ-preserves-WfTy hC TyRenameWf-suc)
          (∈-renameStoreᵗ suc α∈Σ)))

reveal-fresh-typing :
  ∀ {Δ Σ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  suc Δ ∣ (Δ , A) ∷ Σ ⊢ reveal (B [ Δ ]ᴿ) Δ A
    ∶ B [ Δ ]ᴿ =⇒ B [ A ]ᵗ
reveal-fresh-typing {Δ = Δ} hA hB =
  reveal-typing-env
    hB
    (singleRenameᵗ-Wf (n<1+n Δ))
    singleTyEnv-Wf-suc
    singleRevealEnv
    (WfTy-weakenᵗ hA (n≤1+n Δ))
    (here refl)
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
  conceal-typing-env
    hB
    (singleRenameᵗ-Wf (n<1+n Δ))
    singleTyEnv-Wf-suc
    singleRevealEnv
    (WfTy-weakenᵗ hA (n≤1+n Δ))
    (here refl)
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
coercion-src-tgtᵐ (cast-seal hA α∈Σ) = refl , refl
coercion-src-tgtᵐ (cast-unseal hA α∈Σ) = refl , refl
coercion-src-tgtᵐ (cast-seq c⊢ d⊢)
    with coercion-src-tgtᵐ c⊢ | coercion-src-tgtᵐ d⊢
coercion-src-tgtᵐ (cast-seq c⊢ d⊢)
    | src-c , tgt-c | src-d , tgt-d rewrite src-c | tgt-d =
  refl , refl
coercion-src-tgtᵐ (cast-tag hG gG) = refl , refl
coercion-src-tgtᵐ (cast-untag hH gH) = refl , refl
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
coercion-src-tgt = coercion-src-tgtᵐ
