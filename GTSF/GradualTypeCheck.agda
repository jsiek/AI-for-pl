module GradualTypeCheck where

-- File Charter:
--   * Maybe-valued type checker for the GTSF source gradual term language.
--   * Synthesizes a type together with a typing derivation, and provides an
--     expected-type wrapper for examples/tests.
--   * Uses the existing imprecision decision procedure to construct
--     consistency witnesses.

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (refl)
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Ctx using (CtxWf; ctxWf-∷; ⤊ᵗ)
open import GradualTerms
open import Imprecision using (_⊢_~_; idᵢ)
open import Primitives using (Const; constTy; κℕ)
open import proof.ImprecisionProperties using (imp?)
open import proof.TypeProperties
  using
    ( TyRenameWf-suc
    ; renameᵗ-preserves-WfTy
    ; singleTyEnv-Wf
    ; substᵗ-preserves-WfTy
    )

------------------------------------------------------------------------
-- Local result predicates and Maybe witnesses
------------------------------------------------------------------------

HasSomeType : TyCtx → Ctx → GTerm → Set₁
HasSomeType Δ Γ M = Σ[ A ∈ Ty ] Δ ∣ Γ ⊢ M ⦂ A

HasSomeTypeWf : TyCtx → Ctx → GTerm → Set₁
HasSomeTypeWf Δ Γ M =
  Σ[ A ∈ Ty ] (Δ ∣ Γ ⊢ M ⦂ A × WfTy Δ A)

WellTyped : GTerm → Set₁
WellTyped M = HasSomeType 0 [] M

data IsJust {ℓ : Level} {A : Set ℓ} : Maybe A → Set ℓ where
  is-just : ∀ {x} → IsJust (just x)

toWitness : ∀ {ℓ : Level} {A : Set ℓ} {m : Maybe A} → IsJust m → A
toWitness {m = just x} is-just = x

------------------------------------------------------------------------
-- Decidable fragments used by the checker
------------------------------------------------------------------------

wfTy? : (Δ : TyCtx) → (A : Ty) → Maybe (WfTy Δ A)
wfTy? Δ (＇ X) with X <? Δ
... | yes X<Δ = just (wfVar X<Δ)
... | no _ = nothing
wfTy? Δ (‵ ι) = just wfBase
wfTy? Δ ★ = just wf★
wfTy? Δ (A ⇒ B) with wfTy? Δ A | wfTy? Δ B
... | just hA | just hB = just (wf⇒ hA hB)
... | nothing | _ = nothing
... | just hA | nothing = nothing
wfTy? Δ (`∀ A) with wfTy? (suc Δ) A
... | just hA = just (wf∀ hA)
... | nothing = nothing

lookupAny? : (Γ : Ctx) → (x : Var) → Maybe (Σ[ A ∈ Ty ] Γ ∋ x ⦂ A)
lookupAny? [] x = nothing
lookupAny? (A ∷ Γ) zero = just (A , Z)
lookupAny? (A ∷ Γ) (suc x) with lookupAny? Γ x
... | just (B , x∈) = just (B , S x∈)
... | nothing = nothing

value? : (M : GTerm) → Maybe (Value M)
value? (` x) = nothing
value? (ƛ A ⇒ M) = just (ƛ A ⇒ M)
value? (L · M) = nothing
value? (Λ M) = just (Λ M)
value? (M `[ A ]) = nothing
value? ($ κ) = just ($ κ)
value? (L ⊕[ op ] M) = nothing

constTy-wf : ∀ {Δ} → (κ : Const) → WfTy Δ (constTy κ)
constTy-wf (κℕ n) = wfBase

CtxWf-⤊ᵗ :
  ∀ {Δ Γ} →
  CtxWf Δ Γ →
  CtxWf (suc Δ) (⤊ᵗ Γ)
CtxWf-⤊ᵗ {Γ = []} wfΓ ()
CtxWf-⤊ᵗ {Γ = A ∷ Γ} wfΓ Z =
  renameᵗ-preserves-WfTy (wfΓ Z) TyRenameWf-suc
CtxWf-⤊ᵗ {Γ = A ∷ Γ} wfΓ (S h) =
  CtxWf-⤊ᵗ (λ hA → wfΓ (S hA)) h

orElse : ∀ {ℓ : Level} {A : Set ℓ} → Maybe A → Maybe A → Maybe A
orElse (just x) _ = just x
orElse nothing y = y

try-consistent :
  (Δ : TyCtx) (A B C : Ty) →
  Maybe (Δ ⊢ A ~ B)
try-consistent Δ A B C with imp? (idᵢ Δ) C A | imp? (idᵢ Δ) C B
... | yes C⊑A | yes C⊑B = just (C , C⊑A , C⊑B)
... | no _ | _ = nothing
... | yes _ | no _ = nothing

consistent-endpoints :
  (Δ : TyCtx) (A B : Ty) →
  Maybe (Δ ⊢ A ~ B)
consistent-endpoints Δ A B =
  orElse (try-consistent Δ A B A) (try-consistent Δ A B B)

consistent? :
  ∀ (Δ : TyCtx) (A B : Ty) →
  WfTy Δ A →
  WfTy Δ B →
  Maybe (Δ ⊢ A ~ B)
consistent? Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
    (wf⇒ hA₁ hA₂) (wf⇒ hB₁ hB₂)
    with consistent? Δ A₁ B₁ hA₁ hB₁ |
         consistent? Δ A₂ B₂ hA₂ hB₂
... | just (C₁ , C₁⊑A₁ , C₁⊑B₁)
    | just (C₂ , C₂⊑A₂ , C₂⊑B₂) =
  orElse
    (try-consistent Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂) (C₁ ⇒ C₂))
    (consistent-endpoints Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂))
... | nothing | _ = consistent-endpoints Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
... | just _ | nothing = consistent-endpoints Δ (A₁ ⇒ A₂) (B₁ ⇒ B₂)
consistent? Δ (`∀ A) (`∀ B) (wf∀ hA) (wf∀ hB)
    with consistent? (suc Δ) A B hA hB
... | just (C , C⊑A , C⊑B) =
  orElse
    (try-consistent Δ (`∀ A) (`∀ B) (`∀ C))
    (consistent-endpoints Δ (`∀ A) (`∀ B))
... | nothing = consistent-endpoints Δ (`∀ A) (`∀ B)
consistent? Δ A B hA hB = consistent-endpoints Δ A B

------------------------------------------------------------------------
-- Type checking
------------------------------------------------------------------------

type-check-app-from :
  ∀ {Γ L M} →
  (Δ : TyCtx) →
  (A : Ty) →
  Δ ∣ Γ ⊢ L ⦂ A →
  WfTy Δ A →
  (B : Ty) →
  Δ ∣ Γ ⊢ M ⦂ B →
  WfTy Δ B →
  Maybe (HasSomeTypeWf Δ Γ (L · M))
type-check-app-from Δ (＇ X) L⊢ hA B M⊢ hB = nothing
type-check-app-from Δ (‵ ι) L⊢ hA B M⊢ hB = nothing
type-check-app-from Δ ★ L⊢ wf★ B M⊢ hB
    with consistent? Δ B ★ hB wf★
... | just B~★ = just (★ , (⊢·★ L⊢ M⊢ B~★ , wf★))
... | nothing = nothing
type-check-app-from Δ (A₁ ⇒ B₁) L⊢ (wf⇒ hA₁ hB₁) B M⊢ hB
    with consistent? Δ A₁ B hA₁ hB
... | just A₁~B = just (B₁ , (⊢· L⊢ M⊢ A₁~B , hB₁))
... | nothing = nothing
type-check-app-from Δ (`∀ A) L⊢ hA B M⊢ hB = nothing

type-check-wf :
  (Δ : TyCtx) →
  (Γ : Ctx) →
  CtxWf Δ Γ →
  (M : GTerm) →
  Maybe (HasSomeTypeWf Δ Γ M)

type-check-wf Δ Γ wfΓ (` x) with lookupAny? Γ x
... | just (A , x∈) = just (A , (⊢` x∈ , wfΓ x∈))
... | nothing = nothing

type-check-wf Δ Γ wfΓ (ƛ A ⇒ M) with wfTy? Δ A
... | nothing = nothing
... | just hA with type-check-wf Δ (A ∷ Γ) (ctxWf-∷ hA wfΓ) M
...   | just (B , (M⊢ , hB)) = just (A ⇒ B , (⊢ƛ hA M⊢ , wf⇒ hA hB))
...   | nothing = nothing

type-check-wf Δ Γ wfΓ (L · M)
    with type-check-wf Δ Γ wfΓ L | type-check-wf Δ Γ wfΓ M
... | just (A , (L⊢ , hA)) | just (B , (M⊢ , hB)) =
  type-check-app-from Δ A L⊢ hA B M⊢ hB
... | nothing | _ = nothing
... | just _ | nothing = nothing

type-check-wf Δ Γ wfΓ (Λ M) with value? M
type-check-wf Δ Γ wfΓ (Λ M) | nothing = nothing
type-check-wf Δ Γ wfΓ (Λ M) | just vM
    with type-check-wf (suc Δ) (⤊ᵗ Γ) (CtxWf-⤊ᵗ wfΓ) M
type-check-wf Δ Γ wfΓ (Λ M) | just vM | nothing = nothing
type-check-wf Δ Γ wfΓ (Λ M) | just vM | just (A , (M⊢ , hA))
    with occurs zero A in occ≡
type-check-wf Δ Γ wfΓ (Λ M) | just vM | just (A , (M⊢ , hA)) | true =
  just (`∀ A , (⊢Λ {occ = occ≡} vM M⊢ , wf∀ hA))
type-check-wf Δ Γ wfΓ (Λ M) | just vM | just (A , (M⊢ , hA)) | false =
  nothing

type-check-wf Δ Γ wfΓ (M `[ A ]) with type-check-wf Δ Γ wfΓ M
... | nothing = nothing
... | just (＇ X , (M⊢ , hM)) = nothing
... | just (‵ ι , (M⊢ , hM)) = nothing
... | just (★ , (M⊢ , hM)) = nothing
... | just (B ⇒ C , (M⊢ , hM)) = nothing
... | just (`∀ B , (M⊢ , wf∀ hB)) with wfTy? Δ A
...   | just hA =
      just
        ( B [ A ]ᵗ
        , ( ⊢• M⊢ hB hA
          , substᵗ-preserves-WfTy hB (singleTyEnv-Wf hA)
          )
        )
...   | nothing = nothing

type-check-wf Δ Γ wfΓ ($ κ) =
  just (constTy κ , (⊢$ κ , constTy-wf κ))

type-check-wf Δ Γ wfΓ (L ⊕[ op ] M)
    with type-check-wf Δ Γ wfΓ L | type-check-wf Δ Γ wfΓ M
... | just (A , (L⊢ , hA)) | just (B , (M⊢ , hB))
    with consistent? Δ A (‵ `ℕ) hA wfBase |
         consistent? Δ B (‵ `ℕ) hB wfBase
...   | just A~ℕ | just B~ℕ =
      just (‵ `ℕ , (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ , wfBase))
...   | nothing | _ = nothing
...   | just A~ℕ | nothing = nothing
type-check-wf Δ Γ wfΓ (L ⊕[ op ] M) | nothing | _ = nothing
type-check-wf Δ Γ wfΓ (L ⊕[ op ] M) | just _ | nothing = nothing

type-check :
  (Δ : TyCtx) →
  (Γ : Ctx) →
  CtxWf Δ Γ →
  (M : GTerm) →
  Maybe (HasSomeType Δ Γ M)
type-check Δ Γ wfΓ M with type-check-wf Δ Γ wfΓ M
... | just (A , (M⊢ , hA)) = just (A , M⊢)
... | nothing = nothing

type-check-expect :
  (Δ : TyCtx) →
  (Γ : Ctx) →
  CtxWf Δ Γ →
  (M : GTerm) →
  (A : Ty) →
  Maybe (Δ ∣ Γ ⊢ M ⦂ A)
type-check-expect Δ Γ wfΓ M A with type-check-wf Δ Γ wfΓ M
... | nothing = nothing
... | just (B , (M⊢ , hB)) with B ≟Ty A
...   | yes refl = just M⊢
...   | no _ = nothing
