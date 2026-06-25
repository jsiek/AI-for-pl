module TypeCheck where

-- File Charter:
--   * Maybe-based type synthesis and checking for GTSF NuTerms.
--   * Primary exports are coercion checking, term synthesis, expected-type
--     checking, and small Maybe witnesses used by example regression tests.
--   * The checker is intentionally positive-only: failure returns `nothing`
--     instead of carrying negative evidence for every impossible typing shape.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level)
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_<?_; _≟_)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import Ctx using (⤊ᵗ)
open import Coercions
open import Primitives
open import NuTerms
open import proof.TypeProperties using (rename-raise-ext)

------------------------------------------------------------------------
-- Maybe witnesses
------------------------------------------------------------------------

data IsJust {a : Level} {A : Set a} : Maybe A → Set a where
  is-just : ∀ {x} → IsJust (just x)

fromJust : ∀ {a : Level} {A : Set a} → (m : Maybe A) → IsJust m → A
fromJust (just x) is-just = x
fromJust nothing ()

------------------------------------------------------------------------
-- Local result types
------------------------------------------------------------------------

HasSomeType : TyCtx → Store → Ctx → Term → Set₁
HasSomeType Δ Σ Γ M = Σ[ A ∈ Ty ] Δ ∣ Σ ∣ Γ ⊢ M ⦂ A

WellTyped : Term → Set₁
WellTyped M = HasSomeType 0 [] [] M

HasCoercionTypeᵐ : ModeEnv → TyCtx → Store → Coercion → Set
HasCoercionTypeᵐ μ Δ Σ c =
  Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B

HasCoercionType : TyCtx → Store → Coercion → Set
HasCoercionType Δ Σ c =
  Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Δ ∣ Σ ⊢ c ∶ A =⇒ B

------------------------------------------------------------------------
-- Decidable fragments used positively
------------------------------------------------------------------------

true? : (b : Bool) → Maybe (b ≡ true)
true? true = just refl
true? false = nothing

wfTy? : (Δ : TyCtx) → (A : Ty) → Maybe (WfTy Δ A)
wfTy? Δ (＇ X) with X <? Δ
... | yes X<Δ = just (wfVar X<Δ)
... | no _ = nothing
wfTy? Δ (‵ ι) = just wfBase
wfTy? Δ ★ = just wf★
wfTy? Δ (A ⇒ B) with wfTy? Δ A | wfTy? Δ B
... | just wfA | just wfB = just (wf⇒ wfA wfB)
... | _ | _ = nothing
wfTy? Δ (`∀ A) with wfTy? (suc Δ) A
... | just wfA = just (wf∀ wfA)
... | nothing = nothing

ground? : (G : Ty) → Maybe (Ground G)
ground? (＇ α) = just (＇ α)
ground? (‵ ι) = just (‵ ι)
ground? ★ = nothing
ground? (★ ⇒ ★) = just ★⇒★
ground? (A ⇒ B) = nothing
ground? (`∀ A) = nothing

lookup? : (Γ : Ctx) → (x : Var) → Maybe (Σ[ A ∈ Ty ] Γ ∋ x ⦂ A)
lookup? [] x = nothing
lookup? (A ∷ Γ) zero = just (A , Z)
lookup? (A ∷ Γ) (suc x) with lookup? Γ x
... | just (B , h) = just (B , S h)
... | nothing = nothing

storeMember? :
  (α : TyVar) →
  (A : Ty) →
  (Σ : Store) →
  Maybe ((α , A) ∈ Σ)
storeMember? α A [] = nothing
storeMember? α A ((β , B) ∷ Σ) with α ≟ β | A ≟Ty B
... | yes refl | yes refl = just (here refl)
... | _ | _ with storeMember? α A Σ
...   | just h = just (there h)
...   | nothing = nothing

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

inert? : (c : Coercion) → Maybe (Inert c)
inert? (id A) = nothing
inert? (c ︔ d) = nothing
inert? (c ↦ d) = just (c ↦ d)
inert? (`∀ c) = just (`∀ c)
inert? (G !) = just (G !)
inert? (G ？) = nothing
inert? (seal A α) = just (seal A α)
inert? (unseal α A) = nothing
inert? (gen A c) = just (gen A c)
inert? (inst B c) = nothing

value? : (M : Term) → Maybe (Value M)
value? (` x) = nothing
value? (ƛ M) = just (ƛ M)
value? (L · M) = nothing
value? (Λ M) with value? M
... | just vM = just (Λ vM)
... | nothing = nothing
value? (ν A L c) = nothing
value? ($ κ) = just ($ κ)
value? (L ⊕[ op ] M) = nothing
value? (M ⟨ c ⟩) with value? M | inert? c
... | just vM | just ic = just (vM ⟨ ic ⟩)
... | _ | _ = nothing
value? blame = nothing

------------------------------------------------------------------------
-- Inverting `⇑ᵗ`
------------------------------------------------------------------------

lowerVar? :
  (k X : TyVar) →
  Maybe (Σ[ Y ∈ TyVar ] X ≡ raiseVarFrom k Y)
lowerVar? zero zero = nothing
lowerVar? zero (suc X) = just (X , refl)
lowerVar? (suc k) zero = just (zero , refl)
lowerVar? (suc k) (suc X) with lowerVar? k X
... | just (Y , eq) = just (suc Y , cong suc eq)
... | nothing = nothing

unraiseTy? :
  (k : TyVar) →
  (A : Ty) →
  Maybe (Σ[ B ∈ Ty ] A ≡ renameᵗ (raiseVarFrom k) B)
unraiseTy? k (＇ X) with lowerVar? k X
... | just (Y , eq) = just (＇ Y , cong ＇_ eq)
... | nothing = nothing
unraiseTy? k (‵ ι) = just (‵ ι , refl)
unraiseTy? k ★ = just (★ , refl)
unraiseTy? k (A ⇒ B) with unraiseTy? k A | unraiseTy? k B
... | just (A′ , eqA) | just (B′ , eqB) =
  just (A′ ⇒ B′ , cong₂ _⇒_ eqA eqB)
... | _ | _ = nothing
unraiseTy? k (`∀ A) with unraiseTy? (suc k) A
... | just (B , eq) =
  just ((`∀ B) , cong `∀ (trans eq (sym (rename-raise-ext k B))))
... | nothing = nothing

unshiftTy? : (A : Ty) → Maybe (Σ[ B ∈ Ty ] A ≡ ⇑ᵗ B)
unshiftTy? = unraiseTy? zero

------------------------------------------------------------------------
-- Coercion checking
------------------------------------------------------------------------

mutual

  coercion-checkᵐ :
    (μ : ModeEnv) →
    (Δ : TyCtx) →
    (Σ : Store) →
    (c : Coercion) →
    Maybe (HasCoercionTypeᵐ μ Δ Σ c)

  coercion-checkᵐ μ Δ Σ (id A)
      with wfTy? Δ A | true? (idTyAllowed μ A)
  ... | just wfA | just ok = just (A , (A , cast-id wfA ok))
  ... | _ | _ = nothing

  coercion-checkᵐ μ Δ Σ (s ︔ t)
      with coercion-checkᵐ μ Δ Σ s
  ... | nothing = nothing
  ... | just (A , (B , s⊢)) with coercion-checkᵐ μ Δ Σ t
  ...   | nothing = nothing
  ...   | just (B′ , (C , t⊢)) with B ≟Ty B′
  ...     | yes refl = just (A , (C , cast-seq s⊢ t⊢))
  ...     | no _ = nothing

  coercion-checkᵐ μ Δ Σ (s ↦ t)
      with coercion-checkᵐ μ Δ Σ s | coercion-checkᵐ μ Δ Σ t
  ... | just (A′ , (A , s⊢)) | just (B , (B′ , t⊢)) =
    just (A ⇒ B , (A′ ⇒ B′ , cast-fun s⊢ t⊢))
  ... | _ | _ = nothing

  coercion-checkᵐ μ Δ Σ (`∀ c)
      with coercion-checkᵐ (extᵈ μ) (suc Δ) (⟰ᵗ Σ) c
  ... | just (A , (B , c⊢)) =
    just ((`∀ A) , ((`∀ B) , cast-all c⊢))
  ... | nothing = nothing

  coercion-checkᵐ μ Δ Σ (G !)
      with wfTy? Δ G | ground? G | true? (tagTyAllowed μ G)
  ... | just wfG | just g | just ok = just (G , (★ , cast-tag wfG g ok))
  ... | _ | _ | _ = nothing

  coercion-checkᵐ μ Δ Σ (H ？)
      with wfTy? Δ H | ground? H | true? (tagTyAllowed μ H)
  ... | just wfH | just g | just ok = just (★ , (H , cast-untag wfH g ok))
  ... | _ | _ | _ = nothing

  coercion-checkᵐ μ Δ Σ (seal A α)
      with wfTy? Δ A | storeMember? α A Σ | true? (sealModeAllowed (μ α))
  ... | just wfA | just α∈Σ | just ok =
    just (A , (＇ α , cast-seal wfA α∈Σ ok))
  ... | _ | _ | _ = nothing

  coercion-checkᵐ μ Δ Σ (unseal α A)
      with wfTy? Δ A | storeMember? α A Σ | true? (sealModeAllowed (μ α))
  ... | just wfA | just α∈Σ | just ok =
    just (＇ α , (A , cast-unseal wfA α∈Σ ok))
  ... | _ | _ | _ = nothing

  coercion-checkᵐ μ Δ Σ (gen A c)
      with wfTy? Δ A | coercion-checkᵐ (genᵈ μ) (suc Δ) (⟰ᵗ Σ) c
  ... | just wfA | just (A′ , (B , c⊢))
      with A′ ≟Ty ⇑ᵗ A | true? (occurs zero B)
  ...   | yes refl | just occ =
    just (A , ((`∀ B) , cast-gen wfA occ c⊢))
  ...   | _ | _ = nothing
  coercion-checkᵐ μ Δ Σ (gen A c) | _ | _ = nothing

  coercion-checkᵐ μ Δ Σ (inst B c)
      with wfTy? Δ B |
           coercion-checkᵐ (instᵈ μ) (suc Δ) ((zero , ★) ∷ ⟰ᵗ Σ) c
  ... | just wfB | just (A , (B′ , c⊢))
      with B′ ≟Ty ⇑ᵗ B | true? (occurs zero A)
  ...   | yes refl | just occ =
    just ((`∀ A) , (B , cast-inst wfB occ c⊢))
  ...   | _ | _ = nothing
  coercion-checkᵐ μ Δ Σ (inst B c) | _ | _ = nothing

coercion-check : (Δ : TyCtx) → (Σ : Store) → (c : Coercion) →
  Maybe (HasCoercionType Δ Σ c)
coercion-check Δ Σ c with coercion-checkᵐ id-onlyᵈ Δ Σ c
... | just (A , (B , c⊢)) = just (A , (B , (id-onlyᵈ , c⊢)))
... | nothing with coercion-checkᵐ tag-or-idᵈ Δ Σ c
...   | just (A , (B , c⊢)) = just (A , (B , (tag-or-idᵈ , c⊢)))
...   | nothing with coercion-checkᵐ seal-or-idᵈ Δ Σ c
...     | just (A , (B , c⊢)) = just (A , (B , (seal-or-idᵈ , c⊢)))
...     | nothing = nothing

------------------------------------------------------------------------
-- Term synthesis and checking
------------------------------------------------------------------------

mutual

  type-check :
    (Δ : TyCtx) →
    (Σ : Store) →
    (Γ : Ctx) →
    (M : Term) →
    Maybe (HasSomeType Δ Σ Γ M)

  type-check-app-from :
    (Δ : TyCtx) →
    (Σ : Store) →
    (Γ : Ctx) →
    (L M : Term) →
    (T : Ty) →
    Δ ∣ Σ ∣ Γ ⊢ L ⦂ T →
    Maybe (HasSomeType Δ Σ Γ (L · M))

  type-check-nu-from :
    (Δ : TyCtx) →
    (Σ : Store) →
    (Γ : Ctx) →
    (A : Ty) →
    (L : Term) →
    (c : Coercion) →
    WfTy Δ A →
    (T : Ty) →
    Δ ∣ Σ ∣ Γ ⊢ L ⦂ T →
    Maybe (HasSomeType Δ Σ Γ (ν A L c))

  type-check-expect-app-from-arg :
    (Δ : TyCtx) →
    (Σ : Store) →
    (Γ : Ctx) →
    (L M : Term) →
    (C : Ty) →
    Maybe (Δ ∣ Σ ∣ Γ ⊢ L · M ⦂ C)

  type-check-expect-app-from-fun :
    (Δ : TyCtx) →
    (Σ : Store) →
    (Γ : Ctx) →
    (L M : Term) →
    (C T : Ty) →
    Δ ∣ Σ ∣ Γ ⊢ L ⦂ T →
    Maybe (Δ ∣ Σ ∣ Γ ⊢ L · M ⦂ C)

  type-check Δ Σ Γ (` x) with lookup? Γ x
  ... | just (A , x∈Γ) = just (A , ⊢` x∈Γ)
  ... | nothing = nothing

  type-check Δ Σ Γ (ƛ M) = nothing

  type-check Δ Σ Γ (L · M) with type-check Δ Σ Γ L
  ... | nothing = nothing
  ... | just (T , L⊢) = type-check-app-from Δ Σ Γ L M T L⊢

  type-check Δ Σ Γ (Λ M) with value? M
  ... | nothing = nothing
  ... | just vM with type-check (suc Δ) (⟰ᵗ Σ) (⤊ᵗ Γ) M
  ...   | just (A , M⊢) = just ((`∀ A) , ⊢Λ vM M⊢)
  ...   | nothing = nothing

  type-check Δ Σ Γ (ν A L c) with wfTy? Δ A
  ... | nothing = nothing
  ... | just wfA with type-check Δ Σ Γ L
  ...   | nothing = nothing
  ...   | just (T , L⊢) = type-check-nu-from Δ Σ Γ A L c wfA T L⊢

  type-check Δ Σ Γ ($ κ) = just (constTy κ , ⊢$ κ)

  type-check Δ Σ Γ (L ⊕[ op ] M)
      with type-check-expect Δ Σ Γ L (‵ `ℕ) |
           type-check-expect Δ Σ Γ M (‵ `ℕ)
  ... | just L⊢ | just M⊢ = just (‵ `ℕ , ⊢⊕ L⊢ op M⊢)
  ... | _ | _ = nothing

  type-check Δ Σ Γ (M ⟨ c ⟩) with coercion-check Δ Σ c
  ... | nothing = nothing
  ... | just (A , (B , (μ , c⊢))) with type-check-expect Δ Σ Γ M A
  ...   | just M⊢ = just (B , ⊢⟨⟩ c⊢ M⊢)
  ...   | nothing = nothing

  type-check Δ Σ Γ blame = just (★ , ⊢blame wf★)

  type-check-app-from Δ Σ Γ L M (＇ X) L⊢ = nothing
  type-check-app-from Δ Σ Γ L M (‵ ι) L⊢ = nothing
  type-check-app-from Δ Σ Γ L M ★ L⊢ = nothing
  type-check-app-from Δ Σ Γ L M (A ⇒ B) L⊢
      with type-check-expect Δ Σ Γ M A
  ... | just M⊢ = just (B , ⊢· L⊢ M⊢)
  ... | nothing = nothing
  type-check-app-from Δ Σ Γ L M (`∀ A) L⊢ = nothing

  type-check-nu-from Δ Σ Γ A L c wfA (＇ X) L⊢ = nothing
  type-check-nu-from Δ Σ Γ A L c wfA (‵ ι) L⊢ = nothing
  type-check-nu-from Δ Σ Γ A L c wfA ★ L⊢ = nothing
  type-check-nu-from Δ Σ Γ A L c wfA (D ⇒ E) L⊢ = nothing
  type-check-nu-from Δ Σ Γ A L c wfA (`∀ C) L⊢
      with coercion-check (suc Δ) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ) c
  ... | nothing = nothing
  ... | just (C′ , (T , (μ , c⊢))) with C′ ≟Ty C | unshiftTy? T
  ...   | yes refl | just (B , refl) = just (B , ⊢ν wfA L⊢ c⊢)
  ...   | _ | _ = nothing

  type-check-expect :
    (Δ : TyCtx) →
    (Σ : Store) →
    (Γ : Ctx) →
    (M : Term) →
    (A : Ty) →
    Maybe (Δ ∣ Σ ∣ Γ ⊢ M ⦂ A)

  type-check-expect Δ Σ Γ (ƛ M) (A ⇒ B) with wfTy? Δ A
  ... | nothing = nothing
  ... | just wfA with type-check-expect Δ Σ (A ∷ Γ) M B
  ...   | just M⊢ = just (⊢ƛ wfA M⊢)
  ...   | nothing = nothing

  type-check-expect Δ Σ Γ (ƛ M) A = nothing

  type-check-expect Δ Σ Γ (Λ M) (`∀ A) with value? M
  ... | nothing = nothing
  ... | just vM with type-check-expect (suc Δ) (⟰ᵗ Σ) (⤊ᵗ Γ) M A
  ...   | just M⊢ = just (⊢Λ vM M⊢)
  ...   | nothing = nothing

  type-check-expect Δ Σ Γ (Λ M) A = nothing

  type-check-expect Δ Σ Γ (L · M) C with type-check Δ Σ Γ L
  ... | just (T , L⊢) =
    type-check-expect-app-from-fun Δ Σ Γ L M C T L⊢
  ... | nothing = type-check-expect-app-from-arg Δ Σ Γ L M C

  type-check-expect Δ Σ Γ (ν A L c) B with wfTy? Δ A
  ... | nothing = nothing
  ... | just wfA with coercion-check (suc Δ) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ) c
  ...   | nothing = nothing
  ...   | just (C , (T , (μ , c⊢))) with T ≟Ty ⇑ᵗ B
  ...     | no _ = nothing
  ...     | yes refl with type-check-expect Δ Σ Γ L (`∀ C)
  ...       | just L⊢ = just (⊢ν wfA L⊢ c⊢)
  ...       | nothing = nothing

  type-check-expect Δ Σ Γ (M ⟨ c ⟩) B with coercion-check Δ Σ c
  ... | nothing = nothing
  ... | just (A , (B′ , (μ , c⊢))) with B′ ≟Ty B
  ...   | no _ = nothing
  ...   | yes refl with type-check-expect Δ Σ Γ M A
  ...     | just M⊢ = just (⊢⟨⟩ c⊢ M⊢)
  ...     | nothing = nothing

  type-check-expect Δ Σ Γ blame A with wfTy? Δ A
  ... | just wfA = just (⊢blame wfA)
  ... | nothing = nothing

  type-check-expect Δ Σ Γ M A with type-check Δ Σ Γ M
  ... | nothing = nothing
  ... | just (B , M⊢) with B ≟Ty A
  ...   | yes refl = just M⊢
  ...   | no _ = nothing

  type-check-expect-app-from-arg Δ Σ Γ L M C with type-check Δ Σ Γ M
  ... | nothing = nothing
  ... | just (A , M⊢) with type-check-expect Δ Σ Γ L (A ⇒ C)
  ...   | just L⊢ = just (⊢· L⊢ M⊢)
  ...   | nothing = nothing

  type-check-expect-app-from-fun Δ Σ Γ L M C (＇ X) L⊢ =
    type-check-expect-app-from-arg Δ Σ Γ L M C
  type-check-expect-app-from-fun Δ Σ Γ L M C (‵ ι) L⊢ =
    type-check-expect-app-from-arg Δ Σ Γ L M C
  type-check-expect-app-from-fun Δ Σ Γ L M C ★ L⊢ =
    type-check-expect-app-from-arg Δ Σ Γ L M C
  type-check-expect-app-from-fun Δ Σ Γ L M C (A ⇒ B) L⊢
      with B ≟Ty C | type-check-expect Δ Σ Γ M A
  ... | yes refl | just M⊢ = just (⊢· L⊢ M⊢)
  ... | _ | _ = type-check-expect-app-from-arg Δ Σ Γ L M C
  type-check-expect-app-from-fun Δ Σ Γ L M C (`∀ A) L⊢ =
    type-check-expect-app-from-arg Δ Σ Γ L M C
