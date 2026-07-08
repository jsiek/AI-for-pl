module TypeCheck where

-- File Charter:
--   * Executable, proof-producing type checking for PolyNuBar raw extrinsic
--     terms.
--   * Provides structural equality/well-formedness deciders and a recursive
--     inference/checking algorithm whose successful results include typing
--     derivations.
--   * The checker follows the full-barrier Agda typing rules, including the
--     targeted deep-pop discipline for `ν`, `bind`, and `unbind`.

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Terms public

------------------------------------------------------------------------
-- Boolean helpers
------------------------------------------------------------------------

infixr 4 _&&_
_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

decToBool : ∀ {A : Set} → Dec A → Bool
decToBool (yes _) = true
decToBool (no _) = false

------------------------------------------------------------------------
-- Decidable type structure
------------------------------------------------------------------------

baseEqDec : (ι κ : Base) → Dec (ι ≡ κ)
baseEqDec 𝕀 𝕀 = yes refl
baseEqDec 𝕀 𝔹 = no (λ ())
baseEqDec 𝔹 𝕀 = no (λ ())
baseEqDec 𝔹 𝔹 = yes refl

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
(` X) ≟Ty (` Y) with X ≟ Y
(` X) ≟Ty (` Y) | yes refl = yes refl
(` X) ≟Ty (` Y) | no X≢Y = no (λ { refl → X≢Y refl })
(` X) ≟Ty (`ι ι) = no (λ ())
(` X) ≟Ty ★ = no (λ ())
(` X) ≟Ty (B ⇒ C) = no (λ ())
(` X) ≟Ty (B `× C) = no (λ ())
(` X) ≟Ty (`∀ B) = no (λ ())
(`ι ι) ≟Ty (` Y) = no (λ ())
(`ι ι) ≟Ty (`ι κ) with baseEqDec ι κ
(`ι ι) ≟Ty (`ι κ) | yes refl = yes refl
(`ι ι) ≟Ty (`ι κ) | no ι≢κ = no (λ { refl → ι≢κ refl })
(`ι ι) ≟Ty ★ = no (λ ())
(`ι ι) ≟Ty (B ⇒ C) = no (λ ())
(`ι ι) ≟Ty (B `× C) = no (λ ())
(`ι ι) ≟Ty (`∀ B) = no (λ ())
★ ≟Ty (` Y) = no (λ ())
★ ≟Ty (`ι ι) = no (λ ())
★ ≟Ty ★ = yes refl
★ ≟Ty (B ⇒ C) = no (λ ())
★ ≟Ty (B `× C) = no (λ ())
★ ≟Ty (`∀ B) = no (λ ())
(A ⇒ B) ≟Ty (` Y) = no (λ ())
(A ⇒ B) ≟Ty (`ι ι) = no (λ ())
(A ⇒ B) ≟Ty ★ = no (λ ())
(A ⇒ B) ≟Ty (C ⇒ D) with A ≟Ty C | B ≟Ty D
(A ⇒ B) ≟Ty (C ⇒ D) | yes refl | yes refl = yes refl
(A ⇒ B) ≟Ty (C ⇒ D) | no A≢C | _ = no (λ { refl → A≢C refl })
(A ⇒ B) ≟Ty (C ⇒ D) | _ | no B≢D = no (λ { refl → B≢D refl })
(A ⇒ B) ≟Ty (C `× D) = no (λ ())
(A ⇒ B) ≟Ty (`∀ C) = no (λ ())
(A `× B) ≟Ty (` Y) = no (λ ())
(A `× B) ≟Ty (`ι ι) = no (λ ())
(A `× B) ≟Ty ★ = no (λ ())
(A `× B) ≟Ty (C ⇒ D) = no (λ ())
(A `× B) ≟Ty (C `× D) with A ≟Ty C | B ≟Ty D
(A `× B) ≟Ty (C `× D) | yes refl | yes refl = yes refl
(A `× B) ≟Ty (C `× D) | no A≢C | _ = no (λ { refl → A≢C refl })
(A `× B) ≟Ty (C `× D) | _ | no B≢D = no (λ { refl → B≢D refl })
(A `× B) ≟Ty (`∀ C) = no (λ ())
(`∀ A) ≟Ty (` Y) = no (λ ())
(`∀ A) ≟Ty (`ι ι) = no (λ ())
(`∀ A) ≟Ty ★ = no (λ ())
(`∀ A) ≟Ty (B ⇒ C) = no (λ ())
(`∀ A) ≟Ty (B `× C) = no (λ ())
(`∀ A) ≟Ty (`∀ B) with A ≟Ty B
(`∀ A) ≟Ty (`∀ B) | yes refl = yes refl
(`∀ A) ≟Ty (`∀ B) | no A≢B = no (λ { refl → A≢B refl })

tyEq : Ty → Ty → Bool
tyEq A B = decToBool (A ≟Ty B)

maybeEq : Maybe Ty → Ty → Bool
maybeEq (just A) B = tyEq A B
maybeEq nothing B = false

lookupTyDec : (Γ : Ctx) → (X : Var) → Dec (Γ ∋ᵗ X)
lookupTyDec ∅ X = no (λ ())
lookupTyDec (Γ ▷ᵗ) zero = yes TZ
lookupTyDec (Γ ▷ᵗ) (suc X) with lookupTyDec Γ X
lookupTyDec (Γ ▷ᵗ) (suc X) | yes X∈ = yes (TSᵗ X∈)
lookupTyDec (Γ ▷ᵗ) (suc X) | no X∉ =
  no (λ { (TSᵗ X∈) → X∉ X∈ })
lookupTyDec (Γ ▷ᵇ Y) zero = yes TZᵇ
lookupTyDec (Γ ▷ᵇ Y) (suc X) with lookupTyDec Γ X
lookupTyDec (Γ ▷ᵇ Y) (suc X) | yes X∈ = yes (TSᵇ X∈)
lookupTyDec (Γ ▷ᵇ Y) (suc X) | no X∉ =
  no (λ { (TSᵇ X∈) → X∉ X∈ })
lookupTyDec (Γ ▷ˢ A) X with lookupTyDec Γ X
lookupTyDec (Γ ▷ˢ A) X | yes X∈ = yes (TSˢ X∈)
lookupTyDec (Γ ▷ˢ A) X | no X∉ =
  no (λ { (TSˢ X∈) → X∉ X∈ })
lookupTyDec (Γ ▷ᵛ A) X with lookupTyDec Γ X
lookupTyDec (Γ ▷ᵛ A) X | yes X∈ = yes (TSᵛ X∈)
lookupTyDec (Γ ▷ᵛ A) X | no X∉ =
  no (λ { (TSᵛ X∈) → X∉ X∈ })

lookupTy? : (Γ : Ctx) → (X : Var) → Maybe (Γ ∋ᵗ X)
lookupTy? Γ X with lookupTyDec Γ X
lookupTy? Γ X | yes X∈ = just X∈
lookupTy? Γ X | no _ = nothing

wfTyDec : (Γ : Ctx) → (A : Ty) → Dec (WfTy Γ A)
wfTyDec Γ (` X) with lookupTyDec Γ X
wfTyDec Γ (` X) | yes X∈ = yes (wf-var X∈)
wfTyDec Γ (` X) | no X∉ = no (λ { (wf-var X∈) → X∉ X∈ })
wfTyDec Γ (`ι ι) = yes wf-base
wfTyDec Γ ★ = yes wf-★
wfTyDec Γ (A ⇒ B) with wfTyDec Γ A | wfTyDec Γ B
wfTyDec Γ (A ⇒ B) | yes wfA | yes wfB = yes (wf-fun wfA wfB)
wfTyDec Γ (A ⇒ B) | no ¬wfA | _ =
  no (λ { (wf-fun wfA wfB) → ¬wfA wfA })
wfTyDec Γ (A ⇒ B) | _ | no ¬wfB =
  no (λ { (wf-fun wfA wfB) → ¬wfB wfB })
wfTyDec Γ (A `× B) with wfTyDec Γ A | wfTyDec Γ B
wfTyDec Γ (A `× B) | yes wfA | yes wfB = yes (wf-prod wfA wfB)
wfTyDec Γ (A `× B) | no ¬wfA | _ =
  no (λ { (wf-prod wfA wfB) → ¬wfA wfA })
wfTyDec Γ (A `× B) | _ | no ¬wfB =
  no (λ { (wf-prod wfA wfB) → ¬wfB wfB })
wfTyDec Γ (`∀ A) with wfTyDec (Γ ▷ᵗ) A
wfTyDec Γ (`∀ A) | yes wfA = yes (wf-∀ wfA)
wfTyDec Γ (`∀ A) | no ¬wfA = no (λ { (wf-∀ wfA) → ¬wfA wfA })

wfTy? : Ctx → Ty → Bool
wfTy? Γ A = decToBool (wfTyDec Γ A)

openTy? : (C A′ : Ty) → Maybe (Σ[ A ∈ Ty ] A′ ≡ A [ C ]ᵗ)
openTy? C A′ with A′ ≟Ty C
openTy? C A′ | yes refl = just (` zero , refl)
openTy? C (` X) | no _ = just (` suc X , refl)
openTy? C (`ι ι) | no _ = just (`ι ι , refl)
openTy? C ★ | no _ = just (★ , refl)
openTy? C (A′ ⇒ B′) | no _ with openTy? C A′ | openTy? C B′
openTy? C (A′ ⇒ B′) | no _ | just (A , eqA) | just (B , eqB) =
  just (A ⇒ B , cong₂ _⇒_ eqA eqB)
openTy? C (A′ ⇒ B′) | no _ | _ | _ = nothing
openTy? C (A′ `× B′) | no _ with openTy? C A′ | openTy? C B′
openTy? C (A′ `× B′) | no _ | just (A , eqA) | just (B , eqB) =
  just (A `× B , cong₂ _`×_ eqA eqB)
openTy? C (A′ `× B′) | no _ | _ | _ = nothing
openTy? C (`∀ A′) | no _ = nothing

groundWitness? : (G : Ty) → Maybe (Ground G)
groundWitness? (` X) = just g-var
groundWitness? (`ι ι) = just g-base
groundWitness? ★ = nothing
groundWitness? (A ⇒ B) with A ≟Ty ★ | B ≟Ty ★
groundWitness? (A ⇒ B) | yes refl | yes refl = just g-fun
groundWitness? (A ⇒ B) | _ | _ = nothing
groundWitness? (A `× B) with A ≟Ty ★ | B ≟Ty ★
groundWitness? (A `× B) | yes refl | yes refl = just g-prod
groundWitness? (A `× B) | _ | _ = nothing
groundWitness? (`∀ A) = nothing

ground? : Ty → Bool
ground? G with groundWitness? G
ground? G | just _ = true
ground? G | nothing = false

consistentWitnessFuel : ℕ → (A B : Ty) → Maybe (A ∼ B)
consistentWitnessFuel zero A B = nothing
consistentWitnessFuel (suc n) (` X) (` Y) with X ≟ Y
consistentWitnessFuel (suc n) (` X) (` Y) | yes refl = just ∼-var
consistentWitnessFuel (suc n) (` X) (` Y) | no _ = nothing
consistentWitnessFuel (suc n) (`ι ι) (`ι κ) with baseEqDec ι κ
consistentWitnessFuel (suc n) (`ι ι) (`ι κ) | yes refl = just ∼-base
consistentWitnessFuel (suc n) (`ι ι) (`ι κ) | no _ = nothing
consistentWitnessFuel (suc n) ★ B = just ∼-★ˡ
consistentWitnessFuel (suc n) A ★ = just ∼-★ʳ
consistentWitnessFuel (suc n) (A ⇒ B) (C ⇒ D)
  with consistentWitnessFuel n A C | consistentWitnessFuel n B D
consistentWitnessFuel (suc n) (A ⇒ B) (C ⇒ D) | just A∼C | just B∼D =
  just (∼-fun A∼C B∼D)
consistentWitnessFuel (suc n) (A ⇒ B) (C ⇒ D) | _ | _ = nothing
consistentWitnessFuel (suc n) (A `× B) (C `× D)
  with consistentWitnessFuel n A C | consistentWitnessFuel n B D
consistentWitnessFuel (suc n) (A `× B) (C `× D) | just A∼C | just B∼D =
  just (∼-prod A∼C B∼D)
consistentWitnessFuel (suc n) (A `× B) (C `× D) | _ | _ = nothing
consistentWitnessFuel (suc n) (`∀ A) B
  with consistentWitnessFuel n (A [ ★ ]ᵗ) B
consistentWitnessFuel (suc n) (`∀ A) B | just A∼B = just (∼-∀ˡ A∼B)
consistentWitnessFuel (suc n) (`∀ A) B | nothing = nothing
consistentWitnessFuel (suc n) A (`∀ B)
  with consistentWitnessFuel n A (B [ ★ ]ᵗ)
consistentWitnessFuel (suc n) A (`∀ B) | just A∼B = just (∼-∀ʳ A∼B)
consistentWitnessFuel (suc n) A (`∀ B) | nothing = nothing
consistentWitnessFuel (suc n) _ _ = nothing

consistentWitness? : (A B : Ty) → Maybe (A ∼ B)
consistentWitness? = consistentWitnessFuel 64

consistent? : Ty → Ty → Bool
consistent? A B with consistentWitness? A B
consistent? A B | just _ = true
consistent? A B | nothing = false

------------------------------------------------------------------------
-- Context and store lookup
------------------------------------------------------------------------

LookupCtxResult : Ctx → Var → Set
LookupCtxResult Γ x = Σ[ A ∈ Ty ] Γ ∋ x ⦂ A

lookupCtx? : (Γ : Ctx) → (x : Var) → Maybe (LookupCtxResult Γ x)
lookupCtx? ∅ x = nothing
lookupCtx? (Γ ▷ᵗ) x with lookupCtx? Γ x
lookupCtx? (Γ ▷ᵗ) x | just (A , x∈) = just (⇑ᵗ A , Sᵗ x∈)
lookupCtx? (Γ ▷ᵗ) x | nothing = nothing
lookupCtx? (Γ ▷ᵇ X) x with lookupCtx? Γ x
lookupCtx? (Γ ▷ᵇ X) x | just (A , x∈) = just (⇑ᵗ A , Sᵇ x∈)
lookupCtx? (Γ ▷ᵇ X) x | nothing = nothing
lookupCtx? (Γ ▷ˢ A) x with lookupCtx? Γ x
lookupCtx? (Γ ▷ˢ A) x | just (B , x∈) = just (B , Sˢ x∈)
lookupCtx? (Γ ▷ˢ A) x | nothing = nothing
lookupCtx? (Γ ▷ᵛ A) zero = just (A , Z)
lookupCtx? (Γ ▷ᵛ A) (suc x) with lookupCtx? Γ x
lookupCtx? (Γ ▷ᵛ A) (suc x) | just (B , x∈) = just (B , S x∈)
lookupCtx? (Γ ▷ᵛ A) (suc x) | nothing = nothing

LookupStoreResult : Ctx → Var → Set
LookupStoreResult Γ X = Σ[ A ∈ Ty ] Γ ∋ˢ X := A

lookupStore? : (Γ : Ctx) → (X : Var) → Maybe (LookupStoreResult Γ X)
lookupStore? ∅ X = nothing
lookupStore? (Γ ▷ᵗ) X with lookupStore? Γ X
lookupStore? (Γ ▷ᵗ) X | just (A , X∈) = just (⇑ᵗ A , thereᵗ X∈)
lookupStore? (Γ ▷ᵗ) X | nothing = nothing
lookupStore? (Γ ▷ᵇ Y) X with lookupStore? Γ X
lookupStore? (Γ ▷ᵇ Y) X | just (A , X∈) = just (⇑ᵗ A , thereᵇ X∈)
lookupStore? (Γ ▷ᵇ Y) X | nothing = nothing
lookupStore? (Γ ▷ˢ A) zero = just (A , here)
lookupStore? (Γ ▷ˢ A) (suc X) with lookupStore? Γ X
lookupStore? (Γ ▷ˢ A) (suc X) | just (B , X∈) =
  just (B , thereˢ X∈)
lookupStore? (Γ ▷ˢ A) (suc X) | nothing = nothing
lookupStore? (Γ ▷ᵛ A) X with lookupStore? Γ X
lookupStore? (Γ ▷ᵛ A) X | just (B , X∈) = just (B , thereᵛ X∈)
lookupStore? (Γ ▷ᵛ A) X | nothing = nothing

LookupStore0Result : Ctx → Var → Set
LookupStore0Result Γ X = Σ[ A ∈ Ty ] Γ ∋ˢ⁰ X := A

lookupStore0? : (Γ : Ctx) → (X : Var) → Maybe (LookupStore0Result Γ X)
lookupStore0? ∅ X = nothing
lookupStore0? (Γ ▷ᵗ) X = nothing
lookupStore0? (Γ ▷ᵇ Y) X = nothing
lookupStore0? (Γ ▷ˢ A) zero = just (A , here⁰)
lookupStore0? (Γ ▷ˢ A) (suc X) with lookupStore0? Γ X
lookupStore0? (Γ ▷ˢ A) (suc X) | just (B , X∈) =
  just (B , thereˢ⁰ X∈)
lookupStore0? (Γ ▷ˢ A) (suc X) | nothing = nothing
lookupStore0? (Γ ▷ᵛ A) X with lookupStore0? Γ X
lookupStore0? (Γ ▷ᵛ A) X | just (B , X∈) = just (B , thereᵛ⁰ X∈)
lookupStore0? (Γ ▷ᵛ A) X | nothing = nothing

CloseResult : Ctx → Var → Set
CloseResult Γ X =
  Σ[ C ∈ Ty ] Σ[ k ∈ ℕ ] Σ[ Γ′ ∈ Ctx ] PopCtx X C k Γ Γ′

closeFor? : (Γ : Ctx) → (X : Var) → Maybe (CloseResult Γ X)
closeFor? ∅ X = nothing
closeFor? (Γ ▷ᵗ) X with closeFor? Γ X
closeFor? (Γ ▷ᵗ) X | just (C , k , Γ′ , pop) =
  just (C , suc k , (Γ′ ▷ᵗ) , popᵗ pop)
closeFor? (Γ ▷ᵗ) X | nothing = nothing
closeFor? (Γ ▷ᵇ Y) X with Y ≟ X
closeFor? (Γ ▷ᵇ Y) X | yes refl with lookupStore? Γ X
closeFor? (Γ ▷ᵇ X) X | yes refl | just (C , X∈) =
  just (C , zero , Γ , pop-here X∈)
closeFor? (Γ ▷ᵇ X) X | yes refl | nothing = nothing
closeFor? (Γ ▷ᵇ Y) X | no _ with closeFor? Γ X
closeFor? (Γ ▷ᵇ Y) X | no _ | just (C , k , Γ′ , pop) =
  just (C , suc k , (Γ′ ▷ᵇ Y) , popᵇ pop)
closeFor? (Γ ▷ᵇ Y) X | no _ | nothing = nothing
closeFor? (Γ ▷ˢ A) zero = nothing
closeFor? (Γ ▷ˢ A) (suc X) with closeFor? Γ X
closeFor? (Γ ▷ˢ A) (suc X) | just (C , k , Γ′ , pop) =
  just (C , k , (Γ′ ▷ˢ closeTyAt k C A) , popˢ pop refl)
closeFor? (Γ ▷ˢ A) (suc X) | nothing = nothing
closeFor? (Γ ▷ᵛ A) X with closeFor? Γ X
closeFor? (Γ ▷ᵛ A) X | just (C , k , Γ′ , pop) =
  just (C , k , (Γ′ ▷ᵛ closeTyAt k C A) , popᵛ pop refl)
closeFor? (Γ ▷ᵛ A) X | nothing = nothing

------------------------------------------------------------------------
-- Recursive type inference and checking
------------------------------------------------------------------------

InferResult : Ctx → Term → Set
InferResult Γ M = Σ[ A ∈ Ty ] Γ ⊢ M ⦂ A

mutual
  infer : (Γ : Ctx) → (M : Term) → Maybe (InferResult Γ M)
  infer Γ (` x) with lookupCtx? Γ x
  infer Γ (` x) | just (A , x∈) = just (A , ⊢` x∈)
  infer Γ (` x) | nothing = nothing
  infer Γ ($ c) = just (typeOfConst c , ⊢const)
  infer Γ (ƛ[ A ] M) with wfTyDec Γ A
  infer Γ (ƛ[ A ] M) | no _ = nothing
  infer Γ (ƛ[ A ] M) | yes wfA with infer (Γ ▷ᵛ A) M
  infer Γ (ƛ[ A ] M) | yes wfA | just (B , M⊢) =
    just (A ⇒ B , ⊢ƛ wfA M⊢)
  infer Γ (ƛ[ A ] M) | yes wfA | nothing = nothing
  infer Γ (L · M) with infer Γ L
  infer Γ (L · M) | just (A ⇒ B , L⊢) with check Γ M A
  infer Γ (L · M) | just (A ⇒ B , L⊢) | just M⊢ =
    just (B , ⊢· L⊢ M⊢)
  infer Γ (L · M) | just (A ⇒ B , L⊢) | nothing = nothing
  infer Γ (L · M) | just (_ , _) = nothing
  infer Γ (L · M) | nothing = nothing
  infer Γ (letin L M) with infer Γ L
  infer Γ (letin L M) | just (A , L⊢) with infer (Γ ▷ᵛ A) M
  infer Γ (letin L M) | just (A , L⊢) | just (B , M⊢) =
    just (B , ⊢let L⊢ M⊢)
  infer Γ (letin L M) | just (A , L⊢) | nothing = nothing
  infer Γ (letin L M) | nothing = nothing
  infer Γ (Λ[ p ] M :: B) with wfTyDec (Γ ▷ᵗ) B
  infer Γ (Λ[ p ] M :: B) | no _ = nothing
  infer Γ (Λ[ p ] M :: B) | yes wfB with check (Γ ▷ᵗ) M B
  infer Γ (Λ[ p ] M :: B) | yes wfB | just M⊢ =
    just (`∀ B , ⊢Λ wfB M⊢)
  infer Γ (Λ[ p ] M :: B) | yes wfB | nothing = nothing
  infer Γ (M • A) with infer Γ M | wfTyDec Γ A
  infer Γ (M • A) | just (`∀ B , M⊢) | yes wfA =
    just (B [ A ]ᵗ , ⊢inst M⊢ wfA)
  infer Γ (M • A) | _ | _ = nothing
  infer Γ (ν[ A ] p ∙ M) with wfTyDec Γ A
  infer Γ (ν[ A ] p ∙ M) | no _ = nothing
  infer Γ (ν[ A ] p ∙ M) | yes wfA with infer (Γ ▷ˢ A) M
  infer Γ (ν[ A ] p ∙ M) | yes wfA | just (B , M⊢)
      with wfTyDec Γ B
  infer Γ (ν[ A ] p ∙ M) | yes wfA | just (B , M⊢) | yes wfB =
    just (B , ⊢ν wfA wfB M⊢)
  infer Γ (ν[ A ] p ∙ M) | yes wfA | just (B , M⊢) | no _ = nothing
  infer Γ (ν[ A ] p ∙ M) | yes wfA | nothing = nothing
  infer Γ (M ⦂ A ⇒[ p ] B)
      with wfTyDec Γ A | wfTyDec Γ B | infer Γ M
         | consistentWitness? A B
  infer Γ (M ⦂ A ⇒[ p ] B)
      | yes wfA | yes wfB | just (A′ , M⊢) | just A∼B
      with A′ ≟Ty A
  infer Γ (M ⦂ A ⇒[ p ] B)
      | yes wfA | yes wfB | just (A′ , M⊢) | just A∼B | yes refl =
    just (B , ⊢cast wfA wfB M⊢ refl A∼B)
  infer Γ (M ⦂ A ⇒[ p ] B)
      | yes wfA | yes wfB | just (A′ , M⊢) | just A∼B | no _ = nothing
  infer Γ (M ⦂ A ⇒[ p ] B) | _ | _ | _ | _ = nothing
  infer (Γ ▷ᵛ D′) (M ⦂ A ⇒⟨ bind X ⟩ B) with lookupStore? Γ X
  infer (Γ ▷ᵛ D′) (M ⦂ A ⇒⟨ bind X ⟩ B) | nothing = nothing
  infer (Γ ▷ᵛ D′) (M ⦂ A ⇒⟨ bind X ⟩ B) | just (C , X∈)
      with openTy? C D′
  infer (Γ ▷ᵛ D′) (M ⦂ A ⇒⟨ bind X ⟩ B) | just (C , X∈)
      | nothing = nothing
  infer (Γ ▷ᵛ D′) (M ⦂ A ⇒⟨ bind X ⟩ B) | just (C , X∈)
      | just (D , eqD)
      with wfTyDec ((Γ ▷ᵇ X) ▷ᵛ D) A | wfTyDec (Γ ▷ᵛ D′) B
         | check ((Γ ▷ᵇ X) ▷ᵛ D) M A | B ≟Ty (A [ C ]ᵗ)
  infer (Γ ▷ᵛ D′) (M ⦂ A ⇒⟨ bind X ⟩ B) | just (C , X∈)
      | just (D , eqD) | yes wfA | yes wfB | just M⊢ | yes refl =
    just (B , ⊢barᵛ wfA wfB X∈ M⊢ eqD refl)
  infer (Γ ▷ᵛ D′) (M ⦂ A ⇒⟨ bind X ⟩ B) | just (C , X∈)
      | just (D , eqD) | _ | _ | _ | _ = nothing
  infer Γ (M ⦂ A ⇒⟨ bind X ⟩ B) with lookupStore? Γ X
  infer Γ (M ⦂ A ⇒⟨ bind X ⟩ B) | nothing = nothing
  infer Γ (M ⦂ A ⇒⟨ bind X ⟩ B) | just (C , X∈)
      with wfTyDec (Γ ▷ᵇ X) A | wfTyDec Γ B
         | check (Γ ▷ᵇ X) M A | B ≟Ty (A [ C ]ᵗ)
  infer Γ (M ⦂ A ⇒⟨ bind X ⟩ B) | just (C , X∈)
      | yes wfA | yes wfB | just M⊢ | yes refl =
    just (B , ⊢bar wfA wfB X∈ M⊢ refl)
  infer Γ (M ⦂ A ⇒⟨ bind X ⟩ B) | just (C , X∈)
      | _ | _ | _ | _ = nothing
  infer Γ (M ⦂ A ⇒⟨ unbind X ⟩ B) with closeFor? Γ X
  infer Γ (M ⦂ A ⇒⟨ unbind X ⟩ B) | nothing = nothing
  infer Γ (M ⦂ A ⇒⟨ unbind X ⟩ B) | just (C , k , Γ′ , pop)
      with wfTyDec Γ′ A | wfTyDec Γ B | check Γ′ M A
         | A ≟Ty closeTyAt k C B
  infer Γ (M ⦂ A ⇒⟨ unbind X ⟩ B) | just (C , k , Γ′ , pop)
      | yes wfA | yes wfB | just M⊢ | yes refl =
    just (B , ⊢bar̄ᴾ pop wfA wfB M⊢ refl)
  infer Γ (M ⦂ A ⇒⟨ unbind X ⟩ B) | just (C , k , Γ′ , pop)
      | _ | _ | _ | _ = nothing
  infer Γ (is p M G) with groundWitness? G | check Γ M ★
  infer Γ (is p M G) | just g | just M⊢ =
    just (`ι 𝔹 , ⊢is g M⊢)
  infer Γ (is p M G) | _ | _ = nothing
  infer Γ (pair L M) with infer Γ L | infer Γ M
  infer Γ (pair L M) | just (A , L⊢) | just (B , M⊢) =
    just (A `× B , ⊢pair L⊢ M⊢)
  infer Γ (pair L M) | _ | _ = nothing
  infer Γ (fst M) with infer Γ M
  infer Γ (fst M) | just (A `× B , M⊢) = just (A , ⊢fst M⊢)
  infer Γ (fst M) | _ = nothing
  infer Γ (snd M) with infer Γ M
  infer Γ (snd M) | just (A `× B , M⊢) = just (B , ⊢snd M⊢)
  infer Γ (snd M) | _ = nothing
  infer Γ (ifte L M N) with check Γ L (`ι 𝔹) | infer Γ M
  infer Γ (ifte L M N) | just L⊢ | just (A , M⊢) with check Γ N A
  infer Γ (ifte L M N) | just L⊢ | just (A , M⊢) | just N⊢ =
    just (A , ⊢if L⊢ M⊢ N⊢)
  infer Γ (ifte L M N) | just L⊢ | just (A , M⊢) | nothing = nothing
  infer Γ (ifte L M N) | _ | _ = nothing
  infer Γ (prim add1 M) with check Γ M (`ι 𝕀)
  infer Γ (prim add1 M) | just M⊢ = just (`ι 𝕀 , ⊢prim refl M⊢)
  infer Γ (prim add1 M) | nothing = nothing
  infer Γ (prim one-minus M) with check Γ M (`ι 𝕀)
  infer Γ (prim one-minus M) | just M⊢ =
    just (`ι 𝕀 , ⊢prim refl M⊢)
  infer Γ (prim one-minus M) | nothing = nothing
  infer Γ (prim f M) with check Γ M (`ι 𝔹)
  infer Γ (prim f M) | just M⊢ = just (`ι 𝕀 , ⊢prim refl M⊢)
  infer Γ (prim f M) | nothing = nothing
  infer Γ (prim not M) with check Γ M (`ι 𝔹)
  infer Γ (prim not M) | just M⊢ = just (`ι 𝔹 , ⊢prim refl M⊢)
  infer Γ (prim not M) | nothing = nothing
  infer Γ (prim positive? M) with check Γ M (`ι 𝕀)
  infer Γ (prim positive? M) | just M⊢ =
    just (`ι 𝔹 , ⊢prim refl M⊢)
  infer Γ (prim positive? M) | nothing = nothing
  infer Γ (blame p) = nothing

  check : (Γ : Ctx) → (M : Term) → (A : Ty) → Maybe (Γ ⊢ M ⦂ A)
  check Γ (blame p) A with wfTyDec Γ A
  check Γ (blame p) A | yes wfA = just (⊢blame wfA)
  check Γ (blame p) A | no _ = nothing
  check Γ M A with infer Γ M
  check Γ M A | just (B , M⊢) with B ≟Ty A
  check Γ M A | just (B , M⊢) | yes refl = just M⊢
  check Γ M A | just (B , M⊢) | no _ = nothing
  check Γ M A | nothing = nothing

maybeToBool : ∀ {A : Set} → Maybe A → Bool
maybeToBool (just _) = true
maybeToBool nothing = false

inferType : Ctx → Term → Maybe Ty
inferType Γ M with infer Γ M
inferType Γ M | just (A , _) = just A
inferType Γ M | nothing = nothing

check? : Ctx → Term → Ty → Bool
check? Γ M A = maybeToBool (check Γ M A)

inferClosed : Term → Maybe Ty
inferClosed = inferType ∅

checkInAs : Ctx → Term → Ty → Bool
checkInAs = check?

checkClosedAs : Term → Ty → Bool
checkClosedAs = check? ∅
