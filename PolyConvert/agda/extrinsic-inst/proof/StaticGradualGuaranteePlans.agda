module proof.StaticGradualGuaranteePlans where

-- File Charter:
--   * Proof surface for the experimental edit-plan design in
--     `GradualTermPlans`.
--   * States the well-typedness theorem for `applyTermEdit`: applying a
--     well-formed term edit to a well-typed source term produces a target term
--     that is well typed at the type returned by the edit interpreter.
--   * The ordinary SGG proof remains in `proof/StaticGradualGuarantee`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (zero; suc; _+_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import Ctx using (CtxWf; ctxWf-∷; ⤊ᵗ)
open import Imprecision
open import Consistency
open import GradualTerms
  using
    ( GTerm
    ; Value
    ; `_
    ; ƛ_⇒_
    ; _·_
    ; Λ_
    ; _`[_]
    ; _⊕[_]_
    ; $
    ; renameᵗᴳ
    ; renameᵗᴳ-cong
    ; _∣_⊢_⦂_
    ; ⊢`
    ; ⊢ƛ
    ; ⊢·
    ; ⊢·★
    ; ⊢Λ
    ; ⊢•
    ; ⊢$
    ; ⊢⊕
    ; cong-⊢ᴳ⦂
    )
open import GradualTermPlans
open import Primitives using (κℕ)
open import proof.ConsistencyProperties
  using
    ( drop-both-~
    ; drop-⇑ᵗ-WfTy-extend-X⊑X
    ; extend-X~X-sym
    )
open import proof.ImprecisionConsistent using (app-consistencyᵢ)
open import proof.ImprecisionProperties using (⊑-tgt-wf)
open import proof.GradualTermProperties using (drop-renameᵗᴳ-wt)
open import proof.TypeProperties using (raise-ext; rename-raise-ext)

codTy : Ty → Ty
codTy (A ⇒ B) = B
codTy A = ★

bodyTy : Ty → Ty
bodyTy (`∀ A) = A
bodyTy A = ★

lookup-unique-ctx :
  ∀ {Γ x A B} →
  Γ ∋ x ⦂ A →
  Γ ∋ x ⦂ B →
  A ≡ B
lookup-unique-ctx Z Z = refl
lookup-unique-ctx (S x∈) (S y∈) = lookup-unique-ctx x∈ y∈

type-uniqueᴳ :
  ∀ {Δ Γ M A B} →
  Δ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Γ ⊢ M ⦂ B →
  A ≡ B
type-uniqueᴳ (⊢` x∈) (⊢` y∈) = lookup-unique-ctx x∈ y∈
type-uniqueᴳ (⊢ƛ wfA M⊢) (⊢ƛ wfA′ M⊢′) =
  cong (_ ⇒_) (type-uniqueᴳ M⊢ M⊢′)
type-uniqueᴳ (⊢· L⊢ M⊢ A~A′) (⊢· L⊢′ M⊢′ B~B′) =
  cong codTy (type-uniqueᴳ L⊢ L⊢′)
type-uniqueᴳ (⊢· L⊢ M⊢ A~A′) (⊢·★ L⊢′ M⊢′ B~★)
    with type-uniqueᴳ L⊢ L⊢′
type-uniqueᴳ (⊢· L⊢ M⊢ A~A′) (⊢·★ L⊢′ M⊢′ B~★) | ()
type-uniqueᴳ (⊢·★ L⊢ M⊢ A~★) (⊢· L⊢′ M⊢′ B~B′)
    with type-uniqueᴳ L⊢ L⊢′
type-uniqueᴳ (⊢·★ L⊢ M⊢ A~★) (⊢· L⊢′ M⊢′ B~B′) | ()
type-uniqueᴳ (⊢·★ L⊢ M⊢ A~★) (⊢·★ L⊢′ M⊢′ B~★) = refl
type-uniqueᴳ (⊢Λ vM M⊢) (⊢Λ vM′ M⊢′) =
  cong `∀ (type-uniqueᴳ M⊢ M⊢′)
type-uniqueᴳ {M = M `[ T ]} (⊢• M⊢ wfB wfT) (⊢• M⊢′ wfB′ wfT′) =
  cong (λ A → bodyTy A [ T ]ᵗ) (type-uniqueᴳ M⊢ M⊢′)
type-uniqueᴳ (⊢$ κ) (⊢$ κ′) = refl
type-uniqueᴳ (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    (⊢⊕ L⊢′ A′~ℕ op′ M⊢′ B′~ℕ) = refl

cong-~ :
  ∀ {Δ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Δ ⊢ A ~ B →
  Δ ⊢ A′ ~ B′
cong-~ refl refl c = c

sourceCtx-liftTyEditCtx :
  ∀ m {Φ} →
  (Γπ : TyEditCtx Φ) →
  sourceCtx (liftTyEditCtx m Γπ) ≡ ⤊ᵗ (sourceCtx Γπ)
sourceCtx-liftTyEditCtx m [] = refl
sourceCtx-liftTyEditCtx m ((A , e) ∷ Γπ) =
  cong (⇑ᵗ A ∷_) (sourceCtx-liftTyEditCtx m Γπ)

sourceCtxWf-liftTyEditCtx :
  ∀ m {Φ} {Γπ : TyEditCtx Φ} →
  CtxWf (length Φ) 0 (sourceCtx Γπ) →
  CtxWf (length (m ∷ Φ)) 0 (sourceCtx (liftTyEditCtx m Γπ))
sourceCtxWf-liftTyEditCtx m {Γπ = []} wfΓ ()
sourceCtxWf-liftTyEditCtx m {Γπ = (A , e) ∷ Γπ} wfΓ Z =
  renameᵗ-preserves-WfTy (wfΓ Z) TyRenameWf-suc
sourceCtxWf-liftTyEditCtx m {Γπ = (A , e) ∷ Γπ} wfΓ (S x∈) =
  sourceCtxWf-liftTyEditCtx m (λ h → wfΓ (S h)) x∈

termEdit-source-typed :
  ∀ {Φ Γπ M A C} →
  CtxWf (length Φ) 0 (sourceCtx Γπ) →
  (ρ : TermEdit Φ Γπ M A) →
  length Φ ∣ sourceCtx Γπ ⊢ M ⦂ C →
  length Φ ∣ sourceCtx Γπ ⊢ M ⦂ A
termEdit-source-typed wfΓ (term-var {P = A , e} x∈) (⊢` y∈) =
  cong-⊢ᴳ⦂ refl refl refl (sym (lookup-unique-ctx (lookupSourceCtx x∈) y∈))
    (⊢` y∈)
termEdit-source-typed wfΓ (term-lam πA ρM) (⊢ƛ wfA M⊢) =
  ⊢ƛ wfA (termEdit-source-typed (ctxWf-∷ wfA wfΓ) ρM M⊢)
termEdit-source-typed wfΓ (term-app {A = A} {B = B} {A′ = A′} ρL ρM)
    (⊢· {A = C} {A′ = C′} L⊢ M⊢ C~C′)
    with termEdit-source-typed wfΓ ρL L⊢
       | termEdit-source-typed wfΓ ρM M⊢
termEdit-source-typed wfΓ (term-app {A = A} {B = B} {A′ = A′} ρL ρM)
    (⊢· {A = C} {A′ = C′} L⊢ M⊢ C~C′)
    | L⊢′ | M⊢′
    with type-uniqueᴳ L⊢ L⊢′ | type-uniqueᴳ M⊢ M⊢′
termEdit-source-typed wfΓ (term-app ρL ρM)
    (⊢· L⊢ M⊢ C~C′) | L⊢′ | M⊢′ | refl | refl =
  ⊢· L⊢′ M⊢′ C~C′
termEdit-source-typed wfΓ (term-app ρL ρM) (⊢·★ L⊢ M⊢ C~★)
    with termEdit-source-typed wfΓ ρL L⊢
termEdit-source-typed wfΓ (term-app ρL ρM) (⊢·★ L⊢ M⊢ C~★)
    | L⊢′ with type-uniqueᴳ L⊢ L⊢′
termEdit-source-typed wfΓ (term-app ρL ρM) (⊢·★ L⊢ M⊢ C~★)
    | L⊢′ | ()
termEdit-source-typed wfΓ (term-app★ ρL ρM) (⊢· L⊢ M⊢ C~C′)
    with termEdit-source-typed wfΓ ρL L⊢
termEdit-source-typed wfΓ (term-app★ ρL ρM) (⊢· L⊢ M⊢ C~C′)
    | L⊢′ with type-uniqueᴳ L⊢ L⊢′
termEdit-source-typed wfΓ (term-app★ ρL ρM) (⊢· L⊢ M⊢ C~C′)
    | L⊢′ | ()
termEdit-source-typed wfΓ (term-app★ {A′ = A′} ρL ρM)
    (⊢·★ {A′ = C′} L⊢ M⊢ C~★)
    with termEdit-source-typed wfΓ ρL L⊢
       | termEdit-source-typed wfΓ ρM M⊢
termEdit-source-typed wfΓ (term-app★ {A′ = A′} ρL ρM)
    (⊢·★ {A′ = C′} L⊢ M⊢ C~★)
    | L⊢′ | M⊢′
    with type-uniqueᴳ M⊢ M⊢′
termEdit-source-typed wfΓ (term-app★ ρL ρM) (⊢·★ L⊢ M⊢ C~★)
    | L⊢′ | M⊢′ | refl =
  ⊢·★ L⊢′ M⊢′ C~★
termEdit-source-typed wfΓ (term-LamKeep ρM) (⊢Λ vM M⊢) =
  ⊢Λ vM
    (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
      (sourceCtx-liftTyEditCtx X⊑X _)
      (termEdit-source-typed
        (sourceCtxWf-liftTyEditCtx X⊑X wfΓ)
        ρM
        (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
          (sym (sourceCtx-liftTyEditCtx X⊑X _)) M⊢)))
termEdit-source-typed wfΓ (term-LamDrop ρM) (⊢Λ vM M⊢) =
  ⊢Λ vM
    (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
      (sourceCtx-liftTyEditCtx X⊑★ _)
      (termEdit-source-typed
        (sourceCtxWf-liftTyEditCtx X⊑★ wfΓ)
        ρM
        (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
          (sym (sourceCtx-liftTyEditCtx X⊑★ _)) M⊢)))
termEdit-source-typed wfΓ (term-tyappKeep ρM πT) (⊢• M⊢ wfB wfT)
    with termEdit-source-typed wfΓ ρM M⊢
termEdit-source-typed wfΓ (term-tyappKeep ρM πT) (⊢• M⊢ wfB wfT)
    | M⊢′ with type-uniqueᴳ M⊢ M⊢′
termEdit-source-typed wfΓ (term-tyappKeep ρM πT) (⊢• M⊢ wfB wfT)
    | M⊢′ | refl =
  ⊢• M⊢′ wfB wfT
termEdit-source-typed wfΓ (term-tyappDrop ρM πT) (⊢• M⊢ wfB wfT)
    with termEdit-source-typed wfΓ ρM M⊢
termEdit-source-typed wfΓ (term-tyappDrop ρM πT) (⊢• M⊢ wfB wfT)
    | M⊢′ with type-uniqueᴳ M⊢ M⊢′
termEdit-source-typed wfΓ (term-tyappDrop ρM πT) (⊢• M⊢ wfB wfT)
    | M⊢′ | refl =
  ⊢• M⊢′ wfB wfT
termEdit-source-typed wfΓ term-const (⊢$ κ) = ⊢$ κ
termEdit-source-typed wfΓ (term-prim ρL ρM) (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with termEdit-source-typed wfΓ ρL L⊢
       | termEdit-source-typed wfΓ ρM M⊢
termEdit-source-typed wfΓ (term-prim ρL ρM) (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L⊢′ | M⊢′ with type-uniqueᴳ L⊢ L⊢′ | type-uniqueᴳ M⊢ M⊢′
termEdit-source-typed wfΓ (term-prim ρL ρM) (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L⊢′ | M⊢′ | refl | refl =
  ⊢⊕ L⊢′ A~ℕ op M⊢′ B~ℕ

termApp-align :
  ∀ {Φ Γπ L M A B A′} →
  CtxWf (length Φ) 0 (sourceCtx Γπ) →
  (ρL : TermEdit Φ Γπ L (A ⇒ B)) →
  (ρM : TermEdit Φ Γπ M A′) →
  length Φ ∣ sourceCtx Γπ ⊢ L · M ⦂ B →
  ((length Φ ∣ sourceCtx Γπ ⊢ L ⦂ A ⇒ B) ×
   (length Φ ∣ sourceCtx Γπ ⊢ M ⦂ A′)) ×
  extend-X~X (length Φ) [] ⊢ A ~ A′
termApp-align wfΓ ρL ρM (⊢· L⊢ M⊢ A~A′)
    with termEdit-source-typed wfΓ ρL L⊢
       | termEdit-source-typed wfΓ ρM M⊢
termApp-align wfΓ ρL ρM (⊢· L⊢ M⊢ A~A′)
    | L⊢′ | M⊢′
    with type-uniqueᴳ L⊢ L⊢′ | type-uniqueᴳ M⊢ M⊢′
termApp-align wfΓ ρL ρM (⊢· L⊢ M⊢ A~A′)
    | L⊢′ | M⊢′ | refl | refl =
  (L⊢′ , M⊢′) , A~A′
termApp-align wfΓ ρL ρM (⊢·★ L⊢ M⊢ A~★)
    with termEdit-source-typed wfΓ ρL L⊢
termApp-align wfΓ ρL ρM (⊢·★ L⊢ M⊢ A~★)
    | L⊢′ with type-uniqueᴳ L⊢ L⊢′
termApp-align wfΓ ρL ρM (⊢·★ L⊢ M⊢ A~★)
    | L⊢′ | ()

termApp★-align :
  ∀ {Φ Γπ L M A′} →
  CtxWf (length Φ) 0 (sourceCtx Γπ) →
  (ρL : TermEdit Φ Γπ L ★) →
  (ρM : TermEdit Φ Γπ M A′) →
  length Φ ∣ sourceCtx Γπ ⊢ L · M ⦂ ★ →
  ((length Φ ∣ sourceCtx Γπ ⊢ L ⦂ ★) ×
   (length Φ ∣ sourceCtx Γπ ⊢ M ⦂ A′)) ×
  extend-X~X (length Φ) [] ⊢ A′ ~ ★
termApp★-align wfΓ ρL ρM (⊢· L⊢ M⊢ A~A′)
    with termEdit-source-typed wfΓ ρL L⊢
termApp★-align wfΓ ρL ρM (⊢· L⊢ M⊢ A~A′)
    | L⊢′ with type-uniqueᴳ L⊢ L⊢′
termApp★-align wfΓ ρL ρM (⊢· L⊢ M⊢ A~A′)
    | L⊢′ | ()
termApp★-align wfΓ ρL ρM (⊢·★ L⊢ M⊢ A~★)
    with termEdit-source-typed wfΓ ρL L⊢
       | termEdit-source-typed wfΓ ρM M⊢
termApp★-align wfΓ ρL ρM (⊢·★ L⊢ M⊢ A~★)
    | L⊢′ | M⊢′
    with type-uniqueᴳ M⊢ M⊢′
termApp★-align wfΓ ρL ρM (⊢·★ L⊢ M⊢ A~★)
    | L⊢′ | M⊢′ | refl =
  (L⊢′ , M⊢′) , A~★

termTyApp∀-align :
  ∀ {Φ Γπ M T B C} →
  CtxWf (length Φ) 0 (sourceCtx Γπ) →
  (ρM : TermEdit Φ Γπ M (`∀ B)) →
  (πT : TyEdit Φ T) →
  length Φ ∣ sourceCtx Γπ ⊢ M `[ T ] ⦂ C →
  (length Φ ∣ sourceCtx Γπ ⊢ M ⦂ `∀ B) ×
  (WfTy (suc (length Φ)) 0 B × WfTy (length Φ) 0 T)
termTyApp∀-align wfΓ ρM πT (⊢• M⊢ wfB wfT)
    with termEdit-source-typed wfΓ ρM M⊢
termTyApp∀-align wfΓ ρM πT (⊢• M⊢ wfB wfT)
    | M⊢′ with type-uniqueᴳ M⊢ M⊢′
termTyApp∀-align wfΓ ρM πT (⊢• M⊢ wfB wfT)
    | M⊢′ | refl =
  M⊢′ , wfB , wfT

applyTermEdit-term :
  ∀ {Φ A} →
  (Γπ : TyEditCtx Φ) →
  (M : GTerm) →
  TermEdit Φ Γπ M A →
  GTerm
applyTermEdit-term Γπ M ρ = proj₁ (applyTermEdit Γπ M ρ)

applyTermEdit-type :
  ∀ {Φ A} →
  (Γπ : TyEditCtx Φ) →
  (M : GTerm) →
  (ρ : TermEdit Φ Γπ M A) →
  Ty
applyTermEdit-type Γπ M ρ = proj₁ (proj₂ (applyTermEdit Γπ M ρ))

applyTermEdit-term-ok :
  ∀ {Φ A} →
  (Γπ : TyEditCtx Φ) →
  (M : GTerm) →
  (ρ : TermEdit Φ Γπ M A) →
  TargetTermOk Φ (applyTermEdit-term Γπ M ρ)
applyTermEdit-term-ok Γπ M ρ = proj₁ (proj₂ (proj₂ (applyTermEdit Γπ M ρ)))

applyTermEdit-type-ok :
  ∀ {Φ A} →
  (Γπ : TyEditCtx Φ) →
  (M : GTerm) →
  (ρ : TermEdit Φ Γπ M A) →
  TargetOk Φ (applyTermEdit-type Γπ M ρ)
applyTermEdit-type-ok Γπ M ρ = proj₂ (proj₂ (proj₂ (applyTermEdit Γπ M ρ)))

data TermEditOk (Φ : VarPrecCtx) (Γπ : TyEditCtx Φ) :
    ∀ {M A} → TermEdit Φ Γπ M A → Set where
  ok-var : ∀ {x P} {x∈ : Γπ ∋ᴿ x ⦂ P} →
    TermEditOk Φ Γπ (term-var x∈)

  ok-lam : ∀ {A M B} {πA : TyEdit Φ A}
      {ρM : TermEdit Φ ((A , πA) ∷ Γπ) M B} →
    TermEditOk Φ ((A , πA) ∷ Γπ) ρM →
    TermEditOk Φ Γπ (term-lam πA ρM)

  ok-app : ∀ {L M A B A′}
      {ρL : TermEdit Φ Γπ L (A ⇒ B)}
      {ρM : TermEdit Φ Γπ M A′} →
    TermEditOk Φ Γπ ρL →
    TermEditOk Φ Γπ ρM →
    TermEditOk Φ Γπ (term-app ρL ρM)

  ok-app★ : ∀ {L M A′}
      {ρL : TermEdit Φ Γπ L ★}
      {ρM : TermEdit Φ Γπ M A′} →
    TermEditOk Φ Γπ ρL →
    TermEditOk Φ Γπ ρM →
    TermEditOk Φ Γπ (term-app★ ρL ρM)

  ok-LamKeep : ∀ {M A}
      {ρM : TermEdit (X⊑X ∷ Φ) (liftTyEditCtx X⊑X Γπ) M A} →
    TermEditOk (X⊑X ∷ Φ) (liftTyEditCtx X⊑X Γπ) ρM →
    TermEditOk Φ Γπ (term-LamKeep ρM)

  ok-LamDrop : ∀ {M A}
      {ρM : TermEdit (X⊑★ ∷ Φ) (liftTyEditCtx X⊑★ Γπ) M A} →
    TermEditOk (X⊑★ ∷ Φ) (liftTyEditCtx X⊑★ Γπ) ρM →
    TermEditOk Φ Γπ (term-LamDrop ρM)

  ok-tyapp-keep : ∀ {M T B B′ q}
      {ρM : TermEdit Φ Γπ M (`∀ B)}
      {πT : TyEdit Φ T} →
    TermEditOk Φ Γπ ρM →
    applyTermEdit-type Γπ M ρM ≡ `∀ B′ →
    WfTy (suc (length Φ)) 0 B′ →
    0 ∣ Φ ⊢ q ⦂ B [ T ]ᵗ ⊑ B′ [ applyTyEdit-type πT ]ᵗ →
    TermEditOk Φ Γπ (term-tyappKeep ρM πT)

  ok-tyapp-drop : ∀ {M T B q}
      {ρM : TermEdit Φ Γπ M (`∀ B)}
      {πT : TyEdit Φ T} →
    TermEditOk Φ Γπ ρM →
    0 ∣ Φ ⊢ q ⦂ B [ T ]ᵗ ⊑ applyTermEdit-type Γπ M ρM →
    TermEditOk Φ Γπ (term-tyappDrop ρM πT)

  ok-const : ∀ {κ} →
    TermEditOk Φ Γπ (term-const {κ = κ})

  ok-prim : ∀ {L M op A B}
      {ρL : TermEdit Φ Γπ L A}
      {ρM : TermEdit Φ Γπ M B} →
    TermEditOk Φ Γπ ρL →
    TermEditOk Φ Γπ ρM →
    TermEditOk Φ Γπ (term-prim {op = op} ρL ρM)

dropTargetTermFrom-value :
  ∀ n {Γ M} →
  (okM : TargetTermOk (extend-X⊑X n (X⊑★ ∷ Γ)) M) →
  Value M →
  Value (dropTargetTermFrom n okM)
dropTargetTermFrom-value n (tt-lam okA okM) (ƛ A ⇒ M) =
  ƛ _ ⇒ _
dropTargetTermFrom-value n tt-const ($ κ) = $ κ
dropTargetTermFrom-value n (tt-Lam okM) (Λ M) =
  Λ _

applyTermEdit-value :
  ∀ {Φ Γπ M A} →
  CtxWf (length Φ) 0 (sourceCtx Γπ) →
  (ρ : TermEdit Φ Γπ M A) →
  TermEditOk Φ Γπ ρ →
  length Φ ∣ sourceCtx Γπ ⊢ M ⦂ A →
  Value M →
  Value (applyTermEdit-term Γπ M ρ)
applyTermEdit-value wfΓ (term-lam πA ρM) okρ (⊢ƛ wfA M⊢) (ƛ A ⇒ M) =
  ƛ _ ⇒ _
applyTermEdit-value {Γπ = Γπ} wfΓ (term-LamKeep {M = M} ρM)
    (ok-LamKeep okM) (⊢Λ vM M⊢) (Λ M)
    with applyTermEdit (liftTyEditCtx X⊑X Γπ) M ρM
applyTermEdit-value {Γπ = Γπ} wfΓ (term-LamKeep ρM)
    (ok-LamKeep okM) (⊢Λ vM M⊢) (Λ M) | M′ , B′ , okM′ , okB′ =
  Λ M′
applyTermEdit-value {Γπ = Γπ} wfΓ (term-LamDrop {M = M} ρM)
    (ok-LamDrop okM) (⊢Λ vM M⊢) (Λ M)
    with applyTermEdit (liftTyEditCtx X⊑★ Γπ) M ρM
       | applyTermEdit-value
          (sourceCtxWf-liftTyEditCtx X⊑★ wfΓ)
          ρM
          okM
          (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
            (sym (sourceCtx-liftTyEditCtx X⊑★ Γπ)) M⊢)
          vM
applyTermEdit-value {Γπ = Γπ} wfΓ (term-LamDrop ρM)
    (ok-LamDrop okM) (⊢Λ vM M⊢) (Λ M)
    | M′ , B′ , okM′ , okB′ | vM′ =
  dropTargetTermFrom-value zero okM′ vM′
applyTermEdit-value wfΓ term-const ok-const (⊢$ (κℕ n)) ($ (κℕ n)) = $ (κℕ n)

ApplyTermEditWtResult :
  ∀ {Φ A} →
  (Γπ : TyEditCtx Φ) →
  (M : GTerm) →
  TermEdit Φ Γπ M A →
  Set
ApplyTermEditWtResult {Φ} {A} Γπ M ρ =
  (length Φ ∣ targetCtx Γπ ⊢
    applyTermEdit-term Γπ M ρ ⦂ applyTermEdit-type Γπ M ρ) ×
  (Σ[ p ∈ Imp ]
    0 ∣ Φ ⊢ p ⦂ A ⊑ applyTermEdit-type Γπ M ρ)

PlannedAppWtResult :
  ∀ {Φ} →
  (Γπ : TyEditCtx Φ) →
  (L′ M′ : GTerm) →
  TargetTermOk Φ L′ →
  TargetTermOk Φ M′ →
  (D : Ty) →
  TargetOk Φ D →
  (B : Ty) →
  Set
PlannedAppWtResult {Φ} Γπ L′ M′ okL okM D okD B =
  (length Φ ∣ targetCtx Γπ ⊢
    proj₁ (plannedAppTerm L′ M′ okL okM D okD) ⦂
    proj₁ (proj₂ (plannedAppTerm L′ M′ okL okM D okD))) ×
  (Σ[ p ∈ Imp ]
    0 ∣ Φ ⊢ p ⦂ B ⊑
      proj₁ (proj₂ (plannedAppTerm L′ M′ okL okM D okD)))

plannedApp-wt :
  ∀ {Φ Γπ L′ M′ A B A′ C D pF pArg} →
  (okL : TargetTermOk Φ L′) →
  (okM : TargetTermOk Φ M′) →
  (okD : TargetOk Φ D) →
  length Φ ∣ targetCtx Γπ ⊢ L′ ⦂ D →
  0 ∣ Φ ⊢ pF ⦂ (A ⇒ B) ⊑ D →
  length Φ ∣ targetCtx Γπ ⊢ M′ ⦂ C →
  0 ∣ Φ ⊢ pArg ⦂ A′ ⊑ C →
  extend-X~X (length Φ) [] ⊢ A ~ A′ →
  PlannedAppWtResult Γπ L′ M′ okL okM D okD B
plannedApp-wt okL okM (ok-X x∈) L′⊢ () M′⊢ pArg⊢ A~A′
plannedApp-wt okL okM ok-｀ L′⊢ () M′⊢ pArg⊢ A~A′
plannedApp-wt okL okM ok-‵ L′⊢ () M′⊢ pArg⊢ A~A′
plannedApp-wt okL okM ok-★ L′⊢
    (⊢A-⊑-★ ★⇒★
      (⊢A⇒B-⊑-A′⇒B′ {p = pA} {q = pB} pA⊢ pB⊢))
    M′⊢ pArg⊢ A~A′ =
  ⊢·★ L′⊢ M′⊢
    (app-consistencyᵢ refl pArg⊢ (extend-X~X-sym A~A′) pA⊢) ,
  pB , pB⊢
plannedApp-wt okL okM ok-★ L′⊢
    (⊢A-⊑-★ (｀ α) ()) M′⊢ pArg⊢ A~A′
plannedApp-wt okL okM ok-★ L′⊢
    (⊢A-⊑-★ (‵ ι) ()) M′⊢ pArg⊢ A~A′
plannedApp-wt okL okM (ok-⇒ okA okB) L′⊢
    (⊢A⇒B-⊑-A′⇒B′ {p = pA} {q = pB} pA⊢ pB⊢)
    M′⊢ pArg⊢ A~A′ =
  ⊢· L′⊢ M′⊢ (app-consistencyᵢ refl pA⊢ A~A′ pArg⊢) ,
  pB , pB⊢
plannedApp-wt okL okM (ok-∀ okB) L′⊢ () M′⊢ pArg⊢ A~A′

starApp-wt :
  ∀ {Φ} {Γπ : TyEditCtx Φ} {L′ M′ A′ C D pF pArg} →
  TargetOk Φ D →
  length Φ ∣ targetCtx Γπ ⊢ L′ ⦂ D →
  0 ∣ Φ ⊢ pF ⦂ ★ ⊑ D →
  length Φ ∣ targetCtx Γπ ⊢ M′ ⦂ C →
  0 ∣ Φ ⊢ pArg ⦂ A′ ⊑ C →
  extend-X~X (length Φ) [] ⊢ A′ ~ ★ →
  length Φ ∣ targetCtx Γπ ⊢ L′ · M′ ⦂ ★
starApp-wt (ok-X x∈) L′⊢ () M′⊢ pArg⊢ A′~★
starApp-wt ok-｀ L′⊢ () M′⊢ pArg⊢ A′~★
starApp-wt ok-‵ L′⊢ () M′⊢ pArg⊢ A′~★
starApp-wt ok-★ L′⊢ ⊢★-⊑-★ M′⊢ pArg⊢ A′~★ =
  ⊢·★ L′⊢ M′⊢ (app-consistencyᵢ refl pArg⊢ A′~★ ⊢★-⊑-★)
starApp-wt ok-★ L′⊢ (⊢A-⊑-★ (｀ α) ()) M′⊢ pArg⊢ A′~★
starApp-wt ok-★ L′⊢ (⊢A-⊑-★ (‵ ι) ()) M′⊢ pArg⊢ A′~★
starApp-wt ok-★ L′⊢ (⊢A-⊑-★ ★⇒★ ()) M′⊢ pArg⊢ A′~★
starApp-wt (ok-⇒ okA okB) L′⊢ () M′⊢ pArg⊢ A′~★
starApp-wt (ok-∀ okB) L′⊢ () M′⊢ pArg⊢ A′~★

insertMode-extend-X⊑X :
  ∀ n k m Γ →
  insertMode (n + k) m (extend-X⊑X n Γ) ≡
  extend-X⊑X n (insertMode k m Γ)
insertMode-extend-X⊑X zero k m Γ = refl
insertMode-extend-X⊑X (suc n) k m Γ =
  cong (X⊑X ∷_) (insertMode-extend-X⊑X n k m Γ)

dropVarFrom-raise-same :
  ∀ k X →
  dropVarFrom k (raiseVarFrom k X) ≡ X
dropVarFrom-raise-same zero X = refl
dropVarFrom-raise-same (suc k) zero = refl
dropVarFrom-raise-same (suc k) (suc X) =
  cong suc (dropVarFrom-raise-same k X)

dropTyFrom-raise-same :
  ∀ k A →
  dropTyFrom k (renameᵗ (raiseVarFrom k) A) ≡ A
dropTyFrom-raise-same k (＇ X) =
  cong ＇_ (dropVarFrom-raise-same k X)
dropTyFrom-raise-same k (｀ α) = refl
dropTyFrom-raise-same k (‵ ι) = refl
dropTyFrom-raise-same k ★ = refl
dropTyFrom-raise-same k (A ⇒ B) =
  cong₂ _⇒_ (dropTyFrom-raise-same k A) (dropTyFrom-raise-same k B)
dropTyFrom-raise-same k (`∀ A)
  rewrite rename-raise-ext k A =
  cong `∀ (dropTyFrom-raise-same (suc k) A)

rename-raise-injective :
  ∀ k {A B} →
  renameᵗ (raiseVarFrom k) A ≡ renameᵗ (raiseVarFrom k) B →
  A ≡ B
rename-raise-injective k {A = A} {B = B} eq =
  trans (sym (dropTyFrom-raise-same k A))
    (trans (cong (dropTyFrom k) eq) (dropTyFrom-raise-same k B))

dropTargetVar-raw :
  ∀ n {Φ X} →
  (x∈ : extend-X⊑X n (X⊑★ ∷ Φ) ∋ X ∶ X⊑X) →
  dropTargetVar n x∈ ≡ dropVarFrom n X
dropTargetVar-raw zero (there x∈) = refl
dropTargetVar-raw (suc n) here = refl
dropTargetVar-raw (suc n) (there x∈) =
  cong suc (dropTargetVar-raw n x∈)

dropTargetFrom-raw :
  ∀ n {Φ A} →
  (ok : TargetOk (extend-X⊑X n (X⊑★ ∷ Φ)) A) →
  dropTargetFrom n ok ≡ dropTyFrom n A
dropTargetFrom-raw n (ok-X x∈) = cong ＇_ (dropTargetVar-raw n x∈)
dropTargetFrom-raw n ok-｀ = refl
dropTargetFrom-raw n ok-‵ = refl
dropTargetFrom-raw n ok-★ = refl
dropTargetFrom-raw n (ok-⇒ okA okB) =
  cong₂ _⇒_ (dropTargetFrom-raw n okA) (dropTargetFrom-raw n okB)
dropTargetFrom-raw n (ok-∀ okA) =
  cong `∀ (dropTargetFrom-raw (suc n) okA)

dropVarFrom-rename-raise :
  ∀ n k (m : VarPrec) {Φ X} →
  (x∈ : extend-X⊑X n (X⊑★ ∷ Φ) ∋ X ∶ X⊑X) →
  dropVarFrom n (raiseVarFrom (n + suc k) X) ≡
  raiseVarFrom (n + k) (dropVarFrom n X)
dropVarFrom-rename-raise zero k m (there x∈) = refl
dropVarFrom-rename-raise (suc n) k m here = refl
dropVarFrom-rename-raise (suc n) k m (there x∈) =
  cong suc (dropVarFrom-rename-raise n k m x∈)

dropTyFrom-rename-raise :
  ∀ n k {Φ A} →
  (ok : TargetOk (extend-X⊑X n (X⊑★ ∷ Φ)) A) →
  dropTyFrom n (renameᵗ (raiseVarFrom (n + suc k)) A) ≡
  renameᵗ (raiseVarFrom (n + k)) (dropTyFrom n A)
dropTyFrom-rename-raise n k (ok-X x∈) =
  cong ＇_ (dropVarFrom-rename-raise n k X⊑X x∈)
dropTyFrom-rename-raise n k ok-｀ = refl
dropTyFrom-rename-raise n k ok-‵ = refl
dropTyFrom-rename-raise n k ok-★ = refl
dropTyFrom-rename-raise n k (ok-⇒ okA okB) =
  cong₂ _⇒_ (dropTyFrom-rename-raise n k okA)
             (dropTyFrom-rename-raise n k okB)
dropTyFrom-rename-raise n k {A = `∀ A} (ok-∀ okA)
  rewrite rename-raise-ext (n + suc k) A
        | rename-raise-ext (n + k) (dropTyFrom (suc n) A) =
  cong `∀ (dropTyFrom-rename-raise (suc n) k okA)

dropTyEdit-insert-type-raw :
  ∀ n k m {Φ A} →
  (e : TyEdit (extend-X⊑X n (X⊑★ ∷ Φ)) A) →
  dropTyFrom n (applyTyEdit-type (insertTyEditAt (n + suc k) m e)) ≡
  renameᵗ (raiseVarFrom (n + k)) (dropTyFrom n (applyTyEdit-type e))
dropTyEdit-insert-type-raw zero k m (ty-star s) = refl
dropTyEdit-insert-type-raw zero k m (ty-X (there x∈)) = refl
dropTyEdit-insert-type-raw zero k m ty-｀ = refl
dropTyEdit-insert-type-raw zero k m ty-‵ = refl
dropTyEdit-insert-type-raw zero k m ty-★ = refl
dropTyEdit-insert-type-raw zero k m (ty-⇒ eA eB)
  rewrite dropTyEdit-insert-type-raw zero k m eA
        | dropTyEdit-insert-type-raw zero k m eB = refl
dropTyEdit-insert-type-raw zero k m {A = `∀ A} (ty-∀keep eA)
  rewrite rename-raise-ext (suc k) A
        | rename-raise-ext k (dropTyFrom 1 (applyTyEdit-type eA))
        | dropTyEdit-insert-type-raw 1 k m eA = refl
dropTyEdit-insert-type-raw zero k m {A = `∀ A} (ty-∀drop eA)
  rewrite rename-raise-ext (suc k) A
        | dropTargetFrom-raw zero
            (tyEdit-ok (insertTyEditAt (suc (suc k)) m eA))
        | dropTyEdit-insert-type-raw zero (suc k) m eA
        | sym (dropTargetFrom-raw zero (tyEdit-ok eA))
        | dropTyFrom-rename-raise zero k
            (dropTargetFrom-ok zero (tyEdit-ok eA)) = refl
dropTyEdit-insert-type-raw (suc n) k m (ty-star s) = refl
dropTyEdit-insert-type-raw (suc n) k m (ty-X x∈) =
  cong ＇_ (dropVarFrom-rename-raise (suc n) k m x∈)
dropTyEdit-insert-type-raw (suc n) k m ty-｀ = refl
dropTyEdit-insert-type-raw (suc n) k m ty-‵ = refl
dropTyEdit-insert-type-raw (suc n) k m ty-★ = refl
dropTyEdit-insert-type-raw (suc n) k m (ty-⇒ eA eB)
  rewrite dropTyEdit-insert-type-raw (suc n) k m eA
        | dropTyEdit-insert-type-raw (suc n) k m eB = refl
dropTyEdit-insert-type-raw (suc n) k m {A = `∀ A} (ty-∀keep eA)
  rewrite rename-raise-ext (suc (n + suc k)) A
        | rename-raise-ext (suc (n + k))
            (dropTyFrom (suc (suc n)) (applyTyEdit-type eA))
        | dropTyEdit-insert-type-raw (suc (suc n)) k m eA = refl
dropTyEdit-insert-type-raw (suc n) k m {A = `∀ A} (ty-∀drop eA)
  rewrite rename-raise-ext (suc (n + suc k)) A
        | dropTargetFrom-raw zero
            (tyEdit-ok (insertTyEditAt (suc (suc (n + suc k))) m eA))
        | dropTyEdit-insert-type-raw zero (suc (n + suc k)) m eA
        | sym (dropTargetFrom-raw zero (tyEdit-ok eA))
        | dropTyFrom-rename-raise (suc n) k
            (dropTargetFrom-ok zero (tyEdit-ok eA)) = refl

dropTyEdit-insert-type :
  ∀ n k m {Φ A} →
  (e : TyEdit (extend-X⊑X n (X⊑★ ∷ Φ)) A) →
  dropTargetFrom n
    (subst (λ Γ′ → TargetOk Γ′
      (applyTyEdit-type (insertTyEditAt (n + suc k) m e)))
      (insertMode-extend-X⊑X n (suc k) m (X⊑★ ∷ Φ))
      (tyEdit-ok (insertTyEditAt (n + suc k) m e))) ≡
  renameᵗ (raiseVarFrom (n + k)) (dropTargetFrom n (tyEdit-ok e))
dropTyEdit-insert-type n k m {Φ = Φ} e
  rewrite dropTargetFrom-raw n
            (subst (λ Γ′ → TargetOk Γ′
              (applyTyEdit-type (insertTyEditAt (n + suc k) m e)))
              (insertMode-extend-X⊑X n (suc k) m (X⊑★ ∷ Φ))
              (tyEdit-ok (insertTyEditAt (n + suc k) m e)))
        | dropTargetFrom-raw n (tyEdit-ok e) =
  dropTyEdit-insert-type-raw n k m e

dropTyEdit-insert-type-zero :
  ∀ k m {Φ A} →
  (e : TyEdit (X⊑★ ∷ Φ) A) →
  dropTargetFrom zero (tyEdit-ok (insertTyEditAt (suc k) m e)) ≡
  renameᵗ (raiseVarFrom k) (dropTargetFrom zero (tyEdit-ok e))
dropTyEdit-insert-type-zero = dropTyEdit-insert-type zero

dropTargetTermFrom-eq :
  ∀ n {Φ M} →
  (okM : TargetTermOk (extend-X⊑X n (X⊑★ ∷ Φ)) M) →
  M ≡ renameᵗᴳ (raiseVarFrom n) (dropTargetTermFrom n okM)
dropTargetTermFrom-eq n tt-var = refl
dropTargetTermFrom-eq n (tt-lam okA okM) =
  cong₂ ƛ_⇒_ (dropTargetFrom-eq n okA) (dropTargetTermFrom-eq n okM)
dropTargetTermFrom-eq n (tt-app okL okM) =
  cong₂ _·_ (dropTargetTermFrom-eq n okL) (dropTargetTermFrom-eq n okM)
dropTargetTermFrom-eq n (tt-Lam okM) =
  cong Λ_
    (trans (dropTargetTermFrom-eq (suc n) okM)
      (sym (renameᵗᴳ-cong (raise-ext n) (dropTargetTermFrom (suc n) okM))))
dropTargetTermFrom-eq n (tt-tyapp okM okT) =
  cong₂ _`[_] (dropTargetTermFrom-eq n okM) (dropTargetFrom-eq n okT)
dropTargetTermFrom-eq n tt-const = refl
dropTargetTermFrom-eq n (tt-prim {op = op} okL okM) =
  cong₂ (λ L M → L ⊕[ op ] M)
    (dropTargetTermFrom-eq n okL) (dropTargetTermFrom-eq n okM)

applyTyEdit-insert-type :
  ∀ k m {Φ A} →
  (e : TyEdit Φ A) →
  applyTyEdit-type (insertTyEditAt k m e) ≡
  renameᵗ (raiseVarFrom k) (applyTyEdit-type e)
applyTyEdit-insert-type k m (ty-star s) = refl
applyTyEdit-insert-type k m (ty-X x∈) = refl
applyTyEdit-insert-type k m ty-｀ = refl
applyTyEdit-insert-type k m ty-‵ = refl
applyTyEdit-insert-type k m ty-★ = refl
applyTyEdit-insert-type k m (ty-⇒ eA eB)
  rewrite applyTyEdit-insert-type k m eA
        | applyTyEdit-insert-type k m eB = refl
applyTyEdit-insert-type k m {A = `∀ A} (ty-∀keep eA)
  rewrite rename-raise-ext k A
        | rename-raise-ext k (applyTyEdit-type eA)
        | applyTyEdit-insert-type (suc k) m eA = refl
applyTyEdit-insert-type k m {A = `∀ A} (ty-∀drop eA)
  rewrite rename-raise-ext k A
        | dropTyEdit-insert-type-zero k m eA = refl

applyTyEdit-lift-type :
  ∀ m {Φ A} →
  (e : TyEdit Φ A) →
  applyTyEdit-type (liftTyEdit m e) ≡ ⇑ᵗ (applyTyEdit-type e)
applyTyEdit-lift-type m e = applyTyEdit-insert-type zero m e

targetCtx-liftTyEditCtx :
  ∀ m {Φ} →
  (Γπ : TyEditCtx Φ) →
  targetCtx (liftTyEditCtx m Γπ) ≡ ⤊ᵗ (targetCtx Γπ)
targetCtx-liftTyEditCtx m [] = refl
targetCtx-liftTyEditCtx m ((A , e) ∷ Γπ) =
  cong₂ _∷_ (applyTyEdit-lift-type m e) (targetCtx-liftTyEditCtx m Γπ)

dropTargetTermFrom-wt :
  ∀ {Φ} {Γπ : TyEditCtx Φ} {M A}
    (okM : TargetTermOk (X⊑★ ∷ Φ) M)
    (okA : TargetOk (X⊑★ ∷ Φ) A) →
  length (X⊑★ ∷ Φ) ∣ targetCtx (liftTyEditCtx X⊑★ Γπ) ⊢ M ⦂ A →
  length Φ ∣ targetCtx Γπ ⊢
    dropTargetTermFrom zero okM ⦂ dropTargetFrom zero okA
dropTargetTermFrom-wt {Γπ = Γπ} okM okA M⊢
    with drop-renameᵗᴳ-wt
      (cong-⊢ᴳ⦂
        refl
        (targetCtx-liftTyEditCtx X⊑★ Γπ)
        (dropTargetTermFrom-eq zero okM)
        (dropTargetFrom-eq zero okA)
        M⊢)
dropTargetTermFrom-wt okM okA M⊢ | B , eqB , M′⊢ =
  subst (λ C → _ ∣ _ ⊢ dropTargetTermFrom zero okM ⦂ C)
    (sym (rename-raise-injective zero eqB))
    M′⊢

applyTermEdit-wt : ∀ {Φ Γπ M A} →
  CtxWf (length Φ) 0 (sourceCtx Γπ) →
  (ρ : TermEdit Φ Γπ M A) →
  TermEditOk Φ Γπ ρ →
  length Φ ∣ sourceCtx Γπ ⊢ M ⦂ A →
  ApplyTermEditWtResult Γπ M ρ
applyTermEdit-wt wfΓ (term-var {P = A , e} x∈) ok-var (⊢` y∈) =
  ⊢` (lookupTargetCtx x∈) , tyEdit-⊑ (wfΓ (lookupSourceCtx x∈)) e
applyTermEdit-wt wfΓ (term-lam πA ρM) (ok-lam okM) (⊢ƛ wfA M⊢)
    with tyEdit-⊑ wfA πA
       | applyTermEdit-wt (ctxWf-∷ wfA wfΓ) ρM okM M⊢
applyTermEdit-wt wfΓ (term-lam πA ρM) (ok-lam okM) (⊢ƛ wfA M⊢)
    | pA , pA⊢ | M′⊢ , pB , pB⊢ =
  ⊢ƛ (tyEdit-wf wfA πA) M′⊢ ,
  A⇒B-⊑-A′⇒B′ pA pB , ⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢
applyTermEdit-wt wfΓ (term-app ρL ρM) (ok-app okL okM) LM⊢
    with termApp-align wfΓ ρL ρM LM⊢
applyTermEdit-wt wfΓ (term-app ρL ρM) (ok-app okL okM) LM⊢
    | (L⊢ , M⊢) , A~A′
    with applyTermEdit-wt wfΓ ρL okL L⊢ | applyTermEdit-wt wfΓ ρM okM M⊢
applyTermEdit-wt wfΓ (term-app ρL ρM) (ok-app okL okM) LM⊢
    | (L⊢ , M⊢) , A~A′
    | L′⊢ , pF , pF⊢
    | M′⊢ , pArg , pArg⊢ =
  plannedApp-wt
    (applyTermEdit-term-ok _ _ ρL)
    (applyTermEdit-term-ok _ _ ρM)
    (applyTermEdit-type-ok _ _ ρL)
    L′⊢ pF⊢ M′⊢ pArg⊢ A~A′
applyTermEdit-wt wfΓ (term-app★ ρL ρM) (ok-app★ okL okM) LM⊢
    with termApp★-align wfΓ ρL ρM LM⊢
applyTermEdit-wt wfΓ (term-app★ ρL ρM) (ok-app★ okL okM) LM⊢
    | (L⊢ , M⊢) , A~★
    with applyTermEdit-wt wfΓ ρL okL L⊢ | applyTermEdit-wt wfΓ ρM okM M⊢
applyTermEdit-wt wfΓ (term-app★ ρL ρM) (ok-app★ okL okM) LM⊢
    | (L⊢ , M⊢) , A~★
    | L′⊢ , pF , pF⊢ | M′⊢ , pArg , pArg⊢ =
  starApp-wt
    (applyTermEdit-type-ok _ _ ρL)
    L′⊢ pF⊢ M′⊢ pArg⊢ A~★ ,
  ★-⊑-★ , ⊢★-⊑-★
applyTermEdit-wt {Γπ = Γπ} wfΓ (term-LamKeep {M = M} ρM)
    (ok-LamKeep okM) (⊢Λ vM M⊢)
    with applyTermEdit (liftTyEditCtx X⊑X Γπ) M ρM
       | applyTermEdit-wt
          (sourceCtxWf-liftTyEditCtx X⊑X wfΓ)
          ρM
          okM
          (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
            (sym (sourceCtx-liftTyEditCtx X⊑X Γπ)) M⊢)
       | applyTermEdit-value
          (sourceCtxWf-liftTyEditCtx X⊑X wfΓ)
          ρM
          okM
          (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
            (sym (sourceCtx-liftTyEditCtx X⊑X Γπ)) M⊢)
          vM
applyTermEdit-wt {Γπ = Γπ} wfΓ (term-LamKeep ρM)
    (ok-LamKeep okM) (⊢Λ vM M⊢)
    | M′ , B′ , okM′ , okB′ | M′⊢ , pB , pB⊢ | vM′ =
  ⊢Λ
    vM′
    (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
    (targetCtx-liftTyEditCtx X⊑X Γπ) M′⊢) ,
  ∀A-⊑-∀B pB , ⊢∀A-⊑-∀B pB⊢
applyTermEdit-wt {Γπ = Γπ} wfΓ (term-LamDrop {M = M} ρM)
    (ok-LamDrop okM) (⊢Λ vM M⊢)
    with applyTermEdit (liftTyEditCtx X⊑★ Γπ) M ρM
       | applyTermEdit-wt
          (sourceCtxWf-liftTyEditCtx X⊑★ wfΓ)
          ρM
          okM
          (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _)
            (sym (sourceCtx-liftTyEditCtx X⊑★ Γπ)) M⊢)
applyTermEdit-wt {Γπ = Γπ} wfΓ (term-LamDrop ρM)
    (ok-LamDrop okM) (⊢Λ vM M⊢)
    | M′ , B′ , okM′ , okB′ | M′⊢ , pB , pB⊢ =
  dropTargetTermFrom-wt okM′ okB′ M′⊢ ,
  ∀A-⊑-B (dropTargetFrom zero okB′) pB ,
  ⊢∀A-⊑-B
    (dropTargetFrom-WfTy zero (⊑-tgt-wf pB⊢) okB′)
    (subst (λ C → _ ∣ _ ⊢ pB ⦂ _ ⊑ C)
      (dropTargetFrom-eq zero okB′) pB⊢)
applyTermEdit-wt {Γπ = Γπ} wfΓ (term-tyappKeep {M = M} ρM πT)
    (ok-tyapp-keep okM eq wfB′ q⊢) MT⊢
    with termTyApp∀-align wfΓ ρM πT MT⊢
applyTermEdit-wt {Γπ = Γπ} wfΓ (term-tyappKeep {M = M} ρM πT)
    (ok-tyapp-keep okM eq wfB′ q⊢) MT⊢
    | M⊢ , wfB , wfT
    with applyTermEdit Γπ M ρM | eq
       | applyTermEdit-wt wfΓ ρM okM M⊢
applyTermEdit-wt {Γπ = Γπ} wfΓ (term-tyappKeep {M = M} ρM πT)
    (ok-tyapp-keep okM eq wfB′ q⊢) MT⊢
    | M⊢ , wfB , wfT
    | M′ , `∀ B′ , okM′ , ok-∀ okB′ | refl
    | M′⊢ , pM , pM⊢ =
  ⊢• M′⊢ wfB′ (tyEdit-wf wfT πT) , _ , q⊢
applyTermEdit-wt {Γπ = Γπ} wfΓ (term-tyappDrop {M = M} ρM πT)
    (ok-tyapp-drop okM q⊢) MT⊢
    with termTyApp∀-align wfΓ ρM πT MT⊢
applyTermEdit-wt {Γπ = Γπ} wfΓ (term-tyappDrop {M = M} ρM πT)
    (ok-tyapp-drop okM q⊢) MT⊢
    | M⊢ , wfB , wfT
    with applyTermEdit Γπ M ρM
       | applyTermEdit-wt wfΓ ρM okM M⊢
applyTermEdit-wt {Γπ = Γπ} wfΓ (term-tyappDrop {M = M} ρM πT)
    (ok-tyapp-drop okM q⊢) MT⊢
    | M⊢ , wfB , wfT
    | M′ , A′ , okM′ , okA′ | M′⊢ , pM , pM⊢ =
  M′⊢ , _ , q⊢
applyTermEdit-wt wfΓ term-const ok-const (⊢$ (κℕ n)) =
  ⊢$ (κℕ n) , ι-⊑-ι `ℕ , ⊢ι-⊑-ι
applyTermEdit-wt wfΓ (term-prim ρL ρM) (ok-prim okL okM)
    (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with termEdit-source-typed wfΓ ρL L⊢
       | termEdit-source-typed wfΓ ρM M⊢
applyTermEdit-wt wfΓ (term-prim ρL ρM) (ok-prim okL okM)
    (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L⊢′ | M⊢′
    with type-uniqueᴳ L⊢ L⊢′ | type-uniqueᴳ M⊢ M⊢′
applyTermEdit-wt wfΓ (term-prim ρL ρM) (ok-prim okL okM)
    (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L⊢′ | M⊢′ | refl | refl
    with applyTermEdit-wt wfΓ ρL okL L⊢′
       | applyTermEdit-wt wfΓ ρM okM M⊢′
applyTermEdit-wt wfΓ (term-prim ρL ρM) (ok-prim okL okM)
    (⊢⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L⊢′ | M⊢′ | refl | refl
    | L′⊢ , pL , pL⊢ | M′⊢ , pM , pM⊢ =
  ⊢⊕ L′⊢ (app-consistencyᵢ refl pL⊢ A~ℕ ⊢ι-⊑-ι)
    op M′⊢ (app-consistencyᵢ refl pM⊢ B~ℕ ⊢ι-⊑-ι) ,
  ι-⊑-ι `ℕ , ⊢ι-⊑-ι
