module strong.proof.Canonical where

-- Strong System F v8 — canonical forms, and the SHAPE facts the views
-- carry: a conversion the views accept has no renaming elements, so its
-- source has the same shape as its target.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.Terms

private
  variable
    Sg : Store
    Δ Δᵢ : Ctxᵗ
    Γ : Ctx
    A B A₀ : Ty
    c s t : Conv
    ĉ : ConvElt
    V : Term

------------------------------------------------------------------------
-- A typed conversion's target is its syntactic target
------------------------------------------------------------------------

conv-target : Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → target c ≡ B
conv-target (conv-id wf) = refl
conv-target (conv-cons hd tl) = conv-target tl

------------------------------------------------------------------------
-- Type shapes
------------------------------------------------------------------------

data FunShape : Ty → Set where
  fun-shape : ∀ A B → FunShape (A ⇒ B)

data AllShape : Ty → Set where
  all-shape : ∀ A → AllShape (`∀ A)

data GroundShape : Ty → Set where
  ground-ℕ : GroundShape `ℕ
  ground-𝔹 : GroundShape `𝔹

-- An identity crossing preserves shape: it relates A to `shiftAtᵗ X A`.
shift-fun : ∀ X A → FunShape (renameᵗ (shiftAtᵗ X) A) → FunShape A
shift-fun X (` Y) ()
shift-fun X `ℕ ()
shift-fun X `𝔹 ()
shift-fun X (A ⇒ B) _ = fun-shape A B
shift-fun X (`∀ A) ()

shift-all : ∀ X A → AllShape (renameᵗ (shiftAtᵗ X) A) → AllShape A
shift-all X (` Y) ()
shift-all X `ℕ ()
shift-all X `𝔹 ()
shift-all X (A ⇒ B) ()
shift-all X (`∀ A) _ = all-shape A

shift-ground : ∀ X A → GroundShape (renameᵗ (shiftAtᵗ X) A) → GroundShape A
shift-ground X (` Y) ()
shift-ground X `ℕ _ = ground-ℕ
shift-ground X `𝔹 _ = ground-𝔹
shift-ground X (A ⇒ B) ()
shift-ground X (`∀ A) ()

------------------------------------------------------------------------
-- The views determine the target's shape
------------------------------------------------------------------------

arr-target : ∀ {A₀ p c} → arr A₀ c ≡ just p → FunShape (target c)
arr-target {A₀ = A₀} {c = c} eq with arrElts (elts c) | target c
arr-target {A₀ = A₀} {c = c} eq | just q | C ⇒ D = fun-shape C D
arr-target {A₀ = A₀} {c = c} () | just q | ` X
arr-target {A₀ = A₀} {c = c} () | just q | `ℕ
arr-target {A₀ = A₀} {c = c} () | just q | `𝔹
arr-target {A₀ = A₀} {c = c} () | just q | `∀ B
arr-target {A₀ = A₀} {c = c} () | nothing | _

allView-target : ∀ {d c} → allView c ≡ just d → AllShape (target c)
allView-target {c = c} eq with allElts (elts c) | target c
allView-target {c = c} eq | just q | `∀ B = all-shape B
allView-target {c = c} () | just q | ` X
allView-target {c = c} () | just q | `ℕ
allView-target {c = c} () | just q | `𝔹
allView-target {c = c} () | just q | C ⇒ D
allView-target {c = c} () | nothing | _

-- `arr` succeeds on the SHAPE alone; the domain only lands in the
-- output, so success at one domain is success at any.
arr-any : ∀ {A′ p c} (A₀ : Ty) → arr A′ c ≡ just p
  → Σ[ c₁ ∈ Conv ] Σ[ c₂ ∈ Conv ] (arr A₀ c ≡ just (c₁ , c₂))
arr-any {A′ = A′} {c = c} A₀ eq with arrElts (elts c) | target c
arr-any {A′ = A′} {c = c} A₀ eq | just (Ls , Rs) | C ⇒ D = _ , _ , refl
arr-any {A′ = A′} {c = c} A₀ () | just p | ` X
arr-any {A′ = A′} {c = c} A₀ () | just p | `ℕ
arr-any {A′ = A′} {c = c} A₀ () | just p | `𝔹
arr-any {A′ = A′} {c = c} A₀ () | just p | `∀ B
arr-any {A′ = A′} {c = c} A₀ () | nothing | _

-- A conversion the views accept has no RENAMING element at its head:
-- `arr⁻`/`all⁺` are undefined there, and the fold propagates.
headArr : Conv → Set
headArr (id A) = ⊤
headArr (seal X α ∷ᶜ c) = ⊥
headArr (unseal X α ∷ᶜ c) = ⊥
headArr (hide X α ∷ᶜ c) = ⊤
headArr (show X α ∷ᶜ c) = ⊤
headArr ((s ↦ t) ∷ᶜ c) = ⊤
headArr (all s ∷ᶜ c) = ⊥

arr-headArr : ∀ {A₀ p} (c : Conv) → arr A₀ c ≡ just p → headArr c
arr-headArr (id A) eq = tt
arr-headArr (seal X α ∷ᶜ c) ()
arr-headArr (unseal X α ∷ᶜ c) ()
arr-headArr (hide X α ∷ᶜ c) eq = tt
arr-headArr (show X α ∷ᶜ c) eq = tt
arr-headArr ((s ↦ t) ∷ᶜ c) eq = tt
arr-headArr (all s ∷ᶜ c) ()

headAll : Conv → Set
headAll (id A) = ⊤
headAll (seal X α ∷ᶜ c) = ⊥
headAll (unseal X α ∷ᶜ c) = ⊥
headAll (hide X α ∷ᶜ c) = ⊤
headAll (show X α ∷ᶜ c) = ⊤
headAll ((s ↦ t) ∷ᶜ c) = ⊥
headAll (all s ∷ᶜ c) = ⊤

allView-headAll : ∀ {d} (c : Conv) → allView c ≡ just d → headAll c
allView-headAll (id A) eq = tt
allView-headAll (seal X α ∷ᶜ c) ()
allView-headAll (unseal X α ∷ᶜ c) ()
allView-headAll (hide X α ∷ᶜ c) eq = tt
allView-headAll (show X α ∷ᶜ c) eq = tt
allView-headAll ((s ↦ t) ∷ᶜ c) ()
allView-headAll (all s ∷ᶜ c) eq = tt

------------------------------------------------------------------------
-- Applicable at a given target shape
------------------------------------------------------------------------

-- Shapes are mutually exclusive.
fun-not-all : FunShape A → AllShape A → ⊥
fun-not-all (fun-shape _ _) ()

fun-not-ground : FunShape A → GroundShape A → ⊥
fun-not-ground (fun-shape _ _) ()

all-not-ground : AllShape A → GroundShape A → ⊥
all-not-ground (all-shape _) ()

var-not-fun : ∀ {X} → FunShape (` X) → ⊥
var-not-fun ()

var-not-all : ∀ {X} → AllShape (` X) → ⊥
var-not-all ()

var-not-ground : ∀ {X} → GroundShape (` X) → ⊥
var-not-ground ()

applicable-arr : ∀ {c} → Applicable c → FunShape (target c)
  → ∀ A₀ → Σ[ c₁ ∈ Conv ] Σ[ c₂ ∈ Conv ] (arr A₀ c ≡ just (c₁ , c₂))
applicable-arr {c = c} (applies-arr A′ eq) sh A₀ = arr-any {c = c} A₀ eq
applicable-arr {c = c} (applies-all eq) sh A₀ =
  ⊥-elim (fun-not-all sh (allView-target {c = c} eq))
applicable-arr {c = c} (applies-var veq) sh A₀ =
  ⊥-elim (var-not-fun (subst FunShape veq sh))

applicable-all : ∀ {c} → Applicable c → AllShape (target c)
  → Σ[ d ∈ Conv ] (allView c ≡ just d)
applicable-all {c = c} (applies-arr A′ eq) sh =
  ⊥-elim (fun-not-all (arr-target {c = c} eq) sh)
applicable-all (applies-all eq) sh = _ , eq
applicable-all {c = c} (applies-var veq) sh =
  ⊥-elim (var-not-all (subst AllShape veq sh))

applicable-ground : ∀ {c} → Applicable c → GroundShape (target c) → ⊥
applicable-ground {c = c} (applies-arr A′ eq) sh =
  fun-not-ground (arr-target {c = c} eq) sh
applicable-ground {c = c} (applies-all eq) sh =
  all-not-ground (allView-target {c = c} eq) sh
applicable-ground {c = c} (applies-var veq) sh =
  var-not-ground (subst GroundShape veq sh)

------------------------------------------------------------------------
-- Simple values: their types are never type variables
------------------------------------------------------------------------

simple-fun : Simple V → Sg ∣ Δ ∣ [] ⊢ V ⦂ A → FunShape A
  → Σ[ A₁ ∈ Ty ] Σ[ N ∈ Term ] (V ≡ ƛ A₁ ∙ N)
simple-fun S$ ⊢$ ()
simple-fun S# ⊢# ()
simple-fun Sƛ (⊢ƛ wf body) (fun-shape A B) = _ , _ , refl
simple-fun (SΛ v) (⊢Λ _ body) ()

simple-all : Simple V → Sg ∣ Δ ∣ [] ⊢ V ⦂ A → AllShape A
  → Σ[ W ∈ Term ] (Value W × (V ≡ Λ W))
simple-all S$ ⊢$ ()
simple-all S# ⊢# ()
simple-all Sƛ (⊢ƛ wf body) ()
simple-all (SΛ v) (⊢Λ _ body) (all-shape A) = _ , v , refl

simple-ℕ : Simple V → Sg ∣ Δ ∣ [] ⊢ V ⦂ `ℕ → Σ[ n ∈ ℕ ] (V ≡ $ n)
simple-ℕ S$ ⊢$ = _ , refl
simple-ℕ S# ()
simple-ℕ Sƛ ()
simple-ℕ (SΛ v) ()

------------------------------------------------------------------------
-- Canonical forms for values at each type shape
------------------------------------------------------------------------

canonical-ℕ : Value V → Sg ∣ Δ ∣ Γ ⊢ V ⦂ `ℕ
  → (Σ[ n ∈ ℕ ] (V ≡ $ n))
    ⊎ (Σ[ W ∈ Term ] Σ[ c ∈ Conv ] (V ≡ W ⟨ c ⟩))
canonical-ℕ (Vs S$) ⊢$ = inj₁ (_ , refl)
canonical-ℕ (Vs S#) ()
canonical-ℕ (Vs Sƛ) ()
canonical-ℕ (Vs (SΛ v)) ()
canonical-ℕ (V⟨⟩ simple nf app) ⊢V = inj₂ (_ , _ , refl)

------------------------------------------------------------------------
-- The SOURCE shape: a conversion the views accept preserves shape,
-- because only the renaming elements change it
------------------------------------------------------------------------

fun-shift : ∀ X A → FunShape A → FunShape (renameᵗ (shiftAtᵗ X) A)
fun-shift X (A ⇒ B) (fun-shape _ _) = fun-shape _ _

all-shift : ∀ X A → AllShape A → AllShape (renameᵗ (shiftAtᵗ X) A)
all-shift X (`∀ A) (all-shape _) = all-shape _

arr-tail-hide : ∀ {A₀ p X α} (c : Conv) → arr A₀ (hide X α ∷ᶜ c) ≡ just p
  → Σ[ q ∈ Conv × Conv ] (arr A₀ c ≡ just q)
arr-tail-hide c eq with arrElts (elts c) | target c
arr-tail-hide c eq | just q | C ⇒ D = _ , refl
arr-tail-hide c () | just q | ` X
arr-tail-hide c () | just q | `ℕ
arr-tail-hide c () | just q | `𝔹
arr-tail-hide c () | just q | `∀ B
arr-tail-hide c () | nothing | _

arr-tail-show : ∀ {A₀ p X α} (c : Conv) → arr A₀ (show X α ∷ᶜ c) ≡ just p
  → Σ[ q ∈ Conv × Conv ] (arr A₀ c ≡ just q)
arr-tail-show c eq with arrElts (elts c) | target c
arr-tail-show c eq | just q | C ⇒ D = _ , refl
arr-tail-show c () | just q | ` X
arr-tail-show c () | just q | `ℕ
arr-tail-show c () | just q | `𝔹
arr-tail-show c () | just q | `∀ B
arr-tail-show c () | nothing | _

allView-tail-hide : ∀ {d X α} (c : Conv) → allView (hide X α ∷ᶜ c) ≡ just d
  → Σ[ e ∈ Conv ] (allView c ≡ just e)
allView-tail-hide c eq with allElts (elts c) | target c
allView-tail-hide c eq | just q | `∀ B = _ , refl
allView-tail-hide c () | just q | ` X
allView-tail-hide c () | just q | `ℕ
allView-tail-hide c () | just q | `𝔹
allView-tail-hide c () | just q | C ⇒ D
allView-tail-hide c () | nothing | _

allView-tail-show : ∀ {d X α} (c : Conv) → allView (show X α ∷ᶜ c) ≡ just d
  → Σ[ e ∈ Conv ] (allView c ≡ just e)
allView-tail-show c eq with allElts (elts c) | target c
allView-tail-show c eq | just q | `∀ B = _ , refl
allView-tail-show c () | just q | ` X
allView-tail-show c () | just q | `ℕ
allView-tail-show c () | just q | `𝔹
allView-tail-show c () | just q | C ⇒ D
allView-tail-show c () | nothing | _

conv-fun-source : ∀ {Sg Δᵢ Δ c A B A₀ p}
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → arr A₀ c ≡ just p → FunShape A
conv-fun-source {c = id A} (conv-id wf) eq = arr-target {c = id A} eq
conv-fun-source (conv-cons (conv-seal r rd p) tl) ()
conv-fun-source (conv-cons (conv-unseal r rd p) tl) ()
conv-fun-source (conv-cons (conv-all s) tl) ()
conv-fun-source {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl) eq
  with arr-tail-hide c eq
conv-fun-source {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl) eq
  | _ , eq′ = shift-fun X A (conv-fun-source tl eq′)
conv-fun-source {c = show X α ∷ᶜ c} (conv-cons (conv-show wf p) tl) eq
  with arr-tail-show c eq
conv-fun-source {c = show X α ∷ᶜ c} (conv-cons (conv-show wf p) tl) eq
  | _ , eq′ = fun-shift X _ (conv-fun-source tl eq′)
conv-fun-source (conv-cons (conv-fun s t) tl) eq = fun-shape _ _

conv-all-source : ∀ {Sg Δᵢ Δ c A B d}
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → allView c ≡ just d → AllShape A
conv-all-source {c = id A} (conv-id wf) eq = allView-target {c = id A} eq
conv-all-source (conv-cons (conv-seal r rd p) tl) ()
conv-all-source (conv-cons (conv-unseal r rd p) tl) ()
conv-all-source (conv-cons (conv-fun s t) tl) ()
conv-all-source {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl) eq
  with allView-tail-hide c eq
conv-all-source {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl) eq
  | _ , eq′ = shift-all X A (conv-all-source tl eq′)
conv-all-source {c = show X α ∷ᶜ c} (conv-cons (conv-show wf p) tl) eq
  with allView-tail-show c eq
conv-all-source {c = show X α ∷ᶜ c} (conv-cons (conv-show wf p) tl) eq
  | _ , eq′ = all-shift X _ (conv-all-source tl eq′)
conv-all-source (conv-cons (conv-all s) tl) eq = all-shape _

------------------------------------------------------------------------
-- Canonical forms at arrow and universal type
------------------------------------------------------------------------

canonical-⇒ : ∀ {Sg Δ L A B} → Value L → Sg ∣ Δ ∣ [] ⊢ L ⦂ A ⇒ B
  → (Σ[ A₁ ∈ Ty ] Σ[ N ∈ Term ] (L ≡ ƛ A₁ ∙ N))
    ⊎ (Σ[ A₁ ∈ Ty ] Σ[ N ∈ Term ] Σ[ c ∈ Conv ]
       Σ[ c₁ ∈ Conv ] Σ[ c₂ ∈ Conv ]
       ((L ≡ (ƛ A₁ ∙ N) ⟨ c ⟩) × (arr A₁ c ≡ just (c₁ , c₂))))
canonical-⇒ (Vs simple) ⊢L = inj₁ (simple-fun simple ⊢L (fun-shape _ _))
canonical-⇒ {A = A} {B = B} (V⟨⟩ {c = c} simple nf app) (⊢⟨⟩ nf′ ⊢W conv)
  with applicable-arr {c = c} app
         (subst FunShape (sym (conv-target conv)) (fun-shape A B)) `ℕ
canonical-⇒ {A = A} {B = B} (V⟨⟩ {c = c} simple nf app) (⊢⟨⟩ nf′ ⊢W conv)
  | _ , _ , probe with simple-fun simple ⊢W (conv-fun-source conv probe)
canonical-⇒ {A = A} {B = B} (V⟨⟩ {c = c} simple nf app) (⊢⟨⟩ nf′ ⊢W conv)
  | _ , _ , probe | A₁ , N , refl with arr-any {c = c} A₁ probe
canonical-⇒ {A = A} {B = B} (V⟨⟩ {c = c} simple nf app) (⊢⟨⟩ nf′ ⊢W conv)
  | _ , _ , probe | A₁ , N , refl | c₁ , c₂ , arr-eq =
  inj₂ (A₁ , N , _ , c₁ , c₂ , refl , arr-eq)

canonical-∀ : ∀ {Sg Δ L B} → Value L → Sg ∣ Δ ∣ [] ⊢ L ⦂ `∀ B
  → (Σ[ V ∈ Term ] (Value V × (L ≡ Λ V)))
    ⊎ (Σ[ V ∈ Term ] Σ[ c ∈ Conv ] Σ[ d ∈ Conv ]
       ((L ≡ (Λ V) ⟨ c ⟩) × (allView c ≡ just d)))
canonical-∀ (Vs simple) ⊢L = inj₁ (simple-all simple ⊢L (all-shape _))
canonical-∀ {B = B} (V⟨⟩ {c = c} simple nf app) (⊢⟨⟩ nf′ ⊢V conv)
  with applicable-all {c = c} app
         (subst AllShape (sym (conv-target conv)) (all-shape B))
canonical-∀ {B = B} (V⟨⟩ {c = c} simple nf app) (⊢⟨⟩ nf′ ⊢V conv) | d , all-eq
  with simple-all simple ⊢V (conv-all-source conv all-eq)
canonical-∀ {B = B} (V⟨⟩ {c = c} simple nf app) (⊢⟨⟩ nf′ ⊢V conv) | d , all-eq
  | V , v , refl = inj₂ (V , c , d , refl , all-eq)
