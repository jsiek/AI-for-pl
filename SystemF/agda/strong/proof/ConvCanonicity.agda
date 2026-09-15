module strong.proof.ConvCanonicity where

-- Strong System F v8 — CONVERSION CANONICITY: at a boundary over a
-- simple value, the conversion is INERT or the body is a literal the
-- `base` view sees through.  This discharges the parameter of
-- `proof.Progress`.
--
-- The argument has two halves.
--
--  * AFTER AN ADDITION (`after-add`).  A `seal` or a `hide` ADDS the
--    newest crossing assignment, and the running type is then a type
--    VARIABLE.  From there the target stays a variable: an element
--    that REMOVES an assignment (`unseal`, `show`) is forced by
--    pop-determinism to the address the adder just created, so either
--    it fuses with the adder — contradicting `NF` — or the running
--    name and the popped name disagree, because `shiftAtᵗ X′ X` is
--    never `X′`.  A `↦` or `all` cannot follow at all: their sources
--    are arrows and universals, not variables.
--
--  * SHAPE PRESERVATION.  From a NON-variable source — and a simple
--    value's type is never a variable — the crossings and the
--    structural elements preserve the type's shape, so the matching
--    view is defined; the only escape is a `seal`, which lands in the
--    first half and yields `inert-var`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.proof.Canonical

private
  variable
    Sg : Store
    Γ Γ′ Γ″ Δ Δᵢ : Ctxᵗ
    A B : Ty
    X Y r : ℕ
    α β : Addr
    c s t : Conv
    ĉ : ConvElt

------------------------------------------------------------------------
-- The shift never lands on its own cutoff
------------------------------------------------------------------------

shiftAt-≢ : ∀ X′ X → shiftAtᵗ X′ X ≢ X′
shiftAt-≢ zero X ()
shiftAt-≢ (suc X′) zero ()
shiftAt-≢ (suc X′) (suc X) eq = shiftAt-≢ X′ X (suc-inj eq)
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

-- … and so a variable type is never its own shift.
shiftAt-var-≢ : ∀ X′ A → renameᵗ (shiftAtᵗ X′) A ≢ ` X′
shiftAt-var-≢ X′ (` X) eq = shiftAt-≢ X′ X (var-inj eq)
  where
  var-inj : ∀ {m n} → (` m) ≡ (` n) → m ≡ n
  var-inj refl = refl
shiftAt-var-≢ X′ `ℕ ()
shiftAt-var-≢ X′ `𝔹 ()
shiftAt-var-≢ X′ (A ⇒ B) ()
shiftAt-var-≢ X′ (`∀ A) ()

------------------------------------------------------------------------
-- The pop judgment is deterministic
------------------------------------------------------------------------

pop-unique : Γ ▷ X := α ⇒ Γ′ → Γ ▷ Y := β ⇒ Γ″
  → (X ≡ Y) × (α ≡ β) × (Γ′ ≡ Γ″)
pop-unique pop-here pop-here = refl , refl , refl
pop-unique (pop-bind-b p) (pop-bind-b q) with pop-unique p q
pop-unique (pop-bind-b p) (pop-bind-b q) | refl , refl , refl =
  refl , refl , refl
pop-unique (pop-bind-l p) (pop-bind-l q) with pop-unique p q
pop-unique (pop-bind-l p) (pop-bind-l q) | refl , refl , refl =
  refl , refl , refl
pop-unique (pop-bind-b p) (pop-bind-l q) with pop-unique p q
pop-unique (pop-bind-b p) (pop-bind-l q) | refl , () , _
pop-unique (pop-bind-l p) (pop-bind-b q) with pop-unique p q
pop-unique (pop-bind-l p) (pop-bind-b q) | refl , () , _

------------------------------------------------------------------------
-- After an addition: the running type is a variable, and stays one
------------------------------------------------------------------------

-- `AfterAdd Γ r ĉ` — the previous element ĉ ADDED the newest crossing
-- assignment of Γ, and the running type is `` ` r ``: equal to the new
-- name when the adder was a seal (which renames to it), different from
-- it when the adder was a hide (which only shifts).
data AfterAdd (Γ : Ctxᵗ) (r : ℕ) : ConvElt → Set where
  aa-seal : ∀ {X α Γ′} → Γ ▷ X := α ⇒ Γ′ → r ≡ X → AfterAdd Γ r (seal X α)
  aa-hide : ∀ {X α Γ′} → Γ ▷ X := α ⇒ Γ′ → r ≢ X → AfterAdd Γ r (hide X α)

-- fusing a pair at one address
fuse-su : ∀ X Y α → fuse (seal X α) (unseal Y α) ≡ nothing → ⊥
fuse-su X Y α eq with α ≟ᵃ α
fuse-su X Y α () | yes _
fuse-su X Y α eq | no ne = ne refl

fuse-hs : ∀ X Y α → fuse (hide X α) (show Y α) ≡ nothing → ⊥
fuse-hs X Y α eq with α ≟ᵃ α
fuse-hs X Y α () | yes _
fuse-hs X Y α eq | no ne = ne refl

-- The source is carried as an EQUATION rather than as an index: the
-- crossing rules state their source as a rename, which the unifier
-- cannot match against a variable.
var≢⇒ : ∀ {A B X} → (A ⇒ B) ≢ ` X
var≢⇒ ()

var≢∀ : ∀ {A X} → (`∀ A) ≢ ` X
var≢∀ ()

after-add : AfterAdd Γ r ĉ
  → Sg ∣ Γ ⊢ c ∶ A ⇝ B ⊣ Δ → A ≡ ` r → NF c → IrreducibleAfter ĉ c
  → Σ[ Y ∈ ℕ ] (B ≡ ` Y)
after-add aa (conv-id wf) refl nf irr = _ , refl

-- an unseal REMOVES: pop-determinism forces its address
after-add (aa-seal {X = X₁} {α = α₁} p refl)
  (conv-cons (conv-unseal {X = Y₁} rep rd q) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) with pop-unique q p
after-add (aa-seal {X = X₁} {α = α₁} p refl)
  (conv-cons (conv-unseal {X = Y₁} rep rd q) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) | refl , refl , refl =
  ⊥-elim (fuse-su X₁ Y₁ α₁ fq)
after-add (aa-hide p ne) (conv-cons (conv-unseal rep rd q) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) with pop-unique q p
after-add (aa-hide p ne) (conv-cons (conv-unseal rep rd q) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) | refl , refl , refl = ⊥-elim (ne refl)

-- a show REMOVES: blocked by `fuse` after a hide, and by the shift
-- arithmetic after a seal
after-add (aa-seal p refl) (conv-cons (conv-show {A = A} wf q) tl) eq
  (nf-cons nfe nfc irr′) (irr-cons fq) with pop-unique q p
after-add (aa-seal p refl) (conv-cons (conv-show {A = A} wf q) tl) eq
  (nf-cons nfe nfc irr′) (irr-cons fq) | refl , refl , refl =
  ⊥-elim (shiftAt-var-≢ _ A eq)
after-add (aa-hide {X = X₁} {α = α₁} p ne)
  (conv-cons (conv-show {X = Y₁} wf q) tl) eq
  (nf-cons nfe nfc irr′) (irr-cons fq) with pop-unique q p
after-add (aa-hide {X = X₁} {α = α₁} p ne)
  (conv-cons (conv-show {X = Y₁} wf q) tl) eq
  (nf-cons nfe nfc irr′) (irr-cons fq) | refl , refl , refl =
  ⊥-elim (fuse-hs X₁ Y₁ α₁ fq)

-- an ADDITION keeps us in the same situation
after-add aa (conv-cons (conv-seal rep rd q) tl) eq
  (nf-cons nfe nfc irr′) (irr-cons fq) =
  after-add (aa-seal q refl) tl refl nfc irr′
after-add aa (conv-cons (conv-hide {A = A} wf a q) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) =
  after-add (aa-hide q (shiftAt-≢ _ _)) tl refl nfc irr′

-- a structural element needs an arrow or a universal source
after-add aa (conv-cons (conv-fun s′ t′) tl) eq nf irr =
  ⊥-elim (var≢⇒ eq)
after-add aa (conv-cons (conv-all s′) tl) eq nf irr =
  ⊥-elim (var≢∀ eq)

------------------------------------------------------------------------
-- Shape preservation: from a non-variable source, the views are defined
------------------------------------------------------------------------

ground-shift : ∀ X A → GroundShape A → GroundShape (renameᵗ (shiftAtᵗ X) A)
ground-shift X `ℕ ground-ℕ = ground-ℕ
ground-shift X `𝔹 ground-𝔹 = ground-𝔹

-- The fold's step for the three elements the views accept.
lift-arr-hide : ∀ {X α q} (ĉs : List ConvElt) → arrElts ĉs ≡ just q
  → Σ[ q′ ∈ List ConvElt × List ConvElt ]
      (arrElts (hide X α ∷ ĉs) ≡ just q′)
lift-arr-hide ĉs eq rewrite eq = _ , refl

lift-arr-show : ∀ {X α q} (ĉs : List ConvElt) → arrElts ĉs ≡ just q
  → Σ[ q′ ∈ List ConvElt × List ConvElt ]
      (arrElts (show X α ∷ ĉs) ≡ just q′)
lift-arr-show ĉs eq rewrite eq = _ , refl

lift-arr-fun : ∀ {s t q} (ĉs : List ConvElt) → arrElts ĉs ≡ just q
  → Σ[ q′ ∈ List ConvElt × List ConvElt ]
      (arrElts ((s ↦ t) ∷ ĉs) ≡ just q′)
lift-arr-fun ĉs eq rewrite eq = _ , refl

lift-all-hide : ∀ {X α q} (ĉs : List ConvElt) → allElts ĉs ≡ just q
  → Σ[ q′ ∈ List ConvElt ] (allElts (hide X α ∷ ĉs) ≡ just q′)
lift-all-hide ĉs eq rewrite eq = _ , refl

lift-all-show : ∀ {X α q} (ĉs : List ConvElt) → allElts ĉs ≡ just q
  → Σ[ q′ ∈ List ConvElt ] (allElts (show X α ∷ ĉs) ≡ just q′)
lift-all-show ĉs eq rewrite eq = _ , refl

lift-all-all : ∀ {s q} (ĉs : List ConvElt) → allElts ĉs ≡ just q
  → Σ[ q′ ∈ List ConvElt ] (allElts (all s ∷ ĉs) ≡ just q′)
lift-all-all ĉs eq rewrite eq = _ , refl

-- From an ARROW source: either a seal sent the target to a variable, or
-- `arrElts` is defined and the target is an arrow too.
canon-fun : Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → NF c → FunShape A
  → (Σ[ Y ∈ ℕ ] (B ≡ ` Y))
    ⊎ (Σ[ q ∈ List ConvElt × List ConvElt ]
         ((arrElts (elts c) ≡ just q) × FunShape B))
canon-fun (conv-id wf) nf sh = inj₂ (_ , refl , sh)
canon-fun (conv-cons (conv-seal rep rd p) tl) (nf-cons nfe nfc irr) sh
  with after-add (aa-seal p refl) tl refl nfc irr
canon-fun (conv-cons (conv-seal rep rd p) tl) (nf-cons nfe nfc irr) sh
  | Y , eq = inj₁ (Y , eq)
canon-fun (conv-cons (conv-unseal rep rd p) tl) nf ()
canon-fun (conv-cons (conv-all s′) tl) nf ()
canon-fun {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl)
  (nf-cons nfe nfc irr) sh with canon-fun tl nfc (fun-shift X A sh)
canon-fun {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-fun {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-arr-hide {X = X} {α = α} (elts c) eqE
canon-fun {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)
canon-fun {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p) tl)
  (nf-cons nfe nfc irr) sh with canon-fun tl nfc (shift-fun X A sh)
canon-fun {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-fun {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-arr-show {X = X} {α = α} (elts c) eqE
canon-fun {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)
canon-fun {c = (s′ ↦ t′) ∷ᶜ c} (conv-cons (conv-fun s″ t″) tl)
  (nf-cons nfe nfc irr) sh with canon-fun tl nfc (fun-shape _ _)
canon-fun {c = (s′ ↦ t′) ∷ᶜ c} (conv-cons (conv-fun s″ t″) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-fun {c = (s′ ↦ t′) ∷ᶜ c} (conv-cons (conv-fun s″ t″) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-arr-fun {s = s′} {t = t′} (elts c) eqE
canon-fun {c = (s′ ↦ t′) ∷ᶜ c} (conv-cons (conv-fun s″ t″) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)

-- From a UNIVERSAL source, symmetrically.
canon-all : Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → NF c → AllShape A
  → (Σ[ Y ∈ ℕ ] (B ≡ ` Y))
    ⊎ (Σ[ q ∈ List ConvElt ]
         ((allElts (elts c) ≡ just q) × AllShape B))
canon-all (conv-id wf) nf sh = inj₂ (_ , refl , sh)
canon-all (conv-cons (conv-seal rep rd p) tl) (nf-cons nfe nfc irr) sh
  with after-add (aa-seal p refl) tl refl nfc irr
canon-all (conv-cons (conv-seal rep rd p) tl) (nf-cons nfe nfc irr) sh
  | Y , eq = inj₁ (Y , eq)
canon-all (conv-cons (conv-unseal rep rd p) tl) nf ()
canon-all (conv-cons (conv-fun s′ t′) tl) nf ()
canon-all {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl)
  (nf-cons nfe nfc irr) sh with canon-all tl nfc (all-shift X A sh)
canon-all {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-all {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-all-hide {X = X} {α = α} (elts c) eqE
canon-all {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)
canon-all {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p) tl)
  (nf-cons nfe nfc irr) sh with canon-all tl nfc (shift-all X A sh)
canon-all {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-all {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-all-show {X = X} {α = α} (elts c) eqE
canon-all {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)
canon-all {c = all s′ ∷ᶜ c} (conv-cons (conv-all s″) tl)
  (nf-cons nfe nfc irr) sh with canon-all tl nfc (all-shape _)
canon-all {c = all s′ ∷ᶜ c} (conv-cons (conv-all s″) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-all {c = all s′ ∷ᶜ c} (conv-cons (conv-all s″) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-all-all {s = s′} (elts c) eqE
canon-all {c = all s′ ∷ᶜ c} (conv-cons (conv-all s″) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)

-- From a GROUND source: either a seal, or every element is a crossing
-- and `base` sees the ground terminator.
canon-ground : Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → NF c → GroundShape A
  → (Σ[ Y ∈ ℕ ] (B ≡ ` Y)) ⊎ (Σ[ ι ∈ Ty ] (base c ≡ just ι))
canon-ground (conv-id wf) nf ground-ℕ = inj₂ (_ , refl)
canon-ground (conv-id wf) nf ground-𝔹 = inj₂ (_ , refl)
canon-ground (conv-cons (conv-seal rep rd p) tl) (nf-cons nfe nfc irr) sh
  with after-add (aa-seal p refl) tl refl nfc irr
canon-ground (conv-cons (conv-seal rep rd p) tl) (nf-cons nfe nfc irr) sh
  | Y , eq = inj₁ (Y , eq)
canon-ground (conv-cons (conv-unseal rep rd p) tl) nf ()
canon-ground (conv-cons (conv-fun s′ t′) tl) nf ()
canon-ground (conv-cons (conv-all s′) tl) nf ()
canon-ground {c = hide X α ∷ᶜ c} (conv-cons (conv-hide {A = A} wf a p) tl)
  (nf-cons nfe nfc irr) sh = canon-ground tl nfc (ground-shift X A sh)
canon-ground {c = show X α ∷ᶜ c} (conv-cons (conv-show {A = A} wf p) tl)
  (nf-cons nfe nfc irr) sh = canon-ground tl nfc (shift-ground X A sh)

------------------------------------------------------------------------
-- Assembly: the canonicity obligation of `proof.Progress`
------------------------------------------------------------------------

-- A simple value's type is never a type variable, and at a ground type
-- it is a literal.
simple-kind : ∀ {V} → Simple V → Sg ∣ Δ ∣ [] ⊢ V ⦂ A
  → FunShape A ⊎ (AllShape A ⊎ (GroundShape A × Literal V))
simple-kind S$ ⊢$ = inj₂ (inj₂ (ground-ℕ , literal-$))
simple-kind S# ⊢# = inj₂ (inj₂ (ground-𝔹 , literal-#))
simple-kind Sƛ (⊢ƛ wf body) = inj₁ (fun-shape _ _)
simple-kind (SΛ v) (⊢Λ _ body) = inj₂ (inj₁ (all-shape _))

inert-of-arr : ∀ {B Ls Rs} (A₀ : Ty) (c : Conv)
  → arrElts (elts c) ≡ just (Ls , Rs)
  → target c ≡ B → FunShape B
  → Σ[ p ∈ Conv × Conv ] (arr A₀ c ≡ just p)
inert-of-arr A₀ c eqE teq (fun-shape C D)
  rewrite eqE | teq = _ , refl

inert-of-all : ∀ {B Es} (c : Conv) → allElts (elts c) ≡ just Es
  → target c ≡ B → AllShape B
  → Σ[ d ∈ Conv ] (allView c ≡ just d)
inert-of-all c eqE teq (all-shape A) rewrite eqE | teq = _ , refl

canonicity : ∀ {V} → Simple V
  → Sg ∣ Δᵢ ∣ [] ⊢ V ⦂ A
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ
  → NF c
  → Inert c ⊎ (Σ[ ι ∈ Ty ] (Literal V × (base c ≡ just ι)))
canonicity simple ⊢V conv nf with simple-kind simple ⊢V

-- an arrow-typed body: `arr` splits, unless a seal sealed the target
canonicity simple ⊢V conv nf | inj₁ sh with canon-fun conv nf sh
canonicity simple ⊢V conv nf | inj₁ sh | inj₁ (Y , refl) =
  inj₁ (inert-var (conv-target conv))
canonicity {c = c} simple ⊢V conv nf | inj₁ sh
  | inj₂ ((Ls , Rs) , eqE , shB)
  with inert-of-arr `ℕ c eqE (conv-target conv) shB
canonicity {c = c} simple ⊢V conv nf | inj₁ sh
  | inj₂ ((Ls , Rs) , eqE , shB) | _ , arr-eq =
  inj₁ (inert-arr `ℕ arr-eq)

-- a universally-typed body: `allView`
canonicity simple ⊢V conv nf | inj₂ (inj₁ sh) with canon-all conv nf sh
canonicity simple ⊢V conv nf | inj₂ (inj₁ sh) | inj₁ (Y , refl) =
  inj₁ (inert-var (conv-target conv))
canonicity {c = c} simple ⊢V conv nf | inj₂ (inj₁ sh)
  | inj₂ (Es , eqE , shB)
  with inert-of-all c eqE (conv-target conv) shB
canonicity {c = c} simple ⊢V conv nf | inj₂ (inj₁ sh)
  | inj₂ (Es , eqE , shB) | _ , all-eq = inj₁ (inert-all all-eq)

-- a literal body: either a seal sealed the target, or `base` sees it
canonicity simple ⊢V conv nf | inj₂ (inj₂ (sh , lit))
  with canon-ground conv nf sh
canonicity simple ⊢V conv nf | inj₂ (inj₂ (sh , lit)) | inj₁ (Y , refl) =
  inj₁ (inert-var (conv-target conv))
canonicity simple ⊢V conv nf | inj₂ (inj₂ (sh , lit))
  | inj₂ (ι , base-eq) = inj₂ (ι , lit , base-eq)
