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
open import Data.Nat.Properties using (_≟_)
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
open import strong.ConversionReduction
open import strong.Terms
open import strong.proof.Canonical

private
  variable
    Sg : Store
    Ξ : Ctxᵗ
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
pop-unique (pop-bind p) (pop-bind q) with pop-unique p q
pop-unique (pop-bind p) (pop-bind q) | refl , refl , refl =
  refl , refl , refl

------------------------------------------------------------------------
-- After an addition: the running type is a variable, and stays one
------------------------------------------------------------------------

-- `AfterAdd Ξ Γ r ĉ` — the previous element ĉ ADDED the newest crossing
-- assignment of Γ, and the running type is `` ` r ``: the FRAME'S name
-- for the new address when the adder was a seal (which renames to it),
-- a different name when the adder was a hide.
--
-- PORTED 2026-09-17.  Both halves used to speak of the ELEMENT'S name
-- X.  A seal's abstract side is now `` ` X′ `` with `Ξ ∋n X′ := α`, and
-- a hide's discriminator is its own new premise `A ≢ ` X′` rather than
-- the arithmetic of a shift — so both read the name off the frame.
data AfterAdd (Ξ Γ : Ctxᵗ) (r : ℕ) : ConvElt → Set where
  aa-seal : ∀ {X α Γ′} → Γ ▷ X := α ⇒ Γ′ → Ξ ∋n r := α
    → AfterAdd Ξ Γ r (seal X α)
  aa-hide : ∀ {X X′ α Γ′} → Γ ▷ X := α ⇒ Γ′ → Ξ ∋n X′ := α → r ≢ X′
    → AfterAdd Ξ Γ r (hide X α)

-- fusing a pair at one NAME (the address test is gone, 2026-09-17)
fuse-su : ∀ X α β → fuse (seal X α) (unseal X β) ≡ nothing → ⊥
fuse-su X α β eq with X ≟ X
fuse-su X α β () | yes _
fuse-su X α β eq | no ne = ne refl

fuse-hs : ∀ X α β → fuse (hide X α) (show X β) ≡ nothing → ⊥
fuse-hs X α β eq with X ≟ X
fuse-hs X α β () | yes _
fuse-hs X α β eq | no ne = ne refl

-- The source is carried as an EQUATION rather than as an index: the
-- crossing rules state their source as a rename, which the unifier
-- cannot match against a variable.
var≢⇒ : ∀ {A B X} → (A ⇒ B) ≢ ` X
var≢⇒ ()

var≢∀ : ∀ {A X} → (`∀ A) ≢ ` X
var≢∀ ()

-- PORT NOTE (2026-09-17, stage 3).  TWO things changed under it and
-- only the first is a restatement.
--
-- (1) `AfterAdd Γ r ĉ` says the element introduced an assignment at
--     NAME r, and `A ≡ ` r` said the running type was that name.  A
--     seal's abstract side is now `` ` X′ ``, the name Ξ has for the
--     ADDRESS, so the invariant should track the address and read its
--     name off Ξ.  Jeremy approved that restatement.
--
-- (2) BUT the two cases that were blocked by the SHIFT ARITHMETIC lose
--     their argument, because `hide`/`show` no longer re-spell:
--
--       * `show` after `seal` was `⊥-elim (shiftAt-var-≢ _ A eq)` — the
--         show's source used to be `renameᵗ (shiftAtᵗ X) A`, which could
--         not be the variable the seal produced.  It is now just `A`,
--         so the case is no longer absurd.  It also need not be: the
--         show preserves the type, so the running type stays a
--         variable — the RECURSION has to continue rather than close,
--         which means the invariant is not `AfterAdd` but the weaker
--         "the running type is a variable named in Ξ".
--
--       * `unseal` after `hide` was `⊥-elim (ne refl)` from `r ≢ X`,
--         which was about the shift.  Without it, `pop-unique` forces
--         the addresses equal and `fuse (hide X α) (unseal X α)` is
--         `nothing`, so nothing rules the pair out here.  Whether it is
--         ruled out at all — and hence whether the LEMMA still holds —
--         is the open question.
--
-- So this is a proof restructuring, not a restatement, and it is worth
-- settling before the rest of stage 3 leans on it.
after-add : NameFn Ξ → AfterAdd Ξ Γ r ĉ
  → Sg ∣ Ξ ∣ Γ ⊢ c ∶ A ⇝ B ⊣ Δ → A ≡ ` r → NF c → IrreducibleAfter ĉ c
  → Σ[ Y ∈ ℕ ] (B ≡ ` Y)
after-add nfΞ aa (conv-id wf) refl nf irr = _ , refl

-- an unseal REMOVES.  Pop-determinism forces its address to the
-- adder's; after a seal the pair then FUSES, and after a hide the
-- frame's name for that address is both `r` (from the unseal's own
-- abstract side) and not `r` (the hide's discriminator).
after-add nfΞ (aa-seal {X = X₁} p nm)
  (conv-cons (conv-unseal {X = Y₁} rep rd nm′ q na) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) with pop-unique q p
after-add nfΞ (aa-seal {X = X₁} {α = α₁} p nm)
  (conv-cons (conv-unseal {X = Y₁} rep rd nm′ q na) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) | refl , refl , refl =
  ⊥-elim (fuse-su X₁ α₁ α₁ fq)
after-add nfΞ (aa-hide p nm ne)
  (conv-cons (conv-unseal rep rd nm′ q na) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) with pop-unique q p
after-add nfΞ (aa-hide p nm ne)
  (conv-cons (conv-unseal rep rd nm′ q na) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) | refl , refl , refl =
  ⊥-elim (ne (nfΞ nm′ nm))

-- a show REMOVES: after a hide the pair fuses, and after a seal the
-- show's OWN premise `A ≢ ` X′` is contradicted — the running type is
-- `` ` r ``, and `NameFn Ξ` makes `r` the frame's name for the address.
after-add nfΞ (aa-seal p nm)
  (conv-cons (conv-show {A = A} sc wf nm′ ne q na) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) with pop-unique q p
after-add nfΞ (aa-seal p nm)
  (conv-cons (conv-show {A = A} sc wf nm′ ne q na) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) | refl , refl , refl =
  ⊥-elim (ne (cong `_ (nfΞ nm nm′)))
after-add nfΞ (aa-hide {X = X₁} {α = α₁} p nm ne)
  (conv-cons (conv-show {X = Y₁} sc wf nm′ ne′ q na) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) with pop-unique q p
after-add nfΞ (aa-hide {X = X₁} {α = α₁} p nm ne)
  (conv-cons (conv-show {X = Y₁} sc wf nm′ ne′ q na) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) | refl , refl , refl =
  ⊥-elim (fuse-hs X₁ α₁ α₁ fq)

-- an ADDITION keeps us in the same situation
after-add nfΞ aa (conv-cons (conv-seal rep rd nm q) tl) eq
  (nf-cons nfe nfc irr′) (irr-cons fq) =
  after-add nfΞ (aa-seal q nm) tl refl nfc irr′
after-add nfΞ aa (conv-cons (conv-hide {A = A} sc wf q na) tl) refl
  (nf-cons nfe nfc irr′) (irr-cons fq) =
  after-add nfΞ (aa-hide q nm (λ e → ne (cong `_ e))) tl refl nfc irr′

-- a structural element needs an arrow or a universal source
after-add nfΞ aa (conv-cons (conv-fun s′ t′) tl) eq nf irr =
  ⊥-elim (var≢⇒ eq)
after-add nfΞ aa (conv-cons (conv-all s′) tl) eq nf irr =
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
canon-fun : NameFn Ξ → Sg ∣ Ξ ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → NF c → FunShape A
  → (Σ[ Y ∈ ℕ ] (B ≡ ` Y))
    ⊎ (Σ[ q ∈ List ConvElt × List ConvElt ]
         ((arrElts (elts c) ≡ just q) × FunShape B))
canon-fun nfΞ (conv-id wf) nf sh = inj₂ (_ , refl , sh)
canon-fun nfΞ (conv-cons (conv-seal rep rd nm p) tl) (nf-cons nfe nfc irr) sh
  with after-add nfΞ (aa-seal p nm) tl refl nfc irr
canon-fun nfΞ (conv-cons (conv-seal rep rd nm p) tl) (nf-cons nfe nfc irr) sh
  | Y , eq = inj₁ (Y , eq)
canon-fun nfΞ (conv-cons (conv-unseal rep rd nm p na) tl) nf ()
canon-fun nfΞ (conv-cons (conv-all s′) tl) nf ()
canon-fun {c = hide X α ∷ᶜ c} nfΞ (conv-cons (conv-hide {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh with canon-fun nfΞ tl nfc sh
canon-fun {c = hide X α ∷ᶜ c} nfΞ (conv-cons (conv-hide {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-fun {c = hide X α ∷ᶜ c} nfΞ (conv-cons (conv-hide {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-arr-hide {X = X} {α = α} (elts c) eqE
canon-fun {c = hide X α ∷ᶜ c} nfΞ (conv-cons (conv-hide {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)
canon-fun {c = show X α ∷ᶜ c} nfΞ (conv-cons (conv-show {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh with canon-fun nfΞ tl nfc sh
canon-fun {c = show X α ∷ᶜ c} nfΞ (conv-cons (conv-show {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-fun {c = show X α ∷ᶜ c} nfΞ (conv-cons (conv-show {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-arr-show {X = X} {α = α} (elts c) eqE
canon-fun {c = show X α ∷ᶜ c} nfΞ (conv-cons (conv-show {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)
canon-fun {c = (s′ ↦ t′) ∷ᶜ c} nfΞ (conv-cons (conv-fun s″ t″) tl)
  (nf-cons nfe nfc irr) sh with canon-fun nfΞ tl nfc (fun-shape _ _)
canon-fun {c = (s′ ↦ t′) ∷ᶜ c} nfΞ (conv-cons (conv-fun s″ t″) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-fun {c = (s′ ↦ t′) ∷ᶜ c} nfΞ (conv-cons (conv-fun s″ t″) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-arr-fun {s = s′} {t = t′} (elts c) eqE
canon-fun {c = (s′ ↦ t′) ∷ᶜ c} nfΞ (conv-cons (conv-fun s″ t″) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)

-- From a UNIVERSAL source, symmetrically.
canon-all : NameFn Ξ → Sg ∣ Ξ ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → NF c → AllShape A
  → (Σ[ Y ∈ ℕ ] (B ≡ ` Y))
    ⊎ (Σ[ q ∈ List ConvElt ]
         ((allElts (elts c) ≡ just q) × AllShape B))
canon-all nfΞ (conv-id wf) nf sh = inj₂ (_ , refl , sh)
canon-all nfΞ (conv-cons (conv-seal rep rd nm p) tl) (nf-cons nfe nfc irr) sh
  with after-add nfΞ (aa-seal p nm) tl refl nfc irr
canon-all nfΞ (conv-cons (conv-seal rep rd nm p) tl) (nf-cons nfe nfc irr) sh
  | Y , eq = inj₁ (Y , eq)
canon-all nfΞ (conv-cons (conv-unseal rep rd nm p na) tl) nf ()
canon-all nfΞ (conv-cons (conv-fun s′ t′) tl) nf ()
canon-all {c = hide X α ∷ᶜ c} nfΞ (conv-cons (conv-hide {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh with canon-all nfΞ tl nfc sh
canon-all {c = hide X α ∷ᶜ c} nfΞ (conv-cons (conv-hide {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-all {c = hide X α ∷ᶜ c} nfΞ (conv-cons (conv-hide {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-all-hide {X = X} {α = α} (elts c) eqE
canon-all {c = hide X α ∷ᶜ c} nfΞ (conv-cons (conv-hide {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)
canon-all {c = show X α ∷ᶜ c} nfΞ (conv-cons (conv-show {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh with canon-all nfΞ tl nfc sh
canon-all {c = show X α ∷ᶜ c} nfΞ (conv-cons (conv-show {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-all {c = show X α ∷ᶜ c} nfΞ (conv-cons (conv-show {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-all-show {X = X} {α = α} (elts c) eqE
canon-all {c = show X α ∷ᶜ c} nfΞ (conv-cons (conv-show {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)
canon-all {c = all s′ ∷ᶜ c} nfΞ (conv-cons (conv-all s″) tl)
  (nf-cons nfe nfc irr) sh with canon-all nfΞ tl nfc (all-shape _)
canon-all {c = all s′ ∷ᶜ c} nfΞ (conv-cons (conv-all s″) tl)
  (nf-cons nfe nfc irr) sh | inj₁ v = inj₁ v
canon-all {c = all s′ ∷ᶜ c} nfΞ (conv-cons (conv-all s″) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB)
  with lift-all-all {s = s′} (elts c) eqE
canon-all {c = all s′ ∷ᶜ c} nfΞ (conv-cons (conv-all s″) tl)
  (nf-cons nfe nfc irr) sh | inj₂ (q , eqE , shB) | _ , eq′ =
  inj₂ (_ , eq′ , shB)

-- From a GROUND source: either a seal, or every element is a crossing
-- and `base` sees the ground terminator.
canon-ground : NameFn Ξ → Sg ∣ Ξ ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → NF c → GroundShape A
  → (Σ[ Y ∈ ℕ ] (B ≡ ` Y)) ⊎ (Σ[ ι ∈ Ty ] (base c ≡ just ι))
canon-ground nfΞ (conv-id wf) nf ground-ℕ = inj₂ (_ , refl)
canon-ground nfΞ (conv-id wf) nf ground-𝔹 = inj₂ (_ , refl)
canon-ground nfΞ (conv-cons (conv-seal rep rd nm p) tl) (nf-cons nfe nfc irr) sh
  with after-add nfΞ (aa-seal p nm) tl refl nfc irr
canon-ground nfΞ (conv-cons (conv-seal rep rd nm p) tl) (nf-cons nfe nfc irr) sh
  | Y , eq = inj₁ (Y , eq)
canon-ground nfΞ (conv-cons (conv-unseal rep rd nm p na) tl) nf ()
canon-ground nfΞ (conv-cons (conv-fun s′ t′) tl) nf ()
canon-ground nfΞ (conv-cons (conv-all s′) tl) nf ()
canon-ground {c = hide X α ∷ᶜ c} nfΞ (conv-cons (conv-hide {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh = canon-ground nfΞ tl nfc sh
canon-ground {c = show X α ∷ᶜ c} nfΞ (conv-cons (conv-show {A = A} sc wf p na) tl)
  (nf-cons nfe nfc irr) sh = canon-ground nfΞ tl nfc sh

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

canonicity : ∀ {V} → NameFn Ξ → Simple V
  → Sg ∣ Δᵢ ∣ [] ⊢ V ⦂ A
  → Sg ∣ Ξ ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ
  → NF c
  → Inert c ⊎ (Σ[ ι ∈ Ty ] (Literal V × (base c ≡ just ι)))
canonicity nfΞ simple ⊢V conv nf with simple-kind simple ⊢V

-- an arrow-typed body: `arr` splits, unless a seal sealed the target
canonicity nfΞ simple ⊢V conv nf | inj₁ sh with canon-fun nfΞ conv nf sh
canonicity nfΞ simple ⊢V conv nf | inj₁ sh | inj₁ (Y , refl) =
  inj₁ (inert-var (conv-target conv))
canonicity {c = c} nfΞ simple ⊢V conv nf | inj₁ sh
  | inj₂ ((Ls , Rs) , eqE , shB)
  with inert-of-arr `ℕ c eqE (conv-target conv) shB
canonicity {c = c} nfΞ simple ⊢V conv nf | inj₁ sh
  | inj₂ ((Ls , Rs) , eqE , shB) | _ , arr-eq =
  inj₁ (inert-arr `ℕ arr-eq)

-- a universally-typed body: `allView`
canonicity nfΞ simple ⊢V conv nf | inj₂ (inj₁ sh) with canon-all nfΞ conv nf sh
canonicity nfΞ simple ⊢V conv nf | inj₂ (inj₁ sh) | inj₁ (Y , refl) =
  inj₁ (inert-var (conv-target conv))
canonicity {c = c} nfΞ simple ⊢V conv nf | inj₂ (inj₁ sh)
  | inj₂ (Es , eqE , shB)
  with inert-of-all c eqE (conv-target conv) shB
canonicity {c = c} nfΞ simple ⊢V conv nf | inj₂ (inj₁ sh)
  | inj₂ (Es , eqE , shB) | _ , all-eq = inj₁ (inert-all all-eq)

-- a literal body: either a seal sealed the target, or `base` sees it
canonicity nfΞ simple ⊢V conv nf | inj₂ (inj₂ (sh , lit))
  with canon-ground nfΞ conv nf sh
canonicity nfΞ simple ⊢V conv nf | inj₂ (inj₂ (sh , lit)) | inj₁ (Y , refl) =
  inj₁ (inert-var (conv-target conv))
canonicity nfΞ simple ⊢V conv nf | inj₂ (inj₂ (sh , lit))
  | inj₂ (ι , base-eq) = inj₂ (ι , lit , base-eq)
