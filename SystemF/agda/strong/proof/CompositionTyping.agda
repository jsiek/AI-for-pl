module strong.proof.CompositionTyping where

-- Strong System F v8 — COMPOSITION preserves typing.
--
-- The raw append is the easy half, and v8's strictly reflexive
-- terminator is why: `id A ⧺ d = d`, and a typed `id A` has EQUAL
-- endpoints AND an equal context, so the second conversion already has
-- exactly the type and the context the composite needs — no bridging,
-- no transport.  Under v7's bridging terminator this single case was
-- the whole difficulty of the composition campaign.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion

private
  variable
    Sg : Store
    Ξ : Ctxᵗ
    Γ Γ₁ Γ₂ Γ₃ : Ctxᵗ
    A B C : Ty
    R S : RepTy
    α : Addr
    c c′ d s t : Conv
    ĉ : ConvElt

------------------------------------------------------------------------
-- Appending
------------------------------------------------------------------------

⧺-typing : Sg ∣ Ξ ∣ Γ₁ ⊢ c ∶ A ⇝ B ⊣ Γ₂ → Sg ∣ Ξ ∣ Γ₂ ⊢ d ∶ B ⇝ C ⊣ Γ₃
  → Sg ∣ Ξ ∣ Γ₁ ⊢ (c ⧺ d) ∶ A ⇝ C ⊣ Γ₃
⧺-typing (conv-id wf) ⊢d = ⊢d
⧺-typing (conv-cons hd tl) ⊢d = conv-cons hd (⧺-typing tl ⊢d)

------------------------------------------------------------------------
-- The representation of an address is unique
------------------------------------------------------------------------
-- Driven by the address's own structure: a level indexes the store, a
-- bound index counts entries.  No well-formedness is needed.

∋ˡ-unique : ∀ {Sg ℓ R S} → Sg ∋ˡ ℓ := R → Sg ∋ˡ ℓ := S → R ≡ S
∋ˡ-unique l-here l-here = refl
∋ˡ-unique (l-there p) (l-there q) = ∋ˡ-unique p q

∋r-unique : Sg ∣ Γ ∋r α := R → Sg ∣ Γ ∋r α := S → R ≡ S
∋r-unique (r-lvl l) (r-lvl m) = ∋ˡ-unique l m
∋r-unique r-here r-here = refl
∋r-unique (r-skip-addr p) (r-skip-addr q) = cong ⇑ᴿᵉ (∋r-unique p q)
∋r-unique (r-skip-nu p) (r-skip-nu q) = cong ⇑ᴿᵉ (∋r-unique p q)

------------------------------------------------------------------------
-- Name uniqueness propagates, so the read-back is single-valued
------------------------------------------------------------------------
-- The freshness premise on `conv-unseal`/`conv-show` is exactly what
-- carries `NameFn` inward across an element that introduces an
-- assignment; `bind` carries it across a `∀` element's binder.

namefn-bind : NameFn Γ → NameFn (bind ∷ stk Γ ∥ bas Γ)
namefn-bind nf (n-skip-bind p) (n-skip-bind q) = cong suc (nf p q)

namefn-unbind : NameFn (bind ∷ stk Γ ∥ bas Γ) → NameFn Γ
namefn-unbind nf p q = suc-inj (nf (n-skip-bind p) (n-skip-bind q))
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

notasgn-unbind : ∀ {Γ α} → NotAssigned (bind ∷ stk Γ ∥ bas Γ) α
  → NotAssigned Γ α
notasgn-unbind na p = na (n-skip-bind p)

-- Pushing the assignment an `unseal`/`show` introduces keeps names
-- unique, PROVIDED the address was unassigned — which is the premise.
namefn-push : ∀ {Γᵢ Γₑ X α} → NameFn Γₑ → NotAssigned Γₑ α
  → Γᵢ ▷ X := α ⇒ Γₑ → NameFn Γᵢ
namefn-push nf na pop-here n-here-asgn n-here-asgn = refl
namefn-push nf na pop-here n-here-asgn (n-skip-asgn q) = ⊥-elim (na q)
namefn-push nf na pop-here (n-skip-asgn p) n-here-asgn = ⊥-elim (na p)
namefn-push nf na pop-here (n-skip-asgn p) (n-skip-asgn q) =
  cong suc (nf p q)
namefn-push nf na (pop-bind p) =
  namefn-bind (namefn-push (namefn-unbind nf) (notasgn-unbind na) p)

-- the i-th `bind` has exactly one name
∋b-unique : ∀ {Ss X Y i} → Ss ∋b X at i → Ss ∋b Y at i → X ≡ Y
∋b-unique b-here b-here = refl
∋b-unique (b-asgn p) (b-asgn q) = cong suc (∋b-unique p q)
∋b-unique (b-bind p) (b-bind q) = cong suc (∋b-unique p q)

read-unique : ∀ {Γ} → NameFn Γ
  → Sg ∣ Γ ⊢ R ⇓ A → Sg ∣ Γ ⊢ R ⇓ B → A ≡ B
read-unique nf (read-var n) (read-var m) = cong `_ (nf n m)
read-unique nf (read-bv n) (read-bv m) = cong `_ (∋b-unique n m)
read-unique nf read-ℕ read-ℕ = refl
read-unique nf read-𝔹 read-𝔹 = refl
read-unique nf (read-⇒ p q) (read-⇒ p′ q′)
  rewrite read-unique nf p p′ | read-unique nf q q′ = refl
read-unique nf (read-∀ p) (read-∀ q)
  rewrite read-unique (namefn-bind nf) p q = refl

------------------------------------------------------------------------
-- One normalization step preserves typing
------------------------------------------------------------------------
-- A cancelling pair reconnects EXACTLY: `pop-unique` forces the
-- remover to the address AND the context the adder created, `∋r-unique`
-- forces the two representations to agree, and `read-unique` (with the
-- names unique, by the freshness premise) forces the two read-backs to
-- agree.  A `↦` or `all` fusion is `⧺-typing` on the components.

suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

var-inj : ∀ {m n} → (` m) ≡ (` n) → m ≡ n
var-inj refl = refl

⇒-injˡ : ∀ {A B C D} → (A ⇒ B) ≡ (C ⇒ D) → A ≡ C
⇒-injˡ refl = refl

⇒-injʳ : ∀ {A B C D} → (A ⇒ B) ≡ (C ⇒ D) → B ≡ D
⇒-injʳ refl = refl

∀-inj : ∀ {A B} → (`∀ A) ≡ (`∀ B) → A ≡ B
∀-inj refl = refl

Injᵗ : Renameᵗ → Set
Injᵗ ρ = ∀ {m n} → ρ m ≡ ρ n → m ≡ n

ext-inj : ∀ (ρ : Renameᵗ) → Injᵗ ρ → Injᵗ (extᵗ ρ)
ext-inj ρ i {zero} {zero} eq = refl
ext-inj ρ i {zero} {suc n} ()
ext-inj ρ i {suc m} {zero} ()
ext-inj ρ i {suc m} {suc n} eq = cong suc (i (suc-inj eq))

ren-inj : ∀ (ρ : Renameᵗ) → Injᵗ ρ → ∀ A B
  → renameᵗ ρ A ≡ renameᵗ ρ B → A ≡ B
ren-inj ρ inj (` X) (` Y) eq = cong `_ (inj (var-inj eq))
ren-inj ρ inj `ℕ `ℕ eq = refl
ren-inj ρ inj `𝔹 `𝔹 eq = refl
ren-inj ρ inj (A ⇒ B) (C ⇒ D) eq
  rewrite ren-inj ρ inj A C (⇒-injˡ eq) | ren-inj ρ inj B D (⇒-injʳ eq) =
  refl
ren-inj ρ inj (`∀ A) (`∀ B) eq
  rewrite ren-inj (extᵗ ρ) (ext-inj ρ inj) A B (∀-inj eq) = refl
ren-inj ρ inj (` X) `ℕ ()
ren-inj ρ inj (` X) `𝔹 ()
ren-inj ρ inj (` X) (C ⇒ D) ()
ren-inj ρ inj (` X) (`∀ B) ()
ren-inj ρ inj `ℕ (` Y) ()
ren-inj ρ inj `ℕ `𝔹 ()
ren-inj ρ inj `ℕ (C ⇒ D) ()
ren-inj ρ inj `ℕ (`∀ B) ()
ren-inj ρ inj `𝔹 (` Y) ()
ren-inj ρ inj `𝔹 `ℕ ()
ren-inj ρ inj `𝔹 (C ⇒ D) ()
ren-inj ρ inj `𝔹 (`∀ B) ()
ren-inj ρ inj (A ⇒ B) (` Y) ()
ren-inj ρ inj (A ⇒ B) `ℕ ()
ren-inj ρ inj (A ⇒ B) `𝔹 ()
ren-inj ρ inj (A ⇒ B) (`∀ D) ()
ren-inj ρ inj (`∀ A) (` Y) ()
ren-inj ρ inj (`∀ A) `ℕ ()
ren-inj ρ inj (`∀ A) `𝔹 ()
ren-inj ρ inj (`∀ A) (C ⇒ D) ()

inj-shiftAt : ∀ X → Injᵗ (shiftAtᵗ X)
inj-shiftAt zero refl = refl
inj-shiftAt (suc X) {zero} {zero} eq = refl
inj-shiftAt (suc X) {zero} {suc n} ()
inj-shiftAt (suc X) {suc m} {zero} ()
inj-shiftAt (suc X) {suc m} {suc n} eq =
  cong suc (inj-shiftAt X (suc-inj eq))

shiftAtᵗ-inj : ∀ X A B
  → renameᵗ (shiftAtᵗ X) A ≡ renameᵗ (shiftAtᵗ X) B → A ≡ B
shiftAtᵗ-inj X A B eq = ren-inj (shiftAtᵗ X) (inj-shiftAt X) A B eq

-- Removing the newest assignment keeps names unique.
namefn-pop : ∀ {Γᵢ Γₑ X α} → Γᵢ ▷ X := α ⇒ Γₑ → NameFn Γᵢ → NameFn Γₑ
namefn-pop pop-here nf p q = suc-inj (nf (n-skip-asgn p) (n-skip-asgn q))
namefn-pop (pop-bind r) nf =
  namefn-bind (namefn-pop r (namefn-unbind nf))

-- `NameFn` holds at every context a typed conversion passes through,
-- given it at the exterior: an element that introduces an assignment
-- carries its own freshness, and the others only remove or push a
-- binder.
mutual
  elt-namefn : Sg ∣ Ξ ∣ Γ₁ ⊢̂ ĉ ∶ A ⇝ B ⊣ Γ₂ → NameFn Γ₂ → NameFn Γ₁
  elt-namefn (conv-seal rep rd nm p) nf = namefn-pop p nf
  elt-namefn (conv-hide sc wf p na) nf = namefn-pop p nf
  elt-namefn (conv-unseal rep rd nm p na) nf = namefn-push nf na p
  elt-namefn (conv-show sc wf p na) nf = namefn-push nf na p
  elt-namefn (conv-fun s′ t′) nf = conv-namefn t′ nf
  elt-namefn (conv-all s′) nf =
    namefn-unbind (conv-namefn s′ (namefn-bind nf))

  conv-namefn : Sg ∣ Ξ ∣ Γ₁ ⊢ c ∶ A ⇝ B ⊣ Γ₂ → NameFn Γ₂ → NameFn Γ₁
  conv-namefn (conv-id wf) nf = nf
  conv-namefn (conv-cons hd tl) nf = elt-namefn hd (conv-namefn tl nf)

------------------------------------------------------------------------
-- The cancelling pairs reconnect EXACTLY
------------------------------------------------------------------------
-- This is the content `preserve-step` needs at a `ξ-pair`: when a pair
-- fuses away, the conversion on either side of it meets — same
-- context, same type — so the remaining tail already has the composite
-- conversion's type.  `pop-unique` forces the remover to the address
-- AND the context the adder created; `∋r-unique` forces the two
-- representations to agree; `read-unique` (with names unique, by the
-- freshness premise the adder's dual carries) forces the read-backs to
-- agree; and `shiftAtᵗ-inj` undoes the crossing's shift.

open import strong.proof.ConvCanonicity using (pop-unique)
open import strong.proof.Interior using (push-sound)

-- Inversions: the element is in constructor form, so these match where
-- a direct pattern on the derivation would leave the unifier stuck on
-- two renames.
inv-show : ∀ {Γ₁ Γ₂ A B Y β}
  → Sg ∣ Ξ ∣ Γ₁ ⊢̂ show Y β ∶ A ⇝ B ⊣ Γ₂
  → (A ≡ B) × (Γ₁ ▷ Y := β ⇒ Γ₂)
inv-show (conv-show sc wf p na) = refl , p

inv-hide : ∀ {Γ₁ Γ₂ A B X α}
  → Sg ∣ Ξ ∣ Γ₁ ⊢̂ hide X α ∶ A ⇝ B ⊣ Γ₂
  → (B ≡ A) × (Γ₂ ▷ X := α ⇒ Γ₁)
inv-hide (conv-hide sc wf p na) = refl , p

inv-seal : ∀ {Γ₁ Γ₂ A B X α}
  → Sg ∣ Ξ ∣ Γ₁ ⊢̂ seal X α ∶ A ⇝ B ⊣ Γ₂
  → Σ[ R ∈ RepTy ] Σ[ X′ ∈ ℕ ]
      ((B ≡ ` X′) × (Ξ ∋n X′ := α) × (Sg ∣ Γ₂ ∋r α := R)
       × (Sg ∣ Ξ ⊢ R ⇓ A) × (Γ₂ ▷ X := α ⇒ Γ₁))
inv-seal (conv-seal rep rd nm p) = _ , _ , refl , nm , rep , rd , p

inv-unseal : ∀ {Γ₁ Γ₂ A B X α}
  → Sg ∣ Ξ ∣ Γ₁ ⊢̂ unseal X α ∶ A ⇝ B ⊣ Γ₂
  → Σ[ R ∈ RepTy ] Σ[ X′ ∈ ℕ ]
      ((A ≡ ` X′) × (Ξ ∋n X′ := α) × (Sg ∣ Γ₁ ∋r α := R)
       × (Sg ∣ Ξ ⊢ R ⇓ B) × (Γ₁ ▷ X := α ⇒ Γ₂))
inv-unseal (conv-unseal rep rd nm p na) = _ , _ , refl , nm , rep , rd , p

-- seal α then unseal α
-- The ADDRESSES need not be assumed equal: both pops are from Γ₂, so
-- `pop-unique` delivers `α ≡ β` along with the rest.  This is why `fuse`
-- can cancel this pair on the NAME alone (strong.Conversion).
cancel-seal : ∀ {Γ₁ Γ₂ Γ₃ A B C X Y α β}
  → Sg ∣ Ξ ∣ Γ₁ ⊢̂ seal X α ∶ A ⇝ B ⊣ Γ₂
  → Sg ∣ Ξ ∣ Γ₂ ⊢̂ unseal Y β ∶ B ⇝ C ⊣ Γ₃
  → NameFn Ξ
  → (Γ₁ ≡ Γ₃) × (A ≡ C)
cancel-seal hd hd₂ nf with inv-seal hd | inv-unseal hd₂
cancel-seal hd hd₂ nf
  | R , X′ , refl , nm , rep , rd , p | R′ , Y′ , teq , nm′ , rep′ , rd′ , q
  with pop-unique q p
cancel-seal hd hd₂ nf
  | R , X′ , refl , nm , rep , rd , p | R′ , Y′ , teq , nm′ , rep′ , rd′ , q
  | refl , refl , refl with ∋r-unique rep′ rep
cancel-seal hd hd₂ nf
  | R , X′ , refl , nm , rep , rd , p | R′ , Y′ , teq , nm′ , rep′ , rd′ , q
  | refl , refl , refl | refl = refl , read-unique nf rd rd′

-- hide α then show α
cancel-hide : ∀ {Γ₁ Γ₂ Γ₃ A B C X Y α β}
  → Sg ∣ Ξ ∣ Γ₁ ⊢̂ hide X α ∶ A ⇝ B ⊣ Γ₂
  → Sg ∣ Ξ ∣ Γ₂ ⊢̂ show Y β ∶ B ⇝ C ⊣ Γ₃
  → (Γ₁ ≡ Γ₃) × (A ≡ C)
-- neither element re-spells now, so the types meet definitionally
cancel-hide hd hd₂ with inv-hide hd | inv-show hd₂
cancel-hide hd hd₂ | refl , p | refl , q with pop-unique q p
cancel-hide hd hd₂ | refl , p | refl , q | refl , refl , refl = refl , refl

-- The REMOVE-then-ADD orders are GONE: `fuse` no longer has rows for
-- `unseal ∷ seal` or `show ∷ hide` (2026-09-17), so `cancel-unseal` and
-- `cancel-show` had no callers and are deleted with them.

open import strong.ConversionReduction using
  (_—→ᶜ_; ξ-pair; ξ-∷; ξ-↦₁; ξ-↦₂; ξ-all; consAll)

-- Reading a cancellation back out of `fuse`: the NAMES agreed and
-- nothing was produced (the address test is gone, 2026-09-17).
fuse-cancel-su : ∀ {X Y α β ks} → fuse (seal X α) (unseal Y β) ≡ just ks
  → (X ≡ Y) × (ks ≡ [])
fuse-cancel-su {X = X} {Y = Y} eq with X ≟ Y | eq
fuse-cancel-su eq | yes refl | refl = refl , refl
fuse-cancel-su eq | no _ | ()

fuse-cancel-us : ∀ {X Y α β ks} → fuse (unseal X α) (seal Y β) ≡ just ks
  → (X ≡ Y) × (ks ≡ [])
fuse-cancel-us ()

fuse-cancel-hs : ∀ {X Y α β ks} → fuse (hide X α) (show Y β) ≡ just ks
  → (X ≡ Y) × (ks ≡ [])
fuse-cancel-hs {X = X} {Y = Y} eq with X ≟ Y | eq
fuse-cancel-hs eq | yes refl | refl = refl , refl
fuse-cancel-hs eq | no _ | ()

fuse-cancel-sh : ∀ {X Y α β ks} → fuse (show X α) (hide Y β) ≡ just ks
  → (X ≡ Y) × (α ≡ β) × (ks ≡ [])
fuse-cancel-sh {X = X} {Y = Y} {α = α} {β = β} eq with X ≟ Y | α ≟ᵃ β | eq
fuse-cancel-sh eq | yes refl | yes refl | refl = refl , refl , refl
fuse-cancel-sh eq | yes _ | no _ | ()
fuse-cancel-sh eq | no _ | _ | ()

-- show α then hide α.  RESTORED with the row: the two pops are from
-- DIFFERENT contexts, so what makes the endpoints meet is that the
-- addresses agree (which `fuse` checks) and `pushAsgn` is a function.
just-inj : ∀ {A : Set} {x y : A} → (just x) ≡ just y → x ≡ y
just-inj refl = refl

cancel-show : ∀ {Γ₁ Γ₂ Γ₃ A B C X α}
  → Sg ∣ Ξ ∣ Γ₁ ⊢̂ show X α ∶ A ⇝ B ⊣ Γ₂
  → Sg ∣ Ξ ∣ Γ₂ ⊢̂ hide X α ∶ B ⇝ C ⊣ Γ₃
  → (Γ₁ ≡ Γ₃) × (A ≡ C)
cancel-show hd hd₂ with inv-show hd | inv-hide hd₂
cancel-show hd hd₂ | refl , p | refl , q =
  just-inj (trans (sym (push-sound p)) (push-sound q)) , refl

-- the two structural fusions
fuse-fun-eq : ∀ {s₁ t₁ s₂ t₂ ks} → fuse (s₁ ↦ t₁) (s₂ ↦ t₂) ≡ just ks
  → ks ≡ (((s₂ ⧺ s₁) ↦ (t₁ ⧺ t₂)) ∷ [])
fuse-fun-eq refl = refl

fuse-all-eq : ∀ {s₁ s₂ ks} → fuse (all s₁) (all s₂) ≡ just ks
  → ks ≡ (all (s₁ ⧺ s₂) ∷ [])
fuse-all-eq refl = refl

-- `NameFn` is now needed AT THE FRAME — that is where the read-backs
-- live — and `⊢⟨⟩` carries it, so it is a premise rather than something
-- walked inward by `conv-namefn`.
preserve-step : ∀ {Γ₁ Δ} → NameFn Ξ
  → Sg ∣ Ξ ∣ Γ₁ ⊢ c ∶ A ⇝ B ⊣ Δ → c —→ᶜ c′
  → Sg ∣ Ξ ∣ Γ₁ ⊢ c′ ∶ A ⇝ B ⊣ Δ

-- the four cancelling pairs: the conversion on either side meets
preserve-step nf (conv-cons hd (conv-cons hd₂ tl))
  (ξ-pair {ĉ = seal X α} {ḓ = unseal Y β} eq)
  with fuse-cancel-su {X = X} {Y = Y} {α = α} {β = β} eq
preserve-step nf (conv-cons hd (conv-cons hd₂ tl))
  (ξ-pair {ĉ = seal X α} {ḓ = unseal Y β} eq) | refl , refl
  with cancel-seal hd hd₂ nf
preserve-step nf (conv-cons hd (conv-cons hd₂ tl))
  (ξ-pair {ĉ = seal X α} {ḓ = unseal Y β} eq) | refl , refl
  | refl , refl = tl

preserve-step nf (conv-cons hd (conv-cons hd₂ tl))
  (ξ-pair {ĉ = unseal X α} {ḓ = seal Y β} ())

preserve-step nf (conv-cons hd (conv-cons hd₂ tl))
  (ξ-pair {ĉ = hide X α} {ḓ = show Y β} eq)
  with fuse-cancel-hs {X = X} {Y = Y} {α = α} {β = β} eq
preserve-step nf (conv-cons hd (conv-cons hd₂ tl))
  (ξ-pair {ĉ = hide X α} {ḓ = show Y β} eq) | refl , refl
  with cancel-hide hd hd₂
preserve-step nf (conv-cons hd (conv-cons hd₂ tl))
  (ξ-pair {ĉ = hide X α} {ḓ = show Y β} eq) | refl , refl
  | refl , refl = tl

preserve-step nf (conv-cons hd (conv-cons hd₂ tl))
  (ξ-pair {ĉ = show X α} {ḓ = hide Y β} eq)
  with fuse-cancel-sh {X = X} {Y = Y} {α = α} {β = β} eq
preserve-step nf (conv-cons hd (conv-cons hd₂ tl))
  (ξ-pair {ĉ = show X α} {ḓ = hide Y β} eq) | refl , refl , refl
  with cancel-show hd hd₂
preserve-step nf (conv-cons hd (conv-cons hd₂ tl))
  (ξ-pair {ĉ = show X α} {ḓ = hide Y β} eq) | refl , refl , refl
  | refl , refl = tl

-- the two structural fusions: `⧺-typing` on the components
preserve-step nf
  (conv-cons (conv-fun {s = s₁} {t = t₁} ⊢s₁ ⊢t₁)
             (conv-cons (conv-fun {s = s₂} {t = t₂} ⊢s₂ ⊢t₂) tl))
  (ξ-pair {ĉ = s₁ ↦ t₁} {ḓ = s₂ ↦ t₂} eq)
  rewrite fuse-fun-eq {s₁ = s₁} {t₁ = t₁} {s₂ = s₂} {t₂ = t₂} eq =
  conv-cons (conv-fun (⧺-typing ⊢s₂ ⊢s₁) (⧺-typing ⊢t₁ ⊢t₂)) tl
preserve-step nf
  (conv-cons (conv-all {s = s₁} ⊢s₁) (conv-cons (conv-all {s = s₂} ⊢s₂) tl))
  (ξ-pair {ĉ = all s₁} {ḓ = all s₂} eq)
  rewrite fuse-all-eq {s₁ = s₁} {s₂ = s₂} eq =
  conv-cons (conv-all (⧺-typing ⊢s₁ ⊢s₂)) tl

-- the congruences
preserve-step nf (conv-cons hd tl) (ξ-∷ st) =
  conv-cons hd (preserve-step nf tl st)
preserve-step nf (conv-cons (conv-fun s₁ t₁) tl) (ξ-↦₁ st) =
  conv-cons (conv-fun (preserve-step nf s₁ st) t₁) tl
preserve-step nf (conv-cons (conv-fun s₁ t₁) tl) (ξ-↦₂ st) =
  conv-cons (conv-fun s₁ (preserve-step nf t₁ st)) tl
preserve-step nf (conv-cons (conv-all s₁) tl) (ξ-all st) =
  conv-cons (conv-all (preserve-step (namefn-bind nf) s₁ st)) tl

------------------------------------------------------------------------
-- Composition preserves typing
------------------------------------------------------------------------

open import strong.ConversionReduction using
  (_—↠ᶜ_; done; step; _⨟_; ⨟-↠; ⨟-NF)

preserve-↠ : ∀ {Γ₁ Δ} → NameFn Ξ
  → Sg ∣ Ξ ∣ Γ₁ ⊢ c ∶ A ⇝ B ⊣ Δ → c —↠ᶜ c′
  → Sg ∣ Ξ ∣ Γ₁ ⊢ c′ ∶ A ⇝ B ⊣ Δ
preserve-↠ nf ⊢c done = ⊢c
preserve-↠ nf ⊢c (step st tr) = preserve-↠ nf (preserve-step nf ⊢c st) tr

-- `c ⨟ d = normalize (c ⧺ d)`: append, then normalize along the trace.
⨟-typing : ∀ {Γ₁ Γ₂ Γ₃} → NameFn Ξ
  → Sg ∣ Ξ ∣ Γ₁ ⊢ c ∶ A ⇝ B ⊣ Γ₂ → Sg ∣ Ξ ∣ Γ₂ ⊢ d ∶ B ⇝ C ⊣ Γ₃
  → Sg ∣ Ξ ∣ Γ₁ ⊢ (c ⨟ d) ∶ A ⇝ C ⊣ Γ₃
⨟-typing {c = c} {d = d} nf ⊢c ⊢d =
  preserve-↠ nf (⧺-typing ⊢c ⊢d) (⨟-↠ c d)
