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
open import strong.Conversion

private
  variable
    Sg : Store
    Γ Γ₁ Γ₂ Γ₃ : Ctxᵗ
    A B C : Ty
    R S : RepTy
    α : Addr
    c c′ d s t : Conv
    ĉ : ConvElt

------------------------------------------------------------------------
-- Appending
------------------------------------------------------------------------

⧺-typing : Sg ∣ Γ₁ ⊢ c ∶ A ⇝ B ⊣ Γ₂ → Sg ∣ Γ₂ ⊢ d ∶ B ⇝ C ⊣ Γ₃
  → Sg ∣ Γ₁ ⊢ (c ⧺ d) ∶ A ⇝ C ⊣ Γ₃
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
∋r-unique (r-skip-addr p) (r-skip-addr q) = cong ⇑ᴿ (∋r-unique p q)
∋r-unique (r-skip-nu p) (r-skip-nu q) = cong ⇑ᴿ (∋r-unique p q)
∋r-unique (r-skip-bind p) (r-skip-bind q) = cong ⇑ᴿ (∋r-unique p q)
∋r-unique (r-skip-asgn p) (r-skip-asgn q) = ∋r-unique p q

------------------------------------------------------------------------
-- Name uniqueness propagates, so the read-back is single-valued
------------------------------------------------------------------------
-- The freshness premise on `conv-unseal`/`conv-show` is exactly what
-- carries `NameFn` inward across an element that introduces an
-- assignment; `bind` carries it across a `∀` element's binder.

namefn-bind : NameFn Γ → NameFn (bind ∷ Γ)
namefn-bind nf n-here-bind n-here-bind = refl
namefn-bind nf (n-skip-bind-b p) (n-skip-bind-b q) = cong suc (nf p q)
namefn-bind nf (n-skip-bind-l p) (n-skip-bind-l q) = cong suc (nf p q)

namefn-unbind : NameFn (bind ∷ Γ) → NameFn Γ
namefn-unbind nf {α = lvl ℓ} p q =
  suc-inj (nf (n-skip-bind-l p) (n-skip-bind-l q))
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl
namefn-unbind nf {α = bnd i} p q =
  suc-inj (nf (n-skip-bind-b p) (n-skip-bind-b q))
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

notasgn-unbind : ∀ {Γ i} → NotAssigned (bind ∷ Γ) (bnd (suc i))
  → NotAssigned Γ (bnd i)
notasgn-unbind na p = na (n-skip-bind-b p)

notasgn-unbind-l : ∀ {Γ ℓ} → NotAssigned (bind ∷ Γ) (lvl ℓ)
  → NotAssigned Γ (lvl ℓ)
notasgn-unbind-l na p = na (n-skip-bind-l p)

-- Pushing the assignment an `unseal`/`show` introduces keeps names
-- unique, PROVIDED the address was unassigned — which is the premise.
namefn-push : ∀ {Γᵢ Γₑ X α} → NameFn Γₑ → NotAssigned Γₑ α
  → Γᵢ ▷ X := α ⇒ Γₑ → NameFn Γᵢ
namefn-push nf na pop-here n-here-asgn n-here-asgn = refl
namefn-push nf na pop-here n-here-asgn (n-skip-asgn q) = ⊥-elim (na q)
namefn-push nf na pop-here (n-skip-asgn p) n-here-asgn = ⊥-elim (na p)
namefn-push nf na pop-here (n-skip-asgn p) (n-skip-asgn q) =
  cong suc (nf p q)
namefn-push nf na (pop-bind-b p) =
  namefn-bind (namefn-push (namefn-unbind nf) (notasgn-unbind na) p)
namefn-push nf na (pop-bind-l p) =
  namefn-bind (namefn-push (namefn-unbind nf) (notasgn-unbind-l na) p)

read-unique : ∀ {Γ} → NameFn Γ
  → Sg ∣ Γ ⊢ R ⇓ A → Sg ∣ Γ ⊢ R ⇓ B → A ≡ B
read-unique nf (read-var n) (read-var m) = cong `_ (nf n m)
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
namefn-pop (pop-bind-b r) nf =
  namefn-bind (namefn-pop r (namefn-unbind nf))
namefn-pop (pop-bind-l r) nf =
  namefn-bind (namefn-pop r (namefn-unbind nf))

-- `NameFn` holds at every context a typed conversion passes through,
-- given it at the exterior: an element that introduces an assignment
-- carries its own freshness, and the others only remove or push a
-- binder.
mutual
  elt-namefn : Sg ∣ Γ₁ ⊢̂ ĉ ∶ A ⇝ B ⊣ Γ₂ → NameFn Γ₂ → NameFn Γ₁
  elt-namefn (conv-seal rep rd p) nf = namefn-pop p nf
  elt-namefn (conv-hide wf a p) nf = namefn-pop p nf
  elt-namefn (conv-unseal rep rd p na) nf = namefn-push nf na p
  elt-namefn (conv-show wf p na) nf = namefn-push nf na p
  elt-namefn (conv-fun s′ t′) nf = conv-namefn t′ nf
  elt-namefn (conv-all s′) nf =
    namefn-unbind (conv-namefn s′ (namefn-bind nf))

  conv-namefn : Sg ∣ Γ₁ ⊢ c ∶ A ⇝ B ⊣ Γ₂ → NameFn Γ₂ → NameFn Γ₁
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

-- Inversions: the element is in constructor form, so these match where
-- a direct pattern on the derivation would leave the unifier stuck on
-- two renames.
inv-show : ∀ {Γ₁ Γ₂ A B Y β}
  → Sg ∣ Γ₁ ⊢̂ show Y β ∶ A ⇝ B ⊣ Γ₂
  → (A ≡ renameᵗ (shiftAtᵗ Y) B) × (Γ₁ ▷ Y := β ⇒ Γ₂)
inv-show (conv-show wf p na) = refl , p

inv-hide : ∀ {Γ₁ Γ₂ A B X α}
  → Sg ∣ Γ₁ ⊢̂ hide X α ∶ A ⇝ B ⊣ Γ₂
  → (B ≡ renameᵗ (shiftAtᵗ X) A) × (Γ₂ ▷ X := α ⇒ Γ₁)
inv-hide (conv-hide wf a p) = refl , p

inv-seal : ∀ {Γ₁ Γ₂ A B X α}
  → Sg ∣ Γ₁ ⊢̂ seal X α ∶ A ⇝ B ⊣ Γ₂
  → Σ[ R ∈ RepTy ]
      ((B ≡ ` X) × (Sg ∣ Γ₂ ∋r α := R) × (Sg ∣ Γ₁ ⊢ R ⇓ A)
       × (Γ₂ ▷ X := α ⇒ Γ₁))
inv-seal (conv-seal rep rd p) = _ , refl , rep , rd , p

inv-unseal : ∀ {Γ₁ Γ₂ A B X α}
  → Sg ∣ Γ₁ ⊢̂ unseal X α ∶ A ⇝ B ⊣ Γ₂
  → Σ[ R ∈ RepTy ]
      ((A ≡ ` X) × (Sg ∣ Γ₁ ∋r α := R) × (Sg ∣ Γ₂ ⊢ R ⇓ B)
       × (Γ₁ ▷ X := α ⇒ Γ₂))
inv-unseal (conv-unseal rep rd p na) = _ , refl , rep , rd , p

-- seal α then unseal α
cancel-seal : ∀ {Γ₁ Γ₂ Γ₃ A B C X Y α}
  → Sg ∣ Γ₁ ⊢̂ seal X α ∶ A ⇝ B ⊣ Γ₂
  → Sg ∣ Γ₂ ⊢̂ unseal Y α ∶ B ⇝ C ⊣ Γ₃
  → NameFn Γ₃
  → (Γ₁ ≡ Γ₃) × (A ≡ C)
cancel-seal hd hd₂ nf with inv-seal hd | inv-unseal hd₂
cancel-seal hd hd₂ nf | R , refl , rep , rd , p | R′ , teq , rep′ , rd′ , q
  with pop-unique q p
cancel-seal hd hd₂ nf | R , refl , rep , rd , p | R′ , teq , rep′ , rd′ , q
  | refl , refl , refl with ∋r-unique rep′ rep
cancel-seal hd hd₂ nf | R , refl , rep , rd , p | R′ , teq , rep′ , rd′ , q
  | refl , refl , refl | refl = refl , read-unique nf rd rd′

-- hide α then show α
cancel-hide : ∀ {Γ₁ Γ₂ Γ₃ A B C X Y α}
  → Sg ∣ Γ₁ ⊢̂ hide X α ∶ A ⇝ B ⊣ Γ₂
  → Sg ∣ Γ₂ ⊢̂ show Y α ∶ B ⇝ C ⊣ Γ₃
  → (Γ₁ ≡ Γ₃) × (A ≡ C)
cancel-hide {A = A} {C = C} {X = X} hd hd₂ with inv-hide hd | inv-show hd₂
cancel-hide {A = A} {C = C} {X = X} hd hd₂ | refl , p | teq , q
  with pop-unique q p
cancel-hide {A = A} {C = C} {X = X} hd hd₂ | refl , p | teq , q
  | refl , refl , refl = refl , shiftAtᵗ-inj X A C teq
