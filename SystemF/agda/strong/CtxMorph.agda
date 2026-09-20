module strong.CtxMorph where

-- Strong System F -- experimental two-universe context morphisms.
--
-- A morphism remains a pair. Its `binds` are a parallel block of fresh
-- representation-variable binders. Its `changes` sequentially bind and
-- anti-bind ordinary type variables. Every change carries both the ordinary
-- de Bruijn position and the representation variable named at that position.

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (_≟_; +-cancelˡ-≡; +-identityʳ; ≤-trans; suc-injective)
open import Data.List using (List; []; _∷_; _++_; map; reverse; length)
open import Data.List.Properties using (unfold-reverse; map-++)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; ∃-syntax; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import strong.Types using (Ty; `ℕ; ⇑ᵗ; Renameᵗ; renameᵗ; extᵗ)
open import strong.Ctx

private
  variable
    Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ
    Ξ Ξ′ : RepCtx
    Δ Δ′ Δ₁ Δ₂ Δ₃ Δᵢ Δᶜ Δᵈ : TyCtx
    Rs : List Ty
    R : Ty
    b : RepBinding
    X : ℕ
    α β : RVar

------------------------------------------------------------------------
-- 1. Representation-variable binders
------------------------------------------------------------------------

shiftBy : ℕ → Ty → Ty
shiftBy zero    R = R
shiftBy (suc n) R = ⇑ᵗ (shiftBy n R)

-- The bind block is parallel: every payload is written over the exterior
-- representation context. Earlier entries are shifted past their list tail.
pushRepBinds : List Ty → RepCtx → RepCtx
pushRepBinds []       Ξ = Ξ
pushRepBinds (R ∷ Rs) Ξ =
  bindR (shiftBy (length Rs) R) ∷ pushRepBinds Rs Ξ

shiftRVars : ℕ → TyCtx → TyCtx
shiftRVars n = map (n +_)

extendReps : List Ty → Ctxᵗ → Ctxᵗ
extendReps Rs (Ξ ∣ Δ) =
  pushRepBinds Rs Ξ ∣ shiftRVars (length Rs) Δ

-- Every bind payload is checked over the SAME exterior representation
-- context. This is the morphism's parallel-bind discipline.
infix 4 _⊢ᴮ_
data _⊢ᴮ_ (Ξ : RepCtx) : List Ty → Set where
  binds[] : Ξ ⊢ᴮ []
  binds∷  : Ξ ⊢ᴿ R → Ξ ⊢ᴮ Rs → Ξ ⊢ᴮ R ∷ Rs

------------------------------------------------------------------------
-- 2. Ordinary-variable binders and anti-binders
------------------------------------------------------------------------

data Change : Set where
  lock   : ℕ → RVar → Change
  unlock : ℕ → RVar → Change

private
  variable
    δ : Change
    χ : List Change

infix 4 _⊢+_at_⇒_
data _⊢+_at_⇒_ (α : RVar) : TyCtx → ℕ → TyCtx → Set where
  ins-here  : α ⊢+ Δ at zero ⇒ α ∷ Δ
  ins-there : α ⊢+ Δ at X ⇒ Δ′
    → α ⊢+ β ∷ Δ at suc X ⇒ β ∷ Δ′

infix 4 _⊢-_at_⇒_
data _⊢-_at_⇒_ (α : RVar) : TyCtx → ℕ → TyCtx → Set where
  del-here  : α ⊢- α ∷ Δ at zero ⇒ Δ
  del-there : α ⊢- Δ at X ⇒ Δ′
    → α ⊢- β ∷ Δ at suc X ⇒ β ∷ Δ′

insert-functional : α ⊢+ Δ at X ⇒ Δ₁
  → α ⊢+ Δ at X ⇒ Δ₂
  → Δ₁ ≡ Δ₂
insert-functional ins-here ins-here = refl
insert-functional (ins-there i) (ins-there i′) =
  cong (_ ∷_) (insert-functional i i′)

delete-functional : α ⊢- Δ at X ⇒ Δ₁
  → α ⊢- Δ at X ⇒ Δ₂
  → Δ₁ ≡ Δ₂
delete-functional del-here del-here = refl
delete-functional (del-there d) (del-there d′) =
  cong (_ ∷_) (delete-functional d d′)

-- `lock` records freshness of the result and `unlock` demands freshness of
-- its input. Thus one representation variable never has two simultaneous
-- ordinary names, and the two changes are exact inverses. The Ξ index makes
-- the carried representation-variable occurrence well scoped.
infix 4 _∋ʳ_
_∋ʳ_ : RepCtx → RVar → Set
Ξ ∋ʳ α = ∃[ b ] Ξ ∋ˡ α := b

infix 4 _∣_⊢δ_⇒_
data _∣_⊢δ_⇒_ (Ξ : RepCtx) : TyCtx → Change → TyCtx → Set where
  step-lock : Ξ ∋ʳ α → α ⊢- Δ at X ⇒ Δ′ → Δ′ ∌ʳ α
    → Ξ ∣ Δ ⊢δ lock X α ⇒ Δ′
  step-unlock : Ξ ∋ʳ α → Δ ∌ʳ α → α ⊢+ Δ at X ⇒ Δ′
    → Ξ ∣ Δ ⊢δ unlock X α ⇒ Δ′

insert-delete : α ⊢- Δ at X ⇒ Δ′ → α ⊢+ Δ′ at X ⇒ Δ
insert-delete del-here = ins-here
insert-delete (del-there d) = ins-there (insert-delete d)

delete-insert : α ⊢+ Δ at X ⇒ Δ′ → α ⊢- Δ′ at X ⇒ Δ
delete-insert ins-here = del-here
delete-insert (ins-there i) = del-there (delete-insert i)

dualChange : Change → Change
dualChange (lock X α)   = unlock X α
dualChange (unlock X α) = lock X α

dual-step : Ξ ∣ Δ ⊢δ δ ⇒ Δ′
  → Ξ ∣ Δ′ ⊢δ dualChange δ ⇒ Δ
dual-step (step-lock valid d fresh) =
  step-unlock valid fresh (insert-delete d)
dual-step (step-unlock valid fresh i) =
  step-lock valid (delete-insert i) fresh

-- Changes retain the current design's head-LAST order: the tail acts first.
infix 4 _∣_⊢χ_⇒_
data _∣_⊢χ_⇒_ (Ξ : RepCtx)
  : TyCtx → List Change → TyCtx → Set where
  changes[] : Ξ ∣ Δ ⊢χ [] ⇒ Δ
  changes∷  : Ξ ∣ Δ₁ ⊢χ χ ⇒ Δ₂
    → Ξ ∣ Δ₂ ⊢δ δ ⇒ Δ₃
    → Ξ ∣ Δ₁ ⊢χ δ ∷ χ ⇒ Δ₃

change-functional : Ξ ∣ Δ ⊢δ δ ⇒ Δ₁
  → Ξ ∣ Δ ⊢δ δ ⇒ Δ₂
  → Δ₁ ≡ Δ₂
change-functional (step-lock valid d fresh)
                  (step-lock valid′ d′ fresh′) =
  delete-functional d d′
change-functional (step-unlock valid fresh i)
                  (step-unlock valid′ fresh′ i′) =
  insert-functional i i′

changes-functional : Ξ ∣ Δ ⊢χ χ ⇒ Δ₁
  → Ξ ∣ Δ ⊢χ χ ⇒ Δ₂
  → Δ₁ ≡ Δ₂
changes-functional changes[] changes[] = refl
changes-functional (changes∷ cs st) (changes∷ cs′ st′)
  with changes-functional cs cs′
changes-functional (changes∷ cs st) (changes∷ cs′ st′) | refl =
  change-functional st st′

dual : List Change → List Change
dual χ = map dualChange (reverse χ)

-- Move a change underneath `n` representation binders. Ordinary positions
-- do not move; only the carried representation-variable occurrence does.
underRepBinds : ℕ → Change → Change
underRepBinds n (lock X α)   = lock X (n + α)
underRepBinds n (unlock X α) = unlock X (n + α)

-- A REPRESENTATION-ONLY renaming of a change. The ordinary position is
-- untouched, which is what makes a rep-only weakening leave every
-- ordinary de Bruijn spelling in a term exactly where it was.
renᶠᴿ : Renameᵗ → Change → Change
renᶠᴿ ρʳ (lock X α)   = lock X (ρʳ α)
renᶠᴿ ρʳ (unlock X α) = unlock X (ρʳ α)

------------------------------------------------------------------------
-- 3. Context morphisms and their two induced contexts
------------------------------------------------------------------------

record CtxMorph : Set where
  constructor morph
  field
    binds   : List Ty
    changes : List Change
open CtxMorph public

numBinds : CtxMorph → ℕ
numBinds Θ = length (binds Θ)

-- The representation-only renaming of a morphism. Its bind payloads are
-- written over the EXTERIOR representation context, so they move by ρ;
-- its changes run INSIDE the bind block, so they move by `extN` of ρ at
-- the block's width.
renᴮᴿ : Renameᵗ → CtxMorph → CtxMorph
renᴮᴿ ρʳ Θ =
  morph (map (renameᵗ ρʳ) (binds Θ))
        (map (renᶠᴿ (extN (numBinds Θ) ρʳ)) (changes Θ))

-- A crossing argument is already inside the representation bind block of
-- the boundary it crosses. Its dual therefore binds no new representation
-- variables and simply reverses the ordinary-variable changes.
dualMorph : CtxMorph → CtxMorph
dualMorph Θ = morph [] (dual (changes Θ))

-- Rewind retains the bind block and performs the inverse changes before the
-- original changes. This is the syntax used by CancelR and IdPush.
rewind : CtxMorph → CtxMorph
rewind Θ = morph (binds Θ) (dual (changes Θ) ++ changes Θ)

-- Move the outer morphism's ordinary-variable effects into the inner one.
-- The outer binders already occur in the exterior of the resulting inner
-- boundary; the inner bind block shifts their representation occurrences.
infixl 5 _⋉_
_⋉_ : CtxMorph → CtxMorph → CtxMorph
Θ₁ ⋉ Θ₂ =
  morph (binds Θ₁)
        (changes Θ₁ ++ map (underRepBinds (numBinds Θ₁)) (changes Θ₂))

-- When a boundary crosses a fresh `Λ` binder, ordinary position zero names
-- the representation variable immediately outside its own bind prefix.
addLock0 : CtxMorph → CtxMorph
addLock0 Θ =
  morph (binds Θ) (changes Θ ++ (lock 0 (numBinds Θ) ∷ []))

-- Instantiation prepends a represented binder and gives it ordinary name 0.
-- The unlock acts first (head-LAST order); every pre-existing change then
-- moves past both the new ordinary name and the new representation binder.
private
  shiftChange : Change → Change
  shiftChange (lock X α)   = lock (suc X) (suc α)
  shiftChange (unlock X α) = unlock (suc X) (suc α)

instantiate : Ty → CtxMorph → CtxMorph
instantiate R Θ =
  morph (R ∷ binds Θ)
        (map shiftChange (changes Θ) ++ (unlock 0 0 ∷ []))

-- The interior performs every change.
infix 4 _⊢ⁱ_⇒_
data _⊢ⁱ_⇒_ (Γ : Ctxᵗ) (Θ : CtxMorph) : Ctxᵗ → Set where
  interior : ∀ {Δ′}
    → reps (extendReps (binds Θ) Γ)
      ∣ names (extendReps (binds Θ) Γ) ⊢χ changes Θ ⇒ Δ′
    → Γ ⊢ⁱ Θ ⇒ (reps (extendReps (binds Θ) Γ) ∣ Δ′)

-- The conversion context performs `unlock`s but skips `lock`s, so both the
-- concealed variable and its representation are available to the conversion.
-- It is therefore the UNION of the names live anywhere along the morphism,
-- not the name map at any one point of the run.
--
-- THE RE-UNLOCK CLAUSE (2026-09-17).  Reading it as a union forces a third
-- clause.  Skipping a `lock X α` leaves α live, so a LATER `unlock` of that
-- same α — the shape every `dualMorph`/`rewind` composite has, since a dual
-- inverts each lock with an unlock — meets a name that is already there and
-- the freshness premise of `conv-unlock` fails.  Without this clause
-- `rewind Θ` and `Θ′ ⋉ Θ` have NO conversion context whenever Θ locks, so
-- CancelR's and IdPush's contracta are untypeable: that is the wall the
-- fourth reduction example walked into (notes/RepresentationReductionExamples
-- §4, `no-rewind-conv` / `no-cancel-inner-conv`).
--
-- The clause does not widen the judgement where the old one applied: the two
-- unlock clauses are mutually exclusive (`fresh-not-lookup`), so the
-- conversion context stays a FUNCTION of the change list, which is what
-- determinism for CancelR/IdPush/TyPeelR-⟪⟫ consumes
-- (`conv-changes-functional`, `conversion-functional`).
--
-- WHY THE POSITION IS DROPPED.  `conv-lock` already ignores its position:
-- skipping the lock keeps α exactly where it was.  The paired unlock must
-- therefore keep it there too — re-inserting it at the interior position X
-- would move a name the conversion context never moved.  The positions of a
-- conversion context are the interior's positions with the locked names left
-- in place, and this clause is what makes that reading hold through a dual.
infix 4 _∣_⊢χᶜ_⇒_
data _∣_⊢χᶜ_⇒_ (Ξ : RepCtx)
  : TyCtx → List Change → TyCtx → Set where
  conv[] : Ξ ∣ Δ ⊢χᶜ [] ⇒ Δ
  conv-lock : Ξ ∋ʳ α → Ξ ∣ Δ₁ ⊢χᶜ χ ⇒ Δ₂
    → Ξ ∣ Δ₁ ⊢χᶜ lock X α ∷ χ ⇒ Δ₂
  conv-unlock : Ξ ∋ʳ α
    → Ξ ∣ Δ₁ ⊢χᶜ χ ⇒ Δ₂
    → Δ₂ ∌ʳ α
    → α ⊢+ Δ₂ at X ⇒ Δ₃
    → Ξ ∣ Δ₁ ⊢χᶜ unlock X α ∷ χ ⇒ Δ₃
  conv-unlock-live : ∀ {Y} → Ξ ∋ʳ α
    → Ξ ∣ Δ₁ ⊢χᶜ χ ⇒ Δ₂
    → Δ₂ ∋ˡ Y := α
    → Ξ ∣ Δ₁ ⊢χᶜ unlock X α ∷ χ ⇒ Δ₂

conv-changes-functional : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ₁
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ₂
  → Δ₁ ≡ Δ₂
conv-changes-functional conv[] conv[] = refl
conv-changes-functional (conv-lock valid cs) (conv-lock valid′ cs′) =
  conv-changes-functional cs cs′
conv-changes-functional (conv-unlock valid cs fresh i)
                        (conv-unlock valid′ cs′ fresh′ i′)
  with conv-changes-functional cs cs′
conv-changes-functional (conv-unlock valid cs fresh i)
                        (conv-unlock valid′ cs′ fresh′ i′) | refl =
  insert-functional i i′
conv-changes-functional (conv-unlock-live valid cs d)
                        (conv-unlock-live valid′ cs′ d′) =
  conv-changes-functional cs cs′
-- the mixed pairs are impossible: one says α is FRESH in the tail's
-- output, the other says α is LOOKED UP there.
conv-changes-functional (conv-unlock valid cs fresh i)
                        (conv-unlock-live valid′ cs′ d′)
  with conv-changes-functional cs cs′
... | refl = ⊥-elim (fresh-not-lookup fresh d′)
conv-changes-functional (conv-unlock-live valid cs d)
                        (conv-unlock valid′ cs′ fresh′ i′)
  with conv-changes-functional cs cs′
... | refl = ⊥-elim (fresh-not-lookup fresh′ d)

infix 4 _⊢ᶜ_⇒_
data _⊢ᶜ_⇒_ (Γ : Ctxᵗ) (Θ : CtxMorph) : Ctxᵗ → Set where
  conversion : ∀ {Δ′}
    → reps (extendReps (binds Θ) Γ)
      ∣ names (extendReps (binds Θ) Γ) ⊢χᶜ changes Θ ⇒ Δ′
    → Γ ⊢ᶜ Θ ⇒ (reps (extendReps (binds Θ) Γ) ∣ Δ′)

interior-functional : ∀ {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ → Γ ⊢ⁱ Θ ⇒ Γᶜ → Γᵢ ≡ Γᶜ
interior-functional (interior cs) (interior cs′) =
  cong (_ ∣_) (changes-functional cs cs′)

conversion-functional : ∀ {Θ : CtxMorph}
  → Γ ⊢ᶜ Θ ⇒ Γᵢ → Γ ⊢ᶜ Θ ⇒ Γᶜ → Γᵢ ≡ Γᶜ
conversion-functional (conversion cs) (conversion cs′) =
  cong (_ ∣_) (conv-changes-functional cs cs′)

------------------------------------------------------------------------
-- 3a. Transport across a morphism
------------------------------------------------------------------------

-- The two induced contexts are WELL FORMED whenever the exterior is and
-- the bind block checks. Each of `WfCtx`'s three fields transports
-- separately, and none of them needs the term or the conversion.

-- `Δ ∋ᵅ α`: α has an ordinary name in Δ.
infix 4 _∋ᵅ_
_∋ᵅ_ : TyCtx → RVar → Set
Δ ∋ᵅ α = ∃[ X ] Δ ∋ˡ X := α

∋ᵅ-cons : Δ ∋ᵅ α → (β ∷ Δ) ∋ᵅ α
∋ᵅ-cons (X , d) = suc X , there d

ins-live : α ⊢+ Δ at X ⇒ Δ′ → Δ′ ∋ᵅ α
ins-live ins-here = zero , here
ins-live (ins-there i) with ins-live i
ins-live (ins-there i) | X , d = suc X , there d

ins-mono : α ⊢+ Δ at X ⇒ Δ′ → Δ ∋ᵅ β → Δ′ ∋ᵅ β
ins-mono ins-here (X , d) = suc X , there d
ins-mono (ins-there i) (zero , here) = zero , here
ins-mono (ins-there i) (suc X , there d) with ins-mono i (X , d)
ins-mono (ins-there i) (suc X , there d) | Y , d′ = suc Y , there d′

-- A conversion reading only adds ordinary names: locks are skipped and an
-- unlock either inserts its representation variable or finds it already
-- live.  Preservation uses this to re-spell an exterior type in the
-- conversion context selected by the relational reading.
conversion-live : ∀ {Θ : CtxMorph}
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → (names (extendReps (binds Θ) Γ)) ∋ᵅ α
  → (names Γᶜ) ∋ᵅ α
conversion-live (conversion cs) lv = conv-live cs lv
  where
  conv-live : ∀ {Ξ Δ Δ′ χ α}
    → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → Δ ∋ᵅ α → Δ′ ∋ᵅ α
  conv-live conv[] live = live
  conv-live (conv-lock v css) live = conv-live css live
  conv-live (conv-unlock v css fr i) live = ins-mono i (conv-live css live)
  conv-live (conv-unlock-live v css d) live = conv-live css live

ins-inv : α ⊢+ Δ at X ⇒ Δ′ → Δ′ ∋ᵅ β → (β ≡ α) ⊎ Δ ∋ᵅ β
ins-inv ins-here (zero , here) = inj₁ refl
ins-inv ins-here (suc X , there d) = inj₂ (X , d)
ins-inv (ins-there i) (zero , here) = inj₂ (zero , here)
ins-inv (ins-there i) (suc X , there d) with ins-inv i (X , d)
ins-inv (ins-there i) (suc X , there d) | inj₁ eq = inj₁ eq
ins-inv (ins-there i) (suc X , there d) | inj₂ (Y , d′) =
  inj₂ (suc Y , there d′)

del-live : α ⊢- Δ at X ⇒ Δ′ → Δ ∋ᵅ α
del-live del-here = zero , here
del-live (del-there dl) with del-live dl
del-live (del-there dl) | X , d = suc X , there d

del-mono : α ⊢- Δ at X ⇒ Δ′ → β ≢ α → Δ ∋ᵅ β → Δ′ ∋ᵅ β
del-mono del-here ne (zero , here) = ⊥-elim (ne refl)
del-mono del-here ne (suc X , there d) = X , d
del-mono (del-there dl) ne (zero , here) = zero , here
del-mono (del-there dl) ne (suc X , there d) with del-mono dl ne (X , d)
del-mono (del-there dl) ne (suc X , there d) | Y , d′ = suc Y , there d′

del-inv : α ⊢- Δ at X ⇒ Δ′ → Δ′ ∋ᵅ β → Δ ∋ᵅ β
del-inv del-here (X , d) = suc X , there d
del-inv (del-there dl) (zero , here) = zero , here
del-inv (del-there dl) (suc X , there d) with del-inv dl (X , d)
del-inv (del-there dl) (suc X , there d) | Y , d′ = suc Y , there d′

-- Rewinding a morphism.

-- A rewound morphism performs the original changes and then their exact
-- inverse.  Its interior is therefore just the exterior under the original
-- bind block.  Its conversion context is the original conversion context:
-- locks are skipped in both halves, and each inverse unlock is a no-op
-- because the corresponding locked name is live in that union context.
-- The interior reading is the evidence for that last fact: a conversion
-- reading alone permits a `conv-lock` even when its name is absent.

private
  changes-++ : ∀ {Ξ Δ Δ′ Δ″ χ₁ χ₂}
    → Ξ ∣ Δ ⊢χ χ₂ ⇒ Δ′
    → Ξ ∣ Δ′ ⊢χ χ₁ ⇒ Δ″
    → Ξ ∣ Δ ⊢χ χ₁ ++ χ₂ ⇒ Δ″
  changes-++ cs₂ changes[] = cs₂
  changes-++ cs₂ (changes∷ cs₁ st) =
    changes∷ (changes-++ cs₂ cs₁) st

  conv-changes-++ : ∀ {Ξ Δ Δ′ Δ″ χ₁ χ₂}
    → Ξ ∣ Δ ⊢χᶜ χ₂ ⇒ Δ′
    → Ξ ∣ Δ′ ⊢χᶜ χ₁ ⇒ Δ″
    → Ξ ∣ Δ ⊢χᶜ χ₁ ++ χ₂ ⇒ Δ″
  conv-changes-++ cs₂ conv[] = cs₂
  conv-changes-++ cs₂ (conv-lock v cs₁) =
    conv-lock v (conv-changes-++ cs₂ cs₁)
  conv-changes-++ cs₂ (conv-unlock v cs₁ fr i) =
    conv-unlock v (conv-changes-++ cs₂ cs₁) fr i
  conv-changes-++ cs₂ (conv-unlock-live v cs₁ d) =
    conv-unlock-live v (conv-changes-++ cs₂ cs₁) d

  dual-∷ : (δ : Change) (χ : List Change)
    → dual (δ ∷ χ) ≡ dual χ ++ (dualChange δ ∷ [])
  dual-∷ δ χ rewrite unfold-reverse δ χ =
    map-++ dualChange (reverse χ) (δ ∷ [])

  dual-changes : ∀ {Ξ Δ Δ′ χ}
    → Ξ ∣ Δ ⊢χ χ ⇒ Δ′
    → Ξ ∣ Δ′ ⊢χ dual χ ⇒ Δ
  dual-changes changes[] = changes[]
  dual-changes {χ = δ ∷ χ} (changes∷ cs st) =
    subst (λ χ′ → _ ∣ _ ⊢χ χ′ ⇒ _)
          (sym (dual-∷ δ χ))
          (changes-++ (changes∷ changes[] (dual-step st))
                      (dual-changes cs))

  int⇒conv-live : ∀ {Ξ Δ Δᵢ Δᶜ χ α}
    → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
    → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
    → Δᵢ ∋ᵅ α
    → Δᶜ ∋ᵅ α
  int⇒conv-live changes[] conv[] lv = lv
  int⇒conv-live (changes∷ cs (step-lock v dl fr))
                (conv-lock v′ csᶜ) lv =
    int⇒conv-live cs csᶜ (del-inv dl lv)
  int⇒conv-live (changes∷ cs (step-unlock v fr i))
                (conv-unlock v′ csᶜ fr′ i′) lv with ins-inv i lv
  int⇒conv-live (changes∷ cs (step-unlock v fr i))
                (conv-unlock v′ csᶜ fr′ i′) lv | inj₁ refl =
    ins-live i′
  int⇒conv-live (changes∷ cs (step-unlock v fr i))
                (conv-unlock v′ csᶜ fr′ i′) lv | inj₂ lv′ =
    ins-mono i′ (int⇒conv-live cs csᶜ lv′)
  int⇒conv-live (changes∷ cs (step-unlock v fr i))
                (conv-unlock-live v′ csᶜ d) lv with ins-inv i lv
  int⇒conv-live (changes∷ cs (step-unlock v fr i))
                (conv-unlock-live v′ csᶜ d) lv | inj₁ refl = _ , d
  int⇒conv-live (changes∷ cs (step-unlock v fr i))
                (conv-unlock-live v′ csᶜ d) lv | inj₂ lv′ =
    int⇒conv-live cs csᶜ lv′

  conv-dual-id : ∀ {Ξ Δ Δᵢ Δᶜ Δ₀ χ}
    → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
    → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
    → (∀ {α} → Δᶜ ∋ᵅ α → Δ₀ ∋ᵅ α)
    → Ξ ∣ Δ₀ ⊢χᶜ dual χ ⇒ Δ₀
  conv-dual-id changes[] conv[] keep = conv[]
  conv-dual-id {χ = lock X α ∷ χ}
               (changes∷ cs (step-lock v dl fr))
               (conv-lock v′ csᶜ) keep
    with keep (int⇒conv-live cs csᶜ (del-live dl))
  conv-dual-id {χ = lock X α ∷ χ}
               (changes∷ cs (step-lock v dl fr))
               (conv-lock v′ csᶜ) keep | Y , d =
    subst (λ χ′ → _ ∣ _ ⊢χᶜ χ′ ⇒ _)
          (sym (dual-∷ (lock X α) χ))
          (conv-changes-++ (conv-unlock-live v conv[] d)
                           (conv-dual-id cs csᶜ keep))
  conv-dual-id {χ = unlock X α ∷ χ}
               (changes∷ cs (step-unlock v fr i))
               (conv-unlock v′ csᶜ fr′ i′) keep =
    subst (λ χ′ → _ ∣ _ ⊢χᶜ χ′ ⇒ _)
          (sym (dual-∷ (unlock X α) χ))
          (conv-changes-++ (conv-lock v conv[])
            (conv-dual-id cs csᶜ (λ lv → keep (ins-mono i′ lv))))
  conv-dual-id {χ = unlock X α ∷ χ}
               (changes∷ cs (step-unlock v fr i))
               (conv-unlock-live v′ csᶜ d) keep =
    subst (λ χ′ → _ ∣ _ ⊢χᶜ χ′ ⇒ _)
          (sym (dual-∷ (unlock X α) χ))
          (conv-changes-++ (conv-lock v conv[])
                           (conv-dual-id cs csᶜ keep))

  shiftNames-lookup : Δ ∋ˡ X := α → shiftNames Δ ∋ˡ X := suc α
  shiftNames-lookup here = here
  shiftNames-lookup (there d) = there (shiftNames-lookup d)

  valid-suc : Ξ ∋ʳ α → (b ∷ Ξ) ∋ʳ suc α
  valid-suc (b′ , d) = b′ , there d

  insert-shift : α ⊢+ Δ at X ⇒ Δ′
    → suc α ⊢+ shiftNames Δ at X ⇒ shiftNames Δ′
  insert-shift ins-here = ins-here
  insert-shift (ins-there i) = ins-there (insert-shift i)

  delete-shift : α ⊢- Δ at X ⇒ Δ′
    → suc α ⊢- shiftNames Δ at X ⇒ shiftNames Δ′
  delete-shift del-here = del-here
  delete-shift (del-there d) = del-there (delete-shift d)

  step-shift : Ξ ∣ Δ ⊢δ δ ⇒ Δ′
    → (b ∷ Ξ) ∣ (zero ∷ shiftNames Δ) ⊢δ shiftChange δ
        ⇒ (zero ∷ shiftNames Δ′)
  step-shift (step-lock valid d fresh) =
    step-lock (valid-suc valid) (del-there (delete-shift d))
      (fresh∷ (λ ()) (fresh-shift fresh))
  step-shift (step-unlock valid fresh i) =
    step-unlock (valid-suc valid)
      (fresh∷ (λ ()) (fresh-shift fresh))
      (ins-there (insert-shift i))

  changes-shift : Ξ ∣ Δ ⊢χ χ ⇒ Δ′
    → (b ∷ Ξ) ∣ (zero ∷ shiftNames Δ) ⊢χ map shiftChange χ
        ⇒ (zero ∷ shiftNames Δ′)
  changes-shift changes[] = changes[]
  changes-shift (changes∷ cs st) =
    changes∷ (changes-shift cs) (step-shift st)

  conv-changes-shift : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′
    → (b ∷ Ξ) ∣ (zero ∷ shiftNames Δ) ⊢χᶜ map shiftChange χ
        ⇒ (zero ∷ shiftNames Δ′)
  conv-changes-shift conv[] = conv[]
  conv-changes-shift (conv-lock valid cs) =
    conv-lock (valid-suc valid) (conv-changes-shift cs)
  conv-changes-shift (conv-unlock valid cs fresh i) =
    conv-unlock (valid-suc valid) (conv-changes-shift cs)
      (fresh∷ (λ ()) (fresh-shift fresh))
      (ins-there (insert-shift i))
  conv-changes-shift (conv-unlock-live valid cs d) =
    conv-unlock-live (valid-suc valid) (conv-changes-shift cs)
      (there (shiftNames-lookup d))

  shiftRVars-suc : (n : ℕ) (Δ : TyCtx)
    → shiftRVars (suc n) Δ ≡ shiftNames (shiftRVars n Δ)
  shiftRVars-suc n [] = refl
  shiftRVars-suc n (α ∷ Δ) =
    cong (suc (n + α) ∷_) (shiftRVars-suc n Δ)

-- Instantiating a morphism replaces the abstract context in which its
-- `∀` conversion body was read by a represented binder. The old changes
-- run underneath the fresh ordinary name, in both induced readings.
instantiate-interior : ∀ {R : Ty} {Γ Γᵢ : Ctxᵗ} {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ⁱ instantiate R Θ ⇒
      ((bindR (shiftBy (numBinds Θ) R) ∷ reps Γᵢ)
        ∣ (zero ∷ shiftNames (names Γᵢ)))
instantiate-interior {Γ = Ξ ∣ Δ} {Θ = morph Rs χ}
                     (interior cs) =
  interior
    (subst (λ Δ₀ →
             _ ∣ Δ₀ ⊢χ map shiftChange χ ++ (unlock 0 0 ∷ [])
               ⇒ (zero ∷ shiftNames _))
           (sym (shiftRVars-suc (length Rs) Δ))
           (changes-++
             (changes∷ changes[]
               (step-unlock (_ , here) fresh-zero-shift ins-here))
             (changes-shift cs)))

instantiate-conversion : ∀ {R : Ty} {Γ Γᶜ : Ctxᵗ} {Θ : CtxMorph}
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γ ⊢ᶜ instantiate R Θ ⇒
      ((bindR (shiftBy (numBinds Θ) R) ∷ reps Γᶜ)
        ∣ (zero ∷ shiftNames (names Γᶜ)))
instantiate-conversion {Γ = Ξ ∣ Δ} {Θ = morph Rs χ}
                       (conversion cs) =
  conversion
    (subst (λ Δ₀ →
             _ ∣ Δ₀ ⊢χᶜ map shiftChange χ ++ (unlock 0 0 ∷ [])
               ⇒ (zero ∷ shiftNames _))
           (sym (shiftRVars-suc (length Rs) Δ))
           (conv-changes-++
             (conv-unlock (_ , here) conv[] fresh-zero-shift ins-here)
             (conv-changes-shift cs)))

rewind-interior : ∀ {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ⁱ rewind Θ ⇒ extendReps (binds Θ) Γ
rewind-interior (interior cs) =
  interior (changes-++ cs (dual-changes cs))

rewind-conversion : ∀ {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γ ⊢ᶜ rewind Θ ⇒ Γᶜ
rewind-conversion (interior cs) (conversion csᶜ) =
  conversion (conv-changes-++ csᶜ (conv-dual-id cs csᶜ (λ lv → lv)))


-- (i) `name-fn`. A lock deletes and an unlock inserts a name its own
-- premise says is fresh, so both readings preserve uniqueness.
fresh→≢ : Δ ∌ʳ α → Δ ∋ᵅ β → β ≢ α
fresh→≢ (fresh∷ ne fr) (zero , here) = λ eq → ne (sym eq)
fresh→≢ (fresh∷ ne fr) (suc X , there d) = fresh→≢ fr (X , d)

del-fresh : α ⊢- Δ at X ⇒ Δ′ → Δ ∌ʳ β → Δ′ ∌ʳ β
del-fresh del-here (fresh∷ ne fr) = fr
del-fresh (del-there dl) (fresh∷ ne fr) = fresh∷ ne (del-fresh dl fr)

ins-fresh : α ⊢+ Δ at X ⇒ Δ′ → β ≢ α
  → Δ ∌ʳ β → Δ′ ∌ʳ β
ins-fresh ins-here ne fr = fresh∷ ne fr
ins-fresh (ins-there i) ne (fresh∷ ne′ fr) = fresh∷ ne′ (ins-fresh i ne fr)

del-unique : α ⊢- Δ at X ⇒ Δ′ → Unique Δ → Unique Δ′
del-unique del-here (unique∷ fr uq) = uq
del-unique (del-there dl) (unique∷ fr uq) =
  unique∷ (del-fresh dl fr) (del-unique dl uq)

ins-unique : α ⊢+ Δ at X ⇒ Δ′ → Δ ∌ʳ α
  → Unique Δ → Unique Δ′
ins-unique ins-here fr uq = unique∷ fr uq
ins-unique (ins-there i) (fresh∷ ne fr) (unique∷ fr′ uq) =
  unique∷ (ins-fresh i (λ eq → ne (sym eq)) fr′) (ins-unique i fr uq)

int-unique : Unique Δ → Ξ ∣ Δ ⊢χ χ ⇒ Δ′ → Unique Δ′
int-unique uq changes[] = uq
int-unique uq (changes∷ cs (step-lock v dl fr)) =
  del-unique dl (int-unique uq cs)
int-unique uq (changes∷ cs (step-unlock v fr i)) =
  ins-unique i fr (int-unique uq cs)

fresh-shiftRVars : (n : ℕ) → Δ ∌ʳ α → shiftRVars n Δ ∌ʳ n + α
fresh-shiftRVars n fresh[] = fresh[]
fresh-shiftRVars n (fresh∷ ne fr) =
  fresh∷ (λ eq → ne (+-cancelˡ-≡ n _ _ eq)) (fresh-shiftRVars n fr)

unique-shiftRVars : (n : ℕ) → Unique Δ → Unique (shiftRVars n Δ)
unique-shiftRVars n unique[] = unique[]
unique-shiftRVars n (unique∷ fr uq) =
  unique∷ (fresh-shiftRVars n fr) (unique-shiftRVars n uq)

shiftRVars-0 : (Δ : TyCtx) → shiftRVars 0 Δ ≡ Δ
shiftRVars-0 [] = refl
shiftRVars-0 (α ∷ Δ) = cong (α ∷_) (shiftRVars-0 Δ)

-- (ii) `wf-names`. Every name a reading leaves live is one the exterior
-- already had, shifted past the bind block, or one an `unlock` brought
-- in — and an unlock carries its own `Ξ ∋ʳ α` premise.
∋ˡ-push : (Rs : List Ty) → Ξ ∋ˡ α := b
  → pushRepBinds Rs Ξ ∋ˡ (length Rs + α) := b
∋ˡ-push [] d = d
∋ˡ-push (S ∷ Rs) d = there (∋ˡ-push Rs d)

∋ˡ-shiftRVars : (n : ℕ) (Δ : TyCtx) {γ : RVar} → shiftRVars n Δ ∋ˡ X := γ
  → ∃[ α ] ((Δ ∋ˡ X := α) × (γ ≡ n + α))
∋ˡ-shiftRVars n (α ∷ Δ) here = α , here , refl
∋ˡ-shiftRVars n (α ∷ Δ) (there d) with ∋ˡ-shiftRVars n Δ d
∋ˡ-shiftRVars n (α ∷ Δ) (there d) | β , d′ , eq = β , there d′ , eq

validNames-push : (Rs : List Ty) → ValidNames Ξ Δ
  → ValidNames (pushRepBinds Rs Ξ) (shiftRVars (length Rs) Δ)
validNames-push {Δ = Δ} Rs vn d
  with ∋ˡ-shiftRVars (length Rs) Δ d
validNames-push {Δ = Δ} Rs vn d | α , d′ , refl with vn d′
validNames-push {Δ = Δ} Rs vn d | α , d′ , refl | b , dr =
  b , ∋ˡ-push Rs dr

del-valid : α ⊢- Δ at X ⇒ Δ′ → ValidNames Ξ Δ → ValidNames Ξ Δ′
del-valid dl vn d = vn (proj₂ (del-inv dl (_ , d)))

ins-valid : α ⊢+ Δ at X ⇒ Δ′ → Ξ ∋ʳ α
  → ValidNames Ξ Δ → ValidNames Ξ Δ′
ins-valid i v vn d with ins-inv i (_ , d)
ins-valid i v vn d | inj₁ refl = v
ins-valid i v vn d | inj₂ lv = vn (proj₂ lv)

int-valid : ValidNames Ξ Δ → Ξ ∣ Δ ⊢χ χ ⇒ Δ′ → ValidNames Ξ Δ′
int-valid vn changes[] = vn
int-valid vn (changes∷ cs (step-lock v dl fr)) =
  del-valid dl (int-valid vn cs)
int-valid vn (changes∷ cs (step-unlock v fr i)) =
  ins-valid i v (int-valid vn cs)

-- The dual runs the same changes backwards, so its interior is the
-- exterior UNDER THE ORIGINAL BIND BLOCK: a crossing argument is already
-- inside the boundary's representation binders, and the dual returns it
-- to the ordinary name map the boundary was read on.  This is `Peel`'s
-- counterpart of `rewind-interior`, and it needs no `MorphWf` either.
dual-interior : ∀ {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γᵢ ⊢ⁱ dualMorph Θ ⇒ extendReps (binds Θ) Γ
dual-interior {Θ = Θ} (interior cs) =
  interior
    (subst (λ D → _ ∣ D ⊢χ dual (changes Θ) ⇒ _)
           (sym (shiftRVars-0 _))
           (dual-changes cs))

-- Lifting a reading past a PARALLEL BIND BLOCK.  `underRepBinds k` keeps
-- every ordinary POSITION and moves every representation occurrence past
-- k binders; `shiftRVars k` does the same to the name map.  This is what
-- `_⋉_` does to the outer morphism's change list.
private
  del-shiftRVars : (k : ℕ) → α ⊢- Δ at X ⇒ Δ′
    → (k + α) ⊢- shiftRVars k Δ at X ⇒ shiftRVars k Δ′
  del-shiftRVars k del-here = del-here
  del-shiftRVars k (del-there dl) = del-there (del-shiftRVars k dl)

  ins-shiftRVars : (k : ℕ) → α ⊢+ Δ at X ⇒ Δ′
    → (k + α) ⊢+ shiftRVars k Δ at X ⇒ shiftRVars k Δ′
  ins-shiftRVars k ins-here = ins-here
  ins-shiftRVars k (ins-there i) = ins-there (ins-shiftRVars k i)

  step-lift : (Rs : List Ty) → Ξ ∣ Δ ⊢δ δ ⇒ Δ′
    → pushRepBinds Rs Ξ ∣ shiftRVars (length Rs) Δ
        ⊢δ underRepBinds (length Rs) δ ⇒ shiftRVars (length Rs) Δ′
  step-lift Rs (step-lock (b , v) dl fr) =
    step-lock (b , ∋ˡ-push Rs v)
              (del-shiftRVars (length Rs) dl)
              (fresh-shiftRVars (length Rs) fr)
  step-lift Rs (step-unlock (b , v) fr i) =
    step-unlock (b , ∋ˡ-push Rs v)
                (fresh-shiftRVars (length Rs) fr)
                (ins-shiftRVars (length Rs) i)

  changes-lift : (Rs : List Ty) → Ξ ∣ Δ ⊢χ χ ⇒ Δ′
    → pushRepBinds Rs Ξ ∣ shiftRVars (length Rs) Δ
        ⊢χ map (underRepBinds (length Rs)) χ ⇒ shiftRVars (length Rs) Δ′
  changes-lift Rs changes[] = changes[]
  changes-lift Rs (changes∷ cs st) =
    changes∷ (changes-lift Rs cs) (step-lift Rs st)

-- The MERGED frame's interior is the inner frame's own interior.  The
-- lifted copy of the outer changes re-creates the outer interior one bind
-- block in, which is exactly where the inner morphism's reading starts.
-- This is the relational form of the old development's
-- `interior-⋉-rewind` equality (retired proof/MoveScope §4).
merged-interior : ∀ {Θ₁ Θ₂ : CtxMorph} {Γ₁ᵢ : Ctxᵗ}
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ
  → Γᵢ ⊢ⁱ Θ₁ ⇒ Γ₁ᵢ
  → extendReps (binds Θ₂) Γ ⊢ⁱ Θ₁ ⋉ Θ₂ ⇒ Γ₁ᵢ
merged-interior {Θ₁ = Θ₁} (interior cs₂) (interior cs₁) =
  interior (changes-++ (changes-lift (binds Θ₁) cs₂) cs₁)

-- A representation payload looked up THROUGH a bind block is the payload
-- shifted past that block.
∋ʳ-push : (Rs : List Ty) → Ξ ∋ʳ α := bindR R
  → pushRepBinds Rs Ξ ∋ʳ (length Rs + α) := bindR (shiftBy (length Rs) R)
∋ʳ-push [] d = d
∋ʳ-push (S ∷ Rs) d = r-there (∋ʳ-push Rs d)

-- The same fact for an ABSTRACT binding as well: only the payload of a
-- represented one actually moves, but a rep-only weakening has to carry
-- both, so state the shift on bindings rather than on payloads.
shiftByᵇ : ℕ → RepBinding → RepBinding
shiftByᵇ zero    b = b
shiftByᵇ (suc n) b = renRepBinding suc (shiftByᵇ n b)

shiftByᵇ-abstR : (n : ℕ) → shiftByᵇ n abstR ≡ abstR
shiftByᵇ-abstR zero    = refl
shiftByᵇ-abstR (suc n) = cong (renRepBinding suc) (shiftByᵇ-abstR n)

shiftByᵇ-bindR : (n : ℕ) (R : Ty)
  → shiftByᵇ n (bindR R) ≡ bindR (shiftBy n R)
shiftByᵇ-bindR zero    R = refl
shiftByᵇ-bindR (suc n) R = cong (renRepBinding suc) (shiftByᵇ-bindR n R)

∋ʳ-pushᵇ : (Rs : List Ty) → Ξ ∋ʳ α := b
  → pushRepBinds Rs Ξ ∋ʳ (length Rs + α) := shiftByᵇ (length Rs) b
∋ʳ-pushᵇ [] d = d
∋ʳ-pushᵇ (S ∷ Rs) d = r-there (∋ʳ-pushᵇ Rs d)

-- Both readings leave the REPRESENTATION context of the morphism's own
-- bind block; only the ordinary name map moves.
interior-reps : ∀ {Θ : CtxMorph} → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → reps Γᵢ ≡ pushRepBinds (binds Θ) (reps Γ)
interior-reps (interior cs) = refl

conversion-reps : ∀ {Θ : CtxMorph} → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → reps Γᶜ ≡ pushRepBinds (binds Θ) (reps Γ)
conversion-reps (conversion cs) = refl

-- (iii) `wf-reps`. Both readings leave the representation context alone,
-- so all that is needed is that the bind block itself is well formed
-- where it lands — each payload weakened past the block's own tail.
ref-suc : ∀ {n i} → Ξ ⊢ref[ n ] i → Ξ ⊢ref[ suc n ] suc i
ref-suc (local-ref lt) = local-ref (s≤s lt)
ref-suc (free-ref d) = free-ref d

ref-ext : ∀ {Ξ′ n m} {ρ : Renameᵗ}
  → (∀ {i} → Ξ ⊢ref[ n ] i → Ξ′ ⊢ref[ m ] ρ i)
  → ∀ {i} → Ξ ⊢ref[ suc n ] i → Ξ′ ⊢ref[ suc m ] extᵗ ρ i
ref-ext f (local-ref {i = zero} lt) = local-ref (s≤s z≤n)
ref-ext f (local-ref {i = suc j} (s≤s lt)) = ref-suc (f (local-ref lt))
ref-ext f (free-ref d) = ref-suc (f (free-ref d))

wfᴿ-rename : ∀ {Ξ′ n m} {ρ : Renameᵗ}
  → (∀ {i} → Ξ ⊢ref[ n ] i → Ξ′ ⊢ref[ m ] ρ i)
  → Ξ ⊢ᴿ[ n ] R → Ξ′ ⊢ᴿ[ m ] renameᵗ ρ R
wfᴿ-rename f (wfᴿ-var r) = wfᴿ-var (f r)
wfᴿ-rename f wfᴿ-ℕ = wfᴿ-ℕ
wfᴿ-rename f wfᴿ-𝔹 = wfᴿ-𝔹
wfᴿ-rename f (wfᴿ-⇒ a c) = wfᴿ-⇒ (wfᴿ-rename f a) (wfᴿ-rename f c)
wfᴿ-rename f (wfᴿ-∀ a) = wfᴿ-∀ (wfᴿ-rename (ref-ext f) a)

wfᴿ-⇑ : Ξ ⊢ᴿ R → (b ∷ Ξ) ⊢ᴿ ⇑ᵗ R
wfᴿ-⇑ {Ξ = Ξ} {b = b} w = wfᴿ-rename step w
  where
  step : ∀ {i} → Ξ ⊢ref[ 0 ] i → (b ∷ Ξ) ⊢ref[ 0 ] suc i
  step (local-ref ())
  step (free-ref d) = free-ref (there d)

wfᴿ-push : (Rs : List Ty) → Ξ ⊢ᴿ R
  → pushRepBinds Rs Ξ ⊢ᴿ shiftBy (length Rs) R
wfᴿ-push [] w = w
wfᴿ-push (S ∷ Rs) w = wfᴿ-⇑ (wfᴿ-push Rs w)

wfRepCtx-push : Ξ ⊢ᴮ Rs → WfRepCtx Ξ → WfRepCtx (pushRepBinds Rs Ξ)
wfRepCtx-push binds[] wr = wr
wfRepCtx-push (binds∷ {Rs = Rs} w bs) wr =
  wf-bindR (wfᴿ-push Rs w) (wfRepCtx-push bs wr)

-- The conversion reading preserves both, for the same reasons: it skips
-- locks, and an unlock either inserts a name its own premise says is
-- fresh (carrying its `Ξ ∋ʳ α` premise) or does nothing at all.
conv-unique : Unique Δ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → Unique Δ′
conv-unique uq conv[] = uq
conv-unique uq (conv-lock v cs) = conv-unique uq cs
conv-unique uq (conv-unlock v cs fr i) = ins-unique i fr (conv-unique uq cs)
conv-unique uq (conv-unlock-live v cs d) = conv-unique uq cs

conv-valid : ValidNames Ξ Δ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → ValidNames Ξ Δ′
conv-valid vn conv[] = vn
conv-valid vn (conv-lock v cs) = conv-valid vn cs
conv-valid vn (conv-unlock v cs fr i) = ins-valid i v (conv-valid vn cs)
conv-valid vn (conv-unlock-live v cs d) = conv-valid vn cs

-- The lifted readings preserve name-map functionality independently of the
-- other two `WfCtx` fields.  `dual-unique` is the instance needed when a
-- crossed argument is wrapped in a morphism's dual.
interior-unique : ∀ {Θ : CtxMorph}
  → Unique (names Γ) → Γ ⊢ⁱ Θ ⇒ Γᵢ → Unique (names Γᵢ)
interior-unique {Θ = Θ} uq (interior cs) =
  int-unique (unique-shiftRVars (numBinds Θ) uq) cs

conversion-unique : ∀ {Θ : CtxMorph}
  → Unique (names Γ) → Γ ⊢ᶜ Θ ⇒ Γᶜ → Unique (names Γᶜ)
conversion-unique {Θ = Θ} uq (conversion cs) =
  conv-unique (unique-shiftRVars (numBinds Θ) uq) cs

dual-unique : ∀ {Γ Γᵢ Γᵈ : Ctxᵗ} {Θ : CtxMorph}
  → Unique (names Γ)
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γᵢ ⊢ᶜ dualMorph Θ ⇒ Γᵈ
  → Unique (names Γᵈ)
dual-unique uq int dconv =
  conversion-unique (interior-unique uq int) dconv

------------------------------------------------------------------------
-- 3b. The name-set invariant for a crossed morphism
------------------------------------------------------------------------

-- `Peel` reads its domain conversion at a morphism's conversion context,
-- then uses a re-spelling of it at the dual's conversion context.  Those
-- contexts need not have the same name LIST, but they name the same
-- representation variables.  The following development was proved first in
-- notes/PeelPremise.agda; it lives here now because Progress needs the
-- general theorem, not just the note's concrete witness.

data InLocks (α : RVar) : List Change → Set where
  il-here  : ∀ {X χ} → InLocks α (lock X α ∷ χ)
  il-there : ∀ {δ χ} → InLocks α χ → InLocks α (δ ∷ χ)

data InUnlocks (α : RVar) : List Change → Set where
  iu-here  : ∀ {X χ} → InUnlocks α (unlock X α ∷ χ)
  iu-there : ∀ {δ χ} → InUnlocks α χ → InUnlocks α (δ ∷ χ)

inLocks? : (α : RVar) (χ : List Change) → Dec (InLocks α χ)
inLocks? α [] = no (λ ())
inLocks? α (unlock X β ∷ χ) with inLocks? α χ
inLocks? α (unlock X β ∷ χ) | yes il = yes (il-there il)
inLocks? α (unlock X β ∷ χ) | no nl =
  no (λ where (il-there il) → nl il)
inLocks? α (lock X β ∷ χ) with α ≟ β
inLocks? α (lock X β ∷ χ) | yes refl = yes il-here
inLocks? α (lock X β ∷ χ) | no ne with inLocks? α χ
inLocks? α (lock X β ∷ χ) | no ne | yes il = yes (il-there il)
inLocks? α (lock X β ∷ χ) | no ne | no nl =
  no (λ where il-here → ne refl
              (il-there il) → nl il)

conv-mono : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → Δ ∋ᵅ α → Δ′ ∋ᵅ α
conv-mono conv[] lv = lv
conv-mono (conv-lock v cs) lv = conv-mono cs lv
conv-mono (conv-unlock v cs fr i) lv = ins-mono i (conv-mono cs lv)
conv-mono (conv-unlock-live v cs d) lv = conv-mono cs lv

conv-unlocks : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′
  → InUnlocks α χ → Δ′ ∋ᵅ α
conv-unlocks (conv-lock v cs) (iu-there iu) = conv-unlocks cs iu
conv-unlocks (conv-unlock v cs fr i) iu-here = ins-live i
conv-unlocks (conv-unlock v cs fr i) (iu-there iu) =
  ins-mono i (conv-unlocks cs iu)
conv-unlocks (conv-unlock-live v cs d) iu-here = _ , d
conv-unlocks (conv-unlock-live v cs d) (iu-there iu) =
  conv-unlocks cs iu

conv-inv : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → Δ′ ∋ᵅ α
  → Δ ∋ᵅ α ⊎ InUnlocks α χ
conv-inv conv[] lv = inj₁ lv
conv-inv (conv-lock v cs) lv with conv-inv cs lv
conv-inv (conv-lock v cs) lv | inj₁ l = inj₁ l
conv-inv (conv-lock v cs) lv | inj₂ iu = inj₂ (iu-there iu)
conv-inv (conv-unlock v cs fr i) lv with ins-inv i lv
conv-inv (conv-unlock v cs fr i) lv | inj₁ refl = inj₂ iu-here
conv-inv (conv-unlock v cs fr i) lv | inj₂ lv′ with conv-inv cs lv′
conv-inv (conv-unlock v cs fr i) lv | inj₂ lv′ | inj₁ l = inj₁ l
conv-inv (conv-unlock v cs fr i) lv | inj₂ lv′ | inj₂ iu =
  inj₂ (iu-there iu)
conv-inv (conv-unlock-live v cs d) lv with conv-inv cs lv
conv-inv (conv-unlock-live v cs d) lv | inj₁ l = inj₁ l
conv-inv (conv-unlock-live v cs d) lv | inj₂ iu = inj₂ (iu-there iu)

int-keep : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → ¬ InLocks α χ → Δ ∋ᵅ α → Δᵢ ∋ᵅ α
int-keep changes[] nl lv = lv
int-keep (changes∷ cs (step-lock v dl fr)) nl lv =
  del-mono dl (λ where refl → nl il-here)
           (int-keep cs (λ il → nl (il-there il)) lv)
int-keep (changes∷ cs (step-unlock v fr i)) nl lv =
  ins-mono i (int-keep cs (λ il → nl (il-there il)) lv)

int-unlocked : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → ¬ InLocks α χ
  → InUnlocks α χ → Δᵢ ∋ᵅ α
int-unlocked (changes∷ cs (step-lock v dl fr)) nl (iu-there iu) =
  del-mono dl (λ where refl → nl il-here)
           (int-unlocked cs (λ il → nl (il-there il)) iu)
int-unlocked (changes∷ cs (step-unlock v fr i)) nl iu-here = ins-live i
int-unlocked (changes∷ cs (step-unlock v fr i)) nl (iu-there iu) =
  ins-mono i (int-unlocked cs (λ il → nl (il-there il)) iu)

int-inv : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → Δᵢ ∋ᵅ α
  → Δ ∋ᵅ α ⊎ InUnlocks α χ
int-inv changes[] lv = inj₁ lv
int-inv (changes∷ cs (step-lock v dl fr)) lv
  with int-inv cs (del-inv dl lv)
int-inv (changes∷ cs (step-lock v dl fr)) lv | inj₁ l = inj₁ l
int-inv (changes∷ cs (step-lock v dl fr)) lv | inj₂ iu =
  inj₂ (iu-there iu)
int-inv (changes∷ cs (step-unlock v fr i)) lv with ins-inv i lv
int-inv (changes∷ cs (step-unlock v fr i)) lv | inj₁ refl = inj₂ iu-here
int-inv (changes∷ cs (step-unlock v fr i)) lv | inj₂ lv′
  with int-inv cs lv′
int-inv (changes∷ cs (step-unlock v fr i)) lv | inj₂ lv′ | inj₁ l =
  inj₁ l
int-inv (changes∷ cs (step-unlock v fr i)) lv | inj₂ lv′ | inj₂ iu =
  inj₂ (iu-there iu)

int-locked : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → InLocks α χ
  → Δ ∋ᵅ α ⊎ InUnlocks α χ
int-locked (changes∷ cs (step-lock v dl fr)) il-here
  with int-inv cs (del-live dl)
int-locked (changes∷ cs (step-lock v dl fr)) il-here | inj₁ l = inj₁ l
int-locked (changes∷ cs (step-lock v dl fr)) il-here | inj₂ iu =
  inj₂ (iu-there iu)
int-locked (changes∷ cs (step-lock v dl fr)) (il-there il)
  with int-locked cs il
int-locked (changes∷ cs (step-lock v dl fr)) (il-there il) | inj₁ l =
  inj₁ l
int-locked (changes∷ cs (step-lock v dl fr)) (il-there il) | inj₂ iu =
  inj₂ (iu-there iu)
int-locked (changes∷ cs (step-unlock v fr i)) (il-there il)
  with int-locked cs il
int-locked (changes∷ cs (step-unlock v fr i)) (il-there il) | inj₁ l =
  inj₁ l
int-locked (changes∷ cs (step-unlock v fr i)) (il-there il) | inj₂ iu =
  inj₂ (iu-there iu)

in-unlocks-++ˡ : ∀ {χ₂} → InUnlocks α χ → InUnlocks α (χ ++ χ₂)
in-unlocks-++ˡ iu-here = iu-here
in-unlocks-++ˡ (iu-there iu) = iu-there (in-unlocks-++ˡ iu)

in-unlocks-++ʳ : ∀ {χ₂} (χ₁ : List Change)
  → InUnlocks α χ₂ → InUnlocks α (χ₁ ++ χ₂)
in-unlocks-++ʳ [] iu = iu
in-unlocks-++ʳ (δ ∷ χ₁) iu = iu-there (in-unlocks-++ʳ χ₁ iu)

in-unlocks-++-inv : ∀ {χ₂} (χ₁ : List Change)
  → InUnlocks α (χ₁ ++ χ₂)
  → InUnlocks α χ₁ ⊎ InUnlocks α χ₂
in-unlocks-++-inv [] iu = inj₂ iu
in-unlocks-++-inv (unlock X β ∷ χ₁) iu-here = inj₁ iu-here
in-unlocks-++-inv (unlock X β ∷ χ₁) (iu-there iu)
  with in-unlocks-++-inv χ₁ iu
in-unlocks-++-inv (unlock X β ∷ χ₁) (iu-there iu) | inj₁ a =
  inj₁ (iu-there a)
in-unlocks-++-inv (unlock X β ∷ χ₁) (iu-there iu) | inj₂ b = inj₂ b
in-unlocks-++-inv (lock X β ∷ χ₁) (iu-there iu)
  with in-unlocks-++-inv χ₁ iu
in-unlocks-++-inv (lock X β ∷ χ₁) (iu-there iu) | inj₁ a =
  inj₁ (iu-there a)
in-unlocks-++-inv (lock X β ∷ χ₁) (iu-there iu) | inj₂ b = inj₂ b

locks→dual : (χ : List Change) → InLocks α χ → InUnlocks α (dual χ)
locks→dual (lock X β ∷ χ) il-here
  rewrite unfold-reverse (lock X β) χ
        | map-++ dualChange (reverse χ) (lock X β ∷ []) =
  in-unlocks-++ʳ (dual χ) iu-here
locks→dual (lock X β ∷ χ) (il-there il)
  rewrite unfold-reverse (lock X β) χ
        | map-++ dualChange (reverse χ) (lock X β ∷ []) =
  in-unlocks-++ˡ (locks→dual χ il)
locks→dual (unlock X β ∷ χ) (il-there il)
  rewrite unfold-reverse (unlock X β) χ
        | map-++ dualChange (reverse χ) (unlock X β ∷ []) =
  in-unlocks-++ˡ (locks→dual χ il)

dual→locks : (χ : List Change) → InUnlocks α (dual χ) → InLocks α χ
dual→locks [] ()
dual→locks (lock X β ∷ χ) iu
  rewrite unfold-reverse (lock X β) χ
        | map-++ dualChange (reverse χ) (lock X β ∷ [])
  with in-unlocks-++-inv (dual χ) iu
dual→locks (lock X β ∷ χ) iu | inj₁ a = il-there (dual→locks χ a)
dual→locks (lock X β ∷ χ) iu | inj₂ iu-here = il-here
dual→locks (unlock X β ∷ χ) iu
  rewrite unfold-reverse (unlock X β) χ
        | map-++ dualChange (reverse χ) (unlock X β ∷ [])
  with in-unlocks-++-inv (dual χ) iu
dual→locks (unlock X β ∷ χ) iu | inj₁ a = il-there (dual→locks χ a)
dual→locks (unlock X β ∷ χ) iu | inj₂ (iu-there ())

Q-changes : (χ : List Change)
  → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Ξ′ ∣ Δᵢ ⊢χᶜ dual χ ⇒ Δᵈ
  → Δᶜ ∋ᵅ α → Δᵈ ∋ᵅ α
Q-changes {α = α} χ int conv dconv lv with inLocks? α χ
Q-changes {α = α} χ int conv dconv lv | yes il =
  conv-unlocks dconv (locks→dual χ il)
Q-changes {α = α} χ int conv dconv lv | no nl with conv-inv conv lv
Q-changes {α = α} χ int conv dconv lv | no nl | inj₁ l =
  conv-mono dconv (int-keep int nl l)
Q-changes {α = α} χ int conv dconv lv | no nl | inj₂ iu =
  conv-mono dconv (int-unlocked int nl iu)

Q-changes-conv : (χ : List Change)
  → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Ξ′ ∣ Δᵢ ⊢χᶜ dual χ ⇒ Δᵈ
  → Δᵈ ∋ᵅ α → Δᶜ ∋ᵅ α
Q-changes-conv χ int conv dconv lv with conv-inv dconv lv
Q-changes-conv χ int conv dconv lv | inj₁ lvᵢ with int-inv int lvᵢ
Q-changes-conv χ int conv dconv lv | inj₁ lvᵢ | inj₁ l = conv-mono conv l
Q-changes-conv χ int conv dconv lv | inj₁ lvᵢ | inj₂ iu =
  conv-unlocks conv iu
Q-changes-conv χ int conv dconv lv | inj₂ iud
  with int-locked int (dual→locks χ iud)
Q-changes-conv χ int conv dconv lv | inj₂ iud | inj₁ l = conv-mono conv l
Q-changes-conv χ int conv dconv lv | inj₂ iud | inj₂ iu =
  conv-unlocks conv iu

-- (Q): the two conversion contexts straddled by `Peel` name the same
-- representation variables, although their ordinary positions may differ.
Q : ∀ {Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ} {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γᵢ ⊢ᶜ dualMorph Θ ⇒ Γᵈ
  → (names Γᶜ) ∋ᵅ α → (names Γᵈ) ∋ᵅ α
Q {Θ = Θ} (interior cs) (conversion cc) (conversion dc) lv =
  Q-changes (changes Θ) cs cc
    (subst (λ D → _ ∣ D ⊢χᶜ dual (changes Θ) ⇒ _)
           (shiftRVars-0 _) dc)
    lv

Q-inv : ∀ {Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ} {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γᵢ ⊢ᶜ dualMorph Θ ⇒ Γᵈ
  → (names Γᵈ) ∋ᵅ α → (names Γᶜ) ∋ᵅ α
Q-inv {Θ = Θ} (interior cs) (conversion cc) (conversion dc) lv =
  Q-changes-conv (changes Θ) cs cc
    (subst (λ D → _ ∣ D ⊢χᶜ dual (changes Θ) ⇒ _)
           (shiftRVars-0 _) dc)
    lv

live-shift : Δ ∋ᵅ α → (shiftNames Δ) ∋ᵅ (suc α)
live-shift (zero , here) = zero , here
live-shift (suc X , there d) with live-shift (X , d)
live-shift (suc X , there d) | Y , d′ = suc Y , there d′

live-shift-inv : (Δ : TyCtx) → (shiftNames Δ) ∋ᵅ α
  → ∃[ β ] (Δ ∋ᵅ β × (α ≡ suc β))
live-shift-inv (γ ∷ Δ) (zero , here) = γ , (zero , here) , refl
live-shift-inv (γ ∷ Δ) (suc X , there d) with live-shift-inv Δ (X , d)
live-shift-inv (γ ∷ Δ) (suc X , there d) | β , lv , eq =
  β , ∋ᵅ-cons lv , eq

infix 4 _⊆ᵃ_
_⊆ᵃ_ : TyCtx → TyCtx → Set
Δ ⊆ᵃ Δ′ = ∀ {α} → Δ ∋ᵅ α → Δ′ ∋ᵅ α

⊆ᵃ-underΛ : Δ ⊆ᵃ Δ′
  → (zero ∷ shiftNames Δ) ⊆ᵃ (zero ∷ shiftNames Δ′)
⊆ᵃ-underΛ f (zero , here) = zero , here
⊆ᵃ-underΛ {Δ = Δ} f (suc X , there d) with live-shift-inv Δ (X , d)
⊆ᵃ-underΛ {Δ = Δ} f (suc X , there d) | β , lv , refl =
  ∋ᵅ-cons (live-shift (f lv))

------------------------------------------------------------------------
-- 3c. The dual conversion context exists
------------------------------------------------------------------------

live? : (α : RVar) (Δ : TyCtx) → Δ ∋ᵅ α ⊎ Δ ∌ʳ α
live? α [] = inj₂ fresh[]
live? α (β ∷ Δ) with α ≟ β
live? α (β ∷ Δ) | yes refl = inj₁ (zero , here)
live? α (β ∷ Δ) | no ne with live? α Δ
live? α (β ∷ Δ) | no ne | inj₁ lv = inj₁ (∋ᵅ-cons lv)
live? α (β ∷ Δ) | no ne | inj₂ fr = inj₂ (fresh∷ ne fr)

del-length : α ⊢- Δ at X ⇒ Δ′ → length Δ ≡ suc (length Δ′)
del-length del-here = refl
del-length (del-there dl) = cong suc (del-length dl)

del-lt : α ⊢- Δ at X ⇒ Δ′ → suc X ≤ length Δ
del-lt del-here = s≤s z≤n
del-lt (del-there dl) = s≤s (del-lt dl)

lookup→del : Δ ∋ˡ X := α → ∃[ Δ′ ] (α ⊢- Δ at X ⇒ Δ′)
lookup→del here = _ , del-here
lookup→del (there d) with lookup→del d
lookup→del (there d) | Δ′ , dl = _ , del-there dl

ins-exists : (Δ : TyCtx) (X : ℕ) → X ≤ length Δ
  → ∃[ Δ′ ] (α ⊢+ Δ at X ⇒ Δ′)
ins-exists Δ zero le = _ , ins-here
ins-exists (β ∷ Δ) (suc X) (s≤s le) with ins-exists Δ X le
ins-exists (β ∷ Δ) (suc X) (s≤s le) | Δ′ , i =
  β ∷ Δ′ , ins-there i

pigeon : (xs ys : TyCtx) → Unique xs → xs ⊆ᵃ ys
  → length xs ≤ length ys
pigeon [] ys uq k = z≤n
pigeon (α ∷ xs) ys (unique∷ fr uq) k with k (zero , here)
pigeon (α ∷ xs) ys (unique∷ fr uq) k | X , d with lookup→del d
pigeon (α ∷ xs) ys (unique∷ fr uq) k | X , d | ys′ , dl =
  subst (λ n → suc (length xs) ≤ n) (sym (del-length dl))
        (s≤s (pigeon xs ys′ uq k′))
  where
  k′ : xs ⊆ᵃ ys′
  k′ lv = del-mono dl (fresh→≢ fr lv) (k (∋ᵅ-cons lv))

ins-le : α ⊢+ Δ at X ⇒ Δ′ → X ≤ length Δ
ins-le ins-here = z≤n
ins-le (ins-there i) = s≤s (ins-le i)

ins-cover : ∀ {Δ₀} → α ⊢+ Δ at X ⇒ Δ′ → Δ₀ ∋ᵅ α
  → Δ ⊆ᵃ Δ₀ → Δ′ ⊆ᵃ Δ₀
ins-cover i live k lv with ins-inv i lv
ins-cover i live k lv | inj₁ refl = live
ins-cover i live k lv | inj₂ lv′ = k lv′

-- A conversion reading is monotone in its starting name set.  Locks are
-- skipped; an unlock either finds its name already live in the larger set or
-- inserts it at the same position.  The old output therefore remains
-- available, although its ordinary positions may change.  This is the
-- lock-skipping transport needed when `addLock0` carries a boundary across a
-- newly inserted name.
conv-weaken : ∀ {Δ₀ χ} → Unique Δ → Unique Δ₀
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′
  → Δ ⊆ᵃ Δ₀
  → ∃[ Δ₀′ ] ((Ξ ∣ Δ₀ ⊢χᶜ χ ⇒ Δ₀′) × (Δ′ ⊆ᵃ Δ₀′))
conv-weaken uq uq₀ conv[] keep = _ , conv[] , keep
conv-weaken uq uq₀ (conv-lock v cs) keep with conv-weaken uq uq₀ cs keep
conv-weaken uq uq₀ (conv-lock v cs) keep | Δ₀′ , cs′ , keep′ =
  Δ₀′ , conv-lock v cs′ , keep′
conv-weaken uq uq₀ (conv-unlock v cs fr i) keep
  with conv-weaken uq uq₀ cs keep
conv-weaken uq uq₀ (conv-unlock v cs fr i) keep
  | Δ₀′ , cs′ , keep′ with live? _ Δ₀′
conv-weaken uq uq₀ (conv-unlock v cs fr i) keep
  | Δ₀′ , cs′ , keep′ | inj₁ live =
  Δ₀′ , conv-unlock-live v cs′ (proj₂ live)
        , ins-cover i live keep′
conv-weaken uq uq₀ (conv-unlock v cs fr i) keep
  | Δ₀′ , cs′ , keep′ | inj₂ fresh
  with ins-exists Δ₀′ _
         (≤-trans (ins-le i) (pigeon _ _ (conv-unique uq cs) keep′))
conv-weaken uq uq₀ (conv-unlock v cs fr i) keep
  | Δ₀′ , cs′ , keep′ | inj₂ fresh | Δ₀″ , i′ =
  Δ₀″ , conv-unlock v cs′ fresh i′
        , ins-cover i (ins-live i′) (λ lv → ins-mono i′ (keep′ lv))
conv-weaken uq uq₀ (conv-unlock-live v cs d) keep
  with conv-weaken uq uq₀ cs keep
conv-weaken uq uq₀ (conv-unlock-live v cs d) keep
  | Δ₀′ , cs′ , keep′ =
  Δ₀′ , conv-unlock-live v cs′ (proj₂ (keep′ (_ , d))) , keep′

-- Appending a lock makes it run first, and a conversion reading skips it.
conv-snoc-lock : Ξ ∋ʳ α → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′
  → Ξ ∣ Δ ⊢χᶜ χ ++ (lock X α ∷ []) ⇒ Δ′
conv-snoc-lock v conv[] = conv-lock v conv[]
conv-snoc-lock v (conv-lock w cs) = conv-lock w (conv-snoc-lock v cs)
conv-snoc-lock v (conv-unlock w cs fr i) =
  conv-unlock w (conv-snoc-lock v cs) fr i
conv-snoc-lock v (conv-unlock-live w cs d) =
  conv-unlock-live w (conv-snoc-lock v cs) d

sucle : ∀ {a b} → suc a ≤ suc b → a ≤ b
sucle (s≤s le) = le

keeps-del : ∀ {Δ₀} → α ⊢- Δ at X ⇒ Δ′ → Δ₀ ∋ᵅ α
  → Δ′ ⊆ᵃ Δ₀ → Δ ⊆ᵃ Δ₀
keeps-del {α = α} dl lvα k {β} lv with β ≟ α
keeps-del {α = α} dl lvα k {β} lv | yes refl = lvα
keeps-del {α = α} dl lvα k {β} lv | no ne = k (del-mono dl ne lv)

dual-conv-exists : (χ : List Change) {Δ Δᵢ : TyCtx} (Δ₀ : TyCtx)
  → Unique Δ → Unique Δ₀
  → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → Δᵢ ⊆ᵃ Δ₀
  → ∃[ Δᵈ ] (Ξ ∣ Δ₀ ⊢χᶜ dual χ ⇒ Δᵈ)
dual-conv-exists [] Δ₀ uqΔ uq₀ changes[] k = Δ₀ , conv[]
dual-conv-exists (unlock X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-unlock v fr i)) k
  with dual-conv-exists χ Δ₀ uqΔ uq₀ cs (λ lv → k (ins-mono i lv))
dual-conv-exists (unlock X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-unlock v fr i)) k | Δᵈ , dc =
  Δᵈ , subst (λ l → _ ∣ Δ₀ ⊢χᶜ l ⇒ Δᵈ)
             (sym (dual-∷ (unlock X α) χ))
             (conv-changes-++ (conv-lock v conv[]) dc)
dual-conv-exists (lock X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-lock v dl fr)) k with live? α Δ₀
dual-conv-exists (lock X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-lock v dl fr)) k | inj₁ (Y , d)
  with dual-conv-exists χ Δ₀ uqΔ uq₀ cs (keeps-del dl (Y , d) k)
dual-conv-exists (lock X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-lock v dl fr)) k | inj₁ (Y , d)
                 | Δᵈ , dc =
  Δᵈ , subst (λ l → _ ∣ Δ₀ ⊢χᶜ l ⇒ Δᵈ)
             (sym (dual-∷ (lock X α) χ))
             (conv-changes-++ (conv-unlock-live v conv[] d) dc)
dual-conv-exists (lock X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-lock v dl fr)) k | inj₂ frα
  with ins-exists {α = α} Δ₀ X
         (sucle (≤-trans (del-lt dl)
                         (pigeon _ (α ∷ Δ₀) (int-unique uqΔ cs)
                                 (keeps-del dl (zero , here)
                                            (λ lv → ∋ᵅ-cons (k lv))))))
dual-conv-exists (lock X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-lock v dl fr)) k | inj₂ frα | Δ₁ , i
  with dual-conv-exists χ Δ₁ uqΔ (ins-unique i frα uq₀) cs
         (keeps-del dl (ins-live i) (λ lv → ins-mono i (k lv)))
dual-conv-exists (lock X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-lock v dl fr)) k | inj₂ frα | Δ₁ , i
                 | Δᵈ , dc =
  Δᵈ , subst (λ l → _ ∣ Δ₀ ⊢χᶜ l ⇒ Δᵈ)
             (sym (dual-∷ (lock X α) χ))
             (conv-changes-++ (conv-unlock v conv[] frα i) dc)

dual-conversion-exists : ∀ {Γ Γᵢ : Ctxᵗ} {Θ : CtxMorph}
  → Unique (names Γ)
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → ∃[ Γᵈ ] (Γᵢ ⊢ᶜ dualMorph Θ ⇒ Γᵈ)
dual-conversion-exists {Θ = Θ} uq (interior cs)
  with dual-conv-exists (changes Θ) _ (unique-shiftRVars _ uq)
         (int-unique (unique-shiftRVars _ uq) cs) cs (λ lv → lv)
dual-conversion-exists {Θ = Θ} uq (interior cs) | Δᵈ , dc =
  _ , conversion
        (subst (λ D → _ ∣ D ⊢χᶜ dual (changes Θ) ⇒ Δᵈ)
               (sym (shiftRVars-0 _)) dc)

-- THE TWO TRANSPORT THEOREMS.  These are what `MorphWf` used to take as
-- explicit obligations.
interior-wf : ∀ {Θ : CtxMorph} → WfCtx Γ → reps Γ ⊢ᴮ binds Θ
  → Γ ⊢ⁱ Θ ⇒ Γᵢ → WfCtx Γᵢ
interior-wf {Θ = Θ} w bs (interior cs) =
  wf-ctx (wfRepCtx-push bs (wf-reps w))
         (int-valid (validNames-push (binds Θ) (wf-names w)) cs)
         (int-unique (unique-shiftRVars _ (name-fn w)) cs)

conversion-wf : ∀ {Θ : CtxMorph} → WfCtx Γ → reps Γ ⊢ᴮ binds Θ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ → WfCtx Γᶜ
conversion-wf {Θ = Θ} w bs (conversion cs) =
  wf-ctx (wfRepCtx-push bs (wf-reps w))
         (conv-valid (validNames-push (binds Θ) (wf-names w)) cs)
         (conv-unique (unique-shiftRVars _ (name-fn w)) cs)

-- A complete morphism witness names both induced contexts. The output
-- well-formedness is DERIVED (§3a), not stored: a witness carries only
-- what cannot be recovered — the exterior's well-formedness, the bind
-- block, and the two readings.
record MorphWf (Γ : Ctxᵗ) (Θ : CtxMorph)
               (Γᵢ Γᶜ : Ctxᵗ) : Set where
  constructor mw
  field
    mw-exterior  : WfCtx Γ
    mw-binds     : reps Γ ⊢ᴮ binds Θ
    mw-interior  : Γ ⊢ⁱ Θ ⇒ Γᵢ
    mw-conversion : Γ ⊢ᶜ Θ ⇒ Γᶜ
open MorphWf public

-- The two former fields, now theorems. They keep the names they had, so
-- every USE site reads the same; only the construction sites shrink.
mw-interior-wf : ∀ {Θ} → MorphWf Γ Θ Γᵢ Γᶜ → WfCtx Γᵢ
mw-interior-wf mwΘ =
  interior-wf (mw-exterior mwΘ) (mw-binds mwΘ) (mw-interior mwΘ)

mw-conversion-wf : ∀ {Θ} → MorphWf Γ Θ Γᵢ Γᶜ → WfCtx Γᶜ
mw-conversion-wf mwΘ =
  conversion-wf (mw-exterior mwΘ) (mw-binds mwΘ) (mw-conversion mwΘ)

------------------------------------------------------------------------
-- 3d. Renaming the representation universe — the CONTEXT half
------------------------------------------------------------------------

-- A REPRESENTATION-ONLY renaming ρ acts on a context by renaming the
-- representation context and renaming the name map POINTWISE (`map ρ`).
-- Ordinary positions never move, so the ordinary spelling of every type,
-- conversion and change is untouched — which is the whole point of
-- `renᴹᴿ`.  `RepWk ρ Ξ Ξ′` is what such a move must supply, and it is
-- exactly what the two induced readings, the conversion typing and the
-- typing judgement all consume.  Three fields are the three `WfCtx`
-- obligations one universe down; the fourth, injectivity, is what a
-- `lock`'s freshness record needs.
--
-- The base instances insert either one abstract binder (`repwk-abst₀`
-- below, for `crossΛᴹ`) or a bind block (`repwk-wkN`,
-- strong.proof.RepWeaken, for `Peel`).  `repwk-push` and `repwk-abst`
-- close either instance under the two ways the typing induction goes deeper.

record RepWk (ρ : Renameᵗ) (Ξ Ξ′ : RepCtx) : Set where
  constructor repwk
  field
    wk-inj  : Injᵗ ρ
    wk-look : ∀ {α b} → Ξ ∋ˡ α := b → ∃[ b′ ] (Ξ′ ∋ˡ ρ α := b′)
    wk-bind : ∀ {α b} → Ξ ∋ʳ α := b → Ξ′ ∋ʳ ρ α := renRepBinding ρ b
    wk-reps : WfRepCtx Ξ → WfRepCtx Ξ′
open RepWk public

length-map : ∀ {A B : Set} (f : A → B) (xs : List A)
  → length (map f xs) ≡ length xs
length-map f []       = refl
length-map f (x ∷ xs) = cong suc (length-map f xs)

renameᵗ-shiftBy : (n : ℕ) (ρ : Renameᵗ) (R : Ty)
  → renameᵗ (extN n ρ) (shiftBy n R) ≡ shiftBy n (renameᵗ ρ R)
renameᵗ-shiftBy zero    ρ R = refl
renameᵗ-shiftBy (suc n) ρ R =
  trans (renameᵗ-⇑ (extN n ρ) (shiftBy n R))
        (cong ⇑ᵗ (renameᵗ-shiftBy n ρ R))

shiftRVars-ren : (n : ℕ) (ρ : Renameᵗ) (Δ : TyCtx)
  → map (extN n ρ) (shiftRVars n Δ) ≡ shiftRVars n (map ρ Δ)
shiftRVars-ren n ρ []      = refl
shiftRVars-ren n ρ (α ∷ Δ) =
  cong₂ _∷_ (extN-+ n ρ α) (shiftRVars-ren n ρ Δ)

-- A payload is checked at a local-binder depth m, so it moves by
-- `extN m ρ`; a reference at depth m is either local (untouched) or free
-- (renamed), which is exactly what `extN m ρ` does.
wk-ref : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → (m : ℕ) {i : ℕ}
  → Ξ ⊢ref[ m ] i → Ξ′ ⊢ref[ m ] extN m ρ i
wk-ref w zero (local-ref ())
wk-ref w zero (free-ref d) with wk-look w d
wk-ref w zero (free-ref d) | b′ , d′ = free-ref d′
wk-ref w (suc m) r = ref-ext (wk-ref w m) r

wk-wfᴿ : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → (m : ℕ) {R : Ty}
  → Ξ ⊢ᴿ[ m ] R → Ξ′ ⊢ᴿ[ m ] renameᵗ (extN m ρ) R
wk-wfᴿ w m = wfᴿ-rename (wk-ref w m)

binds-ren : ∀ {ρ Ξ Ξ′ Rs} → RepWk ρ Ξ Ξ′ → Ξ ⊢ᴮ Rs
  → Ξ′ ⊢ᴮ map (renameᵗ ρ) Rs
binds-ren w binds[] = binds[]
binds-ren w (binds∷ x xs) = binds∷ (wk-wfᴿ w zero x) (binds-ren w xs)

-- Inserting ONE FRESH BINDING at the head, abstract or represented.
-- Three of the four fields do not look at the binding at all — a name
-- lookup only moves one place further in, and injectivity is `suc`'s —
-- so the only thing the insertion has to supply is the WEAKEST form of
-- its own well-formedness: the step `WfRepCtx Ξ → WfRepCtx (b₀ ∷ Ξ)`,
-- which is `wf-abstR` for an abstract binder and `wf-bindR w` for a
-- represented one whose payload checks over Ξ.  This is the base move
-- made by a term crossing `Λ` (at `abstR`) and by one crossing a new
-- representation binder (at `bindR R`); `repwk-abst` below is the
-- recursion-closure move when an existing renaming itself goes under `Λ`.
∋ˡ-cons : ∀ {Ξ : RepCtx} {b₀ : RepBinding} {α b} → Ξ ∋ˡ α := b
  → ∃[ b′ ] ((b₀ ∷ Ξ) ∋ˡ suc α := b′)
∋ˡ-cons d = _ , there d

repwk-cons₀ : ∀ {Ξ : RepCtx} (b₀ : RepBinding)
  → (WfRepCtx Ξ → WfRepCtx (b₀ ∷ Ξ))
  → RepWk suc Ξ (b₀ ∷ Ξ)
repwk-cons₀ abstR     wr = repwk suc-injective ∋ˡ-cons r-there-abst wr
repwk-cons₀ (bindR R) wr = repwk suc-injective ∋ˡ-cons r-there wr

repwk-abst₀ : ∀ {Ξ : RepCtx} → RepWk suc Ξ (abstR ∷ Ξ)
repwk-abst₀ = repwk-cons₀ abstR wf-abstR

-- Going under an abstract binder — the `Λ` case.
repwk-abst : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′
  → RepWk (extᵗ ρ) (abstR ∷ Ξ) (abstR ∷ Ξ′)
repwk-abst {ρ = ρ} {Ξ = Ξ} {Ξ′ = Ξ′} w =
  repwk (inj-extᵗ (wk-inj w)) look bnd rps
  where
  look : ∀ {α b} → (abstR ∷ Ξ) ∋ˡ α := b
    → ∃[ b′ ] ((abstR ∷ Ξ′) ∋ˡ extᵗ ρ α := b′)
  look here = abstR , here
  look (there d) with wk-look w d
  look (there d) | b′ , d′ = b′ , there d′

  bnd : ∀ {α b} → (abstR ∷ Ξ) ∋ʳ α := b
    → (abstR ∷ Ξ′) ∋ʳ extᵗ ρ α := renRepBinding (extᵗ ρ) b
  bnd r-here = r-here
  bnd (r-there-abst {b = b} d) =
    subst (λ c → (abstR ∷ Ξ′) ∋ʳ suc (ρ _) := c)
          (sym (renRepBinding-⇑ ρ b))
          (r-there-abst (wk-bind w d))

  rps : WfRepCtx (abstR ∷ Ξ) → WfRepCtx (abstR ∷ Ξ′)
  rps (wf-abstR wr) = wf-abstR (wk-reps w wr)

-- Going under a represented binder — one step of a bind block.
repwk-bind : ∀ {ρ Ξ Ξ′ R} → RepWk ρ Ξ Ξ′
  → RepWk (extᵗ ρ) (bindR R ∷ Ξ) (bindR (renameᵗ ρ R) ∷ Ξ′)
repwk-bind {ρ = ρ} {Ξ = Ξ} {Ξ′ = Ξ′} {R = R} w =
  repwk (inj-extᵗ (wk-inj w)) look bnd rps
  where
  look : ∀ {α b} → (bindR R ∷ Ξ) ∋ˡ α := b
    → ∃[ b′ ] ((bindR (renameᵗ ρ R) ∷ Ξ′) ∋ˡ extᵗ ρ α := b′)
  look here = bindR (renameᵗ ρ R) , here
  look (there d) with wk-look w d
  look (there d) | b′ , d′ = b′ , there d′

  bnd : ∀ {α b} → (bindR R ∷ Ξ) ∋ʳ α := b
    → (bindR (renameᵗ ρ R) ∷ Ξ′) ∋ʳ extᵗ ρ α
        := renRepBinding (extᵗ ρ) b
  bnd r-here =
    subst (λ c → (bindR (renameᵗ ρ R) ∷ Ξ′) ∋ʳ zero := c)
          (sym (renRepBinding-⇑ ρ (bindR R)))
          r-here
  bnd (r-there {b = b} d) =
    subst (λ c → (bindR (renameᵗ ρ R) ∷ Ξ′) ∋ʳ suc (ρ _) := c)
          (sym (renRepBinding-⇑ ρ b))
          (r-there (wk-bind w d))

  rps : WfRepCtx (bindR R ∷ Ξ) → WfRepCtx (bindR (renameᵗ ρ R) ∷ Ξ′)
  rps (wf-bindR x wr) = wf-bindR (wk-wfᴿ w zero x) (wk-reps w wr)

-- Going under a whole PARALLEL bind block — the boundary case.  Each
-- payload was written over the exterior, so it moves by ρ; the block's
-- own shifts commute with that (`renameᵗ-shiftBy`).
repwk-push : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → (Rs : List Ty)
  → RepWk (extN (length Rs) ρ) (pushRepBinds Rs Ξ)
      (pushRepBinds (map (renameᵗ ρ) Rs) Ξ′)
repwk-push w [] = w
repwk-push {ρ = ρ} w (R ∷ Rs)
  rewrite length-map (renameᵗ ρ) Rs
        | sym (renameᵗ-shiftBy (length Rs) ρ R) =
  repwk-bind (repwk-push w Rs)

-- The three `WfCtx` fields, and the conversion LOOKUP SQUARE.
validNames-ren : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → ValidNames Ξ Δ
  → ValidNames Ξ′ (map ρ Δ)
validNames-ren {Δ = Δ} {ρ = ρ} w vn d with ∋ˡ-ren⁻ ρ Δ d
validNames-ren {Δ = Δ} {ρ = ρ} w vn d | α , d′ , refl with vn d′
validNames-ren {Δ = Δ} {ρ = ρ} w vn d | α , d′ , refl | b , db =
  wk-look w db

wfctx-ren : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → WfCtx (Ξ ∣ Δ)
  → WfCtx (Ξ′ ∣ map ρ Δ)
wfctx-ren w (wf-ctx wr vn uq) =
  wf-ctx (wk-reps w wr) (validNames-ren w vn) (unique-ren (wk-inj w) uq)

∋:=-ren : ∀ {ρ Ξ Ξ′ A} → RepWk ρ Ξ Ξ′ → (Ξ ∣ Δ) ∋ X := A
  → (Ξ′ ∣ map ρ Δ) ∋ X := A
∋:=-ren {ρ = ρ} w (α , R , dn , dr , sm) =
  ρ α , renameᵗ ρ R , ∋ˡ-ren ρ dn , wk-bind w dr , same-ren ρ sm

-- The change run and both readings.  A `lock` deletes at the same
-- ordinary position and records freshness of the renamed name; an
-- `unlock` inserts at the same position.  Nothing here is arithmetic on
-- ordinary positions, which is why the ordinary spelling survives.
del-ren : (ρ : Renameᵗ) → α ⊢- Δ at X ⇒ Δ′
  → ρ α ⊢- map ρ Δ at X ⇒ map ρ Δ′
del-ren ρ del-here = del-here
del-ren ρ (del-there dl) = del-there (del-ren ρ dl)

ins-ren : (ρ : Renameᵗ) → α ⊢+ Δ at X ⇒ Δ′
  → ρ α ⊢+ map ρ Δ at X ⇒ map ρ Δ′
ins-ren ρ ins-here = ins-here
ins-ren ρ (ins-there i) = ins-there (ins-ren ρ i)

step-ren : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → Ξ ∣ Δ ⊢δ δ ⇒ Δ′
  → Ξ′ ∣ map ρ Δ ⊢δ renᶠᴿ ρ δ ⇒ map ρ Δ′
step-ren {ρ = ρ} w (step-lock (b , v) dl fr) =
  step-lock (wk-look w v) (del-ren ρ dl) (fresh-ren (wk-inj w) fr)
step-ren {ρ = ρ} w (step-unlock (b , v) fr i) =
  step-unlock (wk-look w v) (fresh-ren (wk-inj w) fr) (ins-ren ρ i)

changes-ren : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → Ξ ∣ Δ ⊢χ χ ⇒ Δ′
  → Ξ′ ∣ map ρ Δ ⊢χ map (renᶠᴿ ρ) χ ⇒ map ρ Δ′
changes-ren w changes[] = changes[]
changes-ren w (changes∷ cs st) =
  changes∷ (changes-ren w cs) (step-ren w st)

conv-changes-ren : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′
  → Ξ′ ∣ map ρ Δ ⊢χᶜ map (renᶠᴿ ρ) χ ⇒ map ρ Δ′
conv-changes-ren w conv[] = conv[]
conv-changes-ren w (conv-lock (b , v) cs) =
  conv-lock (wk-look w v) (conv-changes-ren w cs)
conv-changes-ren {ρ = ρ} w (conv-unlock (b , v) cs fr i) =
  conv-unlock (wk-look w v) (conv-changes-ren w cs)
    (fresh-ren (wk-inj w) fr) (ins-ren ρ i)
conv-changes-ren {ρ = ρ} w (conv-unlock-live (b , v) cs d) =
  conv-unlock-live (wk-look w v) (conv-changes-ren w cs) (∋ˡ-ren ρ d)

-- The renamed morphism's exterior name map, as the renaming of the
-- original one: the bind block keeps its width under renaming, and
-- `extN` at that width is what `shiftRVars` at it becomes.
names-ren-push : (ρ : Renameᵗ) (Bs : List Ty) (Δ : TyCtx)
  → map (extN (length Bs) ρ) (shiftRVars (length Bs) Δ)
      ≡ shiftRVars (length (map (renameᵗ ρ) Bs)) (map ρ Δ)
names-ren-push ρ Bs Δ =
  trans (shiftRVars-ren (length Bs) ρ Δ)
        (cong (λ n → shiftRVars n (map ρ Δ))
              (sym (length-map (renameᵗ ρ) Bs)))

-- The two readings of the RENAMED morphism are the renamed readings.
interior-ren : ∀ {ρ Ξ Ξ′ Θ} {Γᵢ : Ctxᵗ} → RepWk ρ Ξ Ξ′
  → (Ξ ∣ Δ) ⊢ⁱ Θ ⇒ Γᵢ
  → (Ξ′ ∣ map ρ Δ) ⊢ⁱ renᴮᴿ ρ Θ ⇒
      (pushRepBinds (map (renameᵗ ρ) (binds Θ)) Ξ′
        ∣ map (extN (numBinds Θ) ρ) (names Γᵢ))
interior-ren {Δ = Δ} {ρ = ρ} {Ξ′ = Ξ′} {Θ = Θ}
             w (interior {Δ′ = Δ′} cs) =
  interior
    (subst (λ D → pushRepBinds (map (renameᵗ ρ) (binds Θ)) Ξ′ ∣ D
                    ⊢χ map (renᶠᴿ (extN (numBinds Θ) ρ)) (changes Θ)
                    ⇒ map (extN (numBinds Θ) ρ) Δ′)
           (names-ren-push ρ (binds Θ) Δ)
           (changes-ren (repwk-push w (binds Θ)) cs))

conversion-ren : ∀ {ρ Ξ Ξ′ Θ} {Γᶜ : Ctxᵗ} → RepWk ρ Ξ Ξ′
  → (Ξ ∣ Δ) ⊢ᶜ Θ ⇒ Γᶜ
  → (Ξ′ ∣ map ρ Δ) ⊢ᶜ renᴮᴿ ρ Θ ⇒
      (pushRepBinds (map (renameᵗ ρ) (binds Θ)) Ξ′
        ∣ map (extN (numBinds Θ) ρ) (names Γᶜ))
conversion-ren {Δ = Δ} {ρ = ρ} {Ξ′ = Ξ′} {Θ = Θ}
               w (conversion {Δ′ = Δ′} cs) =
  conversion
    (subst (λ D → pushRepBinds (map (renameᵗ ρ) (binds Θ)) Ξ′ ∣ D
                    ⊢χᶜ map (renᶠᴿ (extN (numBinds Θ) ρ)) (changes Θ)
                    ⇒ map (extN (numBinds Θ) ρ) Δ′)
           (names-ren-push ρ (binds Θ) Δ)
           (conv-changes-ren (repwk-push w (binds Θ)) cs))

-- The conversion half of moving a boundary across a fresh representation
-- binder.  Representation renaming first transports the old reading.  The
-- appended lock is skipped, so `conv-weaken` starts that transported run in
-- the larger map containing the fresh ordinary name.  The result retains the
-- REPRESENTATION-RENAMED old conversion names; retaining the unrenamed names
-- is false when the old context names a free representation below the new
-- insertion.
addLock0-conversion-ren : ∀ {Ξ Ξ′ Δ Θ Γᶜ}
  → RepWk suc Ξ Ξ′
  → Ξ′ ∋ʳ zero
  → Unique Δ
  → (Ξ ∣ Δ) ⊢ᶜ Θ ⇒ Γᶜ
  → Σ[ Γ′ᶜ ∈ Ctxᵗ ]
        (((Ξ′ ∣ (zero ∷ shiftNames Δ))
          ⊢ᶜ addLock0 (renᴮᴿ suc Θ) ⇒ Γ′ᶜ)
        × (map (extN (numBinds Θ) suc) (names Γᶜ)
             ⊆ᵃ (names Γ′ᶜ)))
addLock0-conversion-ren {Ξ′ = Ξ′} {Δ = Δ} {Θ = morph Rs χ}
                        w v₀ uq (conversion {Δ′ = Δᶜ} cs)
  with conv-weaken
         (unique-shiftRVars (length (map (renameᵗ suc) Rs))
           (unique-shift uq))
         (unique-shiftRVars (length (map (renameᵗ suc) Rs))
           (unique∷ fresh-zero-shift (unique-shift uq)))
         (subst
           (λ D → pushRepBinds (map (renameᵗ suc) Rs) Ξ′ ∣ D
             ⊢χᶜ map (renᶠᴿ (extN (length Rs) suc)) χ
             ⇒ map (extN (length Rs) suc) Δᶜ)
           (names-ren-push suc Rs Δ)
           (conv-changes-ren (repwk-push w Rs) cs))
         ∋ᵅ-cons
addLock0-conversion-ren {Ξ′ = Ξ′} {Δ = Δ} {Θ = morph Rs χ}
                        w v₀ uq (conversion {Δ′ = Δᶜ} cs)
  | Δ′ , cs′ , keep =
  _ , conversion (conv-snoc-lock valid cs′) , keep
  where
  valid : pushRepBinds (map (renameᵗ suc) Rs) Ξ′
            ∋ʳ length (map (renameᵗ suc) Rs)
  valid = subst
                (λ α →
                  pushRepBinds (map (renameᵗ suc) Rs) Ξ′ ∋ʳ α)
                (+-identityʳ (length (map (renameᵗ suc) Rs)))
                (_ , ∋ˡ-push (map (renameᵗ suc) Rs) (proj₂ v₀))

-- The INTERIOR half of the same move, and the reason the moved term needs
-- no ordinary renaming.  The appended lock runs FIRST here too, but an
-- interior reading PERFORMS a lock: it deletes the fresh ordinary name
-- before any of Θ's own changes run, so what remains is exactly the
-- representation-renamed old interior — `interior-ren`, with no ordinary
-- position moved.  Contrast `addLock0-conversion-ren`, where the lock is
-- skipped and the fresh name has to be carried through the whole run.
addLock0-interior-ren : ∀ {Ξ Ξ′ Δ Θ Γᵢ}
  → RepWk suc Ξ Ξ′
  → Ξ′ ∋ʳ zero
  → (Ξ ∣ Δ) ⊢ⁱ Θ ⇒ Γᵢ
  → (Ξ′ ∣ (zero ∷ shiftNames Δ)) ⊢ⁱ addLock0 (renᴮᴿ suc Θ) ⇒
      (pushRepBinds (map (renameᵗ suc) (binds Θ)) Ξ′
        ∣ map (extN (numBinds Θ) suc) (names Γᵢ))
addLock0-interior-ren {Ξ′ = Ξ′} {Δ = Δ} {Θ = morph Rs χ}
                      w v₀ (interior {Δ′ = Δᵢ} cs) =
  interior
    (changes-++
      (changes∷ changes[]
        (step-lock valid
          (subst (λ α → α ⊢- (n + zero) ∷ shiftRVars n (shiftNames Δ)
                          at zero ⇒ shiftRVars n (shiftNames Δ))
                 (+-identityʳ n) del-here)
          (subst (λ α → shiftRVars n (shiftNames Δ) ∌ʳ α)
                 (+-identityʳ n)
                 (fresh-shiftRVars n fresh-zero-shift))))
      (subst
        (λ D → pushRepBinds (map (renameᵗ suc) Rs) Ξ′ ∣ D
          ⊢χ map (renᶠᴿ (extN (length Rs) suc)) χ
          ⇒ map (extN (length Rs) suc) Δᵢ)
        (names-ren-push suc Rs Δ)
        (changes-ren (repwk-push w Rs) cs)))
  where
  n : ℕ
  n = length (map (renameᵗ suc) Rs)

  valid : pushRepBinds (map (renameᵗ suc) Rs) Ξ′ ∋ʳ n
  valid = subst
                (λ α →
                  pushRepBinds (map (renameᵗ suc) Rs) Ξ′ ∋ʳ α)
                (+-identityʳ n)
                (_ , ∋ˡ-push (map (renameᵗ suc) Rs) (proj₂ v₀))

------------------------------------------------------------------------
-- 4. Concrete boundary shapes
------------------------------------------------------------------------

TyBetaMorph : CtxMorph
TyBetaMorph = morph (`ℕ ∷ []) (unlock 0 0 ∷ [])

TyBetaCtx : Ctxᵗ
TyBetaCtx = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

TyBeta-interior : empty ⊢ⁱ TyBetaMorph ⇒ TyBetaCtx
TyBeta-interior =
  interior
    (changes∷ changes[] (step-unlock (_ , here) fresh[] ins-here))

TyBeta-conversion : empty ⊢ᶜ TyBetaMorph ⇒ TyBetaCtx
TyBeta-conversion =
  conversion
    (conv-unlock (_ , here) conv[] fresh[] ins-here)

TyBetaCtx-wf : WfCtx TyBetaCtx
TyBetaCtx-wf =
  wf-ctx (wf-bindR wfᴿ-ℕ wf-reps[])
         (λ { here → _ , here })
         (unique∷ fresh[] unique[])

TyBeta-mw : MorphWf empty TyBetaMorph TyBetaCtx TyBetaCtx
TyBeta-mw =
  mw wf-empty (binds∷ wfᴿ-ℕ binds[]) TyBeta-interior TyBeta-conversion

-- Crossing an argument under `ΛX` removes only ordinary X. Its abstract
-- representation variable remains, and the dual restores X exactly.
ΛXCtx : Ctxᵗ
ΛXCtx = underΛ empty

crossΛ : reps ΛXCtx ∣ names ΛXCtx ⊢δ lock 0 0 ⇒ []
crossΛ = step-lock (_ , here) del-here fresh[]

uncrossΛ : reps ΛXCtx ∣ [] ⊢δ unlock 0 0 ⇒ names ΛXCtx
uncrossΛ = dual-step crossΛ
