module strong-rep-nu.Boundary where

-- File Charter:
--   * THE BOUNDARY SCOPE AND ITS TWO INDUCED CONTEXTS.  §2 `Change`
--     (`unbind`/`bind`), its two running judgements, the dual and
--     `renᶠᴿ`.  §3 `Boundary = List Change` with `renᴮᴿ`, `rewind`,
--     `inst`, and the two readings `_⊢ⁱ_⇒_` (PERFORMS every change)
--     and `_⊢ᶜ_⇒_` (SKIPS unbinds), with their functionality.
--     §§3a–3d transport: well-formedness, (Q), `conv-weaken`,
--     `merged-conversion-exists`, the representation-renaming lemmas,
--     and `BoundaryWf`.  §4 concrete shapes.
--   * EVERYTHING HERE MENTIONS `Change` OR `Boundary`; the context
--     material it stands on is strong-rep-nu.Ctx (whose lemmas are
--     strong-rep-nu.proof.Ctx).  That is why sections begin at 2 —
--     other modules cite these numbers, so do not renumber them.
--   * TWO LAWS.  (1) The CONVERSION context is the UNION of the names
--     live anywhere along the scope (hence `conv-bind-live`).
--     (2) Both readings are nevertheless FUNCTIONS of the change list.
-- Commentary: Commentary.md § Boundary.agda

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s)
open import Data.Nat.Properties using (_≟_; +-identityʳ; ≤-trans)
open import Data.List using (List; []; _∷_; _++_; map; reverse; length)
open import Data.List.Properties using (unfold-reverse; map-++)
open import Data.Product using (Σ-syntax; _,_; _×_; ∃-syntax; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import strong-rep-nu.Types using (Ty; `ℕ; Renameᵗ; renameᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx

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
-- 2. Ordinary-variable binders and anti-binders
------------------------------------------------------------------------

data Change : Set where
  unbind : ℕ → RVar → Change
  bind   : ℕ → RVar → Change

private
  variable
    δ : Change
    χ : List Change

-- `unbind` records freshness of the result and `bind` demands freshness of
-- its input. Thus one representation variable never has two simultaneous
-- ordinary names, and the two changes are exact inverses. The Ξ index makes
-- the carried representation-variable occurrence well scoped.
infix 4 _∣_⊢δ_⇒_
data _∣_⊢δ_⇒_ (Ξ : RepCtx) : TyCtx → Change → TyCtx → Set where
  step-unbind : Ξ ∋ʳ α → α ⊢- Δ at X ⇒ Δ′ → Δ′ ∌ʳ α
    → Ξ ∣ Δ ⊢δ unbind X α ⇒ Δ′
  step-bind : Ξ ∋ʳ α → Δ ∌ʳ α → α ⊢+ Δ at X ⇒ Δ′
    → Ξ ∣ Δ ⊢δ bind X α ⇒ Δ′

dualChange : Change → Change
dualChange (unbind X α)   = bind X α
dualChange (bind X α) = unbind X α

dual-step : Ξ ∣ Δ ⊢δ δ ⇒ Δ′
  → Ξ ∣ Δ′ ⊢δ dualChange δ ⇒ Δ
dual-step (step-unbind valid d fresh) =
  step-bind valid fresh (insert-delete d)
dual-step (step-bind valid fresh i) =
  step-unbind valid (delete-insert i) fresh

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
change-functional (step-unbind valid d fresh)
                  (step-unbind valid′ d′ fresh′) =
  delete-functional d d′
change-functional (step-bind valid fresh i)
                  (step-bind valid′ fresh′ i′) =
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

-- A REPRESENTATION-ONLY renaming of a change. The ordinary position is
-- untouched, which is what makes a rep-only weakening leave every
-- ordinary de Bruijn spelling in a term exactly where it was.
renᶠᴿ : Renameᵗ → Change → Change
renᶠᴿ ρʳ (unbind X α)   = unbind X (ρʳ α)
renᶠᴿ ρʳ (bind X α) = bind X (ρʳ α)

------------------------------------------------------------------------
-- 3. Boundary scopes and their two induced contexts
------------------------------------------------------------------------

-- A boundary scope IS its change list — an ALIAS since 2026-09-22, so
-- merging is `_++_` and the derived scopes are list expressions.
-- Commentary.md § Boundary.agda / Boundary = List Change
Boundary : Set
Boundary = List Change

-- Representation-only renaming of a scope: every change's representation
-- variable, no ordinary position.  There is no bind prefix to skip.
renᴮᴿ : Renameᵗ → Boundary → Boundary
renᴮᴿ ρʳ Θ = map (renᶠᴿ ρʳ) Θ

-- Rewinding: the changes, then their exact inverse.
rewind : Boundary → Boundary
rewind Θ = dual Θ ++ Θ

-- Merging two scopes is `_++_`: the outer scope's changes sit at the
-- TAIL, so they run first.  Appending `unbind 0 0` makes it act FIRST.
-- Commentary.md § Boundary.agda / rewind, ++, the snoc unbind, inst

private
  shiftChange : Change → Change
  shiftChange (unbind X α)   = unbind (suc X) (suc α)
  shiftChange (bind X α) = bind (suc X) (suc α)

-- Instantiating a scope, read at `allocate R Γ`: the appended
-- `bind 0 0` gives the fresh cell ordinary name 0, and the old
-- changes run underneath both — one shift in each universe.
inst : Boundary → Boundary
inst Θ =
  map shiftChange Θ ++ (bind 0 0 ∷ [])

-- The interior reading PERFORMS every change on the name map.  The
-- representation context is untouched: a boundary changes NAMES only.
infix 4 _⊢ⁱ_⇒_
data _⊢ⁱ_⇒_ (Γ : Ctxᵗ) (Θ : Boundary) : Ctxᵗ → Set where
  interior : ∀ {Δ′}
    → reps Γ ∣ names Γ ⊢χ Θ ⇒ Δ′
    → Γ ⊢ⁱ Θ ⇒ (reps Γ ∣ Δ′)


-- The conversion context performs `bind`s but SKIPS `unbind`s, so it is
-- the UNION of the names live anywhere along the boundary scope.  That
-- reading forces the third clause `conv-bind-live` (2026-09-17).
-- Commentary.md § Boundary.agda / _∣_⊢χᶜ_⇒_ and the re-bind clause
infix 4 _∣_⊢χᶜ_⇒_
data _∣_⊢χᶜ_⇒_ (Ξ : RepCtx)
  : TyCtx → List Change → TyCtx → Set where
  conv[] : Ξ ∣ Δ ⊢χᶜ [] ⇒ Δ
  conv-unbind : Ξ ∋ʳ α → Ξ ∣ Δ₁ ⊢χᶜ χ ⇒ Δ₂
    → Ξ ∣ Δ₁ ⊢χᶜ unbind X α ∷ χ ⇒ Δ₂
  conv-bind : Ξ ∋ʳ α
    → Ξ ∣ Δ₁ ⊢χᶜ χ ⇒ Δ₂
    → Δ₂ ∌ʳ α
    → α ⊢+ Δ₂ at X ⇒ Δ₃
    → Ξ ∣ Δ₁ ⊢χᶜ bind X α ∷ χ ⇒ Δ₃
  conv-bind-live : ∀ {Y} → Ξ ∋ʳ α
    → Ξ ∣ Δ₁ ⊢χᶜ χ ⇒ Δ₂
    → Δ₂ ∋ˡ Y := α
    → Ξ ∣ Δ₁ ⊢χᶜ bind X α ∷ χ ⇒ Δ₂

conv-changes-functional : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ₁
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ₂
  → Δ₁ ≡ Δ₂
conv-changes-functional conv[] conv[] = refl
conv-changes-functional (conv-unbind valid cs) (conv-unbind valid′ cs′) =
  conv-changes-functional cs cs′
conv-changes-functional (conv-bind valid cs fresh i)
                        (conv-bind valid′ cs′ fresh′ i′)
  with conv-changes-functional cs cs′
conv-changes-functional (conv-bind valid cs fresh i)
                        (conv-bind valid′ cs′ fresh′ i′) | refl =
  insert-functional i i′
conv-changes-functional (conv-bind-live valid cs d)
                        (conv-bind-live valid′ cs′ d′) =
  conv-changes-functional cs cs′
-- the mixed pairs are impossible: one says α is FRESH in the tail's
-- output, the other says α is LOOKED UP there.
conv-changes-functional (conv-bind valid cs fresh i)
                        (conv-bind-live valid′ cs′ d′)
  with conv-changes-functional cs cs′
... | refl = ⊥-elim (fresh-not-lookup fresh d′)
conv-changes-functional (conv-bind-live valid cs d)
                        (conv-bind valid′ cs′ fresh′ i′)
  with conv-changes-functional cs cs′
... | refl = ⊥-elim (fresh-not-lookup fresh′ d)

infix 4 _⊢ᶜ_⇒_
data _⊢ᶜ_⇒_ (Γ : Ctxᵗ) (Θ : Boundary) : Ctxᵗ → Set where
  conversion : ∀ {Δ′}
    → reps Γ ∣ names Γ ⊢χᶜ Θ ⇒ Δ′
    → Γ ⊢ᶜ Θ ⇒ (reps Γ ∣ Δ′)


interior-functional : ∀ {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ → Γ ⊢ⁱ Θ ⇒ Γᶜ → Γᵢ ≡ Γᶜ
interior-functional (interior cs) (interior cs′) =
  cong (_ ∣_) (changes-functional cs cs′)

conversion-functional : ∀ {Θ : Boundary}
  → Γ ⊢ᶜ Θ ⇒ Γᵢ → Γ ⊢ᶜ Θ ⇒ Γᶜ → Γᵢ ≡ Γᶜ
conversion-functional (conversion cs) (conversion cs′) =
  cong (_ ∣_) (conv-changes-functional cs cs′)

------------------------------------------------------------------------
-- 3a. Transport across a boundary scope
------------------------------------------------------------------------

-- The two induced contexts are WELL FORMED whenever the exterior is:
-- each of `WfCtx`'s three fields transports separately, and none needs
-- the term or the conversion.  A conversion reading only ADDS ordinary
-- names (`conversion-live`).
-- Commentary.md § Boundary.agda / §3a
conversion-live : ∀ {Θ : Boundary}
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → (names Γ) ∋ᵅ α
  → (names Γᶜ) ∋ᵅ α
conversion-live (conversion cs) lv = conv-live cs lv
  where
  conv-live : ∀ {Ξ Δ Δ′ χ α}
    → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → Δ ∋ᵅ α → Δ′ ∋ᵅ α
  conv-live conv[] live = live
  conv-live (conv-unbind v css) live = conv-live css live
  conv-live (conv-bind v css fr i) live = ins-mono i (conv-live css live)
  conv-live (conv-bind-live v css d) live = conv-live css live

-- Rewinding: the original changes, then their exact inverse — so the
-- interior is the EXTERIOR ITSELF and the conversion context is the
-- original one.

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
  conv-changes-++ cs₂ (conv-unbind v cs₁) =
    conv-unbind v (conv-changes-++ cs₂ cs₁)
  conv-changes-++ cs₂ (conv-bind v cs₁ fr i) =
    conv-bind v (conv-changes-++ cs₂ cs₁) fr i
  conv-changes-++ cs₂ (conv-bind-live v cs₁ d) =
    conv-bind-live v (conv-changes-++ cs₂ cs₁) d

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
  int⇒conv-live (changes∷ cs (step-unbind v dl fr))
                (conv-unbind v′ csᶜ) lv =
    int⇒conv-live cs csᶜ (del-inv dl lv)
  int⇒conv-live (changes∷ cs (step-bind v fr i))
                (conv-bind v′ csᶜ fr′ i′) lv with ins-inv i lv
  int⇒conv-live (changes∷ cs (step-bind v fr i))
                (conv-bind v′ csᶜ fr′ i′) lv | inj₁ refl =
    ins-live i′
  int⇒conv-live (changes∷ cs (step-bind v fr i))
                (conv-bind v′ csᶜ fr′ i′) lv | inj₂ lv′ =
    ins-mono i′ (int⇒conv-live cs csᶜ lv′)
  int⇒conv-live (changes∷ cs (step-bind v fr i))
                (conv-bind-live v′ csᶜ d) lv with ins-inv i lv
  int⇒conv-live (changes∷ cs (step-bind v fr i))
                (conv-bind-live v′ csᶜ d) lv | inj₁ refl = _ , d
  int⇒conv-live (changes∷ cs (step-bind v fr i))
                (conv-bind-live v′ csᶜ d) lv | inj₂ lv′ =
    int⇒conv-live cs csᶜ lv′

  conv-dual-id : ∀ {Ξ Δ Δᵢ Δᶜ Δ₀ χ}
    → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
    → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
    → (∀ {α} → Δᶜ ∋ᵅ α → Δ₀ ∋ᵅ α)
    → Ξ ∣ Δ₀ ⊢χᶜ dual χ ⇒ Δ₀
  conv-dual-id changes[] conv[] keep = conv[]
  conv-dual-id {χ = unbind X α ∷ χ}
               (changes∷ cs (step-unbind v dl fr))
               (conv-unbind v′ csᶜ) keep
    with keep (int⇒conv-live cs csᶜ (del-live dl))
  conv-dual-id {χ = unbind X α ∷ χ}
               (changes∷ cs (step-unbind v dl fr))
               (conv-unbind v′ csᶜ) keep | Y , d =
    subst (λ χ′ → _ ∣ _ ⊢χᶜ χ′ ⇒ _)
          (sym (dual-∷ (unbind X α) χ))
          (conv-changes-++ (conv-bind-live v conv[] d)
                           (conv-dual-id cs csᶜ keep))
  conv-dual-id {χ = bind X α ∷ χ}
               (changes∷ cs (step-bind v fr i))
               (conv-bind v′ csᶜ fr′ i′) keep =
    subst (λ χ′ → _ ∣ _ ⊢χᶜ χ′ ⇒ _)
          (sym (dual-∷ (bind X α) χ))
          (conv-changes-++ (conv-unbind v conv[])
            (conv-dual-id cs csᶜ (λ lv → keep (ins-mono i′ lv))))
  conv-dual-id {χ = bind X α ∷ χ}
               (changes∷ cs (step-bind v fr i))
               (conv-bind-live v′ csᶜ d) keep =
    subst (λ χ′ → _ ∣ _ ⊢χᶜ χ′ ⇒ _)
          (sym (dual-∷ (bind X α) χ))
          (conv-changes-++ (conv-unbind v conv[])
                           (conv-dual-id cs csᶜ keep))

  shiftReps-lookup : Δ ∋ˡ X := α → shiftReps Δ ∋ˡ X := suc α
  shiftReps-lookup here = here
  shiftReps-lookup (there d) = there (shiftReps-lookup d)

  valid-suc : Ξ ∋ʳ α → (b ∷ Ξ) ∋ʳ suc α
  valid-suc (b′ , d) = b′ , there d

  insert-shift : α ⊢+ Δ at X ⇒ Δ′
    → suc α ⊢+ shiftReps Δ at X ⇒ shiftReps Δ′
  insert-shift ins-here = ins-here
  insert-shift (ins-there i) = ins-there (insert-shift i)

  delete-shift : α ⊢- Δ at X ⇒ Δ′
    → suc α ⊢- shiftReps Δ at X ⇒ shiftReps Δ′
  delete-shift del-here = del-here
  delete-shift (del-there d) = del-there (delete-shift d)

  step-shift : Ξ ∣ Δ ⊢δ δ ⇒ Δ′
    → (b ∷ Ξ) ∣ (zero ∷ shiftReps Δ) ⊢δ shiftChange δ
        ⇒ (zero ∷ shiftReps Δ′)
  step-shift (step-unbind valid d fresh) =
    step-unbind (valid-suc valid) (del-there (delete-shift d))
      (fresh∷ (λ ()) (fresh-shift fresh))
  step-shift (step-bind valid fresh i) =
    step-bind (valid-suc valid)
      (fresh∷ (λ ()) (fresh-shift fresh))
      (ins-there (insert-shift i))

  changes-shift : Ξ ∣ Δ ⊢χ χ ⇒ Δ′
    → (b ∷ Ξ) ∣ (zero ∷ shiftReps Δ) ⊢χ map shiftChange χ
        ⇒ (zero ∷ shiftReps Δ′)
  changes-shift changes[] = changes[]
  changes-shift (changes∷ cs st) =
    changes∷ (changes-shift cs) (step-shift st)

  conv-changes-shift : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′
    → (b ∷ Ξ) ∣ (zero ∷ shiftReps Δ) ⊢χᶜ map shiftChange χ
        ⇒ (zero ∷ shiftReps Δ′)
  conv-changes-shift conv[] = conv[]
  conv-changes-shift (conv-unbind valid cs) =
    conv-unbind (valid-suc valid) (conv-changes-shift cs)
  conv-changes-shift (conv-bind valid cs fresh i) =
    conv-bind (valid-suc valid) (conv-changes-shift cs)
      (fresh∷ (λ ()) (fresh-shift fresh))
      (ins-there (insert-shift i))
  conv-changes-shift (conv-bind-live valid cs d) =
    conv-bind-live (valid-suc valid) (conv-changes-shift cs)
      (there (shiftReps-lookup d))

-- Instantiating a scope, read at the ALLOCATED context: the old changes
-- run underneath the fresh ordinary name, in both induced readings.
inst-interior : ∀ {R : Ty} {Γ Γᵢ : Ctxᵗ} {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → allocate R Γ ⊢ⁱ inst Θ ⇒
      ((bindR R ∷ reps Γ) ∣ (zero ∷ shiftReps (names Γᵢ)))
inst-interior {Γ = Ξ ∣ Δ} (interior cs) =
  interior
    (changes-++
      (changes∷ changes[]
        (step-bind (_ , here) fresh-zero-shift ins-here))
      (changes-shift cs))

inst-conversion : ∀ {R : Ty} {Γ Γᶜ : Ctxᵗ} {Θ : Boundary}
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → allocate R Γ ⊢ᶜ inst Θ ⇒
      ((bindR R ∷ reps Γ) ∣ (zero ∷ shiftReps (names Γᶜ)))
inst-conversion {Γ = Ξ ∣ Δ} (conversion cs) =
  conversion
    (conv-changes-++
      (conv-bind (_ , here) conv[] fresh-zero-shift ins-here)
      (conv-changes-shift cs))

-- A rewound scope's interior is the exterior itself.
rewind-interior : ∀ {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ⁱ rewind Θ ⇒ Γ
rewind-interior (interior cs) =
  interior (changes-++ cs (dual-changes cs))

rewind-conversion : ∀ {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γ ⊢ᶜ rewind Θ ⇒ Γᶜ
rewind-conversion (interior cs) (conversion csᶜ) =
  conversion (conv-changes-++ csᶜ (conv-dual-id cs csᶜ (λ lv → lv)))


-- (i) `name-fn`: an unbind deletes, a bind inserts a fresh name.
int-unique : Unique Δ → Ξ ∣ Δ ⊢χ χ ⇒ Δ′ → Unique Δ′
int-unique uq changes[] = uq
int-unique uq (changes∷ cs (step-unbind v dl fr)) =
  del-unique dl (int-unique uq cs)
int-unique uq (changes∷ cs (step-bind v fr i)) =
  ins-unique i fr (int-unique uq cs)

-- (ii) `wf-names`: every name a reading leaves live is one the exterior
-- already had or one a `bind` brought in, with its own `Ξ ∋ʳ α`.
int-valid : ValidNames Ξ Δ → Ξ ∣ Δ ⊢χ χ ⇒ Δ′ → ValidNames Ξ Δ′
int-valid vn changes[] = vn
int-valid vn (changes∷ cs (step-unbind v dl fr)) =
  del-valid dl (int-valid vn cs)
int-valid vn (changes∷ cs (step-bind v fr i)) =
  ins-valid i v (int-valid vn cs)

-- The dual runs the same changes backwards, returning a crossing
-- argument to the name map the boundary was read on.  `Peel`'s
-- counterpart of `rewind-interior`; it needs no `BoundaryWf` either.
dual-interior : ∀ {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γᵢ ⊢ⁱ dual Θ ⇒ Γ
dual-interior (interior cs) = interior (dual-changes cs)

-- Merging: the outer's changes run first, on one and the same store.
merged-interior : ∀ {Θ₁ Θ₂ : Boundary} {Γ₁ᵢ : Ctxᵗ}
  → Γ ⊢ⁱ Θ₂ ⇒ Γᵢ
  → Γᵢ ⊢ⁱ Θ₁ ⇒ Γ₁ᵢ
  → Γ ⊢ⁱ Θ₁ ++ Θ₂ ⇒ Γ₁ᵢ
merged-interior (interior cs₂) (interior cs₁) =
  interior (changes-++ cs₂ cs₁)

-- A boundary changes names only: both readings keep the store.
interior-reps : ∀ {Θ : Boundary} → Γ ⊢ⁱ Θ ⇒ Γᵢ → reps Γᵢ ≡ reps Γ
interior-reps (interior cs) = refl

conversion-reps : ∀ {Θ : Boundary} → Γ ⊢ᶜ Θ ⇒ Γᶜ → reps Γᶜ ≡ reps Γ
conversion-reps (conversion cs) = refl

-- The conversion reading preserves both, for the same reasons.
conv-unique : Unique Δ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → Unique Δ′
conv-unique uq conv[] = uq
conv-unique uq (conv-unbind v cs) = conv-unique uq cs
conv-unique uq (conv-bind v cs fr i) = ins-unique i fr (conv-unique uq cs)
conv-unique uq (conv-bind-live v cs d) = conv-unique uq cs

conv-valid : ValidNames Ξ Δ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → ValidNames Ξ Δ′
conv-valid vn conv[] = vn
conv-valid vn (conv-unbind v cs) = conv-valid vn cs
conv-valid vn (conv-bind v cs fr i) = ins-valid i v (conv-valid vn cs)
conv-valid vn (conv-bind-live v cs d) = conv-valid vn cs

-- The lifted readings preserve name-map functionality independently of the
-- other two `WfCtx` fields.  `dual-unique` is the instance needed when a
-- crossed argument is wrapped in a boundary scope's dual.
interior-unique : ∀ {Θ : Boundary}
  → Unique (names Γ) → Γ ⊢ⁱ Θ ⇒ Γᵢ → Unique (names Γᵢ)
interior-unique uq (interior cs) = int-unique uq cs

conversion-unique : ∀ {Θ : Boundary}
  → Unique (names Γ) → Γ ⊢ᶜ Θ ⇒ Γᶜ → Unique (names Γᶜ)
conversion-unique uq (conversion cs) = conv-unique uq cs

dual-unique : ∀ {Γ Γᵢ Γᵈ : Ctxᵗ} {Θ : Boundary}
  → Unique (names Γ)
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γᵢ ⊢ᶜ dual Θ ⇒ Γᵈ
  → Unique (names Γᵈ)
dual-unique uq int dconv =
  conversion-unique (interior-unique uq int) dconv

------------------------------------------------------------------------
-- 3b. The name-set invariant for a crossed boundary scope
------------------------------------------------------------------------

-- (Q): the two conversion contexts straddled by `Peel` name the same
-- representation variables, though their ordinary positions may differ.
-- Commentary.md § Boundary.agda / §3b

data InUnbinds (α : RVar) : List Change → Set where
  iu-here  : ∀ {X χ} → InUnbinds α (unbind X α ∷ χ)
  iu-there : ∀ {δ χ} → InUnbinds α χ → InUnbinds α (δ ∷ χ)

data InBinds (α : RVar) : List Change → Set where
  ib-here  : ∀ {X χ} → InBinds α (bind X α ∷ χ)
  ib-there : ∀ {δ χ} → InBinds α χ → InBinds α (δ ∷ χ)

inUnbinds? : (α : RVar) (χ : List Change) → Dec (InUnbinds α χ)
inUnbinds? α [] = no (λ ())
inUnbinds? α (bind X β ∷ χ) with inUnbinds? α χ
inUnbinds? α (bind X β ∷ χ) | yes iu = yes (iu-there iu)
inUnbinds? α (bind X β ∷ χ) | no nl =
  no (λ where (iu-there iu) → nl iu)
inUnbinds? α (unbind X β ∷ χ) with α ≟ β
inUnbinds? α (unbind X β ∷ χ) | yes refl = yes iu-here
inUnbinds? α (unbind X β ∷ χ) | no ne with inUnbinds? α χ
inUnbinds? α (unbind X β ∷ χ) | no ne | yes iu = yes (iu-there iu)
inUnbinds? α (unbind X β ∷ χ) | no ne | no nl =
  no (λ where iu-here → ne refl
              (iu-there iu) → nl iu)

conv-mono : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → Δ ∋ᵅ α → Δ′ ∋ᵅ α
conv-mono conv[] lv = lv
conv-mono (conv-unbind v cs) lv = conv-mono cs lv
conv-mono (conv-bind v cs fr i) lv = ins-mono i (conv-mono cs lv)
conv-mono (conv-bind-live v cs d) lv = conv-mono cs lv

conv-binds : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′
  → InBinds α χ → Δ′ ∋ᵅ α
conv-binds (conv-unbind v cs) (ib-there ib) = conv-binds cs ib
conv-binds (conv-bind v cs fr i) ib-here = ins-live i
conv-binds (conv-bind v cs fr i) (ib-there ib) =
  ins-mono i (conv-binds cs ib)
conv-binds (conv-bind-live v cs d) ib-here = _ , d
conv-binds (conv-bind-live v cs d) (ib-there ib) =
  conv-binds cs ib

conv-inv : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → Δ′ ∋ᵅ α
  → Δ ∋ᵅ α ⊎ InBinds α χ
conv-inv conv[] lv = inj₁ lv
conv-inv (conv-unbind v cs) lv with conv-inv cs lv
conv-inv (conv-unbind v cs) lv | inj₁ l = inj₁ l
conv-inv (conv-unbind v cs) lv | inj₂ ib = inj₂ (ib-there ib)
conv-inv (conv-bind v cs fr i) lv with ins-inv i lv
conv-inv (conv-bind v cs fr i) lv | inj₁ refl = inj₂ ib-here
conv-inv (conv-bind v cs fr i) lv | inj₂ lv′ with conv-inv cs lv′
conv-inv (conv-bind v cs fr i) lv | inj₂ lv′ | inj₁ l = inj₁ l
conv-inv (conv-bind v cs fr i) lv | inj₂ lv′ | inj₂ ib =
  inj₂ (ib-there ib)
conv-inv (conv-bind-live v cs d) lv with conv-inv cs lv
conv-inv (conv-bind-live v cs d) lv | inj₁ l = inj₁ l
conv-inv (conv-bind-live v cs d) lv | inj₂ ib = inj₂ (ib-there ib)

int-keep : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → ¬ InUnbinds α χ → Δ ∋ᵅ α → Δᵢ ∋ᵅ α
int-keep changes[] nl lv = lv
int-keep (changes∷ cs (step-unbind v dl fr)) nl lv =
  del-mono dl (λ where refl → nl iu-here)
           (int-keep cs (λ iu → nl (iu-there iu)) lv)
int-keep (changes∷ cs (step-bind v fr i)) nl lv =
  ins-mono i (int-keep cs (λ iu → nl (iu-there iu)) lv)

int-bound : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → ¬ InUnbinds α χ
  → InBinds α χ → Δᵢ ∋ᵅ α
int-bound (changes∷ cs (step-unbind v dl fr)) nl (ib-there ib) =
  del-mono dl (λ where refl → nl iu-here)
           (int-bound cs (λ iu → nl (iu-there iu)) ib)
int-bound (changes∷ cs (step-bind v fr i)) nl ib-here = ins-live i
int-bound (changes∷ cs (step-bind v fr i)) nl (ib-there ib) =
  ins-mono i (int-bound cs (λ iu → nl (iu-there iu)) ib)

int-inv : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → Δᵢ ∋ᵅ α
  → Δ ∋ᵅ α ⊎ InBinds α χ
int-inv changes[] lv = inj₁ lv
int-inv (changes∷ cs (step-unbind v dl fr)) lv
  with int-inv cs (del-inv dl lv)
int-inv (changes∷ cs (step-unbind v dl fr)) lv | inj₁ l = inj₁ l
int-inv (changes∷ cs (step-unbind v dl fr)) lv | inj₂ ib =
  inj₂ (ib-there ib)
int-inv (changes∷ cs (step-bind v fr i)) lv with ins-inv i lv
int-inv (changes∷ cs (step-bind v fr i)) lv | inj₁ refl = inj₂ ib-here
int-inv (changes∷ cs (step-bind v fr i)) lv | inj₂ lv′
  with int-inv cs lv′
int-inv (changes∷ cs (step-bind v fr i)) lv | inj₂ lv′ | inj₁ l =
  inj₁ l
int-inv (changes∷ cs (step-bind v fr i)) lv | inj₂ lv′ | inj₂ ib =
  inj₂ (ib-there ib)

int-unbound : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → InUnbinds α χ
  → Δ ∋ᵅ α ⊎ InBinds α χ
int-unbound (changes∷ cs (step-unbind v dl fr)) iu-here
  with int-inv cs (del-live dl)
int-unbound (changes∷ cs (step-unbind v dl fr)) iu-here | inj₁ l = inj₁ l
int-unbound (changes∷ cs (step-unbind v dl fr)) iu-here | inj₂ ib =
  inj₂ (ib-there ib)
int-unbound (changes∷ cs (step-unbind v dl fr)) (iu-there iu)
  with int-unbound cs iu
int-unbound (changes∷ cs (step-unbind v dl fr)) (iu-there iu) | inj₁ l =
  inj₁ l
int-unbound (changes∷ cs (step-unbind v dl fr)) (iu-there iu) | inj₂ ib =
  inj₂ (ib-there ib)
int-unbound (changes∷ cs (step-bind v fr i)) (iu-there iu)
  with int-unbound cs iu
int-unbound (changes∷ cs (step-bind v fr i)) (iu-there iu) | inj₁ l =
  inj₁ l
int-unbound (changes∷ cs (step-bind v fr i)) (iu-there iu) | inj₂ ib =
  inj₂ (ib-there ib)

in-binds-++ˡ : ∀ {χ₂} → InBinds α χ → InBinds α (χ ++ χ₂)
in-binds-++ˡ ib-here = ib-here
in-binds-++ˡ (ib-there ib) = ib-there (in-binds-++ˡ ib)

in-binds-++ʳ : ∀ {χ₂} (χ₁ : List Change)
  → InBinds α χ₂ → InBinds α (χ₁ ++ χ₂)
in-binds-++ʳ [] ib = ib
in-binds-++ʳ (δ ∷ χ₁) ib = ib-there (in-binds-++ʳ χ₁ ib)

in-binds-++-inv : ∀ {χ₂} (χ₁ : List Change)
  → InBinds α (χ₁ ++ χ₂)
  → InBinds α χ₁ ⊎ InBinds α χ₂
in-binds-++-inv [] ib = inj₂ ib
in-binds-++-inv (bind X β ∷ χ₁) ib-here = inj₁ ib-here
in-binds-++-inv (bind X β ∷ χ₁) (ib-there ib)
  with in-binds-++-inv χ₁ ib
in-binds-++-inv (bind X β ∷ χ₁) (ib-there ib) | inj₁ a =
  inj₁ (ib-there a)
in-binds-++-inv (bind X β ∷ χ₁) (ib-there ib) | inj₂ b = inj₂ b
in-binds-++-inv (unbind X β ∷ χ₁) (ib-there ib)
  with in-binds-++-inv χ₁ ib
in-binds-++-inv (unbind X β ∷ χ₁) (ib-there ib) | inj₁ a =
  inj₁ (ib-there a)
in-binds-++-inv (unbind X β ∷ χ₁) (ib-there ib) | inj₂ b = inj₂ b

unbinds→dual : (χ : List Change) → InUnbinds α χ → InBinds α (dual χ)
unbinds→dual (unbind X β ∷ χ) iu-here
  rewrite unfold-reverse (unbind X β) χ
        | map-++ dualChange (reverse χ) (unbind X β ∷ []) =
  in-binds-++ʳ (dual χ) ib-here
unbinds→dual (unbind X β ∷ χ) (iu-there iu)
  rewrite unfold-reverse (unbind X β) χ
        | map-++ dualChange (reverse χ) (unbind X β ∷ []) =
  in-binds-++ˡ (unbinds→dual χ iu)
unbinds→dual (bind X β ∷ χ) (iu-there iu)
  rewrite unfold-reverse (bind X β) χ
        | map-++ dualChange (reverse χ) (bind X β ∷ []) =
  in-binds-++ˡ (unbinds→dual χ iu)

dual→unbinds : (χ : List Change) → InBinds α (dual χ) → InUnbinds α χ
dual→unbinds [] ()
dual→unbinds (unbind X β ∷ χ) ib
  rewrite unfold-reverse (unbind X β) χ
        | map-++ dualChange (reverse χ) (unbind X β ∷ [])
  with in-binds-++-inv (dual χ) ib
dual→unbinds (unbind X β ∷ χ) ib | inj₁ a = iu-there (dual→unbinds χ a)
dual→unbinds (unbind X β ∷ χ) ib | inj₂ ib-here = iu-here
dual→unbinds (bind X β ∷ χ) ib
  rewrite unfold-reverse (bind X β) χ
        | map-++ dualChange (reverse χ) (bind X β ∷ [])
  with in-binds-++-inv (dual χ) ib
dual→unbinds (bind X β ∷ χ) ib | inj₁ a = iu-there (dual→unbinds χ a)
dual→unbinds (bind X β ∷ χ) ib | inj₂ (ib-there ())

Q-changes : (χ : List Change)
  → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Ξ′ ∣ Δᵢ ⊢χᶜ dual χ ⇒ Δᵈ
  → Δᶜ ∋ᵅ α → Δᵈ ∋ᵅ α
Q-changes {α = α} χ int conv dconv lv with inUnbinds? α χ
Q-changes {α = α} χ int conv dconv lv | yes iu =
  conv-binds dconv (unbinds→dual χ iu)
Q-changes {α = α} χ int conv dconv lv | no nl with conv-inv conv lv
Q-changes {α = α} χ int conv dconv lv | no nl | inj₁ l =
  conv-mono dconv (int-keep int nl l)
Q-changes {α = α} χ int conv dconv lv | no nl | inj₂ ib =
  conv-mono dconv (int-bound int nl ib)

Q-changes-conv : (χ : List Change)
  → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Ξ′ ∣ Δᵢ ⊢χᶜ dual χ ⇒ Δᵈ
  → Δᵈ ∋ᵅ α → Δᶜ ∋ᵅ α
Q-changes-conv χ int conv dconv lv with conv-inv dconv lv
Q-changes-conv χ int conv dconv lv | inj₁ lvᵢ with int-inv int lvᵢ
Q-changes-conv χ int conv dconv lv | inj₁ lvᵢ | inj₁ l = conv-mono conv l
Q-changes-conv χ int conv dconv lv | inj₁ lvᵢ | inj₂ ib =
  conv-binds conv ib
Q-changes-conv χ int conv dconv lv | inj₂ iud
  with int-unbound int (dual→unbinds χ iud)
Q-changes-conv χ int conv dconv lv | inj₂ iud | inj₁ l = conv-mono conv l
Q-changes-conv χ int conv dconv lv | inj₂ iud | inj₂ ib =
  conv-binds conv ib

-- (Q) itself.
Q : ∀ {Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ} {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γᵢ ⊢ᶜ dual Θ ⇒ Γᵈ
  → (names Γᶜ) ∋ᵅ α → (names Γᵈ) ∋ᵅ α
Q {Θ = Θ} (interior cs) (conversion cc) (conversion dc) lv =
  Q-changes Θ cs cc dc lv

Q-inv : ∀ {Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ} {Θ : Boundary}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γᵢ ⊢ᶜ dual Θ ⇒ Γᵈ
  → (names Γᵈ) ∋ᵅ α → (names Γᶜ) ∋ᵅ α
Q-inv {Θ = Θ} (interior cs) (conversion cc) (conversion dc) lv =
  Q-changes-conv Θ cs cc dc lv

------------------------------------------------------------------------
-- 3c. The dual conversion context exists
------------------------------------------------------------------------

-- A conversion reading is MONOTONE in its starting name set: unbinds are
-- skipped, a bind either finds its name live or inserts it.
-- Commentary.md § Boundary.agda / §3c
conv-weaken : ∀ {Δ₀ χ} → Unique Δ → Unique Δ₀
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′
  → Δ ⊆ᵃ Δ₀
  → ∃[ Δ₀′ ] ((Ξ ∣ Δ₀ ⊢χᶜ χ ⇒ Δ₀′) × (Δ′ ⊆ᵃ Δ₀′))
conv-weaken uq uq₀ conv[] keep = _ , conv[] , keep
conv-weaken uq uq₀ (conv-unbind v cs) keep with conv-weaken uq uq₀ cs keep
conv-weaken uq uq₀ (conv-unbind v cs) keep | Δ₀′ , cs′ , keep′ =
  Δ₀′ , conv-unbind v cs′ , keep′
conv-weaken uq uq₀ (conv-bind v cs fr i) keep
  with conv-weaken uq uq₀ cs keep
conv-weaken uq uq₀ (conv-bind v cs fr i) keep
  | Δ₀′ , cs′ , keep′ with live? _ Δ₀′
conv-weaken uq uq₀ (conv-bind v cs fr i) keep
  | Δ₀′ , cs′ , keep′ | inj₁ live =
  Δ₀′ , conv-bind-live v cs′ (proj₂ live)
        , ins-cover i live keep′
conv-weaken uq uq₀ (conv-bind v cs fr i) keep
  | Δ₀′ , cs′ , keep′ | inj₂ fresh
  with ins-exists Δ₀′ _
         (≤-trans (ins-le i) (pigeon _ _ (conv-unique uq cs) keep′))
conv-weaken uq uq₀ (conv-bind v cs fr i) keep
  | Δ₀′ , cs′ , keep′ | inj₂ fresh | Δ₀″ , i′ =
  Δ₀″ , conv-bind v cs′ fresh i′
        , ins-cover i (ins-live i′) (λ lv → ins-mono i′ (keep′ lv))
conv-weaken uq uq₀ (conv-bind-live v cs d) keep
  with conv-weaken uq uq₀ cs keep
conv-weaken uq uq₀ (conv-bind-live v cs d) keep
  | Δ₀′ , cs′ , keep′ =
  Δ₀′ , conv-bind-live v cs′ (proj₂ (keep′ (_ , d))) , keep′

-- Appending an unbind makes it run first, and a conversion reading skips it.
conv-snoc-unbind : Ξ ∋ʳ α → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′
  → Ξ ∣ Δ ⊢χᶜ χ ++ (unbind X α ∷ []) ⇒ Δ′
conv-snoc-unbind v conv[] = conv-unbind v conv[]
conv-snoc-unbind v (conv-unbind w cs) = conv-unbind w (conv-snoc-unbind v cs)
conv-snoc-unbind v (conv-bind w cs fr i) =
  conv-bind w (conv-snoc-unbind v cs) fr i
conv-snoc-unbind v (conv-bind-live w cs d) =
  conv-bind-live w (conv-snoc-unbind v cs) d

sucle : ∀ {a b} → suc a ≤ suc b → a ≤ b
sucle (s≤s le) = le

dual-conv-exists : (χ : List Change) {Δ Δᵢ : TyCtx} (Δ₀ : TyCtx)
  → Unique Δ → Unique Δ₀
  → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → Δᵢ ⊆ᵃ Δ₀
  → ∃[ Δᵈ ] (Ξ ∣ Δ₀ ⊢χᶜ dual χ ⇒ Δᵈ)
dual-conv-exists [] Δ₀ uqΔ uq₀ changes[] k = Δ₀ , conv[]
dual-conv-exists (bind X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-bind v fr i)) k
  with dual-conv-exists χ Δ₀ uqΔ uq₀ cs (λ lv → k (ins-mono i lv))
dual-conv-exists (bind X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-bind v fr i)) k | Δᵈ , dc =
  Δᵈ , subst (λ l → _ ∣ Δ₀ ⊢χᶜ l ⇒ Δᵈ)
             (sym (dual-∷ (bind X α) χ))
             (conv-changes-++ (conv-unbind v conv[]) dc)
dual-conv-exists (unbind X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-unbind v dl fr)) k with live? α Δ₀
dual-conv-exists (unbind X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-unbind v dl fr)) k | inj₁ (Y , d)
  with dual-conv-exists χ Δ₀ uqΔ uq₀ cs (keeps-del dl (Y , d) k)
dual-conv-exists (unbind X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-unbind v dl fr)) k | inj₁ (Y , d)
                 | Δᵈ , dc =
  Δᵈ , subst (λ l → _ ∣ Δ₀ ⊢χᶜ l ⇒ Δᵈ)
             (sym (dual-∷ (unbind X α) χ))
             (conv-changes-++ (conv-bind-live v conv[] d) dc)
dual-conv-exists (unbind X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-unbind v dl fr)) k | inj₂ frα
  with ins-exists {α = α} Δ₀ X
         (sucle (≤-trans (del-lt dl)
                         (pigeon _ (α ∷ Δ₀) (int-unique uqΔ cs)
                                 (keeps-del dl (zero , here)
                                            (λ lv → ∋ᵅ-cons (k lv))))))
dual-conv-exists (unbind X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-unbind v dl fr)) k | inj₂ frα | Δ₁ , i
  with dual-conv-exists χ Δ₁ uqΔ (ins-unique i frα uq₀) cs
         (keeps-del dl (ins-live i) (λ lv → ins-mono i (k lv)))
dual-conv-exists (unbind X α ∷ χ) Δ₀ uqΔ uq₀
                 (changes∷ cs (step-unbind v dl fr)) k | inj₂ frα | Δ₁ , i
                 | Δᵈ , dc =
  Δᵈ , subst (λ l → _ ∣ Δ₀ ⊢χᶜ l ⇒ Δᵈ)
             (sym (dual-∷ (unbind X α) χ))
             (conv-changes-++ (conv-bind v conv[] frα i) dc)

dual-conversion-exists : ∀ {Γ Γᵢ : Ctxᵗ} {Θ : Boundary}
  → Unique (names Γ)
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → ∃[ Γᵈ ] (Γᵢ ⊢ᶜ dual Θ ⇒ Γᵈ)
dual-conversion-exists {Θ = Θ} uq (interior cs)
  with dual-conv-exists Θ _ uq (int-unique uq cs) cs (λ lv → lv)
dual-conversion-exists {Θ = Θ} uq (interior cs) | Δᵈ , dc =
  _ , conversion dc

-- THE TWO TRANSPORT THEOREMS.  These are what `BoundaryWf` used to take as
-- explicit obligations.
interior-wf : ∀ {Θ : Boundary} → WfCtx Γ
  → Γ ⊢ⁱ Θ ⇒ Γᵢ → WfCtx Γᵢ
interior-wf w (interior cs) =
  wf-ctx (wf-reps w) (int-valid (wf-names w) cs) (int-unique (name-fn w) cs)

conversion-wf : ∀ {Θ : Boundary} → WfCtx Γ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ → WfCtx Γᶜ
conversion-wf w (conversion cs) =
  wf-ctx (wf-reps w) (conv-valid (wf-names w) cs) (conv-unique (name-fn w) cs)

-- A complete boundary scope witness names both induced contexts.  The
-- output well-formedness is DERIVED (§3a), not stored.
record BoundaryWf (Γ : Ctxᵗ) (Θ : Boundary)
               (Γᵢ Γᶜ : Ctxᵗ) : Set where
  constructor bw
  field
    bw-exterior  : WfCtx Γ
    bw-interior  : Γ ⊢ⁱ Θ ⇒ Γᵢ
    bw-conversion : Γ ⊢ᶜ Θ ⇒ Γᶜ
open BoundaryWf public

-- The two former fields, now theorems; the names are unchanged.
bw-interior-wf : ∀ {Θ} → BoundaryWf Γ Θ Γᵢ Γᶜ → WfCtx Γᵢ
bw-interior-wf mwΘ = interior-wf (bw-exterior mwΘ) (bw-interior mwΘ)

bw-conversion-wf : ∀ {Θ} → BoundaryWf Γ Θ Γᵢ Γᶜ → WfCtx Γᶜ
bw-conversion-wf mwΘ = conversion-wf (bw-exterior mwΘ) (bw-conversion mwΘ)

-- The MERGED frame's conversion reading exists and retains every name
-- available at the inner frame's conversion context.
-- Commentary.md § Boundary.agda / §3c
merged-conversion-exists : ∀ {Γ Γᵢ Γᶜ Γ₁ᵢ Γ₁ᶜ : Ctxᵗ}
    {Θ₁ Θ₂ : Boundary}
  → BoundaryWf Γ Θ₂ Γᵢ Γᶜ
  → BoundaryWf Γᵢ Θ₁ Γ₁ᵢ Γ₁ᶜ
  → Σ[ Γ⋉ᶜ ∈ Ctxᵗ ]
      ((Γ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Γ⋉ᶜ) × (names Γ₁ᶜ ⊆ᵃ names Γ⋉ᶜ))
merged-conversion-exists
    (bw wf₂ (interior cs₂) (conversion cc₂))
    (bw wf₁ (interior cs₁) (conversion cc₁))
  with conv-weaken (name-fn wf₁)
         (name-fn (conversion-wf wf₂ (conversion cc₂)))
         cc₁ (int⇒conv-live cs₂ cc₂)
merged-conversion-exists
    (bw wf₂ (interior cs₂) (conversion cc₂))
    (bw wf₁ (interior cs₁) (conversion cc₁))
  | Δ⋉ᶜ , cc₁′ , keep =
  _ , conversion (conv-changes-++ cc₂ cc₁′) , keep
------------------------------------------------------------------------
-- 3d. Renaming the representation universe — the CONTEXT half
------------------------------------------------------------------------

-- Nothing here is arithmetic on ordinary positions, which is why the
-- ordinary spelling survives.
-- Commentary.md § Boundary.agda / §3d
step-ren : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → Ξ ∣ Δ ⊢δ δ ⇒ Δ′
  → Ξ′ ∣ map ρ Δ ⊢δ renᶠᴿ ρ δ ⇒ map ρ Δ′
step-ren {ρ = ρ} w (step-unbind (b , v) dl fr) =
  step-unbind (wk-look w v) (del-ren ρ dl) (fresh-ren (wk-inj w) fr)
step-ren {ρ = ρ} w (step-bind (b , v) fr i) =
  step-bind (wk-look w v) (fresh-ren (wk-inj w) fr) (ins-ren ρ i)

changes-ren : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → Ξ ∣ Δ ⊢χ χ ⇒ Δ′
  → Ξ′ ∣ map ρ Δ ⊢χ map (renᶠᴿ ρ) χ ⇒ map ρ Δ′
changes-ren w changes[] = changes[]
changes-ren w (changes∷ cs st) =
  changes∷ (changes-ren w cs) (step-ren w st)

conv-changes-ren : ∀ {ρ Ξ Ξ′} → RepWk ρ Ξ Ξ′ → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′
  → Ξ′ ∣ map ρ Δ ⊢χᶜ map (renᶠᴿ ρ) χ ⇒ map ρ Δ′
conv-changes-ren w conv[] = conv[]
conv-changes-ren w (conv-unbind (b , v) cs) =
  conv-unbind (wk-look w v) (conv-changes-ren w cs)
conv-changes-ren {ρ = ρ} w (conv-bind (b , v) cs fr i) =
  conv-bind (wk-look w v) (conv-changes-ren w cs)
    (fresh-ren (wk-inj w) fr) (ins-ren ρ i)
conv-changes-ren {ρ = ρ} w (conv-bind-live (b , v) cs d) =
  conv-bind-live (wk-look w v) (conv-changes-ren w cs) (∋ˡ-ren ρ d)
-- Both readings under a representation renaming.
interior-ren : ∀ {ρ Ξ Ξ′ Θ} {Γᵢ : Ctxᵗ} → RepWk ρ Ξ Ξ′
  → (Ξ ∣ Δ) ⊢ⁱ Θ ⇒ Γᵢ
  → (Ξ′ ∣ map ρ Δ) ⊢ⁱ renᴮᴿ ρ Θ ⇒ (Ξ′ ∣ map ρ (names Γᵢ))
interior-ren w (interior cs) = interior (changes-ren w cs)

conversion-ren : ∀ {ρ Ξ Ξ′ Θ} {Γᶜ : Ctxᵗ} → RepWk ρ Ξ Ξ′
  → (Ξ ∣ Δ) ⊢ᶜ Θ ⇒ Γᶜ
  → (Ξ′ ∣ map ρ Δ) ⊢ᶜ renᴮᴿ ρ Θ ⇒ (Ξ′ ∣ map ρ (names Γᶜ))
conversion-ren w (conversion cs) = conversion (conv-changes-ren w cs)

-- The snoc `Θ ++ (unbind 0 0 ∷ [])` carries a scope past one fresh cell
-- and one fresh ordinary name (`TyPeelR-⟪⟫`) — conversion reading.
-- Commentary.md § Boundary.agda / §3d
snoc-unbind0-conversion-ren : ∀ {Ξ Ξ′ Δ Θ Γᶜ}
  → RepWk suc Ξ Ξ′
  → Ξ′ ∋ʳ zero
  → Unique Δ
  → (Ξ ∣ Δ) ⊢ᶜ Θ ⇒ Γᶜ
  → Σ[ Γ′ᶜ ∈ Ctxᵗ ]
        (((Ξ′ ∣ (zero ∷ shiftReps Δ))
          ⊢ᶜ (renᴮᴿ suc Θ ++ (unbind 0 0 ∷ [])) ⇒ Γ′ᶜ)
        × (map suc (names Γᶜ) ⊆ᵃ (names Γ′ᶜ)))
snoc-unbind0-conversion-ren w v₀ uq (conversion cs)
  with conv-weaken (unique-shift uq)
         (unique∷ fresh-zero-shift (unique-shift uq))
         (conv-changes-ren w cs) ∋ᵅ-cons
snoc-unbind0-conversion-ren w v₀ uq (conversion cs) | Δ′ , cs′ , keep =
  _ , conversion (conv-snoc-unbind v₀ cs′) , keep

-- the interior reading: the appended unbind acts first.
snoc-unbind0-interior-ren : ∀ {Ξ Ξ′ Δ Θ Γᵢ}
  → RepWk suc Ξ Ξ′
  → Ξ′ ∋ʳ zero
  → (Ξ ∣ Δ) ⊢ⁱ Θ ⇒ Γᵢ
  → (Ξ′ ∣ (zero ∷ shiftReps Δ)) ⊢ⁱ (renᴮᴿ suc Θ ++ (unbind 0 0 ∷ [])) ⇒
      (Ξ′ ∣ map suc (names Γᵢ))
snoc-unbind0-interior-ren w v₀ (interior cs) =
  interior
    (changes-++
      (changes∷ changes[] (step-unbind v₀ del-here fresh-zero-shift))
      (changes-ren w cs))

------------------------------------------------------------------------
-- 4. Concrete boundary shapes
------------------------------------------------------------------------

-- `TyBeta` on `(Λ N) ·[ B , ℕ ]` at `empty`: the cell is allocated and
-- the scope binds name 0 for it.
TyBetaBoundary : Boundary
TyBetaBoundary = (bind 0 0 ∷ [])

TyBetaCtx : Ctxᵗ
TyBetaCtx = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

TyBeta-interior : allocate `ℕ empty ⊢ⁱ TyBetaBoundary ⇒ TyBetaCtx
TyBeta-interior =
  interior
    (changes∷ changes[] (step-bind (_ , here) fresh[] ins-here))

TyBeta-conversion : allocate `ℕ empty ⊢ᶜ TyBetaBoundary ⇒ TyBetaCtx
TyBeta-conversion =
  conversion
    (conv-bind (_ , here) conv[] fresh[] ins-here)

TyBetaCtx-wf : WfCtx TyBetaCtx
TyBetaCtx-wf =
  wf-ctx (wf-bindR wfᴿ-ℕ wf-reps[])
         (λ { here → _ , here })
         (unique∷ fresh[] unique[])

allocℕ-wf : WfCtx (allocate `ℕ empty)
allocℕ-wf = wf-ctx (wf-bindR wfᴿ-ℕ wf-reps[]) (λ ()) unique[]

TyBeta-bw : BoundaryWf (allocate `ℕ empty) TyBetaBoundary TyBetaCtx TyBetaCtx
TyBeta-bw = bw allocℕ-wf TyBeta-interior TyBeta-conversion

ΛXCtx : Ctxᵗ
ΛXCtx = underΛ empty

crossΛ : reps ΛXCtx ∣ names ΛXCtx ⊢δ unbind 0 0 ⇒ []
crossΛ = step-unbind (_ , here) del-here fresh[]

uncrossΛ : reps ΛXCtx ∣ [] ⊢δ bind 0 0 ⇒ names ΛXCtx
uncrossΛ = dual-step crossΛ
