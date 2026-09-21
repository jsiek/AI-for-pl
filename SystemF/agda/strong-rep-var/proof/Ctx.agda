module strong-rep-var.proof.Ctx where

-- File Charter:
--   * EVERY FACT ABOUT THE TWO DE BRUIJN UNIVERSES.  §1 is the
--     determinacy and uniqueness suite the reduction rules' `det`
--     consumes — `∋ˡ-det`, `∋ʳ-det`, `same-rep-unique`,
--     `same-target-unique`, `sameTy-src-unique`, `∋:=-det`,
--     `unique-lookup`, `unique-underΛ`, `wf-empty`.  §2 is the NAME-MAP
--     half of representation renaming (`extN-+`, `renameᵗ-fuse`,
--     `inj-extN`, `∋ˡ-ren`, `fresh-ren`).  §3 is the binder blocks
--     (`wfᴿ-push`, `wfRepCtx-push`, `∋ʳ-push`), the insert/delete
--     relations (`lookup→del`, `ins-exists`, `pigeon`, `live?`), and
--     name-set transport `⊆ᵃ-shiftRVars`; `RepWk` — its base instance
--     `repwk-abst₀` and the two closure
--     lemmas `repwk-abst`/`repwk-push`, with `wfctx-ren` and `∋:=-ren`.
--   * NOT THE DEFINITIONS.  Every judgement and relation named above is
--     declared in strong-rep-var.Ctx, which holds definitions only.  Anything
--     mentioning `Change` or `CtxMorph` belongs in strong-rep-var.CtxMorph —
--     including `repwk-wkN`, whose home is strong-rep-var.proof.RepWeaken.
--   * WHY THE SPLIT IS BY SUBJECT, NOT BY LAYER (notes/DECISIONS.md,
--     2026-09-20).  The second half is the context material that used
--     to sit in strong-rep-var.CtxMorph §1; moving it here is what lets
--     strong-rep-var.Ctx stay definition-only and lets strong-rep-var.CtxMorph
-- begin at
--     its §2.  The import list is strong-rep-var.Types,
-- strong-rep-var.proof.Types and
--     strong-rep-var.Ctx — keep it that way, since strong-rep-var.CtxMorph
-- imports this
--     module and a cycle is one careless import away.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (_≟_; +-cancelˡ-≡; suc-injective)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import strong-rep-var.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-var.proof.Types
open import strong-rep-var.Ctx

private
  variable
    Γ : Ctxᵗ
    Ξ : RepCtx
    Δ Δ′ Δ₁ Δ₂ η : TyCtx
    Rs : List Ty
    A B R S : Ty
    b b′ : RepBinding
    X Y : ℕ
    α β : RVar

------------------------------------------------------------------------
-- 1. Lookup, the two readings of `Ty`, and well-formedness
------------------------------------------------------------------------

∋ˡ-det : ∀ {A : Set} {xs : List A} {i x y}
  → xs ∋ˡ i := x → xs ∋ˡ i := y → x ≡ y
∋ˡ-det here here = refl
∋ˡ-det (there d) (there d′) = ∋ˡ-det d d′

base-wf : Base A → Γ ⊢ᵗ A
base-wf base-ℕ = wf-ℕ
base-wf base-𝔹 = wf-𝔹

same-rep-unique : η ⊢ A ~ R → η ⊢ A ~ S → R ≡ S
same-rep-unique (same-var d) (same-var d′) =
  cong `_ (∋ˡ-det d d′)
same-rep-unique same-ℕ same-ℕ = refl
same-rep-unique same-𝔹 same-𝔹 = refl
same-rep-unique (same-⇒ a b) (same-⇒ a′ b′) =
  cong₂ _⇒_ (same-rep-unique a a′) (same-rep-unique b b′)
same-rep-unique (same-∀ a) (same-∀ a′) =
  cong `∀ (same-rep-unique a a′)

fresh-not-lookup : Δ ∌ʳ α → Δ ∋ˡ X := α → ⊥
fresh-not-lookup (fresh∷ ne fresh) here = ne refl
fresh-not-lookup (fresh∷ ne fresh) (there d) = fresh-not-lookup fresh d

unique-lookup : Unique Δ → Δ ∋ˡ X := α → Δ ∋ˡ Y := α → X ≡ Y
unique-lookup (unique∷ fresh unique) here here = refl
unique-lookup (unique∷ fresh unique) here (there d) =
  ⊥-elim (fresh-not-lookup fresh d)
unique-lookup (unique∷ fresh unique) (there d) here =
  ⊥-elim (fresh-not-lookup fresh d)
unique-lookup (unique∷ fresh unique) (there d) (there d′) =
  cong suc (unique-lookup unique d d′)

fresh-zero-shift : shiftNames Δ ∌ʳ zero
fresh-zero-shift {Δ = []} = fresh[]
fresh-zero-shift {Δ = α ∷ Δ} =
  fresh∷ (λ ()) fresh-zero-shift

fresh-shift : Δ ∌ʳ α → shiftNames Δ ∌ʳ suc α
fresh-shift fresh[] = fresh[]
fresh-shift (fresh∷ ne fresh) =
  fresh∷ (λ eq → ne (suc-injective eq)) (fresh-shift fresh)

unique-shift : Unique Δ → Unique (shiftNames Δ)
unique-shift unique[] = unique[]
unique-shift (unique∷ fresh unique) =
  unique∷ (fresh-shift fresh) (unique-shift unique)

unique-underΛ : Unique (names Γ) → Unique (names (underΛ Γ))
unique-underΛ unique = unique∷ fresh-zero-shift (unique-shift unique)

-- For a unique name map, a representation-universe type has at most one
-- ordinary reading.
same-target-unique : Unique Δ → Δ ⊢ A ~ R → Δ ⊢ B ~ R → A ≡ B
same-target-unique unique (same-var d) (same-var d′) =
  cong `_ (unique-lookup unique d d′)
same-target-unique unique same-ℕ same-ℕ = refl
same-target-unique unique same-𝔹 same-𝔹 = refl
same-target-unique unique (same-⇒ a b) (same-⇒ a′ b′) =
  cong₂ _⇒_ (same-target-unique unique a a′)
             (same-target-unique unique b b′)
same-target-unique unique (same-∀ a) (same-∀ a′) =
  cong `∀ (same-target-unique
    (unique∷ fresh-zero-shift (unique-shift unique)) a a′)

-- A spelling CROSSES between the interior and the conversion context by
-- the representation it denotes, never by arithmetic on its position: the
-- two name maps can reorder relative to each other
-- (notes/ForallPayloadWall §3).  `_⊢_≈_⊣_` is that crossing, and on a
-- unique name map it is a function — which is what determinism needs from
-- the rules that carry it.
-- Stated on NAME MAPS: `_⊢_≈_⊣_`'s contexts reach the judgement only
-- through `names`, which is a projection and so does not determine them.
sameTy-src-unique : ∀ {η η′ A A₂ B} → Unique η
  → ∃[ R ] ((η ⊢ A ~ R) × (η′ ⊢ B ~ R))
  → ∃[ R ] ((η ⊢ A₂ ~ R) × (η′ ⊢ B ~ R))
  → A ≡ A₂
sameTy-src-unique unique (R , p , q) (R′ , p′ , q′)
  with same-rep-unique q q′
... | refl = same-target-unique unique p p′

∋ʳ-det : Ξ ∋ʳ α := b → Ξ ∋ʳ α := b′ → b ≡ b′
∋ʳ-det r-here r-here = refl
∋ʳ-det (r-there d) (r-there d′) =
  cong (renRepBinding suc) (∋ʳ-det d d′)
∋ʳ-det (r-there-abst d) (r-there-abst d′) =
  cong (renRepBinding suc) (∋ʳ-det d d′)

∋:=-det : Unique (names Γ) → Γ ∋ X := A → Γ ∋ X := B → A ≡ B
∋:=-det unique (α , R , name , rep , same)
                 (α′ , R′ , name′ , rep′ , same′)
  with ∋ˡ-det name name′
... | refl with ∋ʳ-det rep rep′
...   | refl = same-target-unique unique same same′

wf-empty : WfCtx empty
wf-empty = wf-ctx wf-reps[] (λ ()) unique[]

------------------------------------------------------------------------
-- 2. Renaming the representation universe — the NAME MAP half
------------------------------------------------------------------------

extN-+ : (n : ℕ) (ρ : Renameᵗ) (α : ℕ) → extN n ρ (n + α) ≡ n + ρ α
extN-+ zero    ρ α = refl
extN-+ (suc n) ρ α = cong suc (extN-+ n ρ α)

-- Renaming is a congruence, composes, and commutes with a shift.
extᵗ-cong : ∀ {ρ ρ′ : Renameᵗ} → (∀ X → ρ X ≡ ρ′ X)
  → ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
extᵗ-cong h zero    = refl
extᵗ-cong h (suc X) = cong suc (h X)

renameᵗ-cong : ∀ {ρ ρ′ : Renameᵗ} → (∀ X → ρ X ≡ ρ′ X)
  → ∀ A → renameᵗ ρ A ≡ renameᵗ ρ′ A
renameᵗ-cong h (` X)   = cong `_ (h X)
renameᵗ-cong h `ℕ      = refl
renameᵗ-cong h `𝔹      = refl
renameᵗ-cong h (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-cong h A) (renameᵗ-cong h B)
renameᵗ-cong h (`∀ A)  = cong `∀ (renameᵗ-cong (extᵗ-cong h) A)

extᵗ-fuse : (ρ σ : Renameᵗ) (X : ℕ)
  → extᵗ ρ (extᵗ σ X) ≡ extᵗ (λ Y → ρ (σ Y)) X
extᵗ-fuse ρ σ zero    = refl
extᵗ-fuse ρ σ (suc X) = refl

renameᵗ-fuse : (ρ σ : Renameᵗ) (A : Ty)
  → renameᵗ ρ (renameᵗ σ A) ≡ renameᵗ (λ X → ρ (σ X)) A
renameᵗ-fuse ρ σ (` X)   = refl
renameᵗ-fuse ρ σ `ℕ      = refl
renameᵗ-fuse ρ σ `𝔹      = refl
renameᵗ-fuse ρ σ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-fuse ρ σ A) (renameᵗ-fuse ρ σ B)
renameᵗ-fuse ρ σ (`∀ A)  =
  cong `∀ (trans (renameᵗ-fuse (extᵗ ρ) (extᵗ σ) A)
                 (renameᵗ-cong (extᵗ-fuse ρ σ) A))

renameᵗ-⇑ : (ρ : Renameᵗ) (A : Ty)
  → renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
renameᵗ-⇑ ρ A =
  trans (renameᵗ-fuse (extᵗ ρ) suc A)
        (sym (renameᵗ-fuse suc ρ A))

renRepBinding-⇑ : (ρ : Renameᵗ) (b : RepBinding)
  → renRepBinding (extᵗ ρ) (renRepBinding suc b)
      ≡ renRepBinding suc (renRepBinding ρ b)
renRepBinding-⇑ ρ abstR     = refl
renRepBinding-⇑ ρ (bindR R) = cong bindR (renameᵗ-⇑ ρ R)

inj-extᵗ : ∀ {ρ} → Injᵗ ρ → Injᵗ (extᵗ ρ)
inj-extᵗ inj {zero}  {zero}  eq = refl
inj-extᵗ inj {suc α} {suc β} eq = cong suc (inj (suc-injective eq))

inj-extN : ∀ {ρ} (n : ℕ) → Injᵗ ρ → Injᵗ (extN n ρ)
inj-extN zero    inj = inj
inj-extN (suc n) inj = inj-extᵗ (inj-extN n inj)

∋ˡ-ren : (ρ : Renameᵗ) → Δ ∋ˡ X := α → map ρ Δ ∋ˡ X := ρ α
∋ˡ-ren ρ here      = here
∋ˡ-ren ρ (there d) = there (∋ˡ-ren ρ d)

∋ˡ-ren⁻ : (ρ : Renameᵗ) (Δ : TyCtx) {γ : RVar} → map ρ Δ ∋ˡ X := γ
  → ∃[ α ] ((Δ ∋ˡ X := α) × (γ ≡ ρ α))
∋ˡ-ren⁻ ρ (α ∷ Δ) here = α , here , refl
∋ˡ-ren⁻ ρ (α ∷ Δ) (there d) with ∋ˡ-ren⁻ ρ Δ d
∋ˡ-ren⁻ ρ (α ∷ Δ) (there d) | β , d′ , eq = β , there d′ , eq

fresh-ren : ∀ {ρ} → Injᵗ ρ → Δ ∌ʳ α → map ρ Δ ∌ʳ ρ α
fresh-ren inj fresh[] = fresh[]
fresh-ren inj (fresh∷ ne fr) =
  fresh∷ (λ eq → ne (inj eq)) (fresh-ren inj fr)

unique-ren : ∀ {ρ} → Injᵗ ρ → Unique Δ → Unique (map ρ Δ)
unique-ren inj unique[] = unique[]
unique-ren inj (unique∷ fr uq) =
  unique∷ (fresh-ren inj fr) (unique-ren inj uq)

shiftNames-ren : (ρ : Renameᵗ) (Δ : TyCtx)
  → map (extᵗ ρ) (shiftNames Δ) ≡ shiftNames (map ρ Δ)
shiftNames-ren ρ []      = refl
shiftNames-ren ρ (α ∷ Δ) = cong (suc (ρ α) ∷_) (shiftNames-ren ρ Δ)

names-underΛ-ren : (ρ : Renameᵗ) (Δ : TyCtx)
  → map (extᵗ ρ) (zero ∷ shiftNames Δ) ≡ zero ∷ shiftNames (map ρ Δ)
names-underΛ-ren ρ Δ = cong (zero ∷_) (shiftNames-ren ρ Δ)

-- The representation READING of an ordinary type moves with the map: the
-- ordinary spelling is untouched and the representation it denotes is
-- renamed.
same-cast : ∀ {η η′ : TyCtx} {A R : Ty} → η ≡ η′ → η ⊢ A ~ R → η′ ⊢ A ~ R
same-cast refl p = p

same-ren : (ρ : Renameᵗ) → η ⊢ A ~ R → map ρ η ⊢ A ~ renameᵗ ρ R
same-ren ρ (same-var d) = same-var (∋ˡ-ren ρ d)
same-ren ρ same-ℕ = same-ℕ
same-ren ρ same-𝔹 = same-𝔹
same-ren ρ (same-⇒ p q) = same-⇒ (same-ren ρ p) (same-ren ρ q)
same-ren {η = η} ρ (same-∀ p) =
  same-∀ (same-cast (names-underΛ-ren ρ η) (same-ren (extᵗ ρ) p))

-- Ordinary type formation reads the name map for POSITIONS only, so it
-- transports along any representation renaming whatever.
-- Stated on the NAME MAP: the source representation context plays no
-- part in `∋tv`, so naming it would leave an unsolvable implicit.
tv-ren : (ρ : Renameᵗ)
  → ∃[ α ] (η ∋ˡ X := α) → ∃[ α ] (map ρ η ∋ˡ X := α)
tv-ren ρ (α , d) = ρ α , ∋ˡ-ren ρ d

wf-cast : ∀ {Ξ : RepCtx} {η η′ : TyCtx} {A : Ty} → η ≡ η′
  → (Ξ ∣ η) ⊢ᵗ A → (Ξ ∣ η′) ⊢ᵗ A
wf-cast refl w = w

wf-ren-rep : ∀ {Ξ Ξ′ : RepCtx} {ρ} → (Ξ ∣ η) ⊢ᵗ A → (Ξ′ ∣ map ρ η) ⊢ᵗ A
wf-ren-rep {ρ = ρ} (wf-var tv) = wf-var (tv-ren ρ tv)
wf-ren-rep wf-ℕ = wf-ℕ
wf-ren-rep wf-𝔹 = wf-𝔹
wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} (wf-⇒ wA wB) =
  wf-⇒ (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wA)
       (wf-ren-rep {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} wB)
wf-ren-rep {η = η} {Ξ = Ξ} {Ξ′ = Ξ′} {ρ = ρ} (wf-∀ wA) =
  wf-∀ (wf-cast (names-underΛ-ren ρ η)
                (wf-ren-rep {Ξ = abstR ∷ Ξ} {Ξ′ = abstR ∷ Ξ′}
                            {ρ = extᵗ ρ} wA))

------------------------------------------------------------------------
-- 3. Binder blocks, insert/delete, and RepWk
------------------------------------------------------------------------

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

insert-delete : α ⊢- Δ at X ⇒ Δ′ → α ⊢+ Δ′ at X ⇒ Δ
insert-delete del-here = ins-here
insert-delete (del-there d) = ins-there (insert-delete d)

delete-insert : α ⊢+ Δ at X ⇒ Δ′ → α ⊢- Δ′ at X ⇒ Δ
delete-insert ins-here = del-here
delete-insert (ins-there i) = del-there (delete-insert i)

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

∋ˡ-push : (Rs : List Ty) → Ξ ∋ˡ α := b
  → pushRepBinds Rs Ξ ∋ˡ (length Rs + α) := b
∋ˡ-push [] d = d
∋ˡ-push (S ∷ Rs) d = there (∋ˡ-push Rs d)

∋ˡ-shiftRVars : (n : ℕ) (Δ : TyCtx) {γ : RVar} → shiftRVars n Δ ∋ˡ X := γ
  → ∃[ α ] ((Δ ∋ˡ X := α) × (γ ≡ n + α))
∋ˡ-shiftRVars n (α ∷ Δ) here = α , here , refl
∋ˡ-shiftRVars n (α ∷ Δ) (there d) with ∋ˡ-shiftRVars n Δ d
∋ˡ-shiftRVars n (α ∷ Δ) (there d) | β , d′ , eq = β , there d′ , eq

⊆ᵃ-shiftRVars : (n : ℕ) → Δ ⊆ᵃ Δ′
  → shiftRVars n Δ ⊆ᵃ shiftRVars n Δ′
⊆ᵃ-shiftRVars {Δ = Δ} n keep (X , d)
  with ∋ˡ-shiftRVars n Δ d
⊆ᵃ-shiftRVars n keep (X , d) | α , d′ , refl with keep (X , d′)
⊆ᵃ-shiftRVars n keep (X , d) | α , d′ , refl | Y , d″ =
  Y , ∋ˡ-ren (n +_) d″

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

-- A representation payload looked up THROUGH a bind block is the payload
-- shifted past that block.
∋ʳ-push : (Rs : List Ty) → Ξ ∋ʳ α := bindR R
  → pushRepBinds Rs Ξ ∋ʳ (length Rs + α) := bindR (shiftBy (length Rs) R)
∋ʳ-push [] d = d
∋ʳ-push (S ∷ Rs) d = r-there (∋ʳ-push Rs d)

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

⊆ᵃ-underΛ : Δ ⊆ᵃ Δ′
  → (zero ∷ shiftNames Δ) ⊆ᵃ (zero ∷ shiftNames Δ′)
⊆ᵃ-underΛ f (zero , here) = zero , here
⊆ᵃ-underΛ {Δ = Δ} f (suc X , there d) with live-shift-inv Δ (X , d)
⊆ᵃ-underΛ {Δ = Δ} f (suc X , there d) | β , lv , refl =
  ∋ᵅ-cons (live-shift (f lv))

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

keeps-del : ∀ {Δ₀} → α ⊢- Δ at X ⇒ Δ′ → Δ₀ ∋ᵅ α
  → Δ′ ⊆ᵃ Δ₀ → Δ ⊆ᵃ Δ₀
keeps-del {α = α} dl lvα k {β} lv with β ≟ α
keeps-del {α = α} dl lvα k {β} lv | yes refl = lvα
keeps-del {α = α} dl lvα k {β} lv | no ne = k (del-mono dl ne lv)

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

del-ren : (ρ : Renameᵗ) → α ⊢- Δ at X ⇒ Δ′
  → ρ α ⊢- map ρ Δ at X ⇒ map ρ Δ′
del-ren ρ del-here = del-here
del-ren ρ (del-there dl) = del-there (del-ren ρ dl)

ins-ren : (ρ : Renameᵗ) → α ⊢+ Δ at X ⇒ Δ′
  → ρ α ⊢+ map ρ Δ at X ⇒ map ρ Δ′
ins-ren ρ ins-here = ins-here
ins-ren ρ (ins-there i) = ins-there (ins-ren ρ i)

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
