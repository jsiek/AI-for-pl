module strong.Ctx where

-- Strong System F -- ordinary type variables and representation variables.
--
-- The two uses of the old type-variable slots are split into distinct de
-- Bruijn universes:
--
--   * `names Γ` contains exactly the ordinary type variables currently in
--     scope. An entry is the representation variable named by that ordinary
--     variable. A concealed ordinary variable has no entry here.
--
--   * `reps Γ` contains abstract and represented representation variables.
--     A represented payload is a `Ty` whose FREE indices range over this
--     representation-variable universe. A `∀` inside the payload binds an
--     ordinary local type variable in the usual way.
--
-- A term-level `Λ` extends both universes: it binds an abstract representation
-- variable and an ordinary type variable that names it. Context morphisms
-- extend the representation universe and change the ordinary name map; those
-- operations live in strong.CtxMorph.

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)

------------------------------------------------------------------------
-- 1. The two de Bruijn universes
------------------------------------------------------------------------

RVar : Set
RVar = ℕ

data RepBinding : Set where
  abstR : RepBinding
  bindR : Ty → RepBinding

RepCtx : Set
RepCtx = List RepBinding

TyCtx : Set
TyCtx = List RVar

record Ctxᵗ : Set where
  constructor _∣_
  field
    reps  : RepCtx
    names : TyCtx
open Ctxᵗ public

-- View one context's ordinary names after a representation renaming, using a
-- second context's representation store.  Crossings use this when the same
-- ordinary spelling is carried across an inserted representation binder: the
-- positions stay fixed, but the representation indices they denote move.
renNameCtx : Renameᵗ → Ctxᵗ → Ctxᵗ → Ctxᵗ
renNameCtx ρ target source = reps target ∣ map ρ (names source)

private
  variable
    Γ Γ′ : Ctxᵗ
    Ξ : RepCtx
    Δ Δ′ η : TyCtx
    A B R S : Ty
    b b′ : RepBinding
    X Y i n : ℕ
    α β : RVar

------------------------------------------------------------------------
-- 2. Lookup
------------------------------------------------------------------------

infix 4 _∋ˡ_:=_
data _∋ˡ_:=_ {A : Set} : List A → ℕ → A → Set where
  here  : ∀ {x xs} → (x ∷ xs) ∋ˡ zero := x
  there : ∀ {x y xs i} → xs ∋ˡ i := x → (y ∷ xs) ∋ˡ suc i := x

∋ˡ-det : ∀ {A : Set} {xs : List A} {i x y}
  → xs ∋ˡ i := x → xs ∋ˡ i := y → x ≡ y
∋ˡ-det here here = refl
∋ˡ-det (there d) (there d′) = ∋ˡ-det d d′

-- An ordinary type variable names a representation variable.
infix 4 _∋ᵗ_:=_
_∋ᵗ_:=_ : Ctxᵗ → ℕ → RVar → Set
Γ ∋ᵗ X := α = names Γ ∋ˡ X := α

infix 4 _∋tv_
_∋tv_ : Ctxᵗ → ℕ → Set
Γ ∋tv X = ∃[ α ] Γ ∋ᵗ X := α

renRepBinding : Renameᵗ → RepBinding → RepBinding
renRepBinding ρ abstR     = abstR
renRepBinding ρ (bindR R) = bindR (renameᵗ ρ R)

-- A representation payload is stored outside its own binder. Looking it up
-- shifts it through that binder and every newer representation binder.
infix 4 _∋ʳ_:=_
data _∋ʳ_:=_ : RepCtx → RVar → RepBinding → Set where
  r-here  : (b ∷ Ξ) ∋ʳ zero := renRepBinding suc b
  r-there : Ξ ∋ʳ α := b
    → (bindR R ∷ Ξ) ∋ʳ suc α := renRepBinding suc b
  r-there-abst : Ξ ∋ʳ α := b
    → (abstR ∷ Ξ) ∋ʳ suc α := renRepBinding suc b

infix 4 _∋rep_:=_
_∋rep_:=_ : Ctxᵗ → RVar → Ty → Set
Γ ∋rep α := R = reps Γ ∋ʳ α := bindR R

-- The composite lookup used by conversions: ordinary X names α, whose
-- representation is R.
infix 4 _∋_:=ᴿ_
_∋_:=ᴿ_ : Ctxᵗ → ℕ → Ty → Set
Γ ∋ X :=ᴿ R = ∃[ α ] ((Γ ∋ᵗ X := α) × (Γ ∋rep α := R))

------------------------------------------------------------------------
-- 3. Ordinary types
------------------------------------------------------------------------

shiftNames : TyCtx → TyCtx
shiftNames = map suc

-- A term-level `Λ` and the premise of ordinary `∀` formation bind both an
-- ordinary type variable and an abstract representation variable.
underΛ : Ctxᵗ → Ctxᵗ
underΛ (Ξ ∣ Δ) = (abstR ∷ Ξ) ∣ (zero ∷ shiftNames Δ)

infix 4 _⊢ᵗ_
data _⊢ᵗ_ : Ctxᵗ → Ty → Set where
  wf-var : Γ ∋tv X → Γ ⊢ᵗ ` X
  wf-ℕ   : Γ ⊢ᵗ `ℕ
  wf-𝔹   : Γ ⊢ᵗ `𝔹
  wf-⇒   : Γ ⊢ᵗ A → Γ ⊢ᵗ B → Γ ⊢ᵗ A ⇒ B
  wf-∀   : underΛ Γ ⊢ᵗ A → Γ ⊢ᵗ `∀ A

data Base : Ty → Set where
  base-ℕ : Base `ℕ
  base-𝔹 : Base `𝔹

base-wf : Base A → Γ ⊢ᵗ A
base-wf base-ℕ = wf-ℕ
base-wf base-𝔹 = wf-𝔹

------------------------------------------------------------------------
-- 4. Representation payloads
------------------------------------------------------------------------

-- A payload has a mixed de Bruijn interpretation. The first `n` indices are
-- ordinary variables bound by enclosing payload `∀`s. Index `n + α` is the
-- free representation variable α.
infix 4 _⊢ref[_]_
data _⊢ref[_]_ (Ξ : RepCtx) (n : ℕ) : ℕ → Set where
  local-ref : i < n → Ξ ⊢ref[ n ] i
  free-ref  : Ξ ∋ˡ α := b → Ξ ⊢ref[ n ] (n + α)

infix 4 _⊢ᴿ[_]_
data _⊢ᴿ[_]_ (Ξ : RepCtx) (n : ℕ) : Ty → Set where
  wfᴿ-var : Ξ ⊢ref[ n ] i → Ξ ⊢ᴿ[ n ] ` i
  wfᴿ-ℕ   : Ξ ⊢ᴿ[ n ] `ℕ
  wfᴿ-𝔹   : Ξ ⊢ᴿ[ n ] `𝔹
  wfᴿ-⇒   : Ξ ⊢ᴿ[ n ] R → Ξ ⊢ᴿ[ n ] S → Ξ ⊢ᴿ[ n ] R ⇒ S
  wfᴿ-∀   : Ξ ⊢ᴿ[ suc n ] R → Ξ ⊢ᴿ[ n ] `∀ R

infix 4 _⊢ᴿ_
_⊢ᴿ_ : RepCtx → Ty → Set
Ξ ⊢ᴿ R = Ξ ⊢ᴿ[ zero ] R

-- A concrete representation is checked outside its own binder.
data WfRepCtx : RepCtx → Set where
  wf-reps[] : WfRepCtx []
  wf-abstR  : WfRepCtx Ξ → WfRepCtx (abstR ∷ Ξ)
  wf-bindR  : Ξ ⊢ᴿ R → WfRepCtx Ξ → WfRepCtx (bindR R ∷ Ξ)

------------------------------------------------------------------------
-- 5. Relating the two readings of `Ty`
------------------------------------------------------------------------

-- Free ordinary variables are translated through the name map. A `∀`
-- extends only the LOCAL binder prefix on both sides; it does not allocate a
-- free representation variable.
infix 4 _⊢_~_
data _⊢_~_ (η : TyCtx) : Ty → Ty → Set where
  same-var : η ∋ˡ X := α → η ⊢ ` X ~ ` α
  same-ℕ   : η ⊢ `ℕ ~ `ℕ
  same-𝔹   : η ⊢ `𝔹 ~ `𝔹
  same-⇒   : η ⊢ A ~ R → η ⊢ B ~ S → η ⊢ A ⇒ B ~ R ⇒ S
  same-∀   : (zero ∷ shiftNames η) ⊢ A ~ R → η ⊢ `∀ A ~ `∀ R

infix 4 _⊢ᶜ_~_
_⊢ᶜ_~_ : Ctxᵗ → Ty → Ty → Set
Γ ⊢ᶜ A ~ R = names Γ ⊢ A ~ R

same-rep-unique : η ⊢ A ~ R → η ⊢ A ~ S → R ≡ S
same-rep-unique (same-var d) (same-var d′) =
  cong `_ (∋ˡ-det d d′)
same-rep-unique same-ℕ same-ℕ = refl
same-rep-unique same-𝔹 same-𝔹 = refl
same-rep-unique (same-⇒ a b) (same-⇒ a′ b′) =
  cong₂ _⇒_ (same-rep-unique a a′) (same-rep-unique b b′)
same-rep-unique (same-∀ a) (same-∀ a′) =
  cong `∀ (same-rep-unique a a′)

-- Two ordinary types at the same representation depth denote the same
-- representation-universe type. `lock` and `unlock` may give that type
-- different ordinary de Bruijn spellings.
SameTy : Ctxᵗ → Ty → Ctxᵗ → Ty → Set
SameTy Γ A Γ′ B = ∃[ R ] ((Γ ⊢ᶜ A ~ R) × (Γ′ ⊢ᶜ B ~ R))

shiftRep : ℕ → Ty → Ty
shiftRep zero    R = R
shiftRep (suc n) R = ⇑ᵗ (shiftRep n R)

-- A morphism's representation binders occur in its conversion context but
-- not in its exterior context. Thus an exterior representation reading must
-- cross that bind prefix before it can be compared with a conversion type.
SameTyExt : ℕ → Ctxᵗ → Ty → Ctxᵗ → Ty → Set
SameTyExt n Γ A Γ′ B =
  ∃[ R ] ((Γ ⊢ᶜ A ~ R) × (Γ′ ⊢ᶜ B ~ shiftRep n R))

-- The conversion lookup square. Ordinary X names α; α is represented by R;
-- and ordinary A is R read through the current ordinary-name assignment.
infix 4 _∋_:=_
_∋_:=_ : Ctxᵗ → ℕ → Ty → Set
Γ ∋ X := A =
  ∃[ α ] ∃[ R ]
    ((Γ ∋ᵗ X := α) × (Γ ∋rep α := R) × (Γ ⊢ᶜ A ~ R))

------------------------------------------------------------------------
-- 6. Context well-formedness
------------------------------------------------------------------------

data Fresh : RVar → TyCtx → Set where
  fresh[] : Fresh α []
  fresh∷  : α ≢ β → Fresh α Δ → Fresh α (β ∷ Δ)

data Unique : TyCtx → Set where
  unique[] : Unique []
  unique∷  : Fresh α Δ → Unique Δ → Unique (α ∷ Δ)

fresh-not-lookup : Fresh α Δ → Δ ∋ˡ X := α → ⊥
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

fresh-zero-shift : Fresh zero (shiftNames Δ)
fresh-zero-shift {Δ = []} = fresh[]
fresh-zero-shift {Δ = α ∷ Δ} =
  fresh∷ (λ ()) fresh-zero-shift

fresh-shift : Fresh α Δ → Fresh (suc α) (shiftNames Δ)
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
-- (notes/ForallPayloadWall §3).  `SameTy` is that crossing, and on a
-- unique name map it is a function — which is what determinism needs from
-- the rules that carry it.
-- Stated on NAME MAPS: `SameTy`'s contexts reach the judgement only
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

ValidNames : RepCtx → TyCtx → Set
ValidNames Ξ Δ = ∀ {X α} → Δ ∋ˡ X := α → ∃[ b ] Ξ ∋ˡ α := b

record WfCtx (Γ : Ctxᵗ) : Set where
  constructor wf-ctx
  field
    wf-reps  : WfRepCtx (reps Γ)
    wf-names : ValidNames (reps Γ) (names Γ)
    name-fn  : Unique (names Γ)
open WfCtx public

------------------------------------------------------------------------
-- 7. Small formation checks
------------------------------------------------------------------------

empty : Ctxᵗ
empty = [] ∣ []

wf-empty : WfCtx empty
wf-empty = wf-ctx wf-reps[] (λ ()) unique[]

-- In `∀ Z. Z ⇒ α`, zero is the local Z and one is the free α.
∀-payload-wf : abstR ∷ [] ⊢ᴿ `∀ (` 0 ⇒ ` 1)
∀-payload-wf =
  wfᴿ-∀
    (wfᴿ-⇒ (wfᴿ-var (local-ref (s≤s z≤n)))
           (wfᴿ-var (free-ref here)))

------------------------------------------------------------------------
-- 8. Renaming the representation universe — the NAME MAP half
------------------------------------------------------------------------

-- A REPRESENTATION-ONLY renaming moves representation variables and
-- leaves every ordinary POSITION exactly where it was.  On a name map
-- that is `map ρ`: a lookup keeps its ordinary index and changes only the
-- representation variable it names.  This section is everything that
-- transport needs from the name map alone; the representation-CONTEXT
-- half — where a payload must move too — is strong.CtxMorph §3d.

-- `extN n ρ` renames underneath n binders.  It is used at two depths:
-- `n` local `∀`s inside a representation payload, and the `n` parallel
-- representation binders a morphism's bind block introduces.
extN : ℕ → Renameᵗ → Renameᵗ
extN zero    ρ = ρ
extN (suc n) ρ = extᵗ (extN n ρ)

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

-- An INJECTIVE renaming is what a name map needs: `lock` records that the
-- name it deleted is now fresh, and freshness is not preserved by a map
-- that identifies two representation variables.
Injᵗ : Renameᵗ → Set
Injᵗ ρ = ∀ {α β} → ρ α ≡ ρ β → α ≡ β

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

fresh-ren : ∀ {ρ} → Injᵗ ρ → Fresh α Δ → Fresh (ρ α) (map ρ Δ)
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
