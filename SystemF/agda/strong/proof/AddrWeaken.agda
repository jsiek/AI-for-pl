module strong.proof.AddrWeaken where

-- Strong System F v8 — carrying a judgment under a new BASE binder.
--
-- The color wrap needs this: substituting under a `Λ` sends the value
-- across a boundary, and the `Λ` binds an address, so the value's base
-- addresses shift.  Crossing a `ν` is the same with a `nuBind` entry.
--
-- With the address universe split (`strong.RepresentationTypes`) this
-- is an ORDINARY renaming lemma.  The base renaming `ρ` moves `bse`
-- alone: `bnd` and `lvl` are fixed, so a conversion's crossings keep
-- their addresses, the pop judgment sees the same stack shape, and
-- there is no depth to thread through the boundary.  What moves under
-- a binder is the base: `Λ` and `ν` extend `ρ`, a `∀` does not.

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.proof.Interior using (pop-base)
open import strong.Terms
open import strong.TermSubst

private
  variable
    Sg : Store
    Γ Γ′ Γᵢ Γₑ : Ctxᵗ
    Ss Ss′ : List StackEnt
    Bs Bs′ : List BaseEnt
    A B C D : Ty
    R T : RepTy
    X : ℕ
    α β : Addr
    ρ : Renameᵇ
    c s t : Conv
    ĉ : ConvElt

------------------------------------------------------------------------
-- A base renaming between contexts
------------------------------------------------------------------------
-- Three closure properties, one per lookup.  Names are NOT renamed —
-- a base push adds none — but the address a name is assigned to moves,
-- which is exactly what `renStk` does to the stack.

record Renamesᵇ (Sg : Store) (ρ : Renameᵇ) (Γ Γ′ : Ctxᵗ) : Set where
  field
    -- a STORED representation is base-closed, so the store case of
    -- every lookup is fixed (`lvl-fixed`, below)
    ren-ok : StoreOk Sg
    ren-a : ∀ {α} → Sg ∣ Γ ∋a α → Sg ∣ Γ′ ∋a renᵃᵉ ρ α
    ren-n : ∀ {X α} → Γ ∋n X := α → Γ′ ∋n X := renᵃᵉ ρ α
    ren-r : ∀ {α R} → Sg ∣ Γ ∋r α := R
          → Sg ∣ Γ′ ∋r renᵃᵉ ρ α := renameᴿᵉ ρ R
    -- the NEGATIVE premises (`NotAssigned`, on `unseal`/`hide`/`show`)
    -- need the name lookups to REFLECT, not just to transport
    ren-n⁻ : ∀ {X α} → Γ′ ∋n X := α
           → Σ[ β ∈ Addr ] ((Γ ∋n X := β) × (α ≡ renᵃᵉ ρ β))
    ren-inj : ∀ {α β} → renᵃᵉ ρ α ≡ renᵃᵉ ρ β → α ≡ β
open Renamesᵇ

------------------------------------------------------------------------
-- The commutations the closure lemmas need
------------------------------------------------------------------------
-- The two renaming families act on disjoint address forms, so they
-- commute — pointwise on addresses, hence on representation types.

renᵃ-comm : ∀ ρ η α
  → renᵃᵉ ρ (renᵃ η α) ≡ renᵃ η (renᵃᵉ ρ α)
renᵃ-comm ρ η (lvl ℓ) = refl
renᵃ-comm ρ η (bnd i) = refl
renᵃ-comm ρ η (bse j) = refl

renᴿ-comm : ∀ ρ η R
  → renameᴿᵉ ρ (renameᴿ η R) ≡ renameᴿ η (renameᴿᵉ ρ R)
renᴿ-comm ρ η (`ᵃ α) = cong `ᵃ_ (renᵃ-comm ρ η α)
renᴿ-comm ρ η `ℕᴿ = refl
renᴿ-comm ρ η `𝔹ᴿ = refl
renᴿ-comm ρ η (R ⇒ᴿ T) = cong₂′ (renᴿ-comm ρ η R) (renᴿ-comm ρ η T)
  where
  cong₂′ : ∀ {R R′ T T′} → R ≡ R′ → T ≡ T′ → R ⇒ᴿ T ≡ R′ ⇒ᴿ T′
  cong₂′ refl refl = refl
renᴿ-comm ρ η (`∀ᴿ R) = cong `∀ᴿ (renᴿ-comm ρ (extᵇ η) R)

-- the instance every `r-skip-bind` uses
renᴿ-⇑ : ∀ ρ R → renameᴿᵉ ρ (⇑ᴿ R) ≡ ⇑ᴿ (renameᴿᵉ ρ R)
renᴿ-⇑ ρ R = renᴿ-comm ρ suc R

-- and the one every base skip uses, after the renaming is extended
renᴿ-⇑ᵉ : ∀ ρ R → renameᴿᵉ (extᵇ ρ) (⇑ᴿᵉ R) ≡ ⇑ᴿᵉ (renameᴿᵉ ρ R)
renᴿ-⇑ᵉ ρ (`ᵃ lvl ℓ) = refl
renᴿ-⇑ᵉ ρ (`ᵃ bnd i) = refl
renᴿ-⇑ᵉ ρ (`ᵃ bse j) = refl
renᴿ-⇑ᵉ ρ `ℕᴿ = refl
renᴿ-⇑ᵉ ρ `𝔹ᴿ = refl
renᴿ-⇑ᵉ ρ (R ⇒ᴿ T) = cong₂′ (renᴿ-⇑ᵉ ρ R) (renᴿ-⇑ᵉ ρ T)
  where
  cong₂′ : ∀ {R R′ T T′} → R ≡ R′ → T ≡ T′ → R ⇒ᴿ T ≡ R′ ⇒ᴿ T′
  cong₂′ refl refl = refl
renᴿ-⇑ᵉ ρ (`∀ᴿ R) = cong `∀ᴿ (renᴿ-⇑ᵉ ρ R)

------------------------------------------------------------------------
-- A stored representation mentions no bound address at all: it is
-- well-formed over the EMPTY base, and `∀ᴿ` binds on the stack, so no
-- `bse` rule can ever have applied.
------------------------------------------------------------------------

wfᴿ-nobse : ∀ {Sg Ss R} ρ → Sg ∣ (Ss ∥ []) ⊢ᴿ R → renameᴿᵉ ρ R ≡ R
wfᴿ-nobse ρ (wfᴿ-var (a-lvl l)) = refl
wfᴿ-nobse ρ (wfᴿ-var a-here-bind) = refl
wfᴿ-nobse ρ (wfᴿ-var (a-skip-bind p)) = refl
wfᴿ-nobse ρ (wfᴿ-var (a-skip-asgn p)) = refl
wfᴿ-nobse ρ wfᴿ-ℕ = refl
wfᴿ-nobse ρ wfᴿ-𝔹 = refl
wfᴿ-nobse ρ (wfᴿ-⇒ a b) = cong₂′ (wfᴿ-nobse ρ a) (wfᴿ-nobse ρ b)
  where
  cong₂′ : ∀ {R R′ T T′} → R ≡ R′ → T ≡ T′ → R ⇒ᴿ T ≡ R′ ⇒ᴿ T′
  cong₂′ refl refl = refl
wfᴿ-nobse ρ (wfᴿ-∀ a) = cong `∀ᴿ (wfᴿ-nobse ρ a)

lvl-fixed : ∀ {Sg ℓ R} ρ → StoreOk Sg → Sg ∋ˡ ℓ := R → renameᴿᵉ ρ R ≡ R
lvl-fixed ρ sok l = wfᴿ-nobse ρ (sok l)

------------------------------------------------------------------------
-- Closure under the binders
------------------------------------------------------------------------

ren-bind : Renamesᵇ Sg ρ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → Renamesᵇ Sg ρ (bind ∷ Ss ∥ Bs) (bind ∷ Ss′ ∥ Bs′)
ren-a (ren-bind r) a-here-bind = a-here-bind
ren-a (ren-bind r) (a-skip-bind p) = a-skip-bind (ren-a r p)
ren-a (ren-bind r) (a-lvl l) = a-lvl l
ren-a (ren-bind r) a-here-addr = ∋a-restk (ren-a r a-here-addr)
ren-a (ren-bind r) a-here-nu = ∋a-restk (ren-a r a-here-nu)
ren-a (ren-bind r) (a-skip-addr p) =
  ∋a-restk (ren-a r (a-skip-addr (∋a-restk p)))
ren-a (ren-bind r) (a-skip-nu p) =
  ∋a-restk (ren-a r (a-skip-nu (∋a-restk p)))
ren-ok (ren-bind r) = ren-ok r
ren-n (ren-bind r) n-here-bind = n-here-bind
ren-n (ren-bind r) (n-skip-bind-b p) = n-skip-bind-b (ren-n r p)
ren-n (ren-bind r) (n-skip-bind-l p) = n-skip-bind-l (ren-n r p)
ren-n (ren-bind r) (n-skip-bind-e p) = n-skip-bind-e (ren-n r p)
ren-r (ren-bind {ρ = ρ} r) (r-skip-bind {R = R} p)
  rewrite renᴿ-⇑ ρ R = r-skip-bind (ren-r r p)
ren-r (ren-bind r) r-here = ∋r-restk (ren-r r r-here)
ren-r (ren-bind r) (r-skip-addr p) =
  ∋r-restk (ren-r r (r-skip-addr (∋r-restk p)))
ren-r (ren-bind r) (r-skip-nu p) =
  ∋r-restk (ren-r r (r-skip-nu (∋r-restk p)))
ren-r (ren-bind {ρ = ρ} r) (r-lvl l)
  rewrite lvl-fixed ρ (ren-ok r) l = r-lvl l
ren-inj (ren-bind r) = ren-inj r
ren-n⁻ (ren-bind r) n-here-bind = bnd zero , n-here-bind , refl
ren-n⁻ (ren-bind r) (n-skip-bind-b p) with ren-n⁻ r p
ren-n⁻ (ren-bind r) (n-skip-bind-b p) | bnd i , q , refl =
  bnd (suc i) , n-skip-bind-b q , refl
ren-n⁻ (ren-bind r) (n-skip-bind-l p) with ren-n⁻ r p
ren-n⁻ (ren-bind r) (n-skip-bind-l p) | lvl ℓ , q , refl =
  lvl ℓ , n-skip-bind-l q , refl
ren-n⁻ (ren-bind r) (n-skip-bind-e p) with ren-n⁻ r p
ren-n⁻ (ren-bind r) (n-skip-bind-e p) | bse j , q , refl =
  bse j , n-skip-bind-e q , refl


ren-asgn : ∀ {α} → Renamesᵇ Sg ρ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → Renamesᵇ Sg ρ (asgn α ∷ Ss ∥ Bs) (asgn (renᵃᵉ ρ α) ∷ Ss′ ∥ Bs′)
ren-a (ren-asgn r) (a-skip-asgn p) = a-skip-asgn (ren-a r p)
ren-a (ren-asgn r) (a-lvl l) = a-lvl l
ren-a (ren-asgn r) a-here-addr = ∋a-restk (ren-a r a-here-addr)
ren-a (ren-asgn r) a-here-nu = ∋a-restk (ren-a r a-here-nu)
ren-a (ren-asgn r) (a-skip-addr p) =
  ∋a-restk (ren-a r (a-skip-addr (∋a-restk p)))
ren-a (ren-asgn r) (a-skip-nu p) =
  ∋a-restk (ren-a r (a-skip-nu (∋a-restk p)))
ren-ok (ren-asgn r) = ren-ok r
ren-n (ren-asgn r) n-here-asgn = n-here-asgn
ren-n (ren-asgn r) (n-skip-asgn p) = n-skip-asgn (ren-n r p)
ren-r (ren-asgn r) (r-skip-asgn p) = r-skip-asgn (ren-r r p)
ren-r (ren-asgn r) r-here = ∋r-restk (ren-r r r-here)
ren-r (ren-asgn r) (r-skip-addr p) =
  ∋r-restk (ren-r r (r-skip-addr (∋r-restk p)))
ren-r (ren-asgn r) (r-skip-nu p) =
  ∋r-restk (ren-r r (r-skip-nu (∋r-restk p)))
ren-r (ren-asgn {ρ = ρ} r) (r-lvl l)
  rewrite lvl-fixed ρ (ren-ok r) l = r-lvl l
ren-inj (ren-asgn r) = ren-inj r
ren-n⁻ (ren-asgn {α = α} r) n-here-asgn = α , n-here-asgn , refl
ren-n⁻ (ren-asgn r) (n-skip-asgn p) with ren-n⁻ r p
ren-n⁻ (ren-asgn r) (n-skip-asgn p) | β , q , refl =
  β , n-skip-asgn q , refl


------------------------------------------------------------------------
-- The renaming the weakening itself performs
------------------------------------------------------------------------
-- `⤒ Ss` renames the stack's assignments by `suc`, which is precisely
-- `ren-asgn` applied all the way down, so the stack rides along.

ren-stk : ∀ {Sg ρ Bs Bs′ Ss}
  → Renamesᵇ Sg ρ ([] ∥ Bs) ([] ∥ Bs′)
  → Renamesᵇ Sg ρ (Ss ∥ Bs) (renStk ρ Ss ∥ Bs′)
ren-stk {Ss = []} r = r
ren-stk {Ss = bind ∷ Ss} r = ren-bind (ren-stk r)
ren-stk {Ss = asgn α ∷ Ss} r = ren-asgn (ren-stk r)

------------------------------------------------------------------------
-- The base: one new entry on top, and extension under a base binder
------------------------------------------------------------------------

renᵃᵉ-inj : ∀ {ρ α β} → (∀ {i j} → ρ i ≡ ρ j → i ≡ j)
  → renᵃᵉ ρ α ≡ renᵃᵉ ρ β → α ≡ β
renᵃᵉ-inj {α = lvl ℓ} {lvl m} inj refl = refl
renᵃᵉ-inj {α = bnd i} {bnd j} inj refl = refl
renᵃᵉ-inj {α = bse i} {bse j} inj eq = cong bse (inj (bse-inj eq))

suc-inj : ∀ {i j} → suc i ≡ suc j → i ≡ j
suc-inj refl = refl

-- Pushing ONE entry on the base, with the stack carried along.
ren-wk : ∀ {Sg Bs e} → StoreOk Sg → Renamesᵇ Sg suc ([] ∥ Bs) ([] ∥ e ∷ Bs)
ren-ok (ren-wk sok) = sok
ren-a (ren-wk {e = addr} sok) (a-lvl l) = a-lvl l
ren-a (ren-wk {e = addr} sok) a-here-addr = a-skip-addr a-here-addr
ren-a (ren-wk {e = addr} sok) a-here-nu = a-skip-addr a-here-nu
ren-a (ren-wk {e = addr} sok) (a-skip-addr p) = a-skip-addr (a-skip-addr p)
ren-a (ren-wk {e = addr} sok) (a-skip-nu p) = a-skip-addr (a-skip-nu p)
ren-a (ren-wk {e = nuBind R} sok) (a-lvl l) = a-lvl l
ren-a (ren-wk {e = nuBind R} sok) a-here-addr = a-skip-nu a-here-addr
ren-a (ren-wk {e = nuBind R} sok) a-here-nu = a-skip-nu a-here-nu
ren-a (ren-wk {e = nuBind R} sok) (a-skip-addr p) = a-skip-nu (a-skip-addr p)
ren-a (ren-wk {e = nuBind R} sok) (a-skip-nu p) = a-skip-nu (a-skip-nu p)
ren-n (ren-wk sok) ()
ren-n⁻ (ren-wk sok) ()
ren-r (ren-wk {e = addr} sok) (r-lvl l) rewrite lvl-fixed suc sok l = r-lvl l
ren-r (ren-wk {e = addr} sok) r-here = r-skip-addr r-here
ren-r (ren-wk {e = addr} sok) (r-skip-addr p) = r-skip-addr (r-skip-addr p)
ren-r (ren-wk {e = addr} sok) (r-skip-nu p) = r-skip-addr (r-skip-nu p)
ren-r (ren-wk {e = nuBind T} sok) (r-lvl l)
  rewrite lvl-fixed suc sok l = r-lvl l
ren-r (ren-wk {e = nuBind T} sok) r-here = r-skip-nu r-here
ren-r (ren-wk {e = nuBind T} sok) (r-skip-addr p) = r-skip-nu (r-skip-addr p)
ren-r (ren-wk {e = nuBind T} sok) (r-skip-nu p) = r-skip-nu (r-skip-nu p)
ren-inj (ren-wk sok) = renᵃᵉ-inj suc-inj

------------------------------------------------------------------------
-- The judgments travel
------------------------------------------------------------------------
-- A base renaming leaves NAMES alone, so a source type is unchanged;
-- only the representation types move.

wfᵗ-ren : ∀ {Sg ρ Γ Γ′ A} → Renamesᵇ Sg ρ Γ Γ′ → Γ ⊢ᵗ A → Γ′ ⊢ᵗ A
wfᵗ-ren r (wf-var n) = wf-var (ren-n r n)
wfᵗ-ren r wf-ℕ = wf-ℕ
wfᵗ-ren r wf-𝔹 = wf-𝔹
wfᵗ-ren r (wf-⇒ a b) = wf-⇒ (wfᵗ-ren r a) (wfᵗ-ren r b)
wfᵗ-ren r (wf-∀ a) = wf-∀ (wfᵗ-ren (ren-bind r) a)

wfᴿ-ren : ∀ {Sg ρ Γ Γ′ R} → Renamesᵇ Sg ρ Γ Γ′
  → Sg ∣ Γ ⊢ᴿ R → Sg ∣ Γ′ ⊢ᴿ renameᴿᵉ ρ R
wfᴿ-ren r (wfᴿ-var a) = wfᴿ-var (ren-a r a)
wfᴿ-ren r wfᴿ-ℕ = wfᴿ-ℕ
wfᴿ-ren r wfᴿ-𝔹 = wfᴿ-𝔹
wfᴿ-ren r (wfᴿ-⇒ a b) = wfᴿ-⇒ (wfᴿ-ren r a) (wfᴿ-ren r b)
wfᴿ-ren r (wfᴿ-∀ a) = wfᴿ-∀ (wfᴿ-ren (ren-bind r) a)

read-ren : ∀ {Sg ρ Γ Γ′ R A} → Renamesᵇ Sg ρ Γ Γ′
  → Sg ∣ Γ ⊢ R ⇓ A → Sg ∣ Γ′ ⊢ renameᴿᵉ ρ R ⇓ A
read-ren r (read-var n) = read-var (ren-n r n)
read-ren r read-ℕ = read-ℕ
read-ren r read-𝔹 = read-𝔹
read-ren r (read-⇒ a b) = read-⇒ (read-ren r a) (read-ren r b)
read-ren r (read-∀ a) = read-∀ (read-ren (ren-bind r) a)

-- The pop judgment is pure stack structure, so the renaming passes
-- straight through it — THE point of the split.
pop-ren : ∀ {ρ Ss Ss′ Bs Bs′ X α} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → (renStk ρ Ss ∥ Bs′) ▷ X := renᵃᵉ ρ α ⇒ (renStk ρ Ss′ ∥ Bs′)
pop-ren pop-here = pop-here
pop-ren (pop-bind-b p) = pop-bind-b (pop-ren p)
pop-ren (pop-bind-l p) = pop-bind-l (pop-ren p)
pop-ren (pop-bind-e p) = pop-bind-e (pop-ren p)

notasgn-ren : ∀ {Sg ρ Γ Γ′ α} → Renamesᵇ Sg ρ Γ Γ′
  → NotAssigned Γ α → NotAssigned Γ′ (renᵃᵉ ρ α)
notasgn-ren r na p with ren-n⁻ r p
notasgn-ren r na p | β , q , eq with ren-inj r eq
notasgn-ren r na p | β , q , eq | refl = na q

------------------------------------------------------------------------
-- A conversion travels
------------------------------------------------------------------------
-- The interior and the exterior differ only in the STACK, so one base
-- renaming serves both ends; the crossings keep their names, and their
-- addresses move by `renEltᵉ`.

-- A conversion never touches the base: every crossing is a stack
-- operation, and `all` pushes a `bind` on the stack alone.
mutual
  convElt-base : ∀ {Sg Γᵢ Γₑ ĉ A B} → Sg ∣ Γᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Γₑ
    → bas Γᵢ ≡ bas Γₑ
  convElt-base (conv-seal rep rd pop) = sym (pop-base pop)
  convElt-base (conv-unseal rep rd pop na) = pop-base pop
  convElt-base (conv-hide wf pop na) = sym (pop-base pop)
  convElt-base (conv-show wf pop na) = pop-base pop
  convElt-base (conv-fun s t) = sym (conv-base s)
  convElt-base (conv-all s) = conv-base s

  conv-base : ∀ {Sg Γᵢ Γₑ c A B} → Sg ∣ Γᵢ ⊢ c ∶ A ⇝ B ⊣ Γₑ
    → bas Γᵢ ≡ bas Γₑ
  conv-base (conv-id wf) = refl
  conv-base (conv-cons hd tl) = trans (convElt-base hd) (conv-base tl)

mutual
  convElt-ren : ∀ {Sg ρ Bs Bs′ Ssᵢ Ssₑ ĉ A B}
    → Renamesᵇ Sg ρ ([] ∥ Bs) ([] ∥ Bs′)
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Sg ∣ (renStk ρ Ssᵢ ∥ Bs′) ⊢̂ renEltᵉ ρ ĉ ∶ A ⇝ B ⊣ (renStk ρ Ssₑ ∥ Bs′)
  convElt-ren r (conv-seal rep rd pop) =
    conv-seal (ren-r (ren-stk r) rep) (read-ren (ren-stk r) rd) (pop-ren pop)
  convElt-ren r (conv-unseal rep rd pop na) =
    conv-unseal (ren-r (ren-stk r) rep) (read-ren (ren-stk r) rd)
                (pop-ren pop) (notasgn-ren (ren-stk r) na)
  convElt-ren r (conv-hide wf pop na) =
    conv-hide (wfᵗ-ren (ren-stk r) wf) (pop-ren pop)
              (notasgn-ren (ren-stk r) na)
  convElt-ren r (conv-show wf pop na) =
    conv-show (wfᵗ-ren (ren-stk r) wf) (pop-ren pop)
              (notasgn-ren (ren-stk r) na)
  convElt-ren r (conv-fun s t) = conv-fun (conv-ren r s) (conv-ren r t)
  convElt-ren r (conv-all s) = conv-all (conv-ren r s)

  conv-ren : ∀ {Sg ρ Bs Bs′ Ssᵢ Ssₑ c A B}
    → Renamesᵇ Sg ρ ([] ∥ Bs) ([] ∥ Bs′)
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Sg ∣ (renStk ρ Ssᵢ ∥ Bs′) ⊢ renConvᵉ ρ c ∶ A ⇝ B ⊣ (renStk ρ Ssₑ ∥ Bs′)
  conv-ren r (conv-id wf) = conv-id (wfᵗ-ren (ren-stk r) wf)
  conv-ren r (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) with convElt-base hd
  conv-ren r (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl =
    conv-cons (convElt-ren r hd) (conv-ren r tl)


------------------------------------------------------------------------
-- Normal forms survive a base renaming
------------------------------------------------------------------------
-- A base renaming is injective on addresses and leaves names alone, so
-- a pair that did not cancel still does not: the four cancelling rows
-- compare a name and an address, and every other row is decided by the
-- element shapes, which renaming preserves.

Injᵉ : Renameᵇ → Set
Injᵉ ρ = ∀ {α β} → renᵃᵉ ρ α ≡ renᵃᵉ ρ β → α ≡ β

fuse-renᵉ : ∀ {ρ} → Injᵉ ρ → ∀ ĉ ḓ → fuse ĉ ḓ ≡ nothing
  → fuse (renEltᵉ ρ ĉ) (renEltᵉ ρ ḓ) ≡ nothing
fuse-renᵉ inj (seal X α) (seal Y β) eq = refl
fuse-renᵉ {ρ = ρ} inj (seal X α) (unseal Y β) eq
  with X ≟ Y | α ≟ᵃ β | renᵃᵉ ρ α ≟ᵃ renᵃᵉ ρ β
fuse-renᵉ {ρ = ρ} inj (seal X α) (unseal Y β) () | yes _ | yes _ | _
fuse-renᵉ {ρ = ρ} inj (seal X α) (unseal Y β) eq | yes _ | no ne | yes e =
  ⊥-elim (ne (inj e))
fuse-renᵉ {ρ = ρ} inj (seal X α) (unseal Y β) eq | yes _ | no _ | no _ = refl
fuse-renᵉ {ρ = ρ} inj (seal X α) (unseal Y β) eq | no _ | _ | _ = refl
fuse-renᵉ inj (seal X α) (hide Y β) eq = refl
fuse-renᵉ inj (seal X α) (show Y β) eq = refl
fuse-renᵉ inj (seal X α) (s₂ ↦ t₂) eq = refl
fuse-renᵉ inj (seal X α) (all s₂) eq = refl
fuse-renᵉ {ρ = ρ} inj (unseal X α) (seal Y β) eq
  with X ≟ Y | α ≟ᵃ β | renᵃᵉ ρ α ≟ᵃ renᵃᵉ ρ β
fuse-renᵉ {ρ = ρ} inj (unseal X α) (seal Y β) () | yes _ | yes _ | _
fuse-renᵉ {ρ = ρ} inj (unseal X α) (seal Y β) eq | yes _ | no ne | yes e =
  ⊥-elim (ne (inj e))
fuse-renᵉ {ρ = ρ} inj (unseal X α) (seal Y β) eq | yes _ | no _ | no _ = refl
fuse-renᵉ {ρ = ρ} inj (unseal X α) (seal Y β) eq | no _ | _ | _ = refl
fuse-renᵉ inj (unseal X α) (unseal Y β) eq = refl
fuse-renᵉ inj (unseal X α) (hide Y β) eq = refl
fuse-renᵉ inj (unseal X α) (show Y β) eq = refl
fuse-renᵉ inj (unseal X α) (s₂ ↦ t₂) eq = refl
fuse-renᵉ inj (unseal X α) (all s₂) eq = refl
fuse-renᵉ inj (hide X α) (seal Y β) eq = refl
fuse-renᵉ inj (hide X α) (unseal Y β) eq = refl
fuse-renᵉ inj (hide X α) (hide Y β) eq = refl
fuse-renᵉ {ρ = ρ} inj (hide X α) (show Y β) eq
  with X ≟ Y | α ≟ᵃ β | renᵃᵉ ρ α ≟ᵃ renᵃᵉ ρ β
fuse-renᵉ {ρ = ρ} inj (hide X α) (show Y β) () | yes _ | yes _ | _
fuse-renᵉ {ρ = ρ} inj (hide X α) (show Y β) eq | yes _ | no ne | yes e =
  ⊥-elim (ne (inj e))
fuse-renᵉ {ρ = ρ} inj (hide X α) (show Y β) eq | yes _ | no _ | no _ = refl
fuse-renᵉ {ρ = ρ} inj (hide X α) (show Y β) eq | no _ | _ | _ = refl
fuse-renᵉ inj (hide X α) (s₂ ↦ t₂) eq = refl
fuse-renᵉ inj (hide X α) (all s₂) eq = refl
fuse-renᵉ inj (show X α) (seal Y β) eq = refl
fuse-renᵉ inj (show X α) (unseal Y β) eq = refl
fuse-renᵉ {ρ = ρ} inj (show X α) (hide Y β) eq
  with X ≟ Y | α ≟ᵃ β | renᵃᵉ ρ α ≟ᵃ renᵃᵉ ρ β
fuse-renᵉ {ρ = ρ} inj (show X α) (hide Y β) () | yes _ | yes _ | _
fuse-renᵉ {ρ = ρ} inj (show X α) (hide Y β) eq | yes _ | no ne | yes e =
  ⊥-elim (ne (inj e))
fuse-renᵉ {ρ = ρ} inj (show X α) (hide Y β) eq | yes _ | no _ | no _ = refl
fuse-renᵉ {ρ = ρ} inj (show X α) (hide Y β) eq | no _ | _ | _ = refl
fuse-renᵉ inj (show X α) (show Y β) eq = refl
fuse-renᵉ inj (show X α) (s₂ ↦ t₂) eq = refl
fuse-renᵉ inj (show X α) (all s₂) eq = refl
fuse-renᵉ inj (s₁ ↦ t₁) (seal Y β) eq = refl
fuse-renᵉ inj (s₁ ↦ t₁) (unseal Y β) eq = refl
fuse-renᵉ inj (s₁ ↦ t₁) (hide Y β) eq = refl
fuse-renᵉ inj (s₁ ↦ t₁) (show Y β) eq = refl
fuse-renᵉ inj (s₁ ↦ t₁) (s₂ ↦ t₂) ()
fuse-renᵉ inj (s₁ ↦ t₁) (all s₂) eq = refl
fuse-renᵉ inj (all s₁) (seal Y β) eq = refl
fuse-renᵉ inj (all s₁) (unseal Y β) eq = refl
fuse-renᵉ inj (all s₁) (hide Y β) eq = refl
fuse-renᵉ inj (all s₁) (show Y β) eq = refl
fuse-renᵉ inj (all s₁) (s₂ ↦ t₂) eq = refl
fuse-renᵉ inj (all s₁) (all s₂) ()

mutual
  nfElt-ren : ∀ {ρ ĉ} → Injᵉ ρ → NFElt ĉ → NFElt (renEltᵉ ρ ĉ)
  nfElt-ren inj nf-seal = nf-seal
  nfElt-ren inj nf-unseal = nf-unseal
  nfElt-ren inj nf-hide = nf-hide
  nfElt-ren inj nf-show = nf-show
  nfElt-ren inj (nf-fun s t) = nf-fun (nf-ren inj s) (nf-ren inj t)
  nfElt-ren inj (nf-all s) = nf-all (nf-ren inj s)

  irr-ren : ∀ {ρ ĉ c} → Injᵉ ρ → IrreducibleAfter ĉ c
    → IrreducibleAfter (renEltᵉ ρ ĉ) (renConvᵉ ρ c)
  irr-ren inj irr-id = irr-id
  irr-ren {ĉ = ĉ} inj (irr-cons {ḓ = ḓ} e) =
    irr-cons (fuse-renᵉ inj ĉ ḓ e)

  nf-ren : ∀ {ρ c} → Injᵉ ρ → NF c → NF (renConvᵉ ρ c)
  nf-ren inj nf-id = nf-id
  nf-ren inj (nf-cons hd tl irr) =
    nf-cons (nfElt-ren inj hd) (nf-ren inj tl) (irr-ren inj irr)

------------------------------------------------------------------------
-- Extending under a base binder
------------------------------------------------------------------------

renᵃᵉ-ext : ∀ ρ α → renᵃᵉ (extᵇ ρ) (renᵃᵉ suc α) ≡ renᵃᵉ suc (renᵃᵉ ρ α)
renᵃᵉ-ext ρ (lvl ℓ) = refl
renᵃᵉ-ext ρ (bnd i) = refl
renᵃᵉ-ext ρ (bse j) = refl

-- `⤒` commutes with a base renaming, the usual ext/shift square.
renStk-ext : ∀ ρ Ss → renStk (extᵇ ρ) (⤒ Ss) ≡ ⤒ (renStk ρ Ss)
renStk-ext ρ [] = refl
renStk-ext ρ (bind ∷ Ss) = cong (bind ∷_) (renStk-ext ρ Ss)
renStk-ext ρ (asgn α ∷ Ss)
  rewrite renᵃᵉ-ext ρ α | renStk-ext ρ Ss = refl

extᵇ-inj : ∀ {ρ} → (∀ {i j} → ρ i ≡ ρ j → i ≡ j)
  → ∀ {i j} → extᵇ ρ i ≡ extᵇ ρ j → i ≡ j
extᵇ-inj inj {zero} {zero} eq = refl
extᵇ-inj inj {suc i} {suc j} eq = cong suc (inj (suc-inj eq))

-- One new entry on each side — the SAME entry, its representation
-- renamed — related by the extended renaming.
renEnt : Renameᵇ → BaseEnt → BaseEnt
renEnt ρ addr = addr
renEnt ρ (nuBind R) = nuBind (renameᴿᵉ ρ R)

ren-ext : ∀ {Sg ρ Bs Bs′ e}
  → (∀ {i j} → ρ i ≡ ρ j → i ≡ j)
  → Renamesᵇ Sg ρ ([] ∥ Bs) ([] ∥ Bs′)
  → Renamesᵇ Sg (extᵇ ρ) ([] ∥ e ∷ Bs) ([] ∥ renEnt ρ e ∷ Bs′)
ren-ok (ren-ext inj r) = ren-ok r
ren-n (ren-ext inj r) ()
ren-n⁻ (ren-ext inj r) ()
ren-inj (ren-ext inj r) = renᵃᵉ-inj (extᵇ-inj inj)
ren-a (ren-ext inj r) (a-lvl l) = a-lvl l
ren-a (ren-ext {e = addr} inj r) a-here-addr = a-here-addr
ren-a (ren-ext {e = nuBind T} inj r) a-here-nu = a-here-nu
ren-a (ren-ext {e = addr} inj r) (a-skip-addr p) = a-skip-addr (ren-a r p)
ren-a (ren-ext {e = nuBind T} inj r) (a-skip-nu p) = a-skip-nu (ren-a r p)
ren-r (ren-ext {ρ = ρ} inj r) (r-lvl l)
  rewrite lvl-fixed (extᵇ ρ) (ren-ok r) l = r-lvl l
ren-r (ren-ext {ρ = ρ} {e = nuBind T} inj r) r-here
  rewrite renᴿ-⇑ᵉ ρ T = r-here
ren-r (ren-ext {ρ = ρ} {e = addr} inj r) (r-skip-addr {R = R} p)
  rewrite renᴿ-⇑ᵉ ρ R = r-skip-addr (ren-r r p)
ren-r (ren-ext {ρ = ρ} {e = nuBind T} inj r) (r-skip-nu {R = R} p)
  rewrite renᴿ-⇑ᵉ ρ R = r-skip-nu (ren-r r p)

------------------------------------------------------------------------
-- A term travels
------------------------------------------------------------------------
-- `Λ` and `ν` are the base's binders, so they are where the renaming
-- extends; `⟨ c ⟩` is where the split pays off, since the boundary's
-- interior differs only in the stack.

⊢-ren : ∀ {Sg ρ Bs Bs′ Ss Γ M A}
  → (∀ {i j} → ρ i ≡ ρ j → i ≡ j)
  → Renamesᵇ Sg ρ ([] ∥ Bs) ([] ∥ Bs′)
  → Sg ∣ (Ss ∥ Bs) ∣ Γ ⊢ M ⦂ A
  → Sg ∣ (renStk ρ Ss ∥ Bs′) ∣ Γ ⊢ renBseᴹ ρ M ⦂ A
⊢-ren inj r (⊢` x) = ⊢` x
⊢-ren inj r ⊢$ = ⊢$
⊢-ren inj r ⊢# = ⊢#
⊢-ren inj r (⊢⊕ m n) = ⊢⊕ (⊢-ren inj r m) (⊢-ren inj r n)
⊢-ren inj r (⊢ƛ wf n) = ⊢ƛ (wfᵗ-ren (ren-stk r) wf) (⊢-ren inj r n)
⊢-ren inj r (⊢· l m) = ⊢· (⊢-ren inj r l) (⊢-ren inj r m)
⊢-ren inj r (⊢•[] l wf) = ⊢•[] (⊢-ren inj r l) (wfᵗ-ren (ren-stk r) wf)
⊢-ren inj r (⊢⟨⟩ {Δᵢ = Ssᵢ ∥ Bsᵢ} nf ⊢M ⊢c) with conv-base ⊢c
⊢-ren inj r (⊢⟨⟩ {Δᵢ = Ssᵢ ∥ Bsᵢ} nf ⊢M ⊢c) | refl =
  ⊢⟨⟩ (nf-ren (ren-inj r) nf) (⊢-ren inj r ⊢M) (conv-ren r ⊢c)
-- `Λ` and `ν` bind on the BASE: the renaming extends, the stack rides
-- along by `renStk-ext`, and the boundary inside the body is untouched.
⊢-ren {ρ = ρ} {Ss = Ss} inj r (⊢Λ v ⊢V)
  with ⊢-ren (extᵇ-inj inj) (ren-ext {e = addr} inj r) ⊢V
     | renStk-ext ρ Ss
⊢-ren {ρ = ρ} {Ss = Ss} inj r (⊢Λ v ⊢V) | ⊢V′ | eq
  rewrite eq = ⊢Λ (renᵉ-value v) ⊢V′
  where postulate renᵉ-value : ∀ {ρ V} → Value V → Value (renBseᴹ ρ V)
⊢-ren {ρ = ρ} {Ss = Ss} inj r (⊢ν {R = R} wf ⊢M)
  with ⊢-ren (extᵇ-inj inj) (ren-ext {e = nuBind R} inj r) ⊢M
     | renStk-ext ρ Ss
⊢-ren {ρ = ρ} {Ss = Ss} inj r (⊢ν {R = R} wf ⊢M) | ⊢M′ | eq
  rewrite eq = ⊢ν (wfᴿ-ren (ren-stk r) wf) ⊢M′
