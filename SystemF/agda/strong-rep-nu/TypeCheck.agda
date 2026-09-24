module strong-rep-nu.TypeCheck where

-- File Charter:
--   * AN EXECUTABLE, DERIVATION-PRODUCING TYPE CHECKER FOR THE WHOLE
--     DEVELOPMENT.  §1 `_≟Ty_`; §2–§3 the change atoms and the two
--     change-list readings; §4 payloads and context well-formedness;
--     §5 `interior?`/`conversion?`/`boundaryWf?`; §6 the readings
--     between the universes (`read?`, `sameTy?`, `rebase?`,
--     `weaken?`, `weakenᵀ?`); §7 `∋:=?`, `wfTy?`, `convTy?`; §8 `infer`;
--     §9 `check⊢`/`checkConv`/`check~`; §10 the forcing family.
--   * NOTHING HERE IS ASSUMED AND NOTHING IS TRUSTED: every checker
--     returns a `Maybe` of the ORDINARY derivation, so there is no
--     soundness theorem to owe.  It depends on no metatheory.
--   * USING IT.  `tc` IS a typing derivation, read off the goal; where
--     the answer is an OUTPUT the goal does not fix, use the `!`
--     family (notably `sq!` for a looked-up representation).  A FAILURE IS A
--     REJECTION: Agda reports an unsolved meta, which `make check`
--     turns into an error; `proj₂ (ty! Δ Γ M)` says what it inferred.
-- Commentary: Commentary.md § TypeCheck.agda

open import Data.Nat using (ℕ; zero; suc; _∸_; _<_)
open import Data.Nat.Properties using (_≟_; _<?_; ≮⇒≥; m+[n∸m]≡n)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; From-just; from-just)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; _[_]ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Boundary
open import strong-rep-nu.Terms
open import strong-rep-nu.Lookup public

------------------------------------------------------------------------
-- 1. Decidable equality on types
------------------------------------------------------------------------

infix 4 _≟Ty_
_≟Ty_ : (A B : Ty) → Maybe (A ≡ B)
(` X) ≟Ty (` Y) with X ≟ Y
(` X) ≟Ty (` Y) | yes refl = just refl
(` X) ≟Ty (` Y) | no _     = nothing
(` X) ≟Ty `ℕ      = nothing
(` X) ≟Ty `𝔹      = nothing
(` X) ≟Ty (B ⇒ C) = nothing
(` X) ≟Ty (`∀ B)  = nothing
`ℕ ≟Ty (` Y)   = nothing
`ℕ ≟Ty `ℕ      = just refl
`ℕ ≟Ty `𝔹      = nothing
`ℕ ≟Ty (B ⇒ C) = nothing
`ℕ ≟Ty (`∀ B)  = nothing
`𝔹 ≟Ty (` Y)   = nothing
`𝔹 ≟Ty `ℕ      = nothing
`𝔹 ≟Ty `𝔹      = just refl
`𝔹 ≟Ty (B ⇒ C) = nothing
`𝔹 ≟Ty (`∀ B)  = nothing
(A ⇒ B) ≟Ty (` Y)   = nothing
(A ⇒ B) ≟Ty `ℕ      = nothing
(A ⇒ B) ≟Ty `𝔹      = nothing
(A ⇒ B) ≟Ty (C ⇒ D) with A ≟Ty C
(A ⇒ B) ≟Ty (C ⇒ D) | nothing = nothing
(A ⇒ B) ≟Ty (C ⇒ D) | just refl with B ≟Ty D
(A ⇒ B) ≟Ty (C ⇒ D) | just refl | just refl = just refl
(A ⇒ B) ≟Ty (C ⇒ D) | just refl | nothing   = nothing
(A ⇒ B) ≟Ty (`∀ C)  = nothing
(`∀ A) ≟Ty (` Y)   = nothing
(`∀ A) ≟Ty `ℕ      = nothing
(`∀ A) ≟Ty `𝔹      = nothing
(`∀ A) ≟Ty (B ⇒ C) = nothing
(`∀ A) ≟Ty (`∀ B)  with A ≟Ty B
(`∀ A) ≟Ty (`∀ B)  | just refl = just refl
(`∀ A) ≟Ty (`∀ B)  | nothing   = nothing

------------------------------------------------------------------------
-- 2. The atoms a change carries
------------------------------------------------------------------------

fresh? : (α : RVar) (Δ : TyCtx) → Maybe (Δ ∌ʳ α)
fresh? α []      = just fresh[]
fresh? α (β ∷ Δ) with α ≟ β
fresh? α (β ∷ Δ) | yes _  = nothing
fresh? α (β ∷ Δ) | no  ne with fresh? α Δ
fresh? α (β ∷ Δ) | no  ne | just f  = just (fresh∷ ne f)
fresh? α (β ∷ Δ) | no  ne | nothing = nothing

unique? : (Δ : TyCtx) → Maybe (Unique Δ)
unique? []      = just unique[]
unique? (α ∷ Δ) with fresh? α Δ
unique? (α ∷ Δ) | nothing = nothing
unique? (α ∷ Δ) | just f  with unique? Δ
unique? (α ∷ Δ) | just f  | just u  = just (unique∷ f u)
unique? (α ∷ Δ) | just f  | nothing = nothing

del? : (α : RVar) (Δ : TyCtx) (X : ℕ)
  → Maybe (∃[ Δ′ ] α ⊢- Δ at X ⇒ Δ′)
del? α []      X       = nothing
del? α (β ∷ Δ) zero    with α ≟ β
del? α (β ∷ Δ) zero    | yes refl = just (Δ , del-here)
del? α (β ∷ Δ) zero    | no  _    = nothing
del? α (β ∷ Δ) (suc X) with del? α Δ X
del? α (β ∷ Δ) (suc X) | just (Δ′ , d) = just (β ∷ Δ′ , del-there d)
del? α (β ∷ Δ) (suc X) | nothing       = nothing

ins? : (α : RVar) (Δ : TyCtx) (X : ℕ)
  → Maybe (∃[ Δ′ ] α ⊢+ Δ at X ⇒ Δ′)
ins? α Δ       zero    = just (α ∷ Δ , ins-here)
ins? α []      (suc X) = nothing
ins? α (β ∷ Δ) (suc X) with ins? α Δ X
ins? α (β ∷ Δ) (suc X) | just (Δ′ , i) = just (β ∷ Δ′ , ins-there i)
ins? α (β ∷ Δ) (suc X) | nothing       = nothing

validRVar? : (Ξ : RepCtx) (α : RVar) → Maybe (Ξ ∋ʳ α)
validRVar? Ξ α with lookupˡ? Ξ α
validRVar? Ξ α | just v  = just v
validRVar? Ξ α | nothing = nothing

validNames? : (Ξ : RepCtx) (Δ : TyCtx) → Maybe (ValidNames Ξ Δ)
validNames? Ξ []      = just (λ ())
validNames? Ξ (α ∷ Δ) with lookupˡ? Ξ α
validNames? Ξ (α ∷ Δ) | nothing      = nothing
validNames? Ξ (α ∷ Δ) | just (b , d) with validNames? Ξ Δ
validNames? Ξ (α ∷ Δ) | just (b , d) | nothing = nothing
validNames? Ξ (α ∷ Δ) | just (b , d) | just h =
  just (λ { here → b , d ; (there e) → h e })

------------------------------------------------------------------------
-- 3. Running a change list, in both readings
------------------------------------------------------------------------

runδ : (Ξ : RepCtx) (Δ : TyCtx) (δ : Change)
  → Maybe (∃[ Δ′ ] Ξ ∣ Δ ⊢δ δ ⇒ Δ′)
runδ Ξ Δ (unbind X α) with validRVar? Ξ α
runδ Ξ Δ (unbind X α) | nothing = nothing
runδ Ξ Δ (unbind X α) | just v  with del? α Δ X
runδ Ξ Δ (unbind X α) | just v  | nothing = nothing
runδ Ξ Δ (unbind X α) | just v  | just (Δ′ , d) with fresh? α Δ′
runδ Ξ Δ (unbind X α) | just v  | just (Δ′ , d) | nothing = nothing
runδ Ξ Δ (unbind X α) | just v  | just (Δ′ , d) | just f =
  just (Δ′ , step-unbind v d f)
runδ Ξ Δ (bind X α) with validRVar? Ξ α
runδ Ξ Δ (bind X α) | nothing = nothing
runδ Ξ Δ (bind X α) | just v  with fresh? α Δ
runδ Ξ Δ (bind X α) | just v  | nothing = nothing
runδ Ξ Δ (bind X α) | just v  | just f with ins? α Δ X
runδ Ξ Δ (bind X α) | just v  | just f | nothing = nothing
runδ Ξ Δ (bind X α) | just v  | just f | just (Δ′ , i) =
  just (Δ′ , step-bind v f i)

-- The tail acts first (head-LAST order, strong-rep-nu.Boundary §2).
runχ : (Ξ : RepCtx) (Δ : TyCtx) (χ : List Change)
  → Maybe (∃[ Δ′ ] Ξ ∣ Δ ⊢χ χ ⇒ Δ′)
runχ Ξ Δ []      = just (Δ , changes[])
runχ Ξ Δ (δ ∷ χ) with runχ Ξ Δ χ
runχ Ξ Δ (δ ∷ χ) | nothing = nothing
runχ Ξ Δ (δ ∷ χ) | just (Δ₂ , cs) with runδ Ξ Δ₂ δ
runχ Ξ Δ (δ ∷ χ) | just (Δ₂ , cs) | nothing = nothing
runχ Ξ Δ (δ ∷ χ) | just (Δ₂ , cs) | just (Δ₃ , st) =
  just (Δ₃ , changes∷ cs st)

-- The conversion reading: an `unbind` is skipped, and a `bind` of a name
-- the skipped unbinds left live is a no-op (strong-rep-nu.Boundary §3).
runχᶜ : (Ξ : RepCtx) (Δ : TyCtx) (χ : List Change)
  → Maybe (∃[ Δ′ ] Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′)
runχᶜ Ξ Δ [] = just (Δ , conv[])
runχᶜ Ξ Δ (unbind X α ∷ χ) with validRVar? Ξ α
runχᶜ Ξ Δ (unbind X α ∷ χ) | nothing = nothing
runχᶜ Ξ Δ (unbind X α ∷ χ) | just v with runχᶜ Ξ Δ χ
runχᶜ Ξ Δ (unbind X α ∷ χ) | just v | nothing = nothing
runχᶜ Ξ Δ (unbind X α ∷ χ) | just v | just (Δ₂ , cs) =
  just (Δ₂ , conv-unbind v cs)
runχᶜ Ξ Δ (bind X α ∷ χ) with validRVar? Ξ α
runχᶜ Ξ Δ (bind X α ∷ χ) | nothing = nothing
runχᶜ Ξ Δ (bind X α ∷ χ) | just v with runχᶜ Ξ Δ χ
runχᶜ Ξ Δ (bind X α ∷ χ) | just v | nothing = nothing
runχᶜ Ξ Δ (bind X α ∷ χ) | just v | just (Δ₂ , cs) with fresh? α Δ₂
runχᶜ Ξ Δ (bind X α ∷ χ) | just v | just (Δ₂ , cs) | just f
  with ins? α Δ₂ X
runχᶜ Ξ Δ (bind X α ∷ χ) | just v | just (Δ₂ , cs) | just f
  | just (Δ₃ , i) = just (Δ₃ , conv-bind v cs f i)
runχᶜ Ξ Δ (bind X α ∷ χ) | just v | just (Δ₂ , cs) | just f
  | nothing = nothing
runχᶜ Ξ Δ (bind X α ∷ χ) | just v | just (Δ₂ , cs) | nothing
  with find? Δ₂ α
runχᶜ Ξ Δ (bind X α ∷ χ) | just v | just (Δ₂ , cs) | nothing
  | just (Y , d) = just (Δ₂ , conv-bind-live v cs d)
runχᶜ Ξ Δ (bind X α ∷ χ) | just v | just (Δ₂ , cs) | nothing
  | nothing = nothing

------------------------------------------------------------------------
-- 4. Representation payloads and context well-formedness
------------------------------------------------------------------------

-- An index below the local binder depth is payload-local; otherwise it
-- is `n + α`, and the subtraction has to be PROVED to put the index
-- back in constructor form.
ref? : (Ξ : RepCtx) (n i : ℕ) → Maybe (Ξ ⊢ref[ n ] i)
ref? Ξ n i with i <? n
ref? Ξ n i | yes i<n = just (local-ref i<n)
ref? Ξ n i | no  i≮n with lookupˡ? Ξ (i ∸ n)
ref? Ξ n i | no  i≮n | nothing = nothing
ref? Ξ n i | no  i≮n | just (b , d) =
  just (subst (Ξ ⊢ref[ n ]_) (m+[n∸m]≡n (≮⇒≥ i≮n)) (free-ref d))

wfᴿ? : (Ξ : RepCtx) (n : ℕ) (R : Ty) → Maybe (Ξ ⊢ᴿ[ n ] R)
wfᴿ? Ξ n (` i) with ref? Ξ n i
wfᴿ? Ξ n (` i) | just r  = just (wfᴿ-var r)
wfᴿ? Ξ n (` i) | nothing = nothing
wfᴿ? Ξ n `ℕ = just wfᴿ-ℕ
wfᴿ? Ξ n `𝔹 = just wfᴿ-𝔹
wfᴿ? Ξ n (R ⇒ S) with wfᴿ? Ξ n R
wfᴿ? Ξ n (R ⇒ S) | nothing = nothing
wfᴿ? Ξ n (R ⇒ S) | just wR with wfᴿ? Ξ n S
wfᴿ? Ξ n (R ⇒ S) | just wR | just wS = just (wfᴿ-⇒ wR wS)
wfᴿ? Ξ n (R ⇒ S) | just wR | nothing = nothing
wfᴿ? Ξ n (`∀ R) with wfᴿ? Ξ (suc n) R
wfᴿ? Ξ n (`∀ R) | just wR = just (wfᴿ-∀ wR)
wfᴿ? Ξ n (`∀ R) | nothing = nothing

wfRepCtx? : (Ξ : RepCtx) → Maybe (WfRepCtx Ξ)
wfRepCtx? [] = just wf-reps[]
wfRepCtx? (abstR ∷ Ξ) with wfRepCtx? Ξ
wfRepCtx? (abstR ∷ Ξ) | just w  = just (wf-abstR w)
wfRepCtx? (abstR ∷ Ξ) | nothing = nothing
wfRepCtx? (bindR R ∷ Ξ) with wfᴿ? Ξ zero R
wfRepCtx? (bindR R ∷ Ξ) | nothing = nothing
wfRepCtx? (bindR R ∷ Ξ) | just wR with wfRepCtx? Ξ
wfRepCtx? (bindR R ∷ Ξ) | just wR | just w  = just (wf-bindR wR w)
wfRepCtx? (bindR R ∷ Ξ) | just wR | nothing = nothing

wfCtx? : (Γ : Ctxᵗ) → Maybe (WfCtx Γ)
wfCtx? Γ with wfRepCtx? (reps Γ)
wfCtx? Γ | nothing = nothing
wfCtx? Γ | just wr with validNames? (reps Γ) (names Γ)
wfCtx? Γ | just wr | nothing = nothing
wfCtx? Γ | just wr | just vn with unique? (names Γ)
wfCtx? Γ | just wr | just vn | nothing = nothing
wfCtx? Γ | just wr | just vn | just u  = just (wf-ctx wr vn u)

------------------------------------------------------------------------
-- 5. The two induced contexts, and a complete boundary scope witness
------------------------------------------------------------------------

interior? : (Γ : Ctxᵗ) (Θ : Boundary) → Maybe (∃[ Γᵢ ] Γ ⊢ⁱ Θ ⇒ Γᵢ)
interior? Γ Θ
  with runχ (reps Γ) (names Γ) Θ
interior? Γ Θ | nothing        = nothing
interior? Γ Θ | just (Δ′ , cs) = just (_ , interior cs)

conversion? : (Γ : Ctxᵗ) (Θ : Boundary) → Maybe (∃[ Γᶜ ] Γ ⊢ᶜ Θ ⇒ Γᶜ)
conversion? Γ Θ
  with runχᶜ (reps Γ) (names Γ) Θ
conversion? Γ Θ | nothing        = nothing
conversion? Γ Θ | just (Δ′ , cs) = just (_ , conversion cs)

BoundaryWfResult : Ctxᵗ → Boundary → Set
BoundaryWfResult Γ Θ =
  Σ[ Γᵢ ∈ Ctxᵗ ] Σ[ Γᶜ ∈ Ctxᵗ ] BoundaryWf Γ Θ Γᵢ Γᶜ

boundaryWf? : (Γ : Ctxᵗ) (Θ : Boundary) → Maybe (BoundaryWfResult Γ Θ)
boundaryWf? Γ Θ with wfCtx? Γ
boundaryWf? Γ Θ | nothing = nothing
boundaryWf? Γ Θ | just wΓ with interior? Γ Θ
boundaryWf? Γ Θ | just wΓ | nothing = nothing
boundaryWf? Γ Θ | just wΓ | just (Γᵢ , int) with conversion? Γ Θ
boundaryWf? Γ Θ | just wΓ | just (Γᵢ , int) | nothing = nothing
boundaryWf? Γ Θ | just wΓ | just (Γᵢ , int) | just (Γᶜ , cnv) =
  just (Γᵢ , Γᶜ , bw wΓ int cnv)

------------------------------------------------------------------------
-- 6. Reading types between the two universes
------------------------------------------------------------------------

-- Forward: replace each live ordinary name by the representation variable
-- it names.  A `∀` extends only the LOCAL binder prefix on both sides.
read? : (η : TyCtx) (A : Ty) → Maybe (∃[ R ] η ⊢ A ~ R)
read? η (` X) with lookupˡ? η X
read? η (` X) | just (α , d) = just (` α , same-var d)
read? η (` X) | nothing      = nothing
read? η `ℕ = just (`ℕ , same-ℕ)
read? η `𝔹 = just (`𝔹 , same-𝔹)
read? η (A ⇒ B) with read? η A
read? η (A ⇒ B) | nothing = nothing
read? η (A ⇒ B) | just (R , p) with read? η B
read? η (A ⇒ B) | just (R , p) | just (S , q) = just (R ⇒ S , same-⇒ p q)
read? η (A ⇒ B) | just (R , p) | nothing = nothing
read? η (`∀ A) with read? (zero ∷ shiftReps η) A
read? η (`∀ A) | just (R , p) = just (`∀ R , same-∀ p)
read? η (`∀ A) | nothing      = nothing

-- RE-BASING.  `A` is read on the name map `η`; this finds its spelling
-- on `η′` through the REPRESENTATION, with the `_⊢_≈_⊣_` relating
-- them.  Partial, which is why crossing rules carry it as a premise.
-- Commentary.md § TypeCheck.agda / §6
rebase? : (η η′ : TyCtx) (A : Ty)
  → Maybe (∃[ A′ ] (∃[ R ] ((η′ ⊢ A′ ~ R) × (η ⊢ A ~ R))))
rebase? η η′ A with read? η A
rebase? η η′ A | nothing = nothing
rebase? η η′ A | just (R , q) with unread? η′ R
rebase? η η′ A | just (R , q) | just (A′ , p) = just (A′ , R , p , q)
rebase? η η′ A | just (R , q) | nothing = nothing

-- THE SAME THING FOR A CONVERSION, which is what `Peel` and `Merge`
-- need.  A conversion mentions ordinary names at its `id`, seal and
-- unseal leaves only, so both directions are `read?`/`unread?` with
-- those leaves added, one function per sort.
mutual
  readᵐ? : (η : TyCtx) (g : Mid) → Maybe (∃[ r ] η ⊩ᵐ g ~ r)
  readᵐ? η (id A) with read? η A
  readᵐ? η (id A) | just (R , p) = just (id R , sameᶜ-id p)
  readᵐ? η (id A) | nothing      = nothing
  readᵐ? η (s ↦ t) with readᶜ? η s
  readᵐ? η (s ↦ t) | nothing = nothing
  readᵐ? η (s ↦ t) | just (r , p) with readᶜ? η t
  readᵐ? η (s ↦ t) | just (r , p) | just (u , q) =
    just (r ↦ u , sameᶜ-fun p q)
  readᵐ? η (s ↦ t) | just (r , p) | nothing = nothing
  readᵐ? η (`∀ s) with readᶜ? (zero ∷ shiftReps η) s
  readᵐ? η (`∀ s) | just (r , p) = just (`∀ r , sameᶜ-all p)
  readᵐ? η (`∀ s) | nothing      = nothing

  readᵀ? : (η : TyCtx) (t : Tail) → Maybe (∃[ r ] η ⊩ᵀ t ~ r)
  readᵀ? η (mid g) with readᵐ? η g
  readᵀ? η (mid g) | just (r , p) = just (mid r , sameᶜ-mid p)
  readᵀ? η (mid g) | nothing      = nothing
  readᵀ? η (seal X) with lookupˡ? η X
  readᵀ? η (seal X) | just (α , d) = just (seal α , sameᶜ-seal d)
  readᵀ? η (seal X) | nothing      = nothing
  readᵀ? η (t ⨾seal X) with readᵀ? η t
  readᵀ? η (t ⨾seal X) | nothing = nothing
  readᵀ? η (t ⨾seal X) | just (r , p) with lookupˡ? η X
  readᵀ? η (t ⨾seal X) | just (r , p) | just (α , d) =
    just (r ⨾seal α , sameᶜ-seal-seq p d)
  readᵀ? η (t ⨾seal X) | just (r , p) | nothing = nothing

  readᶜ? : (η : TyCtx) (s : Conv) → Maybe (∃[ r ] η ⊩ s ~ r)
  readᶜ? η (tail t) with readᵀ? η t
  readᶜ? η (tail t) | just (r , p) = just (tail r , sameᶜ-tail p)
  readᶜ? η (tail t) | nothing      = nothing
  readᶜ? η (unseal X) with lookupˡ? η X
  readᶜ? η (unseal X) | just (α , d) = just (unseal α , sameᶜ-unseal d)
  readᶜ? η (unseal X) | nothing      = nothing
  readᶜ? η (unseal X ⨾ c) with lookupˡ? η X
  readᶜ? η (unseal X ⨾ c) | nothing = nothing
  readᶜ? η (unseal X ⨾ c) | just (α , d) with readᶜ? η c
  readᶜ? η (unseal X ⨾ c) | just (α , d) | just (r , p) =
    just (unseal α ⨾ r , sameᶜ-unseal-seq d p)
  readᶜ? η (unseal X ⨾ c) | just (α , d) | nothing = nothing

mutual
  unreadᵐ? : (η : TyCtx) (r : Mid) → Maybe (∃[ g ] η ⊩ᵐ g ~ r)
  unreadᵐ? η (id R) with unread? η R
  unreadᵐ? η (id R) | just (A , p) = just (id A , sameᶜ-id p)
  unreadᵐ? η (id R) | nothing      = nothing
  unreadᵐ? η (r ↦ u) with unreadᶜ? η r
  unreadᵐ? η (r ↦ u) | nothing = nothing
  unreadᵐ? η (r ↦ u) | just (s , p) with unreadᶜ? η u
  unreadᵐ? η (r ↦ u) | just (s , p) | just (t , q) =
    just (s ↦ t , sameᶜ-fun p q)
  unreadᵐ? η (r ↦ u) | just (s , p) | nothing = nothing
  unreadᵐ? η (`∀ r) with unreadᶜ? (zero ∷ shiftReps η) r
  unreadᵐ? η (`∀ r) | just (s , p) = just (`∀ s , sameᶜ-all p)
  unreadᵐ? η (`∀ r) | nothing      = nothing

  unreadᵀ? : (η : TyCtx) (r : Tail) → Maybe (∃[ t ] η ⊩ᵀ t ~ r)
  unreadᵀ? η (mid r) with unreadᵐ? η r
  unreadᵀ? η (mid r) | just (g , p) = just (mid g , sameᶜ-mid p)
  unreadᵀ? η (mid r) | nothing      = nothing
  unreadᵀ? η (seal α) with find? η α
  unreadᵀ? η (seal α) | just (X , d) = just (seal X , sameᶜ-seal d)
  unreadᵀ? η (seal α) | nothing      = nothing
  unreadᵀ? η (r ⨾seal α) with unreadᵀ? η r
  unreadᵀ? η (r ⨾seal α) | nothing = nothing
  unreadᵀ? η (r ⨾seal α) | just (t , p) with find? η α
  unreadᵀ? η (r ⨾seal α) | just (t , p) | just (X , d) =
    just (t ⨾seal X , sameᶜ-seal-seq p d)
  unreadᵀ? η (r ⨾seal α) | just (t , p) | nothing = nothing

  unreadᶜ? : (η : TyCtx) (r : Conv) → Maybe (∃[ s ] η ⊩ s ~ r)
  unreadᶜ? η (tail r) with unreadᵀ? η r
  unreadᶜ? η (tail r) | just (t , p) = just (tail t , sameᶜ-tail p)
  unreadᶜ? η (tail r) | nothing      = nothing
  unreadᶜ? η (unseal α) with find? η α
  unreadᶜ? η (unseal α) | just (X , d) =
    just (unseal X , sameᶜ-unseal d)
  unreadᶜ? η (unseal α) | nothing      = nothing
  unreadᶜ? η (unseal α ⨾ r) with find? η α
  unreadᶜ? η (unseal α ⨾ r) | nothing = nothing
  unreadᶜ? η (unseal α ⨾ r) | just (X , d) with unreadᶜ? η r
  unreadᶜ? η (unseal α ⨾ r) | just (X , d) | just (s , p) =
    just (unseal X ⨾ s , sameᶜ-unseal-seq d p)
  unreadᶜ? η (unseal α ⨾ r) | just (X , d) | nothing = nothing

-- `weaken? η η′ s` is `rebase?` one universe up: `s` is read on η, and
-- this finds its spelling on η′ with the `SameConv` that relates them.
weaken? : (η η′ : TyCtx) (s : Conv)
  → Maybe (∃[ s′ ] (∃[ r ] ((η′ ⊩ s′ ~ r) × (η ⊩ s ~ r))))
weaken? η η′ s with readᶜ? η s
weaken? η η′ s | nothing = nothing
weaken? η η′ s | just (r , q) with unreadᶜ? η′ r
weaken? η η′ s | just (r , q) | just (s′ , p) = just (s′ , r , p , q)
weaken? η η′ s | just (r , q) | nothing = nothing

-- the same for a TAIL, which `Merge` carries for its inner conversion
weakenᵀ? : (η η′ : TyCtx) (t : Tail)
  → Maybe (∃[ t′ ] (∃[ r ] ((η′ ⊩ᵀ t′ ~ r) × (η ⊩ᵀ t ~ r))))
weakenᵀ? η η′ t with readᵀ? η t
weakenᵀ? η η′ t | nothing = nothing
weakenᵀ? η η′ t | just (r , q) with unreadᵀ? η′ r
weakenᵀ? η η′ t | just (r , q) | just (t′ , p) = just (t′ , r , p , q)
weakenᵀ? η η′ t | just (r , q) | nothing = nothing

sameTy? : (Γ Γ′ : Ctxᵗ) (A B : Ty) → Maybe (Γ ⊢ A ≈ B ⊣ Γ′)
sameTy? Γ Γ′ A B with read? (names Γ) A
sameTy? Γ Γ′ A B | nothing = nothing
sameTy? Γ Γ′ A B | just (R , p) with read? (names Γ′) B
sameTy? Γ Γ′ A B | just (R , p) | nothing = nothing
sameTy? Γ Γ′ A B | just (R , p) | just (S , q) with R ≟Ty S
sameTy? Γ Γ′ A B | just (R , p) | just (S , q) | just refl =
  just (R , p , q)
sameTy? Γ Γ′ A B | just (R , p) | just (S , q) | nothing = nothing

------------------------------------------------------------------------
-- 7. The lookup square, type formation, and conversions
------------------------------------------------------------------------

∋tv? : (Γ : Ctxᵗ) (X : ℕ) → Maybe (Γ ∋tv X)
∋tv? Γ X with lookupˡ? (names Γ) X
∋tv? Γ X | just v  = just v
∋tv? Γ X | nothing = nothing

wfTy? : (Γ : Ctxᵗ) (A : Ty) → Maybe (Γ ⊢ᵗ A)
wfTy? Γ (` X) with ∋tv? Γ X
wfTy? Γ (` X) | just tv = just (wf-var tv)
wfTy? Γ (` X) | nothing = nothing
wfTy? Γ `ℕ = just wf-ℕ
wfTy? Γ `𝔹 = just wf-𝔹
wfTy? Γ (A ⇒ B) with wfTy? Γ A
wfTy? Γ (A ⇒ B) | nothing = nothing
wfTy? Γ (A ⇒ B) | just wA with wfTy? Γ B
wfTy? Γ (A ⇒ B) | just wA | just wB = just (wf-⇒ wA wB)
wfTy? Γ (A ⇒ B) | just wA | nothing = nothing
wfTy? Γ (`∀ A) with wfTy? (underΛ Γ) A
wfTy? Γ (`∀ A) | just wA = just (wf-∀ wA)
wfTy? Γ (`∀ A) | nothing = nothing

-- A conversion determines BOTH its types: every rep it mentions is read
-- by name from the conversion context (strong-rep-nu.Conversion §5).
ConvResult : Ctxᵗ → Conv → Set
ConvResult Γ c = Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Γ ⊢ c ∶ A ⇝ B

-- `NoCancel` is decidable: it only compares names.
noCancelᵀ? : (X : ℕ) (t : Tail) → Maybe (NoCancelᵀ X t)
noCancelᵀ? X (mid g) = just tt
noCancelᵀ? X (seal Y) with X ≟ Y
noCancelᵀ? X (seal Y) | yes _  = nothing
noCancelᵀ? X (seal Y) | no ne = just ne
noCancelᵀ? X (t ⨾seal Y) = noCancelᵀ? X t

noCancel? : (X : ℕ) (c : Conv) → Maybe (NoCancel X c)
noCancel? X (tail t)       = noCancelᵀ? X t
noCancel? X (unseal Y)     = just tt
noCancel? X (unseal Y ⨾ c) = just tt

mutual
  convᵐTy? : (Γ : Ctxᵗ) (g : Mid)
    → Maybe (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Γ ⊢ᵐ g ∶ A ⇝ B)
  convᵐTy? Γ (id (` X)) with ∋tv? Γ X
  convᵐTy? Γ (id (` X)) | just tv = just (` X , ` X , conv-idv tv)
  convᵐTy? Γ (id (` X)) | nothing = nothing
  convᵐTy? Γ (id `ℕ) = just (`ℕ , `ℕ , conv-id base-ℕ)
  convᵐTy? Γ (id `𝔹) = just (`𝔹 , `𝔹 , conv-id base-𝔹)
  convᵐTy? Γ (id (A ⇒ B)) = nothing
  convᵐTy? Γ (id (`∀ A)) = nothing
  convᵐTy? Γ (s ↦ t) with convTy? Γ s
  convᵐTy? Γ (s ↦ t) | nothing = nothing
  convᵐTy? Γ (s ↦ t) | just (A′ , A , ⊢s) with convTy? Γ t
  convᵐTy? Γ (s ↦ t) | just (A′ , A , ⊢s) | just (B , B′ , ⊢t) =
    just (A ⇒ B , A′ ⇒ B′ , conv-fun ⊢s ⊢t)
  convᵐTy? Γ (s ↦ t) | just (A′ , A , ⊢s) | nothing = nothing
  convᵐTy? Γ (`∀ s) with convTy? (underΛ Γ) s
  convᵐTy? Γ (`∀ s) | just (A , B , ⊢s) =
    just (`∀ A , `∀ B , conv-all ⊢s)
  convᵐTy? Γ (`∀ s) | nothing = nothing

  convᵀTy? : (Γ : Ctxᵗ) (t : Tail)
    → Maybe (Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Γ ⊢ᵀ t ∶ A ⇝ B)
  convᵀTy? Γ (mid g) with convᵐTy? Γ g
  convᵀTy? Γ (mid g) | just (A , B , ⊢g) = just (A , B , conv-mid ⊢g)
  convᵀTy? Γ (mid g) | nothing = nothing
  convᵀTy? Γ (seal X) with ∋:=? Γ X
  convᵀTy? Γ (seal X) | just (A , d) = just (A , ` X , conv-seal d)
  convᵀTy? Γ (seal X) | nothing      = nothing
  convᵀTy? Γ (t ⨾seal X) with isIdᵀ? t
  convᵀTy? Γ (t ⨾seal X) | yes _ = nothing
  convᵀTy? Γ (t ⨾seal X) | no n with convᵀTy? Γ t
  convᵀTy? Γ (t ⨾seal X) | no n | nothing = nothing
  convᵀTy? Γ (t ⨾seal X) | no n | just (A , R′ , ⊢t) with ∋:=? Γ X
  convᵀTy? Γ (t ⨾seal X) | no n | just (A , R′ , ⊢t) | nothing = nothing
  convᵀTy? Γ (t ⨾seal X) | no n | just (A , R′ , ⊢t) | just (R , d)
    with R′ ≟Ty R
  convᵀTy? Γ (t ⨾seal X) | no n | just (A , R′ , ⊢t) | just (R , d)
    | just refl = just (A , ` X , conv-seal-seq ⊢t d n)
  convᵀTy? Γ (t ⨾seal X) | no n | just (A , R′ , ⊢t) | just (R , d)
    | nothing = nothing

  convTy? : (Γ : Ctxᵗ) (c : Conv) → Maybe (ConvResult Γ c)
  convTy? Γ (tail t) with convᵀTy? Γ t
  convTy? Γ (tail t) | just (A , B , ⊢t) = just (A , B , conv-tail ⊢t)
  convTy? Γ (tail t) | nothing = nothing
  convTy? Γ (unseal X) with ∋:=? Γ X
  convTy? Γ (unseal X) | just (A , d) = just (` X , A , conv-unseal d)
  convTy? Γ (unseal X) | nothing      = nothing
  convTy? Γ (unseal X ⨾ c) with isIdᶜ? c | noCancel? X c
  convTy? Γ (unseal X ⨾ c) | yes _ | m = nothing
  convTy? Γ (unseal X ⨾ c) | no n | nothing = nothing
  convTy? Γ (unseal X ⨾ c) | no n | just nc with ∋:=? Γ X
  convTy? Γ (unseal X ⨾ c) | no n | just nc | nothing = nothing
  convTy? Γ (unseal X ⨾ c) | no n | just nc | just (R , d)
    with convTy? Γ c
  convTy? Γ (unseal X ⨾ c) | no n | just nc | just (R , d) | nothing =
    nothing
  convTy? Γ (unseal X ⨾ c) | no n | just nc | just (R , d)
    | just (R′ , B , ⊢c) with R′ ≟Ty R
  convTy? Γ (unseal X ⨾ c) | no n | just nc | just (R , d)
    | just (R′ , B , ⊢c) | just refl =
    just (` X , B , conv-unseal-seq d ⊢c n nc)
  convTy? Γ (unseal X ⨾ c) | no n | just nc | just (R , d)
    | just (R′ , B , ⊢c) | nothing = nothing

------------------------------------------------------------------------
-- 8. Term typing
------------------------------------------------------------------------

lookupTm? : (Γ : Ctx) (x : Var) → Maybe (∃[ A ] Γ ∋ x ⦂ A)
lookupTm? []      x       = nothing
lookupTm? (A ∷ Γ) zero    = just (A , here)
lookupTm? (A ∷ Γ) (suc x) with lookupTm? Γ x
lookupTm? (A ∷ Γ) (suc x) | just (B , d) = just (B , there d)
lookupTm? (A ∷ Γ) (suc x) | nothing      = nothing

InferResult : Ctxᵗ → Ctx → Term → Set
InferResult Δ Γ M = Σ[ A ∈ Ty ] Δ ∣ Γ ⊢ M ⦂ A

-- Deciding the classifications `Value` guards on.  `infer` needs
-- `value?` for `⊢Λ`'s value restriction; strong-rep-nu.Eval reuses
-- both for the rules' side conditions.
inertTail? : (t : Tail) → Maybe (InertTail t)
inertTail? (mid (id (` X)))   = just I-idv
inertTail? (mid (id `ℕ))      = nothing
inertTail? (mid (id `𝔹))      = nothing
inertTail? (mid (id (A ⇒ B))) = nothing
inertTail? (mid (id (`∀ A)))  = nothing
inertTail? (mid (s ↦ t))      = just I-fun
inertTail? (mid (`∀ s))       = just I-all
inertTail? (seal X)           = just I-seal
inertTail? (t ⨾seal X)        = just I-seal-seq

inert? : (c : Conv) → Maybe (Inert c)
inert? (tail t) with inertTail? t
inert? (tail t) | just it = just (I-tail it)
inert? (tail t) | nothing = nothing
inert? (unseal X)     = nothing
inert? (unseal X ⨾ c) = nothing

-- `S-Λ` carries `Value N` and `V-⟪⟫` carries `Simple U` and
-- `InertTail t`, so this is a recursion, not a shape test.
mutual
  simple? : (M : Term) → Maybe (Simple M)
  simple? (` x)          = nothing
  simple? ($ n)          = just S-$
  simple? `true          = just S-true
  simple? `false         = just S-false
  simple? (ƛ A ∙ N)      = just S-ƛ
  simple? (L · M)        = nothing
  simple? (ν A · L ⟨ c ⟩) = nothing
  simple? (Λ N) with value? N
  simple? (Λ N) | just v  = just (S-Λ v)
  simple? (Λ N) | nothing = nothing
  simple? (M ⟪ Θ , c ⟫)  = nothing

  value? : (M : Term) → Maybe (Value M)
  value? (` x)          = nothing
  value? ($ n)          = just (V-simple S-$)
  value? `true          = just (V-simple S-true)
  value? `false         = just (V-simple S-false)
  value? (ƛ A ∙ N)      = just (V-simple S-ƛ)
  value? (L · M)        = nothing
  value? (ν A · L ⟨ c ⟩) = nothing
  value? (Λ N) with value? N
  value? (Λ N) | just v  = just (V-simple (S-Λ v))
  value? (Λ N) | nothing = nothing
  value? (M ⟪ Θ , tail t ⟫) with simple? M | inertTail? t
  value? (M ⟪ Θ , tail t ⟫) | just u | just it = just (V-⟪⟫ u it)
  value? (M ⟪ Θ , tail t ⟫) | just u | nothing = nothing
  value? (M ⟪ Θ , tail t ⟫) | nothing | it    = nothing
  value? (M ⟪ Θ , unseal X ⟫)     = nothing
  value? (M ⟪ Θ , unseal X ⨾ c ⟫) = nothing

infer : (Δ : Ctxᵗ) (Γ : Ctx) (M : Term) → Maybe (InferResult Δ Γ M)
infer Δ Γ (` x) with lookupTm? Γ x
infer Δ Γ (` x) | just (A , d) = just (A , ⊢` d)
infer Δ Γ (` x) | nothing      = nothing
infer Δ Γ ($ n) = just (`ℕ , ⊢$)
infer Δ Γ `true = just (`𝔹 , ⊢true)
infer Δ Γ `false = just (`𝔹 , ⊢false)
infer Δ Γ (ƛ A ∙ N) with wfTy? Δ A
infer Δ Γ (ƛ A ∙ N) | nothing = nothing
infer Δ Γ (ƛ A ∙ N) | just wA with infer Δ (A ∷ Γ) N
infer Δ Γ (ƛ A ∙ N) | just wA | just (B , ⊢N) =
  just (A ⇒ B , ⊢ƛ wA ⊢N)
infer Δ Γ (ƛ A ∙ N) | just wA | nothing = nothing
infer Δ Γ (L · M) with infer Δ Γ L
infer Δ Γ (L · M) | nothing = nothing
infer Δ Γ (L · M) | just (` X , ⊢L) = nothing
infer Δ Γ (L · M) | just (`ℕ , ⊢L) = nothing
infer Δ Γ (L · M) | just (`𝔹 , ⊢L) = nothing
infer Δ Γ (L · M) | just (`∀ C , ⊢L) = nothing
infer Δ Γ (L · M) | just (A ⇒ B , ⊢L) with infer Δ Γ M
infer Δ Γ (L · M) | just (A ⇒ B , ⊢L) | nothing = nothing
infer Δ Γ (L · M) | just (A ⇒ B , ⊢L) | just (A′ , ⊢M) with A′ ≟Ty A
infer Δ Γ (L · M) | just (A ⇒ B , ⊢L) | just (A′ , ⊢M) | just refl =
  just (B , ⊢· ⊢L ⊢M)
infer Δ Γ (L · M) | just (A ⇒ B , ⊢L) | just (A′ , ⊢M) | nothing =
  nothing
infer Δ Γ (Λ N) with value? N
infer Δ Γ (Λ N) | nothing = nothing
infer Δ Γ (Λ N) | just vN with infer (underΛ Δ) (⤊ Γ) N
infer Δ Γ (Λ N) | just vN | just (C , ⊢N) = just (`∀ C , ⊢Λ vN ⊢N)
infer Δ Γ (Λ N) | just vN | nothing = nothing
-- `ν`.  `R` is READ from `A`; `c` is typed on the conversion context
-- of `TyBetaBoundary` at `allocate R Δ` (the context the `Nu` rules
-- leave), and the result type is `c`'s target re-based onto that
-- allocated exterior.
infer Δ Γ (ν A · L ⟨ c ⟩) with wfTy? Δ A
infer Δ Γ (ν A · L ⟨ c ⟩) | nothing = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA with read? (names Δ) A
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | nothing = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA) with infer Δ Γ L
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA) | nothing = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (` X , ⊢L) = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`ℕ , ⊢L) = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`𝔹 , ⊢L) = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (C ⇒ D , ⊢L) = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) with boundaryWf? (allocate R Δ) TyBetaBoundary
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) | nothing = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) | just (Δᵢ , Δᶜ , mwf) with convTy? Δᶜ c
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) | just (Δᵢ , Δᶜ , mwf) | nothing = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) | just (Δᵢ , Δᶜ , mwf) | just (C′ , Cₑ , ⊢c)
  with C′ ≟Ty C
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) | just (Δᵢ , Δᶜ , mwf) | just (C′ , Cₑ , ⊢c)
  | nothing = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) | just (Δᵢ , Δᶜ , mwf) | just (C′ , Cₑ , ⊢c)
  | just refl with rebase? (names Δᶜ) (names (allocate R Δ)) Cₑ
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) | just (Δᵢ , Δᶜ , mwf) | just (C′ , Cₑ , ⊢c)
  | just refl | nothing = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) | just (Δᵢ , Δᶜ , mwf) | just (C′ , Cₑ , ⊢c)
  | just refl | just (B , sameₑ) with wfTy? Δ B
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) | just (Δᵢ , Δᶜ , mwf) | just (C′ , Cₑ , ⊢c)
  | just refl | just (B , sameₑ) | nothing = nothing
infer Δ Γ (ν A · L ⟨ c ⟩) | just wA | just (R , rA)
  | just (`∀ C , ⊢L) | just (Δᵢ , Δᶜ , mwf) | just (C′ , Cₑ , ⊢c)
  | just refl | just (B , sameₑ) | just wB =
  just (B , ⊢ν wA rA ⊢L mwf ⊢c sameₑ wB)
-- The boundary.  `env`'s mechanical premises come from §5; its three
-- informative ones are the interior term's type, the conversion's two
-- types, and the two readings that relate them.
infer Δ Γ (M ⟪ Θ , c ⟫) with boundaryWf? Δ Θ
infer Δ Γ (M ⟪ Θ , c ⟫) | nothing = nothing
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) with infer Δᵢ [] M
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) | nothing = nothing
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) | just (Bᵢ , ⊢M)
  with convTy? Δᶜ c
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) | just (Bᵢ , ⊢M)
  | nothing = nothing
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) | just (Bᵢ , ⊢M)
  | just (Cᵢ , Cₑ , ⊢c) with sameTy? Δᵢ Δᶜ Bᵢ Cᵢ
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) | just (Bᵢ , ⊢M)
  | just (Cᵢ , Cₑ , ⊢c) | nothing = nothing
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) | just (Bᵢ , ⊢M)
  | just (Cᵢ , Cₑ , ⊢c) | just sameᵢ
  with rebase? (names Δᶜ) (names Δ) Cₑ
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) | just (Bᵢ , ⊢M)
  | just (Cᵢ , Cₑ , ⊢c) | just sameᵢ | nothing = nothing
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) | just (Bᵢ , ⊢M)
  | just (Cᵢ , Cₑ , ⊢c) | just sameᵢ | just (Bₑ , sameₑ) with wfTy? Δ Bₑ
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) | just (Bᵢ , ⊢M)
  | just (Cᵢ , Cₑ , ⊢c) | just sameᵢ | just (Bₑ , sameₑ) | nothing =
  nothing
infer Δ Γ (M ⟪ Θ , c ⟫) | just (Δᵢ , Δᶜ , mwf) | just (Bᵢ , ⊢M)
  | just (Cᵢ , Cₑ , ⊢c) | just sameᵢ | just (Bₑ , sameₑ) | just wE =
  just (Bₑ , env mwf ⊢M ⊢c sameᵢ sameₑ wE)

------------------------------------------------------------------------
-- 9. Checking a term against a stated type
------------------------------------------------------------------------

check⊢ : (Δ : Ctxᵗ) (Γ : Ctx) (M : Term) (A : Ty)
  → Maybe (Δ ∣ Γ ⊢ M ⦂ A)
check⊢ Δ Γ M A with infer Δ Γ M
check⊢ Δ Γ M A | nothing = nothing
check⊢ Δ Γ M A | just (B , ⊢M) with B ≟Ty A
check⊢ Δ Γ M A | just (B , ⊢M) | just refl = just ⊢M
check⊢ Δ Γ M A | just (B , ⊢M) | nothing   = nothing

checkConv : (Γ : Ctxᵗ) (c : Conv) (A B : Ty) → Maybe (Γ ⊢ c ∶ A ⇝ B)
checkConv Γ c A B with convTy? Γ c
checkConv Γ c A B | nothing = nothing
checkConv Γ c A B | just (A′ , B′ , ⊢c) with A′ ≟Ty A
checkConv Γ c A B | just (A′ , B′ , ⊢c) | nothing = nothing
checkConv Γ c A B | just (A′ , B′ , ⊢c) | just refl with B′ ≟Ty B
checkConv Γ c A B | just (A′ , B′ , ⊢c) | just refl | just refl =
  just ⊢c
checkConv Γ c A B | just (A′ , B′ , ⊢c) | just refl | nothing = nothing

check~ : (η : TyCtx) (A R : Ty) → Maybe (η ⊢ A ~ R)
check~ η A R with read? η A
check~ η A R | nothing = nothing
check~ η A R | just (S , p) with S ≟Ty R
check~ η A R | just (S , p) | just refl = just p
check~ η A R | just (S , p) | nothing   = nothing

------------------------------------------------------------------------
-- 10. Forcing a checker
------------------------------------------------------------------------

-- `IsJ m` is the unit RECORD when the checker succeeded, so Agda solves
-- a hidden argument of that type by eta on its own; on `nothing` its
-- type is `⊥`, and the unsolved meta IS the rejection.
-- Commentary.md § TypeCheck.agda / §10
IsJ : ∀ {A : Set} → Maybe A → Set
IsJ (just _) = ⊤
IsJ nothing  = ⊥

force : ∀ {A : Set} (m : Maybe A) → IsJ m → A
force (just x) _  = x
force nothing  ()

-- A term's typing derivation.  Every argument is read off the goal.
tc : ∀ {Δ Γ M A} {w : IsJ (check⊢ Δ Γ M A)} → Δ ∣ Γ ⊢ M ⦂ A
tc {Δ} {Γ} {M} {A} {w} = force (check⊢ Δ Γ M A) w

-- A conversion's typing derivation, likewise read off the goal.
tk : ∀ {Γ c A B} {w : IsJ (checkConv Γ c A B)} → Γ ⊢ c ∶ A ⇝ B
tk {Γ} {c} {A} {B} {w} = force (checkConv Γ c A B) w

-- Name-uniqueness of a name map.  No REDUCTION rule carries this any
-- more, but `WfCtx`'s `name-fn` field still asks for it.
tu : ∀ {Δ} {w : IsJ (unique? Δ)} → Unique Δ
tu {Δ} {w} = force (unique? Δ) w

-- A type's well-formedness.
tf : ∀ {Γ A} {w : IsJ (wfTy? Γ A)} → Γ ⊢ᵗ A
tf {Γ} {A} {w} = force (wfTy? Γ A) w

-- The reading that relates an ordinary type to its representation, which
-- `Nu-Λ` and `Nu-⟪Λ⟫` carry as `Δ ⊢ᶜ A ~ R`.
tr : ∀ {η A R} {w : IsJ (check~ η A R)} → η ⊢ A ~ R
tr {η} {A} {R} {w} = force (check~ η A R) w

-- `from-just` turns a checker into what it found; the caller's type
-- signature pins the answer.  Used where the goal does not fix it.
int! : (Γ : Ctxᵗ) (Θ : Boundary) → From-just (interior? Γ Θ)
int! Γ Θ = from-just (interior? Γ Θ)

conv! : (Γ : Ctxᵗ) (Θ : Boundary) → From-just (conversion? Γ Θ)
conv! Γ Θ = from-just (conversion? Γ Θ)

mw! : (Γ : Ctxᵗ) (Θ : Boundary) → From-just (boundaryWf? Γ Θ)
mw! Γ Θ = from-just (boundaryWf? Γ Θ)

wf! : (Γ : Ctxᵗ) → From-just (wfCtx? Γ)
wf! Γ = from-just (wfCtx? Γ)

-- The lookup square, in the INFERRING form (the goal need not fix the
-- representation).
sq! : (Γ : Ctxᵗ) (X : ℕ) → From-just (∋:=? Γ X)
sq! Γ X = from-just (∋:=? Γ X)

tv! : (Γ : Ctxᵗ) (X : ℕ) → From-just (∋tv? Γ X)
tv! Γ X = from-just (∋tv? Γ X)

cv! : (Γ : Ctxᵗ) (c : Conv) → From-just (convTy? Γ c)
cv! Γ c = from-just (convTy? Γ c)

ty! : (Δ : Ctxᵗ) (Γ : Ctx) (M : Term) → From-just (infer Δ Γ M)
ty! Δ Γ M = from-just (infer Δ Γ M)
