module strong.TypeCheck where

-- Strong System F — EXECUTABLE, DERIVATION-PRODUCING TYPE CHECKING.
--
-- Every checker in this file returns a `Maybe` of the ORDINARY derivation
-- it found, never a bit and never a postulate.  The caller states the
-- answer it expects and §11 forces the checker at it, so a failure or a
-- different answer is a type error rather than a silently accepted
-- witness.  Nothing here is assumed and nothing here is trusted: the
-- derivations are built from the constructors of the judgements in
-- strong.Ctx, strong.CtxMorph, strong.Conversion and strong.Terms.
--
-- USAGE.  `tc` IS a typing derivation — it reads its four arguments off
-- the goal, so
--
--     P₀-⊢ : empty ∣ [] ⊢ P₀ ⦂ `ℕ
--     P₀-⊢ = tc
--
-- is the whole thing.  `tk`, `tu`, `tf` and `tr` do the same for the
-- conversion, uniqueness, type-formation and representation-reading
-- judgements.  Where the answer is an OUTPUT the goal does not fix — a
-- morphism's two induced contexts, a lookup's type — the `!` family is
-- used instead and the input is written out.
--
-- WHY IT EXISTS (2026-09-17).  A boundary `M ⟪ Θ , c ⟫` is typed by `env`,
-- whose six premises are of two very different kinds.  Three of them say
-- something about the PROGRAM: which conversion applies, which `_⊢_≈_⊣_`
-- reading relates the three sides, what the interior term's type is.  The
-- other three are MECHANICAL: the two contexts Θ induces, and the
-- well-formedness of each.  A derivation of `Ξ ∣ Δ ⊢χ changes Θ ⇒ Δ′` is
-- one line per change and contains nothing the change list does not
-- already determine.
--
-- That became unworkable when the fourth reduction example was finished.
-- `CancelR` and `IdPush` replace their frames by the COMPOSITES `Θ₁ ⋉ Θ₂`
-- and `rewind Θ₂`, whose change lists are the concatenations of their
-- arguments', so unwinding an n-deep tower of boundaries reaches frames
-- carrying tens of changes each.  The checker removes that transcription
-- entirely, and — since it decides the term judgement too — an example's
-- typing derivation becomes a statement of the type and nothing else.
--
-- The one genuinely non-obvious checker is `sameTyExt?` (§7).  It is also
-- the reason `infer` is an inference and not a check:  `env`'s
-- exterior premise reads the boundary's exterior type through Θ's
-- representation-bind prefix, `Δᶜ ⊢ᶜ Cₑ ~ shiftRep n R`, so an exterior
-- type can only be inferred by inverting `shiftRep`.  That is `strAt`
-- (§6), strengthening at a binder depth — the one place in the file where
-- a checker builds an equation instead of a derivation.  Checking mode
-- would avoid it, but `⊢·` and `⊢·[]` have to INFER the head's type and a
-- head can be a boundary, so inference is not optional.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_)
open import Data.Nat.Properties using (_≟_; _<?_; ≮⇒≥; m+[n∸m]≡n)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing; From-just; from-just)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; TyVar; Renameᵗ; renameᵗ;
         extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms

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

lookupˡ? : ∀ {A : Set} (xs : List A) (i : ℕ) → Maybe (∃[ x ] xs ∋ˡ i := x)
lookupˡ? []       i       = nothing
lookupˡ? (x ∷ xs) zero    = just (x , here)
lookupˡ? (x ∷ xs) (suc i) with lookupˡ? xs i
lookupˡ? (x ∷ xs) (suc i) | just (y , d) = just (y , there d)
lookupˡ? (x ∷ xs) (suc i) | nothing      = nothing

-- Where a representation variable currently sits, if it is live at all.
-- This is what the re-unlock clause of `_∣_⊢χᶜ_⇒_` needs.
find? : (Δ : TyCtx) (α : RVar) → Maybe (∃[ X ] Δ ∋ˡ X := α)
find? []      α = nothing
find? (β ∷ Δ) α with α ≟ β
find? (β ∷ Δ) α | yes refl = just (zero , here)
find? (β ∷ Δ) α | no  _    with find? Δ α
find? (β ∷ Δ) α | no  _    | just (X , d) = just (suc X , there d)
find? (β ∷ Δ) α | no  _    | nothing      = nothing

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
runδ Ξ Δ (lock X α) with validRVar? Ξ α
runδ Ξ Δ (lock X α) | nothing = nothing
runδ Ξ Δ (lock X α) | just v  with del? α Δ X
runδ Ξ Δ (lock X α) | just v  | nothing = nothing
runδ Ξ Δ (lock X α) | just v  | just (Δ′ , d) with fresh? α Δ′
runδ Ξ Δ (lock X α) | just v  | just (Δ′ , d) | nothing = nothing
runδ Ξ Δ (lock X α) | just v  | just (Δ′ , d) | just f =
  just (Δ′ , step-lock v d f)
runδ Ξ Δ (unlock X α) with validRVar? Ξ α
runδ Ξ Δ (unlock X α) | nothing = nothing
runδ Ξ Δ (unlock X α) | just v  with fresh? α Δ
runδ Ξ Δ (unlock X α) | just v  | nothing = nothing
runδ Ξ Δ (unlock X α) | just v  | just f with ins? α Δ X
runδ Ξ Δ (unlock X α) | just v  | just f | nothing = nothing
runδ Ξ Δ (unlock X α) | just v  | just f | just (Δ′ , i) =
  just (Δ′ , step-unlock v f i)

-- The tail acts first (head-LAST order, strong.CtxMorph §2).
runχ : (Ξ : RepCtx) (Δ : TyCtx) (χ : List Change)
  → Maybe (∃[ Δ′ ] Ξ ∣ Δ ⊢χ χ ⇒ Δ′)
runχ Ξ Δ []      = just (Δ , changes[])
runχ Ξ Δ (δ ∷ χ) with runχ Ξ Δ χ
runχ Ξ Δ (δ ∷ χ) | nothing = nothing
runχ Ξ Δ (δ ∷ χ) | just (Δ₂ , cs) with runδ Ξ Δ₂ δ
runχ Ξ Δ (δ ∷ χ) | just (Δ₂ , cs) | nothing = nothing
runχ Ξ Δ (δ ∷ χ) | just (Δ₂ , cs) | just (Δ₃ , st) =
  just (Δ₃ , changes∷ cs st)

-- The conversion reading: a `lock` is skipped, and an `unlock` of a name
-- the skipped locks left live is a no-op (strong.CtxMorph §3).
runχᶜ : (Ξ : RepCtx) (Δ : TyCtx) (χ : List Change)
  → Maybe (∃[ Δ′ ] Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′)
runχᶜ Ξ Δ [] = just (Δ , conv[])
runχᶜ Ξ Δ (lock X α ∷ χ) with validRVar? Ξ α
runχᶜ Ξ Δ (lock X α ∷ χ) | nothing = nothing
runχᶜ Ξ Δ (lock X α ∷ χ) | just v with runχᶜ Ξ Δ χ
runχᶜ Ξ Δ (lock X α ∷ χ) | just v | nothing = nothing
runχᶜ Ξ Δ (lock X α ∷ χ) | just v | just (Δ₂ , cs) =
  just (Δ₂ , conv-lock v cs)
runχᶜ Ξ Δ (unlock X α ∷ χ) with validRVar? Ξ α
runχᶜ Ξ Δ (unlock X α ∷ χ) | nothing = nothing
runχᶜ Ξ Δ (unlock X α ∷ χ) | just v with runχᶜ Ξ Δ χ
runχᶜ Ξ Δ (unlock X α ∷ χ) | just v | nothing = nothing
runχᶜ Ξ Δ (unlock X α ∷ χ) | just v | just (Δ₂ , cs) with fresh? α Δ₂
runχᶜ Ξ Δ (unlock X α ∷ χ) | just v | just (Δ₂ , cs) | just f
  with ins? α Δ₂ X
runχᶜ Ξ Δ (unlock X α ∷ χ) | just v | just (Δ₂ , cs) | just f
  | just (Δ₃ , i) = just (Δ₃ , conv-unlock v cs f i)
runχᶜ Ξ Δ (unlock X α ∷ χ) | just v | just (Δ₂ , cs) | just f
  | nothing = nothing
runχᶜ Ξ Δ (unlock X α ∷ χ) | just v | just (Δ₂ , cs) | nothing
  with find? Δ₂ α
runχᶜ Ξ Δ (unlock X α ∷ χ) | just v | just (Δ₂ , cs) | nothing
  | just (Y , d) = just (Δ₂ , conv-unlock-live v cs d)
runχᶜ Ξ Δ (unlock X α ∷ χ) | just v | just (Δ₂ , cs) | nothing
  | nothing = nothing

------------------------------------------------------------------------
-- 4. Representation payloads and context well-formedness
------------------------------------------------------------------------

-- A payload index below the local binder depth is a payload-local
-- variable; otherwise it is `n + α` for a free representation variable α,
-- and the subtraction has to be proved to put the index back in
-- constructor form.
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

-- Every bind payload is checked over the SAME exterior representation
-- context (the parallel-bind discipline, strong.CtxMorph §1).
binds? : (Ξ : RepCtx) (Rs : List Ty) → Maybe (Ξ ⊢ᴮ Rs)
binds? Ξ []       = just binds[]
binds? Ξ (R ∷ Rs) with wfᴿ? Ξ zero R
binds? Ξ (R ∷ Rs) | nothing = nothing
binds? Ξ (R ∷ Rs) | just wR with binds? Ξ Rs
binds? Ξ (R ∷ Rs) | just wR | just bs = just (binds∷ wR bs)
binds? Ξ (R ∷ Rs) | just wR | nothing = nothing

------------------------------------------------------------------------
-- 5. The two induced contexts, and a complete morphism witness
------------------------------------------------------------------------

interior? : (Γ : Ctxᵗ) (Θ : CtxMorph) → Maybe (∃[ Γᵢ ] Γ ⊢ⁱ Θ ⇒ Γᵢ)
interior? Γ Θ
  with runχ (reps (extendReps (binds Θ) Γ))
            (names (extendReps (binds Θ) Γ)) (changes Θ)
interior? Γ Θ | nothing        = nothing
interior? Γ Θ | just (Δ′ , cs) = just (_ , interior cs)

conversion? : (Γ : Ctxᵗ) (Θ : CtxMorph) → Maybe (∃[ Γᶜ ] Γ ⊢ᶜ Θ ⇒ Γᶜ)
conversion? Γ Θ
  with runχᶜ (reps (extendReps (binds Θ) Γ))
             (names (extendReps (binds Θ) Γ)) (changes Θ)
conversion? Γ Θ | nothing        = nothing
conversion? Γ Θ | just (Δ′ , cs) = just (_ , conversion cs)

MorphWfResult : Ctxᵗ → CtxMorph → Set
MorphWfResult Γ Θ =
  Σ[ Γᵢ ∈ Ctxᵗ ] Σ[ Γᶜ ∈ Ctxᵗ ] MorphWf Γ Θ Γᵢ Γᶜ

morphWf? : (Γ : Ctxᵗ) (Θ : CtxMorph) → Maybe (MorphWfResult Γ Θ)
morphWf? Γ Θ with wfCtx? Γ
morphWf? Γ Θ | nothing = nothing
morphWf? Γ Θ | just wΓ with binds? (reps Γ) (binds Θ)
morphWf? Γ Θ | just wΓ | nothing = nothing
morphWf? Γ Θ | just wΓ | just bs with interior? Γ Θ
morphWf? Γ Θ | just wΓ | just bs | nothing = nothing
morphWf? Γ Θ | just wΓ | just bs | just (Γᵢ , int) with conversion? Γ Θ
morphWf? Γ Θ | just wΓ | just bs | just (Γᵢ , int) | nothing = nothing
morphWf? Γ Θ | just wΓ | just bs | just (Γᵢ , int) | just (Γᶜ , cnv) =
  just (Γᵢ , Γᶜ , mw wΓ bs int cnv)

------------------------------------------------------------------------
-- 6. Strengthening: the inverse of `shiftRep`
------------------------------------------------------------------------

-- `extN k suc` is the identity below k and `suc` at or above it, so its
-- image misses exactly k.  Inverting it is what lets an exterior type be
-- INFERRED from a conversion's target, which `env` presents through the
-- morphism's representation-bind prefix.
strVar : (k X : ℕ) → Maybe (∃[ Y ] extN k suc Y ≡ X)
strVar zero    zero    = nothing
strVar zero    (suc X) = just (X , refl)
strVar (suc k) zero    = just (zero , refl)
strVar (suc k) (suc X) with strVar k X
strVar (suc k) (suc X) | just (Y , eq) = just (suc Y , cong suc eq)
strVar (suc k) (suc X) | nothing       = nothing

strAt : (k : ℕ) (S : Ty)
  → Maybe (∃[ R ] renameᵗ (extN k suc) R ≡ S)
strAt k (` X) with strVar k X
strAt k (` X) | just (Y , eq) = just (` Y , cong `_ eq)
strAt k (` X) | nothing       = nothing
strAt k `ℕ = just (`ℕ , refl)
strAt k `𝔹 = just (`𝔹 , refl)
strAt k (A ⇒ B) with strAt k A
strAt k (A ⇒ B) | nothing = nothing
strAt k (A ⇒ B) | just (A′ , eqA) with strAt k B
strAt k (A ⇒ B) | just (A′ , eqA) | just (B′ , eqB) =
  just (A′ ⇒ B′ , cong₂ _⇒_ eqA eqB)
strAt k (A ⇒ B) | just (A′ , eqA) | nothing = nothing
strAt k (`∀ A) with strAt (suc k) A
strAt k (`∀ A) | just (A′ , eq) = just (`∀ A′ , cong `∀ eq)
strAt k (`∀ A) | nothing        = nothing

unshiftRep : (n : ℕ) (S : Ty) → Maybe (∃[ R ] shiftRep n R ≡ S)
unshiftRep zero    S = just (S , refl)
unshiftRep (suc n) S with strAt zero S
unshiftRep (suc n) S | nothing = nothing
unshiftRep (suc n) S | just (S′ , eq) with unshiftRep n S′
unshiftRep (suc n) S | just (S′ , eq) | just (R , eq′) =
  just (R , trans (cong ⇑ᵗ eq′) eq)
unshiftRep (suc n) S | just (S′ , eq) | nothing = nothing

------------------------------------------------------------------------
-- 7. Reading types between the two universes
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
read? η (`∀ A) with read? (zero ∷ shiftNames η) A
read? η (`∀ A) | just (R , p) = just (`∀ R , same-∀ p)
read? η (`∀ A) | nothing      = nothing

-- Backward: the ordinary spelling a representation type has under a given
-- name map, if it has one.
unread? : (η : TyCtx) (R : Ty) → Maybe (∃[ A ] η ⊢ A ~ R)
unread? η (` α) with find? η α
unread? η (` α) | just (X , d) = just (` X , same-var d)
unread? η (` α) | nothing      = nothing
unread? η `ℕ = just (`ℕ , same-ℕ)
unread? η `𝔹 = just (`𝔹 , same-𝔹)
unread? η (R ⇒ S) with unread? η R
unread? η (R ⇒ S) | nothing = nothing
unread? η (R ⇒ S) | just (A , p) with unread? η S
unread? η (R ⇒ S) | just (A , p) | just (B , q) =
  just (A ⇒ B , same-⇒ p q)
unread? η (R ⇒ S) | just (A , p) | nothing = nothing
unread? η (`∀ R) with unread? (zero ∷ shiftNames η) R
unread? η (`∀ R) | just (A , p) = just (`∀ A , same-∀ p)
unread? η (`∀ R) | nothing      = nothing

-- RE-BASING.  `A` is read on the name map `η`; this finds its spelling on
-- `η′`, together with the `_⊢_≈_⊣_` that relates them.  It goes
-- through the
-- REPRESENTATION, which is the only route there is: the two maps can
-- reorder relative to each other, so no arithmetic on positions would do
-- (notes/ForallPayloadWall §3).  It is partial, because `η′` need not name
-- everything `η` does — which is why the rules that cross carry this as a
-- premise rather than computing it.
rebase? : (η η′ : TyCtx) (A : Ty)
  → Maybe (∃[ A′ ] (∃[ R ] ((η′ ⊢ A′ ~ R) × (η ⊢ A ~ R))))
rebase? η η′ A with read? η A
rebase? η η′ A | nothing = nothing
rebase? η η′ A | just (R , q) with unread? η′ R
rebase? η η′ A | just (R , q) | just (A′ , p) = just (A′ , R , p , q)
rebase? η η′ A | just (R , q) | nothing = nothing

-- THE SAME THING FOR A CONVERSION, which is what `Peel` needs.  A
-- conversion mentions ordinary names at three leaves only, so both
-- directions are `read?`/`unread?` with those three cases added.
readᶜ? : (η : TyCtx) (s : Conv) → Maybe (∃[ r ] η ⊩ s ~ r)
readᶜ? η (id A) with read? η A
readᶜ? η (id A) | just (R , p) = just (id R , sameᶜ-id p)
readᶜ? η (id A) | nothing      = nothing
readᶜ? η (seal X) with lookupˡ? η X
readᶜ? η (seal X) | just (α , d) = just (seal α , sameᶜ-seal d)
readᶜ? η (seal X) | nothing      = nothing
readᶜ? η (unseal X) with lookupˡ? η X
readᶜ? η (unseal X) | just (α , d) = just (unseal α , sameᶜ-unseal d)
readᶜ? η (unseal X) | nothing      = nothing
readᶜ? η (s ↦ t) with readᶜ? η s
readᶜ? η (s ↦ t) | nothing = nothing
readᶜ? η (s ↦ t) | just (r , p) with readᶜ? η t
readᶜ? η (s ↦ t) | just (r , p) | just (u , q) =
  just (r ↦ u , sameᶜ-fun p q)
readᶜ? η (s ↦ t) | just (r , p) | nothing = nothing
readᶜ? η (`∀ s) with readᶜ? (zero ∷ shiftNames η) s
readᶜ? η (`∀ s) | just (r , p) = just (`∀ r , sameᶜ-all p)
readᶜ? η (`∀ s) | nothing      = nothing

unreadᶜ? : (η : TyCtx) (r : Conv) → Maybe (∃[ s ] η ⊩ s ~ r)
unreadᶜ? η (id R) with unread? η R
unreadᶜ? η (id R) | just (A , p) = just (id A , sameᶜ-id p)
unreadᶜ? η (id R) | nothing      = nothing
unreadᶜ? η (seal α) with find? η α
unreadᶜ? η (seal α) | just (X , d) = just (seal X , sameᶜ-seal d)
unreadᶜ? η (seal α) | nothing      = nothing
unreadᶜ? η (unseal α) with find? η α
unreadᶜ? η (unseal α) | just (X , d) = just (unseal X , sameᶜ-unseal d)
unreadᶜ? η (unseal α) | nothing      = nothing
unreadᶜ? η (r ↦ u) with unreadᶜ? η r
unreadᶜ? η (r ↦ u) | nothing = nothing
unreadᶜ? η (r ↦ u) | just (s , p) with unreadᶜ? η u
unreadᶜ? η (r ↦ u) | just (s , p) | just (t , q) =
  just (s ↦ t , sameᶜ-fun p q)
unreadᶜ? η (r ↦ u) | just (s , p) | nothing = nothing
unreadᶜ? η (`∀ r) with unreadᶜ? (zero ∷ shiftNames η) r
unreadᶜ? η (`∀ r) | just (s , p) = just (`∀ s , sameᶜ-all p)
unreadᶜ? η (`∀ r) | nothing      = nothing

-- `respell? η η′ s` is `rebase?` one universe up: `s` is read on η, and
-- this finds its spelling on η′ with the `SameConv` that relates them.
respell? : (η η′ : TyCtx) (s : Conv)
  → Maybe (∃[ s′ ] (∃[ r ] ((η′ ⊩ s′ ~ r) × (η ⊩ s ~ r))))
respell? η η′ s with readᶜ? η s
respell? η η′ s | nothing = nothing
respell? η η′ s | just (r , q) with unreadᶜ? η′ r
respell? η η′ s | just (r , q) | just (s′ , p) = just (s′ , r , p , q)
respell? η η′ s | just (r , q) | nothing = nothing

sameTy? : (Γ Γ′ : Ctxᵗ) (A B : Ty) → Maybe (Γ ⊢ A ≈ B ⊣ Γ′)
sameTy? Γ Γ′ A B with read? (names Γ) A
sameTy? Γ Γ′ A B | nothing = nothing
sameTy? Γ Γ′ A B | just (R , p) with read? (names Γ′) B
sameTy? Γ Γ′ A B | just (R , p) | nothing = nothing
sameTy? Γ Γ′ A B | just (R , p) | just (S , q) with R ≟Ty S
sameTy? Γ Γ′ A B | just (R , p) | just (S , q) | just refl =
  just (R , p , q)
sameTy? Γ Γ′ A B | just (R , p) | just (S , q) | nothing = nothing

-- `env`'s exterior premise, read from the conversion's TARGET.  The
-- conversion context sees the type across Θ's representation-bind prefix,
-- so recovering the exterior spelling strengthens by `numBinds Θ` first.
SameExtResult : ℕ → Ctxᵗ → Ctxᵗ → Ty → Set
SameExtResult n Γ Γ′ Cₑ = Σ[ Bₑ ∈ Ty ] SameTyExt n Γ Bₑ Γ′ Cₑ

sameTyExt? : (n : ℕ) (Γ Γ′ : Ctxᵗ) (Cₑ : Ty)
  → Maybe (SameExtResult n Γ Γ′ Cₑ)
sameTyExt? n Γ Γ′ Cₑ with read? (names Γ′) Cₑ
sameTyExt? n Γ Γ′ Cₑ | nothing = nothing
sameTyExt? n Γ Γ′ Cₑ | just (S , q) with unshiftRep n S
sameTyExt? n Γ Γ′ Cₑ | just (S , q) | nothing = nothing
sameTyExt? n Γ Γ′ Cₑ | just (S , q) | just (R , eq) with unread? (names Γ) R
sameTyExt? n Γ Γ′ Cₑ | just (S , q) | just (R , eq) | nothing = nothing
sameTyExt? n Γ Γ′ Cₑ | just (S , q) | just (R , eq) | just (Bₑ , p) =
  just (Bₑ , R , p , subst (names Γ′ ⊢ Cₑ ~_) (sym eq) q)

------------------------------------------------------------------------
-- 8. The lookup square, type formation, and conversions
------------------------------------------------------------------------

lookupʳ? : (Ξ : RepCtx) (α : RVar) → Maybe (∃[ b ] Ξ ∋ʳ α := b)
lookupʳ? []            α       = nothing
lookupʳ? (b ∷ Ξ)       zero    = just (renRepBinding suc b , r-here)
lookupʳ? (bindR R ∷ Ξ) (suc α) with lookupʳ? Ξ α
lookupʳ? (bindR R ∷ Ξ) (suc α) | just (b , d) =
  just (renRepBinding suc b , r-there d)
lookupʳ? (bindR R ∷ Ξ) (suc α) | nothing = nothing
lookupʳ? (abstR ∷ Ξ)   (suc α) with lookupʳ? Ξ α
lookupʳ? (abstR ∷ Ξ)   (suc α) | just (b , d) =
  just (renRepBinding suc b , r-there-abst d)
lookupʳ? (abstR ∷ Ξ)   (suc α) | nothing = nothing

∋:=? : (Γ : Ctxᵗ) (X : ℕ) → Maybe (∃[ A ] Γ ∋ X := A)
∋:=? Γ X with lookupˡ? (names Γ) X
∋:=? Γ X | nothing = nothing
∋:=? Γ X | just (α , nm) with lookupʳ? (reps Γ) α
∋:=? Γ X | just (α , nm) | nothing = nothing
∋:=? Γ X | just (α , nm) | just (abstR , rp) = nothing
∋:=? Γ X | just (α , nm) | just (bindR R , rp) with unread? (names Γ) R
∋:=? Γ X | just (α , nm) | just (bindR R , rp) | nothing = nothing
∋:=? Γ X | just (α , nm) | just (bindR R , rp) | just (A , sm) =
  just (A , α , R , nm , rp , sm)

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
-- by name from the conversion context (strong.Conversion §5).
ConvResult : Ctxᵗ → Conv → Set
ConvResult Γ c = Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Γ ⊢ c ∶ A ⇝ B

convTy? : (Γ : Ctxᵗ) (c : Conv) → Maybe (ConvResult Γ c)
convTy? Γ (id (` X)) with ∋tv? Γ X
convTy? Γ (id (` X)) | just tv = just (` X , ` X , conv-idv tv)
convTy? Γ (id (` X)) | nothing = nothing
convTy? Γ (id `ℕ) = just (`ℕ , `ℕ , conv-id base-ℕ)
convTy? Γ (id `𝔹) = just (`𝔹 , `𝔹 , conv-id base-𝔹)
convTy? Γ (id (A ⇒ B)) = nothing
convTy? Γ (id (`∀ A)) = nothing
convTy? Γ (seal X) with ∋:=? Γ X
convTy? Γ (seal X) | just (A , d) = just (A , ` X , conv-seal d)
convTy? Γ (seal X) | nothing      = nothing
convTy? Γ (unseal X) with ∋:=? Γ X
convTy? Γ (unseal X) | just (A , d) = just (` X , A , conv-unseal d)
convTy? Γ (unseal X) | nothing      = nothing
convTy? Γ (s ↦ t) with convTy? Γ s
convTy? Γ (s ↦ t) | nothing = nothing
convTy? Γ (s ↦ t) | just (A′ , A , ⊢s) with convTy? Γ t
convTy? Γ (s ↦ t) | just (A′ , A , ⊢s) | just (B , B′ , ⊢t) =
  just (A ⇒ B , A′ ⇒ B′ , conv-fun ⊢s ⊢t)
convTy? Γ (s ↦ t) | just (A′ , A , ⊢s) | nothing = nothing
convTy? Γ (`∀ s) with convTy? (underΛ Γ) s
convTy? Γ (`∀ s) | just (A , B , ⊢s) = just (`∀ A , `∀ B , conv-all ⊢s)
convTy? Γ (`∀ s) | nothing = nothing

------------------------------------------------------------------------
-- 9. Term typing
------------------------------------------------------------------------

lookupTm? : (Γ : Ctx) (x : Var) → Maybe (∃[ A ] Γ ∋ x ⦂ A)
lookupTm? []      x       = nothing
lookupTm? (A ∷ Γ) zero    = just (A , here)
lookupTm? (A ∷ Γ) (suc x) with lookupTm? Γ x
lookupTm? (A ∷ Γ) (suc x) | just (B , d) = just (B , there d)
lookupTm? (A ∷ Γ) (suc x) | nothing      = nothing

InferResult : Ctxᵗ → Ctx → Term → Set
InferResult Δ Γ M = Σ[ A ∈ Ty ] Δ ∣ Γ ⊢ M ⦂ A

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
infer Δ Γ (Λ N) with infer (underΛ Δ) (⤊ Γ) N
infer Δ Γ (Λ N) | just (C , ⊢N) = just (`∀ C , ⊢Λ ⊢N)
infer Δ Γ (Λ N) | nothing = nothing
infer Δ Γ (L ·[ B , A ]) with wfTy? Δ A
infer Δ Γ (L ·[ B , A ]) | nothing = nothing
infer Δ Γ (L ·[ B , A ]) | just wA with infer Δ Γ L
infer Δ Γ (L ·[ B , A ]) | just wA | nothing = nothing
infer Δ Γ (L ·[ B , A ]) | just wA | just (` X , ⊢L) = nothing
infer Δ Γ (L ·[ B , A ]) | just wA | just (`ℕ , ⊢L) = nothing
infer Δ Γ (L ·[ B , A ]) | just wA | just (`𝔹 , ⊢L) = nothing
infer Δ Γ (L ·[ B , A ]) | just wA | just (C ⇒ D , ⊢L) = nothing
infer Δ Γ (L ·[ B , A ]) | just wA | just (`∀ C , ⊢L) with C ≟Ty B
infer Δ Γ (L ·[ B , A ]) | just wA | just (`∀ C , ⊢L) | just refl =
  just (B [ A ]ᵗ , ⊢·[] ⊢L wA)
infer Δ Γ (L ·[ B , A ]) | just wA | just (`∀ C , ⊢L) | nothing =
  nothing
-- The boundary.  `env`'s mechanical premises come from §5; its three
-- informative ones are the interior term's type, the conversion's two
-- types, and the two readings that relate them.
infer Δ Γ (M ⟪ Θ , c ⟫) with morphWf? Δ Θ
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
  with sameTyExt? (numBinds Θ) Δ Δᶜ Cₑ
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
-- 10. Checking a term against a stated type
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
-- 11. Forcing a checker
------------------------------------------------------------------------

-- `IsJ m` is the unit RECORD when the checker succeeded, so Agda solves a
-- hidden argument of that type by eta on its own.  A checker whose inputs
-- are all determined by the goal therefore needs no arguments written at
-- all: `tc` below IS a typing derivation.
--
-- HOW A FAILURE LOOKS.  When the checker says `nothing` the hidden
-- argument's type is `⊥`, which nothing solves, so Agda reports an
-- UNSOLVED META at the `tc`.  That is a rejection, not an acceptance —
-- `--no-allow-unsolved-metas` (and `make check`) turn it into an error —
-- but it does not say WHY.  To see why, replace `tc` by
-- `proj₂ (ty! Δ Γ M)`, which reports the type the checker did infer, or
-- call the failing sub-checker directly.
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

-- The name-uniqueness side condition that `CancelR`, `IdPush` and both
-- `TyPeelR` clauses carry.
tu : ∀ {Δ} {w : IsJ (unique? Δ)} → Unique Δ
tu {Δ} {w} = force (unique? Δ) w

-- A type's well-formedness.
tf : ∀ {Γ A} {w : IsJ (wfTy? Γ A)} → Γ ⊢ᵗ A
tf {Γ} {A} {w} = force (wfTy? Γ A) w

-- The reading that relates an ordinary type to its representation, which
-- `TyBeta` and both `TyPeelR` clauses carry as `Δ ⊢ᶜ A ~ R`.
tr : ∀ {η A R} {w : IsJ (check~ η A R)} → η ⊢ A ~ R
tr {η} {A} {R} {w} = force (check~ η A R) w

-- `from-just` turns a checker into what it found; the caller's type
-- signature is what pins the answer, because a different one does not
-- typecheck.  These are used where the answer is an OUTPUT the goal does
-- not already fix — a morphism's induced contexts, a lookup's type.
int! : (Γ : Ctxᵗ) (Θ : CtxMorph) → From-just (interior? Γ Θ)
int! Γ Θ = from-just (interior? Γ Θ)

conv! : (Γ : Ctxᵗ) (Θ : CtxMorph) → From-just (conversion? Γ Θ)
conv! Γ Θ = from-just (conversion? Γ Θ)

mw! : (Γ : Ctxᵗ) (Θ : CtxMorph) → From-just (morphWf? Γ Θ)
mw! Γ Θ = from-just (morphWf? Γ Θ)

wf! : (Γ : Ctxᵗ) → From-just (wfCtx? Γ)
wf! Γ = from-just (wfCtx? Γ)

-- The lookup square.  `CancelR` and `IdPush` need the INFERRING form:
-- their contracta mention the looked-up type only under `mkId`, which the
-- unifier cannot invert, so the rules' `A` is fixed by this premise and by
-- nothing else.
sq! : (Γ : Ctxᵗ) (X : ℕ) → From-just (∋:=? Γ X)
sq! Γ X = from-just (∋:=? Γ X)

tv! : (Γ : Ctxᵗ) (X : ℕ) → From-just (∋tv? Γ X)
tv! Γ X = from-just (∋tv? Γ X)

cv! : (Γ : Ctxᵗ) (c : Conv) → From-just (convTy? Γ c)
cv! Γ c = from-just (convTy? Γ c)

ty! : (Δ : Ctxᵗ) (Γ : Ctx) (M : Term) → From-just (infer Δ Γ M)
ty! Δ Γ M = from-just (infer Δ Γ M)
