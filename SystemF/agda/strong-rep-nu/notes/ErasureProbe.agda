module strong-rep-nu.notes.ErasureProbe where

-- File Charter:
--   * THE ERASURE FROM THE RUN-TIME LANGUAGE TO THE SOURCE LANGUAGE,
--     ITS THEOREM STATEMENTS, AND CHECKS OF THEM ON RUNS.  Design and
--     decision points: notes/ErasureSketch.md.
--     §1 what a representation variable DENOTES (`env`), read through
--     the store, and the source count (`countAbs`); §2 the erasure of
--     types (`nameσ`, `eraseTy`); §3 the interior name map, computed
--     (`interiorⁿ`, `inside`), and its agreement with `_⊢ⁱ_⇒_`
--     (`inside-sound`); §4 the erasure of terms (`erase`); §5 the
--     STATEMENTS, as `Set`s, unproved: `ErasureTyping`,
--     `ErasureSimulation`, `ErasureSimulationExact`, `ErasureRun`,
--     `ErasureReflection`, `CompiledRunErases`; §6 `EraseCompileAt`
--     and `EraseCompile`, PROVED; §7 the example checks, by `refl`.
--   * NO POSTULATES.  Typing and simulation are STATED, not proved
--     (Jeremy's rule: statements are reviewed before proofs).
--   * ERASURE IS A FUNCTION OF (Δ, M), not of a typing derivation:
--     the context carries the name map and the store, which is all
--     an ordinary type variable needs to be resolved.

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_)
open import Data.String using (String)
import Data.Nat.Show
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary
  using (Change; unbind; bind; Boundary; _∣_⊢δ_⇒_; step-unbind;
         step-bind; _∣_⊢χ_⇒_; changes[]; changes∷; _⊢ⁱ_⇒_; interior)
open import strong-rep-nu.Terms
  using (Term; Ctx; `_; $_; `true; `false; ƛ_∙_; _·_; Λ_; ν_·_⟨_⟩;
         _⟪_,_⟫; _∣_⊢_⦂_)
open import strong-rep-nu.Reduction
open import strong-rep-nu.Eval using (step)
open import strong-rep-nu.Show using (ruleName; tyBinder; tmBinder; nthS)
open import strong-rep-nu.Source
  using (STerm; `_; $_; `true; `false; ƛ_∙_; _·_; Λ_; _[_];
         _∣_⊢ˢ_⦂_; ⊢ˢ`; ⊢ˢ$; ⊢ˢtrue; ⊢ˢfalse; ⊢ˢƛ; ⊢ˢ·; ⊢ˢΛ; ⊢ˢ[];
         inferˢ)
open import strong-rep-nu.Compile using (compile)
open import strong-rep-nu.Conversion using (⌞_⌟; id)
open import strong-rep-nu.notes.SourceReduction
open import strong-rep-nu.proof.TypeSubst using (subst-cong; subst-id)
import strong-rep-nu.Examples as E
import strong-rep-nu.SourceExamples as SE

------------------------------------------------------------------------
-- 1. What a representation variable denotes
------------------------------------------------------------------------

-- `env Ξ α` is the SOURCE type the representation variable α denotes
-- at the store Ξ.  An abstract cell (created by a `Λ`) denotes a source
-- type variable, numbered by how many abstract cells are NEWER than it;
-- a concrete cell `bindR R` denotes its payload, itself erased at the
-- store BELOW it (a payload is read outside its own binder), so an ALIAS
-- cell `β := γ` denotes whatever γ denotes.  A payload's own `∀`s are
-- handled by `substᵗ`'s `extsᵗ`, which is exactly the mixed reading
-- `_⊢ᴿ[_]_` (local index i < n, free index n + α).
env : RepCtx → Substᵗ
env []            = `_                       -- junk: never read at WfCtx
env (abstR ∷ Ξ)   = ` 0 •ᵗ (λ α → ⇑ᵗ (env Ξ α))
env (bindR R ∷ Ξ) = substᵗ (env Ξ) R •ᵗ env Ξ

-- the number of source type variables in scope: the abstract cells
countAbs : RepCtx → ℕ
countAbs []            = zero
countAbs (abstR ∷ Ξ)   = suc (countAbs Ξ)
countAbs (bindR R ∷ Ξ) = countAbs Ξ

------------------------------------------------------------------------
-- 2. Erasing a type
------------------------------------------------------------------------

lookupⁿ : TyCtx → ℕ → Maybe RVar
lookupⁿ []      X       = nothing
lookupⁿ (α ∷ η) zero    = just α
lookupⁿ (α ∷ η) (suc X) = lookupⁿ η X

-- an ordinary variable with no name-map entry erases to ITSELF (junk,
-- never reached on a well-formed type; it makes `EraseCompile`
-- unconditional)
resolve : RepCtx → ℕ → Maybe RVar → Ty
resolve Ξ X (just α) = env Ξ α
resolve Ξ X nothing  = ` X

-- what each ordinary type variable of Δ denotes: follow the name map
-- to a representation variable, then the store
nameσ : Ctxᵗ → Substᵗ
nameσ Δ X = resolve (reps Δ) X (lookupⁿ (names Δ) X)

-- ⌊ A ⌋ at Δ
eraseTy : Ctxᵗ → Ty → Ty
eraseTy Δ A = substᵗ (nameσ Δ) A

eraseCtx : Ctxᵗ → Ctx → Ctx
eraseCtx Δ Γ = map (eraseTy Δ) Γ

------------------------------------------------------------------------
-- 3. The interior name map, computed
------------------------------------------------------------------------

deleteAt : ℕ → TyCtx → TyCtx
deleteAt k       []       = []
deleteAt zero    (α ∷ αs) = αs
deleteAt (suc k) (α ∷ αs) = α ∷ deleteAt k αs

insertAt : ℕ → RVar → TyCtx → TyCtx
insertAt zero    β αs       = β ∷ αs
insertAt (suc k) β []       = β ∷ []
insertAt (suc k) β (α ∷ αs) = α ∷ insertAt k β αs

act : Change → TyCtx → TyCtx
act (unbind X α) η = deleteAt X η
act (bind X α)   η = insertAt X α η

-- head-LAST, as in `_∣_⊢χ_⇒_`: the tail acts first
interiorⁿ : Boundary → TyCtx → TyCtx
interiorⁿ []      η = η
interiorⁿ (δ ∷ Θ) η = act δ (interiorⁿ Θ η)

-- the context a boundary's body is erased at: same store, interior names
inside : Ctxᵗ → Boundary → Ctxᵗ
inside Δ Θ = reps Δ ∣ interiorⁿ Θ (names Δ)

-- the computed interior IS the relational one
private
  delete-sound : ∀ {α η X η′} → α ⊢- η at X ⇒ η′ → deleteAt X η ≡ η′
  delete-sound del-here      = refl
  delete-sound (del-there d) = cong (_ ∷_) (delete-sound d)

  insert-sound : ∀ {α η X η′} → α ⊢+ η at X ⇒ η′ → insertAt X α η ≡ η′
  insert-sound ins-here      = refl
  insert-sound (ins-there i) = cong (_ ∷_) (insert-sound i)

  act-sound : ∀ {Ξ η δ η′} → Ξ ∣ η ⊢δ δ ⇒ η′ → act δ η ≡ η′
  act-sound (step-unbind v d f) = delete-sound d
  act-sound (step-bind v f i)   = insert-sound i

  changes-sound : ∀ {Ξ η Θ η′} → Ξ ∣ η ⊢χ Θ ⇒ η′ → interiorⁿ Θ η ≡ η′
  changes-sound changes[] = refl
  changes-sound (changes∷ {δ = δ} cs st) =
    trans (cong (act δ) (changes-sound cs)) (act-sound st)

inside-sound : ∀ {Δ Θ Δᵢ} → Δ ⊢ⁱ Θ ⇒ Δᵢ → inside Δ Θ ≡ Δᵢ
inside-sound (interior cs) = cong (_ ∣_) (changes-sound cs)

------------------------------------------------------------------------
-- 4. Erasing a term
------------------------------------------------------------------------

-- ⌊ M ⌋ at Δ.  Boundaries and conversions vanish, but a boundary's body
-- is erased at ITS OWN context `inside Δ Θ`; `ν A · L ⟨ c ⟩` becomes the
-- source type application `⌊L⌋ [ ⌊A⌋ ]`; `Λ` erases its body at
-- `underΛ Δ`, whose new abstract cell is source variable 0.
erase : Ctxᵗ → Term → STerm
erase Δ (` x)           = ` x
erase Δ ($ n)           = $ n
erase Δ `true           = `true
erase Δ `false          = `false
erase Δ (ƛ A ∙ N)       = ƛ eraseTy Δ A ∙ erase Δ N
erase Δ (L · M)         = erase Δ L · erase Δ M
erase Δ (Λ N)           = Λ (erase (underΛ Δ) N)
erase Δ (ν A · L ⟨ c ⟩) = erase Δ L [ eraseTy Δ A ]
erase Δ (M ⟪ Θ , c ⟫)   = erase (inside Δ Θ) M

------------------------------------------------------------------------
-- 5. The statements (NOT proved here)
------------------------------------------------------------------------

-- TYPING.  Erasure preserves typing, at the erased type, over the count
-- of abstract cells.
ErasureTyping : Set
ErasureTyping = ∀ {Δ Γ M A}
  → WfCtx Δ
  → Δ ∣ Γ ⊢ M ⦂ A
    ------------------------------------------------------------
  → countAbs (reps Δ) ∣ eraseCtx Δ Γ ⊢ˢ erase Δ M ⦂ eraseTy Δ A

-- SIMULATION (Blame for All, Prop. 1).  The contractum is erased at the
-- context it lives at, `apply δ Δ`.
ErasureSimulation : Set
ErasureSimulation = ∀ {Δ M M′ A δ}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
    --------------------------------------------------------------
  → (erase Δ M ≡ erase (apply δ Δ) M′)
    ⊎ (erase Δ M ⟶ˢ erase (apply δ Δ) M′)

-- WHICH disjunct, by rule: the boundary rules stutter, the three
-- β-rules take exactly one source step.  (Implies ErasureSimulation.)
data Link : Set where
  same : Link     -- the two erasures are equal
  src  : Link     -- the second is the source step of the first
  bad  : Link     -- neither (only produced by the checker below)

ruleKind : ∀ {Δ M M′ δ} → Δ ⊢ M -→ M′ ∣ δ → Link
ruleKind (TyBeta v a)                       = src
ruleKind (Beta w)                           = src
ruleKind (Wrap v w r₁ r₂ r₃ sc)             = same
ruleKind (TyWrap v r s a)                   = src
ruleKind (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂)   = same
ruleKind (Id u b)                           = same
ruleKind (ξ-·₁ st)                          = ruleKind st
ruleKind (ξ-·₂ v st)                        = ruleKind st
ruleKind (ξ-ν st)                           = ruleKind st
ruleKind (ξ-⟪⟫ r st)                        = ruleKind st

Matches : Link → STerm → STerm → Set
Matches same M N = M ≡ N
Matches src  M N = M ⟶ˢ N
Matches bad  M N = M ≡ N    -- unreachable: ruleKind never says bad

ErasureSimulationExact : Set
ErasureSimulationExact = ∀ {Δ M M′ A δ}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→ M′ ∣ δ)
    ---------------------------------------------------
  → Matches (ruleKind r) (erase Δ M) (erase (apply δ Δ) M′)

-- RUNS.  (From ErasureSimulation and preservation.)
ErasureRun : Set
ErasureRun = ∀ {Δ M N A}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→* N)
    ----------------------------------
  → erase Δ M ⟶ˢ* erase (runCtx r) N

-- REFLECTION (the converse; not in BfA).  Every source step of the
-- erasure is matched by a finite run, stutters then one β-rule.  It
-- needs the stutter rules (Wrap, Merge, Id) to terminate.
ErasureReflection : Set
ErasureReflection = ∀ {Δ M A N}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → erase Δ M ⟶ˢ N
    -------------------------------------------------------------
  → ∃[ M′ ] Σ[ r ∈ Δ ⊢ M -→* M′ ] (erase (runCtx r) M′ ≡ N)

-- A compiled program's run is its own source run, with stutters.
-- (From EraseCompile and ErasureRun.)
CompiledRunErases : Set
CompiledRunErases = ∀ {M A N}
  → (d : 0 ∣ [] ⊢ˢ M ⦂ A)
  → (r : empty ⊢ compile d -→* N)
    ------------------------------
  → M ⟶ˢ* erase (runCtx r) N

------------------------------------------------------------------------
-- 6. Compile then erase — PROVED
------------------------------------------------------------------------

-- the context whose n ordinary names denote the n source variables
idCtx : ℕ → Ctxᵗ
idCtx zero    = empty
idCtx (suc n) = underΛ (idCtx n)

-- AT ANY CONTEXT: erasing the compiled term replaces each type variable
-- by what the context says it denotes.
EraseCompileAt : Set
EraseCompileAt = ∀ (Δ : Ctxᵗ) {n Γ M A} (d : n ∣ Γ ⊢ˢ M ⦂ A)
  → erase Δ (compile d) ≡ substˢᵗ (nameσ Δ) M

EraseCompile : Set
EraseCompile = ∀ {n Γ M A} (d : n ∣ Γ ⊢ˢ M ⦂ A)
  → erase (idCtx n) (compile d) ≡ M

private
  lookupⁿ-suc : ∀ η X
    → lookupⁿ (map suc η) X ≡ Maybe.map suc (lookupⁿ η X)
  lookupⁿ-suc []      X       = refl
  lookupⁿ-suc (α ∷ η) zero    = refl
  lookupⁿ-suc (α ∷ η) (suc X) = lookupⁿ-suc η X

  resolve-abs : ∀ Ξ X m
    → resolve (abstR ∷ Ξ) (suc X) (Maybe.map suc m) ≡ ⇑ᵗ (resolve Ξ X m)
  resolve-abs Ξ X (just α) = refl
  resolve-abs Ξ X nothing  = refl

-- the name map under Λ denotes the extended substitution
nameσ-underΛ : ∀ Δ X → nameσ (underΛ Δ) X ≡ extsᵗ (nameσ Δ) X
nameσ-underΛ (Ξ ∣ η) zero    = refl
nameσ-underΛ (Ξ ∣ η) (suc X) =
  trans (cong (resolve (abstR ∷ Ξ) (suc X)) (lookupⁿ-suc η X))
        (resolve-abs Ξ X (lookupⁿ η X))

substˢᵗ-cong : ∀ {σ τ : Substᵗ} → (∀ X → σ X ≡ τ X)
  → ∀ M → substˢᵗ σ M ≡ substˢᵗ τ M
substˢᵗ-cong h (` x)     = refl
substˢᵗ-cong h ($ k)     = refl
substˢᵗ-cong h `true     = refl
substˢᵗ-cong h `false    = refl
substˢᵗ-cong h (ƛ A ∙ N) =
  cong₂ ƛ_∙_ (subst-cong h A) (substˢᵗ-cong h N)
substˢᵗ-cong h (L · M)   = cong₂ _·_ (substˢᵗ-cong h L) (substˢᵗ-cong h M)
substˢᵗ-cong {σ} {τ} h (Λ N) = cong Λ_ (substˢᵗ-cong h-ext N)
  where
  h-ext : ∀ X → extsᵗ σ X ≡ extsᵗ τ X
  h-ext zero    = refl
  h-ext (suc X) = cong ⇑ᵗ (h X)
substˢᵗ-cong h (L [ A ]) = cong₂ _[_] (substˢᵗ-cong h L) (subst-cong h A)

substˢᵗ-id : ∀ {σ : Substᵗ} → (∀ X → σ X ≡ ` X) → ∀ M → substˢᵗ σ M ≡ M
substˢᵗ-id h (` x)     = refl
substˢᵗ-id h ($ k)     = refl
substˢᵗ-id h `true     = refl
substˢᵗ-id h `false    = refl
substˢᵗ-id h (ƛ A ∙ N) =
  cong₂ ƛ_∙_ (trans (subst-cong h A) (subst-id A)) (substˢᵗ-id h N)
substˢᵗ-id h (L · M)   = cong₂ _·_ (substˢᵗ-id h L) (substˢᵗ-id h M)
substˢᵗ-id {σ} h (Λ N) = cong Λ_ (substˢᵗ-id h-ext N)
  where
  h-ext : ∀ X → extsᵗ σ X ≡ ` X
  h-ext zero    = refl
  h-ext (suc X) = cong ⇑ᵗ (h X)
substˢᵗ-id h (L [ A ]) =
  cong₂ _[_] (substˢᵗ-id h L) (trans (subst-cong h A) (subst-id A))

erase-compile-at : EraseCompileAt
erase-compile-at Δ ⊢ˢ$ = refl
erase-compile-at Δ ⊢ˢtrue = refl
erase-compile-at Δ ⊢ˢfalse = refl
erase-compile-at Δ (⊢ˢ` x) = refl
erase-compile-at Δ (⊢ˢƛ wA d) =
  cong (ƛ_∙_ _) (erase-compile-at Δ d)
erase-compile-at Δ (⊢ˢ· d e) =
  cong₂ _·_ (erase-compile-at Δ d) (erase-compile-at Δ e)
erase-compile-at Δ (⊢ˢΛ {N = N} v d) =
  cong Λ_ (trans (erase-compile-at (underΛ Δ) d)
                 (substˢᵗ-cong (nameσ-underΛ Δ) N))
erase-compile-at Δ (⊢ˢ[] d wA) =
  cong (_[ _ ]) (erase-compile-at Δ d)

nameσ-idCtx : ∀ n X → nameσ (idCtx n) X ≡ ` X
nameσ-idCtx zero    X       = refl
nameσ-idCtx (suc n) zero    = refl
nameσ-idCtx (suc n) (suc X) =
  trans (nameσ-underΛ (idCtx n) (suc X)) (cong ⇑ᵗ (nameσ-idCtx n X))

erase-compile : EraseCompile
erase-compile {n} {M = M} d =
  trans (erase-compile-at (idCtx n) d) (substˢᵗ-id (nameσ-idCtx n) M)

------------------------------------------------------------------------
-- 7. The example checks
------------------------------------------------------------------------

-- 7a. Deciding what a checker needs: equality of types and terms.
_==ᵗ_ : Ty → Ty → Bool
(` X)   ==ᵗ (` Y)     = X ≡ᵇ Y
`ℕ      ==ᵗ `ℕ        = true
`𝔹      ==ᵗ `𝔹        = true
(A ⇒ B) ==ᵗ (A′ ⇒ B′) = (A ==ᵗ A′) ∧ (B ==ᵗ B′)
(`∀ A)  ==ᵗ (`∀ A′)   = A ==ᵗ A′
_       ==ᵗ _         = false

_==ˢ_ : STerm → STerm → Bool
(` x)     ==ˢ (` y)       = x ≡ᵇ y
($ k)     ==ˢ ($ j)       = k ≡ᵇ j
`true     ==ˢ `true       = true
`false    ==ˢ `false      = true
(ƛ A ∙ N) ==ˢ (ƛ A′ ∙ N′) = (A ==ᵗ A′) ∧ (N ==ˢ N′)
(L · M)   ==ˢ (L′ · M′)   = (L ==ˢ L′) ∧ (M ==ˢ M′)
(Λ N)     ==ˢ (Λ N′)      = N ==ˢ N′
(L [ A ]) ==ˢ (L′ [ A′ ]) = (L ==ˢ L′) ∧ (A ==ᵗ A′)
_         ==ˢ _           = false

-- how two consecutive erasures are related, as observed
link : STerm → STerm → Link
link M N with M ==ˢ N
link M N | true = same
link M N | false with stepToˢ M
link M N | false | nothing = bad
link M N | false | just M′ = if M′ ==ˢ N then src else bad

-- 7b. A run-time run, step by step: the rule, what `ruleKind` PREDICTS
-- (ErasureSimulationExact), and what the erasures SHOW.
record Row : Set where
  constructor row
  field
    rule      : String
    predicted : Link
    observed  : Link

rows : ℕ → Ctxᵗ → Term → List Row
rows zero    Δ M = []
rows (suc k) Δ M with step Δ M
rows (suc k) Δ M | nothing = []
rows (suc k) Δ M | just (M′ , δ , r) =
  row (ruleName r) (ruleKind r) (link (erase Δ M) (erase (apply δ Δ) M′))
    ∷ rows k (apply δ Δ) M′

-- the erased states of a run-time run
erasedRun : ℕ → Ctxᵗ → Term → List STerm
erasedRun zero    Δ M = erase Δ M ∷ []
erasedRun (suc k) Δ M with step Δ M
erasedRun (suc k) Δ M | nothing = erase Δ M ∷ []
erasedRun (suc k) Δ M | just (M′ , δ , r) =
  erase Δ M ∷ erasedRun k (apply δ Δ) M′

-- drop the stutters
collapse : List STerm → List STerm
collapse []       = []
collapse (M ∷ Ms) = M ∷ go M Ms
  where
  go : STerm → List STerm → List STerm
  go P []       = []
  go P (N ∷ Ns) = if P ==ˢ N then go P Ns else N ∷ go N Ns

linkEq : Link → Link → Bool
linkEq same same = true
linkEq src  src  = true
linkEq bad  bad  = true
linkEq _    _    = false

-- every step is related as its rule predicts, and none is `bad`
allAgree : List Row → Bool
allAgree []                  = true
allAgree (row n p bad ∷ rs)  = false
allAgree (row n p o ∷ rs)    = linkEq p o ∧ allAgree rs

-- every erased state is a closed source term of type A (ErasureTyping
-- at the empty ambient, where eraseTy is the identity on closed types)
typeOfˢ : STerm → Maybe Ty
typeOfˢ M = Maybe.map proj₁ (inferˢ 0 [] M)

allTyped : Ty → List STerm → Bool
allTyped A []       = true
allTyped A (M ∷ Ms) with typeOfˢ M
allTyped A (M ∷ Ms) | nothing = false
allTyped A (M ∷ Ms) | just B  = (A ==ᵗ B) ∧ allTyped A Ms

-- THE CHECK OF ONE RUN: (i) the rules agree with ErasureSimulationExact,
-- (ii) the erased run with its stutters dropped IS the source
-- evaluator's run from the source program, (iii) every erased state has
-- the program's type.
record RunChecks (k : ℕ) (M : Term) (S : STerm) (A : Ty) : Set where
  field
    agree    : allAgree (rows k empty M) ≡ true
    collapsed : collapse (erasedRun k empty M) ≡ runˢ k S
    typed    : allTyped A (erasedRun k empty M) ≡ true

-- 7c. Rendering a source term with names (for ErasureSketch.md, via
-- scripts/render_term.sh)
showTyˢ : List String → Ty → String
showTyˢ ns (` X)   = nthS ns X
showTyˢ ns `ℕ      = "ℕ"
showTyˢ ns `𝔹      = "𝔹"
showTyˢ ns (A ⇒ B) =
  Data.String._++_ "(" (Data.String._++_ (showTyˢ ns A)
    (Data.String._++_ "⇒" (Data.String._++_ (showTyˢ ns B) ")")))
showTyˢ ns (`∀ A)  =
  Data.String._++_ "(∀" (Data.String._++_ (tyBinder (Data.List.length ns))
    (Data.String._++_ ". "
      (Data.String._++_ (showTyˢ (tyBinder (Data.List.length ns) ∷ ns) A)
        ")")))

private
  infixr 5 _+++_
  _+++_ : String → String → String
  _+++_ = Data.String._++_

showS : List String → List String → STerm → String
showS ts xs (` x)     = nthS xs x
showS ts xs ($ k)     = Data.Nat.Show.show k
showS ts xs `true     = "true"
showS ts xs `false    = "false"
showS ts xs (ƛ A ∙ N) =
  "(λ" +++ tmBinder (Data.List.length xs) +++ ":" +++ showTyˢ ts A
    +++ ". " +++ showS ts (tmBinder (Data.List.length xs) ∷ xs) N +++ ")"
showS ts xs (L · M)   =
  "(" +++ showS ts xs L +++ " · " +++ showS ts xs M +++ ")"
showS ts xs (Λ N)     =
  "(Λ" +++ tyBinder (Data.List.length ts) +++ ". "
    +++ showS (tyBinder (Data.List.length ts) ∷ ts) xs N +++ ")"
showS ts xs (L [ A ]) = showS ts xs L +++ " [" +++ showTyˢ ts A +++ "]"

showRows : List Row → String
showRows [] = ""
showRows (row n p o ∷ rs) =
  n +++ ":" +++ showLink o +++ " " +++ showRows rs
  where
  showLink : Link → String
  showLink same = "="
  showLink src  = "→ˢ"
  showLink bad  = "BAD"

showErased : List STerm → String
showErased []       = ""
showErased (M ∷ []) = showS [] [] M
showErased (M ∷ Ms@(_ ∷ _)) = showS [] [] M +++ "\n  ~~>\n" +++ showErased Ms

-- 7d. THE REQUIRED RUNS AND AN ALIAS RUN, row by row.  A row is
-- `row rule predicted observed`: `predicted` is `ruleKind` of the step
-- `step` took, `observed` is `link` on the two erasures.  Every row
-- agrees: Wrap, Merge and Id stutter; TyBeta, TyWrap and Beta take
-- exactly one source step.

-- Examples §1a `P₀` = (ΛX. λx:X. x) [ℕ] · 7
P-rows : rows 25 empty E.P₀ ≡
    row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "Merge" same same ∷ row "Id" same same ∷ []
P-rows = refl

-- Examples §5a `E₀ᴮ`, the tower
Eᴮ-rows : rows 25 empty E.E₀ᴮ ≡
    row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "TyWrap" src src ∷ row "Merge" same same ∷ row "Wrap" same same
  ∷ row "Id" same same ∷ row "Beta" src src ∷ row "Merge" same same
  ∷ row "TyWrap" src src ∷ row "Merge" same same ∷ row "Merge" same same
  ∷ row "Wrap" same same ∷ row "Beta" src src ∷ row "Merge" same same
  ∷ row "Id" same same ∷ []
Eᴮ-rows = refl

-- Examples §7a `A₀` = (ΛX. λx:X. x) [ℕ⇒ℕ] · (λn:ℕ. n) · 7
A-rows : rows 25 empty E.A₀ ≡
    row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "Merge" same same ∷ row "Wrap" same same ∷ row "Id" same same
  ∷ row "Beta" src src ∷ row "Id" same same ∷ []
A-rows = refl

-- Examples §8 `S₀`: the alias cell β := γ, and the chained seals
S-rows : rows 25 empty E.S₀ ≡
    row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "TyWrap" src src ∷ row "Merge" same same ∷ row "Wrap" same same
  ∷ row "Beta" src src ∷ row "Merge" same same ∷ row "Merge" same same
  ∷ row "Merge" same same ∷ row "Merge" same same ∷ row "Id" same same
  ∷ []
S-rows = refl

-- Examples §2c `R₀`: a cell whose payload is another cell's variable
R-rows : rows 25 empty E.R₀ ≡
    row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Beta" src src
  ∷ row "TyBeta" src src ∷ row "Wrap" same same ∷ row "Merge" same same
  ∷ row "Beta" src src ∷ row "TyBeta" src src ∷ row "Wrap" same same
  ∷ row "Id" same same ∷ row "Beta" src src ∷ row "Merge" same same
  ∷ row "Merge" same same ∷ row "Merge" same same ∷ row "Merge" same same
  ∷ row "Id" same same ∷ []
R-rows = refl

-- 7e. ALL TWENTY COMPILED PROGRAMS (strong-rep-nu.SourceExamples): the
-- rows agree, the collapsed erased run IS the source run of the source
-- program, and every erased state has the program's type.
checks : ∀ {k M S A} → allAgree (rows k empty M) ≡ true
  → collapse (erasedRun k empty M) ≡ runˢ k S
  → allTyped A (erasedRun k empty M) ≡ true
  → RunChecks k M S A
checks a c t = record { agree = a ; collapsed = c ; typed = t }

P-checks : RunChecks 25 E.P₀ SE.P₀ `ℕ
P-checks = checks refl refl refl

K-checks : RunChecks 25 E.K₀ SE.K₀ `𝔹
K-checks = checks refl refl refl

J-checks : RunChecks 25 E.J₀ SE.J₀ `ℕ
J-checks = checks refl refl refl

F-checks : RunChecks 25 E.F₀ SE.F₀ `𝔹
F-checks = checks refl refl refl

U-checks : RunChecks 25 E.U₀ SE.U₀ `ℕ
U-checks = checks refl refl refl

Q-checks : RunChecks 25 E.Q₀ SE.Q₀ `ℕ
Q-checks = checks refl refl refl

D-checks : RunChecks 25 E.D₀ SE.D₀ `ℕ
D-checks = checks refl refl refl

L-checks : RunChecks 25 E.L₀ SE.L₀ `ℕ
L-checks = checks refl refl refl

R-checks : RunChecks 25 E.R₀ SE.R₀ `ℕ
R-checks = checks refl refl refl

G-checks : RunChecks 25 E.G₀ SE.G₀ `ℕ
G-checks = checks refl refl refl

H-checks : RunChecks 25 E.H₀ SE.H₀ `ℕ
H-checks = checks refl refl refl

E-checks : RunChecks 25 E.E₀ SE.E₀ (`∀ (`ℕ ⇒ (` 0 ⇒ ` 0)))
E-checks = checks refl refl refl

Eᴮ-checks : RunChecks 25 E.E₀ᴮ SE.E₀ᴮ `𝔹
Eᴮ-checks = checks refl refl refl

V-checks : RunChecks 25 E.V₀ SE.V₀ `𝔹
V-checks = checks refl refl refl

I-checks : RunChecks 25 E.I₀ SE.I₀ `𝔹
I-checks = checks refl refl refl

N-checks : RunChecks 25 E.N₀ SE.N₀ `ℕ
N-checks = checks refl refl refl

A-checks : RunChecks 25 E.A₀ SE.A₀ `ℕ
A-checks = checks refl refl refl

B-checks : RunChecks 25 E.B₀ SE.B₀ `ℕ
B-checks = checks refl refl refl

C-checks : RunChecks 25 E.C₀ SE.C₀ `ℕ
C-checks = checks refl refl refl

S-checks : RunChecks 25 E.S₀ SE.S₀ `ℕ
S-checks = checks refl refl refl

-- 7f. BEYOND THE COMPILED CORPUS.

-- Examples §10 `Bg`: Beta substitutes 7 UNDER a Λ, so the image crosses
-- in a wrapper `7 ⟪ ↓Z , id ℕ ⟫`; the erasure of the wrapper is the
-- source substitution's type-shifted image (here 7 itself).
Bgˢ : STerm
Bgˢ = ((ƛ `ℕ ∙ (Λ (ƛ `ℕ ∙ ` 1))) · $ 7) [ `ℕ ] · $ 0

Bg-rows : rows 25 empty E.Bg ≡
    row "Beta" src src ∷ row "TyBeta" src src ∷ row "Wrap" same same
  ∷ row "Id" same same ∷ row "Beta" src src ∷ row "Id" same same
  ∷ row "Id" same same ∷ []
Bg-rows = refl

Bg-checks : RunChecks 25 E.Bg Bgˢ `ℕ
Bg-checks = checks refl refl refl

-- Examples §9, at the NON-EMPTY ambient Δ₆ = (α := ℕ) ∣ (X ↦ α): the
-- hand-written seal/unseal layers all stutter, and the ambient name X
-- erases to ℕ.
Tcancel-rows : rows 25 E.Δ₆ E.Tcancel ≡
  row "Merge" same same ∷ row "Id" same same ∷ []
Tcancel-rows = refl

Tid₂-rows : rows 25 E.Δ₆ E.Tid₂ ≡
    row "Merge" same same ∷ row "Merge" same same ∷ row "Merge" same same
  ∷ row "Id" same same ∷ []
Tid₂-rows = refl

Δ₆-X : eraseTy E.Δ₆ (` 0 ⇒ `∀ (` 0 ⇒ ` 1)) ≡ (`ℕ ⇒ `∀ (` 0 ⇒ `ℕ))
Δ₆-X = refl

-- THE STORE, followed: an ALIAS cell denotes what its payload's cell
-- denotes (Examples §8's store [α := ℕ , β := γ , γ := ℕ], newest
-- first) ...
alias-concrete :
  env (bindR `ℕ ∷ bindR (` 0) ∷ bindR `ℕ ∷ []) 1 ≡ `ℕ
alias-concrete = refl

-- ... including an alias of an ABSTRACT cell, which denotes a source
-- variable, numbered by the abstract cells newer than it
alias-abstract :
  env (bindR (` 0) ∷ abstR ∷ bindR `ℕ ∷ abstR ∷ []) 0 ≡ ` 0
alias-abstract = refl

abstract-numbering :
  env (abstR ∷ bindR (` 0) ∷ abstR ∷ []) 1 ≡ ` 1
abstract-numbering = refl

-- WHY THE BODY IS ERASED AT `inside Δ Θ`.  Erasing a boundary's body
-- at the EXTERIOR context instead reads its ordinary names through the
-- wrong name map.  After §1a's TyBeta the state is
-- (λx:X. x) ⟪ ↥X , … ⟫ · 7 at the store (α := ℕ) with no ambient
-- names: the right erasure reads X as ℕ, the naive one leaves it
-- dangling.
eraseNaive : Ctxᵗ → Term → STerm
eraseNaive Δ (` x)           = ` x
eraseNaive Δ ($ n)           = $ n
eraseNaive Δ `true           = `true
eraseNaive Δ `false          = `false
eraseNaive Δ (ƛ A ∙ N)       = ƛ eraseTy Δ A ∙ eraseNaive Δ N
eraseNaive Δ (L · M)         = eraseNaive Δ L · eraseNaive Δ M
eraseNaive Δ (Λ N)           = Λ (eraseNaive (underΛ Δ) N)
eraseNaive Δ (ν A · L ⟨ c ⟩) = eraseNaive Δ L [ eraseTy Δ A ]
eraseNaive Δ (M ⟪ Θ , c ⟫)   = eraseNaive Δ M

P-state₁ : Maybe Term
P-state₁ = Maybe.map proj₁ (step empty E.P₀)

P-state₁-erase :
  Maybe.map (erase (allocate `ℕ empty)) P-state₁
    ≡ just ((ƛ `ℕ ∙ ` 0) · $ 7)
P-state₁-erase = refl

P-state₁-naive :
  Maybe.map (eraseNaive (allocate `ℕ empty)) P-state₁
    ≡ just ((ƛ ` 0 ∙ ` 0) · $ 7)
P-state₁-naive = refl

-- THE TYPING PREMISE IS NEEDED.  `Id` checks only `Simple U` and
-- `Base A`, so on an ILL-TYPED term it can drop an identity boundary
-- whose body is a λ.  At Δ₆ = (α := ℕ) ∣ (X ↦ α), the body of
-- (λx:X. x) ⟪ ↓X , id ℕ ⟫ is erased where X is NOT named (its
-- annotation dangles), while the contractum λx:X. x reads X as ℕ: the
-- two erasures are neither equal nor a source step.
Mbad : Term
Mbad = (ƛ (` 0) ∙ (` 0)) ⟪ unbind 0 0 ∷ [] , ⌞ id `ℕ ⌟ ⟫

Mbad-rows : rows 5 E.Δ₆ Mbad ≡ row "Id" same bad ∷ []
Mbad-rows = refl

-- NON-VACUITY of the checker: `link` does say `bad`
link-bad : link ($ 1) ($ 2) ≡ bad
link-bad = refl

link-bad-step : link ((ƛ `ℕ ∙ ` 0) · $ 1) ($ 2) ≡ bad
link-bad-step = refl
