module strong-rep-nu.Erasure where

-- File Charter:
--   * THE ERASURE FROM THE RUN-TIME LANGUAGE TO THE SOURCE LANGUAGE
--     (strong-rep-nu.Source).  §1 what a representation variable
--     DENOTES (`env`), read through the store, and the source scope
--     (`srcScope`); §2 the erasure of types (`nameσ`, `eraseTy`);
--     §3 the interior name map, computed (`interiorⁿ`, `inside`);
--     §4 the erasure of terms (`erase`); §5 which steps STUTTER
--     (`isStutter`, `Stutter`); §6 `idCtx`.
--   * DEFINITIONS ONLY.  The theorems are stated in
--     strong-rep-nu.ErasureTheorems and proved under proof/Erasure*;
--     the design is notes/ErasureSketch.md.
--   * ERASURE IS A FUNCTION OF (Δ, M), not of a typing derivation:
--     the context carries the name map and the store, which is all
--     an ordinary type variable needs to be resolved.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; T)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)

open import strong-rep-nu.Types
open import strong-rep-nu.Ctx
open import strong-rep-nu.Boundary using (Change; unbind; bind; Boundary)
open import strong-rep-nu.Terms
  using (Term; Ctx; `_; $_; `true; `false; ƛ_∙_; _·_; Λ_; ν_·_⟨_⟩;
         _⟪_,_⟫)
open import strong-rep-nu.Reduction
open import strong-rep-nu.Source
  using (STerm; `_; $_; `true; `false; ƛ_∙_; _·_; Λ_; _[_])

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
srcScope : RepCtx → ℕ
srcScope []            = zero
srcScope (abstR ∷ Ξ)   = suc (srcScope Ξ)
srcScope (bindR R ∷ Ξ) = srcScope Ξ

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
-- 5. Stutters
------------------------------------------------------------------------

-- WHICH disjunct, by rule.  A STUTTER is a step whose erasure does not
-- move: `Wrap`, `Merge`, `Id`, and the congruences around them.  Every
-- other step (`TyBeta`, `Beta`, `TyWrap`, under congruences) takes
-- exactly one source step.
isStutter : ∀ {Δ M M′ δ} → Δ ⊢ M -→ M′ ∣ δ → Bool
isStutter (TyBeta v a)                     = false
isStutter (Beta w)                         = false
isStutter (Wrap v w r₁ r₂ r₃ sc)           = true
isStutter (TyWrap v r s a)                 = false
isStutter (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂) = true
isStutter (Id u b)                         = true
isStutter (ξ-·₁ st)                        = isStutter st
isStutter (ξ-·₂ v st)                      = isStutter st
isStutter (ξ-ν st)                         = isStutter st
isStutter (ξ-⟪⟫ r st)                      = isStutter st

Stutter : ∀ {Δ M M′ δ} → Δ ⊢ M -→ M′ ∣ δ → Set
Stutter r = T (isStutter r)

------------------------------------------------------------------------
-- 6. The identity context
------------------------------------------------------------------------

-- the context whose n ordinary names denote the n source variables
idCtx : ℕ → Ctxᵗ
idCtx zero    = empty
idCtx (suc n) = underΛ (idCtx n)
