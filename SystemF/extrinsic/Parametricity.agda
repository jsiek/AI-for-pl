module extrinsic.Parametricity where

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (Level; Lift; lift; lower)
open import Function using (case_of_)

open import extrinsic.Types
open import extrinsic.Terms
open import extrinsic.Reduction

-- The type of relations on values of type A and B
Rel : Ty → Ty → Set₁
Rel A B = (V : Term) → (W : Term) → Value V → Value W → Set

record RelSub : Set₁ where
  field
    ρ₁ : Substᵗ
    ρ₂ : Substᵗ
    ρR : ∀ α → Rel (ρ₁ α) (ρ₂ α)
open RelSub public

∅ρ : RelSub
(∅ρ .ρ₁) = idᵗ
(∅ρ .ρ₂) = idᵗ
(∅ρ .ρR) = λ α V W x x₁ → ⊥ -- wild guess! -Jeremy

_,⟨_,_,_⟩ : (ρ : RelSub) → (A₁ A₂ : Ty) → Rel A₁ A₂ → RelSub
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρ₁        = A₁ •ᵗ ρ₁ ρ
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρ₂        = A₂ •ᵗ ρ₂ ρ
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρR 0      = R
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρR (suc α)  = ρR ρ α

--------------------------------------------------------------------------------
-- The Logical Relation
--------------------------------------------------------------------------------

𝒱 : (A : Ty) (ρ : RelSub) (V : Term) (W : Term) → Value V → Value W → Set₁
ℰ : (A : Ty) (ρ : RelSub) → Term → Term → Set₁

𝒱 (` α) ρ V W v w = Lift _ (ρR ρ α V W v w)
𝒱 `ℕ ρ `zero `zero vZero vZero = ⊤
𝒱 `ℕ ρ `zero (`suc W) vZero (vSuc w) = ⊥
𝒱 `ℕ ρ (`suc V) `zero (vSuc v) vZero = ⊥
𝒱 `ℕ ρ (`suc V) (`suc W) (vSuc v) (vSuc w) = 𝒱 `ℕ ρ V W v w
𝒱 `Bool ρ `true `true vTrue vTrue = ⊤
𝒱 `Bool ρ `true `false vTrue vFalse = ⊥
𝒱 `Bool ρ `false `true vFalse vTrue = ⊥
𝒱 `Bool ρ `false `false vFalse vFalse = ⊤
𝒱 (A ⇒ B) ρ (ƛ N) (ƛ M) vLam vLam =
  ∀ {V W} (v : Value V) (w : Value W)
   → 𝒱 A ρ V W v w
   → ℰ B ρ (N [ V ]) (M [ W ])
𝒱 (`∀ A) ρ (Λ N) (Λ M) vTlam vTlam =
  ∀ (A₁ A₂ : Ty)
   → (R : Rel A₁ A₂)
   → ℰ A (ρ ,⟨ A₁ , A₂ , R ⟩) N M
𝒱 A ρ N M vN vM = ⊥

ℰ A ρ M N =
  ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
    (M —↠ V) × (N —↠ W) × 𝒱 A ρ V W v w

--------------------------------------------------------------------------------
-- Closing Substitutions
--------------------------------------------------------------------------------

record RelEnv : Set where
  field
    γ₁ : Subst
    γ₂ : Subst
open RelEnv public

∅γ : RelEnv
(∅γ .γ₁) = id
(∅γ .γ₂) = id

_,⟨_,_⟩ : (γ : RelEnv) (V : Term) (W : Term) → RelEnv
((γ ,⟨ V , W ⟩) .γ₁) = V • (γ .γ₁)
((γ ,⟨ V , W ⟩) .γ₂) = W • (γ .γ₂)


⇓γ : RelEnv → RelEnv
(⇓γ γ .γ₁) i = γ₁ γ (suc i)
(⇓γ γ .γ₂) i = γ₂ γ (suc i)

--------------------------------------------------------------------------------
-- Logically related contexts
--------------------------------------------------------------------------------

𝒢 : Ctx → RelSub → RelEnv → Set₁
𝒢 [] ρ γ = ⊤
𝒢 (A ∷ Γ) ρ γ = ℰ A ρ (γ .γ₁ 0) (γ .γ₂ 0) × 𝒢 Γ ρ (⇓γ γ)

--------------------------------------------------------------------------------
-- Logically related terms
--------------------------------------------------------------------------------

LogicalRel : (Γ : Ctx) (A : Ty) (M N : Term) → Set₁
LogicalRel Γ A M N = ∀ (ρ : RelSub) (γ : RelEnv)
  → 𝒢 Γ ρ γ
  → ℰ A ρ (subst (γ .γ₁) M) (subst (γ .γ₂) N)

--------------------------------------------------------------------------------
-- Logically related values are related terms
--------------------------------------------------------------------------------

𝒱⇒ℰ : ∀ {A} {ρ : RelSub} {V W : Term}
  → (v : Value V)
  → (w : Value W)
  → 𝒱 A ρ V W v w
  → ℰ A ρ V W
𝒱⇒ℰ {V = V} {W = W} v w VW-rel =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ V ∎ , ⟨ W ∎ , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩


--------------------------------------------------------------------------------
-- Constructing logically related contexts
--------------------------------------------------------------------------------

𝒢-∅ : 𝒢 [] ∅ρ ∅γ
𝒢-∅ = tt

extendRelEnv-related : ∀ {Γ A} {ρ : RelSub} {γ : RelEnv} {V W : Term}
  → (env : 𝒢 Γ ρ γ)
  → (v : Value V)
  → (w : Value W)
  → 𝒱 A ρ V W v w
  → 𝒢 (A ∷ Γ) ρ (γ ,⟨ V , W ⟩)
extendRelEnv-related {A = A} {ρ = ρ} {V = V} {W = W} env v w VW-rel =
  ⟨ 𝒱⇒ℰ {A = A} {ρ = ρ} {V = V} {W = W} v w VW-rel , env ⟩

--------------------------------------------------------------------------------
-- Compatibility Lemmas
--------------------------------------------------------------------------------

compat-· : ∀ {Γ A B}
  → (L M : Term)
  → LogicalRel Γ (A ⇒ B) L L
  → LogicalRel Γ A M M
  → LogicalRel Γ B (L · M) (L · M)
compat-· {Γ = Γ} {A = A} {B = B} L M L-rel M-rel ρ γ env
  with L-rel ρ γ env | M-rel ρ γ env
... | ⟨ .(ƛ N) , ⟨ .(ƛ P) , ⟨ vLam {N = N} , ⟨ vLam {N = P} , ⟨ L₁—↠V , ⟨ L₂—↠W , f-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ V , ⟨ W , ⟨ vV , ⟨ vW , ⟨ M₁—↠V , ⟨ M₂—↠W , arg-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with f-rel vV vW arg-rel
... | ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ redL' , ⟨ redR' , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V'
  , ⟨ W'
    , ⟨ v'
      , ⟨ w'
        , ⟨ multi-trans left-red redL'
          , ⟨ multi-trans right-red redR'
            , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  app-compat : ∀ {L₀ L' M₀ M' : Term}
    → L₀ —↠ L' → Value L' → M₀ —↠ M' → (L₀ · M₀) —↠ (L' · M')
  app-compat {L₀ = L₀} {L' = L'} {M₀ = M₀} {M' = M'} (L' ∎) vL' (M' ∎) =
    (L' · M') ∎
  app-compat {L₀ = L₀} {L' = L'} {M₀ = M₀} {M' = M'} (L' ∎) vL' (M₀ —→⟨ s ⟩ msM) =
    (L' · M₀) —→⟨ ξ-·₂ vL' s ⟩ app-compat (L' ∎) vL' msM
  app-compat {L₀ = L₀} {L' = L'} {M₀ = M₀} {M' = M'} (L₀ —→⟨ s ⟩ msL) vL' msM =
    (L₀ · M₀) —→⟨ ξ-·₁ s ⟩ app-compat msL vL' msM

  beta-left : ((ƛ N) · V) —↠ N [ V ]
  beta-left = ((ƛ N) · V) —→⟨ β-ƛ vV ⟩ ((N [ V ]) ∎)

  left-red : subst (γ .γ₁) (L · M) —↠ N [ V ]
  left-red =
    multi-trans
      (app-compat
        {L₀ = subst (γ .γ₁) L} {L' = ƛ N}
        {M₀ = subst (γ .γ₁) M} {M' = V}
        L₁—↠V
        vLam
        M₁—↠V)
      beta-left

  beta-right : ((ƛ P) · W) —↠ P [ W ]
  beta-right = ((ƛ P) · W) —→⟨ β-ƛ vW ⟩ ((P [ W ]) ∎)

  right-red : subst (γ .γ₂) (L · M) —↠ P [ W ]
  right-red =
    multi-trans
      (app-compat
        {L₀ = subst (γ .γ₂) L} {L' = ƛ P}
        {M₀ = subst (γ .γ₂) M} {M' = W}
        L₂—↠W
        vLam
        M₂—↠W)
      beta-right

compat-true : ∀ {Γ}
  → LogicalRel Γ `Bool `true `true
compat-true ρ γ env =
  𝒱⇒ℰ {A = `Bool} {ρ = ρ} {V = `true} {W = `true} vTrue vTrue tt

compat-suc : ∀ {Γ}
  → (M : Term)
  → LogicalRel Γ `ℕ M M
  → LogicalRel Γ `ℕ (`suc M) (`suc M)
compat-suc M M-rel ρ γ env with M-rel ρ γ env
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M₁—↠V , ⟨ M₂—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ `suc V
  , ⟨ `suc W
    , ⟨ vSuc v
      , ⟨ vSuc w
        , ⟨ suc-↠ M₁—↠V
          , ⟨ suc-↠ M₂—↠W
            , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  suc-↠ : ∀ {M N} → M —↠ N → (`suc M) —↠ (`suc N)
  suc-↠ (M ∎) = (`suc M) ∎
  suc-↠ (M₀ —→⟨ s ⟩ ms) = (`suc M₀) —→⟨ ξ-suc s ⟩ suc-↠ ms

vw-rel-to-nat : ∀ {ρ V W v w}
  → 𝒱 `ℕ ρ (`suc V) (`suc W) (vSuc v) (vSuc w)
  → 𝒱 `ℕ ρ V W v w
vw-rel-to-nat rel = rel

compat-case : ∀ {Γ A}
  → (L M N : Term)
  → LogicalRel Γ `ℕ L L
  → LogicalRel Γ A M M
  → LogicalRel (`ℕ ∷ Γ) A N N
  → LogicalRel Γ A (case_[zero⇒_|suc⇒_] L M N) (case_[zero⇒_|suc⇒_] L M N)
compat-case {Γ = Γ} {A = A} L M N L-rel M-rel N-rel ρ γ env =
  go {L₀ = L} (L-rel ρ γ env)
  where
  go : ∀ {L₀ : Term}
    → ℰ `ℕ ρ (subst (γ .γ₁) L₀) (subst (γ .γ₂) L₀)
    → ℰ A ρ
        (subst (γ .γ₁) (case_[zero⇒_|suc⇒_] L₀ M N))
        (subst (γ .γ₂) (case_[zero⇒_|suc⇒_] L₀ M N))
  go {L₀ = L₀} ⟨ `zero , ⟨ `zero , ⟨ vZero , ⟨ vZero , ⟨ L₁—↠0 , ⟨ L₂—↠0 , tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with M-rel ρ γ env
  ... | ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ M₁—↠V' , ⟨ M₂—↠W' , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V'
    , ⟨ W'
      , ⟨ v'
        , ⟨ w'
          , ⟨ multi-trans (case-↠ (γ .γ₁) L₁—↠0)
               (multi-trans case-zero-left M₁—↠V')
            , ⟨ multi-trans (case-↠ (γ .γ₂) L₂—↠0)
                 (multi-trans case-zero-right M₂—↠W')
              , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    case-↠ : ∀ (σ : Subst) {L₁ L' : Term}
      → L₁ —↠ L'
      → (case_[zero⇒_|suc⇒_] L₁ (subst σ M) (subst (exts σ) N))
        —↠ case_[zero⇒_|suc⇒_] L' (subst σ M) (subst (exts σ) N)
    case-↠ σ (L₁ ∎) =
      (case_[zero⇒_|suc⇒_] L₁ (subst σ M) (subst (exts σ) N)) ∎
    case-↠ σ (L₁ —→⟨ s ⟩ ms) =
      (case_[zero⇒_|suc⇒_] L₁ (subst σ M) (subst (exts σ) N))
        —→⟨ ξ-case s ⟩
        case-↠ σ ms

    case-zero-left :
      case_[zero⇒_|suc⇒_] `zero (subst (γ .γ₁) M) (subst (exts (γ .γ₁)) N)
        —↠ subst (γ .γ₁) M
    case-zero-left = (case_[zero⇒_|suc⇒_] `zero (subst (γ .γ₁) M) (subst (exts (γ .γ₁)) N))
      —→⟨ β-zero ⟩ (subst (γ .γ₁) M ∎)

    case-zero-right :
      case_[zero⇒_|suc⇒_] `zero (subst (γ .γ₂) M) (subst (exts (γ .γ₂)) N)
        —↠ subst (γ .γ₂) M
    case-zero-right = (case_[zero⇒_|suc⇒_] `zero (subst (γ .γ₂) M) (subst (exts (γ .γ₂)) N))
      —→⟨ β-zero ⟩ (subst (γ .γ₂) M ∎)

  go {L₀ = L₀} ⟨ `suc V , ⟨ `suc W , ⟨ vSuc vV , ⟨ vSuc wW , ⟨ L₁—↠sV , ⟨ L₂—↠sW , vw-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with N-rel ρ (γ ,⟨ V , W ⟩)
         (⟨ 𝒱⇒ℰ {A = `ℕ} {ρ = ρ} {V = V} {W = W} vV wW vw-rel , env ⟩)
  ... | ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ N₁—↠V' , ⟨ N₂—↠W' , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V'
    , ⟨ W'
      , ⟨ v'
        , ⟨ w'
          , ⟨ multi-trans (case-↠ (γ .γ₁) L₁—↠sV)
               (multi-trans (case-suc {σ = γ .γ₁} vV) N₁—↠V')
            , ⟨ multi-trans (case-↠ (γ .γ₂) L₂—↠sW)
                 (multi-trans (case-suc {σ = γ .γ₂} wW) N₂—↠W')
              , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    case-↠ : ∀ (σ : Subst) {L₁ L' : Term}
      → L₁ —↠ L'
      → (case_[zero⇒_|suc⇒_] L₁ (subst σ M) (subst (exts σ) N))
        —↠ case_[zero⇒_|suc⇒_] L' (subst σ M) (subst (exts σ) N)
    case-↠ σ (L₁ ∎) =
      (case_[zero⇒_|suc⇒_] L₁ (subst σ M) (subst (exts σ) N)) ∎
    case-↠ σ (L₁ —→⟨ s ⟩ ms) =
      (case_[zero⇒_|suc⇒_] L₁ (subst σ M) (subst (exts σ) N))
        —→⟨ ξ-case s ⟩
        case-↠ σ ms

    case-suc : ∀ {σ : Subst} {U : Term}
      → Value U
      → case_[zero⇒_|suc⇒_] (`suc U) (subst σ M) (subst (exts σ) N)
        —↠ subst (U • σ) N
    case-suc {σ} {U} vU =
      substEq
        (case_[zero⇒_|suc⇒_] (`suc U) (subst σ M) (subst (exts σ) N) —↠_)
        (exts-sub-cons σ N U)
        ((case_[zero⇒_|suc⇒_] (`suc U) (subst σ M) (subst (exts σ) N))
          —→⟨ β-suc vU ⟩ ((subst (exts σ) N) [ U ] ∎))

compat-zero : ∀ {Γ}
  → LogicalRel Γ `ℕ `zero `zero
compat-zero ρ γ env = 𝒱⇒ℰ {A = `ℕ} {V = `zero} {W = `zero} vZero vZero tt

compat-ƛ : ∀ {Γ A B}
  → (N : Term)
  → LogicalRel (A ∷ Γ) B N N
  → LogicalRel Γ (A ⇒ B) (ƛ N) (ƛ N)
compat-ƛ {A = A} {B = B} N N-rel ρ γ env =
  ⟨ subst (γ .γ₁) (ƛ N)
  , ⟨ subst (γ .γ₂) (ƛ N)
    , ⟨ vLam
      , ⟨ vLam
        , ⟨ subst (γ .γ₁) (ƛ N) ∎
          , ⟨ subst (γ .γ₂) (ƛ N) ∎
            , LR-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  β-subst₁ : ∀ {V}
    → subst (exts (γ .γ₁)) N [ V ] ≡ subst (V • (γ .γ₁)) N
  β-subst₁ {V} = exts-sub-cons (γ .γ₁) N V

  β-subst₂ : ∀ {W}
    → subst (exts (γ .γ₂)) N [ W ] ≡ subst (W • (γ .γ₂)) N
  β-subst₂ {W} = exts-sub-cons (γ .γ₂) N W

  LR-rel : 𝒱 (A ⇒ B) ρ (subst (γ .γ₁) (ƛ N)) (subst (γ .γ₂) (ƛ N)) vLam vLam
  LR-rel {V} {W} v w VW-rel
    rewrite β-subst₁ {V = V}
          | β-subst₂ {W = W} =
    N-rel ρ (γ ,⟨ V , W ⟩)
      (extendRelEnv-related {A = A} {ρ = ρ} {γ = γ} {V = V} {W = W} env v w VW-rel)

compat-false : ∀ {Γ}
  → LogicalRel Γ `Bool `false `false
compat-false ρ γ env =
  𝒱⇒ℰ {A = `Bool} {ρ = ρ} {V = `false} {W = `false} vFalse vFalse tt

if-true-↠ : ∀ {L M N}
  → L —↠ `true
  → (`if_then_else L M N) —↠ M
if-true-↠ {M = M} {N = N} (L ∎) =
  (`if_then_else `true M N) —→⟨ β-true ⟩ (M ∎)
if-true-↠ {M = M} {N = N} (L₀ —→⟨ s ⟩ ms) =
  (`if_then_else L₀ M N) —→⟨ ξ-if s ⟩ if-true-↠ {M = M} {N = N} ms

if-false-↠ : ∀ {L M N}
  → L —↠ `false
  → (`if_then_else L M N) —↠ N
if-false-↠ {M = M} {N = N} (L ∎) =
  (`if_then_else `false M N) —→⟨ β-false ⟩ (N ∎)
if-false-↠ {M = M} {N = N} (L₀ —→⟨ s ⟩ ms) =
  (`if_then_else L₀ M N) —→⟨ ξ-if s ⟩ if-false-↠ {M = M} {N = N} ms

compat-if : ∀ {Γ A}
  → (L M N : Term)
  → LogicalRel Γ `Bool L L
  → LogicalRel Γ A M M
  → LogicalRel Γ A N N
  → LogicalRel Γ A (`if_then_else L M N) (`if_then_else L M N)
compat-if {A = A} L M N L-rel M-rel N-rel ρ γ env
  with L-rel ρ γ env | M-rel ρ γ env | N-rel ρ γ env
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ L₁—↠V , ⟨ L₂—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ M₁—↠V' , ⟨ M₂—↠W' , relM ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ V'' , ⟨ W'' , ⟨ v'' , ⟨ w'' , ⟨ N₁—↠V'' , ⟨ N₂—↠W'' , relN ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with v | w | VW-rel
... | vTrue | vTrue | tt =
  ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨
      multi-trans (if-true-↠ {M = subst (γ .γ₁) M} {N = subst (γ .γ₁) N} L₁—↠V) M₁—↠V'
    , ⟨ multi-trans (if-true-↠ {M = subst (γ .γ₂) M} {N = subst (γ .γ₂) N} L₂—↠W) M₂—↠W'
      , relM ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
... | vFalse | vFalse | tt =
  ⟨ V'' , ⟨ W'' , ⟨ v'' , ⟨ w'' , ⟨
      multi-trans (if-false-↠ {M = subst (γ .γ₁) M} {N = subst (γ .γ₁) N} L₁—↠V) N₁—↠V''
    , ⟨ multi-trans (if-false-↠ {M = subst (γ .γ₂) M} {N = subst (γ .γ₂) N} L₂—↠W) N₂—↠W''
      , relN ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
... | vTrue | vFalse | ()
... | vFalse | vTrue | ()

compat-var : ∀ {Γ A x} → Γ ∋ x ⦂ A → LogicalRel Γ A (` x) (` x)
compat-var Z ρ γ env = proj₁ env
compat-var (S x) ρ γ env = compat-var x ρ (⇓γ γ) (proj₂ env)


data WkRel : Renameᵗ → RelSub → RelSub → Set₁ where
  wk-suc :
    ∀ {ρ A₁ A₂} (R : Rel A₁ A₂) →
    WkRel suc ρ (ρ ,⟨ A₁ , A₂ , R ⟩)

  wk-ext :
    ∀ {ξ ρ ρ' B₁ B₂} (S : Rel B₁ B₂) →
    WkRel ξ ρ ρ' →
    WkRel (extᵗ ξ) (ρ ,⟨ B₁ , B₂ , S ⟩) (ρ' ,⟨ B₁ , B₂ , S ⟩)

wk-ρR-eq : ∀ {ξ ρ ρ'} → WkRel ξ ρ ρ' → (α : Var) → ρR ρ α ≡ ρR ρ' (ξ α)
wk-ρR-eq (wk-suc R) α = refl
wk-ρR-eq (wk-ext _ wk-r) zero = refl
wk-ρR-eq (wk-ext _ wk-r) (suc α) = wk-ρR-eq wk-r α

𝒱-Nat-irrel : ∀ {ρ σ V W} {v : Value V} {w : Value W}
  → 𝒱 `ℕ ρ V W v w
  → 𝒱 `ℕ σ V W v w
𝒱-Nat-irrel {V = `zero} {W = `zero} {v = vZero} {w = vZero} VW-rel = VW-rel
𝒱-Nat-irrel {V = `suc V} {W = `suc W} {v = vSuc v} {w = vSuc w} VW-rel =
  𝒱-Nat-irrel {V = V} {W = W} {v = v} {w = w} VW-rel

𝒱-Bool-irrel : ∀ {ρ σ V W} {v : Value V} {w : Value W}
  → 𝒱 `Bool ρ V W v w
  → 𝒱 `Bool σ V W v w
𝒱-Bool-irrel {V = `true} {W = `true} {v = vTrue} {w = vTrue} VW-rel = VW-rel
𝒱-Bool-irrel {V = `false} {W = `false} {v = vFalse} {w = vFalse} VW-rel = VW-rel

mutual
  𝒱-rename-wk :
    ∀ {A ξ ρ ρ' V W} {v : Value V} {w : Value W}
    → WkRel ξ ρ ρ'
    → 𝒱 A ρ V W v w
    → 𝒱 (renameᵗ ξ A) ρ' V W v w
  𝒱-rename-wk {A = ` α} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    substEq
      (λ X → Lift _ (X V W v w))
      (wk-ρR-eq wk-r α)
      𝒱VW
  𝒱-rename-wk {A = `ℕ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Nat-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-rename-wk {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Bool-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-rename-wk {A = A ⇒ B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = ƛ N} {W = ƛ M} {v = vLam} {w = vLam} wk-r 𝒱VW =
    λ v₁ w₁ arg-rel' →
      ℰ-rename-wk {A = B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
        (𝒱VW v₁ w₁
          (𝒱-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} wk-r arg-rel'))
  𝒱-rename-wk {A = A ⇒ B} {v = vLam} {w = vTrue} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vLam} {w = vFalse} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vLam} {w = vZero} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vLam} {w = vSuc w} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vLam} {w = vTlam} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vTrue} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vFalse} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vZero} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vSuc v} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vTlam} wk-r ()
  𝒱-rename-wk {A = `∀ A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} wk-r 𝒱VW =
    λ A₁ A₂ R →
      ℰ-rename-wk {A = A} {ξ = extᵗ ξ} {ρ = ρ ,⟨ A₁ , A₂ , R ⟩} {ρ' = ρ' ,⟨ A₁ , A₂ , R ⟩}
        (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r)
        (𝒱VW A₁ A₂ R)
  𝒱-rename-wk {A = `∀ A} {v = vTlam} {w = vLam} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vTlam} {w = vTrue} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vTlam} {w = vFalse} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vTlam} {w = vZero} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vTlam} {w = vSuc w} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vTrue} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vFalse} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vZero} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vSuc v} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vLam} wk-r ()

  𝒱-unrename-wk :
    ∀ {A ξ ρ ρ' V W} {v : Value V} {w : Value W}
    → WkRel ξ ρ ρ'
    → 𝒱 (renameᵗ ξ A) ρ' V W v w
    → 𝒱 A ρ V W v w
  𝒱-unrename-wk {A = ` α} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    substEq
      (λ X → Lift _ (X V W v w))
      (sym (wk-ρR-eq wk-r α))
      𝒱VW
  𝒱-unrename-wk {A = `ℕ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Nat-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unrename-wk {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Bool-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unrename-wk {A = A ⇒ B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = ƛ N} {W = ƛ M} {v = vLam} {w = vLam} wk-r 𝒱VW =
    λ v₁ w₁ arg-rel →
      ℰ-unrename-wk {A = B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
        (𝒱VW v₁ w₁
          (𝒱-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} wk-r arg-rel))
  𝒱-unrename-wk {A = A ⇒ B} {v = vLam} {w = vTrue} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vLam} {w = vFalse} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vLam} {w = vZero} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vLam} {w = vSuc w} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vLam} {w = vTlam} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vTrue} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vFalse} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vZero} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vSuc v} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vTlam} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} wk-r 𝒱VW =
    λ A₁ A₂ R →
      ℰ-unrename-wk {A = A} {ξ = extᵗ ξ} {ρ = ρ ,⟨ A₁ , A₂ , R ⟩} {ρ' = ρ' ,⟨ A₁ , A₂ , R ⟩}
        (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r)
        (𝒱VW A₁ A₂ R)
  𝒱-unrename-wk {A = `∀ A} {v = vTlam} {w = vLam} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vTlam} {w = vTrue} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vTlam} {w = vFalse} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vTlam} {w = vZero} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vTlam} {w = vSuc w} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vTrue} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vFalse} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vZero} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vSuc v} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vLam} wk-r ()

  ℰ-rename-wk :
    ∀ {A ξ ρ ρ' M N}
    → WkRel ξ ρ ρ'
    → ℰ A ρ M N
    → ℰ (renameᵗ ξ A) ρ' M N
  ℰ-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
      , 𝒱-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW
      ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  ℰ-unrename-wk :
    ∀ {A ξ ρ ρ' M N}
    → WkRel ξ ρ ρ'
    → ℰ (renameᵗ ξ A) ρ' M N
    → ℰ A ρ M N
  ℰ-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
      , 𝒱-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW
      ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

record SubstRel (σ : Substᵗ) (ρ : RelSub) (ρ' : RelSub) : Set₁ where
  field
    var⇒ : ∀ α {V W} {v : Value V} {w : Value W}
      → 𝒱 (` α) ρ' V W v w
      → 𝒱 (σ α) ρ V W v w

    var⇐ : ∀ α {V W} {v : Value V} {w : Value W}
      → 𝒱 (σ α) ρ V W v w
      → 𝒱 (` α) ρ' V W v w

exts-SubstRel : ∀ {σ ρ ρ' A₁ A₂}
  → (R : Rel A₁ A₂)
  → SubstRel σ ρ ρ'
  → SubstRel (extsᵗ σ) (ρ ,⟨ A₁ , A₂ , R ⟩) (ρ' ,⟨ A₁ , A₂ , R ⟩)
SubstRel.var⇒ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) zero rel = rel
SubstRel.var⇒ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) (suc α) rel =
  𝒱-rename-wk {A = σ α} {ξ = suc} {ρ = ρ} {ρ' = ρ ,⟨ A₁ , A₂ , R ⟩}
    (wk-suc {ρ = ρ} {A₁ = A₁} {A₂ = A₂} R)
    (SubstRel.var⇒ sr α rel)

SubstRel.var⇐ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) zero rel = rel
SubstRel.var⇐ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) (suc α) rel =
  SubstRel.var⇐ sr α
    (𝒱-unrename-wk {A = σ α} {ξ = suc} {ρ = ρ} {ρ' = ρ ,⟨ A₁ , A₂ , R ⟩}
      (wk-suc {ρ = ρ} {A₁ = A₁} {A₂ = A₂} R)
      rel)

mutual
  𝒱-subst :
    ∀ {A σ ρ ρ' V W} {v : Value V} {w : Value W}
    → SubstRel σ ρ ρ'
    → 𝒱 A ρ' V W v w
    → 𝒱 (substᵗ σ A) ρ V W v w
  𝒱-subst {A = ` α} sr 𝒱VW = SubstRel.var⇒ sr α 𝒱VW
  𝒱-subst {A = `ℕ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW =
    𝒱-Nat-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-subst {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW =
    𝒱-Bool-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-subst {A = A ⇒ B} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = ƛ N} {W = ƛ M} {v = vLam} {w = vLam} sr 𝒱VW =
    λ v₁ w₁ arg-rel →
      ℰ-subst {A = B} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
        (𝒱VW v₁ w₁ (𝒱-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} sr arg-rel))
  𝒱-subst {A = A ⇒ B} {v = vLam} {w = vTrue} sr ()
  𝒱-subst {A = A ⇒ B} {v = vLam} {w = vFalse} sr ()
  𝒱-subst {A = A ⇒ B} {v = vLam} {w = vZero} sr ()
  𝒱-subst {A = A ⇒ B} {v = vLam} {w = vSuc w} sr ()
  𝒱-subst {A = A ⇒ B} {v = vLam} {w = vTlam} sr ()
  𝒱-subst {A = A ⇒ B} {v = vTrue} sr ()
  𝒱-subst {A = A ⇒ B} {v = vFalse} sr ()
  𝒱-subst {A = A ⇒ B} {v = vZero} sr ()
  𝒱-subst {A = A ⇒ B} {v = vSuc v} sr ()
  𝒱-subst {A = A ⇒ B} {v = vTlam} sr ()
  𝒱-subst {A = `∀ A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} sr 𝒱VW =
    λ A₁ A₂ R →
      ℰ-subst {A = A} {σ = extsᵗ σ}
        {ρ = ρ ,⟨ A₁ , A₂ , R ⟩}
        {ρ' = ρ' ,⟨ A₁ , A₂ , R ⟩}
        (exts-SubstRel R sr)
        (𝒱VW A₁ A₂ R)
  𝒱-subst {A = `∀ A} {v = vTlam} {w = vLam} sr ()
  𝒱-subst {A = `∀ A} {v = vTlam} {w = vTrue} sr ()
  𝒱-subst {A = `∀ A} {v = vTlam} {w = vFalse} sr ()
  𝒱-subst {A = `∀ A} {v = vTlam} {w = vZero} sr ()
  𝒱-subst {A = `∀ A} {v = vTlam} {w = vSuc w} sr ()
  𝒱-subst {A = `∀ A} {v = vTrue} sr ()
  𝒱-subst {A = `∀ A} {v = vFalse} sr ()
  𝒱-subst {A = `∀ A} {v = vZero} sr ()
  𝒱-subst {A = `∀ A} {v = vSuc v} sr ()
  𝒱-subst {A = `∀ A} {v = vLam} sr ()

  𝒱-unsubst :
    ∀ {A σ ρ ρ' V W} {v : Value V} {w : Value W}
    → SubstRel σ ρ ρ'
    → 𝒱 (substᵗ σ A) ρ V W v w
    → 𝒱 A ρ' V W v w
  𝒱-unsubst {A = ` α} sr 𝒱VW = SubstRel.var⇐ sr α 𝒱VW
  𝒱-unsubst {A = `ℕ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW =
    𝒱-Nat-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unsubst {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW =
    𝒱-Bool-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unsubst {A = A ⇒ B} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = ƛ N} {W = ƛ M} {v = vLam} {w = vLam} sr 𝒱VW =
    λ v₁ w₁ arg-rel →
      ℰ-unsubst {A = B} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
        (𝒱VW v₁ w₁ (𝒱-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} sr arg-rel))
  𝒱-unsubst {A = A ⇒ B} {v = vLam} {w = vTrue} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vLam} {w = vFalse} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vLam} {w = vZero} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vLam} {w = vSuc w} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vLam} {w = vTlam} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vTrue} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vFalse} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vZero} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vSuc v} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vTlam} sr ()
  𝒱-unsubst {A = `∀ A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} sr 𝒱VW =
    λ A₁ A₂ R →
      ℰ-unsubst {A = A} {σ = extsᵗ σ}
        {ρ = ρ ,⟨ A₁ , A₂ , R ⟩}
        {ρ' = ρ' ,⟨ A₁ , A₂ , R ⟩}
        (exts-SubstRel R sr)
        (𝒱VW A₁ A₂ R)
  𝒱-unsubst {A = `∀ A} {v = vTlam} {w = vLam} sr ()
  𝒱-unsubst {A = `∀ A} {v = vTlam} {w = vTrue} sr ()
  𝒱-unsubst {A = `∀ A} {v = vTlam} {w = vFalse} sr ()
  𝒱-unsubst {A = `∀ A} {v = vTlam} {w = vZero} sr ()
  𝒱-unsubst {A = `∀ A} {v = vTlam} {w = vSuc w} sr ()
  𝒱-unsubst {A = `∀ A} {v = vTrue} sr ()
  𝒱-unsubst {A = `∀ A} {v = vFalse} sr ()
  𝒱-unsubst {A = `∀ A} {v = vZero} sr ()
  𝒱-unsubst {A = `∀ A} {v = vSuc v} sr ()
  𝒱-unsubst {A = `∀ A} {v = vLam} sr ()

  ℰ-subst :
    ∀ {A σ ρ ρ' M N}
    → SubstRel σ ρ ρ'
    → ℰ A ρ' M N
    → ℰ (substᵗ σ A) ρ M N
  ℰ-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
      , 𝒱-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW
      ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  ℰ-unsubst :
    ∀ {A σ ρ ρ' M N}
    → SubstRel σ ρ ρ'
    → ℰ (substᵗ σ A) ρ M N
    → ℰ A ρ' M N
  ℰ-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
      , 𝒱-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW
      ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

⇑-ℰ : ∀{A A₁ A₂}{ρ}{γ}{R}
  → ℰ A ρ (γ .γ₁ 0) (γ .γ₂ 0)
  → ℰ (renameᵗ suc A) (ρ ,⟨ A₁ , A₂ , R ⟩) (γ .γ₁ 0) (γ .γ₂ 0)
⇑-ℰ {A}{A₁}{A₂}{ρ}{γ}{R} ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ →V , ⟨ →W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ →V , ⟨ →W , 𝒱-rename-wk{A} (wk-suc R) 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩


liftRelEnv-related : ∀ {Γ A₁ A₂} {ρ : RelSub} {γ : RelEnv}
    (R : Rel A₁ A₂)
  → 𝒢 Γ ρ γ
  → 𝒢 (⤊ Γ) (ρ ,⟨ A₁ , A₂ , R ⟩) γ
liftRelEnv-related {[]} R G = tt
liftRelEnv-related {A ∷ Γ} {A₁ = A₁} {A₂ = A₂} {ρ} {γ} R G =
  ⟨ ⇑-ℰ {A = A} {A₁ = A₁} {A₂ = A₂} {ρ = ρ} {γ = γ} {R = R} (G .proj₁)
  , liftRelEnv-related {Γ} {A₁ = A₁} {A₂ = A₂} {ρ = ρ} {γ = ⇓γ γ} R (G .proj₂)
  ⟩

compat-·[] : ∀ {Γ A B}
  → (M : Term)
  → LogicalRel Γ (`∀ A) M M
  → LogicalRel Γ (A [ B ]ᵗ) (M ·[]) (M ·[])
compat-·[] {A = A} {B = B} M M-rel ρ γ env
  with M-rel ρ γ env
... | ⟨ .(Λ N₁) , ⟨ .(Λ N₂) , ⟨ vTlam {N = N₁} , ⟨ vTlam {N = N₂} , ⟨ M₁—↠ΛN₁ , ⟨ M₂—↠ΛN₂ , ∀-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with ∀-rel (substᵗ (ρ₁ ρ) B) (substᵗ (ρ₂ ρ) B) {!𝒱 B ρ!} -- 𝒱 B ρ, Set₁ != Set
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ N₁—↠V , ⟨ N₂—↠W , 𝒱[A]VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨
    multi-trans left-red N₁—↠V
  , ⟨ multi-trans right-red N₂—↠W
  , 𝒱-subst {A} SR 𝒱[A]VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  SR : SubstRel (singleTyEnv B) ρ
       (ρ ,⟨ substᵗ (ρ₁ ρ) B , substᵗ (ρ₂ ρ) B , {!𝒱 B ρ!} ⟩) -- 𝒱 B ρ, Set₁ != Set
  -- Needed here: from rel produce 𝒱 B ρ V W v w.
  -- Blocker: we'd like to instantiate ∀-rel with R = 𝒱 B ρ, but
  -- Rel's codomain is Set₂ while 𝒱 B ρ ... lives in Set₃ (universe mismatch).
  SubstRel.var⇒ SR zero rel = {! rel!} -- rel
  SubstRel.var⇒ SR (suc α) rel = rel
  SubstRel.var⇐ SR zero rel = {!rel!} -- rel
  SubstRel.var⇐ SR (suc α) rel = rel

  ·[]-↠ : ∀ {L L' : Term}
    → L —↠ L'
    → (L ·[]) —↠ (L' ·[])
  ·[]-↠ (L ∎) = (L ·[]) ∎
  ·[]-↠ (L₀ —→⟨ s ⟩ L₀↠L') = (L₀ ·[]) —→⟨ ξ-·[] s ⟩ ·[]-↠ L₀↠L'

  left-red : subst (γ .γ₁) (M ·[]) —↠ N₁
  left-red =
    multi-trans
      (·[]-↠ M₁—↠ΛN₁)
      (((Λ N₁) ·[]) —→⟨ β-Λ {A = substᵗ (ρ₁ ρ) B} ⟩ (N₁ ∎))

  right-red : subst (γ .γ₂) (M ·[]) —↠ N₂
  right-red =
    multi-trans
      (·[]-↠ M₂—↠ΛN₂)
      (((Λ N₂) ·[]) —→⟨ β-Λ {A = substᵗ (ρ₂ ρ) B} ⟩ (N₂ ∎))

compat-Λ : ∀ {Γ A}
  → (N : Term)
  → LogicalRel (⤊ Γ) A N N
  → LogicalRel Γ (`∀ A) (Λ N) (Λ N)
compat-Λ {Γ = Γ} {A = A} N N-rel ρ γ env =
  ⟨ Λ (subst (γ .γ₁) N)
  , ⟨ Λ (subst (γ .γ₂) N)
    , ⟨ vTlam
      , ⟨ vTlam
        , ⟨ Λ (subst (γ .γ₁) N) ∎
          , ⟨ Λ (subst (γ .γ₂) N) ∎
            , LR-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  LR-rel : 𝒱 (`∀ A) ρ (Λ (subst (γ .γ₁) N)) (Λ (subst (γ .γ₂) N)) vTlam vTlam
  LR-rel A₁ A₂ R =
    N-rel (ρ ,⟨ A₁ , A₂ , R ⟩)
      γ
      (liftRelEnv-related {Γ = Γ} {ρ = ρ} {γ = γ} R env)

--------------------------------------------------------------------------------
-- Fundamental Theorem
--------------------------------------------------------------------------------

fundamental : ∀ {Δ Γ A} (M : Term) → Δ ⊢ Γ ⊢ M ⦂ A → LogicalRel Γ A M M
fundamental _ (⊢` x) = compat-var x
fundamental _ (⊢ƛ {A = A} {B = B} {N = N} _ dN) =
  compat-ƛ {A = A} {B = B} N (fundamental N dN)
fundamental _ (⊢· {A = A} {B = B} {L = L} {M = M} dL dM) =
  compat-· {A = A} {B = B} L M
    (fundamental L dL)
    (fundamental M dM)
fundamental _ ⊢true = compat-true
fundamental _ ⊢false = compat-false
fundamental _ ⊢zero = compat-zero
fundamental _ (⊢suc {M = M} dM) =
  compat-suc M (fundamental M dM)
fundamental _ (⊢case {A = A} {L = L} {M = M} {N = N} dL dM dN) =
  compat-case {A = A} L M N
    (fundamental L dL)
    (fundamental M dM)
    (fundamental N dN)
fundamental _ (⊢if {A = A} {L = L} {M = M} {N = N} dL dM dN) =
  compat-if {A = A} L M N
    (fundamental L dL)
    (fundamental M dM)
    (fundamental N dN)
fundamental _ (⊢Λ {N = N} dN) =
  compat-Λ N (fundamental N dN)
fundamental _ (⊢·[] {M = M} dM _) =
  compat-·[] M (fundamental M dM)
