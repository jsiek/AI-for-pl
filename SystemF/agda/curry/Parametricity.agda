{-# OPTIONS --cumulativity --omega-in-omega #-}
module curry.Parametricity where

-- File Charter:
--   * Proves compatibility lemmas for the curry logical relation.
--   * Derives the fundamental theorem of logical relations.
--   * Relies on `curry.LogicalRelation` for relation definitions and helpers.

-- The --cumulativity and --omega-in-omega flags are needed in the
-- LogicalRelation module imported below and in the proof of compat-·[]. -Jeremy

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; _<_; zero; suc)
open import curry.ProductOmega using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)

open import curry.Terms
open import curry.Reduction
open import curry.LogicalRelation


--------------------------------------------------------------------------------
-- Compatibility Lemmas
--------------------------------------------------------------------------------

compat-· : ∀ {Γ A B}
  → (L M : Term)
  → Γ ⊨ L ≈ L ⦂ (A ⇒ B)
  → Γ ⊨ M ≈ M ⦂ A
  → Γ ⊨ (L · M) ≈ (L · M) ⦂ B
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
        , ⟨   subst (γ .left) (L · M)
            —↠⟨ left-red ⟩
              N [ V ]
            —↠⟨ redL' ⟩
               V'
            ∎
          , ⟨ subst (γ .right) (L · M)
            —↠⟨ right-red ⟩
              P [ W ]
            —↠⟨ redR' ⟩
              W'
            ∎
            , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  left-red : subst (γ .left) (L · M) —↠ N [ V ]
  left-red = subst (γ .left) (L · M)
           —↠⟨ app-↠ {L = subst (γ .left) L} {L' = ƛ N}
                     {M = subst (γ .left) M} {M' = V}
                     L₁—↠V vLam M₁—↠V ⟩
             (ƛ N) · V
           —↠⟨ β-ƛ-↠ vV ⟩
             (N [ V ])
           ∎

  right-red : subst (γ .right) (L · M) —↠ P [ W ]
  right-red = subst (γ .right) (L · M)
            —↠⟨ app-↠ {L = subst (γ .right) L} {L' = ƛ P}
                      {M = subst (γ .right) M} {M' = W}
                      L₂—↠W vLam M₂—↠W ⟩
              (ƛ P) · W
            —↠⟨ β-ƛ-↠ vW ⟩
              P [ W ]
            ∎

compat-true : ∀ {Γ}
  → Γ ⊨ `true ≈ `true ⦂ `Bool
compat-true ρ γ env =
  𝒱⇒ℰ {A = `Bool} {ρ = ρ} {V = `true} {W = `true} vTrue vTrue tt

compat-suc : ∀ {Γ}
  → (M : Term)
  → Γ ⊨ M ≈ M ⦂ `ℕ
  → Γ ⊨ (`suc M) ≈ (`suc M) ⦂ `ℕ
compat-suc M M-rel ρ γ env with M-rel ρ γ env
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M₁—↠V , ⟨ M₂—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ `suc V
  , ⟨ `suc W
    , ⟨ vSuc v
      , ⟨ vSuc w
        , ⟨ suc-↠ M₁—↠V
          , ⟨ suc-↠ M₂—↠W
            , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

compat-case : ∀ {Γ A}
  → (L M N : Term)
  → Γ ⊨ L ≈ L ⦂ `ℕ
  → Γ ⊨ M ≈ M ⦂ A
  → (`ℕ ∷ Γ) ⊨ N ≈ N ⦂ A
  → Γ ⊨ (case_[zero⇒_|suc⇒_] L M N) ≈ (case_[zero⇒_|suc⇒_] L M N) ⦂ A
compat-case {Γ = Γ} {A = A} L M N L-rel M-rel N-rel ρ γ env =
  go {L₀ = L} (L-rel ρ γ env)
  where
  go : ∀ {L₀ : Term}
    → ℰ `ℕ ρ (subst (γ .left) L₀) (subst (γ .right) L₀)
    → ℰ A ρ
        (subst (γ .left) (case_[zero⇒_|suc⇒_] L₀ M N))
        (subst (γ .right) (case_[zero⇒_|suc⇒_] L₀ M N))
  go {L₀ = L₀} ⟨ `zero , ⟨ `zero , ⟨ vZero , ⟨ vZero , ⟨ L₁—↠0 , ⟨ L₂—↠0 , tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with M-rel ρ γ env
  ... | ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ M₁—↠V' , ⟨ M₂—↠W' , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V'
    , ⟨ W'
      , ⟨ v'
        , ⟨ w'
          , ⟨ left-zero-red
            , ⟨ right-zero-red
              , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    left-zero-red :
      subst (γ .left) (case_[zero⇒_|suc⇒_] L₀ M N) —↠ V'
    left-zero-red =
         (subst (γ .left) (case_[zero⇒_|suc⇒_] L₀ M N))
       —↠⟨ case-↠ {M = subst (γ .left) M} {N = subst (exts (γ .left)) N} L₁—↠0 ⟩
         (case_[zero⇒_|suc⇒_] `zero (subst (γ .left) M) (subst (exts (γ .left)) N))
       —↠⟨ case-zero-↠ ⟩
         (subst (γ .left) M)
       —↠⟨ M₁—↠V' ⟩
         V'
       ∎

    right-zero-red :
      subst (γ .right) (case_[zero⇒_|suc⇒_] L₀ M N) —↠ W'
    right-zero-red =
        (subst (γ .right) (case_[zero⇒_|suc⇒_] L₀ M N))
      —↠⟨ case-↠ {M = subst (γ .right) M} {N = subst (exts (γ .right)) N} L₂—↠0 ⟩
        (case_[zero⇒_|suc⇒_] `zero (subst (γ .right) M) (subst (exts (γ .right)) N))
      —↠⟨ case-zero-↠ ⟩
        (subst (γ .right) M)
      —↠⟨ M₂—↠W' ⟩
        W'
      ∎

  go {L₀ = L₀} ⟨ `suc V , ⟨ `suc W , ⟨ vSuc vV , ⟨ vSuc wW , ⟨ L₁—↠sV , ⟨ L₂—↠sW , vw-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with N-rel ρ (γ ,⟨ V , W ⟩)
         (⟨ 𝒱⇒ℰ {A = `ℕ} {ρ = ρ} {V = V} {W = W} vV wW vw-rel , env ⟩)
  ... | ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ N₁—↠V' , ⟨ N₂—↠W' , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V'
    , ⟨ W'
      , ⟨ v'
        , ⟨ w'
          , ⟨ left-suc-red
            , ⟨ right-suc-red
              , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    case-suc : ∀ {σ : Subst} {U : Term}
      → Value U
      → case_[zero⇒_|suc⇒_] (`suc U) (subst σ M) (subst (exts σ) N)
        —↠ subst (U • σ) N
    case-suc {σ} {U} vU =
      substEq
        (case_[zero⇒_|suc⇒_] (`suc U) (subst σ M) (subst (exts σ) N) —↠_)
        (exts-sub-cons σ N U)
        ((case_[zero⇒_|suc⇒_] (`suc U) (subst σ M) (subst (exts σ) N))
          —→⟨ β-suc vU ⟩
            ((subst (exts σ) N) [ U ])
          ∎)

    left-suc-red :
      subst (γ .left) (case_[zero⇒_|suc⇒_] L₀ M N) —↠ V'
    left-suc-red =
        (subst (γ .left) (case_[zero⇒_|suc⇒_] L₀ M N))
      —↠⟨ case-↠ {M = subst (γ .left) M} {N = subst (exts (γ .left)) N} L₁—↠sV ⟩
        (case_[zero⇒_|suc⇒_] (`suc V) (subst (γ .left) M) (subst (exts (γ .left)) N))
      —↠⟨ case-suc {σ = γ .left} vV ⟩
        (subst (V • (γ .left)) N)
      —↠⟨ N₁—↠V' ⟩
        V'
      ∎

    right-suc-red :
      subst (γ .right) (case_[zero⇒_|suc⇒_] L₀ M N) —↠ W'
    right-suc-red =
        (subst (γ .right) (case_[zero⇒_|suc⇒_] L₀ M N))
      —↠⟨ case-↠ {M = subst (γ .right) M} {N = subst (exts (γ .right)) N} L₂—↠sW ⟩
        (case_[zero⇒_|suc⇒_] (`suc W) (subst (γ .right) M) (subst (exts (γ .right)) N))
      —↠⟨ case-suc {σ = γ .right} wW ⟩
        (subst (W • (γ .right)) N)
      —↠⟨ N₂—↠W' ⟩
        W'
      ∎

compat-zero : ∀ {Γ}
  → Γ ⊨ `zero ≈ `zero ⦂ `ℕ
compat-zero ρ γ env = 𝒱⇒ℰ {A = `ℕ} {V = `zero} {W = `zero} vZero vZero tt

compat-ƛ : ∀ {Γ A B}
  → (N : Term)
  → (A ∷ Γ) ⊨ N ≈ N ⦂ B
  → Γ ⊨ (ƛ N) ≈ (ƛ N) ⦂ (A ⇒ B)
compat-ƛ {A = A} {B = B} N N-rel ρ γ env =
  ⟨ subst (γ .left) (ƛ N)
  , ⟨ subst (γ .right) (ƛ N)
    , ⟨ vLam
      , ⟨ vLam
        , ⟨ subst (γ .left) (ƛ N) ∎
          , ⟨ subst (γ .right) (ƛ N) ∎
            , LR-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  β-subst₁ : ∀ {V}
    → subst (exts (γ .left)) N [ V ] ≡ subst (V • (γ .left)) N
  β-subst₁ {V} = exts-sub-cons (γ .left) N V

  β-subst₂ : ∀ {W}
    → subst (exts (γ .right)) N [ W ] ≡ subst (W • (γ .right)) N
  β-subst₂ {W} = exts-sub-cons (γ .right) N W

  LR-rel : 𝒱 (A ⇒ B) ρ (subst (γ .left) (ƛ N)) (subst (γ .right) (ƛ N)) vLam vLam
  LR-rel {V} {W} v w VW-rel
    rewrite β-subst₁ {V = V}
          | β-subst₂ {W = W} =
    N-rel ρ (γ ,⟨ V , W ⟩) (𝒢-extend {A = A} env v w VW-rel)

compat-false : ∀ {Γ}
  → Γ ⊨ `false ≈ `false ⦂ `Bool
compat-false ρ γ env =
  𝒱⇒ℰ {A = `Bool} {ρ = ρ} {V = `false} {W = `false} vFalse vFalse tt

compat-if : ∀ {Γ A}
  → (L M N : Term)
  → Γ ⊨ L ≈ L ⦂ `Bool
  → Γ ⊨ M ≈ M ⦂ A
  → Γ ⊨ N ≈ N ⦂ A
  → Γ ⊨ (`if_then_else L M N) ≈ (`if_then_else L M N) ⦂ A
compat-if {A = A} L M N L-rel M-rel N-rel ρ γ env
  with L-rel ρ γ env | M-rel ρ γ env | N-rel ρ γ env
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ L₁—↠V , ⟨ L₂—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ M₁—↠V' , ⟨ M₂—↠W' , relM ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ V'' , ⟨ W'' , ⟨ v'' , ⟨ w'' , ⟨ N₁—↠V'' , ⟨ N₂—↠W'' , relN ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with v | w | VW-rel
... | vTrue | vTrue | tt =
  ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨
        (`if_then_else (subst (γ .left) L) (subst (γ .left) M) (subst (γ .left) N))
      —↠⟨ if-true-↠ {M = subst (γ .left) M} {N = subst (γ .left) N} L₁—↠V ⟩
        (subst (γ .left) M)
      —↠⟨ M₁—↠V' ⟩
        V'
    ∎
    , ⟨ (`if_then_else (subst (γ .right) L) (subst (γ .right) M) (subst (γ .right) N))
      —↠⟨ if-true-↠ {M = subst (γ .right) M} {N = subst (γ .right) N} L₂—↠W ⟩
        (subst (γ .right) M)
      —↠⟨ M₂—↠W' ⟩
        W'
      ∎
      , relM ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
... | vFalse | vFalse | tt =
  ⟨ V'' , ⟨ W'' , ⟨ v'' , ⟨ w'' , ⟨
      (`if_then_else (subst (γ .left) L) (subst (γ .left) M) (subst (γ .left) N))
    —↠⟨ if-false-↠ {M = subst (γ .left) M} {N = subst (γ .left) N} L₁—↠V ⟩
      (subst (γ .left) N)
    —↠⟨ N₁—↠V'' ⟩
      V''
    ∎
    , ⟨ (`if_then_else (subst (γ .right) L) (subst (γ .right) M) (subst (γ .right) N))
      —↠⟨ if-false-↠ {M = subst (γ .right) M} {N = subst (γ .right) N} L₂—↠W ⟩
        (subst (γ .right) N)
      —↠⟨ N₂—↠W'' ⟩
        W''
      ∎
      , relN ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
... | vTrue | vFalse | ()
... | vFalse | vTrue | ()

compat-var : ∀ {Γ A x} → Γ ∋ x ⦂ A → Γ ⊨ (` x) ≈ (` x) ⦂ A
compat-var Z ρ γ env = proj₁ env
compat-var (S x) ρ γ env = compat-var x ρ (⇓γ γ) (proj₂ env)



compat-·[] : ∀ {Γ A B}
  → (M : Term)
  → Γ ⊨ M ≈ M ⦂ (`∀ A)
  → Γ ⊨ (M ·[]) ≈ (M ·[]) ⦂ (A [ B ]ᵗ)
compat-·[] {A = A} {B = B} M M-rel ρ γ env
  with M-rel ρ γ env
... | ⟨ .(Λ N₁) , ⟨ .(Λ N₂) , ⟨ vTlam {N = N₁} , ⟨ vTlam {N = N₂} , ⟨ M₁—↠ΛN₁ , ⟨ M₂—↠ΛN₂ , ∀-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with ∀-rel (substᵗ (left ρ) B) (substᵗ (right ρ) B) (𝒱 B ρ) -- omega-in-omega needed here
... | ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ N₁—↠V , ⟨ N₂—↠W , 𝒱[A]VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨
      (subst (γ .left) (M ·[]))
    —↠⟨ left-red ⟩
      N₁
    —↠⟨ N₁—↠V ⟩
    V
    ∎
  , ⟨ (subst (γ .right) (M ·[]))
    —↠⟨ right-red ⟩
      N₂
    —↠⟨ N₂—↠W ⟩
      W
    ∎
  , 𝒱-subst {A} SR 𝒱[A]VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  SR : SubstRel (singleTyEnv B) ρ
       (ρ ,⟨ substᵗ (left ρ) B , substᵗ (right ρ) B , 𝒱 B ρ ⟩) -- omega-in-omega needed here
  SubstRel.var⇒ SR zero rel =  rel
  SubstRel.var⇒ SR (suc α) rel = rel
  SubstRel.var⇐ SR zero rel = rel
  SubstRel.var⇐ SR (suc α) rel = rel

  left-red : subst (γ .left) (M ·[]) —↠ N₁
  left-red = (subst (γ .left) (M ·[]))
           —↠⟨ ·[]-↠ M₁—↠ΛN₁ ⟩
             ((Λ N₁) ·[])
           —↠⟨ β-Λ-↠ {A = substᵗ (left ρ) B} ⟩
           N₁
           ∎

  right-red : subst (γ .right) (M ·[]) —↠ N₂
  right-red = (subst (γ .right) (M ·[]))
            —↠⟨ ·[]-↠ M₂—↠ΛN₂ ⟩
              ((Λ N₂) ·[])
            —↠⟨ β-Λ-↠ {A = substᵗ (right ρ) B} ⟩
              N₂
            ∎

compat-Λ : ∀ {Γ A}
  → (N : Term)
  → (⤊ Γ) ⊨ N ≈ N ⦂ A
  → Γ ⊨ (Λ N) ≈ (Λ N) ⦂ (`∀ A)
compat-Λ {Γ = Γ} {A = A} N N-rel ρ γ env =
  ⟨ Λ (subst (γ .left) N)
  , ⟨ Λ (subst (γ .right) N)
    , ⟨ vTlam
      , ⟨ vTlam
        , ⟨ Λ (subst (γ .left) N) ∎
          , ⟨ Λ (subst (γ .right) N) ∎
            , LR-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  LR-rel : 𝒱 (`∀ A) ρ (Λ (subst (γ .left) N)) (Λ (subst (γ .right) N)) vTlam vTlam
  LR-rel A₁ A₂ R =
    N-rel (ρ ,⟨ A₁ , A₂ , R ⟩)
      γ
      (liftRelEnv-related {Γ = Γ} {ρ = ρ} {γ = γ} R env)

--------------------------------------------------------------------------------
-- Fundamental Theorem
--------------------------------------------------------------------------------

fundamental : ∀ {Δ Γ A} (M : Term) → Δ ⊢ Γ ⊢ M ⦂ A → Γ ⊨ M ≈ M ⦂ A
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
