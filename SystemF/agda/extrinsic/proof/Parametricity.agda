{-# OPTIONS --cumulativity --omega-in-omega #-}
module extrinsic.proof.Parametricity where

-- File Charter:
--   * Proves compatibility lemmas for the extrinsic logical relation.
--   * Derives the fundamental theorem of logical relations.
--   * Relies on `extrinsic.LogicalRelation` for relation definitions and helpers.

-- The --cumulativity and --omega-in-omega flags are needed in the
-- LogicalRelation module imported below and in the proof of compat-·[]. -Jeremy

open import Relation.Binary.PropositionalEquality as Eq
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
module EqR = Eq.≡-Reasoning
open import Agda.Builtin.Sigma using (fst; snd)
open import Data.List using (_∷_; []; map)
open import Data.Product as DP using (proj₁; proj₂)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import extrinsic.ProductOmega using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)

open import extrinsic.Terms
open import extrinsic.TypeSubst using (subst-[]ᵗ-commute)
open import extrinsic.TermSubst using (subst-cong; exts-sub-cons; subst-cong-typed)
open import extrinsic.TypeTermSubst using
  (cong₃; substᵀ-renameᵀ-commute; substᵀ-subst-commute; substᵀ-substᵀ; singleTyEnv-suc-cancel; singleTyEnv-suc-cancelᵗ; substᵀ-cong
  ; substᵀ-id-typed; substᵗ-id-typed)
open import extrinsic.Ctx using (lookup-map-inv; lookup-map-substᵗ)
open import extrinsic.Preservation
  using
    ( SubstWf; TySubstWf; TySubstWf-exts; SubstWf-⇑
    ; typing-subst; typing-substᵀ; typing-rename-shift
    ; map-substᵗ-⤊)
open import extrinsic.Reduction
open import extrinsic.LogicalRelation

𝒢-left-SubstWf : ∀ {Γ ρ γ}
  → 𝒢 Γ ρ γ
  → SubstWf zero (map (substᵗ (left ρ)) Γ) [] (left γ)
𝒢-left-SubstWf {Γ = []} env ()
𝒢-left-SubstWf {Γ = A ∷ Γ} env Z = proj₁ (proj₁ env)
𝒢-left-SubstWf {Γ = A ∷ Γ} env (S x) =
  𝒢-left-SubstWf {Γ = Γ} (proj₂ env) x

𝒢-right-SubstWf : ∀ {Γ ρ γ}
  → 𝒢 Γ ρ γ
  → SubstWf zero (map (substᵗ (right ρ)) Γ) [] (right γ)
𝒢-right-SubstWf {Γ = []} env ()
𝒢-right-SubstWf {Γ = A ∷ Γ} env Z = proj₁ (proj₂ (proj₁ env))
𝒢-right-SubstWf {Γ = A ∷ Γ} env (S x) =
  𝒢-right-SubstWf {Γ = Γ} (proj₂ env) x

TySubstWf-zero : ∀ {σ} → TySubstWf zero zero σ
TySubstWf-zero ()


--------------------------------------------------------------------------------
-- Compatibility Lemmas
--------------------------------------------------------------------------------

compat-var : ∀ {Γ A x}
   → Γ ∋ x ⦂ A
   → Γ ⊨ (` x) ≈ (` x) ⦂ A
compat-var {A = A} Z ρ γ env =
  ℰ-close-ρ {A = A} {ρ = ρ} {M = γ .left 0} {N = γ .right 0} (proj₁ env)
compat-var (S x) ρ γ env = compat-var x ρ (⇓γ γ) (proj₂ env)

compat-· : ∀ {Γ A B}
  → (L M : Term)
  → Γ ⊨ L ≈ L ⦂ (A ⇒ B)
  → Γ ⊨ M ≈ M ⦂ A
  → Γ ⊨ (L · M) ≈ (L · M) ⦂ B
compat-· {Γ = Γ} {A = A} {B = B} L M L-rel M-rel ρ γ env
    with L-rel ρ γ env | M-rel ρ γ env
... | ⟨ ⊢L , ⟨ ⊢L' , ⟨ .(ƛ[ _ ] N) , ⟨ .(ƛ[ _ ] P) , ⟨ vLam {N = N} , ⟨ vLam {N = P} , ⟨ L₁—↠V , ⟨ L₂—↠W , f-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ ⊢M , ⟨ ⊢M' , ⟨ V , ⟨ W , ⟨ vV , ⟨ vW , ⟨ M₁—↠V , ⟨ M₂—↠W , arg-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with (proj₂ (proj₂ f-rel)) vV vW arg-rel
... | ⟨ _ , ⟨ _ , ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ N[V]-↠V' , ⟨ P[W]-↠W' , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ ⊢· ⊢L ⊢M
  , ⟨ ⊢· ⊢L' ⊢M'
    , ⟨ V'
      , ⟨ W'
        , ⟨ v'
          , ⟨ w'
            , ⟨   substᵀ (left ρ) (subst (γ .left) (L · M))
                —↠⟨ app-↠ L₁—↠V vLam M₁—↠V ⟩
                  (ƛ[ _ ] N) · V
                —↠⟨ β-ƛ-↠ vV ⟩
                  N [ V ]
                —↠⟨ N[V]-↠V' ⟩
                   V'
                ∎
              , ⟨ substᵀ (right ρ) (subst (γ .right) (L · M))
                —↠⟨ app-↠ L₂—↠W vLam M₂—↠W ⟩
                  (ƛ[ _ ] P) · W
                —↠⟨ β-ƛ-↠ vW ⟩
                  P [ W ]
                —↠⟨ P[W]-↠W' ⟩
                  W'
                ∎
                , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

compat-ƛ : ∀ {Δ Γ A B}
  → (N : Term)
  → Δ ∣ (A ∷ Γ) ⊢ N ⦂ B
  → (A ∷ Γ) ⊨ N ≈ N ⦂ B
  → Γ ⊨ (ƛ[ A ] N) ≈ (ƛ[ A ] N) ⦂ (A ⇒ B)
compat-ƛ {Δ = Δ} {Γ = Γ} {A = A} {B = B} N ⊢N N-rel ρ γ env =
  ⟨ left-typed
  , ⟨ right-typed
    , ⟨ substᵀ (left ρ) (subst (γ .left) (ƛ[ A ] N))
      , ⟨ substᵀ (right ρ) (subst (γ .right) (ƛ[ A ] N))
        , ⟨ vLam
          , ⟨ vLam
            , ⟨ substᵀ (left ρ) (subst (γ .left) (ƛ[ A ] N)) ∎
              , ⟨ substᵀ (right ρ) (subst (γ .right) (ƛ[ A ] N)) ∎
                , LR-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  
  -- Proof that substᵀ (left ρ) (subst (γ .left) (ƛ[ A ] N)) is well typed

  left-TySubstWf : TySubstWf Δ zero (left ρ)
  left-TySubstWf {X} X<Δ = left-closed ρ X

  left-SubstWf-ext :
    SubstWf zero
      (map (substᵗ (left ρ)) (A ∷ Γ))
      (substᵗ (left ρ) A ∷ [])
      (λ i → substᵀ (left ρ) (exts (γ .left) i))
  left-SubstWf-ext Z = ⊢` Z
  left-SubstWf-ext {x = suc x} {A = C} (S h) =
    substEq
      (λ Tm → zero ∣ (substᵗ (left ρ) A ∷ []) ⊢ Tm ⦂ C)
      (sym (substᵀ-id-typed (λ ()) shifted))
      shifted
    where
    shifted = typing-rename-shift (𝒢-left-SubstWf env h)

  left-body-typed : zero ∣ (substᵗ (left ρ) A ∷ [])
    ⊢ substᵀ (left ρ) (subst (exts (γ .left)) N) ⦂ substᵗ (left ρ) B
  left-body-typed =
    substEq
      (λ Tm → zero ∣ (substᵗ (left ρ) A ∷ []) ⊢ Tm ⦂ substᵗ (left ρ) B)
      (sym (substᵀ-subst-commute (left ρ) (exts (γ .left)) N))
      (typing-subst
        left-SubstWf-ext
        (typing-substᵀ left-TySubstWf ⊢N))

  left-typed :
    zero ∣ [] ⊢ substᵀ (left ρ) (subst (γ .left) (ƛ[ A ] N)) ⦂ substᵗ (left ρ) (A ⇒ B)
  left-typed =
    ⊢ƛ (substᵗ-codom-closed (left ρ) (left-closed ρ) A)
       left-body-typed

  -- Proof that substᵀ (right ρ) (subst (γ .right) (ƛ[ A ] N)) is well typed

  right-TySubstWf : TySubstWf Δ zero (right ρ)
  right-TySubstWf {X} X<Δ = right-closed ρ X

  right-SubstWf-ext :
    SubstWf zero
      (map (substᵗ (right ρ)) (A ∷ Γ))
      (substᵗ (right ρ) A ∷ [])
      (λ i → substᵀ (right ρ) (exts (γ .right) i))
  right-SubstWf-ext Z = ⊢` Z
  right-SubstWf-ext {x = suc x} {A = C} (S h) =
    substEq
      (λ Tm → zero ∣ (substᵗ (right ρ) A ∷ []) ⊢ Tm ⦂ C)
      (sym (substᵀ-id-typed (λ ()) shifted))
      shifted
    where
    shifted = typing-rename-shift (𝒢-right-SubstWf env h)

  right-body-typed : zero ∣ (substᵗ (right ρ) A ∷ [])
    ⊢ substᵀ (right ρ) (subst (exts (γ .right)) N) ⦂ substᵗ (right ρ) B
  right-body-typed =
    substEq
      (λ Tm → zero ∣ (substᵗ (right ρ) A ∷ []) ⊢ Tm ⦂ substᵗ (right ρ) B)
      (sym (substᵀ-subst-commute (right ρ) (exts (γ .right)) N))
      (typing-subst
        right-SubstWf-ext
        (typing-substᵀ right-TySubstWf ⊢N))

  right-typed :
    zero ∣ [] ⊢ substᵀ (right ρ) (subst (γ .right) (ƛ[ A ] N))
      ⦂ substᵗ (right ρ) (A ⇒ B)
  right-typed =
    ⊢ƛ
      (substᵗ-codom-closed (right ρ) (right-closed ρ) A)
      right-body-typed

  -- Proof that 𝒱 (A ⇒ B) ρ (ρ.left (γ.left (ƛ[ A ] N))) (ρ.right (γ.right (ƛ[ A ] N)))

  LR-rel : 𝒱 (A ⇒ B) ρ
    (substᵀ (left ρ) (subst (γ .left) (ƛ[ A ] N)))
    (substᵀ (right ρ) (subst (γ .right) (ƛ[ A ] N)))
    vLam vLam
  LR-rel = ⟨ left-typed , ⟨ right-typed , body ⟩ ⟩
    where
    left-V-id : ∀ {V W} {v : Value V} {w : Value W}
      → 𝒱 A ρ V W v w
      → substᵀ (left ρ) V ≡ V
    left-V-id {V} {W} {v} {w} VW-rel
      with 𝒱-typing {A = A} {ρ = ρ} {V = V} {W = W} {v = v} {w = w} VW-rel
    ... | ⟨ ⊢V , _ ⟩ = substᵀ-id-typed (λ ()) ⊢V

    right-W-id : ∀ {V W} {v : Value V} {w : Value W}
      → 𝒱 A ρ V W v w
      → substᵀ (right ρ) W ≡ W
    right-W-id {V} {W} {v} {w} VW-rel
      with 𝒱-typing {A = A} {ρ = ρ} {V = V} {W = W} {v = v} {w = w} VW-rel
    ... | ⟨ _ , ⊢W ⟩ = substᵀ-id-typed (λ ()) ⊢W

    left-singleEnv-close : ∀ {V W} {v : Value V} {w : Value W}
      → (VW-rel : 𝒱 A ρ V W v w)
      → (i : Var)
      → substᵀ (left ρ) (singleEnv V i) ≡ singleEnv V i
    left-singleEnv-close VW-rel zero = left-V-id VW-rel
    left-singleEnv-close VW-rel (suc i) = refl

    right-singleEnv-close : ∀ {V W} {v : Value V} {w : Value W}
      → (VW-rel : 𝒱 A ρ V W v w)
      → (i : Var)
      → substᵀ (right ρ) (singleEnv W i) ≡ singleEnv W i
    right-singleEnv-close VW-rel zero = right-W-id VW-rel
    right-singleEnv-close VW-rel (suc i) = refl

    left-β-bridge : ∀ {V W} {v : Value V} {w : Value W}
      → (VW-rel : 𝒱 A ρ V W v w)
      → ((substᵀ (left ρ) (subst (exts (γ .left)) N)) [ V ])
        ≡ substᵀ (left ρ) (subst (V • (γ .left)) N)
    left-β-bridge {V} {W} {v} {w} VW-rel =
      EqR.begin
        ((substᵀ (left ρ) (subst (exts (γ .left)) N)) [ V ])
      EqR.≡⟨ sym (subst-cong (left-singleEnv-close VW-rel) (substᵀ (left ρ) (subst (exts (γ .left)) N))) ⟩
        subst (λ i → substᵀ (left ρ) (singleEnv V i)) (substᵀ (left ρ) (subst (exts (γ .left)) N))
      EqR.≡⟨ sym (substᵀ-subst-commute (left ρ) (singleEnv V) (subst (exts (γ .left)) N)) ⟩
        substᵀ (left ρ) (subst (singleEnv V) (subst (exts (γ .left)) N))
      EqR.≡⟨ cong (substᵀ (left ρ)) (exts-sub-cons (γ .left) N V) ⟩
        substᵀ (left ρ) (subst (V • (γ .left)) N)
      EqR.∎

    right-β-bridge : ∀ {V W} {v : Value V} {w : Value W}
      → (VW-rel : 𝒱 A ρ V W v w)
      → ((substᵀ (right ρ) (subst (exts (γ .right)) N)) [ W ])
        ≡ substᵀ (right ρ) (subst (W • (γ .right)) N)
    right-β-bridge {V} {W} {v} {w} VW-rel =
      EqR.begin
        ((substᵀ (right ρ) (subst (exts (γ .right)) N)) [ W ])
      EqR.≡⟨ sym (subst-cong (right-singleEnv-close VW-rel) (substᵀ (right ρ) (subst (exts (γ .right)) N))) ⟩
        subst (λ i → substᵀ (right ρ) (singleEnv W i)) (substᵀ (right ρ) (subst (exts (γ .right)) N))
      EqR.≡⟨ sym (substᵀ-subst-commute (right ρ) (singleEnv W) (subst (exts (γ .right)) N)) ⟩
        substᵀ (right ρ) (subst (singleEnv W) (subst (exts (γ .right)) N))
      EqR.≡⟨ cong (substᵀ (right ρ)) (exts-sub-cons (γ .right) N W) ⟩
        substᵀ (right ρ) (subst (W • (γ .right)) N)
      EqR.∎

    body : ∀ {V W} (v : Value V) (w : Value W)
      → 𝒱 A ρ V W v w
      → ℰ B ρ ((substᵀ (left ρ) (subst (exts (γ .left)) N)) [ V ])
              ((substᵀ (right ρ) (subst (exts (γ .right)) N)) [ W ])
    body {V} {W} v w VW-rel
      with N-rel ρ (γ ,⟨ V , W ⟩) (𝒢-extend {A = A} env v w VW-rel)
    ... | ⟨ ⊢L , ⟨ ⊢R , ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ redL , ⟨ redR , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ substEq
          (λ Tm → zero ∣ [] ⊢ Tm ⦂ substᵗ (left ρ) B)
          (sym (left-β-bridge VW-rel))
          ⊢L
      , ⟨ substEq
            (λ Tm → zero ∣ [] ⊢ Tm ⦂ substᵗ (right ρ) B)
            (sym (right-β-bridge VW-rel))
            ⊢R
        , ⟨ V'
          , ⟨ W'
            , ⟨ v'
              , ⟨ w'
                , ⟨ substEq (λ Tm → Tm —↠ V') (sym (left-β-bridge VW-rel)) redL
                  , ⟨ substEq (λ Tm → Tm —↠ W') (sym (right-β-bridge VW-rel)) redR
                    , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

compat-true : ∀ {Γ} → Γ ⊨ `true ≈ `true ⦂ `Bool
compat-true ρ γ env =  𝒱⇒ℰ {A = `Bool} {ρ = ρ} vTrue vTrue tt

compat-false : ∀ {Γ}
  → Γ ⊨ `false ≈ `false ⦂ `Bool
compat-false ρ γ env = 𝒱⇒ℰ {A = `Bool} {ρ = ρ} vFalse vFalse tt

compat-zero : ∀ {Γ}
  → Γ ⊨ `zero ≈ `zero ⦂ `ℕ
compat-zero ρ γ env = 𝒱⇒ℰ {A = `ℕ} {V = `zero} {W = `zero} vZero vZero tt

compat-suc : ∀ {Γ} (M : Term)
  → Γ ⊨ M ≈ M ⦂ `ℕ
  → Γ ⊨ (`suc M) ≈ (`suc M) ⦂ `ℕ
compat-suc M M-rel ρ γ env
    with M-rel ρ γ env
... | ⟨ ⊢M , ⟨ ⊢M' , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M₁—↠V , ⟨ M₂—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ ⊢suc ⊢M
  , ⟨ ⊢suc ⊢M'
    , ⟨ `suc V
      , ⟨ `suc W
        , ⟨ vSuc v
          , ⟨ vSuc w
            , ⟨ suc-↠ M₁—↠V
              , ⟨ suc-↠ M₂—↠W
                , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

compat-case : ∀ {Δ Γ A}
  → (L M N : Term)
  → Δ ∣ (`ℕ ∷ Γ) ⊢ N ⦂ A
  → Γ ⊨ L ≈ L ⦂ `ℕ
  → Γ ⊨ M ≈ M ⦂ A
  → (`ℕ ∷ Γ) ⊨ N ≈ N ⦂ A
  → Γ ⊨ (case_[zero⇒_|suc⇒_] L M N) ≈ (case_[zero⇒_|suc⇒_] L M N) ⦂ A
compat-case {Δ = Δ} {Γ = Γ} {A = A} L M N ⊢N L-rel M-rel N-rel ρ γ env =
  go {L₀ = L} (L-rel ρ γ env)
  where
  left-TySubstWf : TySubstWf Δ zero (left ρ)
  left-TySubstWf {X} X<Δ = left-closed ρ X

  right-TySubstWf : TySubstWf Δ zero (right ρ)
  right-TySubstWf {X} X<Δ = right-closed ρ X

  left-SubstWf-ext :
    SubstWf zero
      (map (substᵗ (left ρ)) (`ℕ ∷ Γ))
      (`ℕ ∷ [])
      (λ i → substᵀ (left ρ) (exts (γ .left) i))
  left-SubstWf-ext Z = ⊢` Z
  left-SubstWf-ext {x = suc x} {A = C} (S h) =
    substEq
      (λ Tm → zero ∣ (`ℕ ∷ []) ⊢ Tm ⦂ C)
      (sym (substᵀ-id-typed (λ ()) shifted))
      shifted
    where
    shifted : zero ∣ (`ℕ ∷ []) ⊢ rename suc (γ .left x) ⦂ C
    shifted = typing-rename-shift (𝒢-left-SubstWf env h)

  right-SubstWf-ext :
    SubstWf zero
      (map (substᵗ (right ρ)) (`ℕ ∷ Γ))
      (`ℕ ∷ [])
      (λ i → substᵀ (right ρ) (exts (γ .right) i))
  right-SubstWf-ext Z = ⊢` Z
  right-SubstWf-ext {x = suc x} {A = C} (S h) =
    substEq
      (λ Tm → zero ∣ (`ℕ ∷ []) ⊢ Tm ⦂ C)
      (sym (substᵀ-id-typed (λ ()) shifted))
      shifted
    where
    shifted : zero ∣ (`ℕ ∷ []) ⊢ rename suc (γ .right x) ⦂ C
    shifted = typing-rename-shift (𝒢-right-SubstWf env h)

  left-N-open-typed :
    zero ∣ (`ℕ ∷ []) ⊢ substᵀ (left ρ) (subst (exts (γ .left)) N) ⦂ substᵗ (left ρ) A
  left-N-open-typed =
    substEq
      (λ Tm → zero ∣ (`ℕ ∷ []) ⊢ Tm ⦂ substᵗ (left ρ) A)
      (sym (substᵀ-subst-commute (left ρ) (exts (γ .left)) N))
      (typing-subst
        left-SubstWf-ext
        (typing-substᵀ left-TySubstWf ⊢N))

  right-N-open-typed :
    zero ∣ (`ℕ ∷ []) ⊢ substᵀ (right ρ) (subst (exts (γ .right)) N) ⦂ substᵗ (right ρ) A
  right-N-open-typed =
    substEq
      (λ Tm → zero ∣ (`ℕ ∷ []) ⊢ Tm ⦂ substᵗ (right ρ) A)
      (sym (substᵀ-subst-commute (right ρ) (exts (γ .right)) N))
      (typing-subst
        right-SubstWf-ext
        (typing-substᵀ right-TySubstWf ⊢N))

  go : ∀ {L₀ : Term}
    → ℰ `ℕ ρ
        (substᵀ (left ρ) (subst (γ .left) L₀))
        (substᵀ (right ρ) (subst (γ .right) L₀))
    → ℰ A ρ
        (substᵀ (left ρ) (subst (γ .left) (case_[zero⇒_|suc⇒_] L₀ M N)))
        (substᵀ (right ρ) (subst (γ .right) (case_[zero⇒_|suc⇒_] L₀ M N)))
  go {L₀ = L₀} ⟨ ⊢L , ⟨ ⊢L' , ⟨ `zero , ⟨ `zero , ⟨ vZero , ⟨ vZero , ⟨ L₁—↠0 , ⟨ L₂—↠0 , tt ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with M-rel ρ γ env
  ... | ⟨ ⊢M , ⟨ ⊢M' , ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ M₁—↠V' , ⟨ M₂—↠W' , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ ⊢case ⊢L ⊢M left-N-open-typed
    , ⟨ ⊢case ⊢L' ⊢M' right-N-open-typed
      , ⟨ V'
        , ⟨ W'
          , ⟨ v'
            , ⟨ w'
              , ⟨ left-zero-red
                , ⟨ right-zero-red
                  , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    left-zero-red :
      substᵀ (left ρ) (subst (γ .left) (case_[zero⇒_|suc⇒_] L₀ M N)) —↠ V'
    left-zero-red =
         (substᵀ (left ρ) (subst (γ .left) (case_[zero⇒_|suc⇒_] L₀ M N)))
       —↠⟨ case-↠ {M = substᵀ (left ρ) (subst (γ .left) M)}
                 {N = substᵀ (left ρ) (subst (exts (γ .left)) N)} L₁—↠0 ⟩
         (case_[zero⇒_|suc⇒_] `zero
            (substᵀ (left ρ) (subst (γ .left) M))
            (substᵀ (left ρ) (subst (exts (γ .left)) N)))
       —↠⟨ case-zero-↠ ⟩
         (substᵀ (left ρ) (subst (γ .left) M))
       —↠⟨ M₁—↠V' ⟩
         V'
       ∎

    right-zero-red :
      substᵀ (right ρ) (subst (γ .right) (case_[zero⇒_|suc⇒_] L₀ M N)) —↠ W'
    right-zero-red =
        (substᵀ (right ρ) (subst (γ .right) (case_[zero⇒_|suc⇒_] L₀ M N)))
      —↠⟨ case-↠ {M = substᵀ (right ρ) (subst (γ .right) M)}
                {N = substᵀ (right ρ) (subst (exts (γ .right)) N)} L₂—↠0 ⟩
        (case_[zero⇒_|suc⇒_] `zero
           (substᵀ (right ρ) (subst (γ .right) M))
           (substᵀ (right ρ) (subst (exts (γ .right)) N)))
      —↠⟨ case-zero-↠ ⟩
        (substᵀ (right ρ) (subst (γ .right) M))
      —↠⟨ M₂—↠W' ⟩
        W'
      ∎

  go {L₀ = L₀} ⟨ ⊢L , ⟨ ⊢L' , ⟨ `suc V , ⟨ `suc W , ⟨ vSuc vV , ⟨ vSuc wW , ⟨ L₁—↠sV , ⟨ L₂—↠sW , vw-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with M-rel ρ γ env
       | N-rel ρ (γ ,⟨ V , W ⟩)
         (⟨ 𝒱⇒ℰ {A = `ℕ} {ρ = ρ} {V = V} {W = W} vV wW vw-rel , env ⟩)
  ... | ⟨ ⊢M , ⟨ ⊢M' , _ ⟩ ⟩
      | ⟨ _ , ⟨ _ , ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ N₁—↠V' , ⟨ N₂—↠W' , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ ⊢case ⊢L ⊢M left-N-open-typed
    , ⟨ ⊢case ⊢L' ⊢M' right-N-open-typed
      , ⟨ V'
        , ⟨ W'
          , ⟨ v'
            , ⟨ w'
              , ⟨ left-suc-red
                , ⟨ right-suc-red
                  , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    case-suc : ∀ {U M₀ N₀ : Term}
      → Value U
      → case_[zero⇒_|suc⇒_] (`suc U) M₀ N₀ —↠ N₀ [ U ]
    case-suc {U} {M₀} {N₀} vU =
      (case_[zero⇒_|suc⇒_] (`suc U) M₀ N₀)
        —→⟨ β-suc vU ⟩
      (N₀ [ U ])
      ∎

    left-V-id : substᵀ (left ρ) V ≡ V
    left-V-id
      with 𝒱-typing {A = `ℕ} {ρ = ρ} {V = V} {W = W} {v = vV} {w = wW} vw-rel
    ... | ⟨ ⊢VNat , _ ⟩ = substᵀ-id-typed (λ ()) ⊢VNat

    right-W-id : substᵀ (right ρ) W ≡ W
    right-W-id
      with 𝒱-typing {A = `ℕ} {ρ = ρ} {V = V} {W = W} {v = vV} {w = wW} vw-rel
    ... | ⟨ _ , ⊢WNat ⟩ = substᵀ-id-typed (λ ()) ⊢WNat

    singleEnv-left-close : (i : Var)
      → substᵀ (left ρ) (singleEnv V i) ≡ singleEnv V i
    singleEnv-left-close zero = left-V-id
    singleEnv-left-close (suc i) = refl

    singleEnv-right-close : (i : Var)
      → substᵀ (right ρ) (singleEnv W i) ≡ singleEnv W i
    singleEnv-right-close zero = right-W-id
    singleEnv-right-close (suc i) = refl

    left-suc-bridge :
      (substᵀ (left ρ) (subst (exts (γ .left)) N) [ V ])
      ≡ substᵀ (left ρ) (subst (V • (γ .left)) N)
    left-suc-bridge =
      trans
        (sym (subst-cong singleEnv-left-close (substᵀ (left ρ) (subst (exts (γ .left)) N))))
        (trans
          (sym (substᵀ-subst-commute (left ρ) (singleEnv V) (subst (exts (γ .left)) N)))
          (cong (substᵀ (left ρ)) (exts-sub-cons (γ .left) N V)))

    right-suc-bridge :
      (substᵀ (right ρ) (subst (exts (γ .right)) N) [ W ])
      ≡ substᵀ (right ρ) (subst (W • (γ .right)) N)
    right-suc-bridge =
      trans
        (sym (subst-cong singleEnv-right-close (substᵀ (right ρ) (subst (exts (γ .right)) N))))
        (trans
          (sym (substᵀ-subst-commute (right ρ) (singleEnv W) (subst (exts (γ .right)) N)))
          (cong (substᵀ (right ρ)) (exts-sub-cons (γ .right) N W)))

    left-suc-red :
      substᵀ (left ρ) (subst (γ .left) (case_[zero⇒_|suc⇒_] L₀ M N)) —↠ V'
    left-suc-red =
        (substᵀ (left ρ) (subst (γ .left) (case_[zero⇒_|suc⇒_] L₀ M N)))
      —↠⟨ case-↠ {M = substᵀ (left ρ) (subst (γ .left) M)}
                {N = substᵀ (left ρ) (subst (exts (γ .left)) N)} L₁—↠sV ⟩
        (case_[zero⇒_|suc⇒_] (`suc V)
          (substᵀ (left ρ) (subst (γ .left) M))
          (substᵀ (left ρ) (subst (exts (γ .left)) N)))
      —↠⟨ case-suc {M₀ = substᵀ (left ρ) (subst (γ .left) M)}
                  {N₀ = substᵀ (left ρ) (subst (exts (γ .left)) N)} vV ⟩
        ((substᵀ (left ρ) (subst (exts (γ .left)) N)) [ V ])
      —↠⟨ substEq (λ Tm → Tm —↠ V') (sym left-suc-bridge) N₁—↠V' ⟩
        V'
      ∎

    right-suc-red :
      substᵀ (right ρ) (subst (γ .right) (case_[zero⇒_|suc⇒_] L₀ M N)) —↠ W'
    right-suc-red =
        (substᵀ (right ρ) (subst (γ .right) (case_[zero⇒_|suc⇒_] L₀ M N)))
      —↠⟨ case-↠ {M = substᵀ (right ρ) (subst (γ .right) M)}
                {N = substᵀ (right ρ) (subst (exts (γ .right)) N)} L₂—↠sW ⟩
        (case_[zero⇒_|suc⇒_] (`suc W)
          (substᵀ (right ρ) (subst (γ .right) M))
          (substᵀ (right ρ) (subst (exts (γ .right)) N)))
      —↠⟨ case-suc {M₀ = substᵀ (right ρ) (subst (γ .right) M)}
                  {N₀ = substᵀ (right ρ) (subst (exts (γ .right)) N)} wW ⟩
        ((substᵀ (right ρ) (subst (exts (γ .right)) N)) [ W ])
      —↠⟨ substEq (λ Tm → Tm —↠ W') (sym right-suc-bridge) N₂—↠W' ⟩
        W'
      ∎

compat-if : ∀ {Γ A}
  → (L M N : Term)
  → Γ ⊨ L ≈ L ⦂ `Bool
  → Γ ⊨ M ≈ M ⦂ A
  → Γ ⊨ N ≈ N ⦂ A
  → Γ ⊨ (`if_then_else L M N) ≈ (`if_then_else L M N) ⦂ A
compat-if {A = A} L M N L-rel M-rel N-rel ρ γ env
  with L-rel ρ γ env | M-rel ρ γ env | N-rel ρ γ env
... | ⟨ ⊢L , ⟨ ⊢L' , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ L₁—↠V , ⟨ L₂—↠W , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ ⊢M , ⟨ ⊢M' , ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨ M₁—↠V' , ⟨ M₂—↠W' , relM ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    | ⟨ ⊢N , ⟨ ⊢N' , ⟨ V'' , ⟨ W'' , ⟨ v'' , ⟨ w'' , ⟨ N₁—↠V'' , ⟨ N₂—↠W'' , relN ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with v | w | VW-rel
... | vTrue | vTrue | tt =
  ⟨ ⊢if ⊢L ⊢M ⊢N
  , ⟨ ⊢if ⊢L' ⊢M' ⊢N'
    , ⟨ V' , ⟨ W' , ⟨ v' , ⟨ w' , ⟨
          (`if_then_else
            (substᵀ (left ρ) (subst (γ .left) L))
            (substᵀ (left ρ) (subst (γ .left) M))
            (substᵀ (left ρ) (subst (γ .left) N)))
        —↠⟨ if-true-↠
              {M = substᵀ (left ρ) (subst (γ .left) M)}
              {N = substᵀ (left ρ) (subst (γ .left) N)}
              L₁—↠V ⟩
          (substᵀ (left ρ) (subst (γ .left) M))
        —↠⟨ M₁—↠V' ⟩
          V'
      ∎
      , ⟨ (`if_then_else
            (substᵀ (right ρ) (subst (γ .right) L))
            (substᵀ (right ρ) (subst (γ .right) M))
            (substᵀ (right ρ) (subst (γ .right) N)))
        —↠⟨ if-true-↠
              {M = substᵀ (right ρ) (subst (γ .right) M)}
              {N = substᵀ (right ρ) (subst (γ .right) N)}
              L₂—↠W ⟩
          (substᵀ (right ρ) (subst (γ .right) M))
        —↠⟨ M₂—↠W' ⟩
          W'
        ∎
        , relM ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
... | vFalse | vFalse | tt =
  ⟨ ⊢if ⊢L ⊢M ⊢N
  , ⟨ ⊢if ⊢L' ⊢M' ⊢N'
    , ⟨ V'' , ⟨ W'' , ⟨ v'' , ⟨ w'' , ⟨
        (`if_then_else
          (substᵀ (left ρ) (subst (γ .left) L))
          (substᵀ (left ρ) (subst (γ .left) M))
          (substᵀ (left ρ) (subst (γ .left) N)))
      —↠⟨ if-false-↠
            {M = substᵀ (left ρ) (subst (γ .left) M)}
            {N = substᵀ (left ρ) (subst (γ .left) N)}
            L₁—↠V ⟩
        (substᵀ (left ρ) (subst (γ .left) N))
      —↠⟨ N₁—↠V'' ⟩
        V''
      ∎
      , ⟨ (`if_then_else
            (substᵀ (right ρ) (subst (γ .right) L))
            (substᵀ (right ρ) (subst (γ .right) M))
            (substᵀ (right ρ) (subst (γ .right) N)))
        —↠⟨ if-false-↠
              {M = substᵀ (right ρ) (subst (γ .right) M)}
              {N = substᵀ (right ρ) (subst (γ .right) N)}
              L₂—↠W ⟩
          (substᵀ (right ρ) (subst (γ .right) N))
        —↠⟨ N₂—↠W'' ⟩
          W''
        ∎
        , relN ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
... | vTrue | vFalse | ()
... | vFalse | vTrue | ()


compat-·[] : ∀ {Δ Γ A B}
  → (M : Term)
  → WfTy Δ B
  → Γ ⊨ M ≈ M ⦂ (`∀ A)
  → Γ ⊨ (M ·[ B ]) ≈ (M ·[ B ]) ⦂ (A [ B ]ᵗ)
compat-·[] {A = A} {B = B} M hB M-rel ρ γ env
  with M-rel ρ γ env
... | ⟨ ⊢M , ⟨ ⊢M' , ⟨ .(Λ N₁) , ⟨ .(Λ N₂) , ⟨ vTlam {N = N₁} , ⟨ vTlam {N = N₂} , ⟨ M₁—↠ΛN₁ , ⟨ M₂—↠ΛN₂ , ∀-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with (proj₂ (proj₂ ∀-rel))
         (substᵗ (left ρ) B)
         (substᵗ (right ρ) B)
         (substᵗ-codom-closed (left ρ) (left-closed ρ) B)
         (substᵗ-codom-closed (right ρ) (right-closed ρ) B)
         (λ V W v w ⊢V ⊢W → 𝒱 B ρ V W v w) -- omega-in-omega needed here
... | rel-inst
  with ℰ-compositionality⇒ {A = A} {B = B} {ρ = ρ} rel-inst
... | ⟨ _ , ⟨ _ , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ N₁—↠V , ⟨ N₂—↠W , 𝒱[A[B]]VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ left-typed
  , ⟨ right-typed
    , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨
        (substᵀ (left ρ) (subst (γ .left) (M ·[ B ])))
      —↠⟨ ·[]-↠ M₁—↠ΛN₁ ⟩
        ((Λ N₁) ·[ substᵗ (left ρ) B ])
      —↠⟨ β-Λ-↠ {A = substᵗ (left ρ) B} ⟩
        N₁ [ substᵗ (left ρ) B ]ᵀ
      —↠⟨ N₁—↠V ⟩
      V
      ∎
    , ⟨ (substᵀ (right ρ) (subst (γ .right) (M ·[ B ])))
      —↠⟨ ·[]-↠ M₂—↠ΛN₂ ⟩
        ((Λ N₂) ·[ substᵗ (right ρ) B ])
      —↠⟨ β-Λ-↠ {A = substᵗ (right ρ) B} ⟩
        N₂ [ substᵗ (right ρ) B ]ᵀ
      —↠⟨ N₂—↠W ⟩
        W
      ∎
    , 𝒱[A[B]]VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where

  left-typed :
    zero ∣ [] ⊢ substᵀ (left ρ) (subst (γ .left) (M ·[ B ])) ⦂ substᵗ (left ρ) (A [ B ]ᵗ)
  left-typed =
    substEq
      (λ T → zero ∣ [] ⊢ substᵀ (left ρ) (subst (γ .left) (M ·[ B ])) ⦂ T)
      (sym (subst-[]ᵗ-commute (left ρ) A B))
      (⊢·[] {B = substᵗ (left ρ) B} ⊢M
        (substᵗ-codom-closed (left ρ) (left-closed ρ) B))

  right-typed :
    zero ∣ [] ⊢ substᵀ (right ρ) (subst (γ .right) (M ·[ B ])) ⦂ substᵗ (right ρ) (A [ B ]ᵗ)
  right-typed =
    substEq
      (λ T → zero ∣ [] ⊢ substᵀ (right ρ) (subst (γ .right) (M ·[ B ])) ⦂ T)
      (sym (subst-[]ᵗ-commute (right ρ) A B))
      (⊢·[] {B = substᵗ (right ρ) B} ⊢M'
        (substᵗ-codom-closed (right ρ) (right-closed ρ) B))

compat-Λ : ∀ {Δ Γ A}
  → (N : Term)
  → (suc Δ) ∣ (⤊ Γ) ⊢ N ⦂ A
  → (⤊ Γ) ⊨ N ≈ N ⦂ A
  → Γ ⊨ (Λ N) ≈ (Λ N) ⦂ (`∀ A)
compat-Λ {Δ = Δ} {Γ = Γ} {A = A} N ⊢N N-rel ρ γ env =
  ⟨ proj₁ LR-rel
  , ⟨ proj₁ (proj₂ LR-rel)
    , ⟨ Λ left-body
      , ⟨ Λ right-body
        , ⟨ vTlam
          , ⟨ vTlam
            , ⟨ left-red
              , ⟨ right-red
                , LR-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  left-body : Term
  left-body = substᵀ (extsᵗ (left ρ)) (subst (⇑ (γ .left)) N)

  right-body : Term
  right-body = substᵀ (extsᵗ (right ρ)) (subst (⇑ (γ .right)) N)

  left-red : substᵀ (left ρ) (subst (γ .left) (Λ N)) —↠ Λ left-body
  left-red = (substᵀ (left ρ) (subst (γ .left) (Λ N))) ∎

  right-red : substᵀ (right ρ) (subst (γ .right) (Λ N)) —↠ Λ right-body
  right-red = (substᵀ (right ρ) (subst (γ .right) (Λ N))) ∎

  left-bridge : (B : Ty) → subst (⇑ (γ .left)) N [ B ]ᵀ ≡ subst (γ .left) (N [ B ]ᵀ)
  left-bridge B =
    trans
      (substᵀ-subst-commute (singleTyEnv B) (⇑ (γ .left)) N)
      (subst-cong (λ i → singleTyEnv-suc-cancel B (γ .left i)) (N [ B ]ᵀ))

  right-bridge : (B : Ty) → subst (⇑ (γ .right)) N [ B ]ᵀ ≡ subst (γ .right) (N [ B ]ᵀ)
  right-bridge B =
    trans
      (substᵀ-subst-commute (singleTyEnv B) (⇑ (γ .right)) N)
      (subst-cong (λ i → singleTyEnv-suc-cancel B (γ .right i)) (N [ B ]ᵀ))

  left-TySubstWf : TySubstWf Δ zero (left ρ)
  left-TySubstWf {X} X<Δ = left-closed ρ X

  right-TySubstWf : TySubstWf Δ zero (right ρ)
  right-TySubstWf {X} X<Δ = right-closed ρ X

  left-id-exts : ∀ {i} → i < suc zero → extsᵗ (left ρ) i ≡ ` i
  left-id-exts {zero} z<s = refl
  left-id-exts {suc i} (s<s ())

  right-id-exts : ∀ {i} → i < suc zero → extsᵗ (right ρ) i ≡ ` i
  right-id-exts {zero} z<s = refl
  right-id-exts {suc i} (s<s ())

  left-σ : Subst
  left-σ i = substᵀ (extsᵗ (left ρ)) (⇑ (γ .left) i)

  right-σ : Subst
  right-σ i = substᵀ (extsᵗ (right ρ)) (⇑ (γ .right) i)

  left-SubstWf : SubstWf (suc zero)
    (map (substᵗ (extsᵗ (left ρ))) (⤊ Γ))
    []
    left-σ
  left-SubstWf {x} {B} h =
    substEq
      (λ Tm → suc zero ∣ [] ⊢ Tm ⦂ B)
      (sym (substᵀ-id-typed left-id-exts h'))
      h'
    where
    h-map : ⤊ (map (substᵗ (left ρ)) Γ) ∋ x ⦂ B
    h-map =
      substEq
        (λ Ψ → Ψ ∋ x ⦂ B)
        (map-substᵗ-⤊ (left ρ) Γ)
        h

    h' : suc zero ∣ [] ⊢ (⇑ (γ .left)) x ⦂ B
    h' = SubstWf-⇑ (𝒢-left-SubstWf env) h-map

  right-SubstWf : SubstWf (suc zero)
    (map (substᵗ (extsᵗ (right ρ))) (⤊ Γ))
    []
    right-σ
  right-SubstWf {x} {B} h =
    substEq
      (λ Tm → suc zero ∣ [] ⊢ Tm ⦂ B)
      (sym (substᵀ-id-typed right-id-exts h'))
      h'
    where
    h-map : ⤊ (map (substᵗ (right ρ)) Γ) ∋ x ⦂ B
    h-map =
      substEq
        (λ Ψ → Ψ ∋ x ⦂ B)
        (map-substᵗ-⤊ (right ρ) Γ)
        h

    h' : suc zero ∣ [] ⊢ (⇑ (γ .right)) x ⦂ B
    h' = SubstWf-⇑ (𝒢-right-SubstWf env) h-map

  left-body-typed :
    suc zero ∣ [] ⊢ left-body ⦂ substᵗ (extsᵗ (left ρ)) A
  left-body-typed =
    substEq
      (λ Tm → suc zero ∣ [] ⊢ Tm ⦂ substᵗ (extsᵗ (left ρ)) A)
      (sym (substᵀ-subst-commute (extsᵗ (left ρ)) (⇑ (γ .left)) N))
      (typing-subst
        left-SubstWf
        (typing-substᵀ (TySubstWf-exts left-TySubstWf) ⊢N))

  right-body-typed :
    suc zero ∣ [] ⊢ right-body ⦂ substᵗ (extsᵗ (right ρ)) A
  right-body-typed =
    substEq
      (λ Tm → suc zero ∣ [] ⊢ Tm ⦂ substᵗ (extsᵗ (right ρ)) A)
      (sym (substᵀ-subst-commute (extsᵗ (right ρ)) (⇑ (γ .right)) N))
      (typing-subst
        right-SubstWf
        (typing-substᵀ (TySubstWf-exts right-TySubstWf) ⊢N))

  LR-rel : 𝒱 (`∀ A) ρ (Λ left-body) (Λ right-body) vTlam vTlam
  LR-rel = ⟨ ⊢Λ left-body-typed , ⟨ ⊢Λ right-body-typed , body ⟩ ⟩
    where
    relN : ∀ (A₁ A₂ : Ty)
      → (hA₁ : WfTy zero A₁)
      → (hA₂ : WfTy zero A₂)
      → (R : Rel A₁ A₂)
      → ℰ A (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)
          (substᵀ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) (subst (γ .left) N))
          (substᵀ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) (subst (γ .right) N))

    left-inst : ∀ (A₁ A₂ : Ty)
      → (hA₁ : WfTy zero A₁)
      → (hA₂ : WfTy zero A₂)
      → (R : Rel A₁ A₂)
      → (left-body [ A₁ ]ᵀ) ≡
          (substᵀ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) (subst (γ .left) N))

    right-inst : ∀ (A₁ A₂ : Ty)
      → (hA₁ : WfTy zero A₁)
      → (hA₂ : WfTy zero A₂)
      → (R : Rel A₁ A₂)
      → (right-body [ A₂ ]ᵀ) ≡
          (substᵀ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) (subst (γ .right) N))

    body : ∀ (A₁ A₂ : Ty)
      → (hA₁ : WfTy zero A₁)
      → (hA₂ : WfTy zero A₂)
      → (R : Rel A₁ A₂)
      → ℰ A (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)
          (left-body [ A₁ ]ᵀ)
          (right-body [ A₂ ]ᵀ)
    body A₁ A₂ hA₁ hA₂ R
      with relN A₁ A₂ hA₁ hA₂ R
    ... | ⟨ ⊢L , ⟨ ⊢R , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ redL , ⟨ redR , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
      ⟨ substEq
          (λ Tm → zero ∣ [] ⊢ Tm ⦂ substᵗ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) A)
          (sym (left-inst A₁ A₂ hA₁ hA₂ R))
          ⊢L
      , ⟨ substEq
            (λ Tm → zero ∣ [] ⊢ Tm ⦂ substᵗ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) A)
            (sym (right-inst A₁ A₂ hA₁ hA₂ R))
            ⊢R
        , ⟨ V
          , ⟨ W
            , ⟨ v
              , ⟨ w
                , ⟨ substEq (λ Tm → Tm —↠ V) (sym (left-inst A₁ A₂ hA₁ hA₂ R)) redL
                  , ⟨ substEq (λ Tm → Tm —↠ W) (sym (right-inst A₁ A₂ hA₁ hA₂ R)) redR
                    , rel' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

    relN A₁ A₂ hA₁ hA₂ R = N-rel
      (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)
      γ
      (liftRelEnv-related hA₁ hA₂ R env)

    left-inst A₁ A₂ hA₁ hA₂ R =
      trans
        (substᵀ-substᵀ (singleTyEnv A₁) (extsᵗ (left ρ))
          (subst (⇑ (γ .left)) N))
        (trans
          (substᵀ-cong left-map
            (subst (⇑ (γ .left)) N))
          (trans
            (substᵀ-subst-commute
              (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩))
              (⇑ (γ .left))
              N)
            (trans
              (subst-cong-typed left-N-typed left-pointwise)
              (sym (substᵀ-subst-commute
                (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩))
                (γ .left)
                N)))))
      where
      left-N-TySubstWf : TySubstWf (suc Δ) zero
        (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩))
      left-N-TySubstWf {zero} _ = hA₁
      left-N-TySubstWf {suc X} X<Δ = left-closed ρ X

      left-N-typed :
        zero ∣ map (substᵗ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ) (⤊ Γ)
        ⊢ substᵀ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) N
            ⦂ substᵗ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) A
      left-N-typed = typing-substᵀ left-N-TySubstWf ⊢N

      left-var-close : ∀ {x C}
        → Γ ∋ x ⦂ C
        → substᵀ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ((⇑ (γ .left)) x)
          ≡ substᵀ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ((γ .left) x)
      left-var-close {x} h =
        trans
          (trans
            (substᵀ-renameᵀ-commute
              suc
              (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩))
              ((γ .left) x))
            (substᵀ-cong (λ i → refl) ((γ .left) x)))
          (trans
            (substᵀ-id-typed (λ ()) (𝒢-left-SubstWf env (lookup-map-substᵗ h)))
            (sym (substᵀ-id-typed (λ ()) (𝒢-left-SubstWf env (lookup-map-substᵗ h)))))

      left-pointwise : ∀ {x B}
        → map (substᵗ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ) (⤊ Γ) ∋ x ⦂ B
        → substᵀ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ((⇑ (γ .left)) x)
          ≡ substᵀ (left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ((γ .left) x)
      left-pointwise {x} h with lookup-map-inv h
      ... | p with lookup-map-inv (DP.proj₁ (snd p))
      ... | q = left-var-close (DP.proj₁ (snd q))

      left-map : (i : Var)
        → substᵗ (singleTyEnv A₁) (extsᵗ (left ρ) i)
        ≡ left (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩) i
      left-map zero = refl
      left-map (suc i) = singleTyEnv-suc-cancelᵗ A₁ (left ρ i)

    right-inst A₁ A₂ hA₁ hA₂ R =
      trans
        (substᵀ-substᵀ (singleTyEnv A₂) (extsᵗ (right ρ))
          (subst (⇑ (γ .right)) N))
        (trans
          (substᵀ-cong right-map
            (subst (⇑ (γ .right)) N))
          (trans
            (substᵀ-subst-commute
              (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩))
              (⇑ (γ .right))
              N)
            (trans
              (subst-cong-typed right-N-typed right-pointwise)
              (sym (substᵀ-subst-commute
                (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩))
                (γ .right)
                N)))))
      where
      right-N-TySubstWf : TySubstWf (suc Δ) zero
        (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩))
      right-N-TySubstWf {zero} _ = hA₂
      right-N-TySubstWf {suc X} X<Δ = right-closed ρ X

      right-N-typed :
        zero ∣ map (substᵗ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ) (⤊ Γ)
        ⊢ substᵀ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) N
            ⦂ substᵗ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) A
      right-N-typed = typing-substᵀ right-N-TySubstWf ⊢N

      right-var-close : ∀ {x C}
        → Γ ∋ x ⦂ C
        → substᵀ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ((⇑ (γ .right)) x)
          ≡ substᵀ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ((γ .right) x)
      right-var-close {x} h =
        trans
          (trans
            (substᵀ-renameᵀ-commute
              suc
              (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩))
              ((γ .right) x))
            (substᵀ-cong (λ i → refl) ((γ .right) x)))
          (trans
            (substᵀ-id-typed (λ ()) (𝒢-right-SubstWf env (lookup-map-substᵗ h)))
            (sym (substᵀ-id-typed (λ ()) (𝒢-right-SubstWf env (lookup-map-substᵗ h)))))

      right-pointwise : ∀ {x B}
        → map (substᵗ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ) (⤊ Γ) ∋ x ⦂ B
        → substᵀ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ((⇑ (γ .right)) x)
          ≡ substᵀ (right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩)) ((γ .right) x)
      right-pointwise {x} h with lookup-map-inv h
      ... | p with lookup-map-inv (DP.proj₁ (snd p))
      ... | q = right-var-close (DP.proj₁ (snd q))

      right-map : (i : Var)
        → substᵗ (singleTyEnv A₂) (extsᵗ (right ρ) i)
        ≡ right (ρ ,⟨ A₁ , A₂ , hA₁ , hA₂ , R ⟩) i
      right-map zero = refl
      right-map (suc i) = singleTyEnv-suc-cancelᵗ A₂ (right ρ i)

--------------------------------------------------------------------------------
-- Fundamental Theorem
--------------------------------------------------------------------------------

fundamental : ∀ {Δ Γ A} (M : Term)
  → Δ ∣ Γ ⊢ M ⦂ A
  → Γ ⊨ M ≈ M ⦂ A
fundamental _ (⊢` x) = compat-var x
fundamental _ (⊢ƛ {A = A} {B = B} {N = N} _ dN) =
  compat-ƛ {A = A} {B = B} N dN (fundamental N dN)
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
  compat-case {A = A} L M N dN
    (fundamental L dL)
    (fundamental M dM)
    (fundamental N dN)
fundamental _ (⊢if {A = A} {L = L} {M = M} {N = N} dL dM dN) =
  compat-if {A = A} L M N
    (fundamental L dL)
    (fundamental M dM)
    (fundamental N dN)
fundamental _ (⊢Λ {N = N} dN) =
  compat-Λ N dN (fundamental N dN)
fundamental _ (⊢·[] {M = M} {B = B} dM hB) =
  compat-·[] M hB (fundamental M dM)
