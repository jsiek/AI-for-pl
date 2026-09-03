module strong.BReduction where

-- Reduction for the tight dual boundary (B₀) design, one rule at a time.
-- Each rule: the rule, a worked typed example, and its preservation case.
-- Preservation is stated at runtime term contexts ([]).

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _⊔_; s≤s; z≤n; _<?_; _≤?_)
open import Data.Nat.Properties
  using (m≤m+n; m+[n∸m]≡n; +-monoʳ-<; +-cancelˡ-<; ≤-trans; <⇒≤; ≤-refl;
         _≟_; <-cmp; <-irrefl; ≰⇒>; m≤n⇒m<n∨m≡n; m≤n⇒m⊔n≡n; m≥n⇒m⊔n≡m;
         m+n∸m≡n; m+n≮m; +-identityʳ; +-suc)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; map)
open import Relation.Nullary using (Dec; yes; no; ¬_; ⌊_⌋)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; subst; subst₂; cong; cong₂)
open import strong.Types
open import strong.TypeSubst
  using (subst-cong; subst-id; rename-rename-commute; rename-[]ᵗ-commute;
         rename-subst; rename-subst-commute)
open import strong.Context
  using (TCtx; abst; rvld; _↓_; _⊢_; wf-var; wf-ℕ; _∋tv_; here-abst; here-rvld;
         skip-abst; skip-rvld; Ctx; _∋_⦂_; here; there; ⤊)
open import strong.Weakening using (wf-rename-fv; fv-scope)
open import strong.Boundary

private
  variable
    Δ : TCtx
    A B C B₀ : Ty
    L L′ M M′ N N′ V W F : Term
    Θ : BCtx
    n x : ℕ

------------------------------------------------------------------------
-- Term-variable substitution (for Beta).  Identity on wrappers: a wrapped value
-- is term-closed (its body is typed at []), so no term variable reaches inside.
-- renameᵀ (type-variable renaming through a wrapper) is PROVISIONAL — the simple
-- β-ƛ example below never pushes a wrapper under a Λ, so it isn't exercised; the
-- correct version is the next piece (needed for the general substitution lemma).
------------------------------------------------------------------------

extⁿ : (ℕ → ℕ) → (ℕ → ℕ)
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renameᵀᵐ : (ℕ → ℕ) → Term → Term
renameᵀᵐ ρ (` x)          = ` (ρ x)
renameᵀᵐ ρ ($ n)          = $ n
renameᵀᵐ ρ (ƛ A ∙ N)      = ƛ A ∙ renameᵀᵐ (extⁿ ρ) N
renameᵀᵐ ρ (L · M)        = renameᵀᵐ ρ L · renameᵀᵐ ρ M
renameᵀᵐ ρ (Λ N)          = Λ (renameᵀᵐ ρ N)
renameᵀᵐ ρ (L ·[ B , A ]) = renameᵀᵐ ρ L ·[ B , A ]
renameᵀᵐ ρ (M ⟪ Θ , B₀ ⟫) = M ⟪ Θ , B₀ ⟫

-- Renaming a wrapper's type variables (ρ : Γ → Γ').  Reveal reps rename by ρ,
-- conceal indices by ρ; B₀ lives over the boundary frame (reveals ++ Γ) so it
-- renames by liftⁿ (revs Θ) ρ; the body and conceal reps live over the interior,
-- which renames by intRenᵇ — identity below a conceal that absorbs ρ (a conceal
-- restricts to Γ↓X, and restrictRen X ρ is the induced renaming on Γ↓X).
liftⁿ : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
liftⁿ zero    ρ = ρ
liftⁿ (suc r) ρ = extᵗ (liftⁿ r ρ)

restrictRen : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
restrictRen X ρ j = ρ (suc X + j) ∸ suc (ρ X)

-- interior renaming (whole-Γ): a SINGLE restriction at cmax (deepRen), lifted
-- past the reveal variables.  restrictRen c is the induced renaming on Γ↓c.
deepRen : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
deepRen zero    ρ = ρ
deepRen (suc c) ρ = restrictRen c ρ

intRen : (ℕ → ℕ) → BCtx → (ℕ → ℕ)
intRen ρ Θ = liftⁿ (revs Θ) (deepRen (cmax Θ) ρ)

renᴮ : (ℕ → ℕ) → (ℕ → ℕ) → BCtx → BCtx      -- ρ for reveal reps/indices, ir for conceal reps
renᴮ ρ ir []             = []
renᴮ ρ ir (rvl A   ∷ Θ) = rvl (renameᵗ ρ A)  ∷ renᴮ ρ ir Θ
renᴮ ρ ir (cnc X A ∷ Θ) = cnc (ρ X) (renameᵗ ir A) ∷ renᴮ ρ ir Θ

renameᵀ : (ℕ → ℕ) → Term → Term          -- rename TYPE variables
renameᵀ ρ (` x)          = ` x
renameᵀ ρ ($ n)          = $ n
renameᵀ ρ (ƛ A ∙ N)      = ƛ (renameᵗ ρ A) ∙ renameᵀ ρ N
renameᵀ ρ (L · M)        = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ (Λ N)          = Λ (renameᵀ (extᵗ ρ) N)
renameᵀ ρ (L ·[ B , A ]) = renameᵀ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renameᵀ ρ (M ⟪ Θ , B₀ ⟫) =
  renameᵀ (intRen ρ Θ) M ⟪ renᴮ ρ (intRen ρ Θ) Θ , renameᵗ (liftⁿ (revs Θ) ρ) B₀ ⟫

⇑ᵀ : Term → Term
⇑ᵀ = renameᵀ suc

extsᵀᵐ : (ℕ → Term) → (ℕ → Term)
extsᵀᵐ σ zero    = ` zero
extsᵀᵐ σ (suc x) = renameᵀᵐ suc (σ x)

substᵀᵐ : (ℕ → Term) → Term → Term
substᵀᵐ σ (` x)          = σ x
substᵀᵐ σ ($ n)          = $ n
substᵀᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵀᵐ (extsᵀᵐ σ) N
substᵀᵐ σ (L · M)        = substᵀᵐ σ L · substᵀᵐ σ M
substᵀᵐ σ (Λ N)          = Λ (substᵀᵐ (λ x → ⇑ᵀ (σ x)) N)
substᵀᵐ σ (L ·[ B , A ]) = substᵀᵐ σ L ·[ B , A ]
substᵀᵐ σ (M ⟪ Θ , B₀ ⟫) = M ⟪ Θ , B₀ ⟫

infix 8 _[_]ᵐ
_[_]ᵐ : Term → Term → Term
N [ W ]ᵐ = substᵀᵐ (λ { zero → W ; (suc x) → ` x }) N

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data GVal : Term → Set
data Value : Term → Set

data GVal where
  G-ƛ : GVal (ƛ A ∙ N)
  G-Λ : Value V → GVal (Λ V)

data Value where
  V-$  : Value ($ n)
  V-G  : GVal V → Value V
  V-⟪⟫ : Value V → Value (V ⟪ Θ , B₀ ⟫)

------------------------------------------------------------------------
-- Reduction
------------------------------------------------------------------------

infix 2 _-→_
data _-→_ : Term → Term → Set where

  -- TyBeta: a boundary is BORN.  The ∀-body B is recorded as the BOUNDARY type;
  -- internal type = B[γ] = B, external type = B[ρ] = B[A]ᵗ.
  β-Λ : Value V
      → (Λ V) ·[ B , A ] -→ V ⟪ rvl A ∷ [] , B ⟫

  -- Beta
  β-ƛ : Value W
      → (ƛ A ∙ N) · W -→ N [ W ]ᵐ

  -- ξ (congruence): the evaluation frames, left-to-right call-by-value.
  -- ξ-Λ and ξ-⟪⟫ are not optional bookkeeping: Λ V is a value only when V is
  -- (G-Λ) and V ⟪ Θ , B₀ ⟫ only when V is (V-⟪⟫), so the body of a Λ and the
  -- interior of a boundary must be reduced in place before either is a value.
  ξ-·-l : L -→ L′
        → L · M -→ L′ · M

  ξ-·-r : Value V → M -→ M′
        → V · M -→ V · M′

  ξ-·[] : L -→ L′
        → L ·[ B , A ] -→ L′ ·[ B , A ]

  ξ-Λ   : N -→ N′
        → Λ N -→ Λ N′

  ξ-⟪⟫  : M -→ M′
        → M ⟪ Θ , B₀ ⟫ -→ M′ ⟪ Θ , B₀ ⟫

------------------------------------------------------------------------
-- Worked example:  (ΛX. λx:X.x) [X→X, ℕ]  →  (λx:X.x)⟪↑X:=ℕ⟫   (both : ℕ→ℕ)
------------------------------------------------------------------------

⊢redex-Λ : [] ∣ [] ⊢ (Λ (ƛ ` 0 ∙ ` 0)) ·[ (` 0 ⇒ ` 0) , `ℕ ] ⦂ (`ℕ ⇒ `ℕ)
⊢redex-Λ = ⊢·[] (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))) wf-ℕ

_ : (Λ (ƛ ` 0 ∙ ` 0)) ·[ (` 0 ⇒ ` 0) , `ℕ ]
    -→ (ƛ ` 0 ∙ ` 0) ⟪ rvl `ℕ ∷ [] , (` 0 ⇒ ` 0) ⟫
_ = β-Λ (V-G G-ƛ)

⊢contractum-Λ : [] ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl `ℕ ∷ [] , (` 0 ⇒ ` 0) ⟫ ⦂ (`ℕ ⇒ `ℕ)
⊢contractum-Λ = env (bwf↑ wf-ℕ bwf[]) (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
                    (⊢ƛ (wf-var here-abst) (⊢` here))

------------------------------------------------------------------------
-- Worked example for β-ƛ:  (λx:ℕ. x) · 5  →  5    (both : ℕ)
------------------------------------------------------------------------

⊢redex-ƛ : [] ∣ [] ⊢ (ƛ `ℕ ∙ ` 0) · ($ 5) ⦂ `ℕ
⊢redex-ƛ = ⊢· (⊢ƛ wf-ℕ (⊢` here)) ⊢$

_ : (ƛ `ℕ ∙ ` 0) · ($ 5) -→ $ 5
_ = β-ƛ V-$

⊢contractum-ƛ : [] ∣ [] ⊢ $ 5 ⦂ `ℕ
⊢contractum-ƛ = ⊢$

------------------------------------------------------------------------
-- Worked example for ξ-⟪⟫:  reduce the INTERIOR of a reveal boundary.
--   ((λx:ℕ. x) · 5) ⟪ ↑X:=ℕ , B₀=ℕ ⟫  →  5 ⟪ ↑X:=ℕ , B₀=ℕ ⟫   (both : ℕ)
-- The interior context is  abst ∣ []  (one reveal, no conceal); B₀ = ℕ has
-- no free variable, so both faces are ℕ: the boundary is inert on the type.
------------------------------------------------------------------------

⊢redex-bnd : [] ∣ [] ⊢ ((ƛ `ℕ ∙ ` 0) · $ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫ ⦂ `ℕ
⊢redex-bnd = env (bwf↑ wf-ℕ bwf[]) sc-ℕ (⊢· (⊢ƛ wf-ℕ (⊢` here)) ⊢$)

_ : ((ƛ `ℕ ∙ ` 0) · $ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫
    -→ ($ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫
_ = ξ-⟪⟫ (β-ƛ V-$)

⊢contractum-bnd : [] ∣ [] ⊢ ($ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫ ⦂ `ℕ
⊢contractum-bnd = env (bwf↑ wf-ℕ bwf[]) sc-ℕ ⊢$

------------------------------------------------------------------------
-- renameᵀ through a boundary, verified on ⇑ᵀ of the non-spurious ($7)⟪Θ₈, X⟫.
-- Under ⇑ᵀ (new abstract W at Γ-index 0):  conceal index 1 ↦ 2, reveal rep ` 0
-- (=Y) ↦ ` 1, B₀ = X = ` 2 ↦ ` 3 (bframe lift), body 7 unchanged (conceal absorbs
-- the shift, so intRenᵇ = id).
------------------------------------------------------------------------

_ : ⇑ᵀ (($ 7) ⟪ Θ₈ , ` 2 ⟫) ≡ ($ 7) ⟪ cnc 2 `ℕ ∷ rvl (` 1) ∷ [] , ` 3 ⟫
_ = refl

-- ⊢renameᵀ on this instance: the renamed wrapper types at abst ∷ Γ₈ with the
-- renamed external type ` 2 (= renameᵗ suc of the original external ` 1 = X).
_ : (abst ∷ Γ₈) ∣ [] ⊢ ($ 7) ⟪ cnc 2 `ℕ ∷ rvl (` 1) ∷ [] , ` 3 ⟫ ⦂ ` 2
_ = env (bwf↓ (skip-abst (skip-abst here-rvld)) wf-ℕ
             (bwf↑ (wf-var (skip-abst here-abst)) bwf[]))
        (sc-var (thereᵒ (thereᵒ (thereᵒ hereᵒ)))) ⊢$

------------------------------------------------------------------------
-- Type-variable renaming preserves typing  (⊢renameᵀ)
------------------------------------------------------------------------

∋-map : ∀ {ρ} {Γₜ : Ctx} {x A} → Γₜ ∋ x ⦂ A → map (renameᵗ ρ) Γₜ ∋ x ⦂ renameᵗ ρ A
∋-map here      = here
∋-map (there p) = there (∋-map p)

wf-ren : ∀ {ρ Δ Δ'} {A : Ty}
       → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Δ ⊢ A → Δ' ⊢ renameᵗ ρ A
wf-ren h wfA = wf-rename-fv (λ y → h (fv-scope wfA y)) wfA

ext-h : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X)
      → (∀ {X} → (abst ∷ Δ) ∋tv X → (abst ∷ Δ') ∋tv extᵗ ρ X)
ext-h h here-abst    = here-abst
ext-h h (skip-abst p) = skip-abst (h p)

⤊-ren : ∀ {ρ} (Γₜ : Ctx) → map (renameᵗ (extᵗ ρ)) (⤊ Γₜ) ≡ ⤊ (map (renameᵗ ρ) Γₜ)
⤊-ren []            = refl
⤊-ren {ρ} (A ∷ Γₜ) = cong₂ _∷_ pt (⤊-ren Γₜ)
  where pt : renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
        pt = trans (rename-rename-commute suc (extᵗ ρ) A)
                   (sym (rename-rename-commute ρ suc A))

-- ↓ / ∋tv bridge: a variable of the existential scope Δ↓X is variable suc X + Y
-- of Δ, and back.  (Needed for the interior commutation.)
↓-∋ : ∀ {Δ} X {Y} → (Δ ↓ X) ∋tv Y → Δ ∋tv (suc X + Y)
↓-∋ {[]}        X       ()
↓-∋ {abst   ∷ Δ} zero    p = skip-abst p
↓-∋ {rvld A ∷ Δ} zero    p = skip-rvld p
↓-∋ {abst   ∷ Δ} (suc X) p = skip-abst (↓-∋ X p)
↓-∋ {rvld A ∷ Δ} (suc X) p = skip-rvld (↓-∋ X p)

↓-∋⁻ : ∀ {Δ} X {Z} → Δ ∋tv (suc X + Z) → (Δ ↓ X) ∋tv Z
↓-∋⁻ {[]}        X       ()
↓-∋⁻ {abst   ∷ Δ} zero    (skip-abst p) = p
↓-∋⁻ {rvld A ∷ Δ} zero    (skip-rvld p) = p
↓-∋⁻ {abst   ∷ Δ} (suc X) (skip-abst p) = ↓-∋⁻ X p
↓-∋⁻ {rvld A ∷ Δ} (suc X) (skip-rvld p) = ↓-∋⁻ X p

-- Mono = strictly monotone renaming (the shape of every renaming that arises:
-- weakenings and their lifts).  restrictRen preserves it.
Mono : (ℕ → ℕ) → Set
Mono ρ = ∀ {a b} → a < b → ρ a < ρ b

-- extᵗ preserves monotonicity, so ⊢renameᵀ can recurse under a Λ.
Mono-extᵗ : ∀ {ρ} → Mono ρ → Mono (extᵗ ρ)
Mono-extᵗ mono {zero}  {suc _} _         = s≤s z≤n
Mono-extᵗ mono {suc _} {suc _} (s≤s a<b) = s≤s (mono a<b)

∸-strict : ∀ {c p q} → c ≤ p → p < q → (p ∸ c) < (q ∸ c)
∸-strict {c} {p} {q} c≤p p<q =
  +-cancelˡ-< c _ _
    (subst₂ _<_ (sym (m+[n∸m]≡n c≤p)) (sym (m+[n∸m]≡n c≤q)) p<q)
  where c≤q : c ≤ q
        c≤q = ≤-trans c≤p (<⇒≤ p<q)

-- external commutation: renaming commutes with the external projection ρᵇ.
ρᵇ-comm : ∀ ρ ir Θ X
        → ρᵇ (renᴮ ρ ir Θ) (liftⁿ (revs Θ) ρ X) ≡ renameᵗ ρ (ρᵇ Θ X)
ρᵇ-comm ρ ir []            X       = refl
ρᵇ-comm ρ ir (rvl A   ∷ Θ) zero    = refl
ρᵇ-comm ρ ir (rvl A   ∷ Θ) (suc Y) = ρᵇ-comm ρ ir Θ Y
ρᵇ-comm ρ ir (cnc X A ∷ Θ) Y       = ρᵇ-comm ρ ir Θ Y

C-ext : ∀ ρ ir Θ B₀
      → substᵗ (ρᵇ (renᴮ ρ ir Θ)) (renameᵗ (liftⁿ (revs Θ) ρ) B₀)
        ≡ renameᵗ ρ (substᵗ (ρᵇ Θ) B₀)
C-ext ρ ir Θ B₀ =
  trans (rename-subst-commute (liftⁿ (revs Θ) ρ) (ρᵇ (renᴮ ρ ir Θ)) B₀)
    (trans (subst-cong (ρᵇ-comm ρ ir Θ) B₀)
           (sym (rename-subst ρ (ρᵇ Θ) B₀)))

-- lookup preservation through one restriction Δ↓X (needed for the interior)
h-restrict : ∀ {ρ Δ Δ'} X
  → (∀ {Y} → Δ ∋tv Y → Δ' ∋tv ρ Y) → Mono ρ
  → ∀ {Y} → (Δ ↓ X) ∋tv Y → (Δ' ↓ ρ X) ∋tv restrictRen X ρ Y
h-restrict {ρ} X h mono {Y} p =
  ↓-∋⁻ (ρ X) (subst (λ n → _ ∋tv n) eq (h (↓-∋ X p)))
  where
    lt : suc (ρ X) ≤ ρ (suc X + Y)
    lt = mono (m≤m+n (suc X) Y)
    eq : ρ (suc X + Y) ≡ suc (ρ X) + restrictRen X ρ Y
    eq = sym (m+[n∸m]≡n lt)

------------------------------------------------------------------------
-- Monotonicity toolbox.  Mono is injective, and it survives every
-- combinator the interior renaming intRen is built from.
------------------------------------------------------------------------

Mono→inj : ∀ {ρ} → Mono ρ → ∀ {a b} → ρ a ≡ ρ b → a ≡ b
Mono→inj {ρ} mono {a} {b} eq with <-cmp a b
Mono→inj {ρ} mono {a} {b} eq | tri< a<b _ _ =
  ⊥-elim (<-irrefl eq (mono a<b))
Mono→inj {ρ} mono {a} {b} eq | tri≈ _ a≡b _ = a≡b
Mono→inj {ρ} mono {a} {b} eq | tri> _ _ b<a =
  ⊥-elim (<-irrefl (sym eq) (mono b<a))

Mono→≤ : ∀ {ρ} → Mono ρ → ∀ {a b} → a ≤ b → ρ a ≤ ρ b
Mono→≤ mono a≤b with m≤n⇒m<n∨m≡n a≤b
Mono→≤ mono a≤b | inj₁ a<b  = <⇒≤ (mono a<b)
Mono→≤ mono a≤b | inj₂ refl = ≤-refl

Mono-restrictRen : ∀ {ρ} X → Mono ρ → Mono (restrictRen X ρ)
Mono-restrictRen {ρ} X mono {a} {b} a<b =
  ∸-strict (mono (m≤m+n (suc X) a)) (mono (+-monoʳ-< (suc X) a<b))

Mono-deepRen : ∀ {ρ} c → Mono ρ → Mono (deepRen c ρ)
Mono-deepRen zero    mono = mono
Mono-deepRen (suc c) mono = Mono-restrictRen c mono

Mono-liftⁿ : ∀ {ρ} r → Mono ρ → Mono (liftⁿ r ρ)
Mono-liftⁿ zero    mono = mono
Mono-liftⁿ (suc r) mono = Mono-extᵗ (Mono-liftⁿ r mono)

Mono-intRen : ∀ {ρ} Θ → Mono ρ → Mono (intRen ρ Θ)
Mono-intRen Θ mono = Mono-liftⁿ (revs Θ) (Mono-deepRen (cmax Θ) mono)

------------------------------------------------------------------------
-- renᴮ keeps the reveal count, and (for a Mono ρ) sends the deepest
-- conceal index X to ρ X — so cmax has one of two shapes after renaming.
------------------------------------------------------------------------

revs-ren : ∀ ρ ir Θ → revs (renᴮ ρ ir Θ) ≡ revs Θ
revs-ren ρ ir []            = refl
revs-ren ρ ir (rvl A ∷ Θ)   = cong suc (revs-ren ρ ir Θ)
revs-ren ρ ir (cnc X A ∷ Θ) = revs-ren ρ ir Θ

⊔-mono-comm : ∀ {ρ} → Mono ρ → ∀ a b → ρ (a ⊔ b) ≡ ρ a ⊔ ρ b
⊔-mono-comm {ρ} mono a b with a ≤? b
⊔-mono-comm {ρ} mono a b | yes a≤b =
  trans (cong ρ (m≤n⇒m⊔n≡n a≤b)) (sym (m≤n⇒m⊔n≡n (Mono→≤ mono a≤b)))
⊔-mono-comm {ρ} mono a b | no ¬a≤b =
  trans (cong ρ (m≥n⇒m⊔n≡m b≤a)) (sym (m≥n⇒m⊔n≡m (Mono→≤ mono b≤a)))
  where b≤a : b ≤ a
        b≤a = <⇒≤ (≰⇒> ¬a≤b)

-- the two possible shapes of cmax under renaming
data CmaxV (ρ ir : ℕ → ℕ) (Θ : BCtx) : Set where
  cm-0 : cmax Θ ≡ 0 → cmax (renᴮ ρ ir Θ) ≡ 0 → CmaxV ρ ir Θ
  cm-s : ∀ X → cmax Θ ≡ suc X → cmax (renᴮ ρ ir Θ) ≡ suc (ρ X)
       → CmaxV ρ ir Θ

cmax-ren : ∀ {ρ} → Mono ρ → ∀ ir Θ → CmaxV ρ ir Θ
cmax-ren mono ir [] = cm-0 refl refl
cmax-ren mono ir (rvl A ∷ Θ) with cmax-ren mono ir Θ
cmax-ren mono ir (rvl A ∷ Θ) | cm-0 e e'   = cm-0 e e'
cmax-ren mono ir (rvl A ∷ Θ) | cm-s Y e e' = cm-s Y e e'
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) with cmax-ren mono ir Θ
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) | cm-0 e e' =
  cm-s X (cong (λ n → suc X ⊔ n) e) (cong (λ n → suc (ρ X) ⊔ n) e')
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) | cm-s Y e e' =
  cm-s (X ⊔ Y) (cong (λ n → suc X ⊔ n) e)
       (trans (cong (λ n → suc (ρ X) ⊔ n) e')
              (cong suc (sym (⊔-mono-comm mono X Y))))

------------------------------------------------------------------------
-- liftⁿ / prepId below and above the reveal prefix, and the view that
-- splits a boundary-frame index into "reveal prefix" or "deep".
------------------------------------------------------------------------

liftⁿ-lo : ∀ r ρ X → X < r → liftⁿ r ρ X ≡ X
liftⁿ-lo zero    ρ X       ()
liftⁿ-lo (suc r) ρ zero    _         = refl
liftⁿ-lo (suc r) ρ (suc X) (s≤s X<r) = cong suc (liftⁿ-lo r ρ X X<r)

liftⁿ-hi : ∀ r ρ i → liftⁿ r ρ (r + i) ≡ r + ρ i
liftⁿ-hi zero    ρ i = refl
liftⁿ-hi (suc r) ρ i = cong suc (liftⁿ-hi r ρ i)

prepId-lo : ∀ r (σ : Substᵗ) X → X < r → prepId r σ X ≡ ` X
prepId-lo r σ X X<r with X <? r
prepId-lo r σ X X<r | yes _   = refl
prepId-lo r σ X X<r | no ¬X<r = ⊥-elim (¬X<r X<r)

prepId-hi : ∀ r (σ : Substᵗ) i → prepId r σ (r + i) ≡ σ i
prepId-hi r σ i with (r + i) <? r
prepId-hi r σ i | yes lt = ⊥-elim (m+n≮m r i lt)
prepId-hi r σ i | no  _  = cong σ (m+n∸m≡n r i)

-- prepId-hi with the reveal count supplied up to an equation (needed
-- because γᵇ of a renamed boundary mentions revs (renᴮ …), not revs Θ)
prepId-hi′ : ∀ r r' (σ : Substᵗ) i → r' ≡ r → prepId r' σ (r + i) ≡ σ i
prepId-hi′ r .r σ i refl = prepId-hi r σ i

split : ∀ r X → (X < r) ⊎ (Σ ℕ λ i → X ≡ r + i)
split zero    X       = inj₂ (X , refl)
split (suc r) zero    = inj₁ (s≤s z≤n)
split (suc r) (suc X) with split r X
split (suc r) (suc X) | inj₁ X<r        = inj₁ (s≤s X<r)
split (suc r) (suc X) | inj₂ (i , X≡ri) = inj₂ (i , cong suc X≡ri)

------------------------------------------------------------------------
-- Decidable/Bool plumbing for isConc (whose cons case is ⌊ i ≟ X ⌋ ∨ …).
------------------------------------------------------------------------

⌊⌋-true : ∀ {P : Set} (d : Dec P) → ⌊ d ⌋ ≡ true → P
⌊⌋-true (yes p) _  = p
⌊⌋-true (no ¬p) ()

⌊⌋-of : ∀ {P : Set} (d : Dec P) → P → ⌊ d ⌋ ≡ true
⌊⌋-of (yes _) _ = refl
⌊⌋-of (no ¬p) p = ⊥-elim (¬p p)

∨-true : ∀ (b₁ b₂ : Bool) → (b₁ ∨ b₂) ≡ true → (b₁ ≡ true) ⊎ (b₂ ≡ true)
∨-true true  b₂ e = inj₁ refl
∨-true false b₂ e = inj₂ e

isConc-cons : ∀ i X A Θ → isConc i (cnc X A ∷ Θ) ≡ true
            → (i ≡ X) ⊎ (isConc i Θ ≡ true)
isConc-cons i X A Θ c with ∨-true ⌊ i ≟ X ⌋ (isConc i Θ) c
isConc-cons i X A Θ c | inj₁ t = inj₁ (⌊⌋-true (i ≟ X) t)
isConc-cons i X A Θ c | inj₂ t = inj₂ t

isConc-here : ∀ i X A Θ → i ≡ X → isConc i (cnc X A ∷ Θ) ≡ true
isConc-here i X A Θ p = cong (λ b → b ∨ isConc i Θ) (⌊⌋-of (i ≟ X) p)

isConc-there : ∀ i X A Θ → isConc i Θ ≡ true → isConc i (cnc X A ∷ Θ) ≡ true
isConc-there i X A Θ c =
  trans (cong (λ b → ⌊ i ≟ X ⌋ ∨ b) c) (∨-zeroʳ ⌊ i ≟ X ⌋)

-- a concealed index stays concealed after renaming (indices move by ρ)
isConc-ren : ∀ ρ ir Θ i → isConc i Θ ≡ true
           → isConc (ρ i) (renᴮ ρ ir Θ) ≡ true
isConc-ren ρ ir []            i ()
isConc-ren ρ ir (rvl A ∷ Θ)   i c = isConc-ren ρ ir Θ i c
isConc-ren ρ ir (cnc X A ∷ Θ) i c with isConc-cons i X A Θ c
isConc-ren ρ ir (cnc X A ∷ Θ) i c | inj₁ p =
  isConc-here (ρ i) (ρ X) (renameᵗ ir A) (renᴮ ρ ir Θ) (cong ρ p)
isConc-ren ρ ir (cnc X A ∷ Θ) i c | inj₂ t =
  isConc-there (ρ i) (ρ X) (renameᵗ ir A) (renᴮ ρ ir Θ)
               (isConc-ren ρ ir Θ i t)

------------------------------------------------------------------------
-- The accessibility bridge: baseS Θ Δ ∋ok (revs Θ + i) says exactly that
-- i is a KEPT (cmax Θ ≤ i) or CONCEALED index of Δ — the two cases where
-- γcnc commutes with renaming.  Both directions are needed.
------------------------------------------------------------------------

ok≢blk : ok ≡ blk → ⊥
ok≢blk ()

∋ok-head : ∀ {s Ψ} → (s ∷ Ψ) ∋ok zero → s ≡ ok
∋ok-head hereᵒ = refl

∋ok-tail : ∀ {s Ψ j} → (s ∷ Ψ) ∋ok suc j → Ψ ∋ok j
∋ok-tail (thereᵒ p) = p

∋ok-≡ : ∀ {Ψ X X'} → X ≡ X' → Ψ ∋ok X → Ψ ∋ok X'
∋ok-≡ refl p = p

∋tv-tail : ∀ {E Γ j} → (E ∷ Γ) ∋tv suc j → Γ ∋tv j
∋tv-tail (skip-abst p) = p
∋tv-tail (skip-rvld p) = p

repl-drop : ∀ r {Ψ i} → (repl-ok r ++ Ψ) ∋ok (r + i) → Ψ ∋ok i
repl-drop zero    p = p
repl-drop (suc r) p = repl-drop r (∋ok-tail p)

repl-add : ∀ r {Ψ i} → Ψ ∋ok i → (repl-ok r ++ Ψ) ∋ok (r + i)
repl-add zero    p = p
repl-add (suc r) p = thereᵒ (repl-add r p)

repl-lo : ∀ r {Ψ} X → X < r → (repl-ok r ++ Ψ) ∋ok X
repl-lo zero    X       ()
repl-lo (suc r) zero    _         = hereᵒ
repl-lo (suc r) (suc X) (s≤s X<r) = thereᵒ (repl-lo r X X<r)

slotsᴳ-ok : ∀ Θ Γ k j → slotsᴳ Θ k Γ ∋ok j → slotAt Θ (k + j) ≡ ok
slotsᴳ-ok Θ []      k j ()
slotsᴳ-ok Θ (E ∷ Γ) k zero    p rewrite +-identityʳ k = ∋ok-head p
slotsᴳ-ok Θ (E ∷ Γ) k (suc j) p rewrite +-suc k j =
  slotsᴳ-ok Θ Γ (suc k) j (∋ok-tail p)

slotsᴳ-∋tv : ∀ Θ Γ k j → slotsᴳ Θ k Γ ∋ok j → Γ ∋tv j
slotsᴳ-∋tv Θ []            k j       ()
slotsᴳ-∋tv Θ (abst ∷ Γ)    k zero    p = here-abst
slotsᴳ-∋tv Θ (rvld A ∷ Γ)  k zero    p = here-rvld
slotsᴳ-∋tv Θ (abst ∷ Γ)    k (suc j) p =
  skip-abst (slotsᴳ-∋tv Θ Γ (suc k) j (∋ok-tail p))
slotsᴳ-∋tv Θ (rvld A ∷ Γ)  k (suc j) p =
  skip-rvld (slotsᴳ-∋tv Θ Γ (suc k) j (∋ok-tail p))

slotsᴳ-add : ∀ Θ Γ k j → Γ ∋tv j → slotAt Θ (k + j) ≡ ok
           → slotsᴳ Θ k Γ ∋ok j
slotsᴳ-add Θ []      k j       ()  e
slotsᴳ-add Θ (E ∷ Γ) k zero    q   e =
  subst (λ s → (s ∷ slotsᴳ Θ (suc k) Γ) ∋ok zero)
        (sym (trans (cong (slotAt Θ) (sym (+-identityʳ k))) e)) hereᵒ
slotsᴳ-add Θ (E ∷ Γ) k (suc j) q   e =
  thereᵒ (slotsᴳ-add Θ Γ (suc k) j (∋tv-tail q)
                     (trans (cong (slotAt Θ) (sym (+-suc k j))) e))

if-ok : ∀ (b : Bool) → b ≡ true → (if b then ok else blk) ≡ ok
if-ok true  _  = refl
if-ok false ()

if-acc : ∀ (b : Bool) → (b ≡ true) ⊎ ((if b then ok else blk) ≡ blk)
if-acc true  = inj₁ refl
if-acc false = inj₂ refl

slotAt-acc : ∀ Θ i
  → (cmax Θ ≤ i) ⊎ ((isConc i Θ ≡ true) ⊎ (slotAt Θ i ≡ blk))
slotAt-acc Θ i with cmax Θ ≤? i
slotAt-acc Θ i | yes le = inj₁ le
slotAt-acc Θ i | no ¬le with if-acc (isConc i Θ)
slotAt-acc Θ i | no ¬le | inj₁ c = inj₂ (inj₁ c)
slotAt-acc Θ i | no ¬le | inj₂ b = inj₂ (inj₂ b)

acc-of : ∀ Θ i → slotAt Θ i ≡ ok → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
acc-of Θ i e with slotAt-acc Θ i
acc-of Θ i e | inj₁ le         = inj₁ le
acc-of Θ i e | inj₂ (inj₁ c)   = inj₂ c
acc-of Θ i e | inj₂ (inj₂ bk)  = ⊥-elim (ok≢blk (trans (sym e) bk))

slotAt-hi : ∀ Θ i → cmax Θ ≤ i → slotAt Θ i ≡ ok
slotAt-hi Θ i le with cmax Θ ≤? i
slotAt-hi Θ i le | yes _   = refl
slotAt-hi Θ i le | no ¬le  = ⊥-elim (¬le le)

slotAt-conc : ∀ Θ i → isConc i Θ ≡ true → slotAt Θ i ≡ ok
slotAt-conc Θ i c with cmax Θ ≤? i
slotAt-conc Θ i c | yes _  = refl
slotAt-conc Θ i c | no ¬le = if-ok (isConc i Θ) c

acc-slotAt : ∀ Θ i → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true) → slotAt Θ i ≡ ok
acc-slotAt Θ i (inj₁ le) = slotAt-hi Θ i le
acc-slotAt Θ i (inj₂ c)  = slotAt-conc Θ i c

baseS-acc : ∀ {Δ} Θ i → baseS Θ Δ ∋ok (revs Θ + i)
          → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
baseS-acc {Δ} Θ i p =
  acc-of Θ i (slotsᴳ-ok Θ Δ 0 i (repl-drop (revs Θ) p))

baseS-∋tv : ∀ {Δ} Θ i → baseS Θ Δ ∋ok (revs Θ + i) → Δ ∋tv i
baseS-∋tv {Δ} Θ i p = slotsᴳ-∋tv Θ Δ 0 i (repl-drop (revs Θ) p)

baseS-ok : ∀ {Δ} Θ i → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true) → Δ ∋tv i
         → baseS Θ Δ ∋ok (revs Θ + i)
baseS-ok {Δ} Θ i acc q =
  repl-add (revs Θ) (slotsᴳ-add Θ Δ 0 i q (acc-slotAt Θ i acc))

------------------------------------------------------------------------
-- Internal commutation.  The deep part of γᵇ is γcnc, which commutes
-- with ρ at kept and concealed indices (it does NOT at blocked ones —
-- that is exactly what the (env) scope premise rules out).
------------------------------------------------------------------------

-- the arithmetic side condition γcnc-comm needs at a kept index: with no
-- conceals ρ passes through, otherwise both sides restrict at the deepest
-- conceal (cmax Θ = suc X on the left, cmax Θ' = suc (ρ X) on the right).
deep-eq : ∀ {ρ} m m' → m ≡ 0 → m' ≡ 0 → ∀ j → m ≤ j
        → ρ j ∸ m' ≡ deepRen m ρ (j ∸ m)
deep-eq {ρ} m m' e e' j le =
  trans (cong (λ n → ρ j ∸ n) e')
        (cong (λ n → deepRen n ρ (j ∸ n)) (sym e))

deep-eq-s : ∀ {ρ} m m' X → m ≡ suc X → m' ≡ suc (ρ X) → ∀ j → m ≤ j
          → ρ j ∸ m' ≡ deepRen m ρ (j ∸ m)
deep-eq-s {ρ} m m' X e e' j le =
  trans (cong (λ n → ρ j ∸ n) e')
    (trans (cong (λ n → ρ n ∸ suc (ρ X)) (sym (m+[n∸m]≡n le')))
           (cong (λ n → deepRen n ρ (j ∸ n)) (sym e)))
  where le' : suc X ≤ j
        le' = subst (λ n → n ≤ j) e le

deep-hyp : ∀ {ρ} → Mono ρ → ∀ Θ j → cmax Θ ≤ j
  → ρ j ∸ cmax (renᴮ ρ (intRen ρ Θ) Θ)
    ≡ deepRen (cmax Θ) ρ (j ∸ cmax Θ)
deep-hyp {ρ} mono Θ j le with cmax-ren mono (intRen ρ Θ) Θ
deep-hyp {ρ} mono Θ j le | cm-0 e e'   = deep-eq (cmax Θ) _ e e' j le
deep-hyp {ρ} mono Θ j le | cm-s X e e' = deep-eq-s (cmax Θ) _ X e e' j le

acc-tail : ∀ m i X A Θ → ¬ (X ≡ i)
  → (m ≤ i) ⊎ (isConc i (cnc X A ∷ Θ) ≡ true)
  → (m ≤ i) ⊎ (isConc i Θ ≡ true)
acc-tail m i X A Θ ne (inj₁ le) = inj₁ le
acc-tail m i X A Θ ne (inj₂ c) with isConc-cons i X A Θ c
acc-tail m i X A Θ ne (inj₂ c) | inj₁ p = ⊥-elim (ne (sym p))
acc-tail m i X A Θ ne (inj₂ c) | inj₂ t = inj₂ t

γcnc-comm : ∀ {ρ} → Mono ρ → ∀ r m m' Θ i
  → (∀ j → m ≤ j → ρ j ∸ m' ≡ deepRen m ρ (j ∸ m))
  → (m ≤ i) ⊎ (isConc i Θ ≡ true)
  → γcnc r m' (renᴮ ρ (liftⁿ r (deepRen m ρ)) Θ) (ρ i)
    ≡ renameᵗ (liftⁿ r (deepRen m ρ)) (γcnc r m Θ i)
γcnc-comm {ρ} mono r m m' [] i hyp (inj₁ le) =
  trans (cong (λ n → ` (r + n)) (hyp i le))
        (cong `_ (sym (liftⁿ-hi r (deepRen m ρ) (i ∸ m))))
γcnc-comm {ρ} mono r m m' [] i hyp (inj₂ ())
γcnc-comm {ρ} mono r m m' (rvl A ∷ Θ) i hyp acc =
  γcnc-comm mono r m m' Θ i hyp acc
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  with X ≟ i | ρ X ≟ ρ i
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | yes refl | yes _ = refl
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | yes p | no ¬q = ⊥-elim (¬q (cong ρ p))
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | no ¬p | yes q = ⊥-elim (¬p (Mono→inj mono q))
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | no ¬p | no ¬q =
  γcnc-comm mono r m m' Θ i hyp (acc-tail m i X A Θ ¬p acc)

-- γᵇ commutes with renaming at every ACCESSIBLE boundary-frame slot.
γᵇ-comm-lo : ∀ {ρ} → Mono ρ → ∀ Θ X → X < revs Θ
  → γᵇ (renᴮ ρ (intRen ρ Θ) Θ) (liftⁿ (revs Θ) ρ X)
    ≡ renameᵗ (intRen ρ Θ) (γᵇ Θ X)
γᵇ-comm-lo {ρ} mono Θ X lt =
  trans (cong (γᵇ (renᴮ ρ (intRen ρ Θ) Θ)) (liftⁿ-lo (revs Θ) ρ X lt))
    (trans (prepId-lo (revs (renᴮ ρ (intRen ρ Θ) Θ)) _ X lt')
      (trans (cong `_ (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) X lt)))
             (cong (renameᵗ (intRen ρ Θ))
                   (sym (prepId-lo (revs Θ) _ X lt)))))
  where lt' : X < revs (renᴮ ρ (intRen ρ Θ) Θ)
        lt' = subst (λ n → X < n) (sym (revs-ren ρ (intRen ρ Θ) Θ)) lt

γᵇ-comm-hi : ∀ {ρ Δ} → Mono ρ → ∀ Θ i
  → baseS Θ Δ ∋ok (revs Θ + i)
  → γᵇ (renᴮ ρ (intRen ρ Θ) Θ) (liftⁿ (revs Θ) ρ (revs Θ + i))
    ≡ renameᵗ (intRen ρ Θ) (γᵇ Θ (revs Θ + i))
γᵇ-comm-hi {ρ} mono Θ i okp =
  trans (cong (γᵇ (renᴮ ρ (intRen ρ Θ) Θ)) (liftⁿ-hi (revs Θ) ρ i))
    (trans (prepId-hi′ (revs Θ) (revs (renᴮ ρ (intRen ρ Θ) Θ)) _ (ρ i) rr)
      (trans (cong (λ n → γcnc n (cmax (renᴮ ρ (intRen ρ Θ) Θ))
                                 (renᴮ ρ (intRen ρ Θ) Θ) (ρ i)) rr)
        (trans (γcnc-comm mono (revs Θ) (cmax Θ)
                          (cmax (renᴮ ρ (intRen ρ Θ) Θ)) Θ i
                          (deep-hyp mono Θ) (baseS-acc Θ i okp))
               (cong (renameᵗ (intRen ρ Θ))
                     (sym (prepId-hi (revs Θ) _ i))))))
  where rr : revs (renᴮ ρ (intRen ρ Θ) Θ) ≡ revs Θ
        rr = revs-ren ρ (intRen ρ Θ) Θ

γᵇ-comm-ok : ∀ {ρ Δ} → Mono ρ → ∀ Θ X → baseS Θ Δ ∋ok X
  → γᵇ (renᴮ ρ (intRen ρ Θ) Θ) (liftⁿ (revs Θ) ρ X)
    ≡ renameᵗ (intRen ρ Θ) (γᵇ Θ X)
γᵇ-comm-ok mono Θ X okp with split (revs Θ) X
γᵇ-comm-ok mono Θ X okp | inj₁ lt = γᵇ-comm-lo mono Θ X lt
γᵇ-comm-ok mono Θ .(revs Θ + i) okp | inj₂ (i , refl) =
  γᵇ-comm-hi mono Θ i okp

-- internal face: mirrors C-ext, but only at accessible slots (subst-cong-sc)
C-int : ∀ {ρ Δ B₀} → Mono ρ → ∀ Θ → Scoped (baseS Θ Δ) B₀
      → substᵗ (γᵇ (renᴮ ρ (intRen ρ Θ) Θ))
               (renameᵗ (liftⁿ (revs Θ) ρ) B₀)
        ≡ renameᵗ (intRen ρ Θ) (substᵗ (γᵇ Θ) B₀)
C-int {ρ} {Δ} {B₀} mono Θ sc =
  trans (rename-subst-commute (liftⁿ (revs Θ) ρ)
                              (γᵇ (renᴮ ρ (intRen ρ Θ) Θ)) B₀)
    (trans (subst-cong-sc sc (λ X okp → γᵇ-comm-ok mono Θ X okp))
           (sym (rename-subst (intRen ρ Θ) (γᵇ Θ) B₀)))

------------------------------------------------------------------------
-- The interior context transports: intOf Δ Θ → intOf Δ' (renᴮ … Θ).
------------------------------------------------------------------------

∋tv-≡ : ∀ {Γ Γ' Z Z'} → Γ ≡ Γ' → Z ≡ Z' → Γ ∋tv Z → Γ' ∋tv Z'
∋tv-≡ refl refl p = p

prepAbst-lo : ∀ r Γ Y → Y < r → prepAbst r Γ ∋tv Y
prepAbst-lo zero    Γ Y       ()
prepAbst-lo (suc r) Γ zero    _         = here-abst
prepAbst-lo (suc r) Γ (suc Y) (s≤s Y<r) =
  skip-abst (prepAbst-lo r Γ Y Y<r)

prepAbst-hi : ∀ r Γ Z → Γ ∋tv Z → prepAbst r Γ ∋tv (r + Z)
prepAbst-hi zero    Γ Z p = p
prepAbst-hi (suc r) Γ Z p = skip-abst (prepAbst-hi r Γ Z p)

prepAbst-hi⁻ : ∀ r Γ Z → prepAbst r Γ ∋tv (r + Z) → Γ ∋tv Z
prepAbst-hi⁻ zero    Γ Z p             = p
prepAbst-hi⁻ (suc r) Γ Z (skip-abst p) = prepAbst-hi⁻ r Γ Z p

-- dropN (suc X) is the existential prefix Δ ↓ X (the conceal interior)
dropN-↓ : ∀ (Γ : TCtx) X → dropN (suc X) Γ ≡ Γ ↓ X
dropN-↓ []             X       = refl
dropN-↓ (abst ∷ Γ)     zero    = refl
dropN-↓ (rvld A ∷ Γ)   zero    = refl
dropN-↓ (abst ∷ Γ)     (suc X) = dropN-↓ Γ X
dropN-↓ (rvld A ∷ Γ)   (suc X) = dropN-↓ Γ X

drop-int : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ {Z}
  → dropN (cmax Θ) Δ ∋tv Z
  → dropN (cmax (renᴮ ρ (intRen ρ Θ) Θ)) Δ' ∋tv deepRen (cmax Θ) ρ Z
drop-int {ρ} {Δ} {Δ'} h mono Θ {Z} q with cmax-ren mono (intRen ρ Θ) Θ
drop-int {ρ} {Δ} {Δ'} h mono Θ {Z} q | cm-0 e e' =
  ∋tv-≡ (cong (λ n → dropN n Δ') (sym e'))
        (cong (λ n → deepRen n ρ Z) (sym e))
        (h (∋tv-≡ (cong (λ n → dropN n Δ) e) refl q))
drop-int {ρ} {Δ} {Δ'} h mono Θ {Z} q | cm-s X e e' =
  ∋tv-≡ (trans (sym (dropN-↓ Δ' (ρ X)))
               (cong (λ n → dropN n Δ') (sym e')))
        (cong (λ n → deepRen n ρ Z) (sym e))
        (h-restrict X h mono
          (∋tv-≡ (trans (cong (λ n → dropN n Δ) e) (dropN-↓ Δ X)) refl q))

h-int : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ {Y}
  → intOf Δ Θ ∋tv Y
  → intOf Δ' (renᴮ ρ (intRen ρ Θ) Θ) ∋tv intRen ρ Θ Y
h-int {ρ} {Δ} {Δ'} h mono Θ {Y} p with split (revs Θ) Y
h-int {ρ} {Δ} {Δ'} h mono Θ {Y} p | inj₁ lt =
  ∋tv-≡ (cong (λ n → prepAbst n (dropN (cmax Θ') Δ'))
              (sym (revs-ren ρ (intRen ρ Θ) Θ)))
        (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) Y lt))
        (prepAbst-lo (revs Θ) (dropN (cmax Θ') Δ') Y lt)
  where Θ' : BCtx
        Θ' = renᴮ ρ (intRen ρ Θ) Θ
h-int {ρ} {Δ} {Δ'} h mono Θ {Y} p | inj₂ (Z , refl) =
  ∋tv-≡ (cong (λ n → prepAbst n (dropN (cmax Θ') Δ'))
              (sym (revs-ren ρ (intRen ρ Θ) Θ)))
        (sym (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ) Z))
        (prepAbst-hi (revs Θ) (dropN (cmax Θ') Δ')
                     (deepRen (cmax Θ) ρ Z)
                     (drop-int h mono Θ
                       (prepAbst-hi⁻ (revs Θ) (dropN (cmax Θ) Δ) Z p)))
  where Θ' : BCtx
        Θ' = renᴮ ρ (intRen ρ Θ) Θ

------------------------------------------------------------------------
-- Boundary well-formedness and the (env) scope premise transport.
------------------------------------------------------------------------

bwf-ren : ∀ {ρ ir Δ Δ' Ψ Ψ' Θ}
  → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X)
  → (∀ {Y} → Ψ ∋tv Y → Ψ' ∋tv ir Y)
  → Δ ∣ Ψ ⊢ᵇ Θ → Δ' ∣ Ψ' ⊢ᵇ renᴮ ρ ir Θ
bwf-ren h hi bwf[]           = bwf[]
bwf-ren h hi (bwf↑ wfA b)    = bwf↑ (wf-ren h wfA) (bwf-ren h hi b)
bwf-ren h hi (bwf↓ p wfA b)  =
  bwf↓ (h p) (wf-ren hi wfA) (bwf-ren h hi b)

sc-rename : ∀ {Ψ Ψ' ρ₀ A} → (∀ X → Ψ ∋ok X → Ψ' ∋ok ρ₀ X)
          → Scoped Ψ A → Scoped Ψ' (renameᵗ ρ₀ A)
sc-rename t (sc-var p)   = sc-var (t _ p)
sc-rename t sc-ℕ         = sc-ℕ
sc-rename t sc-𝔹         = sc-𝔹
sc-rename t (sc-⇒ sA sB) = sc-⇒ (sc-rename t sA) (sc-rename t sB)
sc-rename {Ψ} {Ψ'} {ρ₀} t (sc-∀ sA) = sc-∀ (sc-rename t-ext sA)
  where t-ext : ∀ X → (ok ∷ Ψ) ∋ok X → (ok ∷ Ψ') ∋ok extᵗ ρ₀ X
        t-ext zero    hereᵒ      = hereᵒ
        t-ext (suc X) (thereᵒ p) = thereᵒ (t X p)

-- a kept index stays kept and a concealed one stays concealed under ρ
acc-ren : ∀ {ρ} → Mono ρ → ∀ Θ i → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
  → (cmax (renᴮ ρ (intRen ρ Θ) Θ) ≤ ρ i)
    ⊎ (isConc (ρ i) (renᴮ ρ (intRen ρ Θ) Θ) ≡ true)
acc-ren {ρ} mono Θ i (inj₁ le) with cmax-ren mono (intRen ρ Θ) Θ
acc-ren {ρ} mono Θ i (inj₁ le) | cm-0 e e' =
  inj₁ (subst (λ n → n ≤ ρ i) (sym e') z≤n)
acc-ren {ρ} mono Θ i (inj₁ le) | cm-s X e e' =
  inj₁ (subst (λ n → n ≤ ρ i) (sym e')
              (mono (subst (λ n → n ≤ i) e le)))
acc-ren {ρ} mono Θ i (inj₂ c) =
  inj₂ (isConc-ren ρ (intRen ρ Θ) Θ i c)

baseS-ren : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ
  → ∀ X → baseS Θ Δ ∋ok X
  → baseS (renᴮ ρ (intRen ρ Θ) Θ) Δ' ∋ok liftⁿ (revs Θ) ρ X
baseS-ren {ρ} h mono Θ X okp with split (revs Θ) X
baseS-ren {ρ} h mono Θ X okp | inj₁ lt =
  ∋ok-≡ (sym (liftⁿ-lo (revs Θ) ρ X lt))
        (repl-lo (revs (renᴮ ρ (intRen ρ Θ) Θ)) X
                 (subst (λ n → X < n)
                        (sym (revs-ren ρ (intRen ρ Θ) Θ)) lt))
baseS-ren {ρ} h mono Θ .(revs Θ + i) okp | inj₂ (i , refl) =
  ∋ok-≡ (trans (cong (λ n → n + ρ i) (revs-ren ρ (intRen ρ Θ) Θ))
               (sym (liftⁿ-hi (revs Θ) ρ i)))
        (baseS-ok (renᴮ ρ (intRen ρ Θ) Θ) (ρ i)
                  (acc-ren mono Θ i (baseS-acc Θ i okp))
                  (h (baseS-∋tv Θ i okp)))

sc-ren : ∀ {ρ Δ Δ' B₀} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ
  → Scoped (baseS Θ Δ) B₀
  → Scoped (baseS (renᴮ ρ (intRen ρ Θ) Θ) Δ')
           (renameᵗ (liftⁿ (revs Θ) ρ) B₀)
sc-ren h mono Θ sc = sc-rename (baseS-ren h mono Θ) sc

-- ρ must be MONOTONE, not merely lookup-preserving: boundary renaming depends on
-- index order through cmax / restrictRen (a non-monotone ρ that permutes indices
-- could shrink a conceal's interior and strand a variable).
⊢renameᵀ : ∀ {ρ Δ Δ' Γₜ M A}
  → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ
  → Δ ∣ Γₜ ⊢ M ⦂ A
  → Δ' ∣ map (renameᵗ ρ) Γₜ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A
⊢renameᵀ h mono (⊢` p)       = ⊢` (∋-map p)
⊢renameᵀ h mono ⊢$           = ⊢$
⊢renameᵀ h mono (⊢ƛ wfA ⊢N)  = ⊢ƛ (wf-ren h wfA) (⊢renameᵀ h mono ⊢N)
⊢renameᵀ h mono (⊢· ⊢L ⊢M)   = ⊢· (⊢renameᵀ h mono ⊢L) (⊢renameᵀ h mono ⊢M)
⊢renameᵀ h mono (⊢Λ {Γₜ = Γₜ} ⊢N) =
  ⊢Λ (subst (λ Γ' → _ ∣ Γ' ⊢ _ ⦂ _) (⤊-ren Γₜ)
            (⊢renameᵀ (ext-h h) (Mono-extᵗ mono) ⊢N))
⊢renameᵀ {ρ} h mono (⊢·[] {L = L} {B = B} {A = A} ⊢L wfA) =
  subst (λ T → _ ∣ _ ⊢ renameᵀ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ] ⦂ T)
        (sym (rename-[]ᵗ-commute ρ B A))
    (⊢·[] (⊢renameᵀ h mono ⊢L) (wf-ren h wfA))
⊢renameᵀ {ρ} h mono (env {Θ = Θ} {B₀ = B₀} {M = M} bwf sc ⊢M) =
  subst (λ T → _ ∣ _ ⊢ renameᵀ (intRen ρ Θ) M
                       ⟪ renᴮ ρ (intRen ρ Θ) Θ
                       , renameᵗ (liftⁿ (revs Θ) ρ) B₀ ⟫ ⦂ T)
        (C-ext ρ (intRen ρ Θ) Θ B₀)
    (env (bwf-ren h (h-int h mono Θ) bwf) (sc-ren h mono Θ sc)
         (subst (λ T → _ ∣ [] ⊢ renameᵀ (intRen ρ Θ) M ⦂ T)
                (sym (C-int mono Θ sc))
                (⊢renameᵀ (h-int h mono Θ) (Mono-intRen Θ mono) ⊢M)))
