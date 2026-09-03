module strong.BReduction where

-- Reduction for the tight dual boundary (B₀) design, one rule at a time.
-- Each rule: the rule, a worked typed example, and its preservation case.
-- Preservation is stated at runtime term contexts ([]).

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (m≤m+n; m+[n∸m]≡n; +-monoʳ-<; +-cancelˡ-<; ≤-trans; <⇒≤)
open import Data.List using (List; []; _∷_; map)
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
    L M M′ N V W F : Term
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

⊢renameᵀ : ∀ {ρ Δ Δ' Γₜ M A}
  → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X)
  → Δ ∣ Γₜ ⊢ M ⦂ A
  → Δ' ∣ map (renameᵗ ρ) Γₜ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A
⊢renameᵀ h (⊢` p)       = ⊢` (∋-map p)
⊢renameᵀ h ⊢$           = ⊢$
⊢renameᵀ h (⊢ƛ wfA ⊢N)  = ⊢ƛ (wf-ren h wfA) (⊢renameᵀ h ⊢N)
⊢renameᵀ h (⊢· ⊢L ⊢M)   = ⊢· (⊢renameᵀ h ⊢L) (⊢renameᵀ h ⊢M)
⊢renameᵀ h (⊢Λ {Γₜ = Γₜ} ⊢N) =
  ⊢Λ (subst (λ Γ' → _ ∣ Γ' ⊢ _ ⦂ _) (⤊-ren Γₜ) (⊢renameᵀ (ext-h h) ⊢N))
⊢renameᵀ {ρ} h (⊢·[] {L = L} {B = B} {A = A} ⊢L wfA) =
  subst (λ T → _ ∣ _ ⊢ renameᵀ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ] ⦂ T)
        (sym (rename-[]ᵗ-commute ρ B A))
    (⊢·[] (⊢renameᵀ h ⊢L) (wf-ren h wfA))
⊢renameᵀ h (env bwf sc ⊢M) = {!!}

------------------------------------------------------------------------
-- Preservation (so far: β-Λ)
------------------------------------------------------------------------

preservation : Δ ∣ [] ⊢ M ⦂ A → M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A

preservation (⊢·[] {B = B} {A = A} (⊢Λ {N = V} ⊢V) ⊢A) (β-Λ v) =
  subst (λ T → _ ∣ [] ⊢ V ⟪ rvl A ∷ [] , B ⟫ ⦂ T) ext-eq
    (env {B₀ = B} (bwf↑ ⊢A bwf[])
         scB
         (subst (λ T → _ ∣ [] ⊢ V ⦂ T) (sym int-eq) ⊢V))
  where
    -- internal face:  γᵇ [rvl A] = prepId 1 (γcnc 1 0 [rvl A]) is pointwise `_
    gvar : (x : ℕ) → γᵇ (rvl A ∷ []) x ≡ ` x
    gvar zero    = refl
    gvar (suc _) = refl
    int-eq : substᵗ (γᵇ (rvl A ∷ [])) B ≡ B
    int-eq = trans (subst-cong gvar B) (subst-id B)
    -- external face:  substᵗ (ρᵇ [rvl A]) B = substᵗ (A •ᵗ `_) B ≡ B [ A ]ᵗ
    ext-eq : substᵗ (ρᵇ (rvl A ∷ [])) B ≡ B [ A ]ᵗ
    ext-eq = subst-cong (λ { zero → refl ; (suc _) → refl }) B
    -- Scoped obligation: baseS [rvl A] Δ is ALL ok (cmax = 0), and B is the
    -- ∀-body of Λ V — well-scoped over abst ∷ Δ.  Closing this needs a
    -- context-wf ⇒ typing ⇒ Scoped bridge (the all-ok specialisation).
    scB : Scoped (baseS (rvl A ∷ []) _) B
    scB = {!!}

-- β-ƛ case: pending the term-substitution lemma
--   ⊢substᵀᵐ : (∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Γ' ⊢ σ x ⦂ A)
--            → Δ ∣ Γ ⊢ N ⦂ B → Δ ∣ Γ' ⊢ substᵀᵐ σ N ⦂ B
-- whose Λ case needs type-variable renaming THROUGH a boundary (renameᵀ on a
-- wrapper — currently provisional).  That renaming is the next infrastructure.
preservation (⊢· (⊢ƛ _ ⊢N) ⊢W) (β-ƛ w) = {!!}
