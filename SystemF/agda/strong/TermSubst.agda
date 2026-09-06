module strong.TermSubst where

-- Strong System F — SUBSTITUTION AND THE TWO TRANSPORTS.
--
-- Term substitution is ordinary: boundaries are term-closed, so a wrapper is
-- never descended into.  The interesting content is the pair of TYPE-LEVEL
-- transports the binder design has to pay for, and both come out cheap:
--
--   ⊢rename : a type context renaming moves a whole typing derivation, with the ONE
--             structural hypothesis `Inj ρ` (positional masking; no
--             hypothesis mentions a representation).
--   ⊢retag  : knowledge refinement moves a whole typing derivation with the
--             TERM AND THE TYPE UNCHANGED — no ≈, no unfolding, no residue,
--             because nothing on the type context is ever destroyed.
--
-- §5 defines term-variable renaming (`renⁿ`) and substitution (`substᵐ`,
-- `_[_]ᵐ`); §6 proves them sound (`⊢renⁿ`, `⊢substᵐ`, `⊢subst`), which is
-- what Beta's preservation case consumes (`preserve-Beta`).  TWO CASES carry
-- the whole story:
--
--   (env)  is TRIVIAL — a wrapper is TERM-CLOSED (the rule types its body at
--          Γ = []) and the rule's conclusion holds at an ARBITRARY term
--          context, so both `renⁿ` and `substᵐ` are the identity on wrappers
--          and the case is literally the premises handed back.
--
--   ⊢Λ     is the only real work — it types its body at the SHIFTED term
--          context ⤊ Γ, so every image of σ must be shifted past the new
--          Λ-bound slot by ⇑ᴹ = renᴹ suc.  That is `⊢rename` at suc, with
--          `Ren-wk` and `Inj-suc`; no knowledge premise appears, because a
--          boundary carries NAMES, never spellings.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.TypeSubst using (rename-[]ᵗ-commute)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms

private
  variable
    Δ Δ′ : Ctxᵗ
    ρ : Renameᵗ

------------------------------------------------------------------------
-- 1.  Renaming boundaries and terms
------------------------------------------------------------------------

renᴮ : Renameᵗ → CtxMorph → CtxMorph
renᴮ ρ []          = []
renᴮ ρ (bind A ∷ Θ) = bind (renameᵗ ρ A) ∷ renᴮ ρ Θ
renᴮ ρ (unlock X ∷ Θ) = unlock (ρ X) ∷ renᴮ ρ Θ
renᴮ ρ (lock X ∷ Θ) = lock (ρ X) ∷ renᴮ ρ Θ

repsOf-ren : (ρ : Renameᵗ) (Θ : CtxMorph)
  → repsOf (renᴮ ρ Θ) ≡ map (renameᵗ ρ) (repsOf Θ)
repsOf-ren ρ []             = refl
repsOf-ren ρ (bind A ∷ Θ)   = cong (renameᵗ ρ A ∷_) (repsOf-ren ρ Θ)
repsOf-ren ρ (unlock X ∷ Θ) = repsOf-ren ρ Θ
repsOf-ren ρ (lock X ∷ Θ)   = repsOf-ren ρ Θ

numBinds-ren : (ρ : Renameᵗ) (Θ : CtxMorph) → numBinds (renᴮ ρ Θ) ≡ numBinds Θ
numBinds-ren ρ Θ =
  trans (cong length (repsOf-ren ρ Θ)) (map-length (renameᵗ ρ) (repsOf Θ))

renᴹ : Renameᵗ → Term → Term
renᴹ ρ (` x)          = ` x
renᴹ ρ ($ n)          = $ n
renᴹ ρ (ƛ A ∙ N)      = ƛ renameᵗ ρ A ∙ renᴹ ρ N
renᴹ ρ (L · M)        = renᴹ ρ L · renᴹ ρ M
renᴹ ρ (Λ N)          = Λ (renᴹ (extᵗ ρ) N)
renᴹ ρ (L ·[ B , A ]) = renᴹ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renᴹ ρ (M ⟪ Θ , c ⟫)  =
  renᴹ (extN (numBinds Θ) ρ) M ⟪ renᴮ ρ Θ , renᶜ (extN (numBinds Θ) ρ) c ⟫

-- The weakening a crossing argument undergoes: the boundary's frame grew by
-- `numBinds Θ` binders, so the argument's ANNOTATIONS shift.  Ordinary de
-- Bruijn weakening, not a re-spelling.
wkN : ℕ → Renameᵗ
wkN n X = n + X

wkᴹ : ℕ → Term → Term
wkᴹ n = renᴹ (wkN n)

Inj-wkN : (n : ℕ) → Inj (wkN n)
Inj-wkN zero    eq = eq
Inj-wkN (suc n) eq = Inj-wkN n (Inj-suc eq)

------------------------------------------------------------------------
-- 2.  The type context operations transport (the structural half)
------------------------------------------------------------------------

ren-scope : (Θ : CtxMorph) → Ren ρ Δ Δ′ → Inj ρ
        → Ren ρ (scope Θ Δ) (scope (renᴮ ρ Θ) Δ′)
ren-scope []          r i    = r
ren-scope (bind A ∷ Θ) r i   = ren-scope Θ r i
ren-scope (unlock X ∷ Θ) r i = ren-unmask (ren-scope Θ r i) i
ren-scope (lock X ∷ Θ) r i   = ren-mask (ren-scope Θ r i) i

ren-unlockedScope : (Θ : CtxMorph) → Ren ρ Δ Δ′ → Inj ρ
         → Ren ρ (unlockedScope Θ Δ) (unlockedScope (renᴮ ρ Θ) Δ′)
ren-unlockedScope []          r i    = r
ren-unlockedScope (bind A ∷ Θ) r i   = ren-unlockedScope Θ r i
ren-unlockedScope (unlock X ∷ Θ) r i = ren-unmask (ren-unlockedScope Θ r i) i
ren-unlockedScope (lock X ∷ Θ) r i   = ren-unlockedScope Θ r i

ren-interior : (Θ : CtxMorph) (ρ : Renameᵗ) → Ren ρ Δ Δ′ → Inj ρ
  → Ren (extN (numBinds Θ) ρ) (interior Θ Δ) (interior (renᴮ ρ Θ) Δ′)
ren-interior Θ ρ r i rewrite repsOf-ren ρ Θ =
  ren-pushBinds (repsOf Θ) ρ (ren-scope Θ r i)

ren-convCtx : (Θ : CtxMorph) (ρ : Renameᵗ) → Ren ρ Δ Δ′ → Inj ρ
  → Ren (extN (numBinds Θ) ρ) (convCtx Θ Δ) (convCtx (renᴮ ρ Θ) Δ′)
ren-convCtx Θ ρ r i rewrite repsOf-ren ρ Θ =
  ren-pushBinds (repsOf Θ) ρ (ren-unlockedScope Θ r i)

-- Under the SEQUENTIAL judgement each premise is read on the frame the
-- entry acts on, so each transports by the matching type-context
-- transport: `ren-unlockedScope` for a rep, `ren-scope` for a name.
⊢ᵐ-ren : ∀ {Θ} → Ren ρ Δ Δ′ → Inj ρ → Δ ⊢ᵐ Θ → Δ′ ⊢ᵐ renᴮ ρ Θ
⊢ᵐ-ren                     r i mw[]        = mw[]
⊢ᵐ-ren {Θ = bind A ∷ Θ}    r i (mw-b w b)  =
  mw-b (wf-ren (ren-unlockedScope Θ r i) w) (⊢ᵐ-ren r i b)
⊢ᵐ-ren {Θ = lock X ∷ Θ}    r i (mw-l tv b) =
  mw-l (ren-tv (ren-scope Θ r i) tv) (⊢ᵐ-ren r i b)
⊢ᵐ-ren {Θ = unlock X ∷ Θ}  r i (mw-u lk b) =
  mw-u (ren-∋lk (ren-scope Θ r i) lk) (⊢ᵐ-ren r i b)

------------------------------------------------------------------------
-- 3.  THE RENAMING TRANSPORT
------------------------------------------------------------------------

renΓ : Renameᵗ → Ctx → Ctx
renΓ ρ Γ = map (renameᵗ ρ) Γ

∋⦂-ren : ∀ {Γ x A} (ρ : Renameᵗ) → Γ ∋ x ⦂ A → renΓ ρ Γ ∋ x ⦂ renameᵗ ρ A
∋⦂-ren ρ here      = here
∋⦂-ren ρ (there d) = there (∋⦂-ren ρ d)

⤊-ren : (ρ : Renameᵗ) (Γ : Ctx) → ⤊ (renΓ ρ Γ) ≡ renΓ (extᵗ ρ) (⤊ Γ)
⤊-ren ρ []      = refl
⤊-ren ρ (A ∷ Γ) = cong₂ _∷_ (sym (ren-⇑-comm ρ A)) (⤊-ren ρ Γ)

⊢rename : ∀ {Δ Δ′ Γ M A ρ}
  → Ren ρ Δ Δ′ → Inj ρ
  → Δ  ∣ Γ ⊢ M ⦂ A
    ------------------------------------------------
  → Δ′ ∣ renΓ ρ Γ ⊢ renᴹ ρ M ⦂ renameᵗ ρ A
⊢rename {ρ = ρ} r i (⊢` d)   = ⊢` (∋⦂-ren ρ d)
⊢rename r i ⊢$               = ⊢$
⊢rename r i (⊢ƛ w ⊢N)        = ⊢ƛ (wf-ren r w) (⊢rename r i ⊢N)
⊢rename r i (⊢· ⊢L ⊢M)       = ⊢· (⊢rename r i ⊢L) (⊢rename r i ⊢M)
⊢rename {Γ = Γ} {ρ = ρ} r i (⊢Λ ⊢N) =
  ⊢Λ (subst (λ Γ′ → _ ∣ Γ′ ⊢ _ ⦂ _) (sym (⤊-ren ρ Γ))
            (⊢rename (ren-ext r) (Inj-ext i) ⊢N))
⊢rename {ρ = ρ} r i (⊢·[] {A = A} {B = B} ⊢L w)
  rewrite rename-[]ᵗ-commute ρ B A =
  ⊢·[] (⊢rename r i ⊢L) (wf-ren r w)
⊢rename {Δ′ = Δ′} {ρ = ρ} r i
        (env {Θ = Θ} {c = c} {Bᵢ = Bᵢ} {Bₑ = Bₑ} mw ⊢M ⊢c wE) =
  env (⊢ᵐ-ren r i mw)
      (⊢rename (ren-interior Θ ρ r i) (Inj-extN (numBinds Θ) i) ⊢M)
      cprem
      (wf-ren r wE)
  where
  cprem : convCtx (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (numBinds Θ) ρ) c
            ∶ renameᵗ (extN (numBinds Θ) ρ) Bᵢ
            ⇝ shiftBy (numBinds (renᴮ ρ Θ)) (renameᵗ ρ Bₑ)
  cprem = subst (λ n → convCtx (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (numBinds Θ) ρ) c
                         ∶ renameᵗ (extN (numBinds Θ) ρ) Bᵢ
                         ⇝ shiftBy n (renameᵗ ρ Bₑ))
                (sym (numBinds-ren ρ Θ))
                (subst (λ t → convCtx (renᴮ ρ Θ) Δ′
                                ⊢ renᶜ (extN (numBinds Θ) ρ) c
                                ∶ renameᵗ (extN (numBinds Θ) ρ) Bᵢ ⇝ t)
                       (shiftBy-ren (numBinds Θ) ρ Bₑ)
                       (conv-ren (ren-convCtx Θ ρ r i) ⊢c))

------------------------------------------------------------------------
-- 4.  THE RETAGGING TRANSPORT
------------------------------------------------------------------------

-- THE REFINEMENT A TERM TRAVELS ALONG IS `_⊑ᵃ_` (strong.Ctx §4b), NOT
-- `_⊑_`: a boundary's `unlock X` claims that X is LOCKED, and `le-mu` —
-- the clause that re-exposes a concealed slot — destroys the claim
-- (`⊢ᵐ-⊑ᵃ`, strong.Terms).  TYPES and CONVERSIONS still travel along the
-- full `_⊑_`: `⊑-wf` and `conv-⊑` are applied at `⊑ᵃ→⊑ ls`.
⊢retag : ∀ {Δ Δ′ Γ M A}
  → Δ ⊑ᵃ Δ′
  → Δ  ∣ Γ ⊢ M ⦂ A
    ---------------
  → Δ′ ∣ Γ ⊢ M ⦂ A
⊢retag ls (⊢` d)       = ⊢` d
⊢retag ls ⊢$           = ⊢$
⊢retag ls (⊢ƛ w ⊢N)    = ⊢ƛ (⊑-wf (⊑ᵃ→⊑ ls) w) (⊢retag ls ⊢N)
⊢retag ls (⊢· ⊢L ⊢M)   = ⊢· (⊢retag ls ⊢L) (⊢retag ls ⊢M)
⊢retag ls (⊢Λ ⊢N)      = ⊢Λ (⊢retag (la∷ la-aa ls) ⊢N)
⊢retag ls (⊢·[] ⊢L w)  = ⊢·[] (⊢retag ls ⊢L) (⊑-wf (⊑ᵃ→⊑ ls) w)
⊢retag ls (env {Θ = Θ} mw ⊢M ⊢c wE) =
  env (⊢ᵐ-⊑ᵃ ls mw)
      (⊢retag (⊑ᵃ-interior Θ ls) ⊢M)
      (conv-⊑ (⊑-convCtx Θ (⊑ᵃ→⊑ ls)) ⊢c)
      (⊑-wf (⊑ᵃ→⊑ ls) wE)

------------------------------------------------------------------------
-- 5.  Term substitution
------------------------------------------------------------------------

-- TERM-VARIABLE renaming.  A boundary is TERM-CLOSED — (env) types its body
-- at Γ = [] — so this is the IDENTITY on wrappers, and so is `substᵐ` below.
-- (Shape cherry-picked from v1's `renameᵀᵐ`/`extⁿ`, which live in
-- `git show origin/main:SystemF/agda/strong/BReduction.agda`.)
extⁿ : (ℕ → ℕ) → (ℕ → ℕ)
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renⁿ : (ℕ → ℕ) → Term → Term
renⁿ ρ (` x)          = ` (ρ x)
renⁿ ρ ($ n)          = $ n
renⁿ ρ (ƛ A ∙ N)      = ƛ A ∙ renⁿ (extⁿ ρ) N
renⁿ ρ (L · M)        = renⁿ ρ L · renⁿ ρ M
renⁿ ρ (Λ N)          = Λ (renⁿ ρ N)
renⁿ ρ (L ·[ B , A ]) = renⁿ ρ L ·[ B , A ]
renⁿ ρ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

-- The TYPE-variable weakening OF A TERM: what a Λ imposes on everything
-- that crosses under it.  Note it is NOT the identity on a wrapper — a
-- wrapper is term-closed, not type-closed, and its `seal`/`unseal` NAMES
-- shift with the frame.
⇑ᴹ : Term → Term
⇑ᴹ = renᴹ suc

-- Weakening by one term variable.  It must protect the ƛ-bound slot, hence
-- `extⁿ`: `shiftᵐ (ƛ A ∙ ` 0)` is `ƛ A ∙ ` 0`, not `ƛ A ∙ ` 1`.
shiftᵐ : Term → Term
shiftᵐ = renⁿ suc

extᵐ : (ℕ → Term) → (ℕ → Term)
extᵐ σ zero    = ` zero
extᵐ σ (suc x) = shiftᵐ (σ x)

-- THE Λ CLAUSE.  `⊢Λ` types its body at the SHIFTED term context ⤊ Γ, so
-- an image of σ — a term whose annotations, boundary reps and conversion
-- names are written over the EXTERIOR type context — must be shifted
-- past the new Λ-bound slot before it may be planted inside.  (Same
-- clause as v1's `substᵀᵐ`; v2's ⊢Λ shifts Γ exactly as v1's did.)
substᵐ : (ℕ → Term) → Term → Term
substᵐ σ (` x)          = σ x
substᵐ σ ($ n)          = $ n
substᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵐ (extᵐ σ) N
substᵐ σ (L · M)        = substᵐ σ L · substᵐ σ M
substᵐ σ (Λ N)          = Λ (substᵐ (λ x → ⇑ᴹ (σ x)) N)
substᵐ σ (L ·[ B , A ]) = substᵐ σ L ·[ B , A ]
substᵐ σ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

infix 8 _[_]ᵐ
_[_]ᵐ : Term → Term → Term
N [ W ]ᵐ = substᵐ (λ { zero → W ; (suc x) → ` x }) N

------------------------------------------------------------------------
-- 6.  THE SUBSTITUTION TYPING LEMMA
------------------------------------------------------------------------

-- Pulling a TERM-context lookup back through `map`.  Needed at every ⊢Λ,
-- where the body's term context is ⤊ Γ = map ⇑ᵗ Γ.  (v1's `∋-map⁻`.)
∋⦂-map⁻ : ∀ {f : Ty → Ty} {Γ x A′}
  → map f Γ ∋ x ⦂ A′
    -----------------------------------------
  → ∃[ A ] ((A′ ≡ f A) × (Γ ∋ x ⦂ A))
∋⦂-map⁻ {Γ = []}      ()
∋⦂-map⁻ {Γ = A₀ ∷ Γ₀} here      = A₀ , refl , here
∋⦂-map⁻ {Γ = A₀ ∷ Γ₀} (there d) with ∋⦂-map⁻ d
... | A , eq , q = A , eq , there q

∋⦂-⤊ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ⤊ Γ ∋ x ⦂ ⇑ᵗ A
∋⦂-⤊ here      = here
∋⦂-⤊ (there d) = there (∋⦂-⤊ d)

-- A TERM renaming survives the type-context shift a Λ imposes: the term
-- variables are untouched, only their types are shifted.
⤊-∋ⁿ : ∀ {ρ : ℕ → ℕ} {Γ Γ′}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
    -------------------------------------------
  → (∀ {x B} → ⤊ Γ ∋ x ⦂ B → ⤊ Γ′ ∋ ρ x ⦂ B)
⤊-∋ⁿ h d with ∋⦂-map⁻ d
... | A , refl , q = ∋⦂-⤊ (h q)

extⁿ-∋ : ∀ {ρ : ℕ → ℕ} {Γ Γ′ A}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
    ---------------------------------------------------------------
  → (∀ {x B} → (A ∷ Γ) ∋ x ⦂ B → (A ∷ Γ′) ∋ extⁿ ρ x ⦂ B)
extⁿ-∋ h here      = here
extⁿ-∋ h (there d) = there (h d)

-- Term-variable renaming preserves typing.  The (env) case is LITERALLY the
-- premises back: `renⁿ` is the identity on a wrapper, and (env)'s conclusion
-- holds at an ARBITRARY term context.
⊢renⁿ : ∀ {Δ Γ Γ′ M A} {ρ : ℕ → ℕ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
  → Δ ∣ Γ  ⊢ M ⦂ A
    ---------------------------
  → Δ ∣ Γ′ ⊢ renⁿ ρ M ⦂ A
⊢renⁿ h (⊢` d)            = ⊢` (h d)
⊢renⁿ h ⊢$                = ⊢$
⊢renⁿ h (⊢ƛ w ⊢N)         = ⊢ƛ w (⊢renⁿ (extⁿ-∋ h) ⊢N)
⊢renⁿ h (⊢· ⊢L ⊢M)        = ⊢· (⊢renⁿ h ⊢L) (⊢renⁿ h ⊢M)
⊢renⁿ h (⊢Λ ⊢N)           = ⊢Λ (⊢renⁿ (⤊-∋ⁿ h) ⊢N)
⊢renⁿ h (⊢·[] ⊢L w)       = ⊢·[] (⊢renⁿ h ⊢L) w
⊢renⁿ h (env mw ⊢M ⊢c wE) = env mw ⊢M ⊢c wE

-- The one type-context renaming the substitution lemma needs: pushing a
-- fresh Λ-bound slot on the front.
Ren-wk : ∀ {Δ E} → Ren suc Δ (E ∷ Δ)
Ren-wk = mkRen es

-- Pushing a term substitution under a Λ.  Every image is shifted by ⇑ᴹ,
-- which is `⊢rename` at ρ = suc — `Ren-wk` for the entry transport and
-- `Inj-suc` for the ONE structural hypothesis (positional masking).  No
-- knowledge premise is needed: a name is carried, never a spelling.
⇑ᴹ-⊢ : ∀ {σ : ℕ → Term} {Δ Γ Γ′}
  → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∣ Γ′ ⊢ σ x ⦂ B)
    --------------------------------------------------------------------
  → (∀ {x B} → ⤊ Γ ∋ x ⦂ B → (abst ∷ Δ) ∣ ⤊ Γ′ ⊢ ⇑ᴹ (σ x) ⦂ B)
⇑ᴹ-⊢ h d with ∋⦂-map⁻ d
... | A , refl , q = ⊢rename Ren-wk Inj-suc (h q)

extᵐ-⊢ : ∀ {σ : ℕ → Term} {Δ Γ Γ′ A}
  → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∣ Γ′ ⊢ σ x ⦂ B)
    ------------------------------------------------------------------
  → (∀ {x B} → (A ∷ Γ) ∋ x ⦂ B → Δ ∣ (A ∷ Γ′) ⊢ extᵐ σ x ⦂ B)
extᵐ-⊢ h here      = ⊢` here
extᵐ-⊢ h (there d) = ⊢renⁿ there (h d)

-- THE SIMULTANEOUS SUBSTITUTION LEMMA.  Two cases carry the whole story:
-- (env) is trivial because a wrapper is term-closed, and ⊢Λ is `⇑ᴹ-⊢`,
-- i.e. `⊢rename` at suc.
⊢substᵐ : ∀ {σ : ℕ → Term} {Δ Γ Γ′ N B}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Γ′ ⊢ σ x ⦂ A)
  → Δ ∣ Γ  ⊢ N ⦂ B
    ----------------------------
  → Δ ∣ Γ′ ⊢ substᵐ σ N ⦂ B
⊢substᵐ h (⊢` d)            = h d
⊢substᵐ h ⊢$                = ⊢$
⊢substᵐ h (⊢ƛ w ⊢N)         = ⊢ƛ w (⊢substᵐ (extᵐ-⊢ h) ⊢N)
⊢substᵐ h (⊢· ⊢L ⊢M)        = ⊢· (⊢substᵐ h ⊢L) (⊢substᵐ h ⊢M)
⊢substᵐ h (⊢Λ ⊢N)           = ⊢Λ (⊢substᵐ (⇑ᴹ-⊢ h) ⊢N)
⊢substᵐ h (⊢·[] ⊢L w)       = ⊢·[] (⊢substᵐ h ⊢L) w
⊢substᵐ h (env mw ⊢M ⊢c wE) = env mw ⊢M ⊢c wE

-- THE SUBSTITUTION TYPING LEMMA — what Beta's preservation case consumes.
⊢subst : ∀ {Δ Γ A B N W}
  → Δ ∣ (A ∷ Γ) ⊢ N ⦂ B
  → Δ ∣ Γ ⊢ W ⦂ A
    -----------------------------
  → Δ ∣ Γ ⊢ N [ W ]ᵐ ⦂ B
⊢subst ⊢N ⊢W = ⊢substᵐ (λ { here → ⊢W ; (there d) → ⊢` d }) ⊢N

-- Beta preservation, ready to be wired into the preservation theorem.
-- (⊢·) is the only rule that can conclude an application — (env) concludes a
-- wrapper — so the inversion is a single clause.
preserve-Beta : ∀ {Δ Γ A B N W}
  → Δ ∣ Γ ⊢ (ƛ A ∙ N) · W ⦂ B
    ---------------------------
  → Δ ∣ Γ ⊢ N [ W ]ᵐ ⦂ B
preserve-Beta (⊢· (⊢ƛ _ ⊢N) ⊢W) = ⊢subst ⊢N ⊢W
