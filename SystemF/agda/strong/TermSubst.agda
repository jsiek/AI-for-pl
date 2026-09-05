module strong.TermSubst where

-- Strong System F — SUBSTITUTION AND THE TWO TRANSPORTS.
--
-- Term substitution is ordinary: boundaries are term-closed, so a wrapper is
-- never descended into.  The interesting content is the pair of TYPE-LEVEL
-- transports the ownership design has to pay for, and both come out cheap:
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

reps-ren : (ρ : Renameᵗ) (Θ : CtxMorph)
  → reps (renᴮ ρ Θ) ≡ map (renameᵗ ρ) (reps Θ)
reps-ren ρ []          = refl
reps-ren ρ (bind A ∷ Θ) = cong (renameᵗ ρ A ∷_) (reps-ren ρ Θ)
reps-ren ρ (unlock X ∷ Θ) = reps-ren ρ Θ
reps-ren ρ (lock X ∷ Θ) = reps-ren ρ Θ

nbind-ren : (ρ : Renameᵗ) (Θ : CtxMorph) → nbind (renᴮ ρ Θ) ≡ nbind Θ
nbind-ren ρ Θ =
  trans (cong length (reps-ren ρ Θ)) (map-length (renameᵗ ρ) (reps Θ))

renᴹ : Renameᵗ → Term → Term
renᴹ ρ (` x)          = ` x
renᴹ ρ ($ n)          = $ n
renᴹ ρ (ƛ A ∙ N)      = ƛ renameᵗ ρ A ∙ renᴹ ρ N
renᴹ ρ (L · M)        = renᴹ ρ L · renᴹ ρ M
renᴹ ρ (Λ N)          = Λ (renᴹ (extᵗ ρ) N)
renᴹ ρ (L ·[ B , A ]) = renᴹ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renᴹ ρ (M ⟪ Θ , c ⟫)  =
  renᴹ (extN (nbind Θ) ρ) M ⟪ renᴮ ρ Θ , renᶜ (extN (nbind Θ) ρ) c ⟫

-- The weakening a crossing argument undergoes: the boundary's frame grew by
-- `nbind Θ` binders, so the argument's ANNOTATIONS shift.  Ordinary de Bruijn
-- weakening, not a re-spelling.
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

ren-scp : (Θ : CtxMorph) → Ren ρ Δ Δ′ → Inj ρ
        → Ren ρ (scp Θ Δ) (scp (renᴮ ρ Θ) Δ′)
ren-scp []          r i = r
ren-scp (bind A ∷ Θ) r i = ren-scp Θ r i
ren-scp (unlock X ∷ Θ) r i = ren-unmask (ren-scp Θ r i) i
ren-scp (lock X ∷ Θ) r i = ren-mask (ren-scp Θ r i) i

ren-fscp : (Θ : CtxMorph) → Ren ρ Δ Δ′ → Inj ρ
         → Ren ρ (fscp Θ Δ) (fscp (renᴮ ρ Θ) Δ′)
ren-fscp []          r i = r
ren-fscp (bind A ∷ Θ) r i = ren-fscp Θ r i
ren-fscp (unlock X ∷ Θ) r i = ren-unmask (ren-fscp Θ r i) i
ren-fscp (lock X ∷ Θ) r i = ren-fscp Θ r i

ren-intC : (Θ : CtxMorph) (ρ : Renameᵗ) → Ren ρ Δ Δ′ → Inj ρ
  → Ren (extN (nbind Θ) ρ) (intC Θ Δ) (intC (renᴮ ρ Θ) Δ′)
ren-intC Θ ρ r i rewrite reps-ren ρ Θ = ren-prep (reps Θ) ρ (ren-scp Θ r i)

ren-fceC : (Θ : CtxMorph) (ρ : Renameᵗ) → Ren ρ Δ Δ′ → Inj ρ
  → Ren (extN (nbind Θ) ρ) (fceC Θ Δ) (fceC (renᴮ ρ Θ) Δ′)
ren-fceC Θ ρ r i rewrite reps-ren ρ Θ = ren-prep (reps Θ) ρ (ren-fscp Θ r i)

Bwf-ren : ∀ {Θ} → Ren ρ Δ Δ′ → Inj ρ → Bwf Δ Θ → Bwf Δ′ (renᴮ ρ Θ)
Bwf-ren r i bw[]        = bw[]
Bwf-ren r i (bw-b w b)  = bw-b (wf-ren r w) (Bwf-ren r i b)
Bwf-ren r i (bw-l tv b) = bw-l (ren-tv r tv) (Bwf-ren r i b)
Bwf-ren r i (bw-u d b)  = bw-u (ren∋ r d) (Bwf-ren r i b)

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
        (env {Θ = Θ} {c = c} {Bᵢ = Bᵢ} {Bₑ = Bₑ} {p = p} bw ⊢M ⊢c wE) =
  env (Bwf-ren r i bw)
      (⊢rename (ren-intC Θ ρ r i) (Inj-extN (nbind Θ) i) ⊢M)
      cprem
      (wf-ren r wE)
  where
  cprem : fceC (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (nbind Θ) ρ) c
            ∶ renameᵗ (extN (nbind Θ) ρ) Bᵢ
            ⇝ liftN (nbind (renᴮ ρ Θ)) (renameᵗ ρ Bₑ) ∙ p
  cprem = subst (λ n → fceC (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (nbind Θ) ρ) c
                         ∶ renameᵗ (extN (nbind Θ) ρ) Bᵢ
                         ⇝ liftN n (renameᵗ ρ Bₑ) ∙ p)
                (sym (nbind-ren ρ Θ))
                (subst (λ t → fceC (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (nbind Θ) ρ) c
                                ∶ renameᵗ (extN (nbind Θ) ρ) Bᵢ ⇝ t ∙ p)
                       (liftN-ren (nbind Θ) ρ Bₑ)
                       (conv-ren (ren-fceC Θ ρ r i) ⊢c))

------------------------------------------------------------------------
-- 4.  THE RETAGGING TRANSPORT
------------------------------------------------------------------------

⊢retag : ∀ {Δ Δ′ Γ M A}
  → Δ ⊑ Δ′
  → Δ  ∣ Γ ⊢ M ⦂ A
    ---------------
  → Δ′ ∣ Γ ⊢ M ⦂ A
⊢retag ls (⊢` d)       = ⊢` d
⊢retag ls ⊢$           = ⊢$
⊢retag ls (⊢ƛ w ⊢N)    = ⊢ƛ (⊑-wf ls w) (⊢retag ls ⊢N)
⊢retag ls (⊢· ⊢L ⊢M)   = ⊢· (⊢retag ls ⊢L) (⊢retag ls ⊢M)
⊢retag ls (⊢Λ ⊢N)      = ⊢Λ (⊢retag (le∷ le-aa ls) ⊢N)
⊢retag ls (⊢·[] ⊢L w)  = ⊢·[] (⊢retag ls ⊢L) (⊑-wf ls w)
⊢retag ls (env {Θ = Θ} bw ⊢M ⊢c wE) =
  env (Bwf-⊑ ls bw)
      (⊢retag (⊑-intC Θ ls) ⊢M)
      (conv-⊑ (⊑-fceC Θ ls) ⊢c)
      (⊑-wf ls wE)

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

-- THE Λ CLAUSE.  `⊢Λ` types its body at the SHIFTED term context ⤊ Γ, so an
-- image of σ — a term whose annotations, boundary reps and face names are
-- written over the EXTERIOR type context — must be shifted past the new
-- Λ-bound slot before it may be planted inside.  (Same clause as v1's
-- `substᵀᵐ`; v2's ⊢Λ shifts Γ exactly as v1's did.)
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
⊢renⁿ h (env bw ⊢M ⊢c wE) = env bw ⊢M ⊢c wE

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
⊢substᵐ h (env bw ⊢M ⊢c wE) = env bw ⊢M ⊢c wE

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
