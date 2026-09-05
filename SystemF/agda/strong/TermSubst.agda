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

renᴮ : Renameᵗ → BCtx → BCtx
renᴮ ρ []          = []
renᴮ ρ (own A ∷ Θ) = own (renameᵗ ρ A) ∷ renᴮ ρ Θ
renᴮ ρ (ali X ∷ Θ) = ali (ρ X) ∷ renᴮ ρ Θ
renᴮ ρ (cnc X ∷ Θ) = cnc (ρ X) ∷ renᴮ ρ Θ

reps-ren : (ρ : Renameᵗ) (Θ : BCtx)
  → reps (renᴮ ρ Θ) ≡ map (renameᵗ ρ) (reps Θ)
reps-ren ρ []          = refl
reps-ren ρ (own A ∷ Θ) = cong (renameᵗ ρ A ∷_) (reps-ren ρ Θ)
reps-ren ρ (ali X ∷ Θ) = reps-ren ρ Θ
reps-ren ρ (cnc X ∷ Θ) = reps-ren ρ Θ

nrev-ren : (ρ : Renameᵗ) (Θ : BCtx) → nrev (renᴮ ρ Θ) ≡ nrev Θ
nrev-ren ρ Θ =
  trans (cong length (reps-ren ρ Θ)) (map-length (renameᵗ ρ) (reps Θ))

renᴹ : Renameᵗ → Term → Term
renᴹ ρ (` x)          = ` x
renᴹ ρ ($ n)          = $ n
renᴹ ρ (ƛ A ∙ N)      = ƛ renameᵗ ρ A ∙ renᴹ ρ N
renᴹ ρ (L · M)        = renᴹ ρ L · renᴹ ρ M
renᴹ ρ (Λ N)          = Λ (renᴹ (extᵗ ρ) N)
renᴹ ρ (L ·[ B , A ]) = renᴹ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renᴹ ρ (M ⟪ Θ , c ⟫)  =
  renᴹ (extN (nrev Θ) ρ) M ⟪ renᴮ ρ Θ , renᶜ (extN (nrev Θ) ρ) c ⟫

-- The weakening a crossing argument undergoes: the boundary's frame grew by
-- `nrev Θ` binders, so the argument's ANNOTATIONS shift.  Ordinary de Bruijn
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

ren-scp : (Θ : BCtx) → Ren ρ Δ Δ′ → Inj ρ
        → Ren ρ (scp Θ Δ) (scp (renᴮ ρ Θ) Δ′)
ren-scp []          r i = r
ren-scp (own A ∷ Θ) r i = ren-scp Θ r i
ren-scp (ali X ∷ Θ) r i = ren-unmask (ren-scp Θ r i) i
ren-scp (cnc X ∷ Θ) r i = ren-mask (ren-scp Θ r i) i

ren-fscp : (Θ : BCtx) → Ren ρ Δ Δ′ → Inj ρ
         → Ren ρ (fscp Θ Δ) (fscp (renᴮ ρ Θ) Δ′)
ren-fscp []          r i = r
ren-fscp (own A ∷ Θ) r i = ren-fscp Θ r i
ren-fscp (ali X ∷ Θ) r i = ren-unmask (ren-fscp Θ r i) i
ren-fscp (cnc X ∷ Θ) r i = ren-fscp Θ r i

ren-intC : (Θ : BCtx) (ρ : Renameᵗ) → Ren ρ Δ Δ′ → Inj ρ
  → Ren (extN (nrev Θ) ρ) (intC Θ Δ) (intC (renᴮ ρ Θ) Δ′)
ren-intC Θ ρ r i rewrite reps-ren ρ Θ = ren-prep (reps Θ) ρ (ren-scp Θ r i)

ren-fceC : (Θ : BCtx) (ρ : Renameᵗ) → Ren ρ Δ Δ′ → Inj ρ
  → Ren (extN (nrev Θ) ρ) (fceC Θ Δ) (fceC (renᴮ ρ Θ) Δ′)
ren-fceC Θ ρ r i rewrite reps-ren ρ Θ = ren-prep (reps Θ) ρ (ren-fscp Θ r i)

Bwf-ren : ∀ {Θ} → Ren ρ Δ Δ′ → Inj ρ → Bwf Δ Θ → Bwf Δ′ (renᴮ ρ Θ)
Bwf-ren r i bw[]        = bw[]
Bwf-ren r i (bw-o w b)  = bw-o (wf-ren r w) (Bwf-ren r i b)
Bwf-ren r i (bw-c tv b) = bw-c (ren-tv r tv) (Bwf-ren r i b)
Bwf-ren r i (bw-a d b)  = bw-a (ren∋ r d) (Bwf-ren r i b)

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
      (⊢rename (ren-intC Θ ρ r i) (Inj-extN (nrev Θ) i) ⊢M)
      cprem
      (wf-ren r wE)
  where
  cprem : fceC (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (nrev Θ) ρ) c
            ∶ renameᵗ (extN (nrev Θ) ρ) Bᵢ
            ⇝ liftN (nrev (renᴮ ρ Θ)) (renameᵗ ρ Bₑ) ∙ p
  cprem = subst (λ n → fceC (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (nrev Θ) ρ) c
                         ∶ renameᵗ (extN (nrev Θ) ρ) Bᵢ
                         ⇝ liftN n (renameᵗ ρ Bₑ) ∙ p)
                (sym (nrev-ren ρ Θ))
                (subst (λ t → fceC (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (nrev Θ) ρ) c
                                ∶ renameᵗ (extN (nrev Θ) ρ) Bᵢ ⇝ t ∙ p)
                       (liftN-ren (nrev Θ) ρ Bₑ)
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

shiftᵐ : Term → Term
shiftᵐ (` x)          = ` suc x
shiftᵐ ($ n)          = $ n
shiftᵐ (ƛ A ∙ N)      = ƛ A ∙ shiftᵐ N
shiftᵐ (L · M)        = shiftᵐ L · shiftᵐ M
shiftᵐ (Λ N)          = Λ (shiftᵐ N)
shiftᵐ (L ·[ B , A ]) = shiftᵐ L ·[ B , A ]
shiftᵐ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

extᵐ : (ℕ → Term) → (ℕ → Term)
extᵐ σ zero    = ` zero
extᵐ σ (suc x) = shiftᵐ (σ x)

substᵐ : (ℕ → Term) → Term → Term
substᵐ σ (` x)          = σ x
substᵐ σ ($ n)          = $ n
substᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵐ (extᵐ σ) N
substᵐ σ (L · M)        = substᵐ σ L · substᵐ σ M
substᵐ σ (Λ N)          = Λ (substᵐ σ N)
substᵐ σ (L ·[ B , A ]) = substᵐ σ L ·[ B , A ]
substᵐ σ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

infix 8 _[_]ᵐ
_[_]ᵐ : Term → Term → Term
N [ W ]ᵐ = substᵐ (λ { zero → W ; (suc x) → ` x }) N
