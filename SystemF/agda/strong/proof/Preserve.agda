module strong.proof.Preserve where

-- PRESERVATION for the v2 conversion-boundary calculus — the lemma chains.
--
-- §1  TYPE WELL-FORMEDNESS OF A TYPED TERM (`⊢ᵗ-of`).  No context
--     well-formedness judgment (`⊢ᶜ Δ`, the store-typing pattern) is
--     needed: every rep a rule reads back out of the type context arrives
--     with its well-formedness already on the derivation — `env`'s last
--     premise `Δ ⊢ᵗ Bₑ` — and `unsealAt`'s minted face reads its rep from
--     the OWNER THE RULE ITSELF JUST BOUND, whose rep is `⊢·[]`'s premise.
--
-- §2  THE MINTED FACE (`⊢unsealAt`/`⊢sealAt`), TyBeta's contractum face,
--     proven mutually over the face type exactly as the two functions are
--     defined.
--
-- §3  the per-rule cases that hold, one lemma each.
--
-- §4  `preserve`, over a module parameterized by the four cases that do
--     NOT hold as the rules currently stand (see proof/PreserveObstruct
--     for the machine-checked counterexamples).

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
open import strong.TypeSubst
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

private
  variable
    Δ Δ′ : Ctxᵗ
    Γ : Ctx
    A B C : Ty
    X Y : ℕ
    ρ : Renameᵗ

------------------------------------------------------------------------
-- §1  Well-formedness of the type a derivation concludes
------------------------------------------------------------------------

-- Visibility is reflected by renaming: a renamed entry is visible only if
-- the entry was.  (`blk` is the only invisible shape, and `renᵉ` keeps it.)
Vis-ren⁻ : ∀ {E} → Vis (renᵉ ρ E) → Vis E
Vis-ren⁻ {E = abst}   v  = vis-a
Vis-ren⁻ {E = bind A} v  = vis-b
Vis-ren⁻ {E = blk E}  ()

∋tv-tail : ∀ {E} → (E ∷ Δ) ∋tv suc X → Δ ∋tv X
∋tv-tail (_ , es d , v) = _ , d , Vis-ren⁻ v

-- A type substitution is well formed when it sends every NAMEABLE slot to
-- a well-formed type.
SubWf : Ctxᵗ → Ctxᵗ → Substᵗ → Set
SubWf Δ Δ′ σ = ∀ {X} → Δ ∋tv X → Δ′ ⊢ᵗ σ X

SubWf-ext : ∀ {σ} → SubWf Δ Δ′ σ → SubWf (abst ∷ Δ) (abst ∷ Δ′) (extsᵗ σ)
SubWf-ext h {zero}  tv = wf-var (abst , ez , vis-a)
SubWf-ext h {suc X} tv = wf-ren Ren-wk (h (∋tv-tail tv))

wf-substᵗ : ∀ {σ} → SubWf Δ Δ′ σ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ substᵗ σ A
wf-substᵗ h (wf-var tv)  = h tv
wf-substᵗ h wf-ℕ         = wf-ℕ
wf-substᵗ h wf-𝔹         = wf-𝔹
wf-substᵗ h (wf-⇒ wA wB) = wf-⇒ (wf-substᵗ h wA) (wf-substᵗ h wB)
wf-substᵗ h (wf-∀ wA)    = wf-∀ (wf-substᵗ (SubWf-ext h) wA)

wf-[]ᵗ : (abst ∷ Δ) ⊢ᵗ B → Δ ⊢ᵗ A → Δ ⊢ᵗ B [ A ]ᵗ
wf-[]ᵗ {A = A} wB wA = wf-substᵗ h wB
  where
  h : SubWf _ _ (singleTyEnv A)
  h {zero}  tv = wA
  h {suc X} tv = wf-var (∋tv-tail tv)

-- Every type in the TERM context is well formed.
CtxWf : Ctxᵗ → Ctx → Set
CtxWf Δ Γ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ⊢ᵗ A

CtxWf-[] : CtxWf Δ []
CtxWf-[] ()

CtxWf-∷ : Δ ⊢ᵗ A → CtxWf Δ Γ → CtxWf Δ (A ∷ Γ)
CtxWf-∷ w h here      = w
CtxWf-∷ w h (there d) = h d

CtxWf-⤊ : CtxWf Δ Γ → CtxWf (abst ∷ Δ) (⤊ Γ)
CtxWf-⤊ h d with ∋⦂-map⁻ d
... | A , refl , q = wf-ren Ren-wk (h q)

-- THE TYPE OF A TYPED TERM IS WELL FORMED.  This is what replaces `⊢ᶜ Δ`
-- at every site the endgame note expected to need it: an `env` node hands
-- back `Δ ⊢ᵗ Bₑ` directly, and `⊢·[]` hands back the instantiating type.
⊢ᵗ-of : ∀ {M} → CtxWf Δ Γ → Δ ∣ Γ ⊢ M ⦂ A → Δ ⊢ᵗ A
⊢ᵗ-of h (⊢` d)             = h d
⊢ᵗ-of h ⊢$                 = wf-ℕ
⊢ᵗ-of h (⊢ƛ w ⊢N)          = wf-⇒ w (⊢ᵗ-of (CtxWf-∷ w h) ⊢N)
⊢ᵗ-of h (⊢· ⊢L ⊢M) with ⊢ᵗ-of h ⊢L
... | wf-⇒ wA wB           = wB
⊢ᵗ-of h (⊢Λ ⊢N)            = wf-∀ (⊢ᵗ-of (CtxWf-⤊ h) ⊢N)
⊢ᵗ-of h (⊢·[] ⊢L w) with ⊢ᵗ-of h ⊢L
... | wf-∀ wB              = wf-[]ᵗ wB w
⊢ᵗ-of h (env _ _ _ wE)     = wE

------------------------------------------------------------------------
-- §2  The face TyBeta mints
------------------------------------------------------------------------

-- `unsealAt X B` reveals X inside B; the exterior face is B with X
-- replaced by the OWNER'S REP — `_[_:=_]ᵗ`, the in-place substitution
-- (the concealed variable stays on the type context, so nothing shifts).

-- The two reduction facts about `single-at`.  They are stated against
-- Types' `_≟_`, which is the decision `single-at` itself branches on.
single-at-hit : (X : ℕ) (A : Ty) → single-at X A X ≡ A
single-at-hit X A with X ≟ X
... | yes _  = refl
... | no  ne = ⊥-elim (ne refl)

single-at-miss : (X Y : ℕ) (A : Ty) → ¬ (X ≡ Y) → single-at X A Y ≡ ` Y
single-at-miss X Y A ne with X ≟ Y
... | yes eq = ⊥-elim (ne eq)
... | no  _  = refl

-- Pushing the in-place substitution under a `∀ shifts BOTH the slot and
-- the rep — exactly `unsealAt`'s / `sealAt`'s own `∀ clause.
subst-at-∀ : (X : ℕ) (A B : Ty)
  → (`∀ B) [ X := A ]ᵗ ≡ `∀ (B [ suc X := ⇑ᵗ A ]ᵗ)
subst-at-∀ X A B = cong `∀ (subst-cong ext-at B)
  where
  ext-at : (Y : ℕ) → extsᵗ (single-at X A) Y ≡ single-at (suc X) (⇑ᵗ A) Y
  ext-at zero    = refl
  ext-at (suc Y) with X ≟ℕ Y
  ... | yes refl =
    trans (cong ⇑ᵗ (single-at-hit X A))
          (sym (single-at-hit (suc X) (⇑ᵗ A)))
  ... | no ne =
    trans (cong ⇑ᵗ (single-at-miss X Y A ne))
          (sym (single-at-miss (suc X) (suc Y) (⇑ᵗ A)
                               (λ eq → ne (suc-inj eq))))
    where
    suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl

-- Substituting the SHIFTED rep at slot 0 is the shift of the ordinary
-- single substitution — the equation TyBeta's face has to satisfy.
subst-at-0 : (A B : Ty) → B [ 0 := ⇑ᵗ A ]ᵗ ≡ ⇑ᵗ (B [ A ]ᵗ)
subst-at-0 A B =
  trans (subst-cong env-eq B)
        (sym (rename-subst suc (singleTyEnv A) B))
  where
  env-eq : (Y : ℕ) → single-at 0 (⇑ᵗ A) Y ≡ renameᵗ suc (singleTyEnv A Y)
  env-eq zero    = refl
  env-eq (suc Y) = refl

-- THE MINTED FACE, both polarities, mutually.
mutual
  ⊢unsealAt : Δ ∋ X := A → Δ ⊢ᵗ B
    → Δ ⊢ unsealAt X B ∶ B ⇝ B [ X := A ]ᵗ ∙ ↑ˢ
  ⊢unsealAt {X = X} {A = A} {B = ` Y} d (wf-var tv) with X ≟ℕ Y
  ... | yes refl rewrite single-at-hit X A       = conv-unseal d
  ... | no  ne   rewrite single-at-miss X Y A ne = conv-idv tv
  ⊢unsealAt d wf-ℕ = conv-id base-ℕ
  ⊢unsealAt d wf-𝔹 = conv-id base-𝔹
  ⊢unsealAt d (wf-⇒ wA wB) = conv-fun (⊢sealAt d wA) (⊢unsealAt d wB)
  ⊢unsealAt {X = X} {A = A} {B = `∀ B} d (wf-∀ wB)
    rewrite subst-at-∀ X A B = conv-all (⊢unsealAt (es d) wB)

  ⊢sealAt : Δ ∋ X := A → Δ ⊢ᵗ B
    → Δ ⊢ sealAt X B ∶ B [ X := A ]ᵗ ⇝ B ∙ ↓ˢ
  ⊢sealAt {X = X} {A = A} {B = ` Y} d (wf-var tv) with X ≟ℕ Y
  ... | yes refl rewrite single-at-hit X A       = conv-seal d
  ... | no  ne   rewrite single-at-miss X Y A ne = conv-idv tv
  ⊢sealAt d wf-ℕ = conv-id base-ℕ
  ⊢sealAt d wf-𝔹 = conv-id base-𝔹
  ⊢sealAt d (wf-⇒ wA wB) = conv-fun (⊢unsealAt d wA) (⊢sealAt d wB)
  ⊢sealAt {X = X} {A = A} {B = `∀ B} d (wf-∀ wB)
    rewrite subst-at-∀ X A B = conv-all (⊢sealAt (es d) wB)

------------------------------------------------------------------------
-- §3  The rule cases that hold
------------------------------------------------------------------------

-- A base type survives no lifting but its own.
ren-ℕ⁻ : renameᵗ ρ A ≡ `ℕ → A ≡ `ℕ
ren-ℕ⁻ {A = ` X}   ()
ren-ℕ⁻ {A = `ℕ}    refl = refl
ren-ℕ⁻ {A = `𝔹}    ()
ren-ℕ⁻ {A = A ⇒ B} ()
ren-ℕ⁻ {A = `∀ A}  ()

liftN-ℕ⁻ : (n : ℕ) → liftN n A ≡ `ℕ → A ≡ `ℕ
liftN-ℕ⁻ zero    eq = eq
liftN-ℕ⁻ (suc n) eq = liftN-ℕ⁻ n (ren-ℕ⁻ eq)

-- ── TYBETA ─────────────────────────────────────────────────────────────
-- The boundary is BORN.  Three moves: the interior is RETAGGED (the slot
-- the Λ bound abstractly is now the OWNER — `le-ao`, the one ⊑ᵉ clause
-- that refines an `abst`), the face is MINTED by `⊢unsealAt` at the rep
-- the owner was just given, and the exterior face equation is `subst-at-0`.
preserve-TyBeta : ∀ {N B A}
  → Δ ∣ [] ⊢ (Λ N) ·[ B , A ] ⦂ C
    ------------------------------------------------------
  → Δ ∣ [] ⊢ N ⟪ bind A ∷ [] , unsealAt 0 B ⟫ ⦂ C
preserve-TyBeta {Δ = Δ} {N = N} {B = B} {A = A} (⊢·[] (⊢Λ ⊢N) wA)
  with ⊢ᵗ-of CtxWf-[] (⊢Λ ⊢N)
... | wf-∀ wB =
  env {p = ↑ˢ} (bw-b wA bw[])
      (⊢retag refine ⊢N)
      face
      (wf-[]ᵗ wB wA)
  where
  refine : (abst ∷ Δ) ⊑ (bind A ∷ Δ)
  refine = le∷ le-ao (⊑-refl Δ)

  face : (bind A ∷ Δ) ⊢ unsealAt 0 B ∶ B ⇝ liftN 1 (B [ A ]ᵗ) ∙ ↑ˢ
  face rewrite sym (subst-at-0 A B) = ⊢unsealAt ez (⊑-wf refine wB)

-- ── DROP$ ──────────────────────────────────────────────────────────────
-- `⊢$` types a numeral anywhere; the only content is that the boundary's
-- exterior type really is `ℕ, which the identity face forces.
preserve-Drop$ : ∀ {n Θ}
  → Base A
  → Δ ∣ [] ⊢ ($ n) ⟪ Θ , id A ⟫ ⦂ C
    -------------------------------
  → Δ ∣ [] ⊢ $ n ⦂ C
preserve-Drop$ {C = C} bA (env {Θ = Θ} bw ⊢$ ⊢c wE)
  rewrite liftN-ℕ⁻ {A = C} (nbind Θ) (sym (conv-id-refl ⊢c)) = ⊢$

------------------------------------------------------------------------
-- §4  The four cases that do NOT hold, and `preserve` over them
------------------------------------------------------------------------

-- Each of the four statements below is the preservation obligation of ONE
-- reduction rule, verbatim.  Each is REFUTED in proof/PreserveObstruct by
-- a typed redex whose contractum is untypeable, so they are carried as
-- module parameters rather than proven.  See that file for which design
-- premise each counterexample turns on.

PeelCase : Set
PeelCase = ∀ {Δ V W Θ s t C} → Value V → Value W
  → Δ ∣ [] ⊢ (V ⟪ Θ , s ↦ t ⟫) · W ⦂ C
  → Δ ∣ [] ⊢ (V · (wkᴹ (nbind Θ) W ⟪ dual Θ , s ⟫)) ⟪ Θ , t ⟫ ⦂ C

TyPeelRCase : Set
TyPeelRCase = ∀ {Δ V Θ s B A C} → Value V
  → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
  → Δ ∣ [] ⊢ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) B , ` 0 ])
               ⟪ bind A ∷ renᴮ suc Θ , s ⟫ ⦂ C

CancelRCase : Set
CancelRCase = ∀ {Δ V Θ₁ Θ₂ X Y A C} → Value V → fceC Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢ V ⟪ reps→bind (reps Θ₂) , idc A ⟫ ⦂ C

IdPushCase : Set
IdPushCase = ∀ {Δ V Θ₁ Θ₂ X Y A C} → Value V → fceC Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , unseal X ⟫) ⟪ Θ₂ , idc A ⟫ ⦂ C

-- THE TERM CONTEXT IS EMPTY, and it has to be.  Reduction carries no term
-- context (`_⊢_-→_` indexes on the TYPE context alone) and TyBeta's
-- contractum is a WRAPPER, whose body `env` types at Γ = [].  At a
-- non-empty Γ the rule already breaks: `Λ (ƛ `ℕ ∙ ` 1)` is a value at
-- Γ = `ℕ ∷ [], TyBeta fires, and the contractum's interior mentions a
-- term variable a wrapper body may not have.
module Impl
  (peel   : PeelCase)
  (typeel : TyPeelRCase)
  (cancel : CancelRCase)
  (idpush : IdPushCase)
  where

  preserve : ∀ {Δ M M′ A}
    → Δ ∣ [] ⊢ M ⦂ A
    → Δ ⊢ M -→ M′
      ----------------
    → Δ ∣ [] ⊢ M′ ⦂ A
  preserve ⊢M (TyBeta v)             = preserve-TyBeta ⊢M
  preserve ⊢M (Beta w)               = preserve-Beta ⊢M
  preserve ⊢M (Peel v w)             = peel v w ⊢M
  preserve ⊢M (TyPeelR v)            = typeel v ⊢M
  preserve ⊢M (CancelR v d)          = cancel v d ⊢M
  preserve ⊢M (Drop$ b)              = preserve-Drop$ b ⊢M
  preserve ⊢M (IdPush v d)           = idpush v d ⊢M
  preserve (⊢· ⊢L ⊢M)   (ξ-·-l st)   = ⊢· (preserve ⊢L st) ⊢M
  preserve (⊢· ⊢L ⊢M)   (ξ-·-r v st) = ⊢· ⊢L (preserve ⊢M st)
  preserve (⊢·[] ⊢L w)  (ξ-·[] st)   = ⊢·[] (preserve ⊢L st) w
  preserve (⊢Λ ⊢N)      (ξ-Λ st)     = ⊢Λ (preserve ⊢N st)
  preserve (env bw ⊢M ⊢c wE) (ξ-⟪⟫ st) =
    env bw (preserve ⊢M st) ⊢c wE

  preserve* : ∀ {Δ M M′ A}
    → Δ ∣ [] ⊢ M ⦂ A
    → Δ ⊢ M -→* M′
      ----------------
    → Δ ∣ [] ⊢ M′ ⦂ A
  preserve* ⊢M done          = ⊢M
  preserve* ⊢M (st then sts) = preserve* (preserve ⊢M st) sts
