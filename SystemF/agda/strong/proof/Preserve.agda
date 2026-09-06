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
-- §2b THE MINTED FACE TYPEELR WRITES (`⊢unsealAtᶜ`/`⊢sealAtᶜ`), the
--     conversion-level analogue of §2.  Since the polarity index was
--     retired (strong.Conversion) both directions are TOTAL.
--
-- §3  the per-rule cases that hold, one lemma each — TyBeta, TyPeelR at
--     ANY ∀-face, and Drop$.
--
-- §4  `preserve`, over a module parameterized by the cases whose proofs
--     live downstream (Peel, CancelR) and by IdPush, which is still
--     REFUTED (proof/PreserveObstruct §4).

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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
single-at-ext : (X : ℕ) (A : Ty) (Y : ℕ)
  → extsᵗ (single-at X A) Y ≡ single-at (suc X) (⇑ᵗ A) Y
single-at-ext X A zero    = refl
single-at-ext X A (suc Y) with X ≟ℕ Y
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

subst-at-∀ : (X : ℕ) (A B : Ty)
  → (`∀ B) [ X := A ]ᵗ ≡ `∀ (B [ suc X := ⇑ᵗ A ]ᵗ)
subst-at-∀ X A B = cong `∀ (subst-cong (single-at-ext X A) B)

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

-- THE MINTED FACE, both directions, mutually.
mutual
  ⊢unsealAt : Δ ∋ X := A → Δ ⊢ᵗ B
    → Δ ⊢ unsealAt X B ∶ B ⇝ B [ X := A ]ᵗ
  ⊢unsealAt {X = X} {A = A} {B = ` Y} d (wf-var tv) with X ≟ℕ Y
  ... | yes refl rewrite single-at-hit X A       = conv-unseal d
  ... | no  ne   rewrite single-at-miss X Y A ne = conv-idv tv
  ⊢unsealAt d wf-ℕ = conv-id base-ℕ
  ⊢unsealAt d wf-𝔹 = conv-id base-𝔹
  ⊢unsealAt d (wf-⇒ wA wB) = conv-fun (⊢sealAt d wA) (⊢unsealAt d wB)
  ⊢unsealAt {X = X} {A = A} {B = `∀ B} d (wf-∀ wB)
    rewrite subst-at-∀ X A B = conv-all (⊢unsealAt (es d) wB)

  ⊢sealAt : Δ ∋ X := A → Δ ⊢ᵗ B
    → Δ ⊢ sealAt X B ∶ B [ X := A ]ᵗ ⇝ B
  ⊢sealAt {X = X} {A = A} {B = ` Y} d (wf-var tv) with X ≟ℕ Y
  ... | yes refl rewrite single-at-hit X A       = conv-seal d
  ... | no  ne   rewrite single-at-miss X Y A ne = conv-idv tv
  ⊢sealAt d wf-ℕ = conv-id base-ℕ
  ⊢sealAt d wf-𝔹 = conv-id base-𝔹
  ⊢sealAt d (wf-⇒ wA wB) = conv-fun (⊢unsealAt d wA) (⊢sealAt d wB)
  ⊢sealAt {X = X} {A = A} {B = `∀ B} d (wf-∀ wB)
    rewrite subst-at-∀ X A B = conv-all (⊢sealAt (es d) wB)

------------------------------------------------------------------------
-- §2b  The face TYPEELR mints — `unsealAtᶜ` at the new owner
------------------------------------------------------------------------

-- Four substitution facts about `single-at`, all shift arithmetic.

subst-var-ren : (ρ : Renameᵗ) (T : Ty) → substᵗ (λ X → ` (ρ X)) T ≡ renameᵗ ρ T
subst-var-ren ρ (` X)   = refl
subst-var-ren ρ `ℕ      = refl
subst-var-ren ρ `𝔹      = refl
subst-var-ren ρ (A ⇒ B) =
  cong₂ _⇒_ (subst-var-ren ρ A) (subst-var-ren ρ B)
subst-var-ren ρ (`∀ A)  =
  cong `∀ (trans (subst-cong h A) (subst-var-ren (extᵗ ρ) A))
  where
  h : (Y : ℕ) → extsᵗ (λ X → ` (ρ X)) Y ≡ ` (extᵗ ρ Y)
  h zero    = refl
  h (suc Y) = refl

-- A SHIFTED type never names slot 0, so the mint at slot 0 fixes it.
subst-at-0-⇑ : (R T : Ty) → (⇑ᵗ T) [ 0 := R ]ᵗ ≡ ⇑ᵗ T
subst-at-0-⇑ R T =
  trans (rename-subst-commute suc (single-at 0 R) T)
        (trans (subst-cong (λ X → single-at-miss 0 (suc X) R (λ ())) T)
               (subst-var-ren suc T))

-- … and one binder deeper the mint moves with the shift.
subst-at-⇑ : (n : ℕ) (R T : Ty)
  → (⇑ᵗ T) [ suc n := ⇑ᵗ R ]ᵗ ≡ ⇑ᵗ (T [ n := R ]ᵗ)
subst-at-⇑ n R T =
  trans (subst-cong (λ Y → sym (single-at-ext n R Y)) (⇑ᵗ T))
        (trans (rename-subst-commute suc (extsᵗ (single-at n R)) T)
               (sym (rename-subst suc (single-at n R) T)))

base-subst-at : ∀ {A} (n : ℕ) (R : Ty) → Base A → A [ n := R ]ᵗ ≡ A
base-subst-at n R base-ℕ = refl
base-subst-at n R base-𝔹 = refl

-- Substituting the SHIFTED annotation back at slot 0 is the identity —
-- what TyPeelR's pushed-in `·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ]` computes.
ren-suc-[0] : (T : Ty) → (renameᵗ (extᵗ suc) T) [ ` 0 ]ᵗ ≡ T
ren-suc-[0] T =
  trans (rename-subst-commute (extᵗ suc) (singleTyEnv (` 0)) T)
        (trans (subst-cong h T) (subst-id T))
  where
  h : (X : ℕ) → singleTyEnv (` 0) (extᵗ suc X) ≡ ` X
  h zero    = refl
  h (suc X) = refl

-- THE TYPE CONTEXT THE ∀-FACE IS READ ON.  A face's `` `∀ `` pushes one
-- ABSTRACT slot; TyPeelR turns the outermost such slot into the OWNER it
-- binds, so the two type contexts differ at exactly one entry, `n` binders
-- in.
abstN : ℕ → Ctxᵗ → Ctxᵗ
abstN zero    Ξ = Ξ
abstN (suc n) Ξ = abst ∷ abstN n Ξ

abstN-owner : ∀ {Ψ A} (n : ℕ) → abstN n (bind A ∷ Ψ) ∋ n := liftN (suc n) A
abstN-owner zero    = ez
abstN-owner (suc n) = es (abstN-owner n)

abstN-⊑ : ∀ {Ψ A} (n : ℕ) → abstN n (abst ∷ Ψ) ⊑ abstN n (bind A ∷ Ψ)
abstN-⊑ {Ψ = Ψ} zero = le∷ le-ao (⊑-refl Ψ)
abstN-⊑ (suc n)      = le∷ le-aa (abstN-⊑ n)

-- The mint, applied to a whole ENTRY (the form the lookup transport
-- needs, since `∋e` returns entries and only `bind` carries a rep).
substᵉ : ℕ → Ty → Ent → Ent
substᵉ n R abst     = abst
substᵉ n R (bind A) = bind (A [ n := R ]ᵗ)
substᵉ n R (blk E)  = blk (substᵉ n R E)

substᵉ-0-⇑ : (R : Ty) (E : Ent) → substᵉ 0 R (⇑ᵉ E) ≡ ⇑ᵉ E
substᵉ-0-⇑ R abst     = refl
substᵉ-0-⇑ R (bind A) = cong bind (subst-at-0-⇑ R A)
substᵉ-0-⇑ R (blk E)  = cong blk (substᵉ-0-⇑ R E)

substᵉ-⇑ : (n : ℕ) (R : Ty) (E : Ent)
  → substᵉ (suc n) (⇑ᵗ R) (⇑ᵉ E) ≡ ⇑ᵉ (substᵉ n R E)
substᵉ-⇑ n R abst     = refl
substᵉ-⇑ n R (bind A) = cong bind (subst-at-⇑ n R A)
substᵉ-⇑ n R (blk E)  = cong blk (substᵉ-⇑ n R E)

-- WHAT THE OTHER SLOTS OWE.  Every entry of `abstN n (abst ∷ Ψ)` is
-- either ABSTRACT (the prefix, and slot n itself) or an entry of Ψ read
-- past `n+1` binders — and such an entry names no slot ≤ n, so the mint
-- at slot n leaves it alone.  This is SIMULTANEITY again: a rep is a type
-- over the plain exterior, lifted past the owners bound inside it.
abstN-ent : ∀ {Ψ A} (n : ℕ) {Y E}
  → abstN n (abst ∷ Ψ) ∋e Y , E
    ------------------------------------------------------------
  → (E ≡ abst)
  ⊎ ((abstN n (bind A ∷ Ψ) ∋e Y , E)
     × (substᵉ n (liftN (suc n) A) E ≡ E))
abstN-ent zero ez                = inj₁ refl
abstN-ent {A = A} zero (es {E = E} d) =
  inj₂ (es d , substᵉ-0-⇑ (⇑ᵗ A) E)
abstN-ent (suc n) ez             = inj₁ refl
abstN-ent {A = A} (suc n) (es {E = E} d) with abstN-ent {A = A} n d
... | inj₁ refl        = inj₁ refl
... | inj₂ (d′ , eq) =
  inj₂ (es d′ , trans (substᵉ-⇑ n (liftN (suc n) A) E) (cong ⇑ᵉ eq))

abstN-kn : ∀ {Ψ A} (n : ℕ) {Y B}
  → abstN n (abst ∷ Ψ) ∋ Y := B
    -------------------------------------------------------
  → (abstN n (bind A ∷ Ψ) ∋ Y := B)
    × (B [ n := liftN (suc n) A ]ᵗ ≡ B)
abstN-kn {A = A} n d with abstN-ent {A = A} n d
... | inj₁ ()
... | inj₂ (d′ , eq) = d′ , bind-inj eq

-- SLOT n IS ABSTRACT, so no face leaf the premise already carries can
-- name it.  This is what closes the two leaf cases the polarity index
-- used to rule out (a `seal` under `unsealAtᶜ`, an `unseal` under
-- `sealAtᶜ`): such a leaf cites an OWNER, and slot n has none.
abstN-abst : ∀ {Ψ E} (n : ℕ) → abstN n (abst ∷ Ψ) ∋e n , E → E ≡ abst
abstN-abst zero    ez     = refl
abstN-abst (suc n) (es d) = cong ⇑ᵉ (abstN-abst n d)

abstN-≢ : ∀ {Ψ B Y} (n : ℕ) → abstN n (abst ∷ Ψ) ∋ Y := B → ¬ (n ≡ Y)
abstN-≢ n d refl with abstN-abst n d
... | ()

-- THE MINTED FACE, both directions, mutually — the conversion analogue of
-- `⊢unsealAt`/`⊢sealAt` (§2), and equal to them on an identity face
-- (`unsealAtᶜ-idc`, strong.Reduction).
--
-- WITHOUT THE POLARITY INDEX BOTH DIRECTIONS ARE TOTAL.  The mint inserts
-- `unseal n` where the face runs covariantly and `seal n` where it runs
-- contravariantly; the leaves the face ALREADY carries are copied
-- unchanged, and each of them names an owner ≠ n (`abstN-≢`), so the
-- substitution at slot n leaves its face alone.  That is the whole of the
-- old CONCEAL-face obstruction: it was the index, not the terms.
mutual
  ⊢unsealAtᶜ : ∀ {Ψ A s Bᵢ Bₑ} (n : ℕ)
    → abstN n (abst ∷ Ψ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      ------------------------------------------------------------
    → abstN n (bind A ∷ Ψ) ⊢ unsealAtᶜ n s
        ∶ Bᵢ ⇝ Bₑ [ n := liftN (suc n) A ]ᵗ
  ⊢unsealAtᶜ n (conv-id base-ℕ) = conv-id base-ℕ
  ⊢unsealAtᶜ n (conv-id base-𝔹) = conv-id base-𝔹
  ⊢unsealAtᶜ {A = A} n (conv-idv {X = Y} tv) with n ≟ℕ Y
  ... | yes refl rewrite single-at-hit n (liftN (suc n) A) =
    conv-unseal (abstN-owner n)
  ... | no ne rewrite single-at-miss n Y (liftN (suc n) A) ne =
    conv-idv (⊑-tv (abstN-⊑ n) tv)
  ⊢unsealAtᶜ {A = A} n (conv-unseal d) with abstN-kn {A = A} n d
  ... | d′ , eq rewrite eq = conv-unseal d′
  ⊢unsealAtᶜ {A = A} n (conv-seal {X = Y} d)
    rewrite single-at-miss n Y (liftN (suc n) A) (abstN-≢ n d) =
    conv-seal (proj₁ (abstN-kn {A = A} n d))
  ⊢unsealAtᶜ n (conv-fun ⊢s ⊢t) =
    conv-fun (⊢sealAtᶜ n ⊢s) (⊢unsealAtᶜ n ⊢t)
  ⊢unsealAtᶜ {A = A} {Bₑ = `∀ Bₑ} n (conv-all ⊢s)
    rewrite subst-at-∀ n (liftN (suc n) A) Bₑ = conv-all (⊢unsealAtᶜ (suc n) ⊢s)

  ⊢sealAtᶜ : ∀ {Ψ A s Bᵢ Bₑ} (n : ℕ)
    → abstN n (abst ∷ Ψ) ⊢ s ∶ Bᵢ ⇝ Bₑ
      ------------------------------------------------------------
    → abstN n (bind A ∷ Ψ) ⊢ sealAtᶜ n s
        ∶ Bᵢ [ n := liftN (suc n) A ]ᵗ ⇝ Bₑ
  ⊢sealAtᶜ n (conv-id base-ℕ) = conv-id base-ℕ
  ⊢sealAtᶜ n (conv-id base-𝔹) = conv-id base-𝔹
  ⊢sealAtᶜ {A = A} n (conv-idv {X = Y} tv) with n ≟ℕ Y
  ... | yes refl rewrite single-at-hit n (liftN (suc n) A) =
    conv-seal (abstN-owner n)
  ... | no ne rewrite single-at-miss n Y (liftN (suc n) A) ne =
    conv-idv (⊑-tv (abstN-⊑ n) tv)
  ⊢sealAtᶜ {A = A} n (conv-seal d) with abstN-kn {A = A} n d
  ... | d′ , eq rewrite eq = conv-seal d′
  ⊢sealAtᶜ {A = A} n (conv-unseal {X = Y} d)
    rewrite single-at-miss n Y (liftN (suc n) A) (abstN-≢ n d) =
    conv-unseal (proj₁ (abstN-kn {A = A} n d))
  ⊢sealAtᶜ n (conv-fun ⊢s ⊢t) =
    conv-fun (⊢unsealAtᶜ n ⊢s) (⊢sealAtᶜ n ⊢t)
  ⊢sealAtᶜ {A = A} {Bᵢ = `∀ Bᵢ} n (conv-all ⊢s)
    rewrite subst-at-∀ n (liftN (suc n) A) Bᵢ = conv-all (⊢sealAtᶜ (suc n) ⊢s)

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
  env (bw-b wA bw[])
      (⊢retag refine ⊢N)
      face
      (wf-[]ᵗ wB wA)
  where
  refine : (abst ∷ Δ) ⊑ (bind A ∷ Δ)
  refine = le∷ le-ao (⊑-refl Δ)

  face : (bind A ∷ Δ) ⊢ unsealAt 0 B ∶ B ⇝ liftN 1 (B [ A ]ᵗ)
  face rewrite sym (subst-at-0 A B) = ⊢unsealAt ez (⊑-wf refine wB)

-- ── TYPEELR, AT ANY ∀-FACE ─────────────────────────────────────────────
-- Four moves, one per premise of the contractum's `env`:
--
--   FRAME     `bind A ∷ Θ`, whose interior is `bind (liftN (nbind Θ) A) ∷
--             intC Θ Δ` DEFINITIONALLY — the shift `renᴮ suc Θ` used to
--             add is the one `prep` already performs.
--   INTERIOR  `wkᴹ 1 V` (⊢rename at `Ren-wk`) instantiated at the new
--             owner's own name; the annotation is the INTERIOR ∀-body,
--             shifted, and `ren-suc-[0]` returns it unchanged.
--   FACE      `unsealAtᶜ 0 s` (§2b), whose exterior face is the interior
--             one with slot 0 replaced by the owner's rep — which is the
--             instantiated exterior body, by `subst-at-0`.
--   EXTERIOR  `wf-[]ᵗ`, i.e. `⊢·[]`'s own two premises.
--
-- The premise `⊢s` and the redex's own face derivation agree, by
-- `conv-faces-unique`: that is what makes the pushed-in annotation a
-- function of the redex (and hence `det` true).
--
-- THE CASE IS NOW GENERAL.  Under the polarity index this was a theorem
-- only at a REVEAL ∀-face, because the mint inserts `seal 0`
-- contravariantly and `unseal 0` covariantly and one of the two always
-- sat where the index refused it.  With the index retired the mint's
-- typing (`⊢unsealAtᶜ`, §2b) is total, and so is this case.
TyPeelRCase : Set
TyPeelRCase = ∀ {Δ V Θ s B A C Bᵢ Bₑ} → Value V
  → (abst ∷ fceC Θ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
  → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
  → Δ ∣ [] ⊢ (wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ])
               ⟪ bind A ∷ Θ , unsealAtᶜ 0 s ⟫ ⦂ C

∀-inj : ∀ {A B} → _≡_ {A = Ty} (`∀ A) (`∀ B) → A ≡ B
∀-inj refl = refl

wf-∀⁻ : Δ ⊢ᵗ `∀ A → (abst ∷ Δ) ⊢ᵗ A
wf-∀⁻ (wf-∀ w) = w

-- The exterior body, lifted: `liftᵇ` and the instantiation commute.
liftN-[]ᵗ : (n : ℕ) (B A : Ty)
  → liftN n (B [ A ]ᵗ) ≡ (liftᵇ n B) [ liftN n A ]ᵗ
liftN-[]ᵗ zero    B A = refl
liftN-[]ᵗ (suc n) B A =
  trans (cong ⇑ᵗ (liftN-[]ᵗ n B A))
        (rename-[]ᵗ-commute suc (liftᵇ n B) (liftN n A))

preserve-TyPeelR : TyPeelRCase
preserve-TyPeelR {Δ = Δ} {V = V} {Θ = Θ} {s = s} {B = B} {A = A}
                 {Bᵢ = Bᵢ} {Bₑ = Bₑ} v ⊢s (⊢·[] (env bw ⊢V ⊢c wE) wA)
  with conv-all-inv ⊢c
... | A₀ , B₀ , refl , eqE , ⊢s₀
  with conv-faces-unique ⊢s ⊢s₀
... | refl , refl =
  env (bw-b wA bw) interior face (wf-[]ᵗ (wf-∀⁻ wE) wA)
  where
  A′ : Ty
  A′ = liftN (nbind Θ) A

  -- the exterior ∀-body, read on the boundary's face type context
  eqB : Bₑ ≡ liftᵇ (nbind Θ) B
  eqB = sym (∀-inj (trans (sym (liftN-liftᵇ (nbind Θ) B)) eqE))

  ⊢wkV : (bind A′ ∷ intC Θ Δ) ∣ [] ⊢ wkᴹ 1 V ⦂ `∀ (renameᵗ (extᵗ suc) Bᵢ)
  ⊢wkV = ⊢rename Ren-wk Inj-suc ⊢V

  interior : intC (bind A ∷ Θ) Δ ∣ []
               ⊢ wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ] ⦂ Bᵢ
  interior =
    subst (λ T → intC (bind A ∷ Θ) Δ ∣ []
                   ⊢ wkᴹ 1 V ·[ renameᵗ (extᵗ suc) Bᵢ , ` 0 ] ⦂ T)
          (ren-suc-[0] Bᵢ)
          (⊢·[] ⊢wkV (wf-var (bind (⇑ᵗ A′) , ez , vis-b)))

  eqT : Bₑ [ 0 := ⇑ᵗ A′ ]ᵗ ≡ liftN (suc (nbind Θ)) (B [ A ]ᵗ)
  eqT = trans (cong (λ T → T [ 0 := ⇑ᵗ A′ ]ᵗ) eqB)
              (trans (subst-at-0 A′ (liftᵇ (nbind Θ) B))
                     (cong ⇑ᵗ (sym (liftN-[]ᵗ (nbind Θ) B A))))

  face : fceC (bind A ∷ Θ) Δ ⊢ unsealAtᶜ 0 s
           ∶ Bᵢ ⇝ liftN (suc (nbind Θ)) (B [ A ]ᵗ)
  face = subst (λ T → fceC (bind A ∷ Θ) Δ ⊢ unsealAtᶜ 0 s ∶ Bᵢ ⇝ T)
               eqT (⊢unsealAtᶜ {A = A′} 0 ⊢s)

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
-- §4  The cases carried as parameters, and `preserve` over them
------------------------------------------------------------------------

-- Each statement below is the preservation obligation of ONE reduction
-- rule, verbatim.  `PeelCase` is PROVEN (proof/PeelDual) and `CancelRCase`
-- is DISCHARGED over one scoping interface (proof/CancelFaces); both are
-- stated here because their proofs live downstream of this module.
-- `IdPushCase` is REFUTED as it stands (proof/PreserveObstruct §4).

PeelCase : Set
PeelCase = ∀ {Δ V W Θ s t C} → Value V → Value W
  → Δ ∣ [] ⊢ (V ⟪ Θ , s ↦ t ⟫) · W ⦂ C
  → Δ ∣ [] ⊢ (V · (wkᴹ (nbind Θ) W ⟪ dual Θ , s ⟫)) ⟪ Θ , t ⟫ ⦂ C

-- (`TyPeelRCase` is stated and PROVEN in §3.)

-- CANCELR, at the repaired rule (both frames kept, both faces
-- neutralised).  Discharged over ONE interface in proof/CancelFaces.
CancelRCase : Set
CancelRCase = ∀ {Δ V Θ₁ Θ₂ X Y A C} → Value V → fceC Θ₂ Δ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , idc (liftN (nbind Θ₁) A) ⟫) ⟪ Θ₂ , idc A ⟫ ⦂ C

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
  preserve ⊢M (TyPeelR v ⊢s)         = preserve-TyPeelR v ⊢s ⊢M
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
