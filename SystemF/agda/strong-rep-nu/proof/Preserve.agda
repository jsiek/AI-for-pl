module strong-rep-nu.proof.Preserve where

-- File Charter:
--   * PRESERVATION on the GLOBAL REPRESENTATION STORE.  §1 type
--     well-formedness from typing and the ordinary type-substitution
--     facts; §1b `RepRefines`, the in-place `abstR → bindR R`
--     refinement; §2 the allocation and the minted conversions;
--     §3 the local reduction cases; §4/§4b the transports and crossing
--     cases proved downstream, with the `AllocWf`/`boundary-apply`
--     machinery; §5 `step-alloc`, `preserve-wf`, and `Impl`.
--   * A STEP RETURNS THE CHANGE IT MADE, so the contractum is typed at
--     `apply δ Δ` and the congruences SHIFT THE REDEX'S SIBLINGS
--     (`ShiftTyping`, the one lemma the store experiment added).
--   * EVERY PARAMETER of `Impl` has an implementation, so
--     strong-rep-nu.Preservation exposes no parameter at all.
-- Commentary: Commentary.md § proof/Preserve.agda

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
open import strong-rep-nu.proof.TypeSubst
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.TermSubst
open import strong-rep-nu.proof.TermSubst
open import strong-rep-nu.Reduction

private
  variable
    Δ Δ′ : Ctxᵗ
    Ω : Ctxᵗ
    Γ : Ctx
    η η′ : TyCtx
    Ξ Ξ′ : RepCtx
    b b′ : RepBinding
    δ : Change
    χ : List Change
    Rs : List Ty
    A B C R S : Ty
    s t : Conv
    X Y α β n : ℕ
    ρ : Renameᵗ

------------------------------------------------------------------------
-- §1. Well-formedness of the type a derivation concludes
------------------------------------------------------------------------

shiftReps-∋ : η ∋ˡ X := α → shiftReps η ∋ˡ X := suc α
shiftReps-∋ here = here
shiftReps-∋ (there d) = there (shiftReps-∋ d)

shiftReps-∋⁻ : shiftReps η ∋ˡ X := α
  → ∃[ β ] ((α ≡ suc β) × (η ∋ˡ X := β))
shiftReps-∋⁻ {η = []} ()
shiftReps-∋⁻ {η = β ∷ η} here = β , refl , here
shiftReps-∋⁻ {η = β ∷ η} (there d) with shiftReps-∋⁻ d
shiftReps-∋⁻ {η = β ∷ η} (there d) | α′ , refl , d′ =
  α′ , refl , there d′

tv-underΛ-zero : underΛ Δ ∋tv zero
tv-underΛ-zero = zero , here

tv-underΛ-suc : Δ ∋tv X → underΛ Δ ∋tv suc X
tv-underΛ-suc (α , d) = suc α , there (shiftReps-∋ d)

tv-underΛ-tail : underΛ Δ ∋tv suc X → Δ ∋tv X
tv-underΛ-tail (α , there d) with shiftReps-∋⁻ d
tv-underΛ-tail (α , there d) | β , refl , d′ = β , d′

-- A well-formedness renaming only needs to preserve the existence of an
-- ordinary name. The representation variable denoted by that name is not
-- part of the ordinary type-formation judgment.
WfRen : Ctxᵗ → Ctxᵗ → Renameᵗ → Set
WfRen Δ Δ′ ρ = ∀ {X} → Δ ∋tv X → Δ′ ∋tv ρ X

WfRen-ext : WfRen Δ Δ′ ρ → WfRen (underΛ Δ) (underΛ Δ′) (extᵗ ρ)
WfRen-ext {Δ = Δ} {Δ′ = Δ′} h {zero} tv =
  tv-underΛ-zero {Δ = Δ′}
WfRen-ext {Δ = Δ} {Δ′ = Δ′} h {suc X} tv =
  tv-underΛ-suc {Δ = Δ′} (h (tv-underΛ-tail {Δ = Δ} tv))

WfRen-wk : WfRen Δ (underΛ Δ) suc
WfRen-wk {Δ = Δ} = tv-underΛ-suc {Δ = Δ}

wf-ren : WfRen Δ Δ′ ρ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ renameᵗ ρ A
wf-ren h (wf-var tv) = wf-var (h tv)
wf-ren h wf-ℕ = wf-ℕ
wf-ren h wf-𝔹 = wf-𝔹
wf-ren h (wf-⇒ wA wB) = wf-⇒ (wf-ren h wA) (wf-ren h wB)
wf-ren {Δ = Δ} {Δ′ = Δ′} h (wf-∀ wA) =
  wf-∀ (wf-ren (WfRen-ext {Δ = Δ} {Δ′ = Δ′} h) wA)

-- A type substitution is well formed when it sends every live ordinary
-- variable to a well-formed type.
SubWf : Ctxᵗ → Ctxᵗ → Substᵗ → Set
SubWf Δ Δ′ σ = ∀ {X} → Δ ∋tv X → Δ′ ⊢ᵗ σ X

SubWf-ext : ∀ {σ} → SubWf Δ Δ′ σ
  → SubWf (underΛ Δ) (underΛ Δ′) (extsᵗ σ)
SubWf-ext {Δ = Δ} {Δ′ = Δ′} h {zero} tv =
  wf-var (tv-underΛ-zero {Δ = Δ′})
SubWf-ext {Δ = Δ} {Δ′ = Δ′} h {suc X} tv =
  wf-ren (WfRen-wk {Δ = Δ′}) (h (tv-underΛ-tail {Δ = Δ} tv))

wf-substᵗ : ∀ {σ}
  → SubWf Δ Δ′ σ
  → Δ ⊢ᵗ A
  → Δ′ ⊢ᵗ substᵗ σ A
wf-substᵗ h (wf-var tv) = h tv
wf-substᵗ h wf-ℕ = wf-ℕ
wf-substᵗ h wf-𝔹 = wf-𝔹
wf-substᵗ h (wf-⇒ wA wB) = wf-⇒ (wf-substᵗ h wA) (wf-substᵗ h wB)
wf-substᵗ {Δ = Δ} {Δ′ = Δ′} h (wf-∀ wA) =
  wf-∀ (wf-substᵗ (SubWf-ext {Δ = Δ} {Δ′ = Δ′} h) wA)

wf-[]ᵗ : underΛ Δ ⊢ᵗ B → Δ ⊢ᵗ A → Δ ⊢ᵗ B [ A ]ᵗ
wf-[]ᵗ {Δ = Δ} {A = A} wB wA = wf-substᵗ h wB
  where
  h : SubWf (underΛ Δ) Δ (singleTyEnv A)
  h {zero} tv = wA
  h {suc X} tv = wf-var (tv-underΛ-tail {Δ = Δ} tv)

CtxWf : Ctxᵗ → Ctx → Set
CtxWf Δ Γ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ⊢ᵗ A

CtxWf-[] : CtxWf Δ []
CtxWf-[] ()

CtxWf-∷ : Δ ⊢ᵗ A → CtxWf Δ Γ → CtxWf Δ (A ∷ Γ)
CtxWf-∷ w h here = w
CtxWf-∷ w h (there d) = h d

CtxWf-⤊ : CtxWf Δ Γ → CtxWf (underΛ Δ) (⤊ Γ)
CtxWf-⤊ h d with ∋-map⁻ d
CtxWf-⤊ {Δ = Δ} h d | A , refl , q =
  wf-ren (WfRen-wk {Δ = Δ}) (h q)

⊢ᵗ-of : ∀ {M} → CtxWf Δ Γ → Δ ∣ Γ ⊢ M ⦂ A → Δ ⊢ᵗ A
⊢ᵗ-of h (⊢` d) = h d
⊢ᵗ-of h ⊢$ = wf-ℕ
⊢ᵗ-of h ⊢true = wf-𝔹
⊢ᵗ-of h ⊢false = wf-𝔹
⊢ᵗ-of h (⊢ƛ w ⊢N) = wf-⇒ w (⊢ᵗ-of (CtxWf-∷ w h) ⊢N)
⊢ᵗ-of h (⊢· ⊢L ⊢M) with ⊢ᵗ-of h ⊢L
⊢ᵗ-of h (⊢· ⊢L ⊢M) | wf-⇒ wA wB = wB
⊢ᵗ-of h (⊢Λ _ ⊢N) = wf-∀ (⊢ᵗ-of (CtxWf-⤊ h) ⊢N)
⊢ᵗ-of h (⊢ν wA rA ⊢L mw ⊢c same wB) = wB
⊢ᵗ-of h (boundary _ _ _ _ _ wE) = wE

wf-same : Δ ⊢ᵗ A → ∃[ R ] names Δ ⊢ A ~ R
wf-same (wf-var (α , name)) = ` α , same-var name
wf-same wf-ℕ = `ℕ , same-ℕ
wf-same wf-𝔹 = `𝔹 , same-𝔹
wf-same (wf-⇒ wA wB) with wf-same wA | wf-same wB
wf-same (wf-⇒ wA wB) | R , p | S , q = R ⇒ S , same-⇒ p q
wf-same (wf-∀ wA) with wf-same wA
wf-same (wf-∀ wA) | R , p = `∀ R , same-∀ p

-- and back: a type that HAS a representation reading is well formed,
-- because every leaf of a reading is a live ordinary name.
same-wf : names Δ ⊢ A ~ R → Δ ⊢ᵗ A
same-wf (same-var d) = wf-var (_ , d)
same-wf same-ℕ = wf-ℕ
same-wf same-𝔹 = wf-𝔹
same-wf (same-⇒ p q) = wf-⇒ (same-wf p) (same-wf q)
same-wf {Δ = Δ} (same-∀ p) = wf-∀ (same-wf {Δ = underΛ Δ} p)

------------------------------------------------------------------------
-- §1b. Refining an abstract representation variable
------------------------------------------------------------------------

-- This is the two-universe transcription of the old retagging relation.
-- Concrete bindings and payloads are preserved; an abstract representation
-- variable may become represented.
data RepRefines : RepCtx → RepCtx → Set where
  rr[]   : RepRefines [] []
  rr-abst : RepRefines Ξ Ξ′ → RepRefines (abstR ∷ Ξ) (abstR ∷ Ξ′)
  rr-bind : RepRefines Ξ Ξ′
    → RepRefines (bindR R ∷ Ξ) (bindR R ∷ Ξ′)
  rr-represent : RepRefines Ξ Ξ′
    → RepRefines (abstR ∷ Ξ) (bindR R ∷ Ξ′)

lookup-refine : RepRefines Ξ Ξ′
  → Ξ ∋ˡ α := b
  → ∃[ b′ ] Ξ′ ∋ˡ α := b′
lookup-refine (rr-abst rr) here = abstR , here
lookup-refine (rr-abst rr) (there d) with lookup-refine rr d
lookup-refine (rr-abst rr) (there d) | T , d′ = T , there d′
lookup-refine (rr-bind rr) here = _ , here
lookup-refine (rr-bind rr) (there d) with lookup-refine rr d
lookup-refine (rr-bind rr) (there d) | T , d′ = T , there d′
lookup-refine (rr-represent rr) here = _ , here
lookup-refine (rr-represent rr) (there d) with lookup-refine rr d
lookup-refine (rr-represent rr) (there d) | T , d′ = T , there d′

ref-refine : RepRefines Ξ Ξ′ → Ξ ⊢ref[ X ] Y → Ξ′ ⊢ref[ X ] Y
ref-refine rr (local-ref lt) = local-ref lt
ref-refine rr (free-ref d) with lookup-refine rr d
ref-refine rr (free-ref d) | T , d′ = free-ref d′

wfᴿ-refine : RepRefines Ξ Ξ′ → Ξ ⊢ᴿ[ X ] R → Ξ′ ⊢ᴿ[ X ] R
wfᴿ-refine rr (wfᴿ-var r) = wfᴿ-var (ref-refine rr r)
wfᴿ-refine rr wfᴿ-ℕ = wfᴿ-ℕ
wfᴿ-refine rr wfᴿ-𝔹 = wfᴿ-𝔹
wfᴿ-refine rr (wfᴿ-⇒ p q) =
  wfᴿ-⇒ (wfᴿ-refine rr p) (wfᴿ-refine rr q)
wfᴿ-refine rr (wfᴿ-∀ p) = wfᴿ-∀ (wfᴿ-refine rr p)

valid-refine : RepRefines Ξ Ξ′ → Ξ ∋ʳ α → Ξ′ ∋ʳ α
valid-refine rr (S , d) = lookup-refine rr d

step-refine : RepRefines Ξ Ξ′ → Ξ ∣ η ⊢δ δ ⇒ η′
  → Ξ′ ∣ η ⊢δ δ ⇒ η′
step-refine rr (step-unbind valid d fresh) =
  step-unbind (valid-refine rr valid) d fresh
step-refine rr (step-bind valid fresh i) =
  step-bind (valid-refine rr valid) fresh i

changes-refine : RepRefines Ξ Ξ′ → Ξ ∣ η ⊢χ χ ⇒ η′
  → Ξ′ ∣ η ⊢χ χ ⇒ η′
changes-refine rr changes[] = changes[]
changes-refine rr (changes∷ cs st) =
  changes∷ (changes-refine rr cs) (step-refine rr st)

conv-changes-refine : RepRefines Ξ Ξ′ → Ξ ∣ η ⊢χᶜ χ ⇒ η′
  → Ξ′ ∣ η ⊢χᶜ χ ⇒ η′
conv-changes-refine rr conv[] = conv[]
conv-changes-refine rr (conv-unbind valid cs) =
  conv-unbind (valid-refine rr valid) (conv-changes-refine rr cs)
conv-changes-refine rr (conv-bind valid cs fresh i) =
  conv-bind (valid-refine rr valid) (conv-changes-refine rr cs) fresh i
conv-changes-refine rr (conv-bind-live valid cs d) =
  conv-bind-live (valid-refine rr valid) (conv-changes-refine rr cs) d

rep-lookup-refine : RepRefines Ξ Ξ′ → Ξ ∋ʳ α := b
  → b ≡ bindR R → Ξ′ ∋ʳ α := bindR R
rep-lookup-refine (rr-abst rr) r-here ()
rep-lookup-refine (rr-abst rr) (r-there-abst {b = abstR} d) ()
rep-lookup-refine (rr-abst rr) (r-there-abst {b = bindR S} d) refl =
  r-there-abst (rep-lookup-refine rr d refl)
rep-lookup-refine (rr-bind rr) r-here refl = r-here
rep-lookup-refine (rr-bind rr) (r-there {b = abstR} d) ()
rep-lookup-refine (rr-bind rr) (r-there {b = bindR S} d) refl =
  r-there (rep-lookup-refine rr d refl)
rep-lookup-refine (rr-represent rr) r-here ()
rep-lookup-refine (rr-represent rr) (r-there-abst {b = abstR} d) ()
rep-lookup-refine (rr-represent rr)
                  (r-there-abst {b = bindR S} d) refl =
  r-there (rep-lookup-refine rr d refl)

lookup-square-refine : RepRefines Ξ Ξ′
  → (Ξ ∣ η) ∋ X := A → (Ξ′ ∣ η) ∋ X := A
lookup-square-refine rr (α , R , name , rep , same) =
  α , R , name , rep-lookup-refine rr rep refl , same

tv-refine : (Ξ ∣ η) ∋tv X → (Ξ′ ∣ η) ∋tv X
tv-refine (α , name) = α , name

wf-refine : RepRefines Ξ Ξ′
  → (Ξ ∣ η) ⊢ᵗ A
  → (Ξ′ ∣ η) ⊢ᵗ A
wf-refine {Ξ = Ξ} {Ξ′ = Ξ′} rr (wf-var tv) =
  wf-var (tv-refine {Ξ = Ξ} {Ξ′ = Ξ′} tv)
wf-refine rr wf-ℕ = wf-ℕ
wf-refine rr wf-𝔹 = wf-𝔹
wf-refine rr (wf-⇒ wA wB) = wf-⇒ (wf-refine rr wA) (wf-refine rr wB)
wf-refine rr (wf-∀ wA) = wf-∀ (wf-refine (rr-abst rr) wA)

mutual
  convᵐ-refine : ∀ {g} → RepRefines Ξ Ξ′ → (Ξ ∣ η) ⊢ᵐ g ∶ A ⇝ B
    → (Ξ′ ∣ η) ⊢ᵐ g ∶ A ⇝ B
  convᵐ-refine rr (conv-id b) = conv-id b
  convᵐ-refine {Ξ = Ξ} {Ξ′ = Ξ′} rr (conv-idv tv) =
    conv-idv (tv-refine {Ξ = Ξ} {Ξ′ = Ξ′} tv)
  convᵐ-refine rr (conv-fun p q) =
    conv-fun (conv-refine rr p) (conv-refine rr q)
  convᵐ-refine rr (conv-all p) = conv-all (conv-refine (rr-abst rr) p)

  convᵀ-refine : ∀ {t} → RepRefines Ξ Ξ′ → (Ξ ∣ η) ⊢ᵀ t ∶ A ⇝ B
    → (Ξ′ ∣ η) ⊢ᵀ t ∶ A ⇝ B
  convᵀ-refine rr (conv-mid p) = conv-mid (convᵐ-refine rr p)
  convᵀ-refine rr (conv-seal d) = conv-seal (lookup-square-refine rr d)
  convᵀ-refine rr (conv-seal-seq p d n) =
    conv-seal-seq (convᵀ-refine rr p) (lookup-square-refine rr d) n

  conv-refine : RepRefines Ξ Ξ′ → (Ξ ∣ η) ⊢ s ∶ A ⇝ B
    → (Ξ′ ∣ η) ⊢ s ∶ A ⇝ B
  conv-refine rr (conv-tail p) = conv-tail (convᵀ-refine rr p)
  conv-refine rr (conv-unseal d) =
    conv-unseal (lookup-square-refine rr d)
  conv-refine rr (conv-unseal-seq d p n m) =
    conv-unseal-seq (lookup-square-refine rr d) (conv-refine rr p) n m

------------------------------------------------------------------------
-- §2. The allocation, and the conversion a reveal mints
------------------------------------------------------------------------

single-at-hit : (X : ℕ) (A : Ty) → single-at X A X ≡ A
single-at-hit X A with X ≟ X
single-at-hit X A | yes _ = refl
single-at-hit X A | no ne = ⊥-elim (ne refl)

single-at-miss : (X Y : ℕ) (A : Ty) → ¬ (X ≡ Y)
  → single-at X A Y ≡ ` Y
single-at-miss X Y A ne with X ≟ Y
single-at-miss X Y A ne | yes eq = ⊥-elim (ne eq)
single-at-miss X Y A ne | no _ = refl

_≟ℕ_ : (X Y : ℕ) → Dec (X ≡ Y)
zero ≟ℕ zero = yes refl
zero ≟ℕ suc Y = no (λ ())
suc X ≟ℕ zero = no (λ ())
suc X ≟ℕ suc Y with X ≟ℕ Y
suc X ≟ℕ suc Y | yes refl = yes refl
suc X ≟ℕ suc Y | no ne = no (λ eq → ne (suc-injective eq))

single-at-ext : (X : ℕ) (A : Ty) (Y : ℕ)
  → extsᵗ (single-at X A) Y ≡ single-at (suc X) (⇑ᵗ A) Y
single-at-ext X A zero = refl
single-at-ext X A (suc Y) with X ≟ℕ Y
single-at-ext X A (suc Y) | yes refl =
  trans (cong ⇑ᵗ (single-at-hit X A))
        (sym (single-at-hit (suc X) (⇑ᵗ A)))
single-at-ext X A (suc Y) | no ne =
  trans (cong ⇑ᵗ (single-at-miss X Y A ne))
        (sym (single-at-miss (suc X) (suc Y) (⇑ᵗ A)
                             (λ eq → ne (suc-inj eq))))
  where
  suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

subst-at-∀ : (X : ℕ) (A B : Ty)
  → (`∀ B) [ X := A ]ᵗ ≡ `∀ (B [ suc X := ⇑ᵗ A ]ᵗ)
subst-at-∀ X A B = cong `∀ (subst-cong (single-at-ext X A) B)

subst-at-0 : (A B : Ty) → B [ 0 := ⇑ᵗ A ]ᵗ ≡ ⇑ᵗ (B [ A ]ᵗ)
subst-at-0 A B =
  trans (subst-cong boundary-eq B)
        (sym (rename-subst suc (singleTyEnv A) B))
  where
  boundary-eq : (Y : ℕ)
    → single-at 0 (⇑ᵗ A) Y ≡ renameᵗ suc (singleTyEnv A Y)
  boundary-eq zero = refl
  boundary-eq (suc Y) = refl

underNames : ℕ → TyCtx → TyCtx
underNames zero η = η
underNames (suc n) η = zero ∷ shiftReps (underNames n η)

underNames-weaken : ∀ {η X α} (n : ℕ)
  → underNames n η ∋ˡ X := α
  → underNames n (zero ∷ shiftReps η)
      ∋ˡ extN n suc X := extN n suc α
underNames-weaken zero d = there (shiftReps-∋ d)
underNames-weaken (suc n) here = here
underNames-weaken (suc n) (there d) with shiftReps-∋⁻ d
underNames-weaken (suc n) (there d) | β , refl , d′ =
  there (shiftReps-∋ (underNames-weaken n d′))

same-weaken-at : ∀ {η A R} (n : ℕ) → underNames n η ⊢ A ~ R
  → underNames n (zero ∷ shiftReps η)
      ⊢ renameᵗ (extN n suc) A ~ renameᵗ (extN n suc) R
same-weaken-at n (same-var d) = same-var (underNames-weaken n d)
same-weaken-at n same-ℕ = same-ℕ
same-weaken-at n same-𝔹 = same-𝔹
same-weaken-at n (same-⇒ p q) =
  same-⇒ (same-weaken-at n p) (same-weaken-at n q)
same-weaken-at n (same-∀ p) = same-∀ (same-weaken-at (suc n) p)

same-weaken : η ⊢ A ~ R → (zero ∷ shiftReps η) ⊢ ⇑ᵗ A ~ ⇑ᵗ R
same-weaken = same-weaken-at zero

-- Eliminating an ordinary `∀` binder commutes with the representation
-- reading.  Both sides substitute the readings of the same argument.
SameSub : TyCtx → TyCtx → Substᵗ → Substᵗ → Set
SameSub η η′ σ τ = ∀ {X α}
  → η ∋ˡ X := α
  → η′ ⊢ σ X ~ τ α

SameSub-ext : ∀ {σ τ} → SameSub η η′ σ τ
  → SameSub (zero ∷ shiftReps η) (zero ∷ shiftReps η′)
            (extsᵗ σ) (extsᵗ τ)
SameSub-ext h here = same-var here
SameSub-ext h (there d) with shiftReps-∋⁻ d
SameSub-ext h (there d) | α , refl , d′ = same-weaken (h d′)

same-subst : ∀ {σ τ} → SameSub η η′ σ τ → η ⊢ A ~ R
  → η′ ⊢ substᵗ σ A ~ substᵗ τ R
same-subst h (same-var d) = h d
same-subst h same-ℕ = same-ℕ
same-subst h same-𝔹 = same-𝔹
same-subst h (same-⇒ p q) = same-⇒ (same-subst h p) (same-subst h q)
same-subst h (same-∀ p) = same-∀ (same-subst (SameSub-ext h) p)

same-[] : (zero ∷ shiftReps η) ⊢ B ~ S → η ⊢ A ~ R
  → η ⊢ B [ A ]ᵗ ~ S [ R ]ᵗ
same-[] {A = A} {R = R} p q = same-subst h p
  where
  h : SameSub (zero ∷ shiftReps _) _ (singleTyEnv A) (singleTyEnv R)
  h here = q
  h (there d) with shiftReps-∋⁻ d
  h (there d) | α , refl , d′ = same-var d′

-- Shift only the FREE representation names while leaving the ordinary
-- spelling in place.  The depth parameter accounts for local `∀` names.
underNames-shift-free : ∀ {η X α} (n : ℕ)
  → underNames n η ∋ˡ X := α
  → underNames n (shiftReps η) ∋ˡ X := extN n suc α
underNames-shift-free zero d = shiftReps-∋ d
underNames-shift-free (suc n) here = here
underNames-shift-free (suc n) (there d) with shiftReps-∋⁻ d
underNames-shift-free (suc n) (there d) | α , refl , d′ =
  there (shiftReps-∋ (underNames-shift-free n d′))

same-shift-free-at : ∀ {η A R} (n : ℕ) → underNames n η ⊢ A ~ R
  → underNames n (shiftReps η)
      ⊢ A ~ renameᵗ (extN n suc) R
same-shift-free-at n (same-var d) =
  same-var (underNames-shift-free n d)
same-shift-free-at n same-ℕ = same-ℕ
same-shift-free-at n same-𝔹 = same-𝔹
same-shift-free-at n (same-⇒ p q) =
  same-⇒ (same-shift-free-at n p) (same-shift-free-at n q)
same-shift-free-at n (same-∀ p) = same-∀ (same-shift-free-at (suc n) p)

same-shift-free : η ⊢ A ~ R → shiftReps η ⊢ A ~ ⇑ᵗ R
same-shift-free = same-shift-free-at zero

underNames-ref : ∀ {η X α} (n : ℕ) → ValidNames Ξ η
  → underNames n η ∋ˡ X := α → Ξ ⊢ref[ n ] α
underNames-ref zero valid d with valid d
underNames-ref zero valid d | b , db = free-ref db
underNames-ref (suc n) valid here = local-ref (s≤s z≤n)
underNames-ref (suc n) valid (there d) with shiftReps-∋⁻ d
underNames-ref (suc n) valid (there d) | α , refl , d′ =
  ref-suc (underNames-ref n valid d′)

same-wfᴿ-at : ∀ {η A R} (n : ℕ) → ValidNames Ξ η
  → underNames n η ⊢ A ~ R → Ξ ⊢ᴿ[ n ] R
same-wfᴿ-at n valid (same-var d) =
  wfᴿ-var (underNames-ref n valid d)
same-wfᴿ-at n valid same-ℕ = wfᴿ-ℕ
same-wfᴿ-at n valid same-𝔹 = wfᴿ-𝔹
same-wfᴿ-at n valid (same-⇒ p q) =
  wfᴿ-⇒ (same-wfᴿ-at n valid p) (same-wfᴿ-at n valid q)
same-wfᴿ-at n valid (same-∀ p) = wfᴿ-∀ (same-wfᴿ-at (suc n) valid p)

same-wfᴿ : WfCtx Δ → names Δ ⊢ A ~ R → reps Δ ⊢ᴿ R
same-wfᴿ w p = same-wfᴿ-at zero (wf-names w) p

represented-wf : WfCtx Δ → names Δ ⊢ A ~ R
  → WfCtx ((bindR R ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ)))
represented-wf {Δ = Δ} {R = R} w p =
  wf-ctx (wf-bindR (same-wfᴿ w p) (wf-reps w)) valid
         (unique-underΛ {Γ = Δ} (name-fn w))
  where
  valid : ValidNames (bindR R ∷ reps Δ)
                     (zero ∷ shiftReps (names Δ))
  valid here = bindR R , here
  valid (there d) with shiftReps-∋⁻ d
  valid (there d) | α , refl , d′ with wf-names w d′
  valid (there d) | α , refl , d′ | b , db = b , there db

-- ALLOCATING A CELL.  The store grows at index 0 and every existing
-- representation variable — in the name map and in every sibling term —
-- moves up by one (`allocate`, strong-rep-nu.Ctx §9).  The payload is
-- well formed because `same-wfᴿ` reads it off the argument's `~`.
alloc-wf : ∀ {Δ R} → WfCtx Δ → reps Δ ⊢ᴿ R → WfCtx (allocate R Δ)
alloc-wf {Δ = Δ} {R = R} w wR =
  wf-ctx (wf-bindR wR (wf-reps w)) valid (unique-shift (name-fn w))
  where
  valid : ValidNames (bindR R ∷ reps Δ) (shiftReps (names Δ))
  valid d with shiftReps-∋⁻ d
  valid d | α , refl , d′ with wf-names w d′
  valid d | α , refl , d′ | b , db = b , there db

-- The representation weakening the allocation induces.  `repwk-cons₀`
-- needs exactly the payload's well-formedness.
repwk-alloc : ∀ {Ξ R} → Ξ ⊢ᴿ R → RepWk suc Ξ (bindR R ∷ Ξ)
repwk-alloc {R = R} wR = repwk-cons₀ (bindR R) (wf-bindR wR)

-- The target well-formedness is explicit: the only refinement that creates
-- a concrete binding is supplied by the caller together with its payload
-- proof. All output well-formedness is then derived by `BoundaryWf`.
⊢refine : ∀ {Ξ Ξ′ η Γ M A}
  → RepRefines Ξ Ξ′
  → WfCtx (Ξ′ ∣ η)
  → (Ξ ∣ η) ∣ Γ ⊢ M ⦂ A
  → (Ξ′ ∣ η) ∣ Γ ⊢ M ⦂ A
⊢refine rr w′ (⊢` d) = ⊢` d
⊢refine rr w′ ⊢$ = ⊢$
⊢refine rr w′ ⊢true = ⊢true
⊢refine rr w′ ⊢false = ⊢false
⊢refine rr w′ (⊢ƛ w ⊢N) =
  ⊢ƛ (wf-refine rr w) (⊢refine rr w′ ⊢N)
⊢refine rr w′ (⊢· ⊢L ⊢M) =
  ⊢· (⊢refine rr w′ ⊢L) (⊢refine rr w′ ⊢M)
⊢refine rr w′ (⊢Λ vN ⊢N) =
  ⊢Λ vN (⊢refine (rr-abst rr) (underΛ-wf w′) ⊢N)
  where
  underΛ-wf : ∀ {Γ : Ctxᵗ} → WfCtx Γ → WfCtx (underΛ Γ)
  underΛ-wf {Γ = Δ₀} (wf-ctx wr vn uq) =
    wf-ctx (wf-abstR wr) valid (unique-underΛ {Γ = Δ₀} uq)
    where
    valid : ValidNames (abstR ∷ reps Δ₀)
                       (zero ∷ shiftReps (names Δ₀))
    valid here = abstR , here
    valid (there d) with shiftReps-∋⁻ d
    valid (there d) | α , refl , d′ with vn d′
    valid (there d) | α , refl , d′ | b , db = b , there db
⊢refine rr w′
        (⊢ν wA rA ⊢L (bw w (interior cs) (conversion csᶜ)) ⊢c same wB) =
  ⊢ν (wf-refine rr wA) rA (⊢refine rr w′ ⊢L) mw′
     (conv-refine (rr-bind rr) ⊢c) same (wf-refine rr wB)
  where
  mw′ = bw (alloc-wf w′ (same-wfᴿ w′ rA))
           (interior (changes-refine (rr-bind rr) cs))
           (conversion (conv-changes-refine (rr-bind rr) csᶜ))
⊢refine {Ξ = Ξ} {Ξ′ = Ξ′} {η = η} rr w′
        (boundary (bw w (interior cs) (conversion csᶜ))
             ⊢M ⊢c sameᵢ sameₑ wE) =
  boundary mw′
      (⊢refine rr (bw-interior-wf mw′) ⊢M)
      (conv-refine rr ⊢c)
      sameᵢ sameₑ (wf-refine rr wE)
  where
  mw′ : BoundaryWf (Ξ′ ∣ η) _ (Ξ′ ∣ _) (Ξ′ ∣ _)
  mw′ =
    bw w′ (interior (changes-refine rr cs))
          (conversion (conv-changes-refine rr csᶜ))
-- THE INSTANTIATED SCOPE IS AGAIN A BOUNDARY SCOPE WITNESS, read at
-- the ALLOCATED context; the two readings are `inst-interior` and
-- `inst-conversion` (strong-rep-nu.Boundary §3a).
-- Commentary.md § proof/Preserve.agda / §2
inst-boundarywf : ∀ {Δ Δᵢ Δᶜ Θ A R}
  → BoundaryWf Δ Θ Δᵢ Δᶜ
  → names Δ ⊢ A ~ R
  → BoundaryWf (allocate R Δ) (inst Θ)
      ((bindR R ∷ reps Δᵢ) ∣ (zero ∷ shiftReps (names Δᵢ)))
      ((bindR R ∷ reps Δᶜ) ∣ (zero ∷ shiftReps (names Δᶜ)))
inst-boundarywf (bw wΔ (interior cs) (conversion csᶜ)) p =
  bw (alloc-wf wΔ (same-wfᴿ wΔ p))
     (inst-interior (interior cs))
     (inst-conversion (conversion csᶜ))

-- `⊢ν`'S BOUNDARY UNDER A REPRESENTATION RENAMING.  The scope is
-- `TyBetaBoundary` at `allocate R Δ`, so both its readings are pinned
-- to `R`'s represented binder; the renaming goes under that binder
-- (`repwk-bind`), and the conversion and both readings move with it.
-- Consumed by `⊢renᴿ` (strong-rep-nu.proof.RepWeaken) and by the
-- `ξ-ν` congruence of `preserve`.
ν-boundary-ren : ∀ {ρ Ξ′ Δ A R Δᵢ Δᶜ c C Cₑ B}
  → RepWk ρ (reps Δ) Ξ′
  → Δ ⊢ᶜ A ~ R
  → BoundaryWf (allocate R Δ) TyBetaBoundary Δᵢ Δᶜ
  → Δᶜ ⊢ c ∶ C ⇝ Cₑ
  → allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ
  → Σ[ Δ′ ∈ Ctxᵗ ]
      (BoundaryWf (allocate (renameᵗ ρ R) (Ξ′ ∣ map ρ (names Δ)))
                  TyBetaBoundary Δ′ Δ′
      × (Δ′ ⊢ c ∶ C ⇝ Cₑ)
      × (allocate (renameᵗ ρ R) (Ξ′ ∣ map ρ (names Δ)) ⊢ B ≈ Cₑ ⊣ Δ′))
ν-boundary-ren {ρ = ρ} {Ξ′ = Ξ′} {Δ = Δ} {R = R} w p mw ⊢c (Rₑ , q₁ , q₂)
  with conversion-functional (bw-conversion mw)
         (inst-conversion {R = R} {Γ = Δ} (conversion conv[]))
ν-boundary-ren {ρ = ρ} {Ξ′ = Ξ′} {Δ = Δ} {R = R} w p mw ⊢c (Rₑ , q₁ , q₂)
  | refl = _ , mw′ , ⊢c′ , same′
  where
  η₀ = names Δ

  w⁺ : RepWk (extᵗ ρ) (bindR R ∷ reps Δ) (bindR (renameᵗ ρ R) ∷ Ξ′)
  w⁺ = repwk-bind w

  ext′ : WfCtx (allocate (renameᵗ ρ R) (Ξ′ ∣ map ρ η₀))
  ext′ = subst (λ η′ → WfCtx ((bindR (renameᵗ ρ R) ∷ Ξ′) ∣ η′))
               (shiftReps-ren ρ η₀) (wfctx-ren w⁺ (bw-exterior mw))

  mw′ = bw ext′
           (inst-interior {R = renameᵗ ρ R} {Γ = Ξ′ ∣ map ρ η₀}
                          (interior changes[]))
           (inst-conversion {R = renameᵗ ρ R} {Γ = Ξ′ ∣ map ρ η₀}
                            (conversion conv[]))

  ⊢c′ = conv-cast (names-underΛ-ren ρ η₀) (conv-ren w⁺ ⊢c)

  same′ = renameᵗ (extᵗ ρ) Rₑ
        , same-cast (shiftReps-ren ρ η₀) (same-ren (extᵗ ρ) q₁)
        , same-cast (names-underΛ-ren ρ η₀) (same-ren (extᵗ ρ) q₂)

represented-lookup : names Δ ⊢ A ~ R
  → ((bindR R ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ)))
      ∋ zero := ⇑ᵗ A
represented-lookup {R = R} p =
  zero , ⇑ᵗ R , here , r-here , same-weaken p

lookup-underΛ : Δ ∋ X := A → underΛ Δ ∋ suc X := ⇑ᵗ A
lookup-underΛ (α , R , name , rep , same) =
  suc α , ⇑ᵗ R , there (shiftReps-∋ name) , r-there-abst rep ,
  same-weaken same

reveal-hit : (X : ℕ) → reveal X (` X) ≡ unseal X
reveal-hit X with X ≟ X
reveal-hit X | yes _ = refl
reveal-hit X | no ne = ⊥-elim (ne refl)

reveal-miss : (X Y : ℕ) → X ≢ Y → reveal X (` Y) ≡ ⌞ id (` Y) ⌟
reveal-miss X Y ne with X ≟ Y
reveal-miss X Y ne | yes eq = ⊥-elim (ne eq)
reveal-miss X Y ne | no _ = refl

conceal-hit : (X : ℕ) → conceal X (` X) ≡ tail (seal X)
conceal-hit X with X ≟ X
conceal-hit X | yes _ = refl
conceal-hit X | no ne = ⊥-elim (ne refl)

conceal-miss : (X Y : ℕ) → X ≢ Y → conceal X (` Y) ≡ ⌞ id (` Y) ⌟
conceal-miss X Y ne with X ≟ Y
conceal-miss X Y ne | yes eq = ⊥-elim (ne eq)
conceal-miss X Y ne | no _ = refl

mutual
  ⊢reveal : Δ ∋ X := A → Δ ⊢ᵗ B
    → Δ ⊢ reveal X B ∶ B ⇝ B [ X := A ]ᵗ
  ⊢reveal {X = X} {A = A} {B = ` Y} d (wf-var tv) with X ≟ℕ Y
  ⊢reveal {X = X} {A = A} {B = ` Y} d (wf-var tv) | yes refl
    rewrite reveal-hit X | single-at-hit X A = conv-unseal d
  ⊢reveal {X = X} {A = A} {B = ` Y} d (wf-var tv) | no ne
    rewrite reveal-miss X Y ne | single-at-miss X Y A ne =
    conv-tail (conv-mid (conv-idv tv))
  ⊢reveal d wf-ℕ = conv-tail (conv-mid (conv-id base-ℕ))
  ⊢reveal d wf-𝔹 = conv-tail (conv-mid (conv-id base-𝔹))
  ⊢reveal d (wf-⇒ wA wB) =
    conv-tail (conv-mid (conv-fun (⊢conceal d wA) (⊢reveal d wB)))
  ⊢reveal {X = X} {A = A} {B = `∀ B} d (wf-∀ wB)
    rewrite subst-at-∀ X A B =
    conv-tail (conv-mid (conv-all (⊢reveal (lookup-underΛ d) wB)))

  ⊢conceal : Δ ∋ X := A → Δ ⊢ᵗ B
    → Δ ⊢ conceal X B ∶ B [ X := A ]ᵗ ⇝ B
  ⊢conceal {X = X} {A = A} {B = ` Y} d (wf-var tv) with X ≟ℕ Y
  ⊢conceal {X = X} {A = A} {B = ` Y} d (wf-var tv) | yes refl
    rewrite conceal-hit X | single-at-hit X A = conv-tail (conv-seal d)
  ⊢conceal {X = X} {A = A} {B = ` Y} d (wf-var tv) | no ne
    rewrite conceal-miss X Y ne | single-at-miss X Y A ne =
    conv-tail (conv-mid (conv-idv tv))
  ⊢conceal d wf-ℕ = conv-tail (conv-mid (conv-id base-ℕ))
  ⊢conceal d wf-𝔹 = conv-tail (conv-mid (conv-id base-𝔹))
  ⊢conceal d (wf-⇒ wA wB) =
    conv-tail (conv-mid (conv-fun (⊢reveal d wA) (⊢conceal d wB)))
  ⊢conceal {X = X} {A = A} {B = `∀ B} d (wf-∀ wB)
    rewrite subst-at-∀ X A B =
    conv-tail (conv-mid (conv-all (⊢conceal (lookup-underΛ d) wB)))

rr-refl : RepRefines Ξ Ξ
rr-refl {Ξ = []} = rr[]
rr-refl {Ξ = abstR ∷ Ξ} = rr-abst rr-refl
rr-refl {Ξ = bindR R ∷ Ξ} = rr-bind rr-refl

------------------------------------------------------------------------
-- §3. The local reduction cases
------------------------------------------------------------------------

empty-interior : Δ ⊢ⁱ [] ⇒ Δ
empty-interior = interior changes[]

empty-conversion : Δ ⊢ᶜ [] ⇒ Δ
empty-conversion = conversion conv[]

sameTy-∀⁻ : ∀ {η η′ A B}
  → ∃[ R ] ((η ⊢ `∀ A ~ R) × (η′ ⊢ `∀ B ~ R))
  → ∃[ R ] (((zero ∷ shiftReps η) ⊢ A ~ R) ×
             ((zero ∷ shiftReps η′) ⊢ B ~ R))
sameTy-∀⁻ (`∀ R , same-∀ p , same-∀ q) = R , p , q

sameTy-target-∀⁻ : ∀ {η η′ A B}
  → ∃[ R ] ((η ⊢ A ~ R) × (η′ ⊢ `∀ B ~ R))
  → Σ[ A₀ ∈ Ty ] ((A ≡ `∀ A₀) ×
       (∃[ R ] (((zero ∷ shiftReps η) ⊢ A₀ ~ R) ×
          ((zero ∷ shiftReps η′) ⊢ B ~ R))))
sameTy-target-∀⁻ (`∀ R , same-∀ p , same-∀ q) =
  _ , refl , (R , p , q)
wf-∀⁻ : Δ ⊢ᵗ `∀ A → underΛ Δ ⊢ᵗ A
wf-∀⁻ (wf-∀ w) = w

-- THE REPRESENTED CONTEXT a `ν` at `R` leaves: `R`'s cell with ordinary
-- name 0, the old names shifted underneath.  It is both readings of
-- `inst []` at `allocate R Δ`.
reprCtx : Ty → Ctxᵗ → Ctxᵗ
reprCtx R Δ = (bindR R ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ))

-- THE OUTER LAYER OF EVERY `Nu` CONTRACTUM is `⊢ν`'s own boundary:
-- the scope witness, the conversion and the exterior reading are `⊢ν`'s
-- premises verbatim, once the scope's readings are pinned.
nu-outer : ∀ {Δ R Δᵢ Δᶜ M c C Cₑ B}
  → BoundaryWf (allocate R Δ) TyBetaBoundary Δᵢ Δᶜ
  → reprCtx R Δ ∣ [] ⊢ M ⦂ C
  → Δᶜ ⊢ c ∶ C ⇝ Cₑ
  → allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ
  → Δ ⊢ᵗ B
  → allocate R Δ ∣ [] ⊢ M ⟪ inst [] , c ⟫ ⦂ B
nu-outer {Δ = Δ} {R = R} mw ⊢M ⊢c same wB
  with interior-functional (bw-interior mw)
         (inst-interior {R = R} {Γ = Δ} (interior changes[]))
     | conversion-functional (bw-conversion mw)
         (inst-conversion {R = R} {Γ = Δ} (conversion conv[]))
nu-outer {Δ = Δ} {R = R} mw ⊢M ⊢c same wB | refl | refl =
  boundary mw ⊢M ⊢c sameᵢ same
      (wf-ren-rep {Ξ = reps Δ} {Ξ′ = bindR R ∷ reps Δ} {ρ = suc} wB)
  where
  sameᵢ : reprCtx R Δ ⊢ _ ≈ _ ⊣ reprCtx R Δ
  sameᵢ with wf-same (⊢ᵗ-of CtxWf-[] ⊢M)
  sameᵢ | S , q = S , q , q

-- `Nu-Λ`: the body, refined at the new cell, is the interior.
preserve-Nu-Λ : ∀ {Δ N A R c C}
  → WfCtx Δ
  → Δ ⊢ᶜ A ~ R
  → Δ ∣ [] ⊢ ν A · (Λ N) ⟨ c ⟩ ⦂ C
  → allocate R Δ ∣ [] ⊢ N ⟪ inst [] , c ⟫ ⦂ C
preserve-Nu-Λ wfΔ p (⊢ν wA rA (⊢Λ vN ⊢N) mw ⊢c same wB)
  with same-rep-unique rA p
preserve-Nu-Λ wfΔ p (⊢ν wA rA (⊢Λ vN ⊢N) mw ⊢c same wB) | refl =
  nu-outer mw (⊢refine (rr-represent rr-refl) (represented-wf wfΔ p) ⊢N)
           ⊢c same wB

-- `Nu-⟪Λ⟫`: the middle layer is the crossed boundary read under the new
-- name, and every one of its premises is the crossed `boundary`'s, refined
-- at the new cell (`liftᴮ-interior`, `liftᴮ-conversion`).
preserve-Nu-⟪Λ⟫ : ∀ {Δ N Θ s c A R C}
  → WfCtx Δ
  → Δ ⊢ᶜ A ~ R
  → Δ ∣ [] ⊢ ν A · ((Λ N) ⟪ Θ , ⌞ `∀ s ⌟ ⟫) ⟨ c ⟩ ⦂ C
  → allocate R Δ ∣ [] ⊢ (N ⟪ liftᴮ Θ , s ⟫) ⟪ inst [] , c ⟫ ⦂ C
preserve-Nu-⟪Λ⟫ wfΔ p
    (⊢ν wA rA (boundary mwΘ (⊢Λ vN ⊢N) ⊢c₀ sameᵢ sameₑ wE) mw ⊢c same wB)
  with same-rep-unique rA p | conv-all-inv ⊢c₀
preserve-Nu-⟪Λ⟫ wfΔ p
    (⊢ν wA rA (boundary mwΘ (⊢Λ vN ⊢N) ⊢c₀ sameᵢ sameₑ wE) mw ⊢c same wB)
  | refl | A₀ , B₀ , refl , refl , ⊢s₀ =
  nu-outer mw middle ⊢c same wB
  where
  mw₁ = bw (represented-wf wfΔ p)
           (liftᴮ-interior (bw-interior mwΘ))
           (liftᴮ-conversion (bw-conversion mwΘ))

  middle =
    boundary mw₁ (⊢refine (rr-represent rr-refl) (bw-interior-wf mw₁) ⊢N)
        (conv-refine (rr-represent rr-refl) ⊢s₀)
        (sameTy-∀⁻ sameᵢ) (sameTy-∀⁻ sameₑ)
        (wf-refine (rr-represent rr-refl) (wf-∀⁻ wE))

same-ℕ-rep : η ⊢ `ℕ ~ R → R ≡ `ℕ
same-ℕ-rep same-ℕ = refl

same-𝔹-rep : η ⊢ `𝔹 ~ R → R ≡ `𝔹
same-𝔹-rep same-𝔹 = refl

sameTy-ℕ-𝔹-absurd : ∀ {η η′}
  → ∃[ R ] ((η ⊢ `ℕ ~ R) × (η′ ⊢ `𝔹 ~ R))
  → ⊥
sameTy-ℕ-𝔹-absurd (`ℕ , same-ℕ , ())

-- The exterior comparison is now at EQUAL depth — a boundary carries no
-- bind block — so a base conversion type pins the exterior type outright.
sameTy-ℕ : ∀ {Δ A η′}
  → WfCtx Δ
  → ∃[ R ] ((names Δ ⊢ A ~ R) × (η′ ⊢ `ℕ ~ R))
  → A ≡ `ℕ
sameTy-ℕ wfΔ (R , p , q) with same-ℕ-rep q
sameTy-ℕ wfΔ (R , p , q) | refl =
  same-target-unique (name-fn wfΔ) p same-ℕ

sameTy-𝔹 : ∀ {Δ A η′}
  → WfCtx Δ
  → ∃[ R ] ((names Δ ⊢ A ~ R) × (η′ ⊢ `𝔹 ~ R))
  → A ≡ `𝔹
sameTy-𝔹 wfΔ (R , p , q) with same-𝔹-rep q
sameTy-𝔹 wfΔ (R , p , q) | refl =
  same-target-unique (name-fn wfΔ) p same-𝔹

-- `Drop`: typing makes the simple value a literal at the base type,
-- and a literal types at every context.
preserve-Drop : ∀ {Δ U Θ A C}
  → WfCtx Δ
  → Simple U
  → Base A
  → Δ ∣ [] ⊢ U ⟪ Θ , ⌞ id A ⌟ ⟫ ⦂ C
  → Δ ∣ [] ⊢ U ⦂ C
preserve-Drop wfΔ u base-ℕ
  (boundary mwΘ ⊢$ (conv-tail (conv-mid (conv-id base-ℕ)))
       sameᵢ sameₑ wE)
  rewrite sameTy-ℕ wfΔ sameₑ = ⊢$
preserve-Drop wfΔ u base-𝔹
  (boundary mwΘ ⊢$ (conv-tail (conv-mid (conv-id base-𝔹)))
       sameᵢ sameₑ wE) =
  ⊥-elim (sameTy-ℕ-𝔹-absurd sameᵢ)
preserve-Drop wfΔ u base-𝔹
  (boundary mwΘ ⊢true (conv-tail (conv-mid (conv-id base-𝔹)))
       sameᵢ sameₑ wE)
  rewrite sameTy-𝔹 wfΔ sameₑ = ⊢true
preserve-Drop wfΔ u base-ℕ
  (boundary mwΘ ⊢true (conv-tail (conv-mid (conv-id base-ℕ)))
       (_ , same-𝔹 , ()) sameₑ wE)
preserve-Drop wfΔ u base-𝔹
  (boundary mwΘ ⊢false (conv-tail (conv-mid (conv-id base-𝔹)))
       sameᵢ sameₑ wE)
  rewrite sameTy-𝔹 wfΔ sameₑ = ⊢false
preserve-Drop wfΔ u base-ℕ
  (boundary mwΘ ⊢false (conv-tail (conv-mid (conv-id base-ℕ)))
       (_ , same-𝔹 , ()) sameₑ wE)
preserve-Drop wfΔ u base-ℕ
  (boundary mwΘ (⊢ƛ w ⊢N) (conv-tail (conv-mid (conv-id base-ℕ)))
       (_ , same-⇒ _ _ , ()) sameₑ wE)
preserve-Drop wfΔ u base-𝔹
  (boundary mwΘ (⊢ƛ w ⊢N) (conv-tail (conv-mid (conv-id base-𝔹)))
       (_ , same-⇒ _ _ , ()) sameₑ wE)
preserve-Drop wfΔ u base-ℕ
  (boundary mwΘ (⊢Λ v ⊢N) (conv-tail (conv-mid (conv-id base-ℕ)))
       (_ , same-∀ _ , ()) sameₑ wE)
preserve-Drop wfΔ u base-𝔹
  (boundary mwΘ (⊢Λ v ⊢N) (conv-tail (conv-mid (conv-id base-𝔹)))
       (_ , same-∀ _ , ()) sameₑ wE)

------------------------------------------------------------------------
-- §4. The representation-only transports, and the store bookkeeping
------------------------------------------------------------------------

-- TWO TRANSPORTS, both PROVED downstream, both internal staging
-- interfaces only.  The first needs a BINDER on top of the renaming;
-- the second, the SIBLING SHIFT, is pure renaming.
-- Commentary.md § proof/Preserve.agda / §4
CrossΛTyping : Set
CrossΛTyping = ∀ {Δ W A}
  → WfCtx Δ
  → Δ ⊢ᵗ A
  → Δ ∣ [] ⊢ W ⦂ A
  → underΛ Δ ∣ [] ⊢ crossΛᴹ W A ⦂ ⇑ᵗ A

-- THE SIBLING SHIFT — the one new lemma of the store experiment.
-- THE PAYLOAD MUST BE WELL FORMED: without `reps Δ ⊢ᴿ R` the statement
-- is FALSE, and at every call site it is `same-wfᴿ` of the rule's own
-- `Δ ⊢ᶜ A ~ R` premise (`step-alloc`).
-- Commentary.md § proof/Preserve.agda / §4
ShiftTyping : Set
ShiftTyping = ∀ {Δ Γ M A R}
  → reps Δ ⊢ᴿ R
  → Δ ∣ Γ ⊢ M ⦂ A
  → allocate R Δ ∣ Γ ⊢ renᴹᴿ suc M ⦂ A

-- What a step's change did to the store, as a PROPOSITION: nothing, or
-- one well-formed cell.  Everything the theorems need about `apply` and
-- `↑ᴹ[_]` is stated once at `none` (identity) and once at `new R`.
data AllocWf : Alloc → Ctxᵗ → Set where
  aw-none : ∀ {Δ} → AllocWf none Δ
  aw-new  : ∀ {Δ R} → reps Δ ⊢ᴿ R → AllocWf (new R) Δ

-- A boundary changes NAMES only, so a reading transports an `AllocWf`.
aw-reps : ∀ {Δ Δ′ δ} → reps Δ′ ≡ reps Δ → AllocWf δ Δ′ → AllocWf δ Δ
aw-reps eq aw-none = aw-none
aw-reps eq (aw-new wR) = aw-new (subst (λ Ξ → Ξ ⊢ᴿ _) eq wR)

apply-wf : ∀ {Δ δ} → WfCtx Δ → AllocWf δ Δ → WfCtx (apply δ Δ)
apply-wf w aw-none = w
apply-wf w (aw-new wR) = alloc-wf w wR

⊢ᵗ-apply : ∀ {Δ A} (δ : Alloc) → Δ ⊢ᵗ A → apply δ Δ ⊢ᵗ A
⊢ᵗ-apply none w = w
⊢ᵗ-apply {Δ = Δ} (new R) w =
  wf-ren-rep {Ξ = reps Δ} {Ξ′ = bindR R ∷ reps Δ} {ρ = suc} w

⊢↑ : ShiftTyping → ∀ {Δ Γ M A} {δ : Alloc}
  → AllocWf δ Δ → Δ ∣ Γ ⊢ M ⦂ A
  → apply δ Δ ∣ Γ ⊢ ↑ᴹ[ δ ] M ⦂ A
⊢↑ shift aw-none ⊢M = ⊢M
⊢↑ shift (aw-new wR) ⊢M = shift wR ⊢M

-- THE BOUNDARY CASE OF THE CONGRUENCE: the new boundary's reading at
-- `apply δ Δ` has interior `apply δ Δᵢ`, because a boundary keeps the
-- store.  Commentary.md § proof/Preserve.agda / §4
boundary-apply : ∀ {Δ Δᵢ Δᶜ Γ Θ c M′ Bᵢ Cᵢ Cₑ Bₑ} {δ : Alloc}
  → AllocWf δ Δ
  → BoundaryWf Δ Θ Δᵢ Δᶜ
  → apply δ Δᵢ ∣ [] ⊢ M′ ⦂ Bᵢ
  → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
  → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
  → Δ ⊢ Bₑ ≈ Cₑ ⊣ Δᶜ
  → Δ ⊢ᵗ Bₑ
  → apply δ Δ ∣ Γ ⊢ M′ ⟪ ↑ᴮ[ δ ] Θ , c ⟫ ⦂ Bₑ
boundary-apply aw-none mwΘ ⊢M′ ⊢c sameᵢ sameₑ wE =
  boundary mwΘ ⊢M′ ⊢c sameᵢ sameₑ wE
boundary-apply {Δ = Δ} {δ = new R} (aw-new wR)
          (bw wΔ (interior cs) (conversion csᶜ))
          ⊢M′ ⊢c (Rᵢ , pᵢ , qᵢ) (Rₑ , pₑ , qₑ) wE =
  boundary (bw (alloc-wf wΔ wR)
          (interior-ren w (interior cs))
          (conversion-ren w (conversion csᶜ)))
      ⊢M′
      (conv-ren w ⊢c)
      (renameᵗ suc Rᵢ , same-ren suc pᵢ , same-ren suc qᵢ)
      (renameᵗ suc Rₑ , same-ren suc pₑ , same-ren suc qₑ)
      (wf-ren-rep {Ξ = reps Δ} {Ξ′ = bindR R ∷ reps Δ} {ρ = suc} wE)
  where
  w : RepWk suc (reps Δ) (bindR R ∷ reps Δ)
  w = repwk-alloc wR

-- THE `ν` CASE OF THE CONGRUENCE: `ν`'s own boundary is re-read at
-- `apply δ Δ` by `ν-boundary-ren` at the allocation's weakening.
nu-apply : ∀ {Δ Δᵢ Δᶜ Γ A R L′ C Cₑ B c} {δ : Alloc}
  → AllocWf δ Δ
  → Δ ⊢ᵗ A
  → Δ ⊢ᶜ A ~ R
  → apply δ Δ ∣ Γ ⊢ L′ ⦂ `∀ C
  → BoundaryWf (allocate R Δ) TyBetaBoundary Δᵢ Δᶜ
  → Δᶜ ⊢ c ∶ C ⇝ Cₑ
  → allocate R Δ ⊢ B ≈ Cₑ ⊣ Δᶜ
  → Δ ⊢ᵗ B
  → apply δ Δ ∣ Γ ⊢ ν A · L′ ⟨ c ⟩ ⦂ B
nu-apply aw-none wA rA ⊢L′ mw ⊢c same wB = ⊢ν wA rA ⊢L′ mw ⊢c same wB
nu-apply {δ = new S} (aw-new wS) wA rA ⊢L′ mw ⊢c same wB
  with ν-boundary-ren (repwk-alloc wS) rA mw ⊢c same
nu-apply {δ = new S} (aw-new wS) wA rA ⊢L′ mw ⊢c same wB
  | Δ′ , mw′ , ⊢c′ , same′ =
  ⊢ν (⊢ᵗ-apply (new S) wA) (same-ren suc rA) ⊢L′ mw′ ⊢c′ same′
     (⊢ᵗ-apply (new S) wB)

wf-underΛ : WfCtx Δ → WfCtx (underΛ Δ)
wf-underΛ {Δ = Δ} (wf-ctx wr vn uq) =
  wf-ctx (wf-abstR wr) valid (unique-underΛ {Γ = Δ} uq)
  where
  valid : ValidNames (abstR ∷ reps Δ)
                     (zero ∷ shiftReps (names Δ))
  valid here = abstR , here
  valid (there d) with shiftReps-∋⁻ d
  valid (there d) | α , refl , d′ with vn d′
  valid (there d) | α , refl , d′ | b , db = b , there db

⇑ᴵ-⊢1 : CrossΛTyping → ∀ {Δ Γ i A}
  → WfCtx Δ
  → Δ ∣ Γ ⊢ⁱ i ⦂ A
  → underΛ Δ ∣ ⤊ Γ ⊢ⁱ ⇑ᴵ i ⦂ ⇑ᵗ A
⇑ᴵ-⊢1 cross wfΔ (⊢ivar d) = ⊢ivar (∋-⤊ d)
⇑ᴵ-⊢1 cross {Δ = Δ} wfΔ (⊢ival w ⊢W) =
  ⊢ival (wf-ren (WfRen-wk {Δ = Δ}) w) (cross wfΔ w ⊢W)

⇑ᴵ-⊢ : CrossΛTyping → ∀ {σ : Var → Img} {Δ Γ Γ′}
  → WfCtx Δ
  → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∣ Γ′ ⊢ⁱ σ x ⦂ B)
  → (∀ {x B} → ⤊ Γ ∋ x ⦂ B
      → underΛ Δ ∣ ⤊ Γ′ ⊢ⁱ ⇑ᴵ (σ x) ⦂ B)
⇑ᴵ-⊢ cross wfΔ h d with ∋-map⁻ d
⇑ᴵ-⊢ cross wfΔ h d | A , refl , q = ⇑ᴵ-⊢1 cross wfΔ (h q)

⊢substᴹ : CrossΛTyping → ∀ {σ : Var → Img} {Δ Γ Γ′ N B}
  → WfCtx Δ
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Γ′ ⊢ⁱ σ x ⦂ A)
  → Δ ∣ Γ ⊢ N ⦂ B
  → Δ ∣ Γ′ ⊢ substᵐ σ N ⦂ B
⊢substᴹ cross wfΔ h (⊢` d) = ⊢imgTm (h d)
⊢substᴹ cross wfΔ h ⊢$ = ⊢$
⊢substᴹ cross wfΔ h ⊢true = ⊢true
⊢substᴹ cross wfΔ h ⊢false = ⊢false
⊢substᴹ cross wfΔ h (⊢ƛ w ⊢N) =
  ⊢ƛ w (⊢substᴹ cross wfΔ (extᴵ-⊢ h) ⊢N)
⊢substᴹ cross wfΔ h (⊢· ⊢L ⊢M) =
  ⊢· (⊢substᴹ cross wfΔ h ⊢L) (⊢substᴹ cross wfΔ h ⊢M)
⊢substᴹ cross wfΔ h (⊢Λ vN ⊢N) =
  ⊢Λ (value-substᵐ vN)
     (⊢substᴹ cross (wf-underΛ wfΔ) (⇑ᴵ-⊢ cross wfΔ h) ⊢N)
⊢substᴹ cross wfΔ h (⊢ν wA rA ⊢L mw ⊢c same wB) =
  ⊢ν wA rA (⊢substᴹ cross wfΔ h ⊢L) mw ⊢c same wB
⊢substᴹ cross wfΔ h (boundary mwᵥ ⊢M ⊢c sameᵢ sameₑ wE) =
  boundary mwᵥ ⊢M ⊢c sameᵢ sameₑ wE

⊢subst : CrossΛTyping → ∀ {Δ Γ A B N W}
  → WfCtx Δ
  → Δ ⊢ᵗ A
  → Δ ∣ A ∷ Γ ⊢ N ⦂ B
  → Δ ∣ [] ⊢ W ⦂ A
  → Δ ∣ Γ ⊢ N [ W ∶ A ]ᵐ ⦂ B
⊢subst cross wfΔ w ⊢N ⊢W =
  ⊢substᴹ cross wfΔ
    (λ { here → ⊢ival w ⊢W ; (there d) → ⊢ivar d }) ⊢N

preserve-Beta : CrossΛTyping → ∀ {Δ A B N W}
  → WfCtx Δ
  → Δ ∣ [] ⊢ (ƛ A ∙ N) · W ⦂ B
  → Δ ∣ [] ⊢ N [ W ∶ A ]ᵐ ⦂ B
preserve-Beta cross wfΔ (⊢· (⊢ƛ w ⊢N) ⊢W) =
  ⊢subst cross wfΔ w ⊢N ⊢W

------------------------------------------------------------------------
-- §4b. Preservation assembled over the downstream crossing cases
------------------------------------------------------------------------

-- These stay module parameters HERE because their proofs import this
-- module; strong-rep-nu.Preservation plugs in every implementation
-- and exposes NO public parameter at all.  Who proves what, and when:
-- Commentary.md § proof/Preserve.agda / §4b

PeelCase : Set
PeelCase = ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t C}
  → WfCtx Δ → Simple V → Value W
  → Δ ⊢ᶜ Θ ⇒ Δᶜ → Δ ⊢ⁱ Θ ⇒ Δᵢ
  → Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ → SameConv Δᵈ s′ Δᶜ s
  → Δ ∣ [] ⊢ (V ⟪ Θ , ⌞ s ↦ t ⌟ ⟫) · W ⦂ C
  → Δ ∣ [] ⊢
      (V · (W ⟪ dual Θ , s′ ⟫)) ⟪ Θ , t ⟫ ⦂ C

MergeCase : Set
MergeCase = ∀ {Δ Δᵢ Δ₁ᶜ Δ₂ᶜ Δ⋉ᶜ U Θ₁ Θ₂ t₁ t₁′ c₂ c₂′ C}
  → WfCtx Δ → Simple U → InertTail t₁
  → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
  → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
  → Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ
  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
  → SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)
  → SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂
  → Δ ∣ [] ⊢ (U ⟪ Θ₁ , tail t₁ ⟫) ⟪ Θ₂ , c₂ ⟫ ⦂ C
  → Δ ∣ [] ⊢ U ⟪ Θ₁ ++ Θ₂ , Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′ ⟫ ⦂ C

------------------------------------------------------------------------
-- §5. What a step did to the store
------------------------------------------------------------------------

-- ONLY THE TWO ∀-ELIMINATIONS ALLOCATE, and each carries the reading
-- that makes the minted cell well formed.  NO TYPING DERIVATION IS
-- NEEDED — the rule premises and `WfCtx Δ` are enough.
step-alloc : ∀ {Δ M M′ δ} → WfCtx Δ → Δ ⊢ M -→ M′ ∣ δ → AllocWf δ Δ
step-alloc wfΔ (Nu-Λ v p) = aw-new (same-wfᴿ wfΔ p)
step-alloc wfΔ (Beta w) = aw-none
step-alloc wfΔ (Peel v w rc ri rd sc) = aw-none
step-alloc wfΔ (Nu-⟪Λ⟫ v rc ⊢s p) = aw-new (same-wfᴿ wfΔ p)
step-alloc wfΔ (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂) = aw-none
step-alloc wfΔ (Drop u b) = aw-none
step-alloc wfΔ (ξ-·-l st) = step-alloc wfΔ st
step-alloc wfΔ (ξ-·-r v st) = step-alloc wfΔ st
step-alloc wfΔ (ξ-ν st) = step-alloc wfΔ st
step-alloc wfΔ (ξ-⟪⟫ ri st) =
  aw-reps (interior-reps ri) (step-alloc (interior-wf wfΔ ri) st)

-- PRESERVATION OF WELL-FORMEDNESS.  The typing derivation is not read:
-- it is part of the statement only so that the two preservation theorems
-- read the same.
preserve-wf : ∀ {Δ M M′ A δ} → WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ → WfCtx (apply δ Δ)
preserve-wf wfΔ ⊢M st = apply-wf wfΔ (step-alloc wfΔ st)

module Impl
  (crossΛ  : CrossΛTyping)
  (shift   : ShiftTyping)
  (peel    : PeelCase)
  (merge   : MergeCase)
  where

  preserve : ∀ {Δ M M′ A δ} → WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A
    → Δ ⊢ M -→ M′ ∣ δ → apply δ Δ ∣ [] ⊢ M′ ⦂ A
  preserve wfΔ ⊢M (Nu-Λ v p) = preserve-Nu-Λ wfΔ p ⊢M
  preserve wfΔ ⊢M (Beta v) = preserve-Beta crossΛ wfΔ ⊢M
  preserve wfΔ ⊢M (Peel v w rc ri rd sc) =
    peel wfΔ v w rc ri rd sc ⊢M
  preserve wfΔ ⊢M (Nu-⟪Λ⟫ v rc ⊢s p) = preserve-Nu-⟪Λ⟫ wfΔ p ⊢M
  preserve wfΔ ⊢M (Merge u it ri r₁ r₂ r⋉ sc₁ sc₂) =
    merge wfΔ u it ri r₁ r₂ r⋉ sc₁ sc₂ ⊢M
  preserve wfΔ ⊢M (Drop u b) = preserve-Drop wfΔ u b ⊢M
  preserve wfΔ (⊢· ⊢L ⊢M) (ξ-·-l st) =
    ⊢· (preserve wfΔ ⊢L st) (⊢↑ shift (step-alloc wfΔ st) ⊢M)
  preserve wfΔ (⊢· ⊢L ⊢M) (ξ-·-r v st) =
    ⊢· (⊢↑ shift (step-alloc wfΔ st) ⊢L) (preserve wfΔ ⊢M st)
  preserve wfΔ (⊢ν wA rA ⊢L mw ⊢c same wB) (ξ-ν st) =
    nu-apply (step-alloc wfΔ st) wA rA (preserve wfΔ ⊢L st) mw ⊢c same wB
  preserve wfΔ (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE) (ξ-⟪⟫ ri st)
    with interior-functional ri (bw-interior mwΘ)
  preserve wfΔ (boundary mwΘ ⊢M ⊢c sameᵢ sameₑ wE) (ξ-⟪⟫ ri st)
    | refl =
    boundary-apply (aw-reps (interior-reps ri)
                       (step-alloc (bw-interior-wf mwΘ) st))
              mwΘ (preserve (bw-interior-wf mwΘ) ⊢M st)
              ⊢c sameᵢ sameₑ wE

  -- ALONG A WHOLE RUN.  The endpoint's context is read off the
  -- derivation (`runCtx`): each step's change is applied to the context
  -- the tail runs at.
  preserve* : ∀ {Δ M M′ A} → WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A
    → (r : Δ ⊢ M -→* M′) → runCtx r ∣ [] ⊢ M′ ⦂ A
  preserve* wfΔ ⊢M done = ⊢M
  preserve* wfΔ ⊢M (st then sts) =
    preserve* (preserve-wf wfΔ ⊢M st) (preserve wfΔ ⊢M st) sts
