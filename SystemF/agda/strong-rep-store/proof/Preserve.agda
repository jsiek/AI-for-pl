module strong-rep-store.proof.Preserve where

-- Preservation for the two-universe representation-variable design.
--
-- §1 recovers type well-formedness from typing and supplies the ordinary
-- type-substitution facts used by elimination. §2 types the conversions
-- minted by TyBeta and TyPeelR. §3 proves the local reduction cases. §4
-- assembles preservation while leaving the downstream-owned crossing
-- proofs as parameters.  ALL of them now have implementations, the last
-- being `AddLock0Typing` — reshaped with the 2026-09-20 `TyPeelR-⟪⟫`
-- repair and proved the same day in `strong-rep-store.proof.AddLock0` — so
-- `strong-rep-store.Preservation` exposes no parameter at all.

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-store.Types
open import strong-rep-store.proof.TypeSubst
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst
open import strong-rep-store.Reduction

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

shiftNames-∋ : η ∋ˡ X := α → shiftNames η ∋ˡ X := suc α
shiftNames-∋ here = here
shiftNames-∋ (there d) = there (shiftNames-∋ d)

shiftNames-∋⁻ : shiftNames η ∋ˡ X := α
  → ∃[ β ] ((α ≡ suc β) × (η ∋ˡ X := β))
shiftNames-∋⁻ {η = []} ()
shiftNames-∋⁻ {η = β ∷ η} here = β , refl , here
shiftNames-∋⁻ {η = β ∷ η} (there d) with shiftNames-∋⁻ d
shiftNames-∋⁻ {η = β ∷ η} (there d) | α′ , refl , d′ =
  α′ , refl , there d′

tv-underΛ-zero : underΛ Δ ∋tv zero
tv-underΛ-zero = zero , here

tv-underΛ-suc : Δ ∋tv X → underΛ Δ ∋tv suc X
tv-underΛ-suc (α , d) = suc α , there (shiftNames-∋ d)

tv-underΛ-tail : underΛ Δ ∋tv suc X → Δ ∋tv X
tv-underΛ-tail (α , there d) with shiftNames-∋⁻ d
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
⊢ᵗ-of h (⊢·[] ⊢L w) with ⊢ᵗ-of h ⊢L
⊢ᵗ-of h (⊢·[] ⊢L w) | wf-∀ wB = wf-[]ᵗ wB w
⊢ᵗ-of h (env _ _ _ _ _ wE) = wE

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

-- Type formation depends on the ordinary POSITIONS a context offers and
-- on nothing else, so it transports along any map that keeps them.
TvMono : Ctxᵗ → Ctxᵗ → Set
TvMono Δ Δ′ = ∀ {X} → Δ ∋tv X → Δ′ ∋tv X

tvMono-underΛ : ∀ (Δ Δ′ : Ctxᵗ) → TvMono Δ Δ′
  → TvMono (underΛ Δ) (underΛ Δ′)
tvMono-underΛ Δ Δ′ f (α , here) = zero , here
tvMono-underΛ Δ Δ′ f (α , there d) with shiftNames-∋⁻ d
tvMono-underΛ Δ Δ′ f (α , there d) | β , refl , d′ with f (β , d′)
tvMono-underΛ Δ Δ′ f (α , there d) | β , refl , d′ | γ , d″ =
  suc γ , there (shiftNames-∋ d″)

wf-mono : ∀ {A} (Δ Δ′ : Ctxᵗ) → TvMono Δ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A
wf-mono Δ Δ′ f (wf-var tv) = wf-var (f tv)
wf-mono Δ Δ′ f wf-ℕ = wf-ℕ
wf-mono Δ Δ′ f wf-𝔹 = wf-𝔹
wf-mono Δ Δ′ f (wf-⇒ wA wB) =
  wf-⇒ (wf-mono Δ Δ′ f wA) (wf-mono Δ Δ′ f wB)
wf-mono Δ Δ′ f (wf-∀ wA) =
  wf-∀ (wf-mono (underΛ Δ) (underΛ Δ′) (tvMono-underΛ Δ Δ′ f) wA)

-- A parallel bind block renumbers representation variables and leaves
-- every ordinary position where it was.
shiftRVars-∋ : (k : ℕ) → η ∋ˡ X := α → shiftRVars k η ∋ˡ X := k + α
shiftRVars-∋ k here = here
shiftRVars-∋ k (there d) = there (shiftRVars-∋ k d)

tvMono-extendReps : (Rs : List Ty) (Γ : Ctxᵗ) → TvMono Γ (extendReps Rs Γ)
tvMono-extendReps Rs Γ (α , d) =
  length Rs + α , shiftRVars-∋ (length Rs) d

-- A representation VARIABLE crosses a bind block by addition.
shiftRep-var : (k : ℕ) (α : ℕ) → shiftRep k (` α) ≡ ` (k + α)
shiftRep-var zero α = refl
shiftRep-var (suc k) α rewrite shiftRep-var k α = refl

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

binds-refine : RepRefines Ξ Ξ′ → Ξ ⊢ᴮ Rs → Ξ′ ⊢ᴮ Rs
binds-refine rr binds[] = binds[]
binds-refine rr (binds∷ w ws) =
  binds∷ (wfᴿ-refine rr w) (binds-refine rr ws)

push-refines : (Rs : List Ty) → RepRefines Ξ Ξ′
  → RepRefines (pushRepBinds Rs Ξ) (pushRepBinds Rs Ξ′)
push-refines [] rr = rr
push-refines (R ∷ Rs) rr = rr-bind (push-refines Rs rr)

valid-refine : RepRefines Ξ Ξ′ → Ξ ∋ʳ α → Ξ′ ∋ʳ α
valid-refine rr (S , d) = lookup-refine rr d

step-refine : RepRefines Ξ Ξ′ → Ξ ∣ η ⊢δ δ ⇒ η′
  → Ξ′ ∣ η ⊢δ δ ⇒ η′
step-refine rr (step-lock valid d fresh) =
  step-lock (valid-refine rr valid) d fresh
step-refine rr (step-unlock valid fresh i) =
  step-unlock (valid-refine rr valid) fresh i

changes-refine : RepRefines Ξ Ξ′ → Ξ ∣ η ⊢χ χ ⇒ η′
  → Ξ′ ∣ η ⊢χ χ ⇒ η′
changes-refine rr changes[] = changes[]
changes-refine rr (changes∷ cs st) =
  changes∷ (changes-refine rr cs) (step-refine rr st)

conv-changes-refine : RepRefines Ξ Ξ′ → Ξ ∣ η ⊢χᶜ χ ⇒ η′
  → Ξ′ ∣ η ⊢χᶜ χ ⇒ η′
conv-changes-refine rr conv[] = conv[]
conv-changes-refine rr (conv-lock valid cs) =
  conv-lock (valid-refine rr valid) (conv-changes-refine rr cs)
conv-changes-refine rr (conv-unlock valid cs fresh i) =
  conv-unlock (valid-refine rr valid) (conv-changes-refine rr cs) fresh i
conv-changes-refine rr (conv-unlock-live valid cs d) =
  conv-unlock-live (valid-refine rr valid) (conv-changes-refine rr cs) d

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

conv-refine : RepRefines Ξ Ξ′ → (Ξ ∣ η) ⊢ s ∶ A ⇝ B
  → (Ξ′ ∣ η) ⊢ s ∶ A ⇝ B
conv-refine rr (conv-id b) = conv-id b
conv-refine {Ξ = Ξ} {Ξ′ = Ξ′} rr (conv-idv tv) =
  conv-idv (tv-refine {Ξ = Ξ} {Ξ′ = Ξ′} tv)
conv-refine rr (conv-unseal d) =
  conv-unseal (lookup-square-refine rr d)
conv-refine rr (conv-seal d) = conv-seal (lookup-square-refine rr d)
conv-refine rr (conv-fun p q) =
  conv-fun (conv-refine rr p) (conv-refine rr q)
conv-refine rr (conv-all p) = conv-all (conv-refine (rr-abst rr) p)

interior-refine : ∀ {Θ : Boundary} → RepRefines Ξ Ξ′
  → (Ξ ∣ η) ⊢ⁱ Θ ⇒ Ω
  → (Ξ′ ∣ η) ⊢ⁱ Θ ⇒
      (pushRepBinds (binds Θ) Ξ′ ∣ names Ω)
interior-refine {Θ = boundary Rs χ} rr (interior cs) =
  interior (changes-refine (push-refines Rs rr) cs)

conversion-refine : ∀ {Θ : Boundary} → RepRefines Ξ Ξ′
  → (Ξ ∣ η) ⊢ᶜ Θ ⇒ Ω
  → (Ξ′ ∣ η) ⊢ᶜ Θ ⇒
      (pushRepBinds (binds Θ) Ξ′ ∣ names Ω)
conversion-refine {Θ = boundary Rs χ} rr (conversion cs) =
  conversion (conv-changes-refine (push-refines Rs rr) cs)

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
                       (zero ∷ shiftNames (names Δ₀))
    valid here = abstR , here
    valid (there d) with shiftNames-∋⁻ d
    valid (there d) | α , refl , d′ with vn d′
    valid (there d) | α , refl , d′ | b , db = b , there db
⊢refine rr w′ (⊢·[] ⊢L w) =
  ⊢·[] (⊢refine rr w′ ⊢L) (wf-refine rr w)
⊢refine {Ξ = Ξ} {Ξ′ = Ξ′} {η = η} rr w′
        (env {Θ = boundary Rs χ}
             (bw w bs (interior cs) (conversion csᶜ))
             ⊢M ⊢c sameᵢ sameₑ wE) =
  env mw′
      (⊢refine (push-refines Rs rr) (bw-interior-wf mw′) ⊢M)
      (conv-refine (push-refines Rs rr) ⊢c)
      sameᵢ sameₑ (wf-refine rr wE)
  where
  mw′ : BoundaryWf (Ξ′ ∣ η) (boundary Rs χ)
          (pushRepBinds Rs Ξ′ ∣ _)
          (pushRepBinds Rs Ξ′ ∣ _)
  mw′ =
    bw w′ (binds-refine rr bs)
       (interior (changes-refine (push-refines Rs rr) cs))
       (conversion (conv-changes-refine (push-refines Rs rr) csᶜ))

------------------------------------------------------------------------
-- §2. The conversion TyBeta mints
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
  trans (subst-cong env-eq B)
        (sym (rename-subst suc (singleTyEnv A) B))
  where
  env-eq : (Y : ℕ)
    → single-at 0 (⇑ᵗ A) Y ≡ renameᵗ suc (singleTyEnv A Y)
  env-eq zero = refl
  env-eq (suc Y) = refl

underNames : ℕ → TyCtx → TyCtx
underNames zero η = η
underNames (suc n) η = zero ∷ shiftNames (underNames n η)

underNames-weaken : ∀ {η X α} (n : ℕ)
  → underNames n η ∋ˡ X := α
  → underNames n (zero ∷ shiftNames η)
      ∋ˡ extN n suc X := extN n suc α
underNames-weaken zero d = there (shiftNames-∋ d)
underNames-weaken (suc n) here = here
underNames-weaken (suc n) (there d) with shiftNames-∋⁻ d
underNames-weaken (suc n) (there d) | β , refl , d′ =
  there (shiftNames-∋ (underNames-weaken n d′))

same-weaken-at : ∀ {η A R} (n : ℕ) → underNames n η ⊢ A ~ R
  → underNames n (zero ∷ shiftNames η)
      ⊢ renameᵗ (extN n suc) A ~ renameᵗ (extN n suc) R
same-weaken-at n (same-var d) = same-var (underNames-weaken n d)
same-weaken-at n same-ℕ = same-ℕ
same-weaken-at n same-𝔹 = same-𝔹
same-weaken-at n (same-⇒ p q) =
  same-⇒ (same-weaken-at n p) (same-weaken-at n q)
same-weaken-at n (same-∀ p) = same-∀ (same-weaken-at (suc n) p)

same-weaken : η ⊢ A ~ R → (zero ∷ shiftNames η) ⊢ ⇑ᵗ A ~ ⇑ᵗ R
same-weaken = same-weaken-at zero

-- Eliminating an ordinary `∀` binder commutes with the representation
-- reading.  Both sides substitute the readings of the same argument.
SameSub : TyCtx → TyCtx → Substᵗ → Substᵗ → Set
SameSub η η′ σ τ = ∀ {X α}
  → η ∋ˡ X := α
  → η′ ⊢ σ X ~ τ α

SameSub-ext : ∀ {σ τ} → SameSub η η′ σ τ
  → SameSub (zero ∷ shiftNames η) (zero ∷ shiftNames η′)
            (extsᵗ σ) (extsᵗ τ)
SameSub-ext h here = same-var here
SameSub-ext h (there d) with shiftNames-∋⁻ d
SameSub-ext h (there d) | α , refl , d′ = same-weaken (h d′)

same-subst : ∀ {σ τ} → SameSub η η′ σ τ → η ⊢ A ~ R
  → η′ ⊢ substᵗ σ A ~ substᵗ τ R
same-subst h (same-var d) = h d
same-subst h same-ℕ = same-ℕ
same-subst h same-𝔹 = same-𝔹
same-subst h (same-⇒ p q) = same-⇒ (same-subst h p) (same-subst h q)
same-subst h (same-∀ p) = same-∀ (same-subst (SameSub-ext h) p)

same-[] : (zero ∷ shiftNames η) ⊢ B ~ S → η ⊢ A ~ R
  → η ⊢ B [ A ]ᵗ ~ S [ R ]ᵗ
same-[] {A = A} {R = R} p q = same-subst h p
  where
  h : SameSub (zero ∷ shiftNames _) _ (singleTyEnv A) (singleTyEnv R)
  h here = q
  h (there d) with shiftNames-∋⁻ d
  h (there d) | α , refl , d′ = same-var d′

-- Shift only the FREE representation names while leaving the ordinary
-- spelling in place.  The depth parameter accounts for local `∀` names.
underNames-shift-free : ∀ {η X α} (n : ℕ)
  → underNames n η ∋ˡ X := α
  → underNames n (shiftNames η) ∋ˡ X := extN n suc α
underNames-shift-free zero d = shiftNames-∋ d
underNames-shift-free (suc n) here = here
underNames-shift-free (suc n) (there d) with shiftNames-∋⁻ d
underNames-shift-free (suc n) (there d) | α , refl , d′ =
  there (shiftNames-∋ (underNames-shift-free n d′))

same-shift-free-at : ∀ {η A R} (n : ℕ) → underNames n η ⊢ A ~ R
  → underNames n (shiftNames η)
      ⊢ A ~ renameᵗ (extN n suc) R
same-shift-free-at n (same-var d) =
  same-var (underNames-shift-free n d)
same-shift-free-at n same-ℕ = same-ℕ
same-shift-free-at n same-𝔹 = same-𝔹
same-shift-free-at n (same-⇒ p q) =
  same-⇒ (same-shift-free-at n p) (same-shift-free-at n q)
same-shift-free-at n (same-∀ p) = same-∀ (same-shift-free-at (suc n) p)

same-shift-free : η ⊢ A ~ R → shiftNames η ⊢ A ~ ⇑ᵗ R
same-shift-free = same-shift-free-at zero

shiftRVars-suc′ : (n : ℕ) (η : TyCtx)
  → shiftRVars (suc n) η ≡ shiftNames (shiftRVars n η)
shiftRVars-suc′ n [] = refl
shiftRVars-suc′ n (α ∷ η) =
  cong (suc (n + α) ∷_) (shiftRVars-suc′ n η)

same-shiftRVars : (n : ℕ) → η ⊢ A ~ R
  → shiftRVars n η ⊢ A ~ shiftBy n R
same-shiftRVars { η = η } zero p =
  subst ( _⊢ _ ~ _) (sym (shiftRVars-0 η)) p
same-shiftRVars {η = η} (suc n) p =
  subst (_⊢ _ ~ _) (sym (shiftRVars-suc′ n η))
        (same-shift-free (same-shiftRVars n p))

underNames-ref : ∀ {η X α} (n : ℕ) → ValidNames Ξ η
  → underNames n η ∋ˡ X := α → Ξ ⊢ref[ n ] α
underNames-ref zero valid d with valid d
underNames-ref zero valid d | b , db = free-ref db
underNames-ref (suc n) valid here = local-ref (s≤s z≤n)
underNames-ref (suc n) valid (there d) with shiftNames-∋⁻ d
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
  → WfCtx ((bindR R ∷ reps Δ) ∣ (zero ∷ shiftNames (names Δ)))
represented-wf {Δ = Δ} {R = R} w p =
  wf-ctx (wf-bindR (same-wfᴿ w p) (wf-reps w)) valid
         (unique-underΛ {Γ = Δ} (name-fn w))
  where
  valid : ValidNames (bindR R ∷ reps Δ)
                     (zero ∷ shiftNames (names Δ))
  valid here = bindR R , here
  valid (there d) with shiftNames-∋⁻ d
  valid (there d) | α , refl , d′ with wf-names w d′
  valid (there d) | α , refl , d′ | b , db = b , there db

-- THE INSTANTIATED FRAME IS AGAIN A BOUNDARY SCOPE WITNESS.  `TyBeta` and both
-- `TyPeelR` clauses replace the abstract binder the `∀` conversion was read
-- under by a REPRESENTED one carrying the type argument's representation,
-- and append `unlock 0 0`.  The bind block therefore grows by exactly that
-- representation — well formed because `same-wfᴿ` reads it off the
-- argument's `~` — and the two readings are `instantiate-interior` and
-- `instantiate-conversion`.  `preserve-TyPeelR-⟪⟫` uses it for the moved
-- boundary's exterior; `strong-rep-store.proof.Progress.addLock0-reading` uses
-- it for
-- the `RepWk suc` that the same insertion induces.
instantiate-boundarywf : ∀ {Δ Δᵢ Δᶜ Θ A R}
  → BoundaryWf Δ Θ Δᵢ Δᶜ
  → names Δ ⊢ A ~ R
  → BoundaryWf Δ (instantiate R Θ)
      ((bindR (shiftBy (numBinds Θ) R) ∷ reps Δᵢ)
        ∣ (zero ∷ shiftNames (names Δᵢ)))
      ((bindR (shiftBy (numBinds Θ) R) ∷ reps Δᶜ)
        ∣ (zero ∷ shiftNames (names Δᶜ)))
instantiate-boundarywf mwΘ p =
  bw (bw-exterior mwΘ)
     (binds∷ (same-wfᴿ (bw-exterior mwΘ) p) (bw-binds mwΘ))
     (instantiate-interior (bw-interior mwΘ))
     (instantiate-conversion (bw-conversion mwΘ))

represented-lookup : names Δ ⊢ A ~ R
  → ((bindR R ∷ reps Δ) ∣ (zero ∷ shiftNames (names Δ)))
      ∋ zero := ⇑ᵗ A
represented-lookup {R = R} p =
  zero , ⇑ᵗ R , here , r-here , same-weaken p

lookup-underΛ : Δ ∋ X := A → underΛ Δ ∋ suc X := ⇑ᵗ A
lookup-underΛ (α , R , name , rep , same) =
  suc α , ⇑ᵗ R , there (shiftNames-∋ name) , r-there-abst rep ,
  same-weaken same

reveal-hit : (X : ℕ) → reveal X (` X) ≡ unseal X
reveal-hit X with X ≟ X
reveal-hit X | yes _ = refl
reveal-hit X | no ne = ⊥-elim (ne refl)

reveal-miss : (X Y : ℕ) → X ≢ Y → reveal X (` Y) ≡ id (` Y)
reveal-miss X Y ne with X ≟ Y
reveal-miss X Y ne | yes eq = ⊥-elim (ne eq)
reveal-miss X Y ne | no _ = refl

conceal-hit : (X : ℕ) → conceal X (` X) ≡ seal X
conceal-hit X with X ≟ X
conceal-hit X | yes _ = refl
conceal-hit X | no ne = ⊥-elim (ne refl)

conceal-miss : (X Y : ℕ) → X ≢ Y → conceal X (` Y) ≡ id (` Y)
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
    rewrite reveal-miss X Y ne | single-at-miss X Y A ne = conv-idv tv
  ⊢reveal d wf-ℕ = conv-id base-ℕ
  ⊢reveal d wf-𝔹 = conv-id base-𝔹
  ⊢reveal d (wf-⇒ wA wB) = conv-fun (⊢conceal d wA) (⊢reveal d wB)
  ⊢reveal {X = X} {A = A} {B = `∀ B} d (wf-∀ wB)
    rewrite subst-at-∀ X A B = conv-all (⊢reveal (lookup-underΛ d) wB)

  ⊢conceal : Δ ∋ X := A → Δ ⊢ᵗ B
    → Δ ⊢ conceal X B ∶ B [ X := A ]ᵗ ⇝ B
  ⊢conceal {X = X} {A = A} {B = ` Y} d (wf-var tv) with X ≟ℕ Y
  ⊢conceal {X = X} {A = A} {B = ` Y} d (wf-var tv) | yes refl
    rewrite conceal-hit X | single-at-hit X A = conv-seal d
  ⊢conceal {X = X} {A = A} {B = ` Y} d (wf-var tv) | no ne
    rewrite conceal-miss X Y ne | single-at-miss X Y A ne = conv-idv tv
  ⊢conceal d wf-ℕ = conv-id base-ℕ
  ⊢conceal d wf-𝔹 = conv-id base-𝔹
  ⊢conceal d (wf-⇒ wA wB) = conv-fun (⊢reveal d wA) (⊢conceal d wB)
  ⊢conceal {X = X} {A = A} {B = `∀ B} d (wf-∀ wB)
    rewrite subst-at-∀ X A B = conv-all (⊢conceal (lookup-underΛ d) wB)

------------------------------------------------------------------------
-- §2b. The conversion TyPeelR mints
------------------------------------------------------------------------

underΛN : ℕ → Ctxᵗ → Ctxᵗ
underΛN zero Δ = Δ
underΛN (suc n) Δ = underΛ (underΛN n Δ)

rr-refl : RepRefines Ξ Ξ
rr-refl {Ξ = []} = rr[]
rr-refl {Ξ = abstR ∷ Ξ} = rr-abst rr-refl
rr-refl {Ξ = bindR R ∷ Ξ} = rr-bind rr-refl

abstract-represent-refines : (n : ℕ)
  → RepRefines (reps (underΛN n (underΛ Δ)))
      (reps (underΛN n
        ((bindR R ∷ reps Δ) ∣ (zero ∷ shiftNames (names Δ)))))
abstract-represent-refines zero = rr-represent rr-refl
abstract-represent-refines (suc n) =
  rr-abst (abstract-represent-refines n)

abstract-represent-names : ∀ {Δ R} (n : ℕ)
  → names (underΛN n (underΛ Δ))
    ≡ names (underΛN n
        ((bindR R ∷ reps Δ) ∣ (zero ∷ shiftNames (names Δ))))
abstract-represent-names zero = refl
abstract-represent-names (suc n) =
  cong (λ η → zero ∷ shiftNames η) (abstract-represent-names n)

tv-abstract-represent : ∀ {Δ R X} (n : ℕ)
  → underΛN n (underΛ Δ) ∋tv X
  → underΛN n ((bindR R ∷ reps Δ)
                   ∣ (zero ∷ shiftNames (names Δ))) ∋tv X
tv-abstract-represent n (α , name) =
  α , subst (λ η → η ∋ˡ _ := α) (abstract-represent-names n) name

lookup-abstract-represent : ∀ {Δ R X A} (n : ℕ)
  → underΛN n (underΛ Δ) ∋ X := A
  → underΛN n ((bindR R ∷ reps Δ)
                   ∣ (zero ∷ shiftNames (names Δ))) ∋ X := A
lookup-abstract-represent {Δ = Δ} {R = R} {A = A} n
                          (α , S , name , rep , same) =
  α , S
    , subst (λ η → η ∋ˡ _ := α) eq name
    , rep-lookup-refine (abstract-represent-refines n) rep refl
    , subst (λ η → η ⊢ A ~ S) eq same
  where
  eq = abstract-represent-names {Δ = Δ} {R = R} n

data Avoid (n : ℕ) : Ty → Set where
  avoid-var : n ≢ X → Avoid n (` X)
  avoid-ℕ   : Avoid n `ℕ
  avoid-𝔹   : Avoid n `𝔹
  avoid-⇒   : Avoid n A → Avoid n B → Avoid n (A ⇒ B)
  avoid-∀   : Avoid (suc n) A → Avoid n (`∀ A)

extN-avoid : (n X : ℕ) → n ≢ extN n suc X
extN-avoid zero X ()
extN-avoid (suc n) zero ()
extN-avoid (suc n) (suc X) eq = extN-avoid n X (suc-injective eq)

avoid-insert : (n : ℕ) (A : Ty) → Avoid n (renameᵗ (extN n suc) A)
avoid-insert n (` X) = avoid-var (extN-avoid n X)
avoid-insert n `ℕ = avoid-ℕ
avoid-insert n `𝔹 = avoid-𝔹
avoid-insert n (A ⇒ B) = avoid-⇒ (avoid-insert n A) (avoid-insert n B)
avoid-insert n (`∀ A) = avoid-∀ (avoid-insert (suc n) A)

extN-injective : (k : ℕ) {X Y : ℕ}
  → extN k suc X ≡ extN k suc Y → X ≡ Y
extN-injective zero eq = suc-injective eq
extN-injective (suc k) {zero} {zero} eq = refl
extN-injective (suc k) {zero} {suc Y} ()
extN-injective (suc k) {suc X} {zero} ()
extN-injective (suc k) {suc X} {suc Y} eq =
  cong suc (extN-injective k (suc-injective eq))

avoid-weaken-at : (k : ℕ) → Avoid n A
  → Avoid (extN k suc n) (renameᵗ (extN k suc) A)
avoid-weaken-at k (avoid-var ne) =
  avoid-var (λ eq → ne (extN-injective k eq))
avoid-weaken-at k avoid-ℕ = avoid-ℕ
avoid-weaken-at k avoid-𝔹 = avoid-𝔹
avoid-weaken-at k (avoid-⇒ p q) =
  avoid-⇒ (avoid-weaken-at k p) (avoid-weaken-at k q)
avoid-weaken-at k (avoid-∀ p) = avoid-∀ (avoid-weaken-at (suc k) p)

avoid-weaken : Avoid n A → Avoid (suc n) (⇑ᵗ A)
avoid-weaken = avoid-weaken-at zero

avoid-subst : Avoid X A → A [ X := B ]ᵗ ≡ A
avoid-subst {X = X} {A = ` Y} (avoid-var ne) =
  single-at-miss X Y _ ne
avoid-subst avoid-ℕ = refl
avoid-subst avoid-𝔹 = refl
avoid-subst (avoid-⇒ p q) = cong₂ _⇒_ (avoid-subst p) (avoid-subst q)
avoid-subst {X = X} {B = B} (avoid-∀ {A = A} p) =
  trans (subst-at-∀ X B A) (cong `∀ (avoid-subst p))

-- Looking up a represented payload past an abstract prefix always weakens it
-- past the distinguished abstract binder, so the returned payload avoids the
-- distinguished representation index.
abstract-rep-avoid : ∀ {Δ α b R} (n : ℕ)
  → reps (underΛN n (underΛ Δ)) ∋ʳ α := b
  → b ≡ bindR R → Avoid n R
abstract-rep-avoid zero r-here ()
abstract-rep-avoid zero (r-there-abst {b = abstR} d) ()
abstract-rep-avoid zero (r-there-abst {b = bindR S} d) refl =
  avoid-insert zero S
abstract-rep-avoid (suc n) r-here ()
abstract-rep-avoid (suc n) (r-there-abst {b = abstR} d) ()
abstract-rep-avoid (suc n) (r-there-abst {b = bindR S} d) refl =
  avoid-weaken (abstract-rep-avoid n d refl)

abstract-no-bind : ∀ {Δ b R} (n : ℕ)
  → reps (underΛN n (underΛ Δ)) ∋ʳ n := b
  → b ≡ bindR R → ⊥
abstract-no-bind zero r-here ()
abstract-no-bind (suc n) (r-there-abst {b = abstR} d) ()
abstract-no-bind {Δ = Δ} (suc n)
                 (r-there-abst {b = bindR S} d) refl =
  abstract-no-bind {Δ = Δ} n d refl

abstract-name : (n : ℕ)
  → names (underΛN n (underΛ Δ)) ∋ˡ n := n
abstract-name zero = here
abstract-name (suc n) = there (shiftNames-∋ (abstract-name n))

same-avoid : η ∋ˡ X := X → η ⊢ A ~ R → Avoid X R → Avoid X A
same-avoid self (same-var d) (avoid-var ne) =
  avoid-var (λ { refl → ne (∋ˡ-det self d) })
same-avoid self same-ℕ avoid-ℕ = avoid-ℕ
same-avoid self same-𝔹 avoid-𝔹 = avoid-𝔹
same-avoid self (same-⇒ p q) (avoid-⇒ r s) =
  avoid-⇒ (same-avoid self p r) (same-avoid self q s)
same-avoid self (same-∀ p) (avoid-∀ r) =
  avoid-∀ (same-avoid (there (shiftNames-∋ self)) p r)

abstract-lookup-fixed : ∀ {Δ X A} (n : ℕ)
  → underΛN n (underΛ Δ) ∋ X := A
  → A [ n := B ]ᵗ ≡ A
abstract-lookup-fixed n (α , R , name , rep , same) =
  avoid-subst
    (same-avoid (abstract-name n) same (abstract-rep-avoid n rep refl))

abstract-index-≢ : ∀ {Δ X A} (n : ℕ)
  → underΛN n (underΛ Δ) ∋ X := A → n ≢ X
abstract-index-≢ {Δ = Δ} n (α , R , name , rep , same) refl
  with ∋ˡ-det (abstract-name n) name
abstract-index-≢ {Δ = Δ} n (α , R , name , rep , same) refl | refl =
  abstract-no-bind {Δ = Δ} n rep refl

represented-binder : ∀ {Δ A R} (n : ℕ) → names Δ ⊢ A ~ R
  → underΛN n ((bindR R ∷ reps Δ)
                   ∣ (zero ∷ shiftNames (names Δ)))
      ∋ n := shiftBy (suc n) A
represented-binder zero p = represented-lookup p
represented-binder (suc n) p = lookup-underΛ (represented-binder n p)

mutual
  ⊢instReveal : ∀ {Δ A R s Bᵢ Bₑ} (n : ℕ)
    → names Δ ⊢ A ~ R
    → underΛN n (underΛ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
    → underΛN n ((bindR R ∷ reps Δ)
                    ∣ (zero ∷ shiftNames (names Δ)))
        ⊢ instReveal n s
        ∶ Bᵢ ⇝ Bₑ [ n := shiftBy (suc n) A ]ᵗ
  ⊢instReveal n p (conv-id base-ℕ) = conv-id base-ℕ
  ⊢instReveal n p (conv-id base-𝔹) = conv-id base-𝔹
  ⊢instReveal {A = A} n p (conv-idv {X = Y} tv) with n ≟ℕ Y
  ⊢instReveal {A = A} n p (conv-idv {X = Y} tv) | yes refl
    rewrite reveal-hit n | single-at-hit n (shiftBy (suc n) A) =
      conv-unseal (represented-binder n p)
  ⊢instReveal {A = A} n p
                (conv-idv {X = Y} tv) | no ne
    rewrite reveal-miss n Y ne
          | single-at-miss n Y (shiftBy (suc n) A) ne =
      conv-idv (tv-abstract-represent n tv)
  ⊢instReveal {Δ = Δ} {A = A} {R = R} n p (conv-unseal d)
    rewrite abstract-lookup-fixed {B = shiftBy (suc n) A} n d =
      conv-unseal (lookup-abstract-represent n d)
  ⊢instReveal {Δ = Δ} {A = A} {R = R} n p
                (conv-seal {X = Y} d)
    rewrite single-at-miss n Y (shiftBy (suc n) A)
              (abstract-index-≢ n d) =
      conv-seal (lookup-abstract-represent n d)
  ⊢instReveal n p (conv-fun ⊢s ⊢t) =
    conv-fun (⊢instConceal n p ⊢s) (⊢instReveal n p ⊢t)
  ⊢instReveal {A = A} {Bₑ = `∀ Bₑ} n p (conv-all ⊢s)
    rewrite subst-at-∀ n (shiftBy (suc n) A) Bₑ =
      conv-all (⊢instReveal (suc n) p ⊢s)

  ⊢instConceal : ∀ {Δ A R s Bᵢ Bₑ} (n : ℕ)
    → names Δ ⊢ A ~ R
    → underΛN n (underΛ Δ) ⊢ s ∶ Bᵢ ⇝ Bₑ
    → underΛN n ((bindR R ∷ reps Δ)
                    ∣ (zero ∷ shiftNames (names Δ)))
        ⊢ instConceal n s
        ∶ Bᵢ [ n := shiftBy (suc n) A ]ᵗ ⇝ Bₑ
  ⊢instConceal n p (conv-id base-ℕ) = conv-id base-ℕ
  ⊢instConceal n p (conv-id base-𝔹) = conv-id base-𝔹
  ⊢instConceal {A = A} n p
                 (conv-idv {X = Y} tv) with n ≟ℕ Y
  ⊢instConceal {A = A} n p
                 (conv-idv {X = Y} tv) | yes refl
    rewrite conceal-hit n | single-at-hit n (shiftBy (suc n) A) =
      conv-seal (represented-binder n p)
  ⊢instConceal {A = A} n p
                 (conv-idv {X = Y} tv) | no ne
    rewrite conceal-miss n Y ne
          | single-at-miss n Y (shiftBy (suc n) A) ne =
      conv-idv (tv-abstract-represent n tv)
  ⊢instConceal {Δ = Δ} {A = A} {R = R} n p (conv-seal d)
    rewrite abstract-lookup-fixed {B = shiftBy (suc n) A} n d =
      conv-seal (lookup-abstract-represent n d)
  ⊢instConceal {Δ = Δ} {A = A} {R = R} n p
                 (conv-unseal {X = Y} d)
    rewrite single-at-miss n Y (shiftBy (suc n) A)
              (abstract-index-≢ n d) =
      conv-unseal (lookup-abstract-represent n d)
  ⊢instConceal n p (conv-fun ⊢s ⊢t) =
    conv-fun (⊢instReveal n p ⊢s) (⊢instConceal n p ⊢t)
  ⊢instConceal {A = A} {Bᵢ = `∀ Bᵢ} n p (conv-all ⊢s)
    rewrite subst-at-∀ n (shiftBy (suc n) A) Bᵢ =
      conv-all (⊢instConceal (suc n) p ⊢s)

------------------------------------------------------------------------
-- §3. The local reduction cases
------------------------------------------------------------------------

empty-interior : Δ ⊢ⁱ boundary [] [] ⇒ Δ
empty-interior {Δ = Ξ ∣ η} =
  interior
    (subst (λ η′ → Ξ ∣ η′ ⊢χ [] ⇒ η)
           (sym (shiftRVars-0 η)) changes[])

empty-conversion : Δ ⊢ᶜ boundary [] [] ⇒ Δ
empty-conversion {Δ = Ξ ∣ η} =
  conversion
    (subst (λ η′ → Ξ ∣ η′ ⊢χᶜ [] ⇒ η)
           (sym (shiftRVars-0 η)) conv[])

shiftBodyBy : ℕ → Ty → Ty
shiftBodyBy zero B = B
shiftBodyBy (suc n) B = renameᵗ (extᵗ suc) (shiftBodyBy n B)

shiftBy-∀ : (n : ℕ) (B : Ty)
  → shiftBy n (`∀ B) ≡ `∀ (shiftBodyBy n B)
shiftBy-∀ zero B = refl
shiftBy-∀ (suc n) B rewrite shiftBy-∀ n B = refl

shiftRep-shiftBy : (n : ℕ) (R : Ty) → shiftRep n R ≡ shiftBy n R
shiftRep-shiftBy zero R = refl
shiftRep-shiftBy (suc n) R = cong ⇑ᵗ (shiftRep-shiftBy n R)

shiftBy-[]ᵗ : (n : ℕ) (B A : Ty)
  → shiftBy n (B [ A ]ᵗ)
    ≡ (shiftBodyBy n B) [ shiftBy n A ]ᵗ
shiftBy-[]ᵗ zero B A = refl
shiftBy-[]ᵗ (suc n) B A =
  trans (cong ⇑ᵗ (shiftBy-[]ᵗ n B A))
        (rename-[]ᵗ-commute suc (shiftBodyBy n B) (shiftBy n A))

sameTy-∀⁻ : ∀ {η η′ A B}
  → ∃[ R ] ((η ⊢ `∀ A ~ R) × (η′ ⊢ `∀ B ~ R))
  → ∃[ R ] (((zero ∷ shiftNames η) ⊢ A ~ R) ×
             ((zero ∷ shiftNames η′) ⊢ B ~ R))
sameTy-∀⁻ (`∀ R , same-∀ p , same-∀ q) = R , p , q

sameTy-target-∀⁻ : ∀ {η η′ A B}
  → ∃[ R ] ((η ⊢ A ~ R) × (η′ ⊢ `∀ B ~ R))
  → Σ[ A₀ ∈ Ty ] ((A ≡ `∀ A₀) ×
       (∃[ R ] (((zero ∷ shiftNames η) ⊢ A₀ ~ R) ×
          ((zero ∷ shiftNames η′) ⊢ B ~ R))))
sameTy-target-∀⁻ (`∀ R , same-∀ p , same-∀ q) =
  _ , refl , (R , p , q)

sameTyExt-∀⁻ : ∀ {n η η′ A B}
  → ∃[ R ] ((η ⊢ `∀ A ~ R) ×
       (η′ ⊢ `∀ B ~ shiftRep n R))
  → ∃[ R ] (((zero ∷ shiftNames η) ⊢ A ~ R) ×
       ((zero ∷ shiftNames η′) ⊢ B ~ shiftBodyBy n R))
sameTyExt-∀⁻ {n = n} (`∀ R , same-∀ p , q)
  rewrite shiftRep-shiftBy n (`∀ R) | shiftBy-∀ n R
  with q
sameTyExt-∀⁻ {n = n} (`∀ R , same-∀ p , q)
  | same-∀ q′ = R , p , q′

wf-∀⁻ : Δ ⊢ᵗ `∀ A → underΛ Δ ⊢ᵗ A
wf-∀⁻ (wf-∀ w) = w

preserve-TyBeta : ∀ {Δ N B A R C}
  → WfCtx Δ
  → Δ ⊢ᶜ A ~ R
  → Δ ∣ [] ⊢ (Λ N) ·[ B , A ] ⦂ C
  → Δ ∣ [] ⊢ N ⟪ instantiate R (boundary [] []) , reveal 0 B ⟫ ⦂ C
preserve-TyBeta {Δ = Δ} {N = N} {B = B} {A = A} {R = R}
                wfΔ p (⊢·[] (⊢Λ vN ⊢N) wA)
  with ⊢ᵗ-of CtxWf-[] (⊢Λ vN ⊢N)
preserve-TyBeta {Δ = Δ} {N = N} {B = B} {A = A} {R = R}
                wfΔ p (⊢·[] (⊢Λ vN ⊢N) wA) | wf-∀ wB =
  env mwβ inner conv sameᵢ sameₑ wE
  where
  ΔR : Ctxᵗ
  ΔR = (bindR R ∷ reps Δ) ∣ (zero ∷ shiftNames (names Δ))

  wfΔR : WfCtx ΔR
  wfΔR = represented-wf wfΔ p

  refine : RepRefines (reps (underΛ Δ)) (reps ΔR)
  refine = rr-represent rr-refl

  inner : ΔR ∣ [] ⊢ N ⦂ B
  inner = ⊢refine refine wfΔR ⊢N

  conv : ΔR ⊢ reveal 0 B ∶ B ⇝ ⇑ᵗ (B [ A ]ᵗ)
  conv rewrite sym (subst-at-0 A B) =
    ⊢reveal (represented-lookup p) (wf-refine refine wB)

  sameᵢ : ΔR ⊢ B ≈ B ⊣ ΔR
  sameᵢ with wf-same (wf-refine refine wB)
  sameᵢ | S , q = S , q , q

  wE : Δ ⊢ᵗ B [ A ]ᵗ
  wE = wf-[]ᵗ wB wA

  sameₑ : SameTyExt 1 Δ (B [ A ]ᵗ) ΔR (⇑ᵗ (B [ A ]ᵗ))
  sameₑ with wf-same wE
  sameₑ | S , q = S , q , same-weaken q

  mwβ : BoundaryWf Δ (instantiate R (boundary [] [])) ΔR ΔR
  mwβ =
    bw wfΔ (binds∷ (same-wfᴿ wfΔ p) binds[])
       (instantiate-interior {R = R} empty-interior)
       (instantiate-conversion {R = R} empty-conversion)

preserve-TyPeelR-Λ : ∀ {Δ Δᶜ N Θ s B A R Bᵢ Bₑ C}
  → WfCtx Δ
  → Value N
  → Δ ⊢ᶜ Θ ⇒ Δᶜ
  → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
  → Δ ⊢ᶜ A ~ R
  → Δ ∣ [] ⊢ ((Λ N) ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
  → Δ ∣ [] ⊢ N ⟪ instantiate R Θ , instReveal 0 s ⟫ ⦂ C
preserve-TyPeelR-Λ {Δ = Δ} {Δᶜ = Δᶜ} {N = N} {Θ = Θ} {s = s}
                    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bₑ = Bₑ}
                    wfΔ v rc ⊢s p
                    (⊢·[] (env {Δᵢ = Δᵢ} mwΘ (⊢Λ _ ⊢N)
                                 ⊢c sameᵢ sameₑ wE) wA)
  with conversion-functional rc (bw-conversion mwΘ)
preserve-TyPeelR-Λ {Δ = Δ} {Δᶜ = Δᶜ} {N = N} {Θ = Θ} {s = s}
                    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bₑ = Bₑ}
                    wfΔ v rc ⊢s p
                    (⊢·[] (env {Δᵢ = Δᵢ} mwΘ (⊢Λ _ ⊢N)
                                 ⊢c sameᵢ sameₑ wE) wA)
  | refl with conv-all-inv ⊢c
preserve-TyPeelR-Λ {Δ = Δ} {Δᶜ = Δᶜ} {N = N} {Θ = Θ} {s = s}
                    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bₑ = Bₑ}
                    wfΔ v rc ⊢s p
                    (⊢·[] (env {Δᵢ = Δᵢ} mwΘ (⊢Λ _ ⊢N)
                                 ⊢c sameᵢ sameₑ wE) wA)
  | refl | A₀ , B₀ , refl , refl , ⊢s₀
  with conv-types-unique
         (unique-underΛ {Γ = Δᶜ} (name-fn (bw-conversion-wf mwΘ)))
         ⊢s ⊢s₀
preserve-TyPeelR-Λ {Δ = Δ} {Δᶜ = Δᶜ} {N = N} {Θ = Θ} {s = s}
                    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bₑ = Bₑ}
                    wfΔ v rc ⊢s p
                    (⊢·[] (env {Δᵢ = Δᵢ} mwΘ (⊢Λ _ ⊢N)
                                 ⊢c sameᵢ sameₑ wE) wA)
  | refl | A₀ , B₀ , refl , refl , ⊢s₀ | refl , refl
  with respell-ty (conversion-live rc) (same-shiftRVars (numBinds Θ) p)
preserve-TyPeelR-Λ {Δ = Δ} {Δᶜ = Δᶜ} {N = N} {Θ = Θ} {s = s}
                    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bₑ = Bₑ}
                    wfΔ v rc ⊢s p
                    (⊢·[] (env {Δᵢ = Δᵢ} mwΘ (⊢Λ _ ⊢N)
                                 ⊢c sameᵢ sameₑ wE) wA)
  | refl | A₀ , B₀ , refl , refl , ⊢s₀ | refl , refl | Aᶜ , pᶜ =
  env mwᵢ inner conv sameᵢ′ sameₑ′ wFinal
  where
  k : ℕ
  k = numBinds Θ

  ΔRᵢ : Ctxᵗ
  ΔRᵢ = (bindR (shiftBy k R) ∷ reps Δᵢ)
          ∣ (zero ∷ shiftNames (names Δᵢ))

  ΔRᶜ : Ctxᵗ
  ΔRᶜ = (bindR (shiftBy k R) ∷ reps Δᶜ)
          ∣ (zero ∷ shiftNames (names Δᶜ))

  mwᵢ : BoundaryWf Δ (instantiate R Θ) ΔRᵢ ΔRᶜ
  mwᵢ = instantiate-boundarywf mwΘ p

  inner = ⊢refine (rr-represent rr-refl) (bw-interior-wf mwᵢ) ⊢N

  conv = ⊢instReveal 0 pᶜ ⊢s

  sameᵢ′ : ΔRᵢ ⊢ _ ≈ Bᵢ ⊣ ΔRᶜ
  sameᵢ′ = sameTy-∀⁻ sameᵢ

  wFinal = wf-[]ᵗ (wf-∀⁻ wE) wA

  sameₑ′ : SameTyExt (suc k) Δ (B [ A ]ᵗ) ΔRᶜ
                         (Bₑ [ 0 := ⇑ᵗ Aᶜ ]ᵗ)
  sameₑ′ with sameTyExt-∀⁻ {n = k} sameₑ
  sameₑ′ | S , pB , pBₑ = S [ R ]ᵗ , same-[] pB p , target
    where
    target : names ΔRᶜ ⊢ Bₑ [ 0 := ⇑ᵗ Aᶜ ]ᵗ
               ~ shiftRep (suc k) (S [ R ]ᵗ)
    target rewrite subst-at-0 Aᶜ Bₑ
                 | shiftRep-shiftBy (suc k) (S [ R ]ᵗ)
                 | shiftBy-[]ᵗ k S R =
      same-weaken (same-[] pBₑ pᶜ)

ren-ℕ⁻ : renameᵗ ρ A ≡ `ℕ → A ≡ `ℕ
ren-ℕ⁻ {A = ` X} ()
ren-ℕ⁻ {A = `ℕ} refl = refl
ren-ℕ⁻ {A = `𝔹} ()
ren-ℕ⁻ {A = A ⇒ B} ()
ren-ℕ⁻ {A = `∀ A} ()

ren-𝔹⁻ : renameᵗ ρ A ≡ `𝔹 → A ≡ `𝔹
ren-𝔹⁻ {A = ` X} ()
ren-𝔹⁻ {A = `ℕ} ()
ren-𝔹⁻ {A = `𝔹} refl = refl
ren-𝔹⁻ {A = A ⇒ B} ()
ren-𝔹⁻ {A = `∀ A} ()

shiftRep-ℕ⁻ : (n : ℕ) → shiftRep n R ≡ `ℕ → R ≡ `ℕ
shiftRep-ℕ⁻ zero eq = eq
shiftRep-ℕ⁻ (suc n) eq = shiftRep-ℕ⁻ n (ren-ℕ⁻ eq)

shiftRep-𝔹⁻ : (n : ℕ) → shiftRep n R ≡ `𝔹 → R ≡ `𝔹
shiftRep-𝔹⁻ zero eq = eq
shiftRep-𝔹⁻ (suc n) eq = shiftRep-𝔹⁻ n (ren-𝔹⁻ eq)

same-ℕ-rep : η ⊢ `ℕ ~ R → R ≡ `ℕ
same-ℕ-rep same-ℕ = refl

same-𝔹-rep : η ⊢ `𝔹 ~ R → R ≡ `𝔹
same-𝔹-rep same-𝔹 = refl

sameTy-ℕ-𝔹-absurd : ∀ {η η′}
  → ∃[ R ] ((η ⊢ `ℕ ~ R) × (η′ ⊢ `𝔹 ~ R))
  → ⊥
sameTy-ℕ-𝔹-absurd (`ℕ , same-ℕ , ())

sameTyExt-ℕ : ∀ {n Δ A η′}
  → WfCtx Δ
  → ∃[ R ] ((names Δ ⊢ A ~ R) × (η′ ⊢ `ℕ ~ shiftRep n R))
  → A ≡ `ℕ
sameTyExt-ℕ {n = n} wfΔ (R , p , q) with same-ℕ-rep q
sameTyExt-ℕ {n = n} wfΔ (R , p , q) | eq
  with shiftRep-ℕ⁻ {R = R} n eq
sameTyExt-ℕ {n = n} wfΔ (R , p , q) | eq | refl =
  same-target-unique (name-fn wfΔ) p same-ℕ

sameTyExt-𝔹 : ∀ {n Δ A η′}
  → WfCtx Δ
  → ∃[ R ] ((names Δ ⊢ A ~ R) × (η′ ⊢ `𝔹 ~ shiftRep n R))
  → A ≡ `𝔹
sameTyExt-𝔹 {n = n} wfΔ (R , p , q) with same-𝔹-rep q
sameTyExt-𝔹 {n = n} wfΔ (R , p , q) | eq
  with shiftRep-𝔹⁻ {R = R} n eq
sameTyExt-𝔹 {n = n} wfΔ (R , p , q) | eq | refl =
  same-target-unique (name-fn wfΔ) p same-𝔹

preserve-Drop$ : ∀ {Δ n Θ A C}
  → WfCtx Δ
  → Base A
  → Δ ∣ [] ⊢ ($ n) ⟪ Θ , id A ⟫ ⦂ C
  → Δ ∣ [] ⊢ $ n ⦂ C
preserve-Drop$ {Θ = Θ} wfΔ base-ℕ
  (env mwΘ ⊢$ (conv-id base-ℕ) sameᵢ sameₑ wE)
  rewrite sameTyExt-ℕ {n = numBinds Θ} wfΔ sameₑ = ⊢$
preserve-Drop$ {Θ = Θ} wfΔ base-𝔹
  (env mwΘ ⊢$ (conv-id base-𝔹) sameᵢ sameₑ wE) =
  ⊥-elim (sameTy-ℕ-𝔹-absurd sameᵢ)

preserve-Drop-true : ∀ {Δ Θ C}
  → WfCtx Δ
  → Δ ∣ [] ⊢ `true ⟪ Θ , id `𝔹 ⟫ ⦂ C
  → Δ ∣ [] ⊢ `true ⦂ C
preserve-Drop-true {Θ = Θ} wfΔ
  (env mwΘ ⊢true (conv-id base-𝔹) sameᵢ sameₑ wE)
  rewrite sameTyExt-𝔹 {n = numBinds Θ} wfΔ sameₑ = ⊢true

preserve-Drop-false : ∀ {Δ Θ C}
  → WfCtx Δ
  → Δ ∣ [] ⊢ `false ⟪ Θ , id `𝔹 ⟫ ⦂ C
  → Δ ∣ [] ⊢ `false ⦂ C
preserve-Drop-false {Θ = Θ} wfΔ
  (env mwΘ ⊢false (conv-id base-𝔹) sameᵢ sameₑ wE)
  rewrite sameTyExt-𝔹 {n = numBinds Θ} wfΔ sameₑ = ⊢false

------------------------------------------------------------------------
-- The proved representation-only transport statements
------------------------------------------------------------------------

-- The first two are the new-interface counterparts of the old `⊢crossΛ`
-- and `⊢addLock0-cross`: each needs a BINDER (`underΛ`, `addLock0`) on top
-- of the renaming, which the third does not.  `CrossΛTyping` is PROVED
-- (2026-09-20, `strong-rep-store.proof.RepWeaken.cross-Λ-⊢`), using one
-- zero-bind
-- `env` around `⊢renᴿ` at `repwk-abst₀`.  `AddLock0Typing` was REFUTED,
-- RESHAPED and PROVED, all on 2026-09-20 — see the note on it below.  The
-- third,
-- `RepWeakenTyping`, is pure renaming and is PROVED
-- (2026-09-20, `strong-rep-store.proof.RepWeaken.rep-weaken-⊢`).
-- All three are internal staging interfaces only:
-- `strong-rep-store.Preservation`
-- instantiates them with their proofs, so preservation has no parameter.
CrossΛTyping : Set
CrossΛTyping = ∀ {Δ W A}
  → WfCtx Δ
  → Δ ⊢ᵗ A
  → Δ ∣ [] ⊢ W ⦂ A
  → underΛ Δ ∣ [] ⊢ crossΛᴹ W A ⦂ ⇑ᵗ A

-- REFUTED, THEN RESHAPED WITH THE RULE (2026-09-20).  The old statement
-- FIXED the moved spelling at `renᶜ (extᵗ suc) s`, and that is what
-- `strong-rep-store.notes.AddLock0Wall.no-addLock0°` refutes — it keeps the old
-- statement locally, since this one is no longer it.  The repaired
-- `TyPeelR-⟪⟫` NAMES the moved spelling and supplies the old conversion
-- reading, the moved one, and a `SameConv` pinning the two; those are the
-- three premises added below.  The old context is read through
-- `renNameCtx (extN (numBinds Θ) suc)`, the representation renaming the
-- inserted binder makes — dropping that view loses §6b of
-- strong-rep-store.Examples at step 8 (measured).  No fixed
-- conversion renaming appears here any more.
--
-- AND PROVED (2026-09-20), `strong-rep-store.proof.AddLock0.addLock0-⊢`.  It is
-- the
-- `env`-to-`env` transport across one inserted representation binder and
-- one fresh ordinary name: `bw-binds` by `binds-ren`, the interior reading
-- by `strong-rep-store.Boundary.addLock0-interior-ren` (where the appended lock
-- DELETES the fresh name, so what is left is `interior-ren`), the interior
-- term by `strong-rep-store.proof.RepWeaken.⊢renᴿ` at
-- `repwk-push (repwk-cons₀ (bindR P) …) (binds Θ)`, and the conversion by
-- `conv-ren` (strong-rep-store.Conversion §2d) followed by
-- `strong-rep-store.proof.PeelDual.respell-⊢` — whose `reps Γ′ ≡ reps Γ` premise
-- is
-- exactly what `renNameCtx` arranges.  It stays a PARAMETER of `Impl` here
-- only because its proof imports this module.
AddLock0Typing : Set
AddLock0Typing = ∀ {Δ Δᶜ Δ⁺ᶜ W Θ s s′ A P}
  → WfCtx ((bindR P ∷ reps Δ) ∣
               (zero ∷ shiftNames (names Δ)))
  → Δ ∣ [] ⊢ W ⟪ Θ , `∀ s ⟫ ⦂ `∀ A
  → Δ ⊢ᶜ Θ ⇒ Δᶜ
  → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftNames (names Δ)))
      ⊢ᶜ addLock0 (renᴮ² (ren² (λ X → X) suc) Θ) ⇒ Δ⁺ᶜ
  → SameConv (underΛ Δ⁺ᶜ) s′
      (underΛ (renNameCtx (extN (numBinds Θ) suc) Δ⁺ᶜ Δᶜ)) s
  → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftNames (names Δ)))
      ∣ [] ⊢
        (renᴹ² (ren² (λ X → X) (extN (numBinds Θ) suc)) W
          ⟪ addLock0 (renᴮ² (ren² (λ X → X) suc) Θ)
          , `∀ s′ ⟫)
        ⦂ `∀ (renameᵗ (extᵗ suc) A)

-- The THIRD such transport, identified by the stage-2 `Peel` port
-- (2026-09-19) and PROVED on 2026-09-20 in
-- `strong-rep-store.proof.RepWeaken.rep-weaken-⊢`.  `Peel` moves its argument
-- from
-- the boundary's exterior to that exterior under the boundary's own
-- representation bind block — `dual-interior`, strong-rep-store.Boundary §3a.
-- `renᴹᴿ` is representation-only by construction, so the argument's TYPE
-- and every ordinary spelling are unchanged.  `renᴹ²-ord-id` connects
-- this statement to the paired identity-ordinary spelling retained by
-- `Peel`'s contractum.
--
-- THE BIND BLOCK MUST BE WELL FORMED (2026-09-20).  Without the premise
-- `reps Δ ⊢ᴮ Rs` the statement is FALSE — `notes/RepWeakenBindsWall.agda`
-- refutes it from `β-seven` and the single open payload `` ` 0 ``, since
-- a boundary's `env` stores a `BoundaryWf` whose `bw-exterior` demands a
-- `WfCtx` of the weakened context.  The premise costs nothing: at the one
-- call site it is `bw-binds` of the boundary being crossed.
RepWeakenTyping : Set
RepWeakenTyping = ∀ {Δ W A} (Rs : List Ty)
  → reps Δ ⊢ᴮ Rs
  → Δ ∣ [] ⊢ W ⦂ A
  → extendReps Rs Δ ∣ [] ⊢ renᴹᴿ (wkN (length Rs)) W ⦂ A

wf-underΛ : WfCtx Δ → WfCtx (underΛ Δ)
wf-underΛ {Δ = Δ} (wf-ctx wr vn uq) =
  wf-ctx (wf-abstR wr) valid (unique-underΛ {Γ = Δ} uq)
  where
  valid : ValidNames (abstR ∷ reps Δ)
                     (zero ∷ shiftNames (names Δ))
  valid here = abstR , here
  valid (there d) with shiftNames-∋⁻ d
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
⊢substᴹ cross wfΔ h (⊢·[] ⊢L w) =
  ⊢·[] (⊢substᴹ cross wfΔ h ⊢L) w
⊢substᴹ cross wfΔ h (env mwᵥ ⊢M ⊢c sameᵢ sameₑ wE) =
  env mwᵥ ⊢M ⊢c sameᵢ sameₑ wE

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

ren-suc-[0] : (T : Ty)
  → (renameᵗ (extᵗ suc) T) [ ` 0 ]ᵗ ≡ T
ren-suc-[0] T =
  trans (rename-subst-commute (extᵗ suc) (singleTyEnv (` 0)) T)
        (trans (subst-cong h T) (subst-id T))
  where
  h : (X : ℕ) → singleTyEnv (` 0) (extᵗ suc X) ≡ ` X
  h zero = refl
  h (suc X) = refl

preserve-TyPeelR-⟪⟫ : AddLock0Typing
  → ∀ {Δ Δᵢ Δᵢ⁺ Δᶜ Δ′ᶜ Δ″ᶜ W Θ′ s′ s″ Θ s B A R Bᵢ Bᵢ′ Bₑ C}
  → WfCtx Δ
  → Value W
  → Δ ⊢ⁱ Θ ⇒ Δᵢ
  → Δ ⊢ᶜ Θ ⇒ Δᶜ
  → Δᵢ ⊢ᶜ Θ′ ⇒ Δ′ᶜ
  → Δ ⊢ⁱ instantiate R Θ ⇒ Δᵢ⁺
  → Δᵢ⁺ ⊢ᶜ addLock0 (renᴮ² (ren² (λ X → X) suc) Θ′) ⇒ Δ″ᶜ
  → SameConv (underΛ Δ″ᶜ) s″
      (underΛ
        (renNameCtx (extN (numBinds Θ′) suc) Δ″ᶜ Δ′ᶜ)) s′
  → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
  → underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ
  → Δ ⊢ᶜ A ~ R
  → Δ ∣ [] ⊢
      ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
  → Δ ∣ [] ⊢
      ((renᴹ² (ren² (λ X → X) (extN (numBinds Θ′) suc)) W
          ⟪ addLock0 (renᴮ² (ren² (λ X → X) suc) Θ′) , `∀ s″ ⟫)
        ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ])
        ⟪ instantiate R Θ , instReveal 0 s ⟫ ⦂ C
preserve-TyPeelR-⟪⟫ addlock {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
    {W = W} {Θ′ = Θ′} {s′ = s′} {s″ = s″} {Θ = Θ} {s = s}
    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bᵢ′ = Bᵢ′} {Bₑ = Bₑ}
    wfΔ v ri rc r′ ri⁺ r″ sc ⊢s sm p
    (⊢·[] (env mwΘ (env mw′ ⊢W ⊢c′ sameᵢ′ sameₑ′ wE′)
                       ⊢c sameᵢ sameₑ wE) wA)
  with interior-functional ri (bw-interior mwΘ)
     | conversion-functional rc (bw-conversion mwΘ)
preserve-TyPeelR-⟪⟫ addlock {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
    {W = W} {Θ′ = Θ′} {s′ = s′} {s″ = s″} {Θ = Θ} {s = s}
    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bᵢ′ = Bᵢ′} {Bₑ = Bₑ}
    wfΔ v ri rc r′ ri⁺ r″ sc ⊢s sm p
    (⊢·[] (env mwΘ (env mw′ ⊢W ⊢c′ sameᵢ′ sameₑ′ wE′)
                       ⊢c sameᵢ sameₑ wE) wA)
  | refl | refl
  with conversion-functional r′ (bw-conversion mw′)
     | interior-functional ri⁺ (instantiate-interior (bw-interior mwΘ))
preserve-TyPeelR-⟪⟫ addlock {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
    {W = W} {Θ′ = Θ′} {s′ = s′} {s″ = s″} {Θ = Θ} {s = s}
    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bᵢ′ = Bᵢ′} {Bₑ = Bₑ}
    wfΔ v ri rc r′ ri⁺ r″ sc ⊢s sm p
    (⊢·[] (env mwΘ (env mw′ ⊢W ⊢c′ sameᵢ′ sameₑ′ wE′)
                       ⊢c sameᵢ sameₑ wE) wA)
  | refl | refl | refl | refl with conv-all-inv ⊢c
preserve-TyPeelR-⟪⟫ addlock {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
    {W = W} {Θ′ = Θ′} {s′ = s′} {s″ = s″} {Θ = Θ} {s = s}
    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bᵢ′ = Bᵢ′} {Bₑ = Bₑ}
    wfΔ v ri rc r′ ri⁺ r″ sc ⊢s sm p
    (⊢·[] (env mwΘ (env mw′ ⊢W ⊢c′ sameᵢ′ sameₑ′ wE′)
                       ⊢c sameᵢ sameₑ wE) wA)
  | refl | refl | refl | refl | A₀ , B₀ , refl , refl , ⊢s₀
  with conv-types-unique
         (unique-underΛ {Γ = Δᶜ} (name-fn (bw-conversion-wf mwΘ)))
         ⊢s ⊢s₀
preserve-TyPeelR-⟪⟫ addlock {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
    {W = W} {Θ′ = Θ′} {s′ = s′} {s″ = s″} {Θ = Θ} {s = s}
    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bᵢ′ = Bᵢ′} {Bₑ = Bₑ}
    wfΔ v ri rc r′ ri⁺ r″ sc ⊢s sm p
    (⊢·[] (env mwΘ (env mw′ ⊢W ⊢c′ sameᵢ′ sameₑ′ wE′)
                       ⊢c sameᵢ sameₑ wE) wA)
  | refl | refl | refl | refl | A₀ , B₀ , refl , refl , ⊢s₀
  | refl , refl with sameTy-target-∀⁻ sameᵢ
preserve-TyPeelR-⟪⟫ addlock {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
    {W = W} {Θ′ = Θ′} {s′ = s′} {s″ = s″} {Θ = Θ} {s = s}
    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bᵢ′ = Bᵢ′} {Bₑ = Bₑ}
    wfΔ v ri rc r′ ri⁺ r″ sc ⊢s sm p
    (⊢·[] (env mwΘ (env mw′ ⊢W ⊢c′ sameᵢ′ sameₑ′ wE′)
                       ⊢c sameᵢ sameₑ wE) wA)
  | refl | refl | refl | refl | A₀ , B₀ , refl , refl , ⊢s₀
  | refl , refl | D , refl , sameD
  with sameTy-src-unique
         (name-fn (wf-underΛ (bw-interior-wf mwΘ))) sameD sm
preserve-TyPeelR-⟪⟫ addlock {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
    {W = W} {Θ′ = Θ′} {s′ = s′} {s″ = s″} {Θ = Θ} {s = s}
    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bᵢ′ = Bᵢ′} {Bₑ = Bₑ}
    wfΔ v ri rc r′ ri⁺ r″ sc ⊢s sm p
    (⊢·[] (env mwΘ (env mw′ ⊢W ⊢c′ sameᵢ′ sameₑ′ wE′)
                       ⊢c sameᵢ sameₑ wE) wA)
  | refl | refl | refl | refl | A₀ , B₀ , refl , refl , ⊢s₀
  | refl , refl | D , refl , sameD | refl
  with respell-ty (conversion-live rc) (same-shiftRVars (numBinds Θ) p)
preserve-TyPeelR-⟪⟫ addlock {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
    {W = W} {Θ′ = Θ′} {s′ = s′} {s″ = s″} {Θ = Θ} {s = s}
    {B = B} {A = A} {R = R} {Bᵢ = Bᵢ} {Bᵢ′ = Bᵢ′} {Bₑ = Bₑ}
    wfΔ v ri rc r′ ri⁺ r″ sc ⊢s sm p
    (⊢·[] (env mwΘ (env mw′ ⊢W ⊢c′ sameᵢ′ sameₑ′ wE′)
                       ⊢c sameᵢ sameₑ wE) wA)
  | refl | refl | refl | refl | A₀ , B₀ , refl , refl , ⊢s₀
  | refl , refl | D , refl , sameD | refl | Aᶜ , pᶜ =
  env mwᵢ int conv sm sameₑ′′ wFinal
  where
  k : ℕ
  k = numBinds Θ

  ΔRᵢ : Ctxᵗ
  ΔRᵢ = (bindR (shiftBy k R) ∷ reps Δᵢ)
          ∣ (zero ∷ shiftNames (names Δᵢ))

  ΔRᶜ : Ctxᵗ
  ΔRᶜ = (bindR (shiftBy k R) ∷ reps Δᶜ)
          ∣ (zero ∷ shiftNames (names Δᶜ))

  mwᵢ : BoundaryWf Δ (instantiate R Θ) ΔRᵢ ΔRᶜ
  mwᵢ = instantiate-boundarywf mwΘ p

  moved : ΔRᵢ ∣ [] ⊢
      (renᴹ² (ren² (λ X → X) (extN (numBinds Θ′) suc)) W
        ⟪ addLock0 (renᴮ² (ren² (λ X → X) suc) Θ′) , `∀ s″ ⟫)
      ⦂ `∀ (renameᵗ (extᵗ suc) Bᵢ′)
  moved = addlock (bw-interior-wf mwᵢ)
                  (env mw′ ⊢W ⊢c′ sameᵢ′ sameₑ′ wE′) r′ r″ sc

  int : ΔRᵢ ∣ [] ⊢
      (renᴹ² (ren² (λ X → X) (extN (numBinds Θ′) suc)) W
        ⟪ addLock0 (renᴮ² (ren² (λ X → X) suc) Θ′) , `∀ s″ ⟫)
       ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ] ⦂ Bᵢ′
  int = subst (λ T → ΔRᵢ ∣ [] ⊢
          (renᴹ² (ren² (λ X → X) (extN (numBinds Θ′) suc)) W
            ⟪ addLock0 (renᴮ² (ren² (λ X → X) suc) Θ′) , `∀ s″ ⟫)
           ·[ renameᵗ (extᵗ suc) Bᵢ′ , ` 0 ] ⦂ T)
        (ren-suc-[0] Bᵢ′)
        (⊢·[] moved (wf-var (zero , here)))

  conv = ⊢instReveal 0 pᶜ ⊢s

  wFinal = wf-[]ᵗ (wf-∀⁻ wE) wA

  sameₑ′′ : SameTyExt (suc k) Δ (B [ A ]ᵗ) ΔRᶜ
                           (Bₑ [ 0 := ⇑ᵗ Aᶜ ]ᵗ)
  sameₑ′′ with sameTyExt-∀⁻ {n = k} sameₑ
  sameₑ′′ | S , pB , pBₑ = S [ R ]ᵗ , same-[] pB p , target
    where
    target : names ΔRᶜ ⊢ Bₑ [ 0 := ⇑ᵗ Aᶜ ]ᵗ
               ~ shiftRep (suc k) (S [ R ]ᵗ)
    target rewrite subst-at-0 Aᶜ Bₑ
                 | shiftRep-shiftBy (suc k) (S [ R ]ᵗ)
                 | shiftBy-[]ᵗ k S R =
      same-weaken (same-[] pBₑ pᶜ)

------------------------------------------------------------------------
-- §4. Preservation assembled over the downstream crossing cases
------------------------------------------------------------------------

-- The downstream crossing cases and transports stay module parameters HERE
-- because their proofs import this module.  `strong-rep-store.Preservation`
-- plugs in
-- every implementation, including `CrossΛTyping` and `AddLock0Typing`, and
-- exposes NO public parameter at all.  Until 2026-09-20 `AddLock0Typing` was
-- REFUTED and `Impl.preserve` a conditional theorem with a false
-- hypothesis; the `TyPeelR-⟪⟫` repair installed that day reshaped it
-- (strong-rep-store.notes.AddLock0Wall), and
-- `strong-rep-store.proof.AddLock0.addLock0-⊢`
-- proved the reshaped statement, which made preservation UNCONDITIONAL.
--
--   CrossΛTyping PROVED (2026-09-20) —
--                `strong-rep-store.proof.RepWeaken.cross-Λ-⊢`.
--   AddLock0Typing PROVED (2026-09-20), on the statement RESHAPED with the
--                `TyPeelR-⟪⟫` repair of the same day —
--                `strong-rep-store.proof.AddLock0.addLock0-⊢`.  The old
-- statement
--                fixed the moved conversion at `renᶜ (extᵗ suc) s` and was
--                REFUTED from a closed, plain source program
--                (notes/AddLock0Wall.agda, which keeps that statement
--                locally and still refutes it).
--   PeelCase     PROVED UNCONDITIONALLY (2026-09-20) —
--                `strong-rep-store.proof.PeelDual.preserve-Peel` applied to
--                `strong-rep-store.proof.RepWeaken.rep-weaken-⊢`, which proves
-- the
--                representation-only weakening `RepWeakenTyping` above.
--                `preserve-Peel` keeps its `module _ (repWeaken : …)`
--                shape; `strong-rep-store.Preservation` plugs the theorem in.
--   IdPushCase   PROVED outright —
--                `strong-rep-store.proof.MoveScope.preserve-IdPush`.
--   CancelRCase  PROVED outright, on the rule REPAIRED 2026-09-19 —
--                `strong-rep-store.proof.MoveScope.preserve-CancelR`.  The old
--                statement re-spelled the inner identity FROM the OUTER
--                conversion context and was refuted; the repaired rule
--                reads the cancelled `seal X`'s own source at Θ₁'s
--                conversion context `Δ₁ᶜ`, which makes this block
--                premise-isomorphic to `IdPushCase` below — and the proof
--                is `preserve-IdPush`'s.  See notes/CancelRShiftWall.agda
--                for the incompatibility the old spelling walked into and
--                notes/DECISIONS.md, 2026-09-19.

PeelCase : Set
PeelCase = ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t C}
  → WfCtx Δ → Value V → Value W
  → Δ ⊢ᶜ Θ ⇒ Δᶜ → Δ ⊢ⁱ Θ ⇒ Δᵢ
  → Δᵢ ⊢ᶜ dualBoundary Θ ⇒ Δᵈ → SameConv Δᵈ s′ Δᶜ s
  → Δ ∣ [] ⊢ (V ⟪ Θ , s ↦ t ⟫) · W ⦂ C
  → Δ ∣ [] ⊢
      (V · (renᴹ² (ren² (λ X → X) (wkN (numBinds Θ))) W
              ⟪ dualBoundary Θ , s′ ⟫)) ⟪ Θ , t ⟫ ⦂ C

CancelRCase : Set
CancelRCase = ∀ {Δ Δᵢ Δ₁ᶜ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X Y}
  {A A′ Aᵢ C}
  → WfCtx Δ → Value V → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
  → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
  → Δ₁ᶜ ∋ X := Aᵢ
  → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
  → Δ⋉ᶜ ⊢ A′ ≈ Aᵢ ⊣ Δ₁ᶜ
  → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ
  → Δᶜ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , seal X ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢
      (V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫)
        ⟪ rewind Θ₂ , mkId A ⟫ ⦂ C

IdPushCase : Set
IdPushCase = ∀ {Δ Δᵢ Δ₁ᶜ Δ⋉ᶜ Δᶜ V Θ₁ Θ₂ X X′ Y A C}
  → WfCtx Δ → Value V → Δ ⊢ⁱ Θ₂ ⇒ Δᵢ
  → Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ
  → extendReps (binds Θ₂) Δ ⊢ᶜ Θ₁ ⋉ Θ₂ ⇒ Δ⋉ᶜ
  → Δ⋉ᶜ ⊢ ` X′ ≈ ` X ⊣ Δ₁ᶜ
  → Δ ⊢ᶜ Θ₂ ⇒ Δᶜ → Δᶜ ∋ Y := A
  → Δ ∣ [] ⊢ (V ⟪ Θ₁ , id (` X) ⟫) ⟪ Θ₂ , unseal Y ⟫ ⦂ C
  → Δ ∣ [] ⊢
      (V ⟪ Θ₁ ⋉ Θ₂ , unseal X′ ⟫)
        ⟪ rewind Θ₂ , mkId A ⟫ ⦂ C

module Impl
  (crossΛ  : CrossΛTyping)
  (addLock0 : AddLock0Typing)
  (peel    : PeelCase)
  (cancel  : CancelRCase)
  (idpush  : IdPushCase)
  where

  preserve : ∀ {Δ M M′ A} → WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A
    → Δ ⊢ M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A
  preserve wfΔ ⊢M (TyBeta v p) = preserve-TyBeta wfΔ p ⊢M
  preserve wfΔ ⊢M (Beta v) = preserve-Beta crossΛ wfΔ ⊢M
  preserve wfΔ ⊢M (Peel v w rc ri rd sc) =
    peel wfΔ v w rc ri rd sc ⊢M
  preserve wfΔ ⊢M (TyPeelR-Λ v rc ⊢s p) =
    preserve-TyPeelR-Λ wfΔ v rc ⊢s p ⊢M
  preserve wfΔ ⊢M
    (TyPeelR-⟪⟫ v ri rc r′ ri⁺ r″ sc ⊢s sm p) =
    preserve-TyPeelR-⟪⟫ addLock0 wfΔ v ri rc r′ ri⁺ r″ sc ⊢s sm p ⊢M
  preserve wfΔ ⊢M (CancelR v ri r₁ d₁ rc sm r₂ d₂) =
    cancel wfΔ v ri r₁ d₁ rc sm r₂ d₂ ⊢M
  preserve wfΔ ⊢M (Drop$ b) = preserve-Drop$ wfΔ b ⊢M
  preserve wfΔ ⊢M Drop-true = preserve-Drop-true wfΔ ⊢M
  preserve wfΔ ⊢M Drop-false = preserve-Drop-false wfΔ ⊢M
  preserve wfΔ ⊢M (IdPush v ri r₁ rc sm r₂ d) =
    idpush wfΔ v ri r₁ rc sm r₂ d ⊢M
  preserve wfΔ (⊢· ⊢L ⊢M) (ξ-·-l st) =
    ⊢· (preserve wfΔ ⊢L st) ⊢M
  preserve wfΔ (⊢· ⊢L ⊢M) (ξ-·-r v st) =
    ⊢· ⊢L (preserve wfΔ ⊢M st)
  preserve wfΔ (⊢·[] ⊢L w) (ξ-·[] st) =
    ⊢·[] (preserve wfΔ ⊢L st) w
  preserve wfΔ (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) (ξ-⟪⟫ ri st)
    with interior-functional ri (bw-interior mwΘ)
  preserve wfΔ (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) (ξ-⟪⟫ ri st)
    | refl = env mwΘ (preserve (bw-interior-wf mwΘ) ⊢M st)
                    ⊢c sameᵢ sameₑ wE

  preserve* : ∀ {Δ M M′ A} → WfCtx Δ → Δ ∣ [] ⊢ M ⦂ A
    → Δ ⊢ M -→* M′ → Δ ∣ [] ⊢ M′ ⦂ A
  preserve* wfΔ ⊢M done = ⊢M
  preserve* wfΔ ⊢M (st then sts) =
    preserve* wfΔ (preserve wfΔ ⊢M st) sts
