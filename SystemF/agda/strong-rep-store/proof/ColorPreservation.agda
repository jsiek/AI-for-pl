module strong-rep-store.proof.ColorPreservation where

-- File Charter:
--   * COLOR PRESERVATION — the proof.  §1 map bookkeeping; §2 the
--     frame judgement ignores the store beyond its LENGTH; §3 it is
--     functional; §4 `Beta`'s substitution never moves a frame;
--     §5 the `crossΛᴹ` dual has a reading everywhere; §6 `⊢C-ren`, THE
--     TRANSPORT; §6a the store change on a frame; §7 the copies;
--     §8 `residual-frame`, the PER-STEP theorem; §9 `residuals-color`;
--     §10 the COLOR corollary.
--   * THE SHAPE.  `residual-frame` CONSTRUCTS the target position's
--     frame at `apply δ Δ` with `names Δ₂ ≡ map ρ (names Δ₁)`.  Every
--     rule but the movers is frame-for-frame (Boundary §3a's interior
--     lemmas); the movers go through `⊢C-ren`.  `residuals-color`
--     composes along `ρ′ ∘ ρ`, spending the `WfCtx Δ` premise on
--     `preservation`/`preservation-wf`.
-- Commentary: Commentary.md § proof/ColorPreservation.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong-rep-store.Types
  using (Ty; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; `_)
open import strong-rep-store.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst
open import strong-rep-store.Reduction
open import strong-rep-store.Residual
open import strong-rep-store.proof.Ctx
  using (repwk-cons₀; repwk-abst₀; repwk-abst; fresh-zero-shift)
open import strong-rep-store.proof.Preserve
  using (empty-interior; same-wfᴿ; repwk-alloc;
         AllocWf; aw-none; aw-new; aw-reps; step-alloc)
open import strong-rep-store.Preservation
  using (preservation; preservation-wf)

private
  variable
    Γ Γ′ Δ Δ′ Δᵢ Δ₁ Δ₂ : Ctxᵗ
    Ξ Ξ′ : RepCtx
    Δn Δn′ : TyCtx
    ch : Change
    χ : List Change
    α : RVar
    A B : Ty
    L N P W : Term
    C D : TermCtx
    Θ : Boundary
    c : Conv
    ρ ρ′ : Renameᵗ
    k : ℕ

------------------------------------------------------------------------
-- 1. Map bookkeeping
------------------------------------------------------------------------

map-idᵗ : (Δn : TyCtx) → map idᵗ Δn ≡ Δn
map-idᵗ []       = refl
map-idᵗ (α ∷ Δn) = cong (α ∷_) (map-idᵗ Δn)

map-∘ᵣ : (g f : Renameᵗ) (Δn : TyCtx)
  → map (g ∘ f) Δn ≡ map g (map f Δn)
map-∘ᵣ g f []       = refl
map-∘ᵣ g f (α ∷ Δn) = cong (g (f α) ∷_) (map-∘ᵣ g f Δn)

-- Renaming and the `Λ` shift commute on a name map.
map-suc-ext : (ρ : Renameᵗ) (Δn : TyCtx)
  → map suc (map ρ Δn) ≡ map (extᵗ ρ) (map suc Δn)
map-suc-ext ρ []       = refl
map-suc-ext ρ (α ∷ Δn) = cong (suc (ρ α) ∷_) (map-suc-ext ρ Δn)

------------------------------------------------------------------------
-- 2. The frame judgment ignores the representation STORE beyond its
--    length: the refinement `abstR → bindR R` of a slot (TyBeta's,
--    TyPeelR-Λ's) transports every `⊢C` derivation, names untouched.
------------------------------------------------------------------------

∋ˡ-len : ∀ {A : Set} {Ξ Ξ′ : List A} {α : ℕ} {x : A}
  → length Ξ ≡ length Ξ′ → Ξ ∋ˡ α := x → Σ[ y ∈ A ] Ξ′ ∋ˡ α := y
∋ˡ-len {Ξ′ = y ∷ Ξ′} eq here      = y , here
∋ˡ-len {Ξ′ = y ∷ Ξ′} eq (there d) =
  let (z , d′) = ∋ˡ-len (suc-injective eq) d in z , there d′

∋ʳ-len : length Ξ ≡ length Ξ′ → Ξ ∋ʳ α → Ξ′ ∋ʳ α
∋ʳ-len eq (b , d) = ∋ˡ-len eq d

step-len : length Ξ ≡ length Ξ′
  → Ξ ∣ Δn ⊢δ ch ⇒ Δn′ → Ξ′ ∣ Δn ⊢δ ch ⇒ Δn′
step-len eq (step-lock v d f)   = step-lock (∋ʳ-len eq v) d f
step-len eq (step-unlock v f i) = step-unlock (∋ʳ-len eq v) f i

changes-len : length Ξ ≡ length Ξ′
  → Ξ ∣ Δn ⊢χ χ ⇒ Δn′ → Ξ′ ∣ Δn ⊢χ χ ⇒ Δn′
changes-len eq changes[]        = changes[]
changes-len eq (changes∷ cs st) =
  changes∷ (changes-len eq cs) (step-len eq st)

⊢C-len : ∀ {C Δ₁} (Ξ′ : RepCtx) → length Ξ ≡ length Ξ′
  → (Ξ ∣ Δn) ⊢C C ⊣ Δ₁
  → Σ[ Ξ₂ ∈ RepCtx ] (Ξ′ ∣ Δn) ⊢C C ⊣ (Ξ₂ ∣ names Δ₁)
      × (length (reps Δ₁) ≡ length Ξ₂)
⊢C-len Ξ′ eq frame-□        = Ξ′ , frame-□ , eq
⊢C-len Ξ′ eq (frame-ƛ d)    =
  let (Ξ₂ , d′ , l) = ⊢C-len Ξ′ eq d in Ξ₂ , frame-ƛ d′ , l
⊢C-len Ξ′ eq (frame-·L d)   =
  let (Ξ₂ , d′ , l) = ⊢C-len Ξ′ eq d in Ξ₂ , frame-·L d′ , l
⊢C-len Ξ′ eq (frame-·R d)   =
  let (Ξ₂ , d′ , l) = ⊢C-len Ξ′ eq d in Ξ₂ , frame-·R d′ , l
⊢C-len Ξ′ eq (frame-Λ d)    =
  let (Ξ₂ , d′ , l) = ⊢C-len (abstR ∷ Ξ′) (cong suc eq) d
  in Ξ₂ , frame-Λ d′ , l
⊢C-len Ξ′ eq (frame-·[] d)  =
  let (Ξ₂ , d′ , l) = ⊢C-len Ξ′ eq d in Ξ₂ , frame-·[] d′ , l
⊢C-len Ξ′ eq (frame-⟪⟫ (interior cs) d) =
  let (Ξ₂ , d′ , l) = ⊢C-len Ξ′ eq d
  in Ξ₂ , frame-⟪⟫ (interior (changes-len eq cs)) d′ , l

------------------------------------------------------------------------
-- 3. The frame judgment is functional
------------------------------------------------------------------------

⊢C-functional : Γ ⊢C C ⊣ Δ₁ → Γ ⊢C C ⊣ Δ₂ → Δ₁ ≡ Δ₂
⊢C-functional frame-□ frame-□ = refl
⊢C-functional (frame-ƛ d)   (frame-ƛ d′)   = ⊢C-functional d d′
⊢C-functional (frame-·L d)  (frame-·L d′)  = ⊢C-functional d d′
⊢C-functional (frame-·R d)  (frame-·R d′)  = ⊢C-functional d d′
⊢C-functional (frame-Λ d)   (frame-Λ d′)   = ⊢C-functional d d′
⊢C-functional (frame-·[] d) (frame-·[] d′) = ⊢C-functional d d′
⊢C-functional (frame-⟪⟫ ri d) (frame-⟪⟫ ri′ d′)
  with interior-functional ri ri′
⊢C-functional (frame-⟪⟫ ri d) (frame-⟪⟫ ri′ d′) | refl =
  ⊢C-functional d d′

------------------------------------------------------------------------
-- 4. `Beta`'s substitution never moves a frame: boundary frames are
--    term-closed and every other frame ignores its side terms.
------------------------------------------------------------------------

⊢C-substCtx : (σ : Var → Img) → Γ ⊢C C ⊣ Δ₁ → Γ ⊢C substCtx σ C ⊣ Δ₁
⊢C-substCtx σ frame-□         = frame-□
⊢C-substCtx σ (frame-ƛ d)     = frame-ƛ (⊢C-substCtx (extᴵ σ) d)
⊢C-substCtx σ (frame-·L d)    = frame-·L (⊢C-substCtx σ d)
⊢C-substCtx σ (frame-·R d)    = frame-·R (⊢C-substCtx σ d)
⊢C-substCtx σ (frame-Λ d)     = frame-Λ (⊢C-substCtx (λ x → ⇑ᴵ (σ x)) d)
⊢C-substCtx σ (frame-·[] d)   = frame-·[] (⊢C-substCtx σ d)
⊢C-substCtx σ (frame-⟪⟫ ri d) = frame-⟪⟫ ri d

------------------------------------------------------------------------
-- 5. The dual `crossΛᴹ` mints has a reading at every context: it locks
--    exactly the fresh name the `Λ` added, and slot 0 is fresh in the
--    shifted remainder.
------------------------------------------------------------------------

crossΛ-interior : (Γ : Ctxᵗ)
  → underΛ Γ ⊢ⁱ (lock 0 0 ∷ [])
      ⇒ ((abstR ∷ reps Γ) ∣ shiftNames (names Γ))
crossΛ-interior Γ =
  interior (changes∷ changes[]
    (step-lock (abstR , here) del-here fresh-zero-shift))

------------------------------------------------------------------------
-- 6. THE TRANSPORT: a frame derivation moves along a representation-only
--    renaming, and the hole's scope map moves by exactly the renaming
--    `holeᴿ` delivers there.  The boundary case is `interior-ren`, and
--    since the store it runs at the SAME ρ — there is no bind block to
--    step past.
------------------------------------------------------------------------

⊢C-ren : ∀ (ρ : Renameᵗ) {Γ Γ′ Δ₁} (C : TermCtx)
  → RepWk ρ (reps Γ) (reps Γ′)
  → names Γ′ ≡ map ρ (names Γ)
  → Γ ⊢C C ⊣ Δ₁
  → Σ[ Δ₂ ∈ Ctxᵗ ] (Γ′ ⊢C renCtxᴿ ρ C ⊣ Δ₂)
      × (names Δ₂ ≡ map (holeᴿ ρ C) (names Δ₁))
      × RepWk (holeᴿ ρ C) (reps Δ₁) (reps Δ₂)
⊢C-ren ρ □ w eq frame-□ = _ , frame-□ , eq , w
⊢C-ren ρ (ƛC A ∙ C) w eq (frame-ƛ d) =
  let (Δ₂ , d′ , e , w′) = ⊢C-ren ρ C w eq d
  in Δ₂ , frame-ƛ d′ , e , w′
⊢C-ren ρ (C ·L N) w eq (frame-·L d) =
  let (Δ₂ , d′ , e , w′) = ⊢C-ren ρ C w eq d
  in Δ₂ , frame-·L d′ , e , w′
⊢C-ren ρ (L ·R C) w eq (frame-·R d) =
  let (Δ₂ , d′ , e , w′) = ⊢C-ren ρ C w eq d
  in Δ₂ , frame-·R d′ , e , w′
⊢C-ren ρ (C ·C[ B , A ]) w eq (frame-·[] d) =
  let (Δ₂ , d′ , e , w′) = ⊢C-ren ρ C w eq d
  in Δ₂ , frame-·[] d′ , e , w′
⊢C-ren ρ {Γ = Γ} (ΛC C) w eq (frame-Λ d) =
  let (Δ₂ , d′ , e , w′) =
        ⊢C-ren (extᵗ ρ) C (repwk-abst w)
          (cong₂ _∷_ refl
            (trans (cong (map suc) eq) (map-suc-ext ρ (names Γ))))
          d
  in Δ₂ , frame-Λ d′ , e , w′
⊢C-ren ρ {Γ′ = Γ′} (C ⟪C Θ , c ⟫) w eq (frame-⟪⟫ (interior cs) d) =
  let ri₁ = interior-ren w (interior cs)
      ri₂ = subst (λ Δn → (reps Γ′ ∣ Δn) ⊢ⁱ renᴮᴿ ρ Θ ⇒ _) (sym eq) ri₁
      (Δ₂ , d′ , e , w′) = ⊢C-ren ρ C w refl d
  in Δ₂ , frame-⟪⟫ ri₂ d′ , e , w′

------------------------------------------------------------------------
-- 6a. THE STORE CHANGE, on a frame derivation and on a reading.  A step
--     that allocates moves every position by the sibling shift; a step
--     that does not moves nothing at all, ON THE NOSE.
------------------------------------------------------------------------

⊢C-shift : ∀ {Δ Δ₁} (δ : Alloc) (C : TermCtx) → AllocWf δ Δ
  → Δ ⊢C C ⊣ Δ₁
  → Σ[ Δ₂ ∈ Ctxᵗ ] (apply δ Δ ⊢C ↑ᶜ[ δ ] C ⊣ Δ₂)
      × (names Δ₂ ≡ map (↑ʳ[ δ ] C) (names Δ₁))
⊢C-shift none C aw-none h = _ , h , sym (map-idᵗ _)
⊢C-shift {Δ = Δ} (new R) C (aw-new wR) h
  with ⊢C-ren suc {Γ′ = allocate R Δ} C (repwk-alloc wR) refl h
⊢C-shift {Δ = Δ} (new R) C (aw-new wR) h | Δ₂ , d , e , _ = Δ₂ , d , e

interior-apply : ∀ {Δ Δᵢ Θ} (δ : Alloc) → AllocWf δ Δ
  → Δ ⊢ⁱ Θ ⇒ Δᵢ → apply δ Δ ⊢ⁱ ↑ᴮ[ δ ] Θ ⇒ apply δ Δᵢ
interior-apply none    aw-none     ri           = ri
interior-apply (new R) (aw-new wR) (interior cs) =
  interior-ren (repwk-alloc wR) (interior cs)

------------------------------------------------------------------------
-- 7. The copies: `Beta`'s argument, followed to each occurrence.  The
--    ambient at depth k is `underΛᵏ k` of the redex's, and each `Λ`
--    crossed contributes one `crossΛ-interior` frame and one `suc`
--    transport — which is exactly the `holeᴿ suc D ∘ ρ` the residual's
--    index composes.
------------------------------------------------------------------------

underΛᵏ : ℕ → Ctxᵗ → Ctxᵗ
underΛᵏ zero    Γ = Γ
underΛᵏ (suc k) Γ = underΛ (underΛᵏ k Γ)

image-frame : ∀ {k I C M ρ D N Δ₁}
  → ImageResidual k I C M ρ D N
  → Δ ⊢C C ⊣ Δ₁
  → Σ[ Δ₂ ∈ Ctxᵗ ] (underΛᵏ k Δ ⊢C D ⊣ Δ₂)
      × (names Δ₂ ≡ map ρ (names Δ₁))
image-frame image-here h = _ , h , sym (map-idᵗ _)
image-frame {Δ = Δ} (image-Λ {k = k} {D = D} r) h =
  let (Δ′ , d , e) = image-frame {Δ = Δ} r h
      (Δ₂ , d₂ , e₂ , _) = ⊢C-ren suc D repwk-abst₀ refl d
  in Δ₂
   , frame-⟪⟫ (crossΛ-interior (underΛᵏ k Δ)) d₂
   , trans e₂ (trans (cong (map (holeᴿ suc D)) e)
                     (sym (map-∘ᵣ (holeᴿ suc D) _ _)))

copy-frame : ∀ {k σ P C M ρ D N Δ₁}
  → CopyResidual k σ P C M ρ D N
  → Δ ⊢C C ⊣ Δ₁
  → Σ[ Δ₂ ∈ Ctxᵗ ] (underΛᵏ k Δ ⊢C D ⊣ Δ₂)
      × (names Δ₂ ≡ map ρ (names Δ₁))
copy-frame (copy-var i)  h = image-frame i h
copy-frame (copy-ƛ r)    h =
  let (Δ₂ , d , e) = copy-frame r h in Δ₂ , frame-ƛ d , e
copy-frame (copy-·L r)   h =
  let (Δ₂ , d , e) = copy-frame r h in Δ₂ , frame-·L d , e
copy-frame (copy-·R r)   h =
  let (Δ₂ , d , e) = copy-frame r h in Δ₂ , frame-·R d , e
copy-frame (copy-Λ r)    h =
  let (Δ₂ , d , e) = copy-frame r h in Δ₂ , frame-Λ d , e
copy-frame (copy-·[] r)  h =
  let (Δ₂ , d , e) = copy-frame r h in Δ₂ , frame-·[] d , e

------------------------------------------------------------------------
-- 8. THE PER-STEP THEOREM.  From the source position's frame, the
--    target position's frame — at the context the step's store change
--    left — and the scope-map equation.  The ambient's well-formedness
--    is spent only where an allocation's payload must be known well
--    formed (`step-alloc`, `same-wfᴿ`).
------------------------------------------------------------------------

residual-frame : ∀ {Δ δ L L′ C M ρ D N Δ₁} {r : Δ ⊢ L -→ L′ ∣ δ}
  → WfCtx Δ
  → Residual r C M ρ D N
  → Δ ⊢C C ⊣ Δ₁
  → Σ[ Δ₂ ∈ Ctxᵗ ] (apply δ Δ ⊢C D ⊣ Δ₂) × (names Δ₂ ≡ map ρ (names Δ₁))

residual-frame {Δ = Δ} wfΔ (residual-TyBeta {R = R} vN pA)
    (frame-·[] (frame-Λ h)) =
  let (Ξ₂ , d , _) = ⊢C-len (bindR R ∷ reps Δ) refl h
  in _ , frame-⟪⟫ (inst-interior {R = R} empty-interior) d
       , sym (map-idᵗ _)

residual-frame wfΔ (residual-Beta-body {W = W} {A = A} vW st)
    (frame-·L (frame-ƛ h)) =
  _ , ⊢C-substCtx (betaEnv W A) h , sym (map-idᵗ _)

residual-frame wfΔ (residual-Beta-arg vW cr) (frame-·R h) =
  copy-frame cr h

residual-frame wfΔ (residual-Peel-fun vV vW rc ri rd sc)
    (frame-·L (frame-⟪⟫ riᶠ h)) =
  _ , frame-⟪⟫ riᶠ (frame-·L h) , sym (map-idᵗ _)

-- The crossing argument moves VERBATIM: `dual-interior` says the dual's
-- interior IS the exterior the argument was already read at.
residual-frame wfΔ (residual-Peel-arg vV vW rc ri rd sc) (frame-·R h) =
  _ , frame-⟪⟫ ri (frame-·R (frame-⟪⟫ (dual-interior ri) h))
    , sym (map-idᵗ _)

residual-frame {Δ = Δ} wfΔ (residual-TyPeelR-Λ {R = R} vN rc ⊢s pA)
    (frame-·[] (frame-⟪⟫ (interior csᶠ) (frame-Λ h))) =
  let (Ξ₂ , d , _) = ⊢C-len (bindR R ∷ reps Δ) refl h
  in _ , frame-⟪⟫ (inst-interior (interior csᶠ)) d
       , sym (map-idᵗ _)

-- The one mover left inside a redex: the inner boundary is a SIBLING of
-- the `Λ` slot the allocation consumes, so it takes exactly `suc`.
residual-frame {Δ = Δ} wfΔ
    (residual-TyPeelR-⟪⟫ {C = C} {Θ′ = Θ′} {R = R}
      vW ri rc rc′ ri⁺ rc″ sc ⊢s sm pA)
    (frame-·[] (frame-⟪⟫ (interior csᶠ) (frame-⟪⟫ (interior cs′) h))) =
  let w₀ = repwk-alloc {R = R} (same-wfᴿ wfΔ pA)
      ri″ = snoc-lock0-interior-ren w₀ (bindR R , here) (interior cs′)
      (Δ₂ , d₂ , e₂ , _) = ⊢C-ren suc C w₀ refl h
  in Δ₂
   , frame-⟪⟫ (inst-interior (interior csᶠ))
       (frame-·[] (frame-⟪⟫ ri″ d₂))
   , e₂

residual-frame wfΔ (residual-CancelR vV ri rc₁ lX rc⋉ sm rc₂ lY)
    (frame-⟪⟫ ri₂ᶠ (frame-⟪⟫ ri₁ᶠ h)) =
  _ , frame-⟪⟫ (rewind-interior ri₂ᶠ)
        (frame-⟪⟫ (merged-interior ri₂ᶠ ri₁ᶠ) h)
    , sym (map-idᵗ _)

residual-frame wfΔ (residual-IdPush vV ri rc₁ rc⋉ sm rc₂ lY)
    (frame-⟪⟫ ri₂ᶠ (frame-⟪⟫ ri₁ᶠ h)) =
  _ , frame-⟪⟫ (rewind-interior ri₂ᶠ)
        (frame-⟪⟫ (merged-interior ri₂ᶠ ri₁ᶠ) h)
    , sym (map-idᵗ _)

residual-frame wfΔ (residual-ξ-·-l r) (frame-·L h) =
  let (Δ₂ , d , e) = residual-frame wfΔ r h in Δ₂ , frame-·L d , e
residual-frame {δ = δ} wfΔ (residual-ξ-·-l-sib {C = C} r) (frame-·R h) =
  let (Δ₂ , d , e) = ⊢C-shift δ C (step-alloc wfΔ r) h
  in Δ₂ , frame-·R d , e
residual-frame wfΔ (residual-ξ-·-r v r) (frame-·R h) =
  let (Δ₂ , d , e) = residual-frame wfΔ r h in Δ₂ , frame-·R d , e
residual-frame {δ = δ} wfΔ (residual-ξ-·-r-sib {C = C} v r)
    (frame-·L h) =
  let (Δ₂ , d , e) = ⊢C-shift δ C (step-alloc wfΔ r) h
  in Δ₂ , frame-·L d , e
residual-frame wfΔ (residual-ξ-·[] r) (frame-·[] h) =
  let (Δ₂ , d , e) = residual-frame wfΔ r h in Δ₂ , frame-·[] d , e
residual-frame {δ = δ} wfΔ (residual-ξ-⟪⟫ {r = r} ri res)
    (frame-⟪⟫ riᶠ h)
  with interior-functional riᶠ ri
residual-frame {δ = δ} wfΔ (residual-ξ-⟪⟫ {r = r} ri res)
    (frame-⟪⟫ riᶠ h) | refl =
  let wfΔᵢ = interior-wf wfΔ ri
      aw   = aw-reps (interior-reps ri) (step-alloc wfΔᵢ r)
      (Δ₂ , d , e) = residual-frame wfΔᵢ res h
  in Δ₂ , frame-⟪⟫ (interior-apply δ aw ri) d , e

------------------------------------------------------------------------
-- 9. THE THEOREM: compose the per-step equations along the run,
--    re-typing each contractum by preservation and carrying its
--    context's well-formedness by `preservation-wf`.  The run's target
--    position is read at `runCtx rs`, the context the run ends at.
------------------------------------------------------------------------

residuals-color : ∀ {Δ L L′ A₀ C M ρ D N Δ₁ Δ₂} {rs : Δ ⊢ L -→* L′}
  → WfCtx Δ
  → Δ ∣ [] ⊢ L ⦂ A₀
  → Residuals rs C M ρ D N
  → Δ ⊢C C ⊣ Δ₁
  → runCtx rs ⊢C D ⊣ Δ₂
  → names Δ₂ ≡ map ρ (names Δ₁)
residuals-color wf ⊢L residuals-done dC dD =
  trans (cong names (sym (⊢C-functional dC dD))) (sym (map-idᵗ _))
residuals-color wf ⊢L
    (residuals-step {ρ′ = ρ′} {r = r} res rss) dC dD =
  let (Δmid , dmid , e₁) = residual-frame wf res dC
      e₂ = residuals-color (preservation-wf wf ⊢L r)
             (preservation wf ⊢L r) rss dmid dD
  in trans e₂ (trans (cong (map ρ′) e₁) (sym (map-∘ᵣ ρ′ _ _)))

------------------------------------------------------------------------
-- 10. THE COLOR THEOREM proper (Jeremy, 2026-09-21): color is about
--     TYPE variables only — which ordinary names are live at the hole —
--     not the representation variables they denote.  `map ρ` moves only
--     the entries, never a position, so the corollary is the length
--     equation.
------------------------------------------------------------------------

map-length : (f : Renameᵗ) (Δn : TyCtx)
  → length (map f Δn) ≡ length Δn
map-length f []       = refl
map-length f (α ∷ Δn) = cong suc (map-length f Δn)

residuals-color-length : ∀ {Δ L L′ A₀ C M ρ D N Δ₁ Δ₂}
  {rs : Δ ⊢ L -→* L′}
  → WfCtx Δ
  → Δ ∣ [] ⊢ L ⦂ A₀
  → Residuals rs C M ρ D N
  → Δ ⊢C C ⊣ Δ₁
  → runCtx rs ⊢C D ⊣ Δ₂
  → length (names Δ₂) ≡ length (names Δ₁)
residuals-color-length {ρ = ρ} {Δ₁ = Δ₁} wf ⊢L rs dC dD =
  trans (cong length (residuals-color wf ⊢L rs dC dD))
        (map-length ρ (names Δ₁))
