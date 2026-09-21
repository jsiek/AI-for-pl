module strong-rep-store.proof.ColorPreservation where

-- COLOR PRESERVATION — the proof (statement approved by Jeremy,
-- 2026-09-21; strong-rep-store.ColorPreservation states it publicly).
--
-- THE SHAPE.  `residual-frame` is the per-step theorem: from the source
-- position's frame derivation it CONSTRUCTS the target position's, with
-- the scope-map equation `names Δ₂ ≡ map ρ (names Δ₁)`.  Every rule but
-- the two movers is frame-for-frame (the interior lemmas of
-- strong-rep-store.Boundary §3a supply the new boundary frames' readings:
-- `instantiate-interior`, `dual-interior`, `rewind-interior`,
-- `merged-interior`); the movers — Peel's argument, TyPeelR-⟪⟫'s inner
-- boundary, and Beta's copies under `crossΛᴹ` — go through `⊢C-ren`,
-- the transport of a frame derivation along a representation-only
-- renaming, whose boundary case is `interior-ren`/`RepWk` (Boundary
-- §3d) and whose conclusion is exactly the `holeRen²` the residual's ρ
-- index records.  `residuals-color` composes the per-step equations
-- along `ρ′ ∘ ρ`, re-typing each intermediate term by `preservation` —
-- which is where the theorem's `WfCtx Δ` premise is spent.
--
-- The typing premise is spent at exactly two sites: Peel's argument
-- (the bind block it crosses must be well-formed for `repwk-wkN`, and
-- the redex's own `env` carries that as `bw-binds`) and TyPeelR-⟪⟫
-- (the instantiated store's well-formedness, via
-- `instantiate-boundarywf`).

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
  using (repwk-cons₀; repwk-abst₀; repwk-abst; repwk-push;
         fresh-zero-shift; shiftRVars-0)
open import strong-rep-store.proof.RepWeaken using (repwk-wkN; wkN-+)
open import strong-rep-store.proof.Preserve
  using (empty-interior; instantiate-boundarywf)
open import strong-rep-store.Preservation using (preservation)

private
  variable
    Γ Γ′ Δ Δ′ Δᵢ Δ₁ Δ₂ : Ctxᵗ
    Ξ Ξ′ : RepCtx
    Δn Δn′ : TyCtx
    δ : Change
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

map-≗ : {f g : Renameᵗ} → (∀ α → f α ≡ g α)
  → (Δn : TyCtx) → map f Δn ≡ map g Δn
map-≗ h []       = refl
map-≗ h (α ∷ Δn) = cong₂ _∷_ (h α) (map-≗ h Δn)

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
  → Ξ ∣ Δn ⊢δ δ ⇒ Δn′ → Ξ′ ∣ Δn ⊢δ δ ⇒ Δn′
step-len eq (step-lock v d f)   = step-lock (∋ʳ-len eq v) d f
step-len eq (step-unlock v f i) = step-unlock (∋ʳ-len eq v) f i

changes-len : length Ξ ≡ length Ξ′
  → Ξ ∣ Δn ⊢χ χ ⇒ Δn′ → Ξ′ ∣ Δn ⊢χ χ ⇒ Δn′
changes-len eq changes[]        = changes[]
changes-len eq (changes∷ cs st) =
  changes∷ (changes-len eq cs) (step-len eq st)

pushRepBinds-len : (Rs : List Ty) → length Ξ ≡ length Ξ′
  → length (pushRepBinds Rs Ξ) ≡ length (pushRepBinds Rs Ξ′)
pushRepBinds-len []       eq = eq
pushRepBinds-len (R ∷ Rs) eq = cong suc (pushRepBinds-len Rs eq)

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
⊢C-len Ξ′ eq (frame-⟪⟫ {Θ = Θ} (interior cs) d) =
  let (Ξ₂ , d′ , l) = ⊢C-len (pushRepBinds (binds Θ) Ξ′)
                        (pushRepBinds-len (binds Θ) eq) d
  in Ξ₂
   , frame-⟪⟫ (interior (changes-len (pushRepBinds-len (binds Θ) eq) cs))
       d′
   , l

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
  → underΛ Γ ⊢ⁱ boundary [] (lock 0 0 ∷ [])
      ⇒ ((abstR ∷ reps Γ) ∣ shiftNames (names Γ))
crossΛ-interior Γ =
  interior (changes∷ changes[]
    (subst (λ D → (abstR ∷ reps Γ) ∣ D ⊢δ lock 0 0
                    ⇒ shiftNames (names Γ))
           (sym (shiftRVars-0 _))
           (step-lock (abstR , here) del-here fresh-zero-shift)))

------------------------------------------------------------------------
-- 6. THE TRANSPORT: a frame derivation moves along a representation-only
--    renaming, and the hole's scope map moves by exactly the renaming
--    `holeRen²` delivers there.  The boundary case is `interior-ren`.
------------------------------------------------------------------------

⊢C-ren : ∀ (ρ² : TyRename) {Γ Γ′ Δ₁} (C : TermCtx)
  → (∀ X → ordinary ρ² X ≡ X)
  → RepWk (represent ρ²) (reps Γ) (reps Γ′)
  → names Γ′ ≡ map (represent ρ²) (names Γ)
  → Γ ⊢C C ⊣ Δ₁
  → Σ[ Δ₂ ∈ Ctxᵗ ] (Γ′ ⊢C renCtx² ρ² C ⊣ Δ₂)
      × (names Δ₂ ≡ map (represent (holeRen² ρ² C)) (names Δ₁))
      × RepWk (represent (holeRen² ρ² C)) (reps Δ₁) (reps Δ₂)
⊢C-ren ρ² □ ord w eq frame-□ = _ , frame-□ , eq , w
⊢C-ren ρ² (ƛC A ∙ C) ord w eq (frame-ƛ d) =
  let (Δ₂ , d′ , e , w′) = ⊢C-ren ρ² C ord w eq d
  in Δ₂ , frame-ƛ d′ , e , w′
⊢C-ren ρ² (C ·L N) ord w eq (frame-·L d) =
  let (Δ₂ , d′ , e , w′) = ⊢C-ren ρ² C ord w eq d
  in Δ₂ , frame-·L d′ , e , w′
⊢C-ren ρ² (L ·R C) ord w eq (frame-·R d) =
  let (Δ₂ , d′ , e , w′) = ⊢C-ren ρ² C ord w eq d
  in Δ₂ , frame-·R d′ , e , w′
⊢C-ren ρ² (C ·C[ B , A ]) ord w eq (frame-·[] d) =
  let (Δ₂ , d′ , e , w′) = ⊢C-ren ρ² C ord w eq d
  in Δ₂ , frame-·[] d′ , e , w′
⊢C-ren ρ² {Γ = Γ} {Γ′ = Γ′} (ΛC C) ord w eq (frame-Λ d) =
  let (Δ₂ , d′ , e , w′) =
        ⊢C-ren (underΛ-ren ρ²) C
          (λ { zero → refl ; (suc X) → cong suc (ord X) })
          (repwk-abst w)
          (cong₂ _∷_ refl
            (trans (cong (map suc) eq)
                   (map-suc-ext (represent ρ²) (names Γ))))
          d
  in Δ₂ , frame-Λ d′ , e , w′
⊢C-ren ρ² {Γ = Γ} {Γ′ = Γ′} (C ⟪C Θ , c ⟫) ord w eq
    (frame-⟪⟫ (interior {Δ′ = Δ′} cs) d) =
  let Γᵢ′ = pushRepBinds (map (renameᵗ (represent ρ²)) (binds Θ))
              (reps Γ′)
              ∣ map (extN (numBinds Θ) (represent ρ²)) Δ′
      ri₁ = interior-ren w (interior cs)
      ri₂ = subst (λ D → (reps Γ′ ∣ D) ⊢ⁱ renᴮᴿ (represent ρ²) Θ ⇒ Γᵢ′)
                  (sym eq) ri₁
      ri₃ = subst (λ B → Γ′ ⊢ⁱ B ⇒ Γᵢ′)
                  (sym (renᴮ²-ord-id ord Θ)) ri₂
      (Δ₂ , d′ , e , w′) =
        ⊢C-ren (underReps-ren (numBinds Θ) ρ²) C ord
          (repwk-push w (binds Θ)) refl d
  in Δ₂ , frame-⟪⟫ ri₃ d′ , e , w′


------------------------------------------------------------------------
-- 7. The copies: `Beta`'s argument, followed to each occurrence.  The
--    ambient at depth k is `underΛᵏ k` of the redex's, and each `Λ`
--    crossed contributes one `crossΛ-interior` frame and one `moveᴿ suc`
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
image-frame {Δ = Δ} (image-Λ {A = A} {k = k} {D = D} r) h =
  let (Δ′ , d , e) = image-frame {Δ = Δ} r h
      (Δ₂ , d₂ , e₂ , _) =
        ⊢C-ren (moveᴿ suc) D (λ X → refl) repwk-abst₀ refl d
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
--    target position's frame and the scope-map equation.  The typing
--    premise is inverted only where a bind block's well-formedness is
--    needed (Peel's argument, TyPeelR-⟪⟫).
------------------------------------------------------------------------

residual-frame : ∀ {Δ L L′ A₀ C M ρ D N Δ₁} {r : Δ ⊢ L -→ L′}
  → Δ ∣ [] ⊢ L ⦂ A₀
  → Residual r C M ρ D N
  → Δ ⊢C C ⊣ Δ₁
  → Σ[ Δ₂ ∈ Ctxᵗ ] (Δ ⊢C D ⊣ Δ₂) × (names Δ₂ ≡ map ρ (names Δ₁))

residual-frame {Δ = Δ} ⊢L (residual-TyBeta {R = R} vN pA)
    (frame-·[] (frame-Λ h)) =
  let (Ξ₂ , d , _) = ⊢C-len (bindR (shiftBy 0 R) ∷ reps Δ) refl h
  in _ , frame-⟪⟫ (instantiate-interior empty-interior) d
       , sym (map-idᵗ _)

residual-frame ⊢L (residual-Beta-body {W = W} {A = A} vW st)
    (frame-·L (frame-ƛ h)) =
  _ , ⊢C-substCtx (betaEnv W A) h , sym (map-idᵗ _)

residual-frame ⊢L (residual-Beta-arg vW cr) (frame-·R h) =
  copy-frame cr h

residual-frame ⊢L (residual-Peel-fun vV vW rc ri rd sc)
    (frame-·L (frame-⟪⟫ riᶠ h)) =
  _ , frame-⟪⟫ riᶠ (frame-·L h) , sym (map-idᵗ _)

residual-frame {Δ = Δ}
    (⊢· (env mwΘ ⊢V ⊢c smᵢ smₑ wE) ⊢W)
    (residual-Peel-arg {Θ = Θ} {C = C} vV vW rc ri rd sc)
    (frame-·R h) =
  let (Δ₂ , d₂ , e₂ , _) =
        ⊢C-ren (moveᴿ (wkN (numBinds Θ))) C (λ X → refl)
          (repwk-wkN (binds Θ) (bw-binds mwΘ))
          (map-≗ (λ α → sym (wkN-+ (numBinds Θ) α)) (names Δ))
          h
  in Δ₂ , frame-⟪⟫ ri (frame-·R (frame-⟪⟫ (dual-interior ri) d₂)) , e₂

residual-frame (⊢·[] (env mwΘ ⊢N ⊢c′ smᵢ′ smₑ′ wE′) wA)
    (residual-TyPeelR-Λ {Θ = Θ} {R = R} vN rc ⊢s pA)
    (frame-·[] (frame-⟪⟫ {Δᵢ = Δᵢᶠ} riᶠ (frame-Λ h))) =
  let (Ξ₂ , d , _) =
        ⊢C-len (bindR (shiftBy (numBinds Θ) R) ∷ reps Δᵢᶠ) refl h
  in _ , frame-⟪⟫ (instantiate-interior riᶠ) d , sym (map-idᵗ _)

residual-frame (⊢·[] (env mwΘ ⊢N ⊢c′ smᵢ′ smₑ′ wE′) wA)
    (residual-TyPeelR-⟪⟫ {Θ = Θ} {C = C} {Θ′ = Θ′} {R = R}
      vW ri rc rc′ ri⁺ rc″ sc ⊢s sm pA)
    (frame-·[] (frame-⟪⟫ {Δᵢ = Δᵢ⁰} riᶠ
       (frame-⟪⟫ ri′@(interior {Δ′ = Δ′ᶜˢ} cs′) h)))
  with interior-functional (bw-interior mwΘ) riᶠ
residual-frame (⊢·[] (env mwΘ ⊢N ⊢c′ smᵢ′ smₑ′ wE′) wA)
    (residual-TyPeelR-⟪⟫ {Θ = Θ} {C = C} {Θ′ = Θ′} {R = R}
      vW ri rc rc′ ri⁺ rc″ sc ⊢s sm pA)
    (frame-·[] (frame-⟪⟫ {Δᵢ = Δᵢ⁰} riᶠ
       (frame-⟪⟫ ri′@(interior {Δ′ = Δ′ᶜˢ} cs′) h)))
    | refl =
  let b₀ = bindR (shiftBy (numBinds Θ) R)
      wr = wf-reps (bw-interior-wf (instantiate-boundarywf mwΘ pA))
      w₀ = repwk-cons₀ b₀ (λ _ → wr)
      Δᵢ″ = pushRepBinds (map (renameᵗ suc) (binds Θ′)) (b₀ ∷ reps Δᵢ⁰)
              ∣ map (extN (numBinds Θ′) suc) Δ′ᶜˢ
      ri″₀ = addLock0-interior-ren w₀ (b₀ , here) ri′
      ri″ = subst (λ B → ((b₀ ∷ reps Δᵢ⁰)
                            ∣ (zero ∷ shiftNames (names Δᵢ⁰)))
                          ⊢ⁱ addLock0 B ⇒ Δᵢ″)
                  (sym (renᴮ²-ord-id (λ X → refl) Θ′)) ri″₀
      (Δ₂ , d₂ , e₂ , _) =
        ⊢C-ren (moveᴿ (extN (numBinds Θ′) suc)) C (λ X → refl)
          (repwk-push w₀ (binds Θ′)) refl h
  in Δ₂
   , frame-⟪⟫ (instantiate-interior riᶠ) (frame-·[] (frame-⟪⟫ ri″ d₂))
   , e₂

residual-frame ⊢L (residual-CancelR vV ri rc₁ lX rc⋉ sm rc₂ lY)
    (frame-⟪⟫ ri₂ᶠ (frame-⟪⟫ ri₁ᶠ h)) =
  _ , frame-⟪⟫ (rewind-interior ri₂ᶠ)
        (frame-⟪⟫ (merged-interior ri₂ᶠ ri₁ᶠ) h)
    , sym (map-idᵗ _)

residual-frame ⊢L (residual-IdPush vV ri rc₁ rc⋉ sm rc₂ lY)
    (frame-⟪⟫ ri₂ᶠ (frame-⟪⟫ ri₁ᶠ h)) =
  _ , frame-⟪⟫ (rewind-interior ri₂ᶠ)
        (frame-⟪⟫ (merged-interior ri₂ᶠ ri₁ᶠ) h)
    , sym (map-idᵗ _)

residual-frame (⊢· ⊢f ⊢a) (residual-ξ-·-l r) (frame-·L h) =
  let (Δ₂ , d , e) = residual-frame ⊢f r h in Δ₂ , frame-·L d , e
residual-frame ⊢L (residual-ξ-·-l-sib r) (frame-·R h) =
  _ , frame-·R h , sym (map-idᵗ _)
residual-frame (⊢· ⊢f ⊢a) (residual-ξ-·-r v r) (frame-·R h) =
  let (Δ₂ , d , e) = residual-frame ⊢a r h in Δ₂ , frame-·R d , e
residual-frame ⊢L (residual-ξ-·-r-sib v r) (frame-·L h) =
  _ , frame-·L h , sym (map-idᵗ _)
residual-frame (⊢·[] ⊢f wA) (residual-ξ-·[] r) (frame-·[] h) =
  let (Δ₂ , d , e) = residual-frame ⊢f r h in Δ₂ , frame-·[] d , e
residual-frame (env mwΘ ⊢N ⊢c smᵢ smₑ wE)
    (residual-ξ-⟪⟫ ri r) (frame-⟪⟫ riᶠ h)
  with interior-functional riᶠ (bw-interior mwΘ)
     | interior-functional ri (bw-interior mwΘ)
residual-frame (env mwΘ ⊢N ⊢c smᵢ smₑ wE)
    (residual-ξ-⟪⟫ ri r) (frame-⟪⟫ riᶠ h)
    | refl | refl =
  let (Δ₂ , d , e) = residual-frame ⊢N r h in Δ₂ , frame-⟪⟫ riᶠ d , e

------------------------------------------------------------------------
-- 9. THE THEOREM: compose the per-step equations along the run,
--    re-typing each contractum by preservation — the well-formedness
--    premise is spent there and nowhere else.
------------------------------------------------------------------------

residuals-color : ∀ {Δ L L′ A₀ C M ρ D N Δ₁ Δ₂} {rs : Δ ⊢ L -→* L′}
  → WfCtx Δ
  → Δ ∣ [] ⊢ L ⦂ A₀
  → Residuals rs C M ρ D N
  → Δ ⊢C C ⊣ Δ₁
  → Δ ⊢C D ⊣ Δ₂
  → names Δ₂ ≡ map ρ (names Δ₁)
residuals-color wf ⊢L residuals-done dC dD =
  trans (cong names (sym (⊢C-functional dC dD))) (sym (map-idᵗ _))
residuals-color wf ⊢L
    (residuals-step {ρ′ = ρ′} {r = r} res rss) dC dD =
  let (Δmid , dmid , e₁) = residual-frame ⊢L res dC
      e₂ = residuals-color wf (preservation wf ⊢L r) rss dmid dD
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
  → Δ ⊢C D ⊣ Δ₂
  → length (names Δ₂) ≡ length (names Δ₁)
residuals-color-length {ρ = ρ} {Δ₁ = Δ₁} wf ⊢L rs dC dD =
  trans (cong length (residuals-color wf ⊢L rs dC dD))
        (map-length ρ (names Δ₁))
