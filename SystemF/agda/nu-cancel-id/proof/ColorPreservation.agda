module nu-cancel-id.proof.ColorPreservation where

-- File Charter:
--   * THE PROOF OF COLOR PRESERVATION: a residual's scope map is the
--     original one, renamed by the residual's ρ (`color`, `color*`).
--   * §1 list facts.  §2 the scope map after inserting an unnamed cell
--     (`hole-ins`): it is the old map renamed.  This covers a sibling
--     of an allocation and a copy that `crossΛ` moves under a `Λ`.
--     §3 the flags at a hole, before and after: Beta's substitution
--     keeps the frames, and TyBeta's instantiation trades the `Λ` for
--     the allocated cell.  §4 one step.  §5 a run.
--   * Typing is used only for COHERENCE at the redex: CancelId,
--     Cancel-□ and Wrap's argument restore the exterior flags because
--     the redex's cell has the flag its entry needs outside.  Sink,
--     Swap and Push commute entries for different cells (`setFlag-comm`).

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym)
open import Relation.Nullary using (yes; no)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction
open import nu-cancel-id.Residual
open import nu-cancel-id.proof.Types using (extⁿ)
open import nu-cancel-id.proof.Flags
open import nu-cancel-id.proof.Preservation using (preservation)

private
  variable
    Φ Ψ : Flags

------------------------------------------------------------------------
-- 1. Lists
------------------------------------------------------------------------

map-idʳ : ∀ (xs : List ℕ) → xs ≡ map idʳ xs
map-idʳ []       = refl
map-idʳ (x ∷ xs) = cong (x ∷_) (map-idʳ xs)

map-comp : ∀ (ρ σ : Renameᵗ) (xs : List ℕ)
  → map σ (map ρ xs) ≡ map (λ x → σ (ρ x)) xs
map-comp ρ σ []       = refl
map-comp ρ σ (x ∷ xs) = cong (σ (ρ x) ∷_) (map-comp ρ σ xs)

map-suc-ext : ∀ (ρ : Renameᵗ) (xs : List ℕ)
  → map suc (map ρ xs) ≡ map (extᵗ ρ) (map suc xs)
map-suc-ext ρ []       = refl
map-suc-ext ρ (x ∷ xs) = cong (suc (ρ x) ∷_) (map-suc-ext ρ xs)

------------------------------------------------------------------------
-- 2. Inserting an unnamed cell renames the scope map
------------------------------------------------------------------------

names-ins : ∀ k Φ → names (insᶠ k Φ) ≡ map (extⁿ k suc) (names Φ)
names-ins zero    Φ           = refl
names-ins (suc k) []          = refl
names-ins (suc k) (true ∷ Φ)  =
  cong (zero ∷_) (trans (cong (map suc) (names-ins k Φ))
                        (map-suc-ext (extⁿ k suc) (names Φ)))
names-ins (suc k) (false ∷ Φ) =
  trans (cong (map suc) (names-ins k Φ))
        (map-suc-ext (extⁿ k suc) (names Φ))

hole-ins : ∀ k Φ C
  → names (holeFlags (insᶠ k Φ) (renCtx (extⁿ k suc) C))
    ≡ map (holeᴿ (extⁿ k suc) C) (names (holeFlags Φ C))
hole-ins k Φ □                    = names-ins k Φ
hole-ins k Φ (ƛC A ∙ C)           = hole-ins k Φ C
hole-ins k Φ (C ·L N)             = hole-ins k Φ C
hole-ins k Φ (L ·R C)             = hole-ins k Φ C
hole-ins k Φ (ΛC C)               = hole-ins (suc k) (true ∷ Φ) C
hole-ins k Φ (νC A · C ⟨ c ⟩)     = hole-ins k Φ C
hole-ins k Φ ([ s , α ]C C ⟨ c ⟩) =
  trans (cong (λ Ψ → names (holeFlags Ψ (renCtx (extⁿ k suc) C)))
              (sym (ins-setFlag k α (inside s) Φ)))
        (hole-ins k (setFlag α (inside s) Φ) C)

-- a sibling of a step
sibling : ∀ a Γ C
  → names (holeFlags (flags (a ⨾ Γ)) (↑ᶜ a C))
    ≡ map (↑ʳ a C) (names (holeFlags (flags Γ) C))
sibling keep    Γ C = map-idʳ _
sibling (new P) Γ C = hole-ins 0 (flags Γ) C

------------------------------------------------------------------------
-- 3. The flags at a hole, before and after
------------------------------------------------------------------------

subst-flags : ∀ j V Φ C → holeFlags Φ (substCtx j V C) ≡ holeFlags Φ C
subst-flags j V Φ □                    = refl
subst-flags j V Φ (ƛC A ∙ C)           = subst-flags (suc j) V Φ C
subst-flags j V Φ (C ·L N)             = subst-flags j V Φ C
subst-flags j V Φ (L ·R C)             = subst-flags j V Φ C
subst-flags j V Φ (ΛC C)               = subst-flags j (crossΛ V) _ C
subst-flags j V Φ (νC A · C ⟨ c ⟩)     = subst-flags j V Φ C
subst-flags j V Φ ([ s , α ]C C ⟨ c ⟩) = refl

-- the allocated cell, revealed, stands where the `Λ` named its cell
inst-flags : ∀ {C D} Φ → C •ᶜ⟶ D → holeFlags (true ∷ Φ) D ≡ holeFlags Φ C
inst-flags Φ instᶜ-Λ                      = refl
inst-flags Φ (instᶜ-∀ {s = s} {α = α} ic) =
  inst-flags (setFlag α (inside s) Φ) ic
inst-flags Φ (instᶜ-id {s = s} {α = α} ic) =
  inst-flags (setFlag α (inside s) Φ) ic

-- an image of a copy, under k `Λ`s
image-color : ∀ {k C M ρ D N} Φ
  → ImageResidual k C M ρ D N
  → names (holeFlags (trues k Φ) D) ≡ map ρ (names (holeFlags Φ C))
image-color Φ image-here = map-idʳ _
image-color {k = suc k} Φ (image-Λ {ρ = ρ} {C = C} {D = D} i) =
  trans (hole-ins 0 (trues k Φ) D)
        (trans (cong (map (holeᴿ suc D)) (image-color Φ i))
               (map-comp ρ (holeᴿ suc D) (names (holeFlags Φ C))))

copy-color : ∀ {k j Q C M ρ D N} Φ
  → CopyResidual k j Q C M ρ D N
  → names (holeFlags (trues k Φ) D) ≡ map ρ (names (holeFlags Φ C))
copy-color Φ (copy-var h i) = image-color Φ i
copy-color Φ (copy-ƛ c)     = copy-color Φ c
copy-color Φ (copy-·L c)    = copy-color Φ c
copy-color Φ (copy-·R c)    = copy-color Φ c
copy-color Φ (copy-Λ c)     = copy-color Φ c
copy-color Φ (copy-ν c)     = copy-color Φ c

-- equal flags give the same map, renamed by the identity
same : ∀ {Ψ Ψ′} → Ψ ≡ Ψ′ → names Ψ ≡ map idʳ (names Ψ′)
same refl = map-idʳ _

-- equal flags above a hole give equal flags at the hole
sameAt : ∀ {Ψ Ψ′} C → Ψ ≡ Ψ′
  → names (holeFlags Ψ C) ≡ map idʳ (names (holeFlags Ψ′ C))
sameAt C eq = same (cong (λ Ψ → holeFlags Ψ C) eq)

inside-flip : ∀ s → inside (flip s) ≡ outside s
inside-flip ⁺ = refl
inside-flip ⁻ = refl

-- a second entry on the same cell undoes the first, by coherence
undo : ∀ {α b} s Φ → Φ ∋ᶠ α ⦂ outside s
  → setFlag α (inside (flip s)) (setFlag α b Φ) ≡ Φ
undo {α = α} {b = b} s Φ coh
  rewrite setFlag-twice α (inside (flip s)) b Φ | inside-flip s =
  setFlag-idem coh

-- the alloc moves the boundary's cell and the context alike
interior-alloc : ∀ a s α Γ
  → flags (a ⨾ interior s α Γ)
    ≡ setFlag (↑ᵛ a α) (inside s) (flags (a ⨾ Γ))
interior-alloc keep    s α Γ = refl
interior-alloc (new P) s α Γ = refl

------------------------------------------------------------------------
-- 4. One step
------------------------------------------------------------------------

color : ∀ {Γ Γₜ L L′ a A} {r : Γ ⊢ L ⟶ L′ ∣ a} {C M ρ D N}
  → Γ ∣ Γₜ ⊢ L ⦂ A
  → Residual r C M ρ D N
  → names (holeFlags (flags (a ⨾ Γ)) D)
    ≡ map ρ (names (holeFlags (flags Γ) C))
color {Γ = Γ} _ (residual-β-body {W = W} {C = C} w nh) =
  same (subst-flags 0 W (flags Γ) C)
color {Γ = Γ} _ (residual-β-arg w c) = copy-color (flags Γ) c
color _ (residual-wrap-fun {C = C} v w) = sameAt C refl
color {Γ = Γ} (⊢· (⊢[] coh _ _ _ _) _)
    (residual-wrap-arg {s = s} {α = α} {C = C} v w) =
  sameAt C (undo s (flags Γ) coh)
color _ (residual-wrap-id-fun {C = C} u w) = sameAt C refl
color {Γ = Γ} (⊢· (⊢[] coh _ _ _ _) _)
    (residual-wrap-id-arg {s = s} {α = α} {C = C} u w) =
  sameAt C (undo s (flags Γ) coh)
color {Γ = Γ} _ (residual-tyβ {C = C} sp v i ic) =
  same (inst-flags (flags Γ) ic)
color {Γ = Γ} (⊢[] coh _ _ _ _) (residual-cancel-□ {C = C} w) =
  sameAt C (sym (undo ⁺ (flags Γ) coh))
color {Γ = Γ} (⊢[] coh _ _ _ _) (residual-cancel-id {C = C} u) =
  sameAt C (sym (undo ⁻ (flags Γ) coh))
color {Γ = Γ} _ (residual-sink {C = C} α≢β v) =
  sameAt C (setFlag-comm false false (flags Γ) α≢β)
color {Γ = Γ} _ (residual-swap {C = C} α≢β v) =
  sameAt C (setFlag-comm false true (flags Γ) α≢β)
color {Γ = Γ} _ (residual-push {α = α} {β = β} {C = C} v) with α ≟ β
... | yes refl = sameAt C refl
... | no α≢β   = sameAt C (setFlag-comm true true (flags Γ) α≢β)
color (⊢· ⊢L _) (residual-ξ-·₁ res) = color ⊢L res
color {Γ = Γ} {a = a} _ (residual-ξ-·₁-sib {C = C} r) = sibling a Γ C
color (⊢· _ ⊢M) (residual-ξ-·₂ v res) = color ⊢M res
color {Γ = Γ} {a = a} _ (residual-ξ-·₂-sib {C = C} v r) = sibling a Γ C
color (⊢ν _ ⊢L _ _ _) (residual-ξ-ν res) = color ⊢L res
color {Γ = Γ} {a = a} (⊢[] _ ⊢M _ _ _)
    (residual-ξ-[] {s = s} {α = α} {D = D} res) =
  trans (cong (λ Ψ → names (holeFlags Ψ D)) (sym (interior-alloc a s α Γ)))
        (color ⊢M res)

------------------------------------------------------------------------
-- 5. A run: each step's map composes, and preservation types the tail
------------------------------------------------------------------------

color* : ∀ {Γ Γ′ L L′ A} {rs : Γ ⊢ L —↠ L′ ⊣ Γ′} {C M ρ E O}
  → Γ ∣ [] ⊢ L ⦂ A
  → Residuals rs C M ρ E O
  → names (holeFlags (flags Γ′) E) ≡ map ρ (names (holeFlags (flags Γ) C))
color* _ residuals-done = map-idʳ _
color* {Γ = Γ} ⊢L
    (residuals-step {ρ = ρ} {ρ′ = ρ′} {C = C} {r = r} res rest) =
  trans (color* (preservation ⊢L r) rest)
        (trans (cong (map ρ′) (color ⊢L res))
               (map-comp ρ ρ′ (names (holeFlags (flags Γ) C))))
