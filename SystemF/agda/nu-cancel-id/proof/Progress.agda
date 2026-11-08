module nu-cancel-id.proof.Progress where

-- File Charter:
--   * THE PROGRESS PROOF of νF₁ᶜ with named types (notes/CancelIdSketch.md
--     §8 in strong-rep-nu).
--   * The flag and spelling lemmas are nu-cancel-id.proof.Flags: an
--     entry's own flag is set in its interior, so a second coherent entry
--     for the same cell with the same sign is impossible; spelling is
--     functional.  §3 canonical forms: a
--     functional value's type never reads as a cell, a sealed value's
--     always does, and a `∀`-typed value can be instantiated.  §4 the
--     boundary cases: an unseal's body is its seal (Cancel-□) or a
--     reveal it moves through (Push); a hide carrying `idᶜ` over a
--     sealed value sinks, swaps or cancels.  §5 progress, by induction
--     on the typing derivation.

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (_,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction
open import nu-cancel-id.proof.Flags

private
  variable
    Γ : Ctx
    Γₜ : List Ty
    Φ : Flags
    α β X : ℕ
    b b′ b″ : Bool
    A R R′ : Ty
    F V : Term

------------------------------------------------------------------------
-- 3. Canonical forms
------------------------------------------------------------------------

arrow≢var : ∀ {R S} → R ⇒ S ≡ ` α → ⊥
arrow≢var ()

forall≢var : ∀ {R} → `∀ R ≡ ` α → ⊥
forall≢var ()

-- a functional value's type never reads as a cell
fun-not-var : Fun F
  → Γ ∣ Γₜ ⊢ F ⦂ A
  → flags Γ ⊢ A ⇝ ` α
  → ⊥
fun-not-var F-ƛ         (⊢ƛ _ _) ()
fun-not-var F-Λ         (⊢Λ _)   ()
fun-not-var (F-↦ _)     (⊢[] _ _ _ spB (c-fun _ _)) sp =
  arrow≢var (⇝-unique spB sp)
fun-not-var (F-∀ _)     (⊢[] _ _ _ spB (c-all _)) sp =
  forall≢var (⇝-unique spB sp)
fun-not-var (F-id⁺ F)   (⊢[] _ ⊢F spA spB c-id) sp
  with ⇝-unique spB sp
fun-not-var (F-id⁺ F)   (⊢[] _ ⊢F spA spB c-id) sp | refl =
  fun-not-var F ⊢F spA
fun-not-var (F-id⁻ F _) (⊢[] _ ⊢F spA spB c-id) sp
  with ⇝-unique spB sp
fun-not-var (F-id⁻ F _) (⊢[] _ ⊢F spA spB c-id) sp | refl =
  fun-not-var F ⊢F spA

-- a sealed value's type reads as a cell
sealed-var : Sealed V
  → Γ ∣ Γₜ ⊢ V ⦂ A
  → flags Γ ⊢ A ⇝ R
  → ∃[ α ] R ≡ ` α
sealed-var (S-seal _) (⊢[] _ _ _ spB (c-seal _)) sp =
  _ , ⇝-unique sp spB
sealed-var (S-rev v) (⊢[] _ ⊢V spA spB c-id) sp
  with ⇝-unique spB sp
sealed-var (S-rev v) (⊢[] _ ⊢V spA spB c-id) sp | refl =
  sealed-var v ⊢V spA

-- so its type is never an arrow or a `∀`: read the type where the
-- outer boundary reads it
sealed-not-⇒ : ∀ {B C} → Sealed V → Γ ∣ Γₜ ⊢ V ⦂ B ⇒ C → ⊥
sealed-not-⇒ v ⊢V@(⊢[] _ _ _ spB _) with sealed-var v ⊢V spB
sealed-not-⇒ v (⊢[] _ _ _ (s-⇒ _ _) _) | _ , ()

sealed-not-∀ : ∀ {C} → Sealed V → Γ ∣ Γₜ ⊢ V ⦂ `∀ C → ⊥
sealed-not-∀ v ⊢V@(⊢[] _ _ _ spB _) with sealed-var v ⊢V spB
sealed-not-∀ v (⊢[] _ _ _ (s-∀ _) _) | _ , ()

inst : ∀ {C}
  → Value V
  → Γ ∣ Γₜ ⊢ V ⦂ `∀ C
  → ∃[ N ] V •⟶ N
inst V-$                 ()
inst (V-fun F-ƛ)         ()
inst (V-fun F-Λ)         (⊢Λ _) = _ , inst-Λ
inst (V-fun (F-↦ _))     (⊢[] _ _ _ (s-∀ _) ())
inst (V-fun (F-∀ v))     (⊢[] _ ⊢V (s-∀ _) _ (c-all _)) =
  let (N , i) = inst v ⊢V in _ , inst-∀ i
inst (V-fun (F-id⁺ F))   (⊢[] _ ⊢V (s-∀ _) (s-∀ _) c-id) =
  let (N , i) = inst (V-fun F) ⊢V in _ , inst-id i
inst (V-fun (F-id⁻ F _)) (⊢[] _ ⊢V (s-∀ _) (s-∀ _) c-id) =
  let (N , i) = inst (V-fun F) ⊢V in _ , inst-id i
inst (V-sealed v)        ⊢V = ⊥-elim (sealed-not-∀ v ⊢V)

------------------------------------------------------------------------
-- 4. Boundaries and applications whose subterms are values
------------------------------------------------------------------------

-- An unseal's body has a type that reads as α where α is named, so it
-- is a sealed value: α's own seal, or a reveal of another cell.
unseal-step : ∀ {Γ α V A}
  → Value V
  → interior ⁺ α Γ ∣ [] ⊢ V ⦂ A
  → flags (interior ⁺ α Γ) ⊢ A ⇝ ` α
  → Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ [ ⁺ , α ] V ⟨ unseal ⟩ ⟶ N ∣ a)
unseal-step V-$ ⊢nat  ()
unseal-step V-$ ⊢bool ()
unseal-step (V-fun F) ⊢V sp = ⊥-elim (fun-not-var F ⊢V sp)
unseal-step (V-sealed (S-seal w)) (⊢[] _ _ _ spB (c-seal _)) sp
  with ⇝-unique spB sp
unseal-step (V-sealed (S-seal w)) (⊢[] _ _ _ spB (c-seal _)) sp | refl =
  _ , _ , cancel-□ w
unseal-step (V-sealed (S-rev v)) ⊢V sp = _ , _ , push v

-- `[ ⁻ , α ] F ⟨ idᶜ ⟩` over a functional value: CancelId exactly when F
-- reveals α with `idᶜ`
id⁻-fun : ∀ {Γ α F}
  → Fun F
  → Value ([ ⁻ , α ] F ⟨ idᶜ ⟩)
    ⊎ Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ [ ⁻ , α ] F ⟨ idᶜ ⟩ ⟶ N ∣ a)
id⁻-fun F-ƛ          = inj₁ (V-fun (F-id⁻ F-ƛ (λ ())))
id⁻-fun F-Λ          = inj₁ (V-fun (F-id⁻ F-Λ (λ ())))
id⁻-fun (F-↦ v)      = inj₁ (V-fun (F-id⁻ (F-↦ v) (λ ())))
id⁻-fun (F-∀ v)      = inj₁ (V-fun (F-id⁻ (F-∀ v) (λ ())))
id⁻-fun (F-id⁻ F nr) = inj₁ (V-fun (F-id⁻ (F-id⁻ F nr) (λ ())))
id⁻-fun {α = α} (F-id⁺ {α = β} F) with β ≟ α
id⁻-fun {α = α} (F-id⁺ {α = β} F) | yes refl =
  inj₂ (_ , _ , cancel-id (V-fun F))
id⁻-fun {α = α} (F-id⁺ {α = β} F) | no β≢α =
  inj₁ (V-fun (F-id⁻ (F-id⁺ F) (λ { refl → β≢α refl })))

-- `[ ⁻ , α ] V ⟨ idᶜ ⟩` over a sealed value: Sink, Swap or CancelId
id⁻-sealed : ∀ {Γ α V A}
  → flags Γ ∋ᶠ α ⦂ true
  → Sealed V
  → interior ⁻ α Γ ∣ [] ⊢ V ⦂ A
  → Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ [ ⁻ , α ] V ⟨ idᶜ ⟩ ⟶ N ∣ a)
id⁻-sealed {α = α} coh (S-seal {α = β} w) ⊢V with α ≟ β
id⁻-sealed {α = α} coh (S-seal {α = β} w) (⊢[] coh′ _ _ _ _) | yes refl =
  ⊥-elim (false≢true (flag-clash coh coh′))
id⁻-sealed {α = α} coh (S-seal {α = β} w) ⊢V | no α≢β =
  _ , _ , sink α≢β w
id⁻-sealed {α = α} coh (S-rev {α = β} v) ⊢V with α ≟ β
id⁻-sealed {α = α} coh (S-rev {α = β} v) ⊢V | yes refl =
  _ , _ , cancel-id (V-sealed v)
id⁻-sealed {α = α} coh (S-rev {α = β} v) ⊢V | no α≢β =
  _ , _ , swap α≢β v

-- an `idᶜ` layer over a value
id-step : ∀ {Γ s α V A}
  → flags Γ ∋ᶠ α ⦂ outside s
  → Value V
  → interior s α Γ ∣ [] ⊢ V ⦂ A
  → Value ([ s , α ] V ⟨ idᶜ ⟩)
    ⊎ Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ [ s , α ] V ⟨ idᶜ ⟩ ⟶ N ∣ a)
id-step coh V-$ ⊢V = inj₂ (_ , _ , id-$)
id-step {s = ⁺} coh (V-fun F) ⊢V = inj₁ (V-fun (F-id⁺ F))
id-step {s = ⁻} coh (V-fun F) ⊢V = id⁻-fun F
id-step {s = ⁺} coh (V-sealed v) ⊢V = inj₁ (V-sealed (S-rev v))
id-step {s = ⁻} coh (V-sealed v) ⊢V = inj₂ (id⁻-sealed coh v ⊢V)

-- a boundary over a value, by its conversion
boundary : ∀ {Γ s α M A R S c}
  → flags Γ ∋ᶠ α ⦂ outside s
  → Value M
  → interior s α Γ ∣ [] ⊢ M ⦂ A
  → flags (interior s α Γ) ⊢ A ⇝ R
  → store Γ ∣ s , α ⊢ c ⦂ R ⟹ S
  → Value ([ s , α ] M ⟨ c ⟩)
    ⊎ Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ [ s , α ] M ⟨ c ⟩ ⟶ N ∣ a)
boundary coh v ⊢M spA c-id     = id-step coh v ⊢M
boundary coh v ⊢M spA (c-fun _ _)  = inj₁ (V-fun (F-↦ v))
boundary coh v ⊢M spA (c-all _)    = inj₁ (V-fun (F-∀ v))
boundary coh v ⊢M spA (c-seal _)   = inj₁ (V-sealed (S-seal v))
boundary coh v ⊢M spA (c-unseal _) = inj₂ (unseal-step v ⊢M spA)

-- an application of a value to a value
apply : ∀ {Γ L M A B}
  → Value L
  → Value M
  → Γ ∣ [] ⊢ L ⦂ A ⇒ B
  → Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ L · M ⟶ N ∣ a)
apply V-$                  w ()
apply (V-fun F-ƛ)          w (⊢ƛ _ _) = _ , _ , β-ƛ w
apply (V-fun F-Λ)          w ()
apply (V-fun (F-↦ v))      w _ = _ , _ , wrap v w
apply (V-fun (F-∀ v))      w (⊢[] _ _ _ (s-⇒ _ _) ())
apply (V-fun (F-id⁺ F))    w _ = _ , _ , wrap-id (V-fun (F-id⁺ F)) w
apply (V-fun (F-id⁻ F nr)) w _ = _ , _ , wrap-id (V-fun (F-id⁻ F nr)) w
apply (V-sealed v)         w ⊢L = ⊥-elim (sealed-not-⇒ v ⊢L)

------------------------------------------------------------------------
-- 5. Progress
------------------------------------------------------------------------

progress : ∀ {Γ M A}
  → Γ ∣ [] ⊢ M ⦂ A
  → Value M ⊎ Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ M ⟶ N ∣ a)
progress (⊢` ())
progress ⊢nat     = inj₁ V-$
progress ⊢bool    = inj₁ V-$
progress (⊢ƛ _ _) = inj₁ (V-fun F-ƛ)
progress (⊢Λ _)   = inj₁ (V-fun F-Λ)
progress (⊢· ⊢L ⊢M) with progress ⊢L
progress (⊢· ⊢L ⊢M) | inj₂ (_ , _ , L⟶) = inj₂ (_ , _ , ξ-·₁ L⟶)
progress (⊢· ⊢L ⊢M) | inj₁ v with progress ⊢M
progress (⊢· ⊢L ⊢M) | inj₁ v | inj₂ (_ , _ , M⟶) =
  inj₂ (_ , _ , ξ-·₂ v M⟶)
progress (⊢· ⊢L ⊢M) | inj₁ v | inj₁ w = inj₂ (apply v w ⊢L)
progress (⊢ν sp ⊢L _ _ _) with progress ⊢L
progress (⊢ν sp ⊢L _ _ _) | inj₂ (_ , _ , L⟶) = inj₂ (_ , _ , ξ-ν L⟶)
progress (⊢ν sp ⊢L _ _ _) | inj₁ v =
  let (N , i) = inst v ⊢L in inj₂ (_ , _ , tyβ sp v i)
progress (⊢[] coh ⊢M spA _ ⊢c) with progress ⊢M
progress (⊢[] coh ⊢M spA _ ⊢c) | inj₂ (_ , _ , M⟶) =
  inj₂ (_ , _ , ξ-[] M⟶)
progress (⊢[] coh ⊢M spA _ ⊢c) | inj₁ v = boundary coh v ⊢M spA ⊢c
