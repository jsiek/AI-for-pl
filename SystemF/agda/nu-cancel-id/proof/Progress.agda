module nu-cancel-id.proof.Progress where

-- File Charter:
--   * THE PROGRESS PROOF of νF₁ᶜ (notes/CancelIdSketch.md §4 in
--     strong-rep-nu).  §1 flag lemmas: an entry's own flag is set in its
--     interior, so a second coherent entry for the same cell with the
--     same sign is impossible.  §2 canonical forms: a functional value
--     never has a variable type, and a `∀`-typed value can be
--     instantiated.  §3 the boundary cases: an unseal's body is its own
--     seal (Cancel-□), and an `idᶜ` layer is a value or a CancelId, Sink
--     or Id redex.  §4 progress, by induction on the typing derivation.
--   * No walk down a tower: an unseal looks at one layer.

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction

private
  variable
    Γ : Ctx
    Γₜ : List Ty
    Φ : Flags
    s : Sign
    α : ℕ
    b b′ b″ : Bool
    R S : Ty
    c : Conv
    F V : Term

------------------------------------------------------------------------
-- 1. Flags
------------------------------------------------------------------------

setFlag-hit : Φ ∋ᶠ α ⦂ b → setFlag α b′ Φ ∋ᶠ α ⦂ b′
setFlag-hit f-here      = f-here
setFlag-hit (f-there f) = f-there (setFlag-hit f)

∋ᶠ-unique : Φ ∋ᶠ α ⦂ b → Φ ∋ᶠ α ⦂ b′ → b ≡ b′
∋ᶠ-unique f-here      f-here      = refl
∋ᶠ-unique (f-there f) (f-there g) = ∋ᶠ-unique f g

-- inside a boundary on cell α, α's flag is the one the entry set
flag-clash : Φ ∋ᶠ α ⦂ b → setFlag α b′ Φ ∋ᶠ α ⦂ b″ → b′ ≡ b″
flag-clash f g = ∋ᶠ-unique (setFlag-hit f) g

true≢false : true ≡ false → ⊥
true≢false ()

false≢true : false ≡ true → ⊥
false≢true ()

------------------------------------------------------------------------
-- 2. Canonical forms
------------------------------------------------------------------------

fun-not-var : Fun F → Γ ∣ Γₜ ⊢ F ⦂ ` α → ⊥
fun-not-var F-ƛ          ()
fun-not-var F-Λ          ()
fun-not-var (F-↦ _)      (⊢[] _ _ ())
fun-not-var (F-∀ _)      (⊢[] _ _ ())
fun-not-var (F-id⁺ F)    (⊢[] _ ⊢F (c-id _)) = fun-not-var F ⊢F
fun-not-var (F-id⁻ F _)  (⊢[] _ ⊢F (c-id _)) = fun-not-var F ⊢F

inst : ∀ {R}
  → Value V
  → Γ ∣ Γₜ ⊢ V ⦂ `∀ R
  → ∃[ N ] V •⟶ N
inst V-$                     ()
inst (V-fun F-ƛ)             ()
inst (V-fun F-Λ)             (⊢Λ _) = _ , inst-Λ
inst (V-fun (F-↦ _))         (⊢[] _ _ ())
inst (V-fun (F-∀ v))         (⊢[] _ ⊢V (c-all _)) =
  let (N , i) = inst v ⊢V in _ , inst-∀ i
inst (V-fun (F-id⁺ F))       (⊢[] _ ⊢V (c-id _)) =
  let (N , i) = inst (V-fun F) ⊢V in _ , inst-id i
inst (V-fun (F-id⁻ F _))     (⊢[] _ ⊢V (c-id _)) =
  let (N , i) = inst (V-fun F) ⊢V in _ , inst-id i
inst (V-sealed (S-seal _))   (⊢[] _ _ ())
inst (V-sealed (S-hid _))    (⊢[] _ (⊢[] _ _ ()) (c-id _))

------------------------------------------------------------------------
-- 3. Boundaries and applications whose subterms are values
------------------------------------------------------------------------

-- An unseal's body has type α where α is named, so it is α's first
-- seal head: the second starts by revealing α, which is incoherent.
unseal-step : ∀ {Γ α V}
  → flags Γ ∋ᶠ α ⦂ false
  → Value V
  → interior ⁺ α Γ ∣ [] ⊢ V ⦂ ` α
  → Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ [ ⁺ , α ] V ⟨ unseal ⟩ ⟶ N ∣ a)
unseal-step coh V-$ ()
unseal-step coh (V-fun F) ⊢V = ⊥-elim (fun-not-var F ⊢V)
unseal-step coh (V-sealed (S-seal w)) (⊢[] _ _ (c-seal _)) =
  _ , _ , cancel-□ w
unseal-step coh (V-sealed (S-hid w)) (⊢[] coh′ (⊢[] _ _ (c-seal _)) (c-id _)) =
  ⊥-elim (true≢false (flag-clash coh coh′))

-- `[ ⁻ , α ] F ⟨ idᶜ ⟩` over a functional value: CancelId exactly when F
-- reveals α with `idᶜ`
id⁻-fun : ∀ {Γ α F}
  → Fun F
  → Value ([ ⁻ , α ] F ⟨ idᶜ ⟩)
    ⊎ Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ [ ⁻ , α ] F ⟨ idᶜ ⟩ ⟶ N ∣ a)
id⁻-fun F-ƛ           = inj₁ (V-fun (F-id⁻ F-ƛ (λ ())))
id⁻-fun F-Λ           = inj₁ (V-fun (F-id⁻ F-Λ (λ ())))
id⁻-fun (F-↦ v)       = inj₁ (V-fun (F-id⁻ (F-↦ v) (λ ())))
id⁻-fun (F-∀ v)       = inj₁ (V-fun (F-id⁻ (F-∀ v) (λ ())))
id⁻-fun (F-id⁻ F nr)  = inj₁ (V-fun (F-id⁻ (F-id⁻ F nr) (λ ())))
id⁻-fun {α = α} (F-id⁺ {α = β} F) with β ≟ α
id⁻-fun {α = α} (F-id⁺ {α = β} F) | yes refl =
  inj₂ (_ , _ , cancel-id (V-fun F))
id⁻-fun {α = α} (F-id⁺ {α = β} F) | no β≢α =
  inj₁ (V-fun (F-id⁻ (F-id⁺ F) (λ { refl → β≢α refl })))

-- an `idᶜ` layer over a value
id-step : ∀ {Γ s α V R}
  → flags Γ ∋ᶠ α ⦂ outside s
  → Value V
  → interior s α Γ ∣ [] ⊢ V ⦂ R
  → Value ([ s , α ] V ⟨ idᶜ ⟩)
    ⊎ Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ [ s , α ] V ⟨ idᶜ ⟩ ⟶ N ∣ a)
id-step coh V-$ ⊢V = inj₂ (_ , _ , id-$)
id-step {s = ⁺} coh (V-fun F) ⊢V = inj₁ (V-fun (F-id⁺ F))
id-step {s = ⁻} coh (V-fun F) ⊢V = id⁻-fun F
id-step {α = α} coh (V-sealed (S-seal {α = β} w)) ⊢V with α ≟ β
id-step {s = ⁺} {α = α} coh (V-sealed (S-seal {α = β} w)) ⊢V
  | yes refl = inj₁ (V-sealed (S-hid w))
id-step {s = ⁻} {α = α} coh (V-sealed (S-seal {α = β} w)) (⊢[] coh′ _ _)
  | yes refl = ⊥-elim (false≢true (flag-clash coh coh′))
id-step {α = α} coh (V-sealed (S-seal {α = β} w)) ⊢V
  | no α≢β = inj₂ (_ , _ , sink-seal α≢β w)
id-step {α = α} coh (V-sealed (S-hid {α = β} w)) ⊢V with α ≟ β
id-step {s = ⁺} {α = α} coh (V-sealed (S-hid {α = β} w)) (⊢[] coh′ _ _)
  | yes refl = ⊥-elim (true≢false (flag-clash coh coh′))
id-step {s = ⁻} {α = α} coh (V-sealed (S-hid {α = β} w)) ⊢V
  | yes refl = inj₂ (_ , _ , cancel-id (V-sealed (S-seal w)))
id-step {α = α} coh (V-sealed (S-hid {α = β} w)) ⊢V
  | no α≢β = inj₂ (_ , _ , sink-hid α≢β w)

-- a boundary over a value, by its conversion
boundary : ∀ {Γ s α M R S c}
  → flags Γ ∋ᶠ α ⦂ outside s
  → Value M
  → interior s α Γ ∣ [] ⊢ M ⦂ R
  → store Γ ∣ s , α ⊢ c ⦂ R ⟹ S
  → Value ([ s , α ] M ⟨ c ⟩)
    ⊎ Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ [ s , α ] M ⟨ c ⟩ ⟶ N ∣ a)
boundary coh v ⊢M (c-id _)     = id-step coh v ⊢M
boundary coh v ⊢M (c-fun _ _)  = inj₁ (V-fun (F-↦ v))
boundary coh v ⊢M (c-all _)    = inj₁ (V-fun (F-∀ v))
boundary coh v ⊢M (c-seal _)   = inj₁ (V-sealed (S-seal v))
boundary coh v ⊢M (c-unseal _) = inj₂ (unseal-step coh v ⊢M)

-- an application of a value to a value
apply : ∀ {Γ L M R S}
  → Value L
  → Value M
  → Γ ∣ [] ⊢ L ⦂ R ⇒ S
  → Σ[ N ∈ Term ] Σ[ a ∈ Alloc ] (Γ ⊢ L · M ⟶ N ∣ a)
apply V-$                    w ()
apply (V-fun F-ƛ)            w (⊢ƛ _ _) = _ , _ , β-ƛ w
apply (V-fun F-Λ)            w ()
apply (V-fun (F-↦ v))        w _ = _ , _ , wrap v w
apply (V-fun (F-∀ v))        w (⊢[] _ _ ())
apply (V-fun (F-id⁺ F))      w _ = _ , _ , wrap-id (V-fun (F-id⁺ F)) w
apply (V-fun (F-id⁻ F nr))   w _ = _ , _ , wrap-id (V-fun (F-id⁻ F nr)) w
apply (V-sealed (S-seal _))  w (⊢[] _ _ ())
apply (V-sealed (S-hid _))   w (⊢[] _ (⊢[] _ _ ()) (c-id _))

------------------------------------------------------------------------
-- 4. Progress
------------------------------------------------------------------------

progress : ∀ {Γ M R}
  → Γ ∣ [] ⊢ M ⦂ R
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
progress (⊢ν sp ⊢L _ _) with progress ⊢L
progress (⊢ν sp ⊢L _ _) | inj₂ (_ , _ , L⟶) = inj₂ (_ , _ , ξ-ν L⟶)
progress (⊢ν sp ⊢L _ _) | inj₁ v =
  let (N , i) = inst v ⊢L in inj₂ (_ , _ , tyβ sp v i)
progress (⊢[] coh ⊢M ⊢c) with progress ⊢M
progress (⊢[] coh ⊢M ⊢c) | inj₂ (_ , _ , M⟶) = inj₂ (_ , _ , ξ-[] M⟶)
progress (⊢[] coh ⊢M ⊢c) | inj₁ v = boundary coh v ⊢M ⊢c
