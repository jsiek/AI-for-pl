module nu-cancel-id.proof.Preservation where

-- File Charter:
--   * THE PRESERVATION PROOF of νF₁ᶜ with named types
--     (notes/CancelIdSketch.md §8 in strong-rep-nu).  A step at Γ types
--     its contractum at `a ⨾ Γ`, the context after its allocation, at
--     the SAME named type: an allocated cell is unnamed, so no name
--     moves.
--   * §1 casts; §2 TyBeta's instantiation (the `Λ`'s abstract cell is
--     refined to the payload); §3 the argument Wrap builds; §4 the case
--     for each rule.  The boundary rules use three facts about named
--     types: spelling is functional and injective (CancelId, Cancel-□),
--     and a type read in one context can be re-read in a context with
--     more names (Sink, Swap, Push).

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst)

open import nu-cancel-id.Types
open import nu-cancel-id.Ctx
open import nu-cancel-id.Terms
open import nu-cancel-id.Reduction
open import nu-cancel-id.proof.Flags
open import nu-cancel-id.proof.Weaken
open import nu-cancel-id.proof.Subst

private
  variable
    Γ : Ctx
    Σ : Store
    Φ Φ′ : Flags
    Γₜ : List Ty
    α β : ℕ
    A B R : Ty
    M : Term

------------------------------------------------------------------------
-- 1. Casts
------------------------------------------------------------------------

cast-⊢ : Φ ≡ Φ′ → A ≡ B → (Σ ∣ Φ) ∣ Γₜ ⊢ M ⦂ A → (Σ ∣ Φ′) ∣ Γₜ ⊢ M ⦂ B
cast-⊢ refl refl ⊢M = ⊢M

respell : Φ ≡ Φ′ → Φ ⊢ A ⇝ R → Φ′ ⊢ A ⇝ R
respell refl sp = sp

-- an unseal of α and a reveal of β inside it are on different cells
unseal-distinct : Φ ∋ᶠ α ⦂ false → setFlag α true Φ ∋ᶠ β ⦂ false → α ≢ β
unseal-distinct c₁ c₂ refl = true≢false (flag-clash c₁ c₂)

------------------------------------------------------------------------
-- 2. TyBeta's instantiation
------------------------------------------------------------------------

inst-pres : ∀ {Γ V N C P}
  → Γ ∣ [] ⊢ V ⦂ `∀ C
  → V •⟶ N
  → (pay P ∷ store Γ ∣ true ∷ flags Γ) ∣ [] ⊢ N ⦂ C
inst-pres {Γ = Γ} (⊢Λ ⊢N) inst-Λ = ⊑-⊢ (⊑-abs (⊑-refl (store Γ))) ⊢N
inst-pres {Γ = Γ} (⊢[] coh ⊢V (s-∀ spC′) (s-∀ spC) (c-all ⊢c)) (inst-∀ i) =
  ⊢[] (f-there coh) (inst-pres ⊢V i) spC′ spC
      (⊑-conv (⊑-abs (⊑-refl (store Γ))) ⊢c)
inst-pres (⊢[] coh ⊢V (s-∀ spC′) (s-∀ spC) c-id) (inst-id i) =
  ⊢[] (f-there coh) (inst-pres ⊢V i) spC′ spC c-id

------------------------------------------------------------------------
-- 3. The argument Wrap builds: the dual entry restores the flags
------------------------------------------------------------------------

wrap-arg : ∀ s {Γ α W A₁ A₂ R′ R c}
  → flags Γ ∋ᶠ α ⦂ outside s
  → Γ ∣ [] ⊢ W ⦂ A₁
  → flags Γ ⊢ A₁ ⇝ R′
  → flags (interior s α Γ) ⊢ A₂ ⇝ R
  → store Γ ∣ flip s , α ⊢ c ⦂ R′ ⟹ R
  → interior s α Γ ∣ [] ⊢ [ flip s , α ] W ⟨ c ⟩ ⦂ A₂
wrap-arg ⁺ {Γ} {α} coh ⊢W spW spA ⊢c =
  ⊢[] (setFlag-hit coh) (cast-⊢ eq refl ⊢W) (respell eq spW) spA ⊢c
  where
  eq : flags Γ ≡ setFlag α false (setFlag α true (flags Γ))
  eq = sym (trans (setFlag-twice α false true (flags Γ)) (setFlag-idem coh))
wrap-arg ⁻ {Γ} {α} coh ⊢W spW spA ⊢c =
  ⊢[] (setFlag-hit coh) (cast-⊢ eq refl ⊢W) (respell eq spW) spA ⊢c
  where
  eq : flags Γ ≡ setFlag α true (setFlag α false (flags Γ))
  eq = sym (trans (setFlag-twice α true false (flags Γ)) (setFlag-idem coh))

-- Wrap: the domain conversion goes to the argument, under the dual
-- entry; the layer keeps the codomain conversion
wrap-pres : ∀ {Γ s α V W c d A B}
  → Γ ∣ [] ⊢ [ s , α ] V ⟨ c ↦ d ⟩ ⦂ A ⇒ B
  → Γ ∣ [] ⊢ W ⦂ A
  → Γ ∣ [] ⊢ [ s , α ] (V · [ flip s , α ] W ⟨ c ⟩) ⟨ d ⟩ ⦂ B
wrap-pres (⊢[] {s = s} coh ⊢V spA spB (c-fun ⊢c ⊢d)) ⊢W with spA | spB
... | s-⇒ spA₂ spB₂ | s-⇒ spA₁ spB₁ =
  ⊢[] coh (⊢· ⊢V (wrap-arg s coh ⊢W spA₁ spA₂ ⊢c)) spB₂ spB₁ ⊢d

wrap-id-pres : ∀ {Γ s α V W A B}
  → Γ ∣ [] ⊢ [ s , α ] V ⟨ idᶜ ⟩ ⦂ A ⇒ B
  → Γ ∣ [] ⊢ W ⦂ A
  → Γ ∣ [] ⊢ [ s , α ] (V · [ flip s , α ] W ⟨ idᶜ ⟩) ⟨ idᶜ ⟩ ⦂ B
wrap-id-pres (⊢[] {s = s} coh ⊢V spA spB c-id) ⊢W with spB | spA
... | s-⇒ spA₁ spB₁ | s-⇒ spA₂ spB₂ =
  ⊢[] coh (⊢· ⊢V (wrap-arg s coh ⊢W spA₁ spA₂ c-id)) spB₂ spB₁ c-id

------------------------------------------------------------------------
-- 4. Preservation
------------------------------------------------------------------------

preservation : ∀ {Γ M N A a}
  → Γ ∣ [] ⊢ M ⦂ A
  → Γ ⊢ M ⟶ N ∣ a
  → a ⨾ Γ ∣ [] ⊢ N ⦂ A
preservation (⊢· (⊢ƛ sp ⊢N) ⊢W) (β-ƛ w) = subst-pres [] ⊢N ⊢W sp
preservation (⊢· ⊢L ⊢W) (wrap v w)    = wrap-pres ⊢L ⊢W
preservation (⊢· ⊢L ⊢W) (wrap-id v w) = wrap-id-pres ⊢L ⊢W
preservation (⊢ν sp′ ⊢V spC spB ⊢d) (tyβ sp v i) with ⇝-unique sp′ sp
preservation (⊢ν sp′ ⊢V spC spB ⊢d) (tyβ sp v i) | refl =
  ⊢[] f-here (inst-pres ⊢V i) spC spB ⊢d
preservation (⊢[] coh ⊢nat  s-ℕ s-ℕ c-id) id-$ = ⊢nat
preservation (⊢[] coh ⊢bool s-𝔹 s-𝔹 c-id) id-$ = ⊢bool
preservation {Γ = Γ}
    (⊢[] {α = α} coh₁ (⊢[] coh₂ ⊢W spW spX (c-seal l₁)) spX′ spB
         (c-unseal l₂))
    (cancel-□ w)
  with ∋-unique l₁ l₂
... | refl = cast-⊢ eq (⇝-inj (respell eq spW) spB) ⊢W
  where
  eq : setFlag α false (setFlag α true (flags Γ)) ≡ flags Γ
  eq = trans (setFlag-twice α false true (flags Γ)) (setFlag-idem coh₁)
preservation {Γ = Γ}
    (⊢[] {α = α} coh₁ (⊢[] coh₂ ⊢V spV spM c-id) spM′ spB c-id)
    (cancel-id v)
  with ⇝-unique spM spM′
... | refl = cast-⊢ eq (⇝-inj (respell eq spV) spB) ⊢V
  where
  eq : setFlag α true (setFlag α false (flags Γ)) ≡ flags Γ
  eq = trans (setFlag-twice α true false (flags Γ)) (setFlag-idem coh₁)
preservation {Γ = Γ}
    (⊢[] {α = α} coh₁ (⊢[] {α = β} coh₂ ⊢V spV spX (c-seal l)) spM spB c-id)
    (sink α≢β v)
  with ⇝-unique spM spX
... | refl = ⊢[] (setFlag-miss⁻¹ α≢β coh₂) inner spIn spB (c-seal l)
  where
  β≢α : β ≢ α
  β≢α eq = α≢β (sym eq)
  eq : setFlag β false (setFlag α false (flags Γ))
     ≡ setFlag α false (setFlag β false (flags Γ))
  eq = setFlag-comm false false (flags Γ) β≢α
  spV′ = respell eq spV
  spIn = proj₂ (reread hide-⊆ spV′)
  inner = ⊢[] (setFlag-miss β≢α coh₁) (cast-⊢ eq refl ⊢V) spV′ spIn c-id
preservation {Γ = Γ}
    (⊢[] {α = α} coh₁ (⊢[] {α = β} coh₂ ⊢V spV spX c-id) spM spB c-id)
    (swap α≢β v)
  with ⇝-unique spM spX
... | refl = ⊢[] (setFlag-miss⁻¹ α≢β coh₂) inner spIn spB c-id
  where
  β≢α : β ≢ α
  β≢α eq = α≢β (sym eq)
  eq : setFlag β true (setFlag α false (flags Γ))
     ≡ setFlag α false (setFlag β true (flags Γ))
  eq = setFlag-comm true false (flags Γ) β≢α
  spIn = proj₂ (reread reveal-⊆ spB)
  inner = ⊢[] (setFlag-miss β≢α coh₁) (cast-⊢ eq refl ⊢V) (respell eq spV)
              spIn c-id
preservation {Γ = Γ}
    (⊢[] {α = α} coh₁ (⊢[] {α = β} coh₂ ⊢V spV spX c-id) spM spB
         (c-unseal l))
    (push v)
  with ⇝-unique spM spX
... | refl = ⊢[] (setFlag-miss⁻¹ α≢β coh₂) inner spIn spB c-id
  where
  α≢β : α ≢ β
  α≢β = unseal-distinct coh₁ coh₂
  β≢α : β ≢ α
  β≢α eq = α≢β (sym eq)
  eq : setFlag β true (setFlag α true (flags Γ))
     ≡ setFlag α true (setFlag β true (flags Γ))
  eq = setFlag-comm true true (flags Γ) β≢α
  spIn = proj₂ (reread reveal-⊆ spB)
  inner = ⊢[] (setFlag-miss β≢α coh₁) (cast-⊢ eq refl ⊢V) (respell eq spV)
              spIn (c-unseal l)
preservation (⊢· ⊢L ⊢M) (ξ-·₁ {a = a} L⟶) =
  ⊢· (preservation ⊢L L⟶) (⊢↑ᵃ a ⊢M)
preservation (⊢· ⊢L ⊢M) (ξ-·₂ {a = a} v M⟶) =
  ⊢· (⊢↑ᵃ a ⊢L) (preservation ⊢M M⟶)
preservation (⊢ν sp ⊢L spC spB ⊢c) (ξ-ν {a = keep} L⟶) =
  ⊢ν sp (preservation ⊢L L⟶) spC spB ⊢c
preservation (⊢ν sp ⊢L spC spB ⊢c) (ξ-ν {a = new Q} L⟶) =
  ⊢ν (ins-⇝ zero sp) (preservation ⊢L L⟶) (ins-⇝ (suc zero) spC)
     (ins-⇝ (suc zero) spB) (ins-conv (suc zero) ⊢c)
preservation (⊢[] coh ⊢M spA spB ⊢c) (ξ-[] {a = keep} M⟶) =
  ⊢[] coh (preservation ⊢M M⟶) spA spB ⊢c
preservation (⊢[] coh ⊢M spA spB ⊢c) (ξ-[] {a = new Q} M⟶) =
  ⊢[] (f-there coh) (preservation ⊢M M⟶) (ins-⇝ zero spA) (ins-⇝ zero spB)
      (ins-conv zero ⊢c)

-- runs
preservation* : ∀ {Γ Γ′ M N A}
  → Γ ∣ [] ⊢ M ⦂ A
  → Γ ⊢ M —↠ N ⊣ Γ′
  → Γ′ ∣ [] ⊢ N ⦂ A
preservation* ⊢M (_ ∎)            = ⊢M
preservation* ⊢M (_ —→⟨ s ⟩ M↠N) = preservation* (preservation ⊢M s) M↠N
