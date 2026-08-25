module proof.DGG.ExtraCastRight2 where

-- File Charter:
--   * States target extra-cast and instantiation catch-up directly over the
--     canonical relation between complete CastTerms contexts.
--   * Records target-only execution with MultiWorldEvolution; there is no
--     projected world-extension record or separate context-imprecision list.
--   * Proves the inert and identity cast cases, which do not allocate.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
  renaming (subst to subst≡)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; id; inst_)
import Consistency as C
open import CastTerms using
  (Ctx; Δᵉ; Term; Value; Inert; _⟨_⟩; _《_》)
open import Reduction using
  (StoreChanges; []; _∷_; keep; applyTys; _—→[_]_; _—→[_]⟨_⟩_;
   _—↠[_]_; _∎[]; pure-step; β-id)
import Reduction as R
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open import proof.DGG.World
open import proof.DGG.WorldEvolution using (evolution-keep)
open import proof.DGG.WorldEvolutionSequence
open import proof.Imprecision using (⊑-unique)


------------------------------------------------------------------------
-- Statements
------------------------------------------------------------------------

ExtraCastRight² : Set
ExtraCastRight² = ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B B′ : Ty (Δᵉ Γᴿ)} {ν : Env∼ (Δᵉ Γᴿ)}
    {q : A ⊑ᵀ⟨ γ ⟩ B′}
  → (c′ : ν ⊢ B ∼ B′)
  → γ ⊢² M ⊑ M′ ⟨ c′ ⟩ ∶ q
  → Value M
  → Value M′
  → Σ[ Γᴿ′ ∈ Ctx ]
    Σ[ χs ∈ StoreChanges (Δᵉ Γᴿ) (Δᵉ Γᴿ′) ]
    Σ[ γ′ ∈ Γᴸ ⊑ᶜ Γᴿ′ ]
    Σ[ evol ∈ MultiWorldEvolution
      {W = γ} {W′ = γ′} [] χs ]
    Σ[ N′ ∈ Term (Δᵉ Γᴿ′) ]
    Σ[ r ∈ A ⊑ᵀ⟨ γ′ ⟩ (χs ▶ᵗ B′) ]
      Value N′
      × (M′ ⟨ c′ ⟩ —↠[ χs ] N′)
      × (γ′ ⊢² M ⊑ N′ ∶ r)


InstCatchupRight² : Set
InstCatchupRight² = ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (suc (Δᵉ Γᴿ))}
    {B′ : Ty (Δᵉ Γᴿ)} {ν : Env∼ (Δᵉ Γᴿ)}
    {p : A ⊑ᵀ⟨ γ ⟩ `∀ B}
  → γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → AllValueView M′
  → (c′ : C.instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → Σ[ Γᴿ′ ∈ Ctx ]
    Σ[ χs ∈ StoreChanges (Δᵉ Γᴿ) (Δᵉ Γᴿ′) ]
    Σ[ γ′ ∈ Γᴸ ⊑ᶜ Γᴿ′ ]
    Σ[ evol ∈ MultiWorldEvolution
      {W = γ} {W′ = γ′} [] χs ]
    Σ[ N′ ∈ Term (Δᵉ Γᴿ′) ]
    Σ[ r ∈ A ⊑ᵀ⟨ γ′ ⟩ (χs ▶ᵗ B′) ]
      Value N′
      × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
      × (γ′ ⊢² M ⊑ N′ ∶ r)


------------------------------------------------------------------------
-- Non-allocating cases
------------------------------------------------------------------------

inert-extra-cast-right² : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B B′ : Ty (Δᵉ Γᴿ)} {ν : Env∼ (Δᵉ Γᴿ)}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → (vM′ : Value M′)
  → (c′ : ν ⊢ B ∼ B′)
  → Inert c′
  → (q : A ⊑ᵀ⟨ γ ⟩ B′)
  → Σ[ Γᴿ′ ∈ Ctx ]
    Σ[ χs ∈ StoreChanges (Δᵉ Γᴿ) (Δᵉ Γᴿ′) ]
    Σ[ γ′ ∈ Γᴸ ⊑ᶜ Γᴿ′ ]
    Σ[ evol ∈ MultiWorldEvolution
      {W = γ} {W′ = γ′} [] χs ]
    Σ[ N′ ∈ Term (Δᵉ Γᴿ′) ]
    Σ[ r ∈ A ⊑ᵀ⟨ γ′ ⟩ (χs ▶ᵗ B′) ]
      Value N′
      × (M′ ⟨ c′ ⟩ —↠[ χs ] N′)
      × (γ′ ⊢² M ⊑ N′ ∶ r)
inert-extra-cast-right² {Γᴿ = Γᴿ} {γ = γ} {M = M} {M′ = M′}
    M⊑M′ vM vM′ c′ inert q =
  Γᴿ , [] , γ , evolutions-refl , M′ ⟨ c′ ⟩ , q ,
  vM′ 《 inert 》 ,
  (M′ ⟨ c′ ⟩ ∎[]) ,
  CTI.⊑cast² c′ M⊑M′ q


id-extra-cast-right² : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)} {ν : Env∼ (Δᵉ Γᴿ)}
    {p : A ⊑ᵀ⟨ γ ⟩ B}
  → γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → (vM′ : Value M′)
  → (a : Atom B)
  → (q : A ⊑ᵀ⟨ γ ⟩ B)
  → Σ[ Γᴿ′ ∈ Ctx ]
    Σ[ χs ∈ StoreChanges (Δᵉ Γᴿ) (Δᵉ Γᴿ′) ]
    Σ[ γ′ ∈ Γᴸ ⊑ᶜ Γᴿ′ ]
    Σ[ evol ∈ MultiWorldEvolution
      {W = γ} {W′ = γ′} [] χs ]
    Σ[ N′ ∈ Term (Δᵉ Γᴿ′) ]
    Σ[ r ∈ A ⊑ᵀ⟨ γ′ ⟩ (χs ▶ᵗ B) ]
      Value N′
      × (M′ ⟨ id {μ = ν} a ⟩ —↠[ χs ] N′)
      × (γ′ ⊢² M ⊑ N′ ∶ r)
id-extra-cast-right² {Γᴿ = Γᴿ} {γ = γ} {M = M} {M′ = M′}
    {p = p} M⊑M′ vM vM′ a q =
  Γᴿ , keep ∷ [] , γ ,
  evolutions-step-right refl evolution-keep evolutions-refl , M′ , q ,
  vM′ ,
  (M′ ⟨ id a ⟩
    —→[ keep ]⟨ pure-step (β-id vM′) ⟩
  M′ ∎[]) ,
  subst≡ (λ r → γ ⊢² M ⊑ M′ ∶ r) (⊑-unique p q) M⊑M′
