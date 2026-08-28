{-# OPTIONS --safe #-}

module proof.DGG.notes.SemanticInstantiationSpineProbe where

-- File Charter:
--   * Probes a private semantic companion to InstantiationSpine.
--   * Records the exact CTI derivation at every pending frame boundary.
--   * Records live conversion typing on reveal and conceal frames, making the
--     generator position available without reconstructing it from syntax.
--   * Checks identity and universal conceal instances and extracts their tail
--     relations from the semantic spine.
--   * Changes no production relation or public proof interface.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; ★; ＇_; `∀; _[_]ᵗ; ⇑ᵗ)
open import TyStore using (_∋_⦂_; S-lift∋; store-lift)
open import Consistency using (Env∼; _⊢_∼_)
import Conversion as Conv
open import CastTerms using
  (Ctx; Term; Δᵉ; Σᵉ; _⟨_⟩; _⦂∀_[_]; _↑_; _↓_)
open import proof.DGG.ConversionPivotAlignment using
  (GeneratorPosition; generator-absent; concealGeneratorPosition)
open import proof.DGG.CastTermImprecision using (_⊢²_⊑_∶_)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.World
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef using
  ( InstantiationSpine; []ⁱ; _▻ⁱ_; type-transport-frame
  ; name-type-app-frame; cast-frame; reveal-frame; conceal-frame
  )


-- This is deliberately separate from SpineNamesTargetOnlyᶜ.  Name freshness
-- describes allocation provenance; this judgment describes the semantic
-- boundary crossed by each pending frame.  Its indices mention only data
-- constructors and variables.  In particular, applyInstantiationFrame does
-- not occur in an index.
data SemanticInstantiationSpineᶜ
    {Γᴸ Γᴿ : Ctx}
    {M : Term (Δᵉ Γᴸ)} {A : Ty (Δᵉ Γᴸ)} :
    ∀ {γ : Γᴸ ⊑ᶜ Γᴿ}
      {N : Term (Δᵉ Γᴿ)} {B : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
    → γ ⊢² M ⊑ N ∶ p
    → {E : Ty (Δᵉ Γᴿ)}
    → InstantiationSpine B E
    → Set where

  semantic-[] : ∀ {γ : Γᴸ ⊑ᶜ Γᴿ}
      {N : Term (Δᵉ Γᴿ)} {B : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B}
      {rel : γ ⊢² M ⊑ N ∶ p}
    → SemanticInstantiationSpineᶜ rel []ⁱ

  semantic-type-transport : ∀ {γ : Γᴸ ⊑ᶜ Γᴿ}
      {N : Term (Δᵉ Γᴿ)} {B C E : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {q : A ⊑ᵀ⟨ γ ⟩ C}
      {rel : γ ⊢² M ⊑ N ∶ p} {eq : B ≡ C}
      {next : γ ⊢² M ⊑ N ∶ q}
      {spine : InstantiationSpine C E}
    → SemanticInstantiationSpineᶜ next spine
    → SemanticInstantiationSpineᶜ rel
        (type-transport-frame eq ▻ⁱ spine)

  semantic-name-type-app : ∀ {γ : Γᴸ ⊑ᶜ Γᴿ}
      {N : Term (Δᵉ Γᴿ)} {B C E : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {q : A ⊑ᵀ⟨ γ ⟩ C}
      {D : Ty (Nat.suc (Δᵉ Γᴿ))} {X : TyVar (Δᵉ Γᴿ)}
      {rel : γ ⊢² M ⊑ N ∶ p}
      {eqB : B ≡ `∀ D} {eqC : C ≡ D [ ＇ X ]ᵗ}
      {next : γ ⊢² M ⊑ N ⦂∀ D [ ＇ X ] ∶ q}
      {spine : InstantiationSpine C E}
    → SemanticInstantiationSpineᶜ next spine
    → SemanticInstantiationSpineᶜ rel
        (name-type-app-frame D X eqB eqC ▻ⁱ spine)

  semantic-cast : ∀ {γ : Γᴸ ⊑ᶜ Γᴿ}
      {N : Term (Δᵉ Γᴿ)} {B C E : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {q : A ⊑ᵀ⟨ γ ⟩ C}
      {ν : Env∼ (Δᵉ Γᴿ)} {c : ν ⊢ B ∼ C}
      {rel : γ ⊢² M ⊑ N ∶ p}
      {next : γ ⊢² M ⊑ N ⟨ c ⟩ ∶ q}
      {spine : InstantiationSpine C E}
    → SemanticInstantiationSpineᶜ next spine
    → SemanticInstantiationSpineᶜ rel (cast-frame c ▻ⁱ spine)

  semantic-reveal : ∀ {γ γ′ : Γᴸ ⊑ᶜ Γᴿ}
      {N : Term (Δᵉ Γᴿ)} {B C E : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {q : A ⊑ᵀ⟨ γ′ ⟩ C}
      {X : TyVar (Δᵉ Γᴿ)} {R : Ty (Δᵉ Γᴿ)}
      {c : Conv.Conv↑ (Δᵉ Γᴿ) B C}
      {rel : γ ⊢² M ⊑ N ∶ p}
    → (c⊢ : Σᵉ Γᴿ Conv.⊢↑[ X ⦂ R ] c)
    → {next : γ′ ⊢² M ⊑ N ↑ c ∶ q}
      {spine : InstantiationSpine C E}
    → SemanticInstantiationSpineᶜ next spine
    → SemanticInstantiationSpineᶜ rel (reveal-frame c ▻ⁱ spine)

  semantic-conceal : ∀ {γ γ′ : Γᴸ ⊑ᶜ Γᴿ}
      {N : Term (Δᵉ Γᴿ)} {B C E : Ty (Δᵉ Γᴿ)}
      {p : A ⊑ᵀ⟨ γ ⟩ B} {q : A ⊑ᵀ⟨ γ′ ⟩ C}
      {X : TyVar (Δᵉ Γᴿ)} {R : Ty (Δᵉ Γᴿ)}
      {c : Conv.Conv↓ (Δᵉ Γᴿ) B C}
      {rel : γ ⊢² M ⊑ N ∶ p}
    → (c⊢ : Σᵉ Γᴿ Conv.⊢↓[ X ⦂ R ] c)
    → {next : γ′ ⊢² M ⊑ N ↓ c ∶ q}
      {spine : InstantiationSpine C E}
    → SemanticInstantiationSpineᶜ next spine
    → SemanticInstantiationSpineᶜ rel (conceal-frame c ▻ⁱ spine)


-- Eliminating one conceal node exposes exactly the facts the pending-frame
-- normalizer lacked: live store typing, its computed generator position, the
-- intermediate type-imprecision witness, the CTI relation at the wrapped
-- target term, and the semantic certificate for the remaining tail.
semantic-conceal-tail : ∀ {Γᴸ Γᴿ : Ctx}
    {M : Term (Δᵉ Γᴸ)} {N : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B C E : Ty (Δᵉ Γᴿ)}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {p : A ⊑ᵀ⟨ γ ⟩ B}
    {c : Conv.Conv↓ (Δᵉ Γᴿ) B C}
    {rel : γ ⊢² M ⊑ N ∶ p}
    {spine : InstantiationSpine C E}
  → SemanticInstantiationSpineᶜ rel (conceal-frame c ▻ⁱ spine)
  → Σ[ X ∈ TyVar (Δᵉ Γᴿ) ]
    Σ[ R ∈ Ty (Δᵉ Γᴿ) ]
    Σ[ c⊢ ∈ Σᵉ Γᴿ Conv.⊢↓[ X ⦂ R ] c ]
    Σ[ position ∈ GeneratorPosition ]
    Σ[ position-eq ∈ concealGeneratorPosition c⊢ ≡ position ]
    Σ[ γ′ ∈ Γᴸ ⊑ᶜ Γᴿ ]
    Σ[ q ∈ A ⊑ᵀ⟨ γ′ ⟩ C ]
    Σ[ next ∈ γ′ ⊢² M ⊑ N ↓ c ∶ q ]
      SemanticInstantiationSpineᶜ next spine
semantic-conceal-tail
    (semantic-conceal {γ′ = γ′} {q = q} {X = X} {R = R}
      c⊢ {next = next} tail) =
  X , R , c⊢ , concealGeneratorPosition c⊢ , refl ,
    γ′ , q , next , tail


module IdentityConcealProbe {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {N : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {p : A ⊑ᵀ⟨ γ ⟩ ★}
    (rel : γ ⊢² M ⊑ N ∶ p)
    {X : TyVar (Δᵉ Γᴿ)} {R : Ty (Δᵉ Γᴿ)}
    (X∈ : Σᵉ Γᴿ ∋ X ⦂ R) where

  id↓⊢ : Σᵉ Γᴿ Conv.⊢↓[ X ⦂ R ] Conv.id↓ ★
  id↓⊢ = Conv.⊢↓-id-star X∈

  id↓-position : concealGeneratorPosition id↓⊢ ≡ generator-absent
  id↓-position = refl

  id↓-semantic : SemanticInstantiationSpineᶜ rel
      (conceal-frame (Conv.id↓ ★) ▻ⁱ []ⁱ)
  id↓-semantic =
    semantic-conceal id↓⊢
      (semantic-[]
        {rel = CTI.⊑conceal-identity id↓⊢ id↓-position rel p})

  id↓-tail-relation : γ ⊢² M ⊑ N ↓ Conv.id↓ ★ ∶ p
  id↓-tail-relation =
    CTI.⊑conceal-identity id↓⊢ id↓-position rel p

  id↓-tail-is-stored : semantic-conceal-tail id↓-semantic ≡
      (X , R , id↓⊢ , generator-absent , refl ,
        γ , p , id↓-tail-relation , semantic-[])
  id↓-tail-is-stored = refl


module UniversalConcealProbe {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {N : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {p : A ⊑ᵀ⟨ γ ⟩ `∀ ★}
    (rel : γ ⊢² M ⊑ N ∶ p)
    {X : TyVar (Δᵉ Γᴿ)} {R : Ty (Δᵉ Γᴿ)}
    (X∈ : Σᵉ Γᴿ ∋ X ⦂ R) where

  ∀↓⊢ : Σᵉ Γᴿ Conv.⊢↓[ X ⦂ R ]
      Conv.`∀↓ (Conv.id↓ ★)
  ∀↓⊢ =
    Conv.⊢↓-∀ refl (Conv.⊢↓-id-star (S-lift∋ X∈ refl))

  ∀↓-position : concealGeneratorPosition ∀↓⊢ ≡ generator-absent
  ∀↓-position = refl

  ∀↓-semantic : SemanticInstantiationSpineᶜ rel
      (conceal-frame (Conv.`∀↓ (Conv.id↓ ★)) ▻ⁱ []ⁱ)
  ∀↓-semantic =
    semantic-conceal ∀↓⊢
      (semantic-[]
        {rel = CTI.⊑conceal-identity ∀↓⊢ ∀↓-position rel p})

  ∀↓-tail-relation :
    γ ⊢² M ⊑ N ↓ Conv.`∀↓ (Conv.id↓ ★) ∶ p
  ∀↓-tail-relation =
    CTI.⊑conceal-identity ∀↓⊢ ∀↓-position rel p

  ∀↓-tail-is-stored : semantic-conceal-tail ∀↓-semantic ≡
      (X , R , ∀↓⊢ , generator-absent , refl ,
        γ , p , ∀↓-tail-relation , semantic-[])
  ∀↓-tail-is-stored = refl


------------------------------------------------------------------------
-- Seeding and preservation verdict
------------------------------------------------------------------------

-- The certificate is sufficient at an already exposed target frame: the two
-- checks above recover the conversion typing, its position, the intermediate
-- CTI derivation, and the remaining tail without another inversion argument.
-- It is not sufficient as the sole new state of the live combined worker.
--
-- At the target-only public beta-inst root, the first pending frame is a
-- target type application.  CTI has no target-only type-application rule, so
-- there is no boundary derivation with which to seed semantic-name-type-app.
-- One can seed the certificate only after the AllValueView branch exposes and
-- reduces that application.  Constructing the later residual reveal/cast
-- boundaries from the final q additionally needs the separate induction on
-- the instantiation consistency; the public inputs do not contain them.
--
-- At the paired public beta-inst root, seeding is impossible even after such a
-- target-only preprocessing step: retaining the source inert cast would need
-- the false intermediate input square checked in
-- PairedTargetInstantiationInputSquareCounterexample.agda.  The paired proof
-- must therefore keep its source replay obligation in the induction state
-- rather than ask for a target-only semantic chain up front.
--
-- Same-world tail descent preserves this certificate by construction.
-- Store-changing mapInstantiationSpine transitions would need a structural
-- mapping theorem for every stored CTI derivation and conversion typing proof.
-- Target-only bind freshness from SpineNamesTargetOnlyᶜ supplies one premise,
-- but source reveal rebase does not preserve target-only occupancy (the strict
-- TargetOnlyNameRevealRebaseCounterexample.agda checks that failure).  Those
-- branches still require the rebase-aware contextual zipper.  Consequently
-- this probe should not be promoted to the production worker unchanged.
