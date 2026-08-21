module proof.DGG.TransportTermImprecisionProof where

-- File Charter:
--   * Implements the parked-evolution driver for CTI2 term-imprecision
--     transport from the source-only and paired single-bind transports.
--   * Discharges the right-only bind case with the existing parked-to-target
--     world extension bridge and target-extension theorem.
--   * Keeps the source-only and paired bind inductions as explicit inputs.

open import Data.List using ([]; _∷_)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
  renaming (subst to subst≡)

open import CastTerms using (Term)
import Consistency
open import Imprecision using (X⊑X; X⊑★)
import Reduction
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
open CTI2 using
  (World;
   CtxImp;
   ctx-imp;
   _⊑ᵂ⟨_⟩_)
open CTIR using (_∣_⊢²_⊑_∶_)
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Parked.ParkedWorldDef
  using
    ( ParkedEvolve
    ; evolve-refl
    ; evolve-keepᴸ
    ; evolve-keepᴿ
    ; evolve-left-bind
    ; evolve-right-bind
    ; evolve-both-bind
    ; evolve-structural-right-bind
    )
open import proof.DGG.Parked.ParkedWorldLemma
  using (mapCtxᴾ; right-only-parked→world-extendᴿ; transport⊑ᴾ)
open import proof.DGG.TargetExtend using (⊢²-target-extend-bind)
import proof.DGG.TargetExtend as TE
open import proof.TypeInTermSubst using (renameᵗ-wk-eq)
open import proof.DGG.TransportTermImprecisionDef
  using
    ( BothBindTransport²ᵀ
    ; SourceBindTransport²ᵀ
    ; TargetInsertProvenanceᵀ
    ; TransportTermImprecisionCtxᴾᵀ
    ; TransportTermImprecisionᴾᵀ
    )


mapCtxᴾ-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    (γ : CtxImp W)
  → mapCtxᴾ evolve-refl γ ≡ γ
mapCtxᴾ-refl [] = refl
mapCtxᴾ-refl (ctx-imp A B p ∷ γ) =
  cong (λ γ′ → ctx-imp A B p ∷ γ′) (mapCtxᴾ-refl γ)


mapCtxᴾ-keepᴸ : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : Reduction.StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : Reduction.StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → (evol : ParkedEvolve χsᴸ χsᴿ W W′)
  → (γ : CtxImp W)
  → mapCtxᴾ evol γ ≡ mapCtxᴾ (evolve-keepᴸ evol) γ
mapCtxᴾ-keepᴸ evol [] = refl
mapCtxᴾ-keepᴸ evol (ctx-imp A B p ∷ γ) =
  cong (λ γ′ → ctx-imp _ _ _ ∷ γ′) (mapCtxᴾ-keepᴸ evol γ)


mapCtxᴾ-keepᴿ : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : Reduction.StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : Reduction.StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → (evol : ParkedEvolve χsᴸ χsᴿ W W′)
  → (γ : CtxImp W)
  → mapCtxᴾ evol γ ≡ mapCtxᴾ (evolve-keepᴿ evol) γ
mapCtxᴾ-keepᴿ evol [] = refl
mapCtxᴾ-keepᴿ evol (ctx-imp A B p ∷ γ) =
  cong (λ γ′ → ctx-imp _ _ _ ∷ γ′) (mapCtxᴾ-keepᴿ evol γ)


mapCtxᴾ-left-bind : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : Reduction.StoreChanges (Nat.suc Δᴸ) Δᴸ′}
    {χsᴿ : Reduction.StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {A₀}
  → (evol : ParkedEvolve χsᴸ χsᴿ (CTI2.leftOnlyWorld W A₀) W′)
  → (γ : CtxImp W)
  → mapCtxᴾ evol
      (mapCtxᴾ (evolve-left-bind {W = W} {A = A₀} evolve-refl) γ)
      ≡ mapCtxᴾ (evolve-left-bind {W = W} {A = A₀} evol) γ
mapCtxᴾ-left-bind evol [] = refl
mapCtxᴾ-left-bind evol (ctx-imp A B p ∷ γ) =
  cong (λ γ′ → ctx-imp _ _ _ ∷ γ′) (mapCtxᴾ-left-bind evol γ)


mapCtxᴾ-both-bind : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : Reduction.StoreChanges (Nat.suc Δᴸ) Δᴸ′}
    {χsᴿ : Reduction.StoreChanges (Nat.suc Δᴿ) Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {A₀ B₀} {bind-p : A₀ ⊑ᵂ⟨ W ⟩ B₀}
  → (evol : ParkedEvolve χsᴸ χsᴿ
      (CTI2.bothBindWorld W A₀ B₀ bind-p) W′)
  → (γ : CtxImp W)
  → mapCtxᴾ evol
      (mapCtxᴾ
        (evolve-both-bind {W = W} {A = A₀} {B = B₀}
          {p = bind-p} evolve-refl) γ)
      ≡ mapCtxᴾ
        (evolve-both-bind {W = W} {A = A₀} {B = B₀}
          {p = bind-p} evol) γ
mapCtxᴾ-both-bind evol [] = refl
mapCtxᴾ-both-bind evol (ctx-imp A B p ∷ γ) =
  cong (λ γ′ → ctx-imp _ _ _ ∷ γ′) (mapCtxᴾ-both-bind evol γ)


mapCtxᴾ-right-bind : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : Reduction.StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : Reduction.StoreChanges (Nat.suc Δᴿ) Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {B₀} {fresh : CTI2.RightBindFresh W B₀}
  → (evol : ParkedEvolve χsᴸ χsᴿ
      (CTI2.rightOnlyWorld W B₀ fresh) W′)
  → (γ : CtxImp W)
  → let ext = right-only-parked→world-extendᴿ
          (evolve-right-bind {W = W} {B = B₀} {fresh = fresh}
            evolve-refl)
     in mapCtxᴾ evol (ECR.mapCtxᴿ ext γ)
        ≡ mapCtxᴾ (evolve-right-bind {W = W} {B = B₀}
          {fresh = fresh} evol) γ
mapCtxᴾ-right-bind evol [] = refl
mapCtxᴾ-right-bind evol (ctx-imp A B p ∷ γ) =
  cong (λ γ′ → ctx-imp _ _ _ ∷ γ′) (mapCtxᴾ-right-bind evol γ)


mapCtxᴾ-structural-right-bind : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ₁ Δ′}
    {χsᴸ : Reduction.StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : Reduction.StoreChanges (Nat.suc Δᴿ) Δᴿ′}
    {W : World Δᴸ Δᴿ Δ}
    {W₁ : World Δᴸ (Nat.suc Δᴿ) Δ₁}
    {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {B₀} {π}
  → (ins : TE.TargetInsert Consistency.wk↪ᵗ π W W₁)
  → (follows : CTI2.targetStoreʷ W₁ ≡
      Reduction.applyStore (Reduction.bind B₀) (CTI2.targetStoreʷ W))
  → (evol : ParkedEvolve χsᴸ χsᴿ W₁ W′)
  → (γ : CtxImp W)
  → mapCtxᴾ evol (TE.mapCtxᵀ ins γ)
      ≡ mapCtxᴾ (evolve-structural-right-bind ins follows evol) γ
mapCtxᴾ-structural-right-bind ins follows evol [] = refl
mapCtxᴾ-structural-right-bind {χsᴿ = χsᴿ}
    ins follows evol (ctx-imp A B p ∷ γ) =
  cong₂ _∷_ entry-eq
    (mapCtxᴾ-structural-right-bind ins follows evol γ)
  where
  entry-eq =
    TE.ctx-imp-target-eq
      (cong (Reduction.applyTys χsᴿ) (renameᵗ-wk-eq B))


transport-term-imprecision-ctx :
  SourceBindTransport²ᵀ
  → BothBindTransport²ᵀ
  → TargetInsertProvenanceᵀ
  → TransportTermImprecisionCtxᴾᵀ
transport-term-imprecision-ctx src both target-provenance
    {W = W} {γ = γ} {M = M} {M′ = M′} {p = p}
    evolve-refl M⊑M′ =
  subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ M′ ∶ p)
    (sym (mapCtxᴾ-refl γ)) M⊑M′
transport-term-imprecision-ctx src both target-provenance
    {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
    {W′ = W′} {γ = γ} {M = M} {M′ = M′} {p = p}
    (evolve-keepᴸ evol) M⊑M′ =
  subst≡
    (λ γ′ → W′ ∣ γ′ ⊢²
      Reduction.applyTerms χsᴸ M ⊑ Reduction.applyTerms χsᴿ M′
        ∶ transport⊑ᴾ evol p)
    (mapCtxᴾ-keepᴸ evol γ)
    (transport-term-imprecision-ctx src both target-provenance evol M⊑M′)
transport-term-imprecision-ctx src both target-provenance
    {χsᴸ = χsᴸ} {χsᴿ = χsᴿ}
    {W′ = W′} {γ = γ} {M = M} {M′ = M′} {p = p}
    (evolve-keepᴿ evol) M⊑M′ =
  subst≡
    (λ γ′ → W′ ∣ γ′ ⊢²
      Reduction.applyTerms χsᴸ M ⊑ Reduction.applyTerms χsᴿ M′
        ∶ transport⊑ᴾ evol p)
    (mapCtxᴾ-keepᴿ evol γ)
    (transport-term-imprecision-ctx src both target-provenance evol M⊑M′)
transport-term-imprecision-ctx src both target-provenance
    (evolve-left-bind {W′ = W′} {A = A₀} evol) M⊑M′ =
  subst≡
    (λ γ′ → W′ ∣ γ′ ⊢² _ ⊑ _ ∶ _)
    (mapCtxᴾ-left-bind evol _)
    (transport-term-imprecision-ctx src both target-provenance evol
      (src {A₀ = A₀} M⊑M′))
transport-term-imprecision-ctx src both target-provenance
    (evolve-right-bind {W = W} {W′ = W′} {B = B₀}
      {fresh = fresh} evol) M⊑M′ =
  subst≡
    (λ γ′ → W′ ∣ γ′ ⊢² _ ⊑ _ ∶ _)
    (mapCtxᴾ-right-bind evol _)
    (transport-term-imprecision-ctx src both target-provenance evol
      (⊢²-target-extend-bind
        (right-only-parked→world-extendᴿ
          (evolve-right-bind {W = W} {B = B₀} {fresh = fresh}
            evolve-refl))
        M⊑M′
        (target-provenance
          (CTI2.rightOnlyWorld W B₀ fresh)
          (TE.rightBindTargetInsert fresh) M⊑M′)))
transport-term-imprecision-ctx src both target-provenance
    {W′ = W′}
    (evolve-structural-right-bind ins follows evol) M⊑M′ =
  subst≡
    (λ γ′ → W′ ∣ γ′ ⊢² _ ⊑ _ ∶ _)
    (mapCtxᴾ-structural-right-bind ins follows evol _)
    (transport-term-imprecision-ctx src both target-provenance evol
      (TE.⊢²-retargetᴿ (renameᵗ-wk-eq _)
        (TE.⊢²-target-insert _ ins M⊑M′
          (target-provenance _ ins M⊑M′))))
transport-term-imprecision-ctx src both target-provenance
    (evolve-both-bind {W′ = W′} {A = A₀} {B = B₀}
      {p = bind-p} evol) M⊑M′ =
  subst≡
    (λ γ′ → W′ ∣ γ′ ⊢² _ ⊑ _ ∶ _)
    (mapCtxᴾ-both-bind evol _)
    (transport-term-imprecision-ctx src both target-provenance evol
      (both {A₀ = A₀} {B₀ = B₀} bind-p M⊑M′))


transport-term-imprecision :
  SourceBindTransport²ᵀ
  → BothBindTransport²ᵀ
  → TargetInsertProvenanceᵀ
  → TransportTermImprecisionᴾᵀ
transport-term-imprecision src both target-provenance evol M⊑M′ =
  transport-term-imprecision-ctx src both target-provenance evol M⊑M′
