module proof.DGG.Catchup.LeftValueCatchupDef where

-- File Charter:
--   * Defines the source-cast fuel bound for left catch-up.
--   * States fuel-indexed source value catch-up, both boundary-general and
--     closed same-boundary.
--   * Charges source-side cast heads only; target cast heads are structural
--     wrappers around the fixed target value.
--   * Contains no catch-up proof.

open import Data.List using ([])
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import Types using (Ty; TyVar)
open import CastTerms using (Term; Value)
open import proof.Consistency using (castSize)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Catchup.LeftBoundaryCatchupDef
  using (LeftCatchupResult)
open import proof.DGG.CatchupToMorePreciseDef
  using (CatchupBoundary; CatchupBoundaryKind; same-boundary)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld)
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


SourceCastBound : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → ℕ
  → W ∣ γ ⊢² M ⊑ M′ ∶ q
  → Set
SourceCastBound fuel (CTI2.x⊑x² x∈) = ⊤
SourceCastBound fuel (CTI2.ƛ⊑ƛ² rel) = SourceCastBound fuel rel
SourceCastBound fuel (CTI2.·⊑·² rel₁ rel₂) =
  SourceCastBound fuel rel₁ × SourceCastBound fuel rel₂
SourceCastBound fuel (CTI2.Λ⊑Λ² liftγ vV vV′ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.Λ⊑² Anv z∈A liftγ vV M⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV M⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.•⊑•² p∀ rel q r) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.•⊑² p∀ rel q r) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.κ⊑κ² κ p) = ⊤
SourceCastBound fuel (CTI2.cast⊑cast² c c′ rel q) =
  castSize c < fuel × SourceCastBound fuel rel
SourceCastBound fuel (CTI2.⊑cast² c′ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.⊑reveal² mono rb sameγ c′⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.⊑conceal² mono rb sameγ c′⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.cast⊑² c rel q) =
  castSize c < fuel × SourceCastBound fuel rel
SourceCastBound fuel (CTI2.reveal⊑² mono rb sameγ c⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel
    (CTI2.conceal⊑² mono rb sameγ c⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel
    (CTI2.reveal⊑reveal² mono rb sameγ c⊢ c′⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel
    (CTI2.conceal⊑conceal² mono rb sameγ c⊢ c′⊢ rel q) =
  SourceCastBound fuel rel
SourceCastBound fuel (CTI2.blame⊑² M′⊢ p) = ⊤
SourceCastBound fuel (CTI2.⊕⊑⊕² op rel₁ rel₂ r) =
  SourceCastBound fuel rel₁ × SourceCastBound fuel rel₂


LeftValueCatchupBoundaryAt : ℕ → Set
LeftValueCatchupBoundaryAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {kind : CatchupBoundaryKind}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → ParkedWorld W
  → CatchupBoundary kind Xᴸ? Xᴿ? W Wᵖ
  → (rel : Wᵖ ∣ [] ⊢² M ⊑ V′ ∶ q)
  → Value V′
  → SourceCastBound fuel rel
  → LeftCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = kind}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {M = M} {V′ = V′} {A = A} {B = B}


LeftValueCatchupAt : ℕ → Set
LeftValueCatchupAt fuel =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → (rel : W ∣ [] ⊢² M ⊑ V′ ∶ q)
  → Value V′
  → SourceCastBound fuel rel
  → LeftCatchupResult
      {W = W} {Wᵖ = W}
      {kind = same-boundary}
      {Xᴸ? = nothing} {Xᴿ? = nothing}
      {M = M} {V′ = V′} {A = A} {B = B}
