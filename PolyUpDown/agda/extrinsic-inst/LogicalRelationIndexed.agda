module LogicalRelationIndexed where

-- File Charter:
--   * Indexed logical-relation core for `PolyUpDown`.
--   * This is the migration target from `LogicalRelation`: the relation is
--     indexed by `ImprecisionIndexed._⊢_⊑ᵢ_` and interprets an indexed type
--     context at the current world before applying the relational substitution.
--   * The key invariant is that `𝒱`/`ℰ` should be used at closed interpreted
--     types: ν-bound variables become the runtime seals recorded in the world,
--     while plain type variables are supplied by `RelSub`.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
  using
    ( ℕ; zero; suc; z<s; z≤n; s<s; s≤s; _+_; _∸_; _<_; _≤_; _<′_
    ; <′-base; ≤′-step; ≤′-reflexive
    )
open import Data.Nat.Properties
  using
    ( ≤-refl; ≤-trans; n≤1+n; m≤n⇒m≤1+n; m+[n∸m]≡n
    ; +-comm; <-≤-trans
    )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; 0ℓ; lift) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no)

open import Types
open import Store
  using (_⊆ˢ_; ⊆ˢ-refl; ⊆ˢ-trans; done; keep; drop;
         StoreWf; LookupStoreAny; uniq∷_; storeWf-unique; storeWf-wfTy;
         storeWf-dom<; storeWf-dom∋; storeWf-length)
open import ImprecisionIndexed
open import TypeProperties
  using (renameᵗ-preserves-WfTy; renameˢ-preserves-WfTy;
         TyRenameWf-suc; SealRenameWf-suc; TySubstWf)
open import UpDown using (WfTy-weakenᵗ; WfTy-weakenˢ; Label; tag; seal)
open import Terms
open import ReductionFresh using (Value; _∣_—→_∣_; _∣_—↠_∣_)
open import ProgressFresh
  using
    ( canonical-★
    ; canonical-｀
    ; StarView
    ; sv-up-tag
    ; SealView
    ; sv-down-seal
    )
open import PreservationFresh
  using (wkΨ-term-suc; len<suc-StoreWf; length∉dom-StoreWf)

------------------------------------------------------------------------
-- Direction and semantic relations
------------------------------------------------------------------------

data Dir : Set where
  ≼ : Dir
  ≽ : Dir

Rel : Set₁
Rel = ℕ → Dir → Term → Term → Set

DownClosed : Rel → Set
DownClosed R = ∀ {k dir V W} → R (suc k) dir V W → R k dir V W

sealedRel : Seal → Seal → Rel → Rel
sealedRel αˡ αʳ R k dir V W =
  Σ[ V′ ∈ Term ] Σ[ W′ ∈ Term ] Σ[ pˡ ∈ UpDown.Down ] Σ[ pʳ ∈ UpDown.Down ]
    (V ≡ (V′ down seal pˡ αˡ)) ×
    (W ≡ (W′ down seal pʳ αʳ)) ×
    R k dir (V′ down pˡ) (W′ down pʳ)

sealedRel-down :
  ∀ {αˡ αʳ R} →
  DownClosed R →
  DownClosed (sealedRel αˡ αʳ R)
sealedRel-down downR (V′ , W′ , pˡ , pʳ , eqV , eqW , rel) =
  V′ , W′ , pˡ , pʳ , eqV , eqW , downR rel

WfTyClosedᵗ : Ty → Set
WfTyClosedᵗ A = Σ[ Ψ ∈ SealCtx ] WfTy 0 Ψ A

plainCount : ICtx → TyCtx
plainCount [] = 0
plainCount (plain ∷ Ξ) = suc (plainCount Ξ)
plainCount (ν-bound ∷ Ξ) = plainCount Ξ

record SealRel : Set₁ where
  constructor ηentry
  field
    αˡ : Seal
    αʳ : Seal
    Rη : Rel
    downη : DownClosed Rη
open SealRel public

infix 4 _∋η_↔_∶_

data _∋η_↔_∶_ : List SealRel → Seal → Seal → Rel → Set₁ where
  hereη :
    ∀ {η αˡ αʳ R} {dR : DownClosed R} →
    (ηentry αˡ αʳ R dR ∷ η) ∋η αˡ ↔ αʳ ∶ R

  thereη :
    ∀ {η αˡ αʳ R βˡ βʳ R′} {dR′ : DownClosed R′} →
    η ∋η αˡ ↔ αʳ ∶ R →
    (ηentry βˡ βʳ R′ dR′ ∷ η) ∋η αˡ ↔ αʳ ∶ R

infix 4 _⊆η_

data _⊆η_ : List SealRel → List SealRel → Set₁ where
  η-done : ∀ {η} → [] ⊆η η
  η-keep : ∀ {η η′ e} → η ⊆η η′ → (e ∷ η) ⊆η (e ∷ η′)
  η-drop : ∀ {η η′ e} → η ⊆η η′ → η ⊆η (e ∷ η′)

⊆η-refl : ∀ {η} → η ⊆η η
⊆η-refl {η = []} = η-done
⊆η-refl {η = e ∷ η} = η-keep ⊆η-refl

⊆η-trans : ∀ {η₁ η₂ η₃} → η₁ ⊆η η₂ → η₂ ⊆η η₃ → η₁ ⊆η η₃
⊆η-trans η-done η₂₃ = η-done
⊆η-trans (η-keep η₁₂) (η-keep η₂₃) =
  η-keep (⊆η-trans η₁₂ η₂₃)
⊆η-trans (η-keep η₁₂) (η-drop η₂₃) =
  η-drop (⊆η-trans (η-keep η₁₂) η₂₃)
⊆η-trans (η-drop η₁₂) (η-keep η₂₃) =
  η-drop (⊆η-trans η₁₂ η₂₃)
⊆η-trans (η-drop η₁₂) (η-drop η₂₃) =
  η-drop (⊆η-trans (η-drop η₁₂) η₂₃)

ηWfˡ : SealCtx → List SealRel → Set₁
ηWfˡ Ψ [] = Lift (lsuc 0ℓ) ⊤
ηWfˡ Ψ (e ∷ η) = αˡ e < Ψ × ηWfˡ Ψ η

ηWfʳ : SealCtx → List SealRel → Set₁
ηWfʳ Ψ [] = Lift (lsuc 0ℓ) ⊤
ηWfʳ Ψ (e ∷ η) = αʳ e < Ψ × ηWfʳ Ψ η

ηWfˡ-weaken :
  ∀ {Ψ Ψ′ η} →
  Ψ ≤ Ψ′ →
  ηWfˡ Ψ η →
  ηWfˡ Ψ′ η
ηWfˡ-weaken {η = []} Ψ≤ wfη = lift tt
ηWfˡ-weaken {η = e ∷ η} Ψ≤ (α<Ψ , wfη) =
  <-≤-trans α<Ψ Ψ≤ , ηWfˡ-weaken Ψ≤ wfη

ηWfʳ-weaken :
  ∀ {Ψ Ψ′ η} →
  Ψ ≤ Ψ′ →
  ηWfʳ Ψ η →
  ηWfʳ Ψ′ η
ηWfʳ-weaken {η = []} Ψ≤ wfη = lift tt
ηWfʳ-weaken {η = e ∷ η} Ψ≤ (α<Ψ , wfη) =
  <-≤-trans α<Ψ Ψ≤ , ηWfʳ-weaken Ψ≤ wfη

data νFits : ICtx → List SealRel → Set₁ where
  fits-[] : νFits [] []
  fits-plain : ∀ {Ξ η} → νFits Ξ η → νFits (plain ∷ Ξ) η
  fits-ν : ∀ {Ξ η e} → νFits Ξ η → νFits (ν-bound ∷ Ξ) (e ∷ η)

νFits-tailPlain :
  ∀ {Ξ η} →
  νFits (plain ∷ Ξ) η →
  νFits Ξ η
νFits-tailPlain (fits-plain fit) = fit

νenv-tailν :
  ∀ {Ξ η} →
  νFits (ν-bound ∷ Ξ) η →
  List SealRel
νenv-tailν (fits-ν {η = η} fit) = η

νFits-tailν :
  ∀ {Ξ η} →
  (fit : νFits (ν-bound ∷ Ξ) η) →
  νFits Ξ (νenv-tailν fit)
νFits-tailν (fits-ν fit) = fit

ηWfˡ-tailν :
  ∀ {Ξ Ψ η} →
  (fit : νFits (ν-bound ∷ Ξ) η) →
  ηWfˡ Ψ η →
  ηWfˡ Ψ (νenv-tailν fit)
ηWfˡ-tailν (fits-ν fit) (α<Ψ , wfη) = wfη

ηWfʳ-tailν :
  ∀ {Ξ Ψ η} →
  (fit : νFits (ν-bound ∷ Ξ) η) →
  ηWfʳ Ψ η →
  ηWfʳ Ψ (νenv-tailν fit)
ηWfʳ-tailν (fits-ν fit) (α<Ψ , wfη) = wfη

record World : Set₁ where
  constructor mkWorld
  field
    Ψˡ : SealCtx
    Ψʳ : SealCtx
    Σˡ : Store
    Σʳ : Store
    wfΣˡ : StoreWf 0 Ψˡ Σˡ
    wfΣʳ : StoreWf 0 Ψʳ Σʳ
    η : List SealRel
open World public

record _⪰_ (w′ w : World) : Set₁ where
  field
    growΨˡ : Ψˡ w ≤ Ψˡ w′
    growΨʳ : Ψʳ w ≤ Ψʳ w′
    growˡ : Σˡ w ⊆ˢ Σˡ w′
    growʳ : Σʳ w ⊆ˢ Σʳ w′
    growη : η w ⊆η η w′

⪰-refl : ∀ {w} → w ⪰ w
⪰-refl ._⪰_.growΨˡ = ≤-refl
⪰-refl ._⪰_.growΨʳ = ≤-refl
⪰-refl ._⪰_.growˡ = ⊆ˢ-refl
⪰-refl ._⪰_.growʳ = ⊆ˢ-refl
⪰-refl ._⪰_.growη = ⊆η-refl

⪰-trans : ∀ {w₁ w₂ w₃} → w₃ ⪰ w₂ → w₂ ⪰ w₁ → w₃ ⪰ w₁
⪰-trans w₃⪰w₂ w₂⪰w₁ ._⪰_.growΨˡ =
  ≤-trans (_⪰_.growΨˡ w₂⪰w₁) (_⪰_.growΨˡ w₃⪰w₂)
⪰-trans w₃⪰w₂ w₂⪰w₁ ._⪰_.growΨʳ =
  ≤-trans (_⪰_.growΨʳ w₂⪰w₁) (_⪰_.growΨʳ w₃⪰w₂)
⪰-trans w₃⪰w₂ w₂⪰w₁ ._⪰_.growˡ =
  ⊆ˢ-trans (_⪰_.growˡ w₂⪰w₁) (_⪰_.growˡ w₃⪰w₂)
⪰-trans w₃⪰w₂ w₂⪰w₁ ._⪰_.growʳ =
  ⊆ˢ-trans (_⪰_.growʳ w₂⪰w₁) (_⪰_.growʳ w₃⪰w₂)
⪰-trans w₃⪰w₂ w₂⪰w₁ ._⪰_.growη =
  ⊆η-trans (_⪰_.growη w₂⪰w₁) (_⪰_.growη w₃⪰w₂)

⊆ˢ-length≤ : ∀ {Σ Σ′} → Σ ⊆ˢ Σ′ → length Σ ≤ length Σ′
⊆ˢ-length≤ done = z≤n
⊆ˢ-length≤ (keep grow) = s≤s (⊆ˢ-length≤ grow)
⊆ˢ-length≤ (drop grow) = m≤n⇒m≤1+n (⊆ˢ-length≤ grow)

pred-<ᴿ :
  ∀ {α Ψ} →
  α < suc Ψ →
  α ≢ Ψ →
  α < Ψ
pred-<ᴿ {zero} {zero} z<s α≢Ψ = ⊥-elim (α≢Ψ refl)
pred-<ᴿ {zero} {suc Ψ} z<s α≢Ψ = z<s
pred-<ᴿ {suc α} {zero} (s<s ()) α≢Ψ
pred-<ᴿ {suc α} {suc Ψ} (s<s α<sucΨ) α≢sucΨ =
  s<s (pred-<ᴿ α<sucΨ (λ eq → α≢sucΨ (cong suc eq)))

storeWf-fresh-extᴿ :
  ∀ {Ψ Σ} {T : Ty} →
  WfTy 0 Ψ T →
  StoreWf 0 Ψ Σ →
  StoreWf 0 (suc Ψ) ((length Σ , T) ∷ Σ)
storeWf-fresh-extᴿ {Ψ = Ψ} {Σ = Σ} {T = T} wfT wfΣ =
  record
    { unique = uniq∷_ (length∉dom-StoreWf wfΣ) (storeWf-unique wfΣ)
    ; wfTy = wf
    ; dom< = domBound
    ; dom∋ = domAny
    ; len = cong suc (storeWf-length wfΣ)
    }
  where
  wf : ∀ {α A} → ((length Σ , T) ∷ Σ) ∋ˢ α ⦂ A → WfTy 0 (suc Ψ) A
  wf (Z∋ˢ α≡β A≡B) =
    subst (WfTy 0 (suc Ψ)) (sym A≡B) (WfTy-weakenˢ wfT (n≤1+n _))
  wf (S∋ˢ h) = WfTy-weakenˢ (storeWf-wfTy wfΣ h) (n≤1+n _)

  domBound : ∀ {α A} → ((length Σ , T) ∷ Σ) ∋ˢ α ⦂ A → α < suc Ψ
  domBound (Z∋ˢ α≡β A≡B) =
    subst (λ γ → γ < suc Ψ) (sym α≡β) (len<suc-StoreWf wfΣ)
  domBound (S∋ˢ h) = <-≤-trans (storeWf-dom< wfΣ h) (n≤1+n _)

  domAny : ∀ {α} → α < suc Ψ → LookupStoreAny ((length Σ , T) ∷ Σ) α
  domAny {α} α<sucΨ with seal-≟ α (length Σ)
  domAny {α} α<sucΨ | yes α≡len = T , Z∋ˢ α≡len refl
  domAny {α} α<sucΨ | no α≢len with
    storeWf-dom∋ wfΣ
      (pred-<ᴿ α<sucΨ (λ eq → α≢len (trans eq (sym (storeWf-length wfΣ)))))
  domAny {α} α<sucΨ | no α≢len | A , h = A , S∋ˢ h

extendWorldν :
  (w : World) →
  (R : Rel) → DownClosed R →
  (Tˡ Tʳ : Ty) →
  WfTy 0 (Ψˡ w) Tˡ →
  WfTy 0 (Ψʳ w) Tʳ →
  World
extendWorldν w R downR Tˡ Tʳ hTˡ hTʳ =
  mkWorld (suc (Ψˡ w)) (suc (Ψʳ w))
    ((length (Σˡ w) , Tˡ) ∷ Σˡ w)
    ((length (Σʳ w) , Tʳ) ∷ Σʳ w)
    (storeWf-fresh-extᴿ hTˡ (wfΣˡ w))
    (storeWf-fresh-extᴿ hTʳ (wfΣʳ w))
    (ηentry (length (Σˡ w)) (length (Σʳ w)) R downR ∷ η w)

extendWorldν-⪰ :
  ∀ {w} (R : Rel) (downR : DownClosed R) Tˡ Tʳ hTˡ hTʳ →
  extendWorldν w R downR Tˡ Tʳ hTˡ hTʳ ⪰ w
extendWorldν-⪰ R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growΨˡ =
  n≤1+n _
extendWorldν-⪰ R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growΨʳ =
  n≤1+n _
extendWorldν-⪰ R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growˡ = drop ⊆ˢ-refl
extendWorldν-⪰ R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growʳ = drop ⊆ˢ-refl
extendWorldν-⪰ R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growη =
  η-drop ⊆η-refl

mkWorldˡ :
  (w : World) →
  (Σˡ′ : Store) →
  ∀ {Ψˡ′} →
  StoreWf 0 Ψˡ′ Σˡ′ →
  World
mkWorldˡ w Σˡ′ wfΣˡ′ =
  mkWorld _ (Ψʳ w) Σˡ′ (Σʳ w) wfΣˡ′ (wfΣʳ w) (η w)

mkWorldʳ :
  (w : World) →
  (Σʳ′ : Store) →
  ∀ {Ψʳ′} →
  StoreWf 0 Ψʳ′ Σʳ′ →
  World
mkWorldʳ w Σʳ′ wfΣʳ′ =
  mkWorld (Ψˡ w) _ (Σˡ w) Σʳ′ (wfΣˡ w) wfΣʳ′ (η w)

mkWorldˡʳ :
  (w : World) →
  (Σˡ′ : Store) →
  ∀ {Ψˡ′} →
  StoreWf 0 Ψˡ′ Σˡ′ →
  (Σʳ′ : Store) →
  ∀ {Ψʳ′} →
  StoreWf 0 Ψʳ′ Σʳ′ →
  World
mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′ =
  mkWorld _ _ Σˡ′ Σʳ′ wfΣˡ′ wfΣʳ′ (η w)

extendWorldν-⪰-currentˡ :
  ∀ {w R Tˡ Tʳ hTˡ hTʳ} (downR : DownClosed R) →
  extendWorldν w R downR Tˡ Tʳ hTˡ hTʳ ⪰
  mkWorldˡʳ w
    ((length (Σˡ w) , Tˡ) ∷ Σˡ w)
    (storeWf-fresh-extᴿ hTˡ (wfΣˡ w))
    (Σʳ w)
    (wfΣʳ w)
extendWorldν-⪰-currentˡ downR ._⪰_.growΨˡ = ≤-refl
extendWorldν-⪰-currentˡ downR ._⪰_.growΨʳ = n≤1+n _
extendWorldν-⪰-currentˡ downR ._⪰_.growˡ = ⊆ˢ-refl
extendWorldν-⪰-currentˡ downR ._⪰_.growʳ = drop ⊆ˢ-refl
extendWorldν-⪰-currentˡ downR ._⪰_.growη = η-drop ⊆η-refl

ℕ-payload : Term → Term → Set₁
ℕ-payload ($ (κℕ m)) ($ (κℕ m′)) = Lift (lsuc 0ℓ) (m ≡ m′)
ℕ-payload V W = Lift (lsuc 0ℓ) ⊥

lift⊤ : Lift (lsuc 0ℓ) ⊤
lift⊤ = lift tt

------------------------------------------------------------------------
-- Closed relational substitutions for indexed contexts
------------------------------------------------------------------------

record RelSub (Ξ : ICtx) : Set₁ where
  field
    νenv : List SealRel
    νenv-fit : νFits Ξ νenv
    leftᵗ : Substᵗ
    rightᵗ : Substᵗ
    left-closed : (X : TyVar) → WfTyClosedᵗ (leftᵗ X)
    right-closed : (X : TyVar) → WfTyClosedᵗ (rightᵗ X)
    precᵗ : (X : TyVar) → [] ⊢ leftᵗ X ⊑ᵢ rightᵗ X
    relᵗ : (X : TyVar) → Rel
    rel-downᵗ : (X : TyVar) → DownClosed (relᵗ X)
open RelSub public

record RelWf {Ξ : ICtx} (w : World) (ρ : RelSub Ξ) : Set₁ where
  field
    νenv⊆η : νenv ρ ⊆η η w
    νenvˡ-wf : ηWfˡ (Ψˡ w) (νenv ρ)
    νenvʳ-wf : ηWfʳ (Ψʳ w) (νenv ρ)
    leftᵗ-wf : TySubstWf (plainCount Ξ) 0 (Ψˡ w) (leftᵗ ρ)
    rightᵗ-wf : TySubstWf (plainCount Ξ) 0 (Ψʳ w) (rightᵗ ρ)
open RelWf public

RelWf-⪰ :
  ∀ {Ξ w w′} {ρ : RelSub Ξ} →
  w′ ⪰ w →
  RelWf w ρ →
  RelWf w′ ρ
RelWf-⪰ w′⪰w wf .RelWf.νenv⊆η =
  ⊆η-trans (νenv⊆η wf) (_⪰_.growη w′⪰w)
RelWf-⪰ w′⪰w wf .RelWf.νenvˡ-wf =
  ηWfˡ-weaken (_⪰_.growΨˡ w′⪰w) (νenvˡ-wf wf)
RelWf-⪰ w′⪰w wf .RelWf.νenvʳ-wf =
  ηWfʳ-weaken (_⪰_.growΨʳ w′⪰w) (νenvʳ-wf wf)
RelWf-⪰ w′⪰w wf .RelWf.leftᵗ-wf X< =
  WfTy-weakenˢ (leftᵗ-wf wf X<) (_⪰_.growΨˡ w′⪰w)
RelWf-⪰ w′⪰w wf .RelWf.rightᵗ-wf X< =
  WfTy-weakenˢ (rightᵗ-wf wf X<) (_⪰_.growΨʳ w′⪰w)

------------------------------------------------------------------------
-- World-relative interpretation of indexed types
------------------------------------------------------------------------

interpLRVarˡ : ICtx → List SealRel → TyVar → Ty
interpLRVarˡ [] η X = ＇ X
interpLRVarˡ (plain ∷ Ξ) η zero = ＇ zero
interpLRVarˡ (plain ∷ Ξ) η (suc X) = ⇑ᵗ (interpLRVarˡ Ξ η X)
interpLRVarˡ (ν-bound ∷ Ξ) [] zero = ｀ zero
interpLRVarˡ (ν-bound ∷ Ξ) (e ∷ η) zero = ｀ (αˡ e)
interpLRVarˡ (ν-bound ∷ Ξ) [] (suc X) = interpLRVarˡ Ξ [] X
interpLRVarˡ (ν-bound ∷ Ξ) (e ∷ η) (suc X) = interpLRVarˡ Ξ η X

interpLRVarʳ : ICtx → List SealRel → TyVar → Ty
interpLRVarʳ [] η X = ＇ X
interpLRVarʳ (plain ∷ Ξ) η zero = ＇ zero
interpLRVarʳ (plain ∷ Ξ) η (suc X) = ⇑ᵗ (interpLRVarʳ Ξ η X)
interpLRVarʳ (ν-bound ∷ Ξ) [] zero = ｀ zero
interpLRVarʳ (ν-bound ∷ Ξ) (e ∷ η) zero = ｀ (αʳ e)
interpLRVarʳ (ν-bound ∷ Ξ) [] (suc X) = interpLRVarʳ Ξ [] X
interpLRVarʳ (ν-bound ∷ Ξ) (e ∷ η) (suc X) = interpLRVarʳ Ξ η X

interpLRˡ : ICtx → List SealRel → Ty → Ty
interpLRˡ Ξ η (＇ X) = interpLRVarˡ Ξ η X
interpLRˡ Ξ η (｀ α) = ｀ α
interpLRˡ Ξ η (‵ ι) = ‵ ι
interpLRˡ Ξ η ★ = ★
interpLRˡ Ξ η (A ⇒ B) = interpLRˡ Ξ η A ⇒ interpLRˡ Ξ η B
interpLRˡ Ξ η (`∀ A) = `∀ (interpLRˡ (plain ∷ Ξ) η A)

interpLRʳ : ICtx → List SealRel → Ty → Ty
interpLRʳ Ξ η (＇ X) = interpLRVarʳ Ξ η X
interpLRʳ Ξ η (｀ α) = ｀ α
interpLRʳ Ξ η (‵ ι) = ‵ ι
interpLRʳ Ξ η ★ = ★
interpLRʳ Ξ η (A ⇒ B) = interpLRʳ Ξ η A ⇒ interpLRʳ Ξ η B
interpLRʳ Ξ η (`∀ A) = `∀ (interpLRʳ (plain ∷ Ξ) η A)

leftᵢ : ∀ {Ξ} → RelSub Ξ → World → Ty → Ty
leftᵢ {Ξ = Ξ} ρ w A = substᵗ (leftᵗ ρ) (interpLRˡ Ξ (νenv ρ) A)

rightᵢ : ∀ {Ξ} → RelSub Ξ → World → Ty → Ty
rightᵢ {Ξ = Ξ} ρ w A = substᵗ (rightᵗ ρ) (interpLRʳ Ξ (νenv ρ) A)

left∀ᵢ : ∀ {Ξ} → RelSub Ξ → World → Ty → Ty
left∀ᵢ {Ξ = Ξ} ρ w A =
  substᵗ (extsᵗ (leftᵗ ρ)) (interpLRˡ (plain ∷ Ξ) (νenv ρ) A)

right∀ᵢ : ∀ {Ξ} → RelSub Ξ → World → Ty → Ty
right∀ᵢ {Ξ = Ξ} ρ w A =
  substᵗ (extsᵗ (rightᵗ ρ)) (interpLRʳ (plain ∷ Ξ) (νenv ρ) A)

VHeader :
  ∀ {Ξ A B} →
  RelSub Ξ → World → Term → Term → Set
VHeader {A = A} {B = B} ρ w V W =
  Value V × Value W ×
  ((0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ leftᵢ ρ w A) ×
   (0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ rightᵢ ρ w B))

EHeader :
  ∀ {Ξ A B} →
  RelSub Ξ → World → Term → Term → Set
EHeader {A = A} {B = B} ρ w M N =
  (0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ M ⦂ leftᵢ ρ w A) ×
  (0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ N ⦂ rightᵢ ρ w B)

∅ρ : RelSub []
(∅ρ .νenv) = []
(∅ρ .νenv-fit) = fits-[]
(∅ρ .leftᵗ) = λ _ → ‵ `ℕ
(∅ρ .rightᵗ) = λ _ → ‵ `ℕ
(∅ρ .left-closed) = λ _ → 0 , wfBase
(∅ρ .right-closed) = λ _ → 0 , wfBase
(∅ρ .precᵗ) = λ _ → ⊑ᵢ-‵ `ℕ
(∅ρ .relᵗ) = λ _ k dir V W → Lift 0ℓ ⊥
(∅ρ .rel-downᵗ) = λ _ ()

extendPlainρ :
  ∀ {Ξ} →
  RelSub Ξ →
  (A B : Ty) →
  WfTyClosedᵗ A →
  WfTyClosedᵗ B →
  [] ⊢ A ⊑ᵢ B →
  (R : Rel) →
  DownClosed R →
  RelSub (plain ∷ Ξ)
(extendPlainρ ρ A B wfA wfB p R downR .νenv) = νenv ρ
(extendPlainρ ρ A B wfA wfB p R downR .νenv-fit) =
  fits-plain (νenv-fit ρ)
(extendPlainρ ρ A B wfA wfB p R downR .leftᵗ) zero = A
(extendPlainρ ρ A B wfA wfB p R downR .leftᵗ) (suc X) = leftᵗ ρ X
(extendPlainρ ρ A B wfA wfB p R downR .rightᵗ) zero = B
(extendPlainρ ρ A B wfA wfB p R downR .rightᵗ) (suc X) = rightᵗ ρ X
(extendPlainρ ρ A B wfA wfB p R downR .left-closed) zero = wfA
(extendPlainρ ρ A B wfA wfB p R downR .left-closed) (suc X) =
  left-closed ρ X
(extendPlainρ ρ A B wfA wfB p R downR .right-closed) zero = wfB
(extendPlainρ ρ A B wfA wfB p R downR .right-closed) (suc X) =
  right-closed ρ X
(extendPlainρ ρ A B wfA wfB p R downR .precᵗ) zero = p
(extendPlainρ ρ A B wfA wfB p R downR .precᵗ) (suc X) = precᵗ ρ X
(extendPlainρ ρ A B wfA wfB p R downR .relᵗ) zero = R
(extendPlainρ ρ A B wfA wfB p R downR .relᵗ) (suc X) = relᵗ ρ X
(extendPlainρ ρ A B wfA wfB p R downR .rel-downᵗ)
  zero {k} {dir} {V} {W} = downR {k} {dir} {V} {W}
(extendPlainρ ρ A B wfA wfB p R downR .rel-downᵗ) (suc X) =
  rel-downᵗ ρ X

extendνρ : ∀ {Ξ} → RelSub Ξ → SealRel → RelSub (ν-bound ∷ Ξ)
(extendνρ ρ e .νenv) = e ∷ νenv ρ
(extendνρ ρ e .νenv-fit) = fits-ν (νenv-fit ρ)
(extendνρ ρ e .leftᵗ) = leftᵗ ρ
(extendνρ ρ e .rightᵗ) = rightᵗ ρ
(extendνρ ρ e .left-closed) = left-closed ρ
(extendνρ ρ e .right-closed) = right-closed ρ
(extendνρ ρ e .precᵗ) = precᵗ ρ
(extendνρ ρ e .relᵗ) = relᵗ ρ
(extendνρ ρ e .rel-downᵗ) = rel-downᵗ ρ

tailPlainρ : ∀ {Ξ} → RelSub (plain ∷ Ξ) → RelSub Ξ
(tailPlainρ ρ .νenv) = νenv ρ
(tailPlainρ ρ .νenv-fit) = νFits-tailPlain (νenv-fit ρ)
(tailPlainρ ρ .leftᵗ) X = leftᵗ ρ (suc X)
(tailPlainρ ρ .rightᵗ) X = rightᵗ ρ (suc X)
(tailPlainρ ρ .left-closed) X = left-closed ρ (suc X)
(tailPlainρ ρ .right-closed) X = right-closed ρ (suc X)
(tailPlainρ ρ .precᵗ) X = precᵗ ρ (suc X)
(tailPlainρ ρ .relᵗ) X = relᵗ ρ (suc X)
(tailPlainρ ρ .rel-downᵗ) X = rel-downᵗ ρ (suc X)

tailνρ : ∀ {Ξ} → RelSub (ν-bound ∷ Ξ) → RelSub Ξ
(tailνρ ρ .νenv) = νenv-tailν (νenv-fit ρ)
(tailνρ ρ .νenv-fit) = νFits-tailν (νenv-fit ρ)
(tailνρ ρ .leftᵗ) = leftᵗ ρ
(tailνρ ρ .rightᵗ) = rightᵗ ρ
(tailνρ ρ .left-closed) = left-closed ρ
(tailνρ ρ .right-closed) = right-closed ρ
(tailνρ ρ .precᵗ) = precᵗ ρ
(tailνρ ρ .relᵗ) = relᵗ ρ
(tailνρ ρ .rel-downᵗ) = rel-downᵗ ρ

RelWf-tailPlainρ :
  ∀ {Ξ w} {ρ : RelSub (plain ∷ Ξ)} →
  RelWf w ρ →
  RelWf w (tailPlainρ ρ)
RelWf-tailPlainρ wf .RelWf.νenv⊆η = νenv⊆η wf
RelWf-tailPlainρ wf .RelWf.νenvˡ-wf = νenvˡ-wf wf
RelWf-tailPlainρ wf .RelWf.νenvʳ-wf = νenvʳ-wf wf
RelWf-tailPlainρ wf .RelWf.leftᵗ-wf X< =
  leftᵗ-wf wf (s<s X<)
RelWf-tailPlainρ wf .RelWf.rightᵗ-wf X< =
  rightᵗ-wf wf (s<s X<)

RelWf-tailνρ :
  ∀ {Ξ w} {ρ : RelSub (ν-bound ∷ Ξ)} →
  RelWf w ρ →
  RelWf w (tailνρ ρ)
RelWf-tailνρ {ρ = ρ} wf .RelWf.νenv⊆η = tail⊆ (νenv-fit ρ) (νenv⊆η wf)
  where
  tail⊆ :
    ∀ {Ξ η ηw} →
    (fit : νFits (ν-bound ∷ Ξ) η) →
    η ⊆η ηw →
    νenv-tailν fit ⊆η ηw
  tail⊆ (fits-ν fit) (η-keep incl) = η-drop incl
  tail⊆ (fits-ν fit) (η-drop incl) = η-drop (tail⊆ (fits-ν fit) incl)
RelWf-tailνρ {ρ = ρ} wf .RelWf.νenvˡ-wf =
  ηWfˡ-tailν (νenv-fit ρ) (νenvˡ-wf wf)
RelWf-tailνρ {ρ = ρ} wf .RelWf.νenvʳ-wf =
  ηWfʳ-tailν (νenv-fit ρ) (νenvʳ-wf wf)
RelWf-tailνρ wf .RelWf.leftᵗ-wf = leftᵗ-wf wf
RelWf-tailνρ wf .RelWf.rightᵗ-wf = rightᵗ-wf wf

RelWf-extendPlainρ :
  ∀ {Ξ w A B p R} {downR : DownClosed R} {ρ : RelSub Ξ}
    {wfA : WfTyClosedᵗ A} {wfB : WfTyClosedᵗ B} →
  RelWf w ρ →
  WfTy 0 (Ψˡ w) A →
  WfTy 0 (Ψʳ w) B →
  RelWf w (extendPlainρ ρ A B wfA wfB p R downR)
RelWf-extendPlainρ wf hA hB .RelWf.νenv⊆η = νenv⊆η wf
RelWf-extendPlainρ wf hA hB .RelWf.νenvˡ-wf = νenvˡ-wf wf
RelWf-extendPlainρ wf hA hB .RelWf.νenvʳ-wf = νenvʳ-wf wf
RelWf-extendPlainρ wf hA hB .RelWf.leftᵗ-wf {zero} z<s = hA
RelWf-extendPlainρ wf hA hB .RelWf.leftᵗ-wf {suc X} (s<s X<) =
  leftᵗ-wf wf X<
RelWf-extendPlainρ wf hA hB .RelWf.rightᵗ-wf {zero} z<s = hB
RelWf-extendPlainρ wf hA hB .RelWf.rightᵗ-wf {suc X} (s<s X<) =
  rightᵗ-wf wf X<

RelWf-extendνρ :
  ∀ {Ξ w R Tˡ Tʳ hTˡ hTʳ} {ρ : RelSub Ξ}
    (downR : DownClosed R) →
  RelWf w ρ →
  let e = ηentry (length (Σˡ w)) (length (Σʳ w)) R downR in
  RelWf (extendWorldν w R downR Tˡ Tʳ hTˡ hTʳ) (extendνρ ρ e)
RelWf-extendνρ downR wf .RelWf.νenv⊆η = η-keep (νenv⊆η wf)
RelWf-extendνρ {w = w} downR wf .RelWf.νenvˡ-wf =
  len<suc-StoreWf (wfΣˡ w) ,
  ηWfˡ-weaken (n≤1+n _) (νenvˡ-wf wf)
RelWf-extendνρ {w = w} downR wf .RelWf.νenvʳ-wf =
  len<suc-StoreWf (wfΣʳ w) ,
  ηWfʳ-weaken (n≤1+n _) (νenvʳ-wf wf)
RelWf-extendνρ downR wf .RelWf.leftᵗ-wf X< =
  WfTy-weakenˢ (leftᵗ-wf wf X<) (n≤1+n _)
RelWf-extendνρ downR wf .RelWf.rightᵗ-wf X< =
  WfTy-weakenˢ (rightᵗ-wf wf X<) (n≤1+n _)

varRel : ∀ {Ξ} → RelSub Ξ → TyVar → Rel
varRel {Ξ = []} ρ X = relᵗ ρ X
varRel {Ξ = plain ∷ Ξ} ρ zero = relᵗ ρ zero
varRel {Ξ = plain ∷ Ξ} ρ (suc X) = varRel (tailPlainρ ρ) X
varRel {Ξ = ν-bound ∷ Ξ} ρ zero with νenv-fit ρ
varRel {Ξ = ν-bound ∷ Ξ} ρ zero | fits-ν {e = e} fit =
  sealedRel (αˡ e) (αʳ e) (Rη e)
varRel {Ξ = ν-bound ∷ Ξ} ρ (suc X) = varRel (tailνρ ρ) X

varRel-down : ∀ {Ξ} (ρ : RelSub Ξ) (X : TyVar) → DownClosed (varRel ρ X)
varRel-down {Ξ = []} ρ X = rel-downᵗ ρ X
varRel-down {Ξ = plain ∷ Ξ} ρ zero = rel-downᵗ ρ zero
varRel-down {Ξ = plain ∷ Ξ} ρ (suc X) = varRel-down (tailPlainρ ρ) X
varRel-down {Ξ = ν-bound ∷ Ξ} ρ zero with νenv-fit ρ
varRel-down {Ξ = ν-bound ∷ Ξ} ρ zero | fits-ν {e = e} fit =
  sealedRel-down {αˡ = αˡ e} {αʳ = αʳ e} {R = Rη e} (downη e)
varRel-down {Ξ = ν-bound ∷ Ξ} ρ (suc X) = varRel-down (tailνρ ρ) X

mutual
  𝒱′ :
    ∀ {Ξ Aˡ Aʳ Bˡ Bʳ} →
    RelSub Ξ → ℕ → Dir →
    Ξ ⊢ Aˡ ⊑ᵢ Aʳ →
    Ξ ⊢ Bˡ ⊑ᵢ Bʳ →
    World → Term → Term → Set₁
  𝒱′ ρ zero dir pA pB w V W = Lift (lsuc 0ℓ) ⊤
  𝒱′ ρ (suc k) dir pA pB w V W =
    (∀ {w′} → w′ ⪰ w → ∀ {V′ W′} →
      𝒱 ρ pA (suc k) dir w′ V′ W′ →
      Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
        (Σˡ w′ ∣ (V · V′) —→ Σˡ w′ ∣ Lβ) ×
        (Σʳ w′ ∣ (W · W′) —→ Σʳ w′ ∣ Rβ) ×
        ℰ ρ pB (suc k) dir w′ Lβ Rβ)
    ×
    𝒱′ ρ k dir pA pB w V W

  𝒱body :
    ∀ {Ξ A B} →
    RelSub Ξ → Ξ ⊢ A ⊑ᵢ B → ℕ → Dir → World → Term → Term → Set₁
  𝒱body ρ (⊑ᵢ-‵ `ℕ) n dir w V W = ℕ-payload V W
  𝒱body ρ (⊑ᵢ-‵ `𝔹) n dir w V W = Lift (lsuc 0ℓ) ⊥
  𝒱body ρ (⊑ᵢ-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) n dir w V W =
    𝒱′ ρ n dir pA pB w V W
  𝒱body {Ξ = Ξ} ρ (⊑ᵢ-∀ Aˡ Aʳ p) n dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      (Tˡ Tʳ : Ty) →
      (hTˡ : WfTy 0 (Ψˡ w′) Tˡ) →
      (hTʳ : WfTy 0 (Ψʳ w′) Tʳ) →
      (pT : [] ⊢ Tˡ ⊑ᵢ Tʳ) →
      ℰ (extendPlainρ ρ Tˡ Tʳ
           (Ψˡ w′ , hTˡ)
           (Ψʳ w′ , hTʳ)
           pT R downR)
        p n dir w′
        (V ⦂∀ left∀ᵢ ρ w′ Aˡ [ Tˡ ])
        (W ⦂∀ right∀ᵢ ρ w′ Aʳ [ Tʳ ])
  𝒱body {Ξ = Ξ} ρ (⊑ᵢ-ν A′ B′ p) n dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      (Tˡ Tʳ : Ty) →
      (hTˡ : WfTy 0 (Ψˡ w′) Tˡ) →
      (hTʳ : WfTy 0 (Ψʳ w′) Tʳ) →
      (pT : [] ⊢ Tˡ ⊑ᵢ Tʳ) →
      ℰ (extendνρ ρ
           (ηentry (length (Σˡ w′)) (length (Σʳ w′)) R downR))
        p n dir (extendWorldν w′ R downR Tˡ Tʳ hTˡ hTʳ)
        (V ⦂∀ left∀ᵢ ρ w′ A′ [ ｀ length (Σˡ w′) ])
        W
  𝒱body ρ ⊑ᵢ-★★ zero dir w V W = Lift (lsuc 0ℓ) ⊤
  𝒱body ρ ⊑ᵢ-★★ (suc k) dir w V W = star-rel V W
    where
    star-rel : Term → Term → Set₁
    star-rel (V up tag pˡ G) (W up tag pʳ H) =
      Lift (lsuc 0ℓ) (G ≡ H) ×
      𝒱 ρ (⊑ᵢ-refl {A = G}) k dir w (V up pˡ) (W up pʳ)
    star-rel (V down seal pˡ αˡ) (W down seal pʳ αʳ) =
      Σ[ R ∈ Rel ] (η w ∋η αˡ ↔ αʳ ∶ R) × R k dir (V down pˡ) (W down pʳ)
    star-rel V W = Lift (lsuc 0ℓ) ⊥
  𝒱body ρ (⊑ᵢ-★ _ G g p) zero ≼ w V W = Lift (lsuc 0ℓ) ⊤
  𝒱body ρ (⊑ᵢ-★ _ G g p) zero ≽ w V W = Lift (lsuc 0ℓ) ⊤
  𝒱body ρ (⊑ᵢ-★ _ G g p) (suc k) ≼ w V W = star-right-rel W
    where
    star-right-rel : Term → Set₁
    star-right-rel (W up tag pʳ H) =
      Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 ρ p k ≼ w V (W up pʳ)
    star-right-rel W = Lift (lsuc 0ℓ) ⊥
  𝒱body ρ (⊑ᵢ-★ _ G g p) (suc k) ≽ w V W = star-right-rel W
    where
    star-right-rel : Term → Set₁
    star-right-rel (W up tag pʳ H) =
      Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 ρ p k ≽ w V (W up pʳ)
    star-right-rel W = Lift (lsuc 0ℓ) ⊥
  𝒱body ρ (⊑ᵢ-｀ α) zero dir w V W = seal-rel V W
    where
    seal-rel : Term → Term → Set₁
    seal-rel (V down seal pˡ βˡ) (W down seal pʳ βʳ) =
      Σ[ eqˡ ∈ α ≡ βˡ ] Σ[ eqʳ ∈ α ≡ βʳ ] Σ[ R ∈ Rel ]
        (η w ∋η α ↔ α ∶ R) × R zero dir (V down pˡ) (W down pʳ)
    seal-rel V W = Lift (lsuc 0ℓ) ⊥
  𝒱body ρ (⊑ᵢ-｀ α) (suc k) dir w V W = seal-rel V W
    where
    seal-rel : Term → Term → Set₁
    seal-rel (V down seal pˡ βˡ) (W down seal pʳ βʳ) =
      Σ[ eqˡ ∈ α ≡ βˡ ] Σ[ eqʳ ∈ α ≡ βʳ ] Σ[ R ∈ Rel ]
        (η w ∋η α ↔ α ∶ R) × R (suc k) dir (V down pˡ) (W down pʳ)
    seal-rel V W = Lift (lsuc 0ℓ) ⊥
  𝒱body ρ (⊑ᵢ-＇ X) n dir w V W =
    Lift (lsuc 0ℓ) (varRel ρ X n dir V W)

  ℰbody :
    ∀ {Ξ A B} →
    RelSub Ξ → Ξ ⊢ A ⊑ᵢ B → ℕ → Dir → World → Term → Term → Set₁
  ℰbody ρ p zero dir w Mˡ Mʳ = Lift (lsuc 0ℓ) ⊤
  ℰbody ρ p (suc k) ≼ w Mˡ Mʳ =
    (Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ] Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ]
      Σ[ Mˡ′ ∈ Term ]
      (Σˡ w ∣ Mˡ —→ Σˡ′ ∣ Mˡ′) ×
      Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ] Σ[ Mʳ′ ∈ Term ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Mʳ′) ×
      ℰ ρ p k ≼ (mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′) Mˡ′ Mʳ′)
    ⊎
    (Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ] Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ]
      Σ[ ℓ ∈ Label ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ blame ℓ))
    ⊎
    (Value Mˡ × Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ]
      Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ] Σ[ Wʳ ∈ Term ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Wʳ) ×
      𝒱 ρ p k ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Wʳ)
  ℰbody ρ p (suc k) ≽ w Mˡ Mʳ =
    (Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ] Σ[ wfΣʳ′ ∈ StoreWf 0 Ψʳ′ Σʳ′ ]
      Σ[ Mʳ′ ∈ Term ]
      (Σʳ w ∣ Mʳ —→ Σʳ′ ∣ Mʳ′) ×
      Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ]
      Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ] Σ[ Mˡ′ ∈ Term ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Mˡ′) ×
      ℰ ρ p k ≽ (mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′) Mˡ′ Mʳ′)
    ⊎
    (Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ] Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ]
      Σ[ ℓ ∈ Label ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ blame ℓ))
    ⊎
    (Value Mʳ × Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ]
      Σ[ wfΣˡ′ ∈ StoreWf 0 Ψˡ′ Σˡ′ ] Σ[ Wˡ ∈ Term ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Wˡ) ×
      𝒱 ρ p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ Mʳ)

  𝒱 :
    ∀ {Ξ A B} →
    RelSub Ξ → Ξ ⊢ A ⊑ᵢ B → ℕ → Dir → World → Term → Term → Set₁
  𝒱 {A = A} {B = B} ρ p zero dir w V W =
    Lift (lsuc 0ℓ) (VHeader {A = A} {B = B} ρ w V W)
  𝒱 {A = A} {B = B} ρ p (suc n) dir w V W =
    VHeader {A = A} {B = B} ρ w V W ×
    𝒱body ρ p (suc n) dir w V W

  ℰ :
    ∀ {Ξ A B} →
    RelSub Ξ → Ξ ⊢ A ⊑ᵢ B → ℕ → Dir → World → Term → Term → Set₁
  ℰ {A = A} {B = B} ρ p n dir w Mˡ Mʳ =
    EHeader {A = A} {B = B} ρ w Mˡ Mʳ ×
    ℰbody ρ p n dir w Mˡ Mʳ

η∋-downClosed :
  ∀ {η αˡ αʳ R} →
  η ∋η αˡ ↔ αʳ ∶ R →
  DownClosed R
η∋-downClosed (hereη {dR = dR}) = dR
η∋-downClosed (thereη η∋) = η∋-downClosed η∋

mutual
  ∀-payload-monotone :
    ∀ {Ξ Aˡ Aʳ} {p : (plain ∷ Ξ) ⊢ Aˡ ⊑ᵢ Aʳ}
      (ρ : RelSub Ξ) k dir w V W →
    (∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      (Tˡ Tʳ : Ty) →
      (hTˡ : WfTy 0 (Ψˡ w′) Tˡ) →
      (hTʳ : WfTy 0 (Ψʳ w′) Tʳ) →
      (pT : [] ⊢ Tˡ ⊑ᵢ Tʳ) →
      ℰ (extendPlainρ ρ Tˡ Tʳ
           (Ψˡ w′ , hTˡ)
           (Ψʳ w′ , hTʳ)
           pT R downR)
        p (suc (suc k)) dir w′
        (V ⦂∀ left∀ᵢ ρ w′ Aˡ [ Tˡ ])
        (W ⦂∀ right∀ᵢ ρ w′ Aʳ [ Tʳ ])) →
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      (Tˡ Tʳ : Ty) →
      (hTˡ : WfTy 0 (Ψˡ w′) Tˡ) →
      (hTʳ : WfTy 0 (Ψʳ w′) Tʳ) →
      (pT : [] ⊢ Tˡ ⊑ᵢ Tʳ) →
      ℰ (extendPlainρ ρ Tˡ Tʳ
           (Ψˡ w′ , hTˡ)
           (Ψʳ w′ , hTʳ)
           pT R downR)
        p (suc k) dir w′
        (V ⦂∀ left∀ᵢ ρ w′ Aˡ [ Tˡ ])
        (W ⦂∀ right∀ᵢ ρ w′ Aʳ [ Tʳ ])
  ∀-payload-monotone {Aˡ = Aˡ} {Aʳ = Aʳ} {p = p}
      ρ k dir w V W all-rel
      {w′ = w′} w′⪰ R downR Tˡ Tʳ hTˡ hTʳ pT =
    ℰ-monotone
      (extendPlainρ ρ Tˡ Tʳ
        (Ψˡ w′ , hTˡ) (Ψʳ w′ , hTʳ) pT R downR)
      p (suc k) dir w′
      (V ⦂∀ left∀ᵢ ρ w′ Aˡ [ Tˡ ])
      (W ⦂∀ right∀ᵢ ρ w′ Aʳ [ Tʳ ])
      (all-rel w′⪰ R downR Tˡ Tʳ hTˡ hTʳ pT)

  ν-payload-monotone :
    ∀ {Ξ A′ B′} {p : (ν-bound ∷ Ξ) ⊢ A′ ⊑ᵢ ⇑ᵗ B′}
      (ρ : RelSub Ξ) k dir w V W →
    (∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      (Tˡ Tʳ : Ty) →
      (hTˡ : WfTy 0 (Ψˡ w′) Tˡ) →
      (hTʳ : WfTy 0 (Ψʳ w′) Tʳ) →
      (pT : [] ⊢ Tˡ ⊑ᵢ Tʳ) →
      ℰ (extendνρ ρ
           (ηentry (length (Σˡ w′)) (length (Σʳ w′)) R downR))
        p (suc (suc k)) dir
        (extendWorldν w′ R downR Tˡ Tʳ hTˡ hTʳ)
        (V ⦂∀ left∀ᵢ ρ w′ A′ [ ｀ length (Σˡ w′) ])
        W) →
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      (Tˡ Tʳ : Ty) →
      (hTˡ : WfTy 0 (Ψˡ w′) Tˡ) →
      (hTʳ : WfTy 0 (Ψʳ w′) Tʳ) →
      (pT : [] ⊢ Tˡ ⊑ᵢ Tʳ) →
      ℰ (extendνρ ρ
           (ηentry (length (Σˡ w′)) (length (Σʳ w′)) R downR))
        p (suc k) dir
        (extendWorldν w′ R downR Tˡ Tʳ hTˡ hTʳ)
        (V ⦂∀ left∀ᵢ ρ w′ A′ [ ｀ length (Σˡ w′) ])
        W
  ν-payload-monotone {A′ = A′} {p = p} ρ k dir w V W ν-rel
      {w′ = w′} w′⪰ R downR Tˡ Tʳ hTˡ hTʳ pT =
    ℰ-monotone
      (extendνρ ρ
        (ηentry (length (Σˡ w′)) (length (Σʳ w′)) R downR))
      p (suc k) dir (extendWorldν w′ R downR Tˡ Tʳ hTˡ hTʳ)
      (V ⦂∀ left∀ᵢ ρ w′ A′ [ ｀ length (Σˡ w′) ])
      W
      (ν-rel w′⪰ R downR Tˡ Tʳ hTˡ hTʳ pT)

  𝒱body-monotone :
    ∀ {Ξ A B} (ρ : RelSub Ξ) (p : Ξ ⊢ A ⊑ᵢ B)
      k dir w V W →
    VHeader {A = A} {B = B} ρ w V W →
    𝒱body ρ p (suc (suc k)) dir w V W →
    𝒱body ρ p (suc k) dir w V W
  𝒱body-monotone ρ (⊑ᵢ-‵ `ℕ) k dir w V W header rel = rel
  𝒱body-monotone ρ (⊑ᵢ-‵ `𝔹) k dir w V W header rel = rel
  𝒱body-monotone ρ (⊑ᵢ-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) k dir w V W header rel =
    proj₂ rel
  𝒱body-monotone ρ (⊑ᵢ-∀ Aˡ Aʳ p) k dir w V W header all-rel =
    ∀-payload-monotone ρ k dir w V W all-rel
  𝒱body-monotone ρ (⊑ᵢ-ν A′ B′ p) k dir w V W header ν-rel =
    ν-payload-monotone ρ k dir w V W ν-rel
  𝒱body-monotone ρ ⊑ᵢ-★★ k dir w V W
      (vV , vW , (V⊢ , W⊢)) rel
      with canonical-★ vV V⊢ | canonical-★ vW W⊢
  𝒱body-monotone ρ ⊑ᵢ-★★ k dir w V W
      (vV , vW , (V⊢ , W⊢)) rel
      | sv-up-tag {W = U} {p = pˡ} {G = G} vU eqV
      | sv-up-tag {W = U′} {p = pʳ} {G = H} vU′ eqW
      rewrite eqV | eqW with rel
  𝒱body-monotone ρ ⊑ᵢ-★★ k dir w V W
      (vV , vW , (V⊢ , W⊢)) rel
      | sv-up-tag {W = U} {p = pˡ} {G = G} vU eqV
      | sv-up-tag {W = U′} {p = pʳ} {G = H} vU′ eqW
      | eqG , inner =
    eqG , 𝒱-monotone ρ (⊑ᵢ-refl {A = G}) k dir w (U up pˡ) (U′ up pʳ) inner
  𝒱body-monotone ρ (⊑ᵢ-★ A G g p) k ≼ w V W
      (vV , vW , (V⊢ , W⊢)) rel
      with canonical-★ vW W⊢
  𝒱body-monotone ρ (⊑ᵢ-★ A G g p) k ≼ w V W
      (vV , vW , (V⊢ , W⊢)) rel
      | sv-up-tag {W = W′} {p = pʳ} {G = H} vW′ eqW
      rewrite eqW with rel
  𝒱body-monotone ρ (⊑ᵢ-★ A G g p) k ≼ w V W
      (vV , vW , (V⊢ , W⊢)) rel
      | sv-up-tag {W = W′} {p = pʳ} {G = H} vW′ eqW
      | eqG , inner =
    eqG , 𝒱-monotone ρ p k ≼ w V (W′ up pʳ) inner
  𝒱body-monotone ρ (⊑ᵢ-★ A G g p) k ≽ w V W
      (vV , vW , (V⊢ , W⊢)) rel
      with canonical-★ vW W⊢
  𝒱body-monotone ρ (⊑ᵢ-★ A G g p) k ≽ w V W
      (vV , vW , (V⊢ , W⊢)) rel
      | sv-up-tag {W = W′} {p = pʳ} {G = H} vW′ eqW
      rewrite eqW with rel
  𝒱body-monotone ρ (⊑ᵢ-★ A G g p) k ≽ w V W
      (vV , vW , (V⊢ , W⊢)) rel
      | sv-up-tag {W = W′} {p = pʳ} {G = H} vW′ eqW
      | eqG , inner =
    eqG , 𝒱-monotone ρ p k ≽ w V (W′ up pʳ) inner
  𝒱body-monotone ρ (⊑ᵢ-｀ α) k dir w V W
      (vV , vW , (V⊢ , W⊢)) rel
      with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
  𝒱body-monotone ρ (⊑ᵢ-｀ α) k dir w V W
      (vV , vW , (V⊢ , W⊢)) rel
      | sv-down-seal {W = V′} {p = pˡ} vV′ eqV
      | sv-down-seal {W = W′} {p = pʳ} vW′ eqW
      rewrite eqV | eqW with rel
  𝒱body-monotone ρ (⊑ᵢ-｀ α) k dir w V W
      (vV , vW , (V⊢ , W⊢)) rel
      | sv-down-seal {W = V′} {p = pˡ} vV′ eqV
      | sv-down-seal {W = W′} {p = pʳ} vW′ eqW
      | eqˡ , eqʳ , R , η∋ , Rrel =
    eqˡ , eqʳ , R , η∋ , η∋-downClosed η∋ Rrel
  𝒱body-monotone ρ (⊑ᵢ-＇ X) k dir w V W header (lift rel) =
    lift (varRel-down ρ X rel)

  𝒱-monotone :
    ∀ {Ξ A B} (ρ : RelSub Ξ) (p : Ξ ⊢ A ⊑ᵢ B)
      k dir w V W →
    𝒱 ρ p (suc k) dir w V W →
    𝒱 ρ p k dir w V W
  𝒱-monotone ρ p zero dir w V W (header , body) = lift header
  𝒱-monotone ρ p (suc k) dir w V W (header , body) =
    header , 𝒱body-monotone ρ p k dir w V W header body

  ℰbody-monotone :
    ∀ {Ξ A B} (ρ : RelSub Ξ) (p : Ξ ⊢ A ⊑ᵢ B)
      k dir w Mˡ Mʳ →
    ℰbody ρ p (suc k) dir w Mˡ Mʳ →
    ℰbody ρ p k dir w Mˡ Mʳ
  ℰbody-monotone ρ p zero dir w Mˡ Mʳ rel = lift⊤
  ℰbody-monotone ρ p (suc k) ≼ w Mˡ Mʳ
      (inj₁
        (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , step ,
         Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , steps , rel′)) =
    inj₁
      (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , step ,
       Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , steps ,
       ℰ-monotone ρ p k ≼
         (mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′) Mˡ′ Mʳ′ rel′)
  ℰbody-monotone ρ p (suc k) ≼ w Mˡ Mʳ
      (inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , blame↠))) =
    inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , blame↠))
  ℰbody-monotone ρ p (suc k) ≼ w Mˡ Mʳ
      (inj₂ (inj₂
        (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Wʳ , steps , Vrel))) =
    inj₂ (inj₂ (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Wʳ , steps ,
      𝒱-monotone ρ p k ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Wʳ Vrel))
  ℰbody-monotone ρ p (suc k) ≽ w Mˡ Mʳ
      (inj₁
        (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , step ,
         Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , steps , rel′)) =
    inj₁
      (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , step ,
       Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , steps ,
       ℰ-monotone ρ p k ≽
         (mkWorldˡʳ w Σˡ′ wfΣˡ′ Σʳ′ wfΣʳ′) Mˡ′ Mʳ′ rel′)
  ℰbody-monotone ρ p (suc k) ≽ w Mˡ Mʳ
      (inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , blame↠))) =
    inj₂ (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , ℓ , blame↠))
  ℰbody-monotone ρ p (suc k) ≽ w Mˡ Mʳ
      (inj₂ (inj₂
        (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Wˡ , steps , Vrel))) =
    inj₂ (inj₂ (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Wˡ , steps ,
      𝒱-monotone ρ p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ Mʳ Vrel))

  ℰ-monotone :
    ∀ {Ξ A B} (ρ : RelSub Ξ) (p : Ξ ⊢ A ⊑ᵢ B)
      k dir w Mˡ Mʳ →
    ℰ ρ p (suc k) dir w Mˡ Mʳ →
    ℰ ρ p k dir w Mˡ Mʳ
  ℰ-monotone ρ p zero dir w Mˡ Mʳ ((Mˡ⊢ , Mʳ⊢) , body) =
    (Mˡ⊢ , Mʳ⊢) , lift⊤
  ℰ-monotone ρ p (suc k) dir w Mˡ Mʳ ((Mˡ⊢ , Mʳ⊢) , body) =
    (Mˡ⊢ , Mʳ⊢) ,
    ℰbody-monotone ρ p (suc k) dir w Mˡ Mʳ body

wkΨ-term-+ :
  ∀ {Δ Ψ Σ Γ M A} →
  (k : ℕ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ k + Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
wkΨ-term-+ zero M⊢ = M⊢
wkΨ-term-+ (suc k) M⊢ = wkΨ-term-suc (wkΨ-term-+ k M⊢)

wkΨ-term-≤ :
  ∀ {Δ Ψ Ψ′ Σ Γ M A} →
  Ψ ≤ Ψ′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ′ ∣ Σ ∣ Γ ⊢ M ⦂ A
wkΨ-term-≤ {Δ} {Ψ} {Ψ′} {Σ} {Γ} {M} {A} Ψ≤Ψ′ M⊢ =
  subst
    (λ q → Δ ∣ q ∣ Σ ∣ Γ ⊢ M ⦂ A)
    (trans (+-comm (Ψ′ ∸ Ψ) Ψ) (m+[n∸m]≡n Ψ≤Ψ′))
    (wkΨ-term-+ (Ψ′ ∸ Ψ) M⊢)

wk⪰ˡ :
  ∀ {w w′ A V} →
  w′ ⪰ w →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ A →
  0 ∣ Ψˡ w′ ∣ Σˡ w′ ∣ [] ⊢ V ⦂ A
wk⪰ˡ w′⪰ V⊢ =
  wkΣ-term (_⪰_.growˡ w′⪰) (wkΨ-term-≤ (_⪰_.growΨˡ w′⪰) V⊢)

wk⪰ʳ :
  ∀ {w w′ A V} →
  w′ ⪰ w →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ V ⦂ A →
  0 ∣ Ψʳ w′ ∣ Σʳ w′ ∣ [] ⊢ V ⦂ A
wk⪰ʳ w′⪰ V⊢ =
  wkΣ-term (_⪰_.growʳ w′⪰) (wkΨ-term-≤ (_⪰_.growΨʳ w′⪰) V⊢)

𝒱⇒′-⪰ :
  ∀ {Ξ Aˡ Aʳ Bˡ Bʳ k dir w w′ V W}
    {ρ : RelSub Ξ}
    {pA : Ξ ⊢ Aˡ ⊑ᵢ Aʳ}
    {pB : Ξ ⊢ Bˡ ⊑ᵢ Bʳ} →
  w′ ⪰ w →
  𝒱′ ρ k dir pA pB w V W →
  𝒱′ ρ k dir pA pB w′ V W
𝒱⇒′-⪰ {k = zero} w′⪰ rel = lift tt
𝒱⇒′-⪰
    {k = suc k} {dir = dir} {w′ = w′} {V = V} {W = W} {ρ = ρ}
    {pA = pA} {pB = pB} w′⪰ (step , rest) =
  step′ , 𝒱⇒′-⪰ {k = k} w′⪰ rest
  where
  step′ :
    ∀ {w″} →
    w″ ⪰ w′ →
    ∀ {V′ W′} →
    𝒱 ρ pA (suc k) dir w″ V′ W′ →
    Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
      (Σˡ w″ ∣ (V · V′) —→ Σˡ w″ ∣ Lβ) ×
      (Σʳ w″ ∣ (W · W′) —→ Σʳ w″ ∣ Rβ) ×
      ℰ ρ pB (suc k) dir w″ Lβ Rβ
  step′ w″⪰ rel = step (⪰-trans w″⪰ w′⪰) rel

𝒱⇒-⪰ :
  ∀ {Ξ Aˡ Aʳ Bˡ Bʳ n dir w w′ V W}
    (ρ : RelSub Ξ)
    {pA : Ξ ⊢ Aˡ ⊑ᵢ Aʳ}
    {pB : Ξ ⊢ Bˡ ⊑ᵢ Bʳ} →
  w′ ⪰ w →
  𝒱 ρ (⊑ᵢ-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) n dir w V W →
  𝒱 ρ (⊑ᵢ-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) n dir w′ V W
𝒱⇒-⪰ {n = zero} ρ w′⪰
    (lift (vV , vW , (V⊢ , W⊢))) =
  lift (vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢))
𝒱⇒-⪰ {n = suc n} ρ w′⪰
    ((vV , vW , (V⊢ , W⊢)) , fun-rel) =
  (vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢)) ,
  𝒱⇒′-⪰ {k = suc n} w′⪰ fun-rel

𝒱-lower :
  ∀ {Ξ n j A B} (j<n : j <′ n) {ρ : RelSub Ξ}
    {p : Ξ ⊢ A ⊑ᵢ B} {dir w V W} →
  𝒱 ρ p n dir w V W →
  𝒱 ρ p j dir w V W
𝒱-lower {n = zero} (≤′-reflexive ()) rel
𝒱-lower {n = suc n} {A = A} {B = B} <′-base
    {ρ = ρ} {p = p} {dir = dir} {w = w} {V = V} {W = W} rel =
  𝒱-monotone ρ p n dir w V W rel
𝒱-lower {n = suc n} (≤′-step j<n)
    {ρ = ρ} {p = p} {dir = dir} {w = w} {V = V} {W = W} rel =
  𝒱-lower j<n {ρ = ρ} {p = p} {dir = dir} {w = w} {V = V} {W = W}
    (𝒱-monotone ρ p n dir w V W rel)

ℰ-lower :
  ∀ {Ξ n j A B} (j<n : j <′ n) {ρ : RelSub Ξ}
    {p : Ξ ⊢ A ⊑ᵢ B} {dir w Mˡ Mʳ} →
  ℰ ρ p n dir w Mˡ Mʳ →
  ℰ ρ p j dir w Mˡ Mʳ
ℰ-lower {n = zero} (≤′-reflexive ()) rel
ℰ-lower {n = suc n} {A = A} {B = B} <′-base
    {ρ = ρ} {p = p} {dir = dir} {w = w} {Mˡ = Mˡ} {Mʳ = Mʳ} rel =
  ℰ-monotone ρ p n dir w Mˡ Mʳ rel
ℰ-lower {n = suc n} (≤′-step j<n)
    {ρ = ρ} {p = p} {dir = dir} {w = w} {Mˡ = Mˡ} {Mʳ = Mʳ} rel =
  ℰ-lower j<n {ρ = ρ} {p = p} {dir = dir} {w = w}
    {Mˡ = Mˡ} {Mʳ = Mʳ}
    (ℰ-monotone ρ p n dir w Mˡ Mʳ rel)
