module LogicalRelation where

-- File Charter:
--   * Alternative step-indexed logical relation for `PolyUpDown`.
--   * Uses direct recursion on indices (no well-founded recursion machinery).
--   * Uses a `V′`-style helper for function types.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat
  using (ℕ; zero; suc; z<s; z≤n; s<s; s≤s; _+_; _∸_; _<_; _<′_; _≤_;
         <′-base; ≤′-step; ≤′-reflexive)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; n≤1+n; m≤n⇒m≤1+n; m+[n∸m]≡n; +-comm;
         <-≤-trans)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; 0ℓ; lift) renaming (suc to lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no)

open import Types
open import Store
  using (_⊆ˢ_; ⊆ˢ-refl; ⊆ˢ-trans; done; keep; drop;
         StoreWf; substStoreᵗ; Uniqueˢ; uniq∷_;
         LookupStoreAny; storeWf-unique; storeWf-wfTy; storeWf-dom<;
         storeWf-dom∋; storeWf-length)
open import Imprecision
open import TypeProperties
  using (liftSubstˢ; substᵗ-ν-src; substᵗ-⇑ˢ; substᵗ-id; renameᵗ-substᵗ;
         substᵗ-renameᵗ; substᵗ-cong;
         substᵗ-ground; renameᵗ-preserves-WfTy; renameˢ-preserves-WfTy;
         TyRenameWf-suc; SealRenameWf-suc; TySubstWf)
open import UpDown
open import Terms
open import TermPrecision using (PCtx; TPEnv; extendᴾ; ⇑ᵗᴾ; renameᵗ-⊑; ν-inst-⊑)
open import TermProperties using (Substˣ; substˣ-term; ↑ᵗᵐ)
open import ReductionFresh using (Value; _∣_—→_∣_; _∣_—↠_∣_; _—→⟨_⟩_)
open import ProgressFresh using (canonical-★; sv-up-tag; canonical-｀; sv-down-seal)
open import PreservationFresh using (wkΨ-term-suc; len<suc-StoreWf; length∉dom-StoreWf)

------------------------------------------------------------------------
-- Direction, world, and precision index
------------------------------------------------------------------------

data Dir : Set where
  ≼ : Dir
  ≽ : Dir

Rel : Set₁
Rel = ℕ → Dir → Term → Term → Set

DownClosed : Rel → Set
DownClosed R = ∀ {k dir V W} → R (suc k) dir V W → R k dir V W

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
⊆η-trans (η-keep η₁₂) (η-keep η₂₃) = η-keep (⊆η-trans η₁₂ η₂₃)
⊆η-trans (η-keep η₁₂) (η-drop η₂₃) =
  η-drop (⊆η-trans (η-keep η₁₂) η₂₃)
⊆η-trans (η-drop η₁₂) (η-keep η₂₃) = η-drop (⊆η-trans η₁₂ η₂₃)
⊆η-trans (η-drop η₁₂) (η-drop η₂₃) =
  η-drop (⊆η-trans (η-drop η₁₂) η₂₃)

η∋-weaken :
  ∀ {η η′ αˡ αʳ R} →
  η ⊆η η′ →
  η ∋η αˡ ↔ αʳ ∶ R →
  η′ ∋η αˡ ↔ αʳ ∶ R
η∋-weaken η-done ()
η∋-weaken (η-keep η⊆) hereη = hereη
η∋-weaken (η-keep η⊆) (thereη η∋) = thereη (η∋-weaken η⊆ η∋)
η∋-weaken (η-drop η⊆) η∋ = thereη (η∋-weaken η⊆ η∋)

record World : Set₁ where
  constructor mkWorld
  field
    Δ : TyCtx
    Ψˡ : SealCtx
    Ψʳ : SealCtx
    Σˡ : Store
    Σʳ : Store
    wfΣˡ : StoreWf Δ Ψˡ Σˡ
    wfΣʳ : StoreWf Δ Ψʳ Σʳ
    η : List SealRel
open World public

record _⪰_ (w′ w : World) : Set₁ where
  field
    growΔ : Δ w′ ≡ Δ w
    growΨˡ : Ψˡ w ≤ Ψˡ w′
    growΨʳ : Ψʳ w ≤ Ψʳ w′
    growˡ : Σˡ w ⊆ˢ Σˡ w′
    growʳ : Σʳ w ⊆ˢ Σʳ w′
    growη : η w ⊆η η w′

⪰-refl : ∀ {w} → w ⪰ w
⪰-refl ._⪰_.growΔ = refl
⪰-refl ._⪰_.growΨˡ = ≤-refl
⪰-refl ._⪰_.growΨʳ = ≤-refl
⪰-refl ._⪰_.growˡ = ⊆ˢ-refl
⪰-refl ._⪰_.growʳ = ⊆ˢ-refl
⪰-refl ._⪰_.growη = ⊆η-refl

⪰-trans : ∀ {w₁ w₂ w₃} → w₃ ⪰ w₂ → w₂ ⪰ w₁ → w₃ ⪰ w₁
⪰-trans w₃⪰w₂ w₂⪰w₁ ._⪰_.growΔ =
  trans (_⪰_.growΔ w₃⪰w₂) (_⪰_.growΔ w₂⪰w₁)
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

extendWorld : World → (R : Rel) → DownClosed R → World
extendWorld w R downR =
  mkWorld (Δ w) (Ψˡ w) (Ψʳ w) (Σˡ w) (Σʳ w) (wfΣˡ w) (wfΣʳ w)
    (ηentry (length (Σˡ w)) (length (Σʳ w)) R downR ∷ η w)

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
  ∀ {Δ Ψ Σ} {T : Ty} →
  WfTy Δ Ψ T →
  StoreWf Δ Ψ Σ →
  StoreWf Δ (suc Ψ) ((length Σ , T) ∷ Σ)
storeWf-fresh-extᴿ {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {T = T} wfT wfΣ =
  record
    { unique = uniq∷_ (length∉dom-StoreWf wfΣ) (storeWf-unique wfΣ)
    ; wfTy = wf
    ; dom< = domBound
    ; dom∋ = domAny
    ; len = cong suc (storeWf-length wfΣ)
    }
  where
  wf : ∀ {α A} → ((length Σ , T) ∷ Σ) ∋ˢ α ⦂ A → WfTy Δ (suc Ψ) A
  wf (Z∋ˢ α≡β A≡B) =
    subst (WfTy Δ (suc Ψ)) (sym A≡B) (WfTy-weakenˢ wfT (n≤1+n _))
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
  mkWorld (Δ w) (suc (Ψˡ w)) (suc (Ψʳ w))
    ((length (Σˡ w) , Tˡ) ∷ Σˡ w)
    ((length (Σʳ w) , Tʳ) ∷ Σʳ w)
    (storeWf-fresh-extᴿ (WfTy-weakenᵗ hTˡ z≤n) (wfΣˡ w))
    (storeWf-fresh-extᴿ (WfTy-weakenᵗ hTʳ z≤n) (wfΣʳ w))
    (ηentry (length (Σˡ w)) (length (Σʳ w)) R downR ∷ η w)

mkWorldˡ :
  (w : World) →
  (Σˡ′ : Store) →
  ∀ {Ψˡ′} →
  StoreWf (Δ w) Ψˡ′ Σˡ′ →
  World
mkWorldˡ w Σˡ′ wfΣˡ′ =
  mkWorld (Δ w) _ (Ψʳ w) Σˡ′ (Σʳ w) wfΣˡ′ (wfΣʳ w) (η w)

mkWorldʳ :
  (w : World) →
  (Σʳ′ : Store) →
  ∀ {Ψʳ′} →
  StoreWf (Δ w) Ψʳ′ Σʳ′ →
  World
mkWorldʳ w Σʳ′ wfΣʳ′ =
  mkWorld (Δ w) (Ψˡ w) _ (Σˡ w) Σʳ′ (wfΣˡ w) wfΣʳ′ (η w)

mkWorldˡ-⪰ :
  ∀ {w Σˡ′ Ψˡ′} {wfΣˡ′ : StoreWf (Δ w) Ψˡ′ Σˡ′} →
  Σˡ w ⊆ˢ Σˡ′ →
  mkWorldˡ w Σˡ′ wfΣˡ′ ⪰ w
mkWorldˡ-⪰ grow ._⪰_.growΔ = refl
mkWorldˡ-⪰ {w = w} {wfΣˡ′ = wfΣˡ′} grow ._⪰_.growΨˡ
  rewrite sym (StoreWf.len (wfΣˡ w)) | sym (StoreWf.len wfΣˡ′) =
  ⊆ˢ-length≤ grow
mkWorldˡ-⪰ grow ._⪰_.growΨʳ = ≤-refl
mkWorldˡ-⪰ grow ._⪰_.growˡ = grow
mkWorldˡ-⪰ grow ._⪰_.growʳ = ⊆ˢ-refl
mkWorldˡ-⪰ grow ._⪰_.growη = ⊆η-refl

mkWorldʳ-⪰ :
  ∀ {w Σʳ′ Ψʳ′} {wfΣʳ′ : StoreWf (Δ w) Ψʳ′ Σʳ′} →
  Σʳ w ⊆ˢ Σʳ′ →
  mkWorldʳ w Σʳ′ wfΣʳ′ ⪰ w
mkWorldʳ-⪰ grow ._⪰_.growΔ = refl
mkWorldʳ-⪰ grow ._⪰_.growΨˡ = ≤-refl
mkWorldʳ-⪰ {w = w} {wfΣʳ′ = wfΣʳ′} grow ._⪰_.growΨʳ
  rewrite sym (StoreWf.len (wfΣʳ w)) | sym (StoreWf.len wfΣʳ′) =
  ⊆ˢ-length≤ grow
mkWorldʳ-⪰ grow ._⪰_.growˡ = ⊆ˢ-refl
mkWorldʳ-⪰ grow ._⪰_.growʳ = grow
mkWorldʳ-⪰ grow ._⪰_.growη = ⊆η-refl

extendWorld-⪰ : ∀ {w} (R : Rel) (downR : DownClosed R) → extendWorld w R downR ⪰ w
extendWorld-⪰ {w} R downR ._⪰_.growΔ = refl
extendWorld-⪰ {w} R downR ._⪰_.growΨˡ = ≤-refl
extendWorld-⪰ {w} R downR ._⪰_.growΨʳ = ≤-refl
extendWorld-⪰ {w} R downR ._⪰_.growˡ = ⊆ˢ-refl
extendWorld-⪰ {w} R downR ._⪰_.growʳ = ⊆ˢ-refl
extendWorld-⪰ {w} R downR ._⪰_.growη = η-drop ⊆η-refl

extendWorldν-⪰ :
  ∀ {w} (R : Rel) (downR : DownClosed R) Tˡ Tʳ hTˡ hTʳ →
  extendWorldν w R downR Tˡ Tʳ hTˡ hTʳ ⪰ w
extendWorldν-⪰ {w} R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growΔ = refl
extendWorldν-⪰ {w} R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growΨˡ = n≤1+n _
extendWorldν-⪰ {w} R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growΨʳ = n≤1+n _
extendWorldν-⪰ {w} R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growˡ =
  drop ⊆ˢ-refl
extendWorldν-⪰ {w} R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growʳ =
  drop ⊆ˢ-refl
extendWorldν-⪰ {w} R downR Tˡ Tʳ hTˡ hTʳ ._⪰_.growη =
  η-drop ⊆η-refl

η∋-downClosed : ∀ {η αˡ αʳ R} → η ∋η αˡ ↔ αʳ ∶ R → DownClosed R
η∋-downClosed {η = ηentry _ _ _ dR ∷ η} hereη {k} {dir} {V} {W} =
  dR {k} {dir} {V} {W}
η∋-downClosed (thereη η∋) {k} {dir} {V} {W} =
  η∋-downClosed η∋ {k} {dir} {V} {W}

ℕ-payload : Term → Term → Set₁
ℕ-payload ($ (κℕ m)) ($ (κℕ m′)) = Lift (lsuc 0ℓ) (m ≡ m′)
ℕ-payload V W = Lift (lsuc 0ℓ) ⊥

lift⊤ : Lift (lsuc 0ℓ) ⊤
lift⊤ = lift tt

WfTyClosedᵗ : TyCtx → Ty → Set
WfTyClosedᵗ Δ A = Σ[ Ψ ∈ SealCtx ] WfTy Δ Ψ A

record RelSub (Δ : TyCtx) : Set₁ where
  field
    leftᵗ : Substᵗ
    rightᵗ : Substᵗ
    left-closed : (X : TyVar) → WfTyClosedᵗ Δ (leftᵗ X)
    right-closed : (X : TyVar) → WfTyClosedᵗ Δ (rightᵗ X)
    precᵗ : (X : TyVar) → leftᵗ X ⊑ rightᵗ X
    relᵗ : (X : TyVar) → Rel
    rel-downᵗ : (X : TyVar) → DownClosed (relᵗ X)
open RelSub public

record WkRel (ξ : Renameᵗ) {Δ : TyCtx} (ρ ρ′ : RelSub Δ) : Set₁ where
  field
    wk-left-var : (X : TyVar) → leftᵗ ρ X ≡ leftᵗ ρ′ (ξ X)
    wk-right-var : (X : TyVar) → rightᵗ ρ X ≡ rightᵗ ρ′ (ξ X)
    wk-prec-var :
      (X : TyVar) →
      cast-⊑
        (wk-left-var X)
        (wk-right-var X)
        (precᵗ ρ X)
        ≡
      precᵗ ρ′ (ξ X)
    wk-rel⇒ :
      (X : TyVar) →
      ∀ {k dir V W} →
      relᵗ ρ X k dir V W →
      relᵗ ρ′ (ξ X) k dir V W
    wk-rel⇐ :
      (X : TyVar) →
      ∀ {k dir V W} →
      relᵗ ρ′ (ξ X) k dir V W →
      relᵗ ρ X k dir V W
open WkRel public

wk-left-subst :
  ∀ {ξ Δ} {ρ ρ′ : RelSub Δ} →
  WkRel ξ ρ ρ′ →
  (A : Ty) →
  substᵗ (leftᵗ ρ′) (renameᵗ ξ A) ≡ substᵗ (leftᵗ ρ) A
wk-left-subst {ξ = ξ} {ρ = ρ} {ρ′ = ρ′} wk A =
  trans
    (substᵗ-renameᵗ ξ (leftᵗ ρ′) A)
    (substᵗ-cong (λ X → sym (wk-left-var wk X)) A)

wk-right-subst :
  ∀ {ξ Δ} {ρ ρ′ : RelSub Δ} →
  WkRel ξ ρ ρ′ →
  (A : Ty) →
  substᵗ (rightᵗ ρ′) (renameᵗ ξ A) ≡ substᵗ (rightᵗ ρ) A
wk-right-subst {ξ = ξ} {ρ = ρ} {ρ′ = ρ′} wk A =
  trans
    (substᵗ-renameᵗ ξ (rightᵗ ρ′) A)
    (substᵗ-cong (λ X → sym (wk-right-var wk X)) A)

wk-left-subst-var :
  ∀ {ξ Δ} {ρ ρ′ : RelSub Δ} →
  (wk : WkRel ξ ρ ρ′) →
  (X : TyVar) →
  sym (wk-left-subst wk (＇ X)) ≡ wk-left-var wk X
wk-left-subst-var wk X rewrite wk-left-var wk X = refl

wk-right-subst-var :
  ∀ {ξ Δ} {ρ ρ′ : RelSub Δ} →
  (wk : WkRel ξ ρ ρ′) →
  (X : TyVar) →
  sym (wk-right-subst wk (＇ X)) ≡ wk-right-var wk X
wk-right-subst-var wk X rewrite wk-right-var wk X = refl

∅ρ : RelSub 0
(∅ρ .leftᵗ) = λ _ → ‵ `ℕ
(∅ρ .rightᵗ) = λ _ → ‵ `ℕ
(∅ρ .left-closed) = λ _ → 0 , wfBase
(∅ρ .right-closed) = λ _ → 0 , wfBase
(∅ρ .precᵗ) = λ _ → ⊑-‵ `ℕ
(∅ρ .relᵗ) = λ _ k dir V W → ⊥
(∅ρ .rel-downᵗ) = λ _ {k} {dir} {V} {W} ()

extendρ :
  ∀ {Δ} →
  RelSub Δ →
  (A B : Ty) →
  WfTyClosedᵗ Δ A →
  WfTyClosedᵗ Δ B →
  A ⊑ B →
  (R : Rel) →
  DownClosed R →
  RelSub Δ
(extendρ ρ A B wfA wfB p R downR .leftᵗ) zero = A
(extendρ ρ A B wfA wfB p R downR .leftᵗ) (suc X) = leftᵗ ρ X
(extendρ ρ A B wfA wfB p R downR .rightᵗ) zero = B
(extendρ ρ A B wfA wfB p R downR .rightᵗ) (suc X) = rightᵗ ρ X
(extendρ ρ A B wfA wfB p R downR .left-closed) zero = wfA
(extendρ ρ A B wfA wfB p R downR .left-closed) (suc X) =
  left-closed ρ X
(extendρ ρ A B wfA wfB p R downR .right-closed) zero = wfB
(extendρ ρ A B wfA wfB p R downR .right-closed) (suc X) =
  right-closed ρ X
(extendρ ρ A B wfA wfB p R downR .precᵗ) zero = p
(extendρ ρ A B wfA wfB p R downR .precᵗ) (suc X) = precᵗ ρ X
(extendρ ρ A B wfA wfB p R downR .relᵗ) zero = R
(extendρ ρ A B wfA wfB p R downR .relᵗ) (suc X) = relᵗ ρ X
(extendρ ρ A B wfA wfB p R downR .rel-downᵗ)
  zero {k} {dir} {V} {W} = downR {k} {dir} {V} {W}
(extendρ ρ A B wfA wfB p R downR .rel-downᵗ) (suc X) =
  rel-downᵗ ρ X

shift-substᵗ : (A : Ty) → substᵗ (λ X → ＇ suc X) A ≡ renameᵗ suc A
shift-substᵗ A = trans (sym (renameᵗ-substᵗ suc (λ X → ＇ X) A))
                        (cong (renameᵗ suc) (substᵗ-id A))

⇑ᵗρ : ∀ {Δ} → RelSub Δ → RelSub (suc Δ)
(⇑ᵗρ ρ .leftᵗ) = extsᵗ (leftᵗ ρ)
(⇑ᵗρ ρ .rightᵗ) = extsᵗ (rightᵗ ρ)
(⇑ᵗρ ρ .left-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .left-closed) (suc X) =
  let Ψ , wfA = left-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .right-closed) zero = 0 , wfVar z<s
(⇑ᵗρ ρ .right-closed) (suc X) =
  let Ψ , wfA = right-closed ρ X in Ψ , renameᵗ-preserves-WfTy wfA TyRenameWf-suc
(⇑ᵗρ ρ .precᵗ) zero = ⊑-＇ zero
(⇑ᵗρ ρ .precᵗ) (suc X) =
  cast-⊑ (shift-substᵗ (leftᵗ ρ X))
          (shift-substᵗ (rightᵗ ρ X))
          (Imprecision.substᵗ-⊑ (λ Y → ＇ suc Y) (precᵗ ρ X))
(⇑ᵗρ ρ .relᵗ) zero = λ k dir V W → ⊥
(⇑ᵗρ ρ .relᵗ) (suc X) = relᵗ ρ X
(⇑ᵗρ ρ .rel-downᵗ) zero {k} {dir} {V} {W} ()
(⇑ᵗρ ρ .rel-downᵗ) (suc X) = rel-downᵗ ρ X

WkRel-refl : ∀ {Δ} (ρ : RelSub Δ) → WkRel (λ X → X) ρ ρ
WkRel-refl ρ .WkRel.wk-left-var X = refl
WkRel-refl ρ .WkRel.wk-right-var X = refl
WkRel-refl ρ .WkRel.wk-prec-var X = refl
WkRel-refl ρ .WkRel.wk-rel⇒ X rel = rel
WkRel-refl ρ .WkRel.wk-rel⇐ X rel = rel

WkRel-suc :
  ∀ {Δ} {ρ : RelSub Δ} {A B}
    {wfA : WfTyClosedᵗ Δ A} {wfB : WfTyClosedᵗ Δ B}
    {p : A ⊑ B} {R : Rel} {downR : DownClosed R} →
  WkRel suc ρ (extendρ ρ A B wfA wfB p R downR)
WkRel-suc .WkRel.wk-left-var X = refl
WkRel-suc .WkRel.wk-right-var X = refl
WkRel-suc .WkRel.wk-prec-var X = refl
WkRel-suc .WkRel.wk-rel⇒ X rel = rel
WkRel-suc .WkRel.wk-rel⇐ X rel = rel

wk-shiftᵗ-prec :
  ∀ {A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  ∀ {p : A ⊑ B} {p′ : A′ ⊑ B′} →
  cast-⊑ eqA eqB p ≡ p′ →
  cast-⊑
    (cong (renameᵗ suc) eqA)
    (cong (renameᵗ suc) eqB)
    (cast-⊑
      (shift-substᵗ A)
      (shift-substᵗ B)
      (Imprecision.substᵗ-⊑ (λ Y → ＇ suc Y) p))
    ≡
  cast-⊑
    (shift-substᵗ A′)
    (shift-substᵗ B′)
    (Imprecision.substᵗ-⊑ (λ Y → ＇ suc Y) p′)
wk-shiftᵗ-prec refl refl refl = refl

wk-shiftˢ-prec :
  ∀ {A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  ∀ {p : A ⊑ B} {p′ : A′ ⊑ B′} →
  cast-⊑ eqA eqB p ≡ p′ →
  cast-⊑
    (cong ⇑ˢ eqA)
    (cong ⇑ˢ eqB)
    (renameˢ-⊑ suc p)
    ≡
  renameˢ-⊑ suc p′
wk-shiftˢ-prec refl refl refl = refl

WkRel-extᵗ :
  ∀ {ξ Δ} {ρ ρ′ : RelSub Δ} →
  WkRel ξ ρ ρ′ →
  WkRel (extᵗ ξ) (⇑ᵗρ ρ) (⇑ᵗρ ρ′)
WkRel-extᵗ wk .WkRel.wk-left-var zero = refl
WkRel-extᵗ wk .WkRel.wk-left-var (suc X) =
  cong (renameᵗ suc) (wk-left-var wk X)
WkRel-extᵗ wk .WkRel.wk-right-var zero = refl
WkRel-extᵗ wk .WkRel.wk-right-var (suc X) =
  cong (renameᵗ suc) (wk-right-var wk X)
WkRel-extᵗ wk .WkRel.wk-prec-var zero = refl
WkRel-extᵗ wk .WkRel.wk-prec-var (suc X) =
  wk-shiftᵗ-prec
    (wk-left-var wk X)
    (wk-right-var wk X)
    (wk-prec-var wk X)
WkRel-extᵗ wk .WkRel.wk-rel⇒ zero rel = rel
WkRel-extᵗ wk .WkRel.wk-rel⇒ (suc X) rel = wk-rel⇒ wk X rel
WkRel-extᵗ wk .WkRel.wk-rel⇐ zero rel = rel
WkRel-extᵗ wk .WkRel.wk-rel⇐ (suc X) rel = wk-rel⇐ wk X rel

⇑ˢρ : ∀ {Δ} → RelSub Δ → RelSub Δ
(⇑ˢρ ρ .leftᵗ) = liftSubstˢ (leftᵗ ρ)
(⇑ˢρ ρ .rightᵗ) = liftSubstˢ (rightᵗ ρ)
(⇑ˢρ ρ .left-closed) X =
  let Ψ , wfA = left-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .right-closed) X =
  let Ψ , wfA = right-closed ρ X in suc Ψ , renameˢ-preserves-WfTy wfA SealRenameWf-suc
(⇑ˢρ ρ .precᵗ) X = renameˢ-⊑ suc (precᵗ ρ X)
(⇑ˢρ ρ .relᵗ) X = relᵗ ρ X
(⇑ˢρ ρ .rel-downᵗ) X = rel-downᵗ ρ X

WkRel-liftˢ :
  ∀ {ξ Δ} {ρ ρ′ : RelSub Δ} →
  WkRel ξ ρ ρ′ →
  WkRel ξ (⇑ˢρ ρ) (⇑ˢρ ρ′)
WkRel-liftˢ wk .WkRel.wk-left-var X =
  cong ⇑ˢ (wk-left-var wk X)
WkRel-liftˢ wk .WkRel.wk-right-var X =
  cong ⇑ˢ (wk-right-var wk X)
WkRel-liftˢ wk .WkRel.wk-prec-var X =
  wk-shiftˢ-prec
    (wk-left-var wk X)
    (wk-right-var wk X)
    (wk-prec-var wk X)
WkRel-liftˢ wk .WkRel.wk-rel⇒ X rel = wk-rel⇒ wk X rel
WkRel-liftˢ wk .WkRel.wk-rel⇐ X rel = wk-rel⇐ wk X rel

substᴿ-⊑ :
  ∀ {Δ} →
  (ρ : RelSub Δ) →
  ∀ {A B} →
  A ⊑ B →
  substᵗ (leftᵗ ρ) A ⊑ substᵗ (rightᵗ ρ) B
substᴿ-⊑ ρ ⊑-★★ = ⊑-★★
substᴿ-⊑ ρ (⊑-★ A G g p) =
  ⊑-★
    (substᵗ (leftᵗ ρ) A)
    (substᵗ (rightᵗ ρ) G)
    (substᵗ-ground (rightᵗ ρ) g)
    (substᴿ-⊑ ρ p)
substᴿ-⊑ ρ (⊑-＇ X) = precᵗ ρ X
substᴿ-⊑ ρ (⊑-｀ αˡ αʳ) = ⊑-｀ αˡ αʳ
substᴿ-⊑ ρ (⊑-‵ ι) = ⊑-‵ ι
substᴿ-⊑ ρ (⊑-⇒ A A′ B B′ p q) =
  ⊑-⇒
    (substᵗ (leftᵗ ρ) A)
    (substᵗ (rightᵗ ρ) A′)
    (substᵗ (leftᵗ ρ) B)
    (substᵗ (rightᵗ ρ) B′)
    (substᴿ-⊑ ρ p)
    (substᴿ-⊑ ρ q)
substᴿ-⊑ ρ (⊑-∀ A B p) =
  ⊑-∀
    (substᵗ (extsᵗ (leftᵗ ρ)) A)
    (substᵗ (extsᵗ (rightᵗ ρ)) B)
    (substᴿ-⊑ (⇑ᵗρ ρ) p)
substᴿ-⊑ ρ (⊑-ν A B p) =
  ⊑-ν
    (substᵗ (extsᵗ (leftᵗ ρ)) A)
    (substᵗ (rightᵗ ρ) B)
    (cast-⊑ (substᵗ-ν-src (leftᵗ ρ) A)
             (substᵗ-⇑ˢ (rightᵗ ρ) B)
             (substᴿ-⊑ (⇑ˢρ ρ) p))

mutual
  𝒱′ :
    ∀ {Δ Aˡ Aʳ Bˡ Bʳ} →
    RelSub Δ → ℕ → Dir → Aˡ ⊑ Aʳ → Bˡ ⊑ Bʳ →
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
    ∀ {Δ A B} →
    RelSub Δ → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  𝒱body ρ (⊑-‵ `ℕ) n dir w V W = ℕ-payload V W
  𝒱body ρ (⊑-‵ `𝔹) n dir w V W = Lift (lsuc 0ℓ) ⊥
  𝒱body {A = Aˡ ⇒ Bˡ} {B = Aʳ ⇒ Bʳ}
      ρ (⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) n dir w V W =
    𝒱′ ρ n dir pA pB w V W
  𝒱body ρ (⊑-∀ Aˡ Aʳ p) n dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      (Tˡ Tʳ : Ty) →
      (hTˡ : WfTy 0 (Ψˡ w′) Tˡ) →
      (hTʳ : WfTy 0 (Ψʳ w′) Tʳ) →
      (pT : Tˡ ⊑ Tʳ) →
      ℰ (extendρ ρ Tˡ Tʳ
           (Ψˡ w′ , WfTy-weakenᵗ hTˡ z≤n)
           (Ψʳ w′ , WfTy-weakenᵗ hTʳ z≤n)
           pT R downR)
        p n dir (extendWorld w′ R downR)
        (V ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) Aˡ [ Tˡ ])
        (W ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) Aʳ [ Tʳ ])
  𝒱body ρ (⊑-ν A′ B′ p) n dir w V W =
    ∀ {w′} → w′ ⪰ w → (R : Rel) → (downR : DownClosed R) →
      (Tˡ Tʳ : Ty) →
      (hTˡ : WfTy 0 (Ψˡ w′) Tˡ) →
      (hTʳ : WfTy 0 (Ψʳ w′) Tʳ) →
      (pT : Tˡ ⊑ Tʳ) →
      ℰ (⇑ˢρ ρ) p n dir (extendWorldν w′ R downR Tˡ Tʳ hTˡ hTʳ)
        (V ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) A′ [ ｀ length (Σˡ w′) ]) W

  𝒱body ρ ⊑-★★ zero dir w V W = Lift (lsuc 0ℓ) ⊤
  𝒱body ρ ⊑-★★ (suc k) dir w V W = star-rel V W
    where
    star-rel : Term → Term → Set₁
    star-rel (V up tag G) (W up tag H) =
      Lift (lsuc 0ℓ) (G ≡ H) ×
      𝒱 ρ (⊑-refl {A = G}) k dir w V W
    star-rel (V down seal αˡ) (W down seal αʳ) =
      Σ[ R ∈ Rel ] (η w ∋η αˡ ↔ αʳ ∶ R) × R k dir V W
    star-rel V W = Lift (lsuc 0ℓ) ⊥

  𝒱body ρ (⊑-★ _ G g p) zero ≼ w V W = Lift (lsuc 0ℓ) ⊤
  𝒱body ρ (⊑-★ _ G g p) zero ≽ w V W = Lift (lsuc 0ℓ) ⊤
  𝒱body ρ (⊑-★ _ G g p) (suc k) ≼ w V W = star-right-rel W
    where
    star-right-rel : Term → Set₁
    star-right-rel (W up tag H) =
      Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 ρ p k ≼ w V W
    star-right-rel W = Lift (lsuc 0ℓ) ⊥
  𝒱body {A = A} {B = ★} ρ (⊑-★ _ G g p) (suc k) ≽ w V W =
    star-right-rel W
    where
    star-right-rel : Term → Set₁
    star-right-rel (W up tag H) =
      Lift (lsuc 0ℓ) (G ≡ H) × 𝒱 ρ p k ≽ w V W
    star-right-rel W = Lift (lsuc 0ℓ) ⊥

  𝒱body ρ (⊑-｀ αˡ αʳ) zero dir w V W = seal-rel V W
    where
    seal-rel : Term → Term → Set₁
    seal-rel (V down seal βˡ) (W down seal βʳ) =
      Σ[ eqˡ ∈ αˡ ≡ βˡ ] Σ[ eqʳ ∈ αʳ ≡ βʳ ] Σ[ R ∈ Rel ]
        (η w ∋η αˡ ↔ αʳ ∶ R) × R zero dir V W
    seal-rel V W = Lift (lsuc 0ℓ) ⊥
  𝒱body ρ (⊑-｀ αˡ αʳ) (suc k) dir w V W = seal-rel V W
    where
    seal-rel : Term → Term → Set₁
    seal-rel (V down seal βˡ) (W down seal βʳ) =
      Σ[ eqˡ ∈ αˡ ≡ βˡ ] Σ[ eqʳ ∈ αʳ ≡ βʳ ] Σ[ R ∈ Rel ]
        (η w ∋η αˡ ↔ αʳ ∶ R) × R (suc k) dir V W
    seal-rel V W = Lift (lsuc 0ℓ) ⊥

  𝒱body ρ (⊑-＇ X) n dir w V W =
    Lift (lsuc 0ℓ) (relᵗ ρ X n dir V W)

  ℰbody :
    ∀ {Δ A B} →
    RelSub Δ → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  ℰbody ρ p zero dir w Mˡ Mʳ = Lift (lsuc 0ℓ) ⊤

  ℰbody {A = A} {B = B} ρ p (suc k) ≼ w Mˡ Mʳ =
    (Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ] Σ[ wfΣˡ′ ∈ StoreWf (Δ w) Ψˡ′ Σˡ′ ] Σ[ Mˡ′ ∈ Term ]
      (Σˡ w ∣ Mˡ —→ Σˡ′ ∣ Mˡ′) ×
      ℰ ρ p k ≼ (mkWorldˡ w Σˡ′ wfΣˡ′) Mˡ′ Mʳ)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) Ψʳ′ Σʳ′ ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mˡ × Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) Ψʳ′ Σʳ′ ]
      Σ[ Wʳ ∈ Term ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ Wʳ) ×
      𝒱 ρ p k ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Wʳ)

  ℰbody {A = A} {B = B} ρ p (suc k) ≽ w Mˡ Mʳ =
    (Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) Ψʳ′ Σʳ′ ] Σ[ Mʳ′ ∈ Term ]
      (Σʳ w ∣ Mʳ —→ Σʳ′ ∣ Mʳ′) ×
      ℰ ρ p k ≽ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Mʳ′)
    ⊎
    (Σ[ Σʳ′ ∈ Store ] Σ[ Ψʳ′ ∈ SealCtx ] Σ[ wfΣʳ′ ∈ StoreWf (Δ w) Ψʳ′ Σʳ′ ] Σ[ ℓ ∈ Label ]
      (Σʳ w ∣ Mʳ —↠ Σʳ′ ∣ blame ℓ))
    ⊎
    (Value Mʳ × Σ[ Σˡ′ ∈ Store ] Σ[ Ψˡ′ ∈ SealCtx ] Σ[ wfΣˡ′ ∈ StoreWf (Δ w) Ψˡ′ Σˡ′ ]
      Σ[ Wˡ ∈ Term ]
      (Σˡ w ∣ Mˡ —↠ Σˡ′ ∣ Wˡ) ×
      𝒱 ρ p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ Mʳ)

  𝒱 :
    ∀ {Δ A B} →
    RelSub Δ → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  𝒱 {A = A} {B = B} ρ p n dir w V W =
    Value V × Value W ×
    ((0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ V ⦂ substᵗ (leftᵗ ρ) A) ×
     (0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ W ⦂ substᵗ (rightᵗ ρ) B)) ×
    𝒱body ρ p n dir w V W

  ℰ :
    ∀ {Δ A B} →
    RelSub Δ → A ⊑ B → ℕ → Dir → World → Term → Term → Set₁
  ℰ {A = A} {B = B} ρ p n dir w Mˡ Mʳ =
    ((0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ substᵗ (leftᵗ ρ) A) ×
     (0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ substᵗ (rightᵗ ρ) B)) ×
    ℰbody ρ p n dir w Mˡ Mʳ

𝒱-cast :
  ∀ {Δ A A′ B B′ n dir w V W} {ρ : RelSub Δ} {p : A ⊑ B} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  𝒱 ρ p n dir w V W →
  𝒱 ρ (cast-⊑ eqA eqB p) n dir w V W
𝒱-cast refl refl rel = rel

ℰ-cast :
  ∀ {Δ A A′ B B′ n dir w M N} {ρ : RelSub Δ} {p : A ⊑ B} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  ℰ ρ p n dir w M N →
  ℰ ρ (cast-⊑ eqA eqB p) n dir w M N
ℰ-cast refl refl rel = rel

record SemanticRelAt {A B : Ty}
    (ρ : RelSub 0)
    (p : A ⊑ B)
    (w : World)
    (R : Rel) : Set₁ where
  field
    sound :
      ∀ {w′ k dir V W} →
      w′ ⪰ w →
      R k dir V W →
      𝒱 ρ p k dir w′ V W
    complete :
      ∀ {w′ k dir V W} →
      w′ ⪰ w →
      𝒱 ρ p k dir w′ V W →
      R k dir V W
    semantic-down : DownClosed R
open SemanticRelAt public

record SemanticRelKit {A B : Ty}
    (ρ : RelSub 0)
    (p : A ⊑ B)
    (w : World) : Set₁ where
  constructor semanticRelKit
  field
    rel : Rel
    semantic : SemanticRelAt ρ p w rel
open SemanticRelKit public

postulate
  semanticRelAt :
    ∀ {A B : Ty} →
    (ρ : RelSub 0) →
    (p : A ⊑ B) →
    (w : World) →
    SemanticRelKit ρ p w

  𝒱-semantic-open :
    ∀ {A B T n dir w₀ w V W R} {ρ : RelSub 0}
      {p : A ⊑ B}
      {wfTˡ : WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T)}
      {wfTʳ : WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T)} →
    w ⪰ w₀ →
    (sem : SemanticRelAt ρ (substᴿ-⊑ ρ (⊑-refl {A = T})) w₀ R) →
    𝒱 (extendρ ρ
         (substᵗ (leftᵗ ρ) T)
         (substᵗ (rightᵗ ρ) T)
         (Ψˡ w , WfTy-weakenᵗ wfTˡ z≤n)
         (Ψʳ w , WfTy-weakenᵗ wfTʳ z≤n)
         (substᴿ-⊑ ρ (⊑-refl {A = T}))
         R
         (semantic-down sem))
      p n dir w V W →
    𝒱 ρ (substᵗ-⊑ (singleTyEnv T) p) n dir w V W

  ℰ-semantic-open :
    ∀ {A B T n dir w₀ w M N R} {ρ : RelSub 0}
      {p : A ⊑ B}
      {wfTˡ : WfTy 0 (Ψˡ w) (substᵗ (leftᵗ ρ) T)}
      {wfTʳ : WfTy 0 (Ψʳ w) (substᵗ (rightᵗ ρ) T)} →
    w ⪰ w₀ →
    (sem : SemanticRelAt ρ (substᴿ-⊑ ρ (⊑-refl {A = T})) w₀ R) →
    ℰ (extendρ ρ
         (substᵗ (leftᵗ ρ) T)
         (substᵗ (rightᵗ ρ) T)
         (Ψˡ w , WfTy-weakenᵗ wfTˡ z≤n)
         (Ψʳ w , WfTy-weakenᵗ wfTʳ z≤n)
         (substᴿ-⊑ ρ (⊑-refl {A = T}))
         R
         (semantic-down sem))
      p n dir w M N →
    ℰ ρ (substᵗ-⊑ (singleTyEnv T) p) n dir w M N

𝒱-left-value :
  ∀ {Δ A B} {ρ : RelSub Δ} {p : A ⊑ B} {k : ℕ} {dir : Dir}
    {w : World} {V W : Term} →
  𝒱 ρ p k dir w V W →
  Value V
𝒱-left-value {k = zero} Vrel = proj₁ Vrel
𝒱-left-value {k = suc n} Vrel = proj₁ Vrel

𝒱-right-value :
  ∀ {Δ A B} {ρ : RelSub Δ} {p : A ⊑ B} {k : ℕ} {dir : Dir}
    {w : World} {V W : Term} →
  𝒱 ρ p k dir w V W →
  Value W
𝒱-right-value {k = zero} Vrel = proj₁ (proj₂ Vrel)
𝒱-right-value {k = suc n} Vrel = proj₁ (proj₂ Vrel)

wkΨ-term-+ :
  ∀ {Δ Ψ Σ Γ M A} →
  (k : ℕ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ (k + Ψ) ∣ Σ ∣ Γ ⊢ M ⦂ A
wkΨ-term-+ zero V⊢ = V⊢
wkΨ-term-+ (suc k) V⊢ = wkΨ-term-suc (wkΨ-term-+ k V⊢)

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

𝒱′-⪰ :
  ∀ {Δ Aˡ Aʳ Bˡ Bʳ k dir w w′ V W}
    {ρ : RelSub Δ} {pA : Aˡ ⊑ Aʳ} {pB : Bˡ ⊑ Bʳ} →
  w′ ⪰ w →
  𝒱′ ρ k dir pA pB w V W →
  𝒱′ ρ k dir pA pB w′ V W
𝒱′-⪰ {k = zero} w′⪰ rel = lift tt
𝒱′-⪰
    {k = suc k} {dir = dir} {w′ = w′} {V = V} {W = W} {ρ = ρ}
    {pA = pA} {pB = pB} w′⪰ (step , rest) =
  step′ , 𝒱′-⪰ {k = k} w′⪰ rest
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

𝒱-⪰ :
  ∀ {Δ A B n dir w w′ V W} (ρ : RelSub Δ) (p : A ⊑ B) →
  w′ ⪰ w →
  𝒱 ρ p n dir w V W →
  𝒱 ρ p n dir w′ V W
𝒱-⪰ {n = zero} ρ (⊑-‵ `ℕ) w′⪰
  (vV , vW , (V⊢ , W⊢) , nat-rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , nat-rel
𝒱-⪰ {n = suc k} ρ (⊑-‵ `ℕ) w′⪰
  (vV , vW , (V⊢ , W⊢) , nat-rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , nat-rel
𝒱-⪰ {n = zero} ρ (⊑-‵ `𝔹) w′⪰
  (vV , vW , (V⊢ , W⊢) , lift ())
𝒱-⪰ {n = suc k} ρ (⊑-‵ `𝔹) w′⪰
  (vV , vW , (V⊢ , W⊢) , lift ())
𝒱-⪰ {n = zero} ρ (⊑-＇ X) w′⪰
  (vV , vW , (V⊢ , W⊢) , lift rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , lift rel
𝒱-⪰ {n = suc k} ρ (⊑-＇ X) w′⪰
  (vV , vW , (V⊢ , W⊢) , lift rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , lift rel
𝒱-⪰ {n = zero} ρ ⊑-★★ w′⪰
  (vV , vW , (V⊢ , W⊢) , rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , lift⊤
𝒱-⪰ {n = suc k} {dir = dir} ρ ⊑-★★ w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  with canonical-★ vV V⊢ | canonical-★ vW W⊢
𝒱-⪰ {n = suc k} {dir = dir} ρ ⊑-★★ w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = U} {G = G} vU eqV
  | sv-up-tag {W = U′} {G = H} vU′ eqW
  rewrite eqV | eqW with rel
𝒱-⪰ {n = suc k} {dir = dir} ρ ⊑-★★ w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = U} {G = G} vU eqV
  | sv-up-tag {W = U′} {G = H} vU′ eqW
  | eqG , inner =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    eqG , 𝒱-⪰ {n = k} {dir = dir} ρ (⊑-refl {A = G}) w′⪰ inner
𝒱-⪰ {n = zero} {dir = ≼} ρ (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , lift⊤
𝒱-⪰ {n = zero} {dir = ≽} ρ (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , lift⊤
𝒱-⪰ {n = suc k} {dir = ≼} ρ (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  with canonical-★ vW W⊢
𝒱-⪰ {n = suc k} {dir = ≼} ρ (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = W′} {G = H} vW′ eqW
  rewrite eqW with rel
𝒱-⪰ {n = suc k} {dir = ≼} ρ (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = W′} {G = H} vW′ eqW
  | eqG , inner =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    eqG , 𝒱-⪰ {n = k} {dir = ≼} ρ p w′⪰ inner
𝒱-⪰ {n = suc k} {dir = ≽} ρ (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  with canonical-★ vW W⊢
𝒱-⪰ {n = suc k} {dir = ≽} ρ (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = W′} {G = H} vW′ eqW
  rewrite eqW with rel
𝒱-⪰ {n = suc k} {dir = ≽} ρ (⊑-★ _ G g p) w′⪰
  (vV , vW , (V⊢ , W⊢) , rel)
  | sv-up-tag {W = W′} {G = H} vW′ eqW
  | eqG , inner =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    eqG , 𝒱-⪰ {n = k} {dir = ≽} ρ p w′⪰ inner
𝒱-⪰ {n = zero} ρ (⊑-｀ αˡ αʳ) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
𝒱-⪰ {n = zero} ρ (⊑-｀ αˡ αʳ) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  | sv-down-seal {W = V′} vV′ eqV
  | sv-down-seal {W = W′} vW′ eqW
  rewrite eqV | eqW with rel
𝒱-⪰ {n = zero} ρ (⊑-｀ αˡ αʳ) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  | sv-down-seal {W = V′} vV′ eqV
  | sv-down-seal {W = W′} vW′ eqW
  | eqˡ , eqʳ , R , η∋ , Rrel =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    eqˡ , eqʳ , R , η∋-weaken (_⪰_.growη w′⪰) η∋ , Rrel
𝒱-⪰ {n = suc k} ρ (⊑-｀ αˡ αʳ) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
𝒱-⪰ {n = suc k} ρ (⊑-｀ αˡ αʳ) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  | sv-down-seal {W = V′} vV′ eqV
  | sv-down-seal {W = W′} vW′ eqW
  rewrite eqV | eqW with rel
𝒱-⪰ {n = suc k} ρ (⊑-｀ αˡ αʳ) w′⪰ (vV , vW , (V⊢ , W⊢) , rel)
  | sv-down-seal {W = V′} vV′ eqV
  | sv-down-seal {W = W′} vW′ eqW
  | eqˡ , eqʳ , R , η∋ , Rrel =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    eqˡ , eqʳ , R , η∋-weaken (_⪰_.growη w′⪰) η∋ , Rrel
𝒱-⪰ {n = n} ρ (⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) w′⪰
  (vV , vW , (V⊢ , W⊢) , fun-rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) , 𝒱′-⪰ {k = n} w′⪰ fun-rel
𝒱-⪰ {n = n} ρ (⊑-∀ Aˡ Aʳ p) w′⪰
  (vV , vW , (V⊢ , W⊢) , all-rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    λ {w″} w″⪰ R downR Tˡ Tʳ hTˡ hTʳ pT →
      all-rel (⪰-trans w″⪰ w′⪰) R downR Tˡ Tʳ hTˡ hTʳ pT
𝒱-⪰ {n = n} ρ (⊑-ν Aˡ Bʳ p) w′⪰
  (vV , vW , (V⊢ , W⊢) , nu-rel) =
  vV , vW , (wk⪰ˡ w′⪰ V⊢ , wk⪰ʳ w′⪰ W⊢) ,
    λ {w″} w″⪰ R downR Tˡ Tʳ hTˡ hTʳ pT →
      nu-rel (⪰-trans w″⪰ w′⪰) R downR Tˡ Tʳ hTˡ hTʳ pT

ℰ-expand-≼-left :
  ∀ {Δ A B} {ρ : RelSub Δ} {p : A ⊑ B}
    {k : ℕ} {w : World} {Mˡ Mˡ′ Mʳ} →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ substᵗ (leftᵗ ρ) A →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ substᵗ (rightᵗ ρ) B →
  Σˡ w ∣ Mˡ —→ Σˡ w ∣ Mˡ′ →
  ℰ ρ p k ≼ w Mˡ′ Mʳ →
  ℰ ρ p (suc k) ≼ w Mˡ Mʳ
ℰ-expand-≼-left
  {w = mkWorld Δ Ψˡ Ψʳ Σˡ Σʳ wfΣˡ wfΣʳ η}
  Mˡ⊢ Mʳ⊢ Mˡ→Mˡ′ rel =
  (Mˡ⊢ , Mʳ⊢) , inj₁ (Σˡ , Ψˡ , wfΣˡ , _ , Mˡ→Mˡ′ , rel)

ℰ-expand-≽-right :
  ∀ {Δ A B} {ρ : RelSub Δ} {p : A ⊑ B}
    {k : ℕ} {w : World} {Mˡ Mʳ Mʳ′} →
  0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ substᵗ (leftᵗ ρ) A →
  0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ substᵗ (rightᵗ ρ) B →
  Σʳ w ∣ Mʳ —→ Σʳ w ∣ Mʳ′ →
  ℰ ρ p k ≽ w Mˡ Mʳ′ →
  ℰ ρ p (suc k) ≽ w Mˡ Mʳ
ℰ-expand-≽-right
  {w = mkWorld Δ Ψˡ Ψʳ Σˡ Σʳ wfΣˡ wfΣʳ η}
  Mˡ⊢ Mʳ⊢ Mʳ→Mʳ′ rel =
  (Mˡ⊢ , Mʳ⊢) , inj₁ (Σʳ , Ψʳ , wfΣʳ , _ , Mʳ→Mʳ′ , rel)

mutual
  ℰ-expand-≼-right :
    ∀ {Δ A B} {ρ : RelSub Δ} {p : A ⊑ B}
      {k : ℕ} {w : World} {Mˡ Mʳ Mʳ′} →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ substᵗ (leftᵗ ρ) A →
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ substᵗ (rightᵗ ρ) B →
    Σʳ w ∣ Mʳ —→ Σʳ w ∣ Mʳ′ →
    ℰ ρ p k ≼ w Mˡ Mʳ′ →
    ℰ ρ p k ≼ w Mˡ Mʳ
  ℰ-expand-≼-right {k = zero} Mˡ⊢ Mʳ⊢ Mʳ→Mʳ′ rel =
    (Mˡ⊢ , Mʳ⊢) , lift tt
  ℰ-expand-≼-right {ρ = ρ} {p = p} {k = suc k} {w = w} {Mʳ = Mʳ}
    {Mʳ′ = Mʳ′} Mˡ⊢ Mʳ⊢ Mʳ→Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ , rel)) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₁
      (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , Mˡ→Mˡ′ ,
        ℰ-expand-≼-right {ρ = ρ} {p = p} {k = k}
          {w = mkWorldˡ w Σˡ′ wfΣˡ′} {Mˡ = Mˡ′}
          {Mʳ = Mʳ} {Mʳ′ = Mʳ′}
          (proj₁ (proj₁ rel)) Mʳ⊢ Mʳ→Mʳ′ rel)
  ℰ-expand-≼-right {k = suc k} {Mʳ = Mʳ} Mˡ⊢ Mʳ⊢ Mʳ→Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , Mʳ′↠blame))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂
      (inj₁
        (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ ,
         _—→⟨_⟩_ Mʳ Mʳ→Mʳ′ Mʳ′↠blame))
  ℰ-expand-≼-right {k = suc k} {Mʳ = Mʳ} Mˡ⊢ Mʳ⊢ Mʳ→Mʳ′
    ((Mˡ⊢′ , Mʳ′⊢) , inj₂ (inj₂
      (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Wʳ , Mʳ′↠Wʳ , rel))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂ (inj₂
      (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Wʳ ,
       _—→⟨_⟩_ Mʳ Mʳ→Mʳ′ Mʳ′↠Wʳ ,
       rel))

  ℰ-expand-≽-left :
    ∀ {Δ A B} {ρ : RelSub Δ} {p : A ⊑ B}
      {k : ℕ} {w : World} {Mˡ Mˡ′ Mʳ} →
    0 ∣ Ψˡ w ∣ Σˡ w ∣ [] ⊢ Mˡ ⦂ substᵗ (leftᵗ ρ) A →
    0 ∣ Ψʳ w ∣ Σʳ w ∣ [] ⊢ Mʳ ⦂ substᵗ (rightᵗ ρ) B →
    Σˡ w ∣ Mˡ —→ Σˡ w ∣ Mˡ′ →
    ℰ ρ p k ≽ w Mˡ′ Mʳ →
    ℰ ρ p k ≽ w Mˡ Mʳ
  ℰ-expand-≽-left {k = zero} Mˡ⊢ Mʳ⊢ Mˡ→Mˡ′ rel =
    (Mˡ⊢ , Mʳ⊢) , lift tt
  ℰ-expand-≽-left {ρ = ρ} {p = p} {k = suc k} {w = w} {Mˡ = Mˡ}
    {Mˡ′ = Mˡ′} Mˡ⊢ Mʳ⊢ Mˡ→Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , Mʳ→Mʳ′ , rel)) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₁
      (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , Mʳ→Mʳ′ ,
        ℰ-expand-≽-left {ρ = ρ} {p = p} {k = k}
          {w = mkWorldʳ w Σʳ′ wfΣʳ′} {Mˡ = Mˡ}
          {Mˡ′ = Mˡ′} {Mʳ = Mʳ′}
          Mˡ⊢ (proj₂ (proj₁ rel)) Mˡ→Mˡ′ rel)
  ℰ-expand-≽-left {k = suc k} Mˡ⊢ Mʳ⊢ Mˡ→Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , Mʳ↠blame))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , Mʳ↠blame))
  ℰ-expand-≽-left {k = suc k} {Mˡ = Mˡ} Mˡ⊢ Mʳ⊢ Mˡ→Mˡ′
    ((Mˡ′⊢ , Mʳ⊢′) , inj₂ (inj₂
      (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Wˡ , Mˡ′↠Wˡ , rel))) =
    (Mˡ⊢ , Mʳ⊢) ,
    inj₂ (inj₂
      (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Wˡ ,
       _—→⟨_⟩_ Mˡ Mˡ→Mˡ′ Mˡ′↠Wˡ ,
       rel))

------------------------------------------------------------------------
-- Environment interpretation for open terms
------------------------------------------------------------------------

record RelEnv : Set where
  field
    leftˣ : Substˣ
    rightˣ : Substˣ
open RelEnv public

∅γ : RelEnv
(∅γ .leftˣ) x = ` x
(∅γ .rightˣ) x = ` x

⇓γ : RelEnv → RelEnv
(⇓γ γ .leftˣ) x = leftˣ γ (suc x)
(⇓γ γ .rightˣ) x = rightˣ γ (suc x)

⇑ᵗγ : RelEnv → RelEnv
(⇑ᵗγ γ .leftˣ) = ↑ᵗᵐ (leftˣ γ)
(⇑ᵗγ γ .rightˣ) = ↑ᵗᵐ (rightˣ γ)

𝒢 : PCtx → ℕ → Dir → World → RelSub 0 → RelEnv → Set₁
𝒢 [] n dir w ρ γ = Lift (lsuc 0ℓ) ⊤
𝒢 ((A , B , p) ∷ Γ) n dir w ρ γ =
  Value (leftˣ γ zero) ×
  Value (rightˣ γ zero) ×
  𝒱 ρ p n dir w (leftˣ γ zero) (rightˣ γ zero) ×
  (substᵗᵐ (leftᵗ ρ) (leftˣ γ zero) ≡ leftˣ γ zero) ×
  (substᵗᵐ (rightᵗ ρ) (rightˣ γ zero) ≡ rightˣ γ zero) ×
  𝒢 Γ n dir w ρ (⇓γ γ)

postulate
  𝒱-rename-wk :
    ∀ {A B n dir w V W} {ρ ρ′ : RelSub 0} {ξ : Renameᵗ}
      {p : A ⊑ B} →
    WkRel ξ ρ ρ′ →
    𝒱 ρ p n dir w V W →
    𝒱 ρ′ (renameᵗ-⊑ ξ p) n dir w V W

  ℰ-rename-wk :
    ∀ {A B n dir w M N} {ρ ρ′ : RelSub 0} {ξ : Renameᵗ}
      {p : A ⊑ B} →
    WkRel ξ ρ ρ′ →
    ℰ ρ p n dir w M N →
    ℰ ρ′ (renameᵗ-⊑ ξ p) n dir w M N

  𝒢-rename-suc :
    ∀ {Γ n dir w ρ ρ′ γ} →
    WkRel suc ρ ρ′ →
    𝒢 Γ n dir w ρ γ →
    𝒢 (⇑ᵗᴾ Γ) n dir w ρ′ (⇑ᵗγ γ)

record RelWf (E : TPEnv) (w : World) (ρ : RelSub 0) : Set where
  field
    Ψˡ≤ : TPEnv.Ψ E ≤ Ψˡ w
    Ψʳ≤ : TPEnv.Ψ E ≤ Ψʳ w
    leftᵗ-wf : TySubstWf (TPEnv.Δ E) 0 (Ψˡ w) (leftᵗ ρ)
    rightᵗ-wf : TySubstWf (TPEnv.Δ E) 0 (Ψʳ w) (rightᵗ ρ)
    storeˡ : substStoreᵗ (leftᵗ ρ) (TPEnv.store E) ⊆ˢ Σˡ w
    storeʳ : substStoreᵗ (rightᵗ ρ) (TPEnv.store E) ⊆ˢ Σʳ w
open RelWf public

TySubstWf-weakenˢ :
  ∀ {Δ Δ′ Ψ Ψ′} {σ : Substᵗ} →
  Ψ ≤ Ψ′ →
  TySubstWf Δ Δ′ Ψ σ →
  TySubstWf Δ Δ′ Ψ′ σ
TySubstWf-weakenˢ Ψ≤Ψ′ hσ X<Δ = WfTy-weakenˢ (hσ X<Δ) Ψ≤Ψ′

RelWf-extend :
  ∀ {E P w ρ} →
  RelWf E w ρ →
  RelWf (extendᴾ E P) w ρ
RelWf-extend wf .RelWf.Ψˡ≤ = Ψˡ≤ wf
RelWf-extend wf .RelWf.Ψʳ≤ = Ψʳ≤ wf
RelWf-extend wf .RelWf.leftᵗ-wf = leftᵗ-wf wf
RelWf-extend wf .RelWf.rightᵗ-wf = rightᵗ-wf wf
RelWf-extend wf .RelWf.storeˡ = storeˡ wf
RelWf-extend wf .RelWf.storeʳ = storeʳ wf

RelWf-⪰ :
  ∀ {E w w′ ρ} →
  w′ ⪰ w →
  RelWf E w ρ →
  RelWf E w′ ρ
RelWf-⪰ w′⪰ wf .RelWf.Ψˡ≤ = ≤-trans (Ψˡ≤ wf) (_⪰_.growΨˡ w′⪰)
RelWf-⪰ w′⪰ wf .RelWf.Ψʳ≤ = ≤-trans (Ψʳ≤ wf) (_⪰_.growΨʳ w′⪰)
RelWf-⪰ w′⪰ wf .RelWf.leftᵗ-wf =
  TySubstWf-weakenˢ (_⪰_.growΨˡ w′⪰) (leftᵗ-wf wf)
RelWf-⪰ w′⪰ wf .RelWf.rightᵗ-wf =
  TySubstWf-weakenˢ (_⪰_.growΨʳ w′⪰) (rightᵗ-wf wf)
RelWf-⪰ w′⪰ wf .RelWf.storeˡ =
  ⊆ˢ-trans (storeˡ wf) (_⪰_.growˡ w′⪰)
RelWf-⪰ w′⪰ wf .RelWf.storeʳ =
  ⊆ˢ-trans (storeʳ wf) (_⪰_.growʳ w′⪰)

_∣_⊨_⊑_⦂_ : TPEnv → Dir → Term → Term → ∀ {A B} → A ⊑ B → Set₁
E ∣ dir ⊨ M ⊑ M′ ⦂ p =
  ∀ (n : ℕ) (w : World) (ρ : RelSub 0) (γ : RelEnv) →
  RelWf E w ρ →
  𝒢 (TPEnv.Γ E) n dir w ρ γ →
  ℰ ρ p n dir w
    (substᵗᵐ (leftᵗ ρ) (substˣ-term (leftˣ γ) M))
    (substᵗᵐ (rightᵗ ρ) (substˣ-term (rightˣ γ) M′))

_⊨_⊑_⦂_ : TPEnv → Term → Term → ∀ {A B} → A ⊑ B → Set₁
E ⊨ M ⊑ M′ ⦂ p = (E ∣ ≼ ⊨ M ⊑ M′ ⦂ p) × (E ∣ ≽ ⊨ M ⊑ M′ ⦂ p)

proj⊨ :
  ∀ {E M M′ A B} {p : A ⊑ B} →
  (dir : Dir) →
  E ⊨ M ⊑ M′ ⦂ p →
  E ∣ dir ⊨ M ⊑ M′ ⦂ p
proj⊨ ≼ rel = proj₁ rel
proj⊨ ≽ rel = proj₂ rel

FunAll :
  ∀ {Δ Aˡ Aʳ Bˡ Bʳ} →
  RelSub Δ → ℕ → Aˡ ⊑ Aʳ → Bˡ ⊑ Bʳ →
  Dir → World → Term → Term → Set₁
FunAll ρ zero pA pB dir w V W = Lift (lsuc 0ℓ) ⊤
FunAll ρ (suc k) pA pB dir w V W =
  (∀ {w′} → w′ ⪰ w → ∀ {V′ W′} →
    𝒱 ρ pA (suc k) dir w′ V′ W′ →
    Σ[ Lβ ∈ Term ] Σ[ Rβ ∈ Term ]
      (Σˡ w′ ∣ (V · V′) —→ Σˡ w′ ∣ Lβ) ×
      (Σʳ w′ ∣ (W · W′) —→ Σʳ w′ ∣ Rβ) ×
      ℰ ρ pB (suc k) dir w′ Lβ Rβ)
  ×
  FunAll ρ k pA pB dir w V W

𝒱′→FunAll :
  ∀ {Δ Aˡ Aʳ Bˡ Bʳ n dir w V W}
    {ρ : RelSub Δ} {pA : Aˡ ⊑ Aʳ} {pB : Bˡ ⊑ Bʳ} →
  𝒱′ ρ n dir pA pB w V W →
  FunAll ρ n pA pB dir w V W
𝒱′→FunAll {n = zero} V′n = lift tt
𝒱′→FunAll {n = suc k} (step , rest) = step , 𝒱′→FunAll {n = k} rest

FunAll→𝒱′ :
  ∀ {Δ Aˡ Aʳ Bˡ Bʳ n dir w V W}
    {ρ : RelSub Δ} {pA : Aˡ ⊑ Aʳ} {pB : Bˡ ⊑ Bʳ} →
  FunAll ρ n pA pB dir w V W →
  𝒱′ ρ n dir pA pB w V W
FunAll→𝒱′ {n = zero} all = lift⊤
FunAll→𝒱′ {n = suc k} (step , rest) =
  step , FunAll→𝒱′ {n = k} rest

mutual
  𝒱-monotone :
    ∀ {Δ} (ρ : RelSub Δ) A B (p : A ⊑ B) k dir w V W →
    𝒱 ρ p (suc k) dir w V W →
    𝒱 ρ p k dir w V W
  𝒱-monotone ρ .(‵ `ℕ) .(‵ `ℕ) (⊑-‵ `ℕ) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , nat-rel) =
    vV , vW , (V⊢ , W⊢) , nat-rel
  𝒱-monotone ρ .(‵ `ℕ) .(‵ `ℕ) (⊑-‵ `ℕ) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , nat-rel) =
    vV , vW , (V⊢ , W⊢) , nat-rel
  𝒱-monotone ρ .(‵ `𝔹) .(‵ `𝔹) (⊑-‵ `𝔹) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , lift ())
  𝒱-monotone ρ .(‵ `𝔹) .(‵ `𝔹) (⊑-‵ `𝔹) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , lift ())
  𝒱-monotone ρ .(＇ _) .(＇ _) (⊑-＇ X) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , lift rel) =
    vV , vW , (V⊢ , W⊢) , lift (rel-downᵗ ρ X rel)
  𝒱-monotone ρ .(＇ _) .(＇ _) (⊑-＇ X) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , lift rel) =
    vV , vW , (V⊢ , W⊢) , lift (rel-downᵗ ρ X rel)
  𝒱-monotone ρ .(★) .(★) ⊑-★★ zero dir w V W
    (vV , vW , (V⊢ , W⊢) , rel) =
    vV , vW , (V⊢ , W⊢) , lift⊤
  𝒱-monotone ρ .(★) .(★) ⊑-★★ (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    with canonical-★ vV V⊢ | canonical-★ vW W⊢
  𝒱-monotone ρ .(★) .(★) ⊑-★★ (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-up-tag {W = U} {G = G} vU eqV
    | sv-up-tag {W = U′} {G = H} vU′ eqW
    rewrite eqV | eqW with rel
  𝒱-monotone ρ .(★) .(★) ⊑-★★ (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-up-tag {W = U} {G = G} vU eqV
    | sv-up-tag {W = U′} {G = H} vU′ eqW
    | eqG , inner =
    vV , vW , (V⊢ , W⊢) ,
      eqG ,
      𝒱-monotone ρ G G (⊑-refl {A = G}) k dir w U U′ inner
  𝒱-monotone ρ A .(★) (⊑-★ _ G g p) zero ≼ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel) =
    vV , vW , (V⊢ , W⊢) , lift⊤
  𝒱-monotone ρ A .(★) (⊑-★ _ G g p) zero ≽ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel) =
    vV , vW , (V⊢ , W⊢) , lift⊤
  𝒱-monotone ρ A B (⊑-★ _ G g p) (suc k) ≼ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    with canonical-★ vW W⊢
  𝒱-monotone ρ A B (⊑-★ _ G g p) (suc k) ≼ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    rewrite eqW with star-rel
  𝒱-monotone ρ A B (⊑-★ _ G g p) (suc k) ≼ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    | eqG , inner =
    vV , vW , (V⊢ , W⊢) ,
      eqG ,
      𝒱-monotone ρ A G p k ≼ w V W′ inner
  𝒱-monotone ρ A B (⊑-★ _ G g p) (suc k) ≽ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    with canonical-★ vW W⊢
  𝒱-monotone ρ A B (⊑-★ _ G g p) (suc k) ≽ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    rewrite eqW with star-rel
  𝒱-monotone ρ A B (⊑-★ _ G g p) (suc k) ≽ w V W
    (vV , vW , (V⊢ , W⊢) , star-rel)
    | sv-up-tag {W = W′} {G = H} vW′ eqW
    | eqG , inner =
    vV , vW , (V⊢ , W⊢) ,
      eqG ,
      𝒱-monotone ρ A G p k ≽ w V W′ inner
  𝒱-monotone ρ A B (⊑-｀ αˡ αʳ) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
  𝒱-monotone ρ A B (⊑-｀ αˡ αʳ) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    rewrite eqV | eqW with rel
  𝒱-monotone ρ A B (⊑-｀ αˡ αʳ) zero dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    | eqˡ , eqʳ , R , η∋ , Rrel =
    vV , vW , (V⊢ , W⊢) ,
      eqˡ , eqʳ , R , η∋ , η∋-downClosed η∋ Rrel
  𝒱-monotone ρ A B (⊑-｀ αˡ αʳ) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    with canonical-｀ vV V⊢ | canonical-｀ vW W⊢
  𝒱-monotone ρ A B (⊑-｀ αˡ αʳ) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    rewrite eqV | eqW with rel
  𝒱-monotone ρ A B (⊑-｀ αˡ αʳ) (suc k) dir w V W
    (vV , vW , (V⊢ , W⊢) , rel)
    | sv-down-seal {W = V′} vV′ eqV
    | sv-down-seal {W = W′} vW′ eqW
    | eqˡ , eqʳ , R , η∋ , Rrel =
    vV , vW , (V⊢ , W⊢) ,
      eqˡ , eqʳ , R , η∋ , η∋-downClosed η∋ Rrel
  𝒱-monotone ρ A B (⊑-⇒ Aˡ Aʳ Bˡ Bʳ pA pB) k dir w V W
    (vV , vW , (V⊢ , W⊢) , fun-rel) =
    vV , vW , (V⊢ , W⊢) , proj₂ fun-rel
  𝒱-monotone ρ A B (⊑-∀ Aˡ Aʳ p) k dir w V W
    (vV , vW , (V⊢ , W⊢) , all-rel) =
    vV , vW , (V⊢ , W⊢) ,
      λ {w′} w⪰ (R : Rel) (downR : DownClosed R) Tˡ Tʳ hTˡ hTʳ pT →
        ℰ-monotone (extendρ ρ Tˡ Tʳ
                     (Ψˡ w′ , WfTy-weakenᵗ hTˡ z≤n)
                     (Ψʳ w′ , WfTy-weakenᵗ hTʳ z≤n)
                     pT R downR)
          _ _ p k dir
          (extendWorld w′ R downR)
          (V ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) Aˡ [ Tˡ ])
          (W ⦂∀ substᵗ (extsᵗ (rightᵗ ρ)) Aʳ [ Tʳ ])
          (all-rel w⪰ R downR Tˡ Tʳ hTˡ hTʳ pT)
  𝒱-monotone ρ .(`∀ _) B (⊑-ν Aˡ Bʳ p) k dir w V W
    (vV , vW , (V⊢ , W⊢) , nu-rel) =
    vV , vW , (V⊢ , W⊢) ,
      λ {w′} w⪰ (R : Rel) (downR : DownClosed R)
          Tˡ Tʳ hTˡ hTʳ pT →
        ℰ-monotone (⇑ˢρ ρ) _ _ p k dir
          (extendWorldν w′ R downR Tˡ Tʳ hTˡ hTʳ)
          (V ⦂∀ substᵗ (extsᵗ (leftᵗ ρ)) Aˡ [ ｀ length (Σˡ w′) ]) W
          (nu-rel w⪰ R downR Tˡ Tʳ hTˡ hTʳ pT)

  ℰbody-monotone :
    ∀ {Δ} (ρ : RelSub Δ) A B (p : A ⊑ B) k dir w Mˡ Mʳ →
    ℰbody ρ p (suc k) dir w Mˡ Mʳ →
    ℰbody ρ p k dir w Mˡ Mʳ
  ℰbody-monotone ρ A B p zero ≼ w Mˡ Mʳ rel = lift⊤
  ℰbody-monotone ρ A B p zero ≽ w Mˡ Mʳ rel = lift⊤
  ℰbody-monotone ρ A B p (suc k) ≼ w Mˡ Mʳ
    (inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , step , rel′)) =
    inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , step ,
      ℰ-monotone ρ A B p k ≼ (mkWorldˡ w Σˡ′ wfΣˡ′) Mˡ′ Mʳ rel′)
  ℰbody-monotone ρ A B p (suc k) ≼ w Mˡ Mʳ
    (inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , blame↠))) =
    inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , blame↠))
  ℰbody-monotone ρ A B p (suc k) ≼ w Mˡ Mʳ
    (inj₂ (inj₂ (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Wʳ , steps , Vrel))) =
    inj₂ (inj₂ (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Wʳ , steps ,
      𝒱-monotone ρ A B p k ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Wʳ Vrel))
  ℰbody-monotone ρ A B p (suc k) ≽ w Mˡ Mʳ
    (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , step , rel′)) =
    inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , step ,
      ℰ-monotone ρ A B p k ≽ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Mʳ′ rel′)
  ℰbody-monotone ρ A B p (suc k) ≽ w Mˡ Mʳ
    (inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , blame↠))) =
    inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , blame↠))
  ℰbody-monotone ρ A B p (suc k) ≽ w Mˡ Mʳ
    (inj₂ (inj₂ (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Wˡ , steps , Vrel))) =
    inj₂ (inj₂ (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Wˡ , steps ,
      𝒱-monotone ρ A B p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ Mʳ Vrel))

  ℰ-monotone :
    ∀ {Δ} (ρ : RelSub Δ) A B (p : A ⊑ B) k dir w Mˡ Mʳ →
    ℰ ρ p (suc k) dir w Mˡ Mʳ →
    ℰ ρ p k dir w Mˡ Mʳ
  ℰ-monotone ρ A B p zero ≼ w Mˡ Mʳ ((Mˡ⊢ , Mʳ⊢) , rel) =
    (Mˡ⊢ , Mʳ⊢) , lift⊤
  ℰ-monotone ρ A B p zero ≽ w Mˡ Mʳ ((Mˡ⊢ , Mʳ⊢) , rel) =
    (Mˡ⊢ , Mʳ⊢) , lift⊤
  ℰ-monotone ρ A B p (suc k) ≼ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , step , rel′)) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₁ (Σˡ′ , Ψˡ′ , wfΣˡ′ , Mˡ′ , step ,
        ℰ-monotone ρ A B p k ≼ (mkWorldˡ w Σˡ′ wfΣˡ′) Mˡ′ Mʳ rel′)
  ℰ-monotone ρ A B p (suc k) ≼ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , blame↠))) =
    (Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , blame↠))
  ℰ-monotone ρ A B p (suc k) ≼ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Wʳ , steps , Vrel))) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMˡ , Σʳ′ , Ψʳ′ , wfΣʳ′ , Wʳ , steps ,
        𝒱-monotone ρ A B p k ≼ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Wʳ Vrel))
  ℰ-monotone ρ A B p (suc k) ≽ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , step , rel′)) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , Mʳ′ , step ,
        ℰ-monotone ρ A B p k ≽ (mkWorldʳ w Σʳ′ wfΣʳ′) Mˡ Mʳ′ rel′)
  ℰ-monotone ρ A B p (suc k) ≽ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , blame↠))) =
    (Mˡ⊢ , Mʳ⊢) , inj₂ (inj₁ (Σʳ′ , Ψʳ′ , wfΣʳ′ , ℓ , blame↠))
  ℰ-monotone ρ A B p (suc k) ≽ w Mˡ Mʳ
    ((Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Wˡ , steps , Vrel))) =
    (Mˡ⊢ , Mʳ⊢) ,
      inj₂ (inj₂ (vMʳ , Σˡ′ , Ψˡ′ , wfΣˡ′ , Wˡ , steps ,
        𝒱-monotone ρ A B p k ≽ (mkWorldˡ w Σˡ′ wfΣˡ′) Wˡ Mʳ Vrel))

𝒱-lower :
  ∀ {Δ n j A B} (j<n : j <′ n) {ρ : RelSub Δ}
    {p : A ⊑ B} {dir w V W} →
  𝒱 ρ p n dir w V W →
  𝒱 ρ p j dir w V W
𝒱-lower {n = zero} (≤′-reflexive ()) rel
𝒱-lower
    {n = suc n} {A = A} {B = B} <′-base
    {ρ = ρ} {p = p} {dir = dir} {w = w} {V = V} {W = W} rel =
  𝒱-monotone ρ A B p n dir w V W rel
𝒱-lower
    {n = suc n} {A = A} {B = B} (≤′-step j<n)
    {ρ = ρ} {p = p} {dir = dir} {w = w} {V = V} {W = W} rel =
  𝒱-lower j<n {ρ = ρ} {p = p} {dir = dir} {w = w} {V = V} {W = W}
    (𝒱-monotone ρ A B p n dir w V W rel)

ℰ-lower :
  ∀ {Δ n j A B} (j<n : j <′ n) {ρ : RelSub Δ}
    {p : A ⊑ B} {dir w Mˡ Mʳ} →
  ℰ ρ p n dir w Mˡ Mʳ →
  ℰ ρ p j dir w Mˡ Mʳ
ℰ-lower {n = zero} (≤′-reflexive ()) rel
ℰ-lower
    {n = suc n} {A = A} {B = B} <′-base
    {ρ = ρ} {p = p} {dir = dir} {w = w} {Mˡ = Mˡ} {Mʳ = Mʳ} rel =
  ℰ-monotone ρ A B p n dir w Mˡ Mʳ rel
ℰ-lower
    {n = suc n} {A = A} {B = B} (≤′-step j<n)
    {ρ = ρ} {p = p} {dir = dir} {w = w} {Mˡ = Mˡ} {Mʳ = Mʳ} rel =
  ℰ-lower j<n {ρ = ρ} {p = p} {dir = dir} {w = w} {Mˡ = Mˡ} {Mʳ = Mʳ}
    (ℰ-monotone ρ A B p n dir w Mˡ Mʳ rel)
