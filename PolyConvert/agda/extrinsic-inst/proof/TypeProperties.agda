module proof.TypeProperties where

-- File Charter:
--   * Proof-only metatheory for type-level operations on `Ty`.
--   * Substitution algebra laws, commutation lemmas, and instantiation lemmas
--     that are not required by top-level definition modules.
--   * No context-shape lemmas (put those in `Ctx`) and no coercion-specific
--     lemmas.
-- Note to self:
--   * Before adding a theorem here, check whether it is really about `Ty` itself;
--     if it mentions context lookup/store/coercions as primary structure,
--     place it in that module instead.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc; _+_; _<_; _≤_; z<s; s<s)
open import Data.Nat.Properties using (<-≤-trans; _≟_; m<n⇒m<1+n; suc-injective)
open import Data.Product using (Σ-syntax)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂; subst; sym; trans)

open import Types
open import Imprecision

------------------------------------------------------------------------
-- basic lemmas
------------------------------------------------------------------------

renameᵗ-ground : ∀{G : Ty} (ρ : Renameᵗ)
  → Ground G
  → Ground (renameᵗ ρ G)
renameᵗ-ground ρ (｀ α) = ｀ α
renameᵗ-ground ρ (‵ ι) = ‵ ι
renameᵗ-ground ρ ★⇒★ = ★⇒★

substᵗ-ground : ∀{G : Ty} (σ : Substᵗ)
  → Ground G
  → Ground (substᵗ σ G)
substᵗ-ground σ (｀ α) = ｀ α
substᵗ-ground σ (‵ ι) = ‵ ι
substᵗ-ground σ ★⇒★ = ★⇒★

substVarFrom-seal-self :
  ∀ X α →
  substVarFrom X (｀ α) X ≡ ｀ α
substVarFrom-seal-self zero α = refl
substVarFrom-seal-self (suc X) α =
  cong (renameᵗ suc) (substVarFrom-seal-self X α)

substVarFrom-≢ :
  ∀ X Y s t →
  X ≢ Y →
  substVarFrom X s Y ≡ substVarFrom X t Y
substVarFrom-≢ zero zero s t X≢Y = ⊥-elim (X≢Y refl)
substVarFrom-≢ zero (suc Y) s t X≢Y = refl
substVarFrom-≢ (suc X) zero s t X≢Y = refl
substVarFrom-≢ (suc X) (suc Y) s t X≢Y =
  cong (renameᵗ suc)
    (substVarFrom-≢ X Y s t (λ eq → X≢Y (cong suc eq)))

raiseVarFrom-≢ :
  ∀ k X →
  raiseVarFrom k X ≡ k →
  ⊥
raiseVarFrom-≢ zero X ()
raiseVarFrom-≢ (suc k) zero ()
raiseVarFrom-≢ (suc k) (suc X) eq =
  raiseVarFrom-≢ k X (suc-injective eq)

raiseVarFrom-injective :
  ∀ k {X Y} →
  raiseVarFrom k X ≡ raiseVarFrom k Y →
  X ≡ Y
raiseVarFrom-injective zero eq = suc-injective eq
raiseVarFrom-injective (suc k) {zero} {zero} eq = refl
raiseVarFrom-injective (suc k) {zero} {suc Y} ()
raiseVarFrom-injective (suc k) {suc X} {zero} ()
raiseVarFrom-injective (suc k) {suc X} {suc Y} eq =
  cong suc (raiseVarFrom-injective k (suc-injective eq))

raiseVarFrom-<-inv :
  ∀ k {Δ X} →
  raiseVarFrom k X < Δ →
  X < Δ
raiseVarFrom-<-inv zero {Δ = zero} ()
raiseVarFrom-<-inv zero {Δ = suc Δ} (s<s X<Δ) = m<n⇒m<1+n X<Δ
raiseVarFrom-<-inv (suc k) {Δ = zero} ()
raiseVarFrom-<-inv (suc k) {Δ = suc Δ} {X = zero} z<s = z<s
raiseVarFrom-<-inv (suc k) {Δ = suc Δ} {X = suc X} (s<s rX<Δ) =
  s<s (raiseVarFrom-<-inv k rX<Δ)

raise-ext :
  ∀ k X →
  extᵗ (raiseVarFrom k) X ≡ raiseVarFrom (suc k) X
raise-ext k zero = refl
raise-ext k (suc X) = refl

rename-raise-ext :
  ∀ k A →
  renameᵗ (extᵗ (raiseVarFrom k)) A ≡
  renameᵗ (raiseVarFrom (suc k)) A
rename-raise-ext k A = rename-cong (raise-ext k) A

rename-raise-⇑ᵗ :
  ∀ k A →
  renameᵗ (raiseVarFrom (suc k)) (⇑ᵗ A) ≡
  ⇑ᵗ (renameᵗ (raiseVarFrom k) A)
rename-raise-⇑ᵗ k A =
  trans
    (rename-cong (λ X → sym (raise-ext k X)) (⇑ᵗ A))
    (sym (renameᵗ-suc-comm (raiseVarFrom k) A))

renameᵗ-preserves-Non∀ :
  (ρ : Renameᵗ) {A : Ty} →
  Non∀ A →
  Non∀ (renameᵗ ρ A)
renameᵗ-preserves-Non∀ ρ non∀-＇ = non∀-＇
renameᵗ-preserves-Non∀ ρ non∀-｀ = non∀-｀
renameᵗ-preserves-Non∀ ρ non∀-‵ = non∀-‵
renameᵗ-preserves-Non∀ ρ non∀-★ = non∀-★
renameᵗ-preserves-Non∀ ρ non∀-⇒ = non∀-⇒

renameᵗ-inv-Non∀ :
  (ρ : Renameᵗ) {A : Ty} →
  Non∀ (renameᵗ ρ A) →
  Non∀ A
renameᵗ-inv-Non∀ ρ {A = ＇ X} non∀A = non∀-＇
renameᵗ-inv-Non∀ ρ {A = ｀ α} non∀A = non∀-｀
renameᵗ-inv-Non∀ ρ {A = ‵ ι} non∀A = non∀-‵
renameᵗ-inv-Non∀ ρ {A = ★} non∀A = non∀-★
renameᵗ-inv-Non∀ ρ {A = A ⇒ B} non∀A = non∀-⇒
renameᵗ-inv-Non∀ ρ {A = `∀ A} ()

occurs-raise :
  ∀ k X A →
  occurs (raiseVarFrom k X) (renameᵗ (raiseVarFrom k) A) ≡
  occurs X A
occurs-raise k X (＇ Y) with X ≟ Y | raiseVarFrom k X ≟ raiseVarFrom k Y
occurs-raise k X (＇ .X) | yes refl | yes refl = refl
occurs-raise k X (＇ .X) | yes refl | no neq = ⊥-elim (neq refl)
occurs-raise k X (＇ Y) | no neq | yes eq =
  ⊥-elim (neq (raiseVarFrom-injective k eq))
occurs-raise k X (＇ Y) | no neq | no neq′ = refl
occurs-raise k X (｀ α) = refl
occurs-raise k X (‵ ι) = refl
occurs-raise k X ★ = refl
occurs-raise k X (A ⇒ B)
  rewrite occurs-raise k X A
        | occurs-raise k X B = refl
occurs-raise k X (`∀ A)
  rewrite rename-raise-ext k A =
  occurs-raise (suc k) (suc X) A

occurs-raise-fresh :
  ∀ k A →
  occurs k (renameᵗ (raiseVarFrom k) A) ≡ false
occurs-raise-fresh k (＇ X) with k ≟ raiseVarFrom k X
occurs-raise-fresh k (＇ X) | yes eq =
  ⊥-elim (raiseVarFrom-≢ k X (sym eq))
occurs-raise-fresh k (＇ X) | no neq = refl
occurs-raise-fresh k (｀ α) = refl
occurs-raise-fresh k (‵ ι) = refl
occurs-raise-fresh k ★ = refl
occurs-raise-fresh k (A ⇒ B)
  rewrite occurs-raise-fresh k A
        | occurs-raise-fresh k B = refl
occurs-raise-fresh k (`∀ A)
  rewrite rename-raise-ext k A =
  occurs-raise-fresh (suc k) A

occurs-substVarFrom-var-< :
  ∀ k X Y T →
  X < k →
  occurs X (substVarFrom k T Y) ≡ occurs X (＇ Y)
occurs-substVarFrom-var-< zero X Y T ()
occurs-substVarFrom-var-< (suc k) zero zero T z<s = refl
occurs-substVarFrom-var-< (suc k) zero (suc Y) T z<s
  rewrite occurs-raise-fresh zero (substVarFrom k T Y) = refl
occurs-substVarFrom-var-< (suc k) (suc X) zero T (s<s X<k) = refl
occurs-substVarFrom-var-< (suc k) (suc X) (suc Y) T (s<s X<k)
  rewrite occurs-raise zero X (substVarFrom k T Y)
        | occurs-substVarFrom-var-< k X Y T X<k
        | occurs-raise zero X (＇ Y) = refl

occurs-substVarFrom-<-ty :
  ∀ A k X T →
  X < k →
  occurs X (substᵗ (substVarFrom k T) A) ≡ occurs X A
occurs-substVarFrom-<-ty (＇ Y) k X T X<k =
  occurs-substVarFrom-var-< k X Y T X<k
occurs-substVarFrom-<-ty (｀ α) k X T X<k = refl
occurs-substVarFrom-<-ty (‵ ι) k X T X<k = refl
occurs-substVarFrom-<-ty ★ k X T X<k = refl
occurs-substVarFrom-<-ty (A ⇒ B) k X T X<k
  rewrite occurs-substVarFrom-<-ty A k X T X<k
        | occurs-substVarFrom-<-ty B k X T X<k = refl
occurs-substVarFrom-<-ty (`∀ A) k X T X<k =
  occurs-substVarFrom-<-ty A (suc k) (suc X) T (s<s X<k)

occurs-substVarFrom-< :
  ∀ k X T A →
  X < k →
  occurs X (substᵗ (substVarFrom k T) A) ≡ occurs X A
occurs-substVarFrom-< k X T A =
  occurs-substVarFrom-<-ty A k X T

renameˢ-ground : ∀{G : Ty} (ρ : Renameˢ)
  → Ground G
  → Ground (renameˢ ρ G)
renameˢ-ground ρ (｀ α) = ｀ (ρ α)
renameˢ-ground ρ (‵ ι) = ‵ ι
renameˢ-ground ρ ★⇒★ = ★⇒★

renameᵗ-ground-id :
  ∀ {ρ G} →
  Ground G →
  renameᵗ ρ G ≡ G
renameᵗ-ground-id (｀ α) = refl
renameᵗ-ground-id (‵ ι) = refl
renameᵗ-ground-id ★⇒★ = refl

ground-upper-unique-⊑ :
  ∀ {Ψ Γ A G H p q} →
  Ground G →
  Ground H →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ G →
  Ψ ∣ Γ ⊢ q ⦂ A ⊑ H →
  G ≡ H
ground-upper-unique-⊑ (｀ α) (｀ .α) (⊢α-⊑-α wfα) (⊢α-⊑-α wfβ) = refl
ground-upper-unique-⊑ (｀ α) (｀ β)
  (⊢∀A-⊑-B _ wfB p⊢) (⊢∀A-⊑-B _ wfB′ q⊢) =
  ground-upper-unique-⊑ (｀ α) (｀ β) p⊢ q⊢
ground-upper-unique-⊑ (｀ α) (‵ ι) (⊢α-⊑-α wfα) ()
ground-upper-unique-⊑ (｀ α) (‵ ι)
  (⊢∀A-⊑-B _ wfB p⊢) (⊢∀A-⊑-B _ wfB′ q⊢) =
  ground-upper-unique-⊑ (｀ α) (‵ ι) p⊢ q⊢
ground-upper-unique-⊑ (｀ α) ★⇒★ (⊢α-⊑-α wfα) ()
ground-upper-unique-⊑ (｀ α) ★⇒★
  (⊢∀A-⊑-B _ wfB p⊢) (⊢∀A-⊑-B _ wfB′ q⊢) =
  ground-upper-unique-⊑ (｀ α) ★⇒★ p⊢ q⊢
ground-upper-unique-⊑ (‵ ι) (｀ α) (⊢ι-⊑-ι) ()
ground-upper-unique-⊑ (‵ ι) (｀ α)
  (⊢∀A-⊑-B _ wfB p⊢) (⊢∀A-⊑-B _ wfB′ q⊢) =
  ground-upper-unique-⊑ (‵ ι) (｀ α) p⊢ q⊢
ground-upper-unique-⊑ (‵ ι) (‵ .ι) (⊢ι-⊑-ι) (⊢ι-⊑-ι) = refl
ground-upper-unique-⊑ (‵ ι) (‵ ι′)
  (⊢∀A-⊑-B _ wfB p⊢) (⊢∀A-⊑-B _ wfB′ q⊢) =
  ground-upper-unique-⊑ (‵ ι) (‵ ι′) p⊢ q⊢
ground-upper-unique-⊑ (‵ ι) ★⇒★ (⊢ι-⊑-ι) ()
ground-upper-unique-⊑ (‵ ι) ★⇒★
  (⊢∀A-⊑-B _ wfB p⊢) (⊢∀A-⊑-B _ wfB′ q⊢) =
  ground-upper-unique-⊑ (‵ ι) ★⇒★ p⊢ q⊢
ground-upper-unique-⊑ ★⇒★ (｀ α) (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) ()
ground-upper-unique-⊑ ★⇒★ (｀ α)
  (⊢∀A-⊑-B _ wfB p⊢) (⊢∀A-⊑-B _ wfB′ q⊢) =
  ground-upper-unique-⊑ ★⇒★ (｀ α) p⊢ q⊢
ground-upper-unique-⊑ ★⇒★ (‵ ι) (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) ()
ground-upper-unique-⊑ ★⇒★ (‵ ι)
  (⊢∀A-⊑-B _ wfB p⊢) (⊢∀A-⊑-B _ wfB′ q⊢) =
  ground-upper-unique-⊑ ★⇒★ (‵ ι) p⊢ q⊢
ground-upper-unique-⊑ ★⇒★ ★⇒★ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) (⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′) =
  refl
ground-upper-unique-⊑ ★⇒★ ★⇒★
  (⊢∀A-⊑-B _ wfB p⊢) (⊢∀A-⊑-B _ wfB′ q⊢) =
  ground-upper-unique-⊑ ★⇒★ ★⇒★ p⊢ q⊢

★⊑Ground-elim :
  ∀ {Ψ Γ G p} {A : Set} →
  Ground G →
  Ψ ∣ Γ ⊢ p ⦂ ★ ⊑ G →
  A
★⊑Ground-elim (｀ α) ()
★⊑Ground-elim (‵ ι) ()
★⊑Ground-elim ★⇒★ ()

＇⊑Ground-elim :
  ∀ {Ψ Γ X G p} {A : Set} →
  Ground G →
  Ψ ∣ Γ ⊢ p ⦂ ＇ X ⊑ G →
  A
＇⊑Ground-elim (｀ α) ()
＇⊑Ground-elim (‵ ι) ()
＇⊑Ground-elim ★⇒★ ()

ground-upper-unique-chain-non∀-⊑ :
  ∀ {Ψ Γ A B C G H p q r s} →
  Non∀ A →
  Ground G →
  Ground H →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ q ⦂ B ⊑ G →
  Ψ ∣ Γ ⊢ r ⦂ A ⊑ C →
  Ψ ∣ Γ ⊢ s ⦂ C ⊑ H →
  G ≡ H
ground-upper-unique-chain-non∀-⊑ non∀-＇ g h (⊢X-⊑-★ xν) q⊢ r⊢ s⊢ =
  ★⊑Ground-elim g q⊢
ground-upper-unique-chain-non∀-⊑ non∀-＇ g h (⊢A-⊑-★ g′ p⊢) q⊢ r⊢ s⊢ =
  ★⊑Ground-elim g q⊢
ground-upper-unique-chain-non∀-⊑ non∀-＇ g h (⊢X-⊑-X wfX) q⊢ r⊢ s⊢ =
  ＇⊑Ground-elim g q⊢
ground-upper-unique-chain-non∀-⊑ non∀-｀ g h (⊢A-⊑-★ g′ p⊢) q⊢ r⊢ s⊢ =
  ★⊑Ground-elim g q⊢
ground-upper-unique-chain-non∀-⊑
  non∀-｀ (｀ α) (｀ .α) (⊢α-⊑-α wfα) (⊢α-⊑-α wfα′)
  (⊢α-⊑-α wfα″) (⊢α-⊑-α wfα‴) = refl
ground-upper-unique-chain-non∀-⊑
  non∀-｀ (｀ α) (‵ ι) (⊢α-⊑-α wfα) (⊢α-⊑-α wfα′)
  (⊢α-⊑-α wfα″) ()
ground-upper-unique-chain-non∀-⊑
  non∀-｀ (｀ α) ★⇒★ (⊢α-⊑-α wfα) (⊢α-⊑-α wfα′)
  (⊢α-⊑-α wfα″) ()
ground-upper-unique-chain-non∀-⊑
  non∀-｀ g h (⊢α-⊑-α wfα) (⊢α-⊑-α wfα′) (⊢A-⊑-★ g′ r⊢) s⊢ =
  ★⊑Ground-elim h s⊢
ground-upper-unique-chain-non∀-⊑ non∀-‵ g h (⊢A-⊑-★ g′ p⊢) q⊢ r⊢ s⊢ =
  ★⊑Ground-elim g q⊢
ground-upper-unique-chain-non∀-⊑
  non∀-‵ (｀ α) h (⊢ι-⊑-ι) () r⊢ s⊢
ground-upper-unique-chain-non∀-⊑
  non∀-‵ (‵ ι) (｀ α) (⊢ι-⊑-ι) (⊢ι-⊑-ι) (⊢ι-⊑-ι) ()
ground-upper-unique-chain-non∀-⊑
  non∀-‵ (‵ ι) (‵ .ι) (⊢ι-⊑-ι) (⊢ι-⊑-ι) (⊢ι-⊑-ι) (⊢ι-⊑-ι) = refl
ground-upper-unique-chain-non∀-⊑
  non∀-‵ (‵ ι) ★⇒★ (⊢ι-⊑-ι) (⊢ι-⊑-ι) (⊢ι-⊑-ι) ()
ground-upper-unique-chain-non∀-⊑
  non∀-‵ ★⇒★ h (⊢ι-⊑-ι) () r⊢ s⊢
ground-upper-unique-chain-non∀-⊑
  non∀-‵ g h (⊢ι-⊑-ι) (⊢ι-⊑-ι) (⊢A-⊑-★ g′ r⊢) s⊢ =
  ★⊑Ground-elim h s⊢
ground-upper-unique-chain-non∀-⊑ non∀-★ g h ⊢★-⊑-★ q⊢ r⊢ s⊢ =
  ★⊑Ground-elim g q⊢
ground-upper-unique-chain-non∀-⊑ non∀-★ g h (⊢A-⊑-★ g′ p⊢) q⊢ r⊢ s⊢ =
  ★⊑Ground-elim g q⊢
ground-upper-unique-chain-non∀-⊑
  non∀-⇒ g h (⊢A-⊑-★ g′ p⊢) q⊢ r⊢ s⊢ =
  ★⊑Ground-elim g q⊢
ground-upper-unique-chain-non∀-⊑
  non∀-⇒ (｀ α) h (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) () r⊢ s⊢
ground-upper-unique-chain-non∀-⊑
  non∀-⇒ (‵ ι) h (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) () r⊢ s⊢
ground-upper-unique-chain-non∀-⊑
  non∀-⇒ ★⇒★ (｀ α) (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) (⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′)
  (⊢A⇒B-⊑-A′⇒B′ r⊢ s⊢) () 
ground-upper-unique-chain-non∀-⊑
  non∀-⇒ ★⇒★ (‵ ι) (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) (⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′)
  (⊢A⇒B-⊑-A′⇒B′ r⊢ s⊢) ()
ground-upper-unique-chain-non∀-⊑
  non∀-⇒ ★⇒★ ★⇒★ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) (⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′)
  (⊢A⇒B-⊑-A′⇒B′ r⊢ s⊢) (⊢A⇒B-⊑-A′⇒B′ r⊢′ s⊢′) = refl
ground-upper-unique-chain-non∀-⊑
  non∀-⇒ ★⇒★ h (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) (⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′)
  (⊢A-⊑-★ g′ r⊢) s⊢ =
  ★⊑Ground-elim h s⊢

------------------------------------------------------------------------
-- Well-formedness preserved by substitution
------------------------------------------------------------------------

WfTy-weakenˢ :
  ∀ {Δ Ψ Ψ′ A} →
  WfTy Δ Ψ A →
  Ψ ≤ Ψ′ →
  WfTy Δ Ψ′ A
WfTy-weakenˢ (wfVar X<Δ) Ψ≤Ψ′ = wfVar X<Δ
WfTy-weakenˢ (wfSeal α<Ψ) Ψ≤Ψ′ = wfSeal (<-≤-trans α<Ψ Ψ≤Ψ′)
WfTy-weakenˢ wfBase Ψ≤Ψ′ = wfBase
WfTy-weakenˢ wf★ Ψ≤Ψ′ = wf★
WfTy-weakenˢ (wf⇒ hA hB) Ψ≤Ψ′ =
  wf⇒ (WfTy-weakenˢ hA Ψ≤Ψ′) (WfTy-weakenˢ hB Ψ≤Ψ′)
WfTy-weakenˢ (wf∀ hA) Ψ≤Ψ′ =
  wf∀ (WfTy-weakenˢ hA Ψ≤Ψ′)

<-weaken+ :
  ∀ Δ {X k} →
  X < k →
  X < k + Δ
<-weaken+ Δ {k = zero} ()
<-weaken+ Δ {X = zero} {k = suc k} z<s = z<s
<-weaken+ Δ {X = suc X} {k = suc k} (s<s X<k) =
  s<s (<-weaken+ Δ X<k)

WfTy-weakenᵗ :
  ∀ k Δ {Ψ A} →
  WfTy k Ψ A →
  WfTy (k + Δ) Ψ A
WfTy-weakenᵗ k Δ (wfVar X<k) = wfVar (<-weaken+ Δ X<k)
WfTy-weakenᵗ k Δ (wfSeal α<Ψ) = wfSeal α<Ψ
WfTy-weakenᵗ k Δ wfBase = wfBase
WfTy-weakenᵗ k Δ wf★ = wf★
WfTy-weakenᵗ k Δ (wf⇒ wfA wfB) =
  wf⇒ (WfTy-weakenᵗ k Δ wfA) (WfTy-weakenᵗ k Δ wfB)
WfTy-weakenᵗ k Δ (wf∀ wfA) = wf∀ (WfTy-weakenᵗ (suc k) Δ wfA)

WfTy-closed-weakenᵗ :
  ∀ Δ {Ψ A} →
  WfTy 0 Ψ A →
  WfTy Δ Ψ A
WfTy-closed-weakenᵗ Δ wfA = WfTy-weakenᵗ zero Δ wfA

renameᵗ-inv-WfTy :
  ∀ {Δ Ψ A ρ} →
  (∀ {X} → ρ X < Δ → X < Δ) →
  WfTy Δ Ψ (renameᵗ ρ A) →
  WfTy Δ Ψ A
renameᵗ-inv-WfTy {A = ＇ X} hρ (wfVar ρX<Δ) = wfVar (hρ ρX<Δ)
renameᵗ-inv-WfTy {A = ｀ α} hρ (wfSeal α<Ψ) = wfSeal α<Ψ
renameᵗ-inv-WfTy {A = ‵ ι} hρ wfBase = wfBase
renameᵗ-inv-WfTy {A = ★} hρ wf★ = wf★
renameᵗ-inv-WfTy {A = A ⇒ B} hρ (wf⇒ wfA wfB) =
  wf⇒ (renameᵗ-inv-WfTy hρ wfA) (renameᵗ-inv-WfTy hρ wfB)
renameᵗ-inv-WfTy {A = `∀ A} hρ (wf∀ wfA) =
  wf∀ (renameᵗ-inv-WfTy h-ext wfA)
  where
    h-ext : ∀ {X} → extᵗ _ X < _ → X < _
    h-ext {zero} z<s = z<s
    h-ext {suc X} (s<s ρX<Δ) = s<s (hρ ρX<Δ)

TySubstWf : TyCtx → TyCtx → SealCtx → Substᵗ → Set
TySubstWf Δ Δ′ Ψ σ = ∀ {X} → X < Δ → WfTy Δ′ Ψ (σ X)

singleTyEnv-Wf :
  ∀ {Δ Ψ} (T : Ty) →
  WfTy Δ Ψ T →
  TySubstWf (suc Δ) Δ Ψ (singleTyEnv T)
singleTyEnv-Wf T wfT {zero} z<s = wfT
singleTyEnv-Wf T wfT {suc X} (s<s X<Δ) = wfVar X<Δ

TySubstWf-exts :
  ∀ {Δ Δ′ Ψ} {σ : Substᵗ} →
  TySubstWf Δ Δ′ Ψ σ →
  TySubstWf (suc Δ) (suc Δ′) Ψ (extsᵗ σ)
TySubstWf-exts hσ {zero} z<s = wfVar z<s
TySubstWf-exts hσ {suc X} (s<s X<Δ) =
  renameᵗ-preserves-WfTy (hσ X<Δ) TyRenameWf-suc

TySubstWf-liftˢ :
  ∀ {Δ Δ′ Ψ} {σ : Substᵗ} →
  TySubstWf Δ Δ′ Ψ σ →
  TySubstWf Δ Δ′ (suc Ψ) (liftSubstˢ σ)
TySubstWf-liftˢ hσ X<Δ =
  renameˢ-preserves-WfTy (hσ X<Δ) SealRenameWf-suc

substᵗ-preserves-WfTy :
  ∀ {Δ Δ′ Ψ} {σ : Substᵗ} {A : Ty} →
  WfTy Δ Ψ A →
  TySubstWf Δ Δ′ Ψ σ →
  WfTy Δ′ Ψ (substᵗ σ A)
substᵗ-preserves-WfTy (wfVar X<Δ) hσ = hσ X<Δ
substᵗ-preserves-WfTy (wfSeal α<Ψ) hσ = wfSeal α<Ψ
substᵗ-preserves-WfTy wfBase hσ = wfBase
substᵗ-preserves-WfTy wf★ hσ = wf★
substᵗ-preserves-WfTy (wf⇒ hA hB) hσ =
  wf⇒ (substᵗ-preserves-WfTy hA hσ) (substᵗ-preserves-WfTy hB hσ)
substᵗ-preserves-WfTy (wf∀ hA) hσ =
  wf∀ (substᵗ-preserves-WfTy hA (TySubstWf-exts hσ))

------------------------------------------------------------------------
-- Core renaming/substitution infrastructure
------------------------------------------------------------------------

substˢᵗ-cong :
  ∀
  {τ υ : Substˢᵗ} →
  ((α : Seal) → τ α ≡ υ α) →
  (A : Ty) →
  substˢᵗ τ A ≡ substˢᵗ υ A
substˢᵗ-cong h (＇ X) = refl
substˢᵗ-cong h (｀ α) = h α
substˢᵗ-cong h (‵ ι) = refl
substˢᵗ-cong h ★ = refl
substˢᵗ-cong h (A ⇒ B) =
  cong₂ _⇒_ (substˢᵗ-cong h A) (substˢᵗ-cong h B)
substˢᵗ-cong {τ = τ} {υ = υ} h (`∀ A) =
  cong `∀ (substˢᵗ-cong h-ext A)
  where
    h-ext : (α : Seal) → extsˢᵗ τ α ≡ extsˢᵗ υ α
    h-ext α = cong (renameᵗ suc) (h α)

substᵗ-substᵗ :
  ∀
  (σ : Substᵗ) (τ : Substᵗ) (A : Ty) →
  substᵗ σ (substᵗ τ A) ≡
  substᵗ (λ X → substᵗ σ (τ X)) A
substᵗ-substᵗ σ τ (＇ X) = refl
substᵗ-substᵗ σ τ (｀ α) = refl
substᵗ-substᵗ σ τ (‵ ι) = refl
substᵗ-substᵗ σ τ ★ = refl
substᵗ-substᵗ σ τ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-substᵗ σ τ A) (substᵗ-substᵗ σ τ B)
substᵗ-substᵗ σ τ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-substᵗ (extsᵗ σ) (extsᵗ τ) A)
      (substᵗ-cong env-eq A))
  where
    env-eq :
      (X : TyVar) →
      substᵗ (extsᵗ σ) (extsᵗ τ X) ≡
      extsᵗ (λ Y → substᵗ σ (τ Y)) X
    env-eq zero = refl
    env-eq (suc X) = substᵗ-suc-renameᵗ-suc σ (τ X)

------------------------------------------------------------------------
-- Seal commutation
------------------------------------------------------------------------

renameᵗ-renameˢ :
  ∀
  (ρ : Renameᵗ) (ϱ : Renameˢ) (A : Ty) →
  renameᵗ ρ (renameˢ ϱ A) ≡ renameˢ ϱ (renameᵗ ρ A)
renameᵗ-renameˢ ρ ϱ (＇ X) = refl
renameᵗ-renameˢ ρ ϱ (｀ α) = refl
renameᵗ-renameˢ ρ ϱ (‵ ι) = refl
renameᵗ-renameˢ ρ ϱ ★ = refl
renameᵗ-renameˢ ρ ϱ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-renameˢ ρ ϱ A) (renameᵗ-renameˢ ρ ϱ B)
renameᵗ-renameˢ ρ ϱ (`∀ A) =
  cong `∀ (renameᵗ-renameˢ (extᵗ ρ) ϱ A)

renameˢ-substᵗ :
  ∀
  (ρ : Renameˢ) (σ : Substᵗ) (A : Ty) →
  renameˢ ρ (substᵗ σ A) ≡
  substᵗ (λ X → renameˢ ρ (σ X)) (renameˢ ρ A)
renameˢ-substᵗ ρ σ (＇ X) = refl
renameˢ-substᵗ ρ σ (｀ α) = refl
renameˢ-substᵗ ρ σ (‵ ι) = refl
renameˢ-substᵗ ρ σ ★ = refl
renameˢ-substᵗ ρ σ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-substᵗ ρ σ A) (renameˢ-substᵗ ρ σ B)
renameˢ-substᵗ ρ σ (`∀ A) =
  cong `∀
    (trans
      (renameˢ-substᵗ ρ (extsᵗ σ) A)
      (substᵗ-cong env-eq (renameˢ ρ A)))
  where
    env-eq :
      (X : TyVar) →
      renameˢ ρ (extsᵗ σ X) ≡ extsᵗ (λ Y → renameˢ ρ (σ Y)) X
    env-eq zero = refl
    env-eq (suc X) = sym (renameᵗ-renameˢ suc ρ (σ X))

inst★-renameᵗ-suc :
  ∀ (A : Ty) →
  (renameᵗ suc A) [ ★ ]ᵗ ≡ A
inst★-renameᵗ-suc A =
  trans
    (substᵗ-renameᵗ suc (singleTyEnv ★) A)
    (trans
      (substᵗ-cong (λ X → refl) A)
      (substᵗ-id A))

renameᵗ-inst★ :
  ∀
  (ρ : Renameᵗ) (A : Ty) →
  renameᵗ ρ (A [ ★ ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ ★ ]ᵗ
renameᵗ-inst★ ρ A =
  trans
    (renameᵗ-substᵗ ρ (singleTyEnv ★) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-renameᵗ (extᵗ ρ) (singleTyEnv ★) A)))
  where
    env :
      (X : TyVar) →
      renameᵗ ρ (singleTyEnv ★ X) ≡
      singleTyEnv ★ (extᵗ ρ X)
    env zero = refl
    env (suc X) = refl

substᵗ-inst★ :
  ∀
  (σ : Substᵗ) (A : Ty) →
  substᵗ σ (A [ ★ ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ ★ ]ᵗ
substᵗ-inst★ σ A =
  trans
    (substᵗ-substᵗ σ (singleTyEnv ★) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ (singleTyEnv ★) (extsᵗ σ) A)))
  where
    env :
      (X : TyVar) →
      substᵗ σ (singleTyEnv ★ X) ≡ substᵗ (singleTyEnv ★) (extsᵗ σ X)
    env zero = refl
    env (suc X) = sym (inst★-renameᵗ-suc (σ X))

renameˢ-inst★ :
  ∀
  (ρ : Renameˢ) (A : Ty) →
  renameˢ ρ (A [ ★ ]ᵗ) ≡ (renameˢ ρ A) [ ★ ]ᵗ
renameˢ-inst★ ρ A =
  trans
    (renameˢ-substᵗ ρ (singleTyEnv ★) A)
    (substᵗ-cong env (renameˢ ρ A))
  where
    env :
      (X : TyVar) →
      renameˢ ρ (singleTyEnv ★ X) ≡ singleTyEnv ★ X
    env zero = refl
    env (suc X) = refl

------------------------------------------------------------------------
-- Commuting with seal lifting/opening and contexts
------------------------------------------------------------------------

renameᵗ-[]ᵗ-seal :
  ∀
  (ρ : Renameᵗ) (A : Ty) (α : Seal) →
  renameᵗ ρ (A [ ｀ α ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ ｀ α ]ᵗ
renameᵗ-[]ᵗ-seal ρ A α =
  trans
    (renameᵗ-substᵗ ρ (singleTyEnv (｀ α)) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-renameᵗ (extᵗ ρ) (singleTyEnv (｀ α)) A)))
  where
    env :
      (X : TyVar) →
      renameᵗ ρ (singleTyEnv (｀ α) X) ≡
      singleTyEnv (｀ α) (extᵗ ρ X)
    env zero = refl
    env (suc X) = refl

substᵗ-[]ᵗ-seal :
  ∀
  (σ : Substᵗ) (A : Ty) (α : Seal) →
  substᵗ σ (A [ ｀ α ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ ｀ α ]ᵗ
substᵗ-[]ᵗ-seal σ A α =
  trans
    (substᵗ-substᵗ σ (singleTyEnv (｀ α)) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ (singleTyEnv (｀ α)) (extsᵗ σ) A)))
  where
    env :
      (X : TyVar) →
      substᵗ σ (singleTyEnv (｀ α) X) ≡
      substᵗ (singleTyEnv (｀ α)) (extsᵗ σ X)
    env zero = refl
    env (suc X) = sym (open-renᵗ-suc (σ X) (｀ α))

renameˢ-[]ᵗ-seal :
  ∀
  (ρ : Renameˢ) (A : Ty) (α : Seal) →
  renameˢ ρ (A [ ｀ α ]ᵗ) ≡ (renameˢ ρ A) [ ｀ (ρ α) ]ᵗ
renameˢ-[]ᵗ-seal ρ A α =
  trans
    (renameˢ-substᵗ ρ (singleTyEnv (｀ α)) A)
    (substᵗ-cong env (renameˢ ρ A))
  where
    env :
      (X : TyVar) →
      renameˢ ρ (singleTyEnv (｀ α) X) ≡
      singleTyEnv (｀ (ρ α)) X
    env zero = refl
    env (suc X) = refl

renameᵗ-ν-src :
  ∀  (ρ : Renameᵗ) (A : Ty) →
  renameᵗ ρ ((⇑ˢ A) [ α₀ ]ᵗ) ≡
  (⇑ˢ (renameᵗ (extᵗ ρ) A)) [ α₀ ]ᵗ
renameᵗ-ν-src ρ A =
  trans
    (renameᵗ-[]ᵗ-seal ρ (⇑ˢ A) zero)
    (cong (λ C → C [ α₀ ]ᵗ) (renameᵗ-⇑ˢ (extᵗ ρ) A))

private
  exts-liftSubstˢ :
    ∀
    (σ : Substᵗ) (X : TyVar) →
    extsᵗ (liftSubstˢ σ) X ≡ liftSubstˢ (extsᵗ σ) X
  exts-liftSubstˢ σ zero = refl
  exts-liftSubstˢ σ (suc X) = renameᵗ-⇑ˢ suc (σ X)

substᵗ-ν-src :
  ∀  (σ : Substᵗ) (A : Ty) →
  substᵗ (liftSubstˢ σ) ((⇑ˢ A) [ α₀ ]ᵗ) ≡
  (⇑ˢ (substᵗ (extsᵗ σ) A)) [ α₀ ]ᵗ
substᵗ-ν-src σ A =
  trans
    (substᵗ-[]ᵗ-seal (liftSubstˢ σ) (⇑ˢ A) zero)
    (cong
      (λ C → C [ α₀ ]ᵗ)
      (trans
        (substᵗ-cong (exts-liftSubstˢ σ) (⇑ˢ A))
        (substᵗ-⇑ˢ (extsᵗ σ) A)))

renameˢ-ν-src :
  ∀  (ρ : Renameˢ) (A : Ty) →
  renameˢ (extˢ ρ) ((⇑ˢ A) [ α₀ ]ᵗ) ≡
  (⇑ˢ (renameˢ ρ A)) [ α₀ ]ᵗ
renameˢ-ν-src ρ A =
  trans
    (renameˢ-[]ᵗ-seal (extˢ ρ) (⇑ˢ A) 0)
    (cong (λ C → C [ α₀ ]ᵗ) (renameˢ-ext-⇑ˢ ρ A))

