module proof.ImprecisionModeWeakening where

-- File Charter:
--   * Weakens one-context narrowing and widening along mode inclusion.
--   * Provides the inclusion from an ordinary binder to a generated binder.

open import Data.Bool using (true)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import Coercions
open import NarrowWiden

record ModeIncl (mu nu : ModeEnv) : Set where
  constructor mode-incl
  field
    tag-incl : forall G
      -> tagAllowed mu G ≡ true
      -> tagAllowed nu G ≡ true
    seal-incl : forall X
      -> sealModeAllowed (mu X) ≡ true
      -> sealModeAllowed (nu X) ≡ true

open ModeIncl

ext-tag-var-incl : forall {mu nu} X
  -> ModeIncl mu nu
  -> tagAllowed (extᵈ mu) (＇ X) ≡ true
  -> tagAllowed (extᵈ nu) (＇ X) ≡ true
ext-tag-var-incl zero incl ()
ext-tag-var-incl (suc X) incl allowed = tag-incl incl (＇ X) allowed

ext-tag-incl : forall {mu nu} G
  -> ModeIncl mu nu
  -> tagAllowed (extᵈ mu) G ≡ true
  -> tagAllowed (extᵈ nu) G ≡ true
ext-tag-incl (＇ X) incl allowed = ext-tag-var-incl X incl allowed
ext-tag-incl (‵ iota) incl allowed = refl
ext-tag-incl ★⇒★ incl allowed = refl

ext-seal-incl : forall {mu nu} X
  -> ModeIncl mu nu
  -> sealModeAllowed (extᵈ mu X) ≡ true
  -> sealModeAllowed (extᵈ nu X) ≡ true
ext-seal-incl zero incl ()
ext-seal-incl (suc X) incl allowed = seal-incl incl X allowed

ext-incl : forall {mu nu}
  -> ModeIncl mu nu
  -> ModeIncl (extᵈ mu) (extᵈ nu)
ext-incl incl =
  mode-incl (λ G → ext-tag-incl G incl) (λ X → ext-seal-incl X incl)

gen-tag-var-incl : forall {mu nu} X
  -> ModeIncl mu nu
  -> tagAllowed (genᵈ mu) (＇ X) ≡ true
  -> tagAllowed (genᵈ nu) (＇ X) ≡ true
gen-tag-var-incl zero incl allowed = refl
gen-tag-var-incl (suc X) incl allowed = tag-incl incl (＇ X) allowed

gen-tag-incl : forall {mu nu} G
  -> ModeIncl mu nu
  -> tagAllowed (genᵈ mu) G ≡ true
  -> tagAllowed (genᵈ nu) G ≡ true
gen-tag-incl (＇ X) incl allowed = gen-tag-var-incl X incl allowed
gen-tag-incl (‵ iota) incl allowed = refl
gen-tag-incl ★⇒★ incl allowed = refl

gen-seal-incl : forall {mu nu} X
  -> ModeIncl mu nu
  -> sealModeAllowed (genᵈ mu X) ≡ true
  -> sealModeAllowed (genᵈ nu X) ≡ true
gen-seal-incl zero incl ()
gen-seal-incl (suc X) incl allowed = seal-incl incl X allowed

gen-incl : forall {mu nu}
  -> ModeIncl mu nu
  -> ModeIncl (genᵈ mu) (genᵈ nu)
gen-incl incl =
  mode-incl (λ G → gen-tag-incl G incl) (λ X → gen-seal-incl X incl)

inst-tag-var-incl : forall {mu nu} X
  -> ModeIncl mu nu
  -> tagAllowed (instᵈ mu) (＇ X) ≡ true
  -> tagAllowed (instᵈ nu) (＇ X) ≡ true
inst-tag-var-incl zero incl ()
inst-tag-var-incl (suc X) incl allowed = tag-incl incl (＇ X) allowed

inst-tag-incl : forall {mu nu} G
  -> ModeIncl mu nu
  -> tagAllowed (instᵈ mu) G ≡ true
  -> tagAllowed (instᵈ nu) G ≡ true
inst-tag-incl (＇ X) incl allowed = inst-tag-var-incl X incl allowed
inst-tag-incl (‵ iota) incl allowed = refl
inst-tag-incl ★⇒★ incl allowed = refl

inst-seal-incl : forall {mu nu} X
  -> ModeIncl mu nu
  -> sealModeAllowed (instᵈ mu X) ≡ true
  -> sealModeAllowed (instᵈ nu X) ≡ true
inst-seal-incl zero incl allowed = refl
inst-seal-incl (suc X) incl allowed = seal-incl incl X allowed

inst-incl : forall {mu nu}
  -> ModeIncl mu nu
  -> ModeIncl (instᵈ mu) (instᵈ nu)
inst-incl incl =
  mode-incl (λ G → inst-tag-incl G incl) (λ X → inst-seal-incl X incl)

ext-gen-tag-var-incl : forall {mu} X
  -> tagAllowed (extᵈ mu) (＇ X) ≡ true
  -> tagAllowed (genᵈ mu) (＇ X) ≡ true
ext-gen-tag-var-incl zero ()
ext-gen-tag-var-incl (suc X) allowed = allowed

ext-gen-tag-incl : forall {mu} G
  -> tagAllowed (extᵈ mu) G ≡ true
  -> tagAllowed (genᵈ mu) G ≡ true
ext-gen-tag-incl (＇ X) allowed = ext-gen-tag-var-incl X allowed
ext-gen-tag-incl (‵ iota) allowed = refl
ext-gen-tag-incl ★⇒★ allowed = refl

ext-gen-seal-incl : forall {mu} X
  -> sealModeAllowed (extᵈ mu X) ≡ true
  -> sealModeAllowed (genᵈ mu X) ≡ true
ext-gen-seal-incl zero ()
ext-gen-seal-incl (suc X) allowed = allowed

ext-gen-incl : forall {mu} -> ModeIncl (extᵈ mu) (genᵈ mu)
ext-gen-incl = mode-incl ext-gen-tag-incl ext-gen-seal-incl

ext-inst-tag-incl : forall {mu} G
  -> tagAllowed (extᵈ mu) G ≡ true
  -> tagAllowed (instᵈ mu) G ≡ true
ext-inst-tag-incl (＇ zero) ()
ext-inst-tag-incl (＇ suc X) allowed = allowed
ext-inst-tag-incl (‵ iota) allowed = refl
ext-inst-tag-incl ★⇒★ allowed = refl

ext-inst-seal-incl : forall {mu} X
  -> sealModeAllowed (extᵈ mu X) ≡ true
  -> sealModeAllowed (instᵈ mu X) ≡ true
ext-inst-seal-incl zero ()
ext-inst-seal-incl (suc X) allowed = allowed

ext-inst-incl : forall {mu} -> ModeIncl (extᵈ mu) (instᵈ mu)
ext-inst-incl = mode-incl ext-inst-tag-incl ext-inst-seal-incl

mutual

  weakenʷ : forall {mu nu Delta Sigma c A B}
    -> ModeIncl mu nu
    -> mu ∣ Delta ∣ Sigma ⊢ c ⦂ A ⊑ B
    -> nu ∣ Delta ∣ Sigma ⊢ c ⦂ A ⊑ B
  weakenʷ incl (idᵃ a hA) = idᵃ a hA
  weakenʷ incl (p ↦ q) = weakenⁿ incl p ↦ weakenʷ incl q
  weakenʷ incl (∀ʷ p) = ∀ʷ (weakenʷ (ext-incl incl) p)
  weakenʷ incl (tag G hG allowed G⍉A) =
    tag G hG (tag-incl incl G allowed) G⍉A
  weakenʷ incl (tag-seq G p hG allowed G⍉B nonvarA A≠B) =
    tag-seq G (weakenʷ incl p) hG (tag-incl incl G allowed)
      G⍉B nonvarA A≠B
  weakenʷ incl (unseal {X = X} X<Delta hA X,A∈Sigma allowed) =
    unseal X<Delta hA X,A∈Sigma (seal-incl incl X allowed)
  weakenʷ incl (unseal-seq {X = X} X<Delta X,A∈Sigma allowed p A≠B) =
    unseal-seq X<Delta X,A∈Sigma (seal-incl incl X allowed)
      (weakenʷ incl p) A≠B
  weakenʷ incl (inst nonvarA zero∈A hB p B≠★) =
    inst nonvarA zero∈A hB (weakenʷ (inst-incl incl) p) B≠★

  weakenⁿ : forall {mu nu Delta Sigma c A B}
    -> ModeIncl mu nu
    -> mu ∣ Delta ∣ Sigma ⊢ c ⦂ A ⊒ B
    -> nu ∣ Delta ∣ Sigma ⊢ c ⦂ A ⊒ B
  weakenⁿ incl (idᵃ a hA) = idᵃ a hA
  weakenⁿ incl (p ↦ q) = weakenʷ incl p ↦ weakenⁿ incl q
  weakenⁿ incl (∀ⁿ p) = ∀ⁿ (weakenⁿ (ext-incl incl) p)
  weakenⁿ incl (untag G hG allowed G⍉B) =
    untag G hG (tag-incl incl G allowed) G⍉B
  weakenⁿ incl (untag-seq G hG allowed G⍉A p nonvarB A≠B) =
    untag-seq G hG (tag-incl incl G allowed) G⍉A
      (weakenⁿ incl p) nonvarB A≠B
  weakenⁿ incl (seal {X = X} X<Delta hA X,A∈Sigma allowed) =
    seal X<Delta hA X,A∈Sigma (seal-incl incl X allowed)
  weakenⁿ incl (seal-seq {X = X} p X<Delta X,B∈Sigma allowed A≠B) =
    seal-seq (weakenⁿ incl p) X<Delta X,B∈Sigma
      (seal-incl incl X allowed) A≠B
  weakenⁿ incl (gen nonvarA zero∈A hB p B≠★) =
    gen nonvarA zero∈A hB (weakenⁿ (gen-incl incl) p) B≠★

weakenʷ-bundle : forall {mu nu Delta Sigma A B}
  -> ModeIncl mu nu
  -> mu ∣ Delta ∣ Sigma ⊢ A ⊑ B
  -> nu ∣ Delta ∣ Sigma ⊢ A ⊑ B
weakenʷ-bundle incl (c , c⊑) = c , weakenʷ incl c⊑

weakenⁿ-bundle : forall {mu nu Delta Sigma A B}
  -> ModeIncl mu nu
  -> mu ∣ Delta ∣ Sigma ⊢ A ⊒ B
  -> nu ∣ Delta ∣ Sigma ⊢ A ⊒ B
weakenⁿ-bundle incl (c , c⊒) = c , weakenⁿ incl c⊒
