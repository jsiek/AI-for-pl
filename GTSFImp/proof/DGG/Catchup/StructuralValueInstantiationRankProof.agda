module proof.DGG.Catchup.StructuralValueInstantiationRankProof where

-- File Charter:
--   * Proves preservation and descent facts for the internal
--     structural-instantiation administrative rank.
--   * Supplies the lexicographic accessibility relation used by the
--     structural named-instantiation worker.
--   * Keeps rank arithmetic separate from relation replay code.

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_; _*_; _^_)
open import Data.Nat.Properties using
  (m≤m+n; ≤-trans; +-assoc; +-identityʳ; +-monoʳ-<; m<n+m;
   n<1+n; <-trans)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans)
  renaming (subst to subst≡)

open import Types using (Ty; TyVar; ＇_; _[_]ᵗ; ⇑ᵗ)
open import Consistency using (_↪ᵗ_; wk↪ᵗ; keep)
open import Conversion using (Conv↑; Conv↓; 〖_,_↑_〗)
open import Reduction using (StoreChange; keep; bind; applyBody)
import CastTerms as CT
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralValueInstantiationRankDef

open +-*-Solver using (solve; _:+_; _:*_; con)
  renaming (_:=_ to _:=ᵉ_)


cong₃ : ∀ {a b c d e f : ℕ}
    (F : ℕ → ℕ → ℕ → InstantiationRank)
  → a ≡ b
  → c ≡ d
  → e ≡ f
  → F a c e ≡ F b d f
cong₃ F refl refl refl = refl


data _<ʳ_ : InstantiationRank → InstantiationRank → Set where
  rank-name< : ∀ {n n′ e e′ l l′}
    → n < n′
    → inst-rank n e l <ʳ inst-rank n′ e′ l′

  rank-exp< : ∀ {n n′ e e′ l l′}
    → n ≡ n′
    → e < e′
    → inst-rank n e l <ʳ inst-rank n′ e′ l′

  rank-length< : ∀ {n n′ e e′ l l′}
    → n ≡ n′
    → e ≡ e′
    → l < l′
    → inst-rank n e l <ʳ inst-rank n′ e′ l′


pow3-positive : ∀ n → 1 ≤ 3 ^ n
pow3-positive zero = Nat.s≤s Nat.z≤n
pow3-positive (suc n) =
  ≤-trans (pow3-positive n)
    (m≤m+n (3 ^ n) (2 * 3 ^ n))


two-generated-frames-decrease : ∀ n p
  → 3 ^ n + (3 ^ n + p) <
      3 ^ n + (3 ^ n + (3 ^ n + p))
two-generated-frames-decrease n p =
  m<n+m (3 ^ n + (3 ^ n + p)) (pow3-positive n)


parent-wrapper-potential-normalize : ∀ w n p
  → suc w * 3 ^ suc n + p ≡
      w * 3 ^ suc n + (3 ^ n + (3 ^ n + (3 ^ n + p)))
parent-wrapper-potential-normalize w n p = solve 3
  (λ w a p →
    ((con 1 :+ w) :* (a :+ (a :+ (a :+ con 0))) :+ p) :=ᵉ
    (w :* (a :+ (a :+ (a :+ con 0))) :+
      (a :+ (a :+ (a :+ p)))))
  refl w (3 ^ n) p


conversion-wrapper-expansion-decreases : ∀ w n p
  → w * 3 ^ suc n + (3 ^ n + (3 ^ n + p)) <
      suc w * 3 ^ suc n + p
conversion-wrapper-expansion-decreases w n p =
  subst≡
    (λ q → w * 3 ^ suc n + (3 ^ n + (3 ^ n + p)) < q)
    (sym (parent-wrapper-potential-normalize w n p))
    (+-monoʳ-< (w * 3 ^ suc n)
      (two-generated-frames-decrease n p))


frame-wrapper-potential-same : ∀ w n p
  → suc w * 3 ^ n + p ≡ w * 3 ^ n + (3 ^ n + p)
frame-wrapper-potential-same w n p = solve 3
  (λ w a p →
    ((con 1 :+ w) :* a :+ p) :=ᵉ
    (w :* a :+ (a :+ p)))
  refl w (3 ^ n) p


frame-potential-decreases : ∀ w n p
  → w * 3 ^ n + p < w * 3 ^ n + (3 ^ n + p)
frame-potential-decreases w n p =
  +-monoʳ-< (w * 3 ^ n) (m<n+m p (pow3-positive n))


conceal-reveal-potential-normalize : ∀ w n p
  → suc w * 3 ^ n + (3 ^ n + p) ≡
      w * 3 ^ n + (3 ^ n + (3 ^ n + p))
conceal-reveal-potential-normalize w n p = solve 3
  (λ w a p →
    ((con 1 :+ w) :* a :+ (a :+ p)) :=ᵉ
    (w :* a :+ (a :+ (a :+ p))))
  refl w (3 ^ n) p


conceal-reveal-potential-decreases : ∀ w n p
  → w * 3 ^ n + p < suc w * 3 ^ n + (3 ^ n + p)
conceal-reveal-potential-decreases w n p =
  subst≡
    (λ q → w * 3 ^ n + p < q)
    (sym (conceal-reveal-potential-normalize w n p))
    (+-monoʳ-< (w * 3 ^ n)
      (<-trans
        (m<n+m p (pow3-positive n))
        (m<n+m (3 ^ n + p) (pow3-positive n))))


value-conversion-units-rename : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′)
    {V : CT.Term Δ} (vV : CT.Value V)
  → valueConversionUnits (renameᵗᵐ-preserves-Value ρ vV) ≡
      valueConversionUnits vV
value-conversion-units-rename ρ (CT.ƛ N) = refl
value-conversion-units-rename ρ (CT.Λ vV) =
  value-conversion-units-rename (keep ρ) vV
value-conversion-units-rename ρ (CT.$ k) = refl
value-conversion-units-rename ρ (vV CT.《 CT.inj 》) =
  value-conversion-units-rename ρ vV
value-conversion-units-rename ρ (vV CT.《 CT.fun 》) =
  value-conversion-units-rename ρ vV
value-conversion-units-rename ρ (vV CT.《 CT.all 》) =
  value-conversion-units-rename ρ vV
value-conversion-units-rename ρ (vV CT.《 CT.genᵥ A≠★ safe 》) =
  value-conversion-units-rename ρ vV
value-conversion-units-rename ρ (vV CT.↑ CT.fun) =
  cong suc (value-conversion-units-rename ρ vV)
value-conversion-units-rename ρ (vV CT.↑ CT.all) =
  cong suc (value-conversion-units-rename ρ vV)
value-conversion-units-rename ρ (vV CT.↓ CT.seal) =
  cong suc (value-conversion-units-rename ρ vV)
value-conversion-units-rename ρ (vV CT.↓ CT.fun) =
  cong suc (value-conversion-units-rename ρ vV)
value-conversion-units-rename ρ (vV CT.↓ CT.all) =
  cong suc (value-conversion-units-rename ρ vV)


value-conversion-units-irrel : ∀ {Δ} {V : CT.Term Δ}
  → (v₁ v₂ : CT.Value V)
  → valueConversionUnits v₁ ≡ valueConversionUnits v₂
value-conversion-units-irrel (CT.ƛ N) (CT.ƛ N′) = refl
value-conversion-units-irrel (CT.Λ v₁) (CT.Λ v₂) =
  value-conversion-units-irrel v₁ v₂
value-conversion-units-irrel (CT.$ k) (CT.$ k′) = refl
value-conversion-units-irrel (v₁ CT.《 inert₁ 》) (v₂ CT.《 inert₂ 》) =
  value-conversion-units-irrel v₁ v₂
value-conversion-units-irrel (v₁ CT.↑ rv₁) (v₂ CT.↑ rv₂) =
  cong suc (value-conversion-units-irrel v₁ v₂)
value-conversion-units-irrel (v₁ CT.↓ cv₁) (v₂ CT.↓ cv₂) =
  cong suc (value-conversion-units-irrel v₁ v₂)


nameFrames-map : ∀ {Δ Δ′ A B}
    (χ : StoreChange Δ Δ′) (spine : InstantiationSpine A B)
  → nameFrames (mapInstantiationSpine χ spine) ≡ nameFrames spine
nameFrames-map χ []ⁱ = refl
nameFrames-map χ (type-transport-frame eq ▻ⁱ spine) =
  nameFrames-map χ spine
nameFrames-map keep (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  cong suc (nameFrames-map keep spine)
nameFrames-map (bind R) (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  cong suc (nameFrames-map (bind R) spine)
nameFrames-map keep (cast-frame c ▻ⁱ spine) =
  nameFrames-map keep spine
nameFrames-map (bind R) (cast-frame c ▻ⁱ spine) =
  nameFrames-map (bind R) spine
nameFrames-map keep (reveal-frame c ▻ⁱ spine) =
  nameFrames-map keep spine
nameFrames-map (bind R) (reveal-frame c ▻ⁱ spine) =
  nameFrames-map (bind R) spine
nameFrames-map keep (conceal-frame c ▻ⁱ spine) =
  nameFrames-map keep spine
nameFrames-map (bind R) (conceal-frame c ▻ⁱ spine) =
  nameFrames-map (bind R) spine


spine-conversion-potential-map : ∀ {Δ Δ′ A B}
    (χ : StoreChange Δ Δ′) (spine : InstantiationSpine A B)
  → spineConversionPotential (mapInstantiationSpine χ spine) ≡
      spineConversionPotential spine
spine-conversion-potential-map χ []ⁱ = refl
spine-conversion-potential-map χ
    (type-transport-frame eq ▻ⁱ spine) =
  spine-conversion-potential-map χ spine
spine-conversion-potential-map keep
    (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  spine-conversion-potential-map keep spine
spine-conversion-potential-map (bind R)
    (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  spine-conversion-potential-map (bind R) spine
spine-conversion-potential-map keep (cast-frame c ▻ⁱ spine) =
  spine-conversion-potential-map keep spine
spine-conversion-potential-map (bind R) (cast-frame c ▻ⁱ spine) =
  spine-conversion-potential-map (bind R) spine
spine-conversion-potential-map keep (reveal-frame c ▻ⁱ spine)
    rewrite nameFrames-map keep spine
          | spine-conversion-potential-map keep spine =
  refl
spine-conversion-potential-map (bind R) (reveal-frame c ▻ⁱ spine)
    rewrite nameFrames-map (bind R) spine
          | spine-conversion-potential-map (bind R) spine =
  refl
spine-conversion-potential-map keep (conceal-frame c ▻ⁱ spine)
    rewrite nameFrames-map keep spine
          | spine-conversion-potential-map keep spine =
  refl
spine-conversion-potential-map (bind R) (conceal-frame c ▻ⁱ spine)
    rewrite nameFrames-map (bind R) spine
          | spine-conversion-potential-map (bind R) spine =
  refl


spineLength-map : ∀ {Δ Δ′ A B}
    (χ : StoreChange Δ Δ′) (spine : InstantiationSpine A B)
  → spineLength (mapInstantiationSpine χ spine) ≡ spineLength spine
spineLength-map χ []ⁱ = refl
spineLength-map χ (type-transport-frame eq ▻ⁱ spine) =
  cong suc (spineLength-map χ spine)
spineLength-map keep (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  cong suc (spineLength-map keep spine)
spineLength-map (bind R) (name-type-app-frame B X eqA eqC ▻ⁱ spine) =
  cong suc (spineLength-map (bind R) spine)
spineLength-map keep (cast-frame c ▻ⁱ spine) =
  cong suc (spineLength-map keep spine)
spineLength-map (bind R) (cast-frame c ▻ⁱ spine) =
  cong suc (spineLength-map (bind R) spine)
spineLength-map keep (reveal-frame c ▻ⁱ spine) =
  cong suc (spineLength-map keep spine)
spineLength-map (bind R) (reveal-frame c ▻ⁱ spine) =
  cong suc (spineLength-map (bind R) spine)
spineLength-map keep (conceal-frame c ▻ⁱ spine) =
  cong suc (spineLength-map keep spine)
spineLength-map (bind R) (conceal-frame c ▻ⁱ spine) =
  cong suc (spineLength-map (bind R) spine)


expPotential-map-rename : ∀ {Δ Δ′ A B V}
    (χ : StoreChange Δ Δ′) (ρ : Δ ↪ᵗ Δ′)
    (vV : CT.Value V) (spine : InstantiationSpine A B)
  → expPotential (renameᵗᵐ-preserves-Value ρ vV)
      (mapInstantiationSpine χ spine) ≡
      expPotential vV spine
expPotential-map-rename χ ρ vV spine
    rewrite value-conversion-units-rename ρ vV
          | nameFrames-map χ spine
          | spine-conversion-potential-map χ spine =
  refl


rank-map-rename : ∀ {Δ Δ′ A B V}
    (χ : StoreChange Δ Δ′) (ρ : Δ ↪ᵗ Δ′)
    (vV : CT.Value V) (spine : InstantiationSpine A B)
  → pendingRank (renameᵗᵐ-preserves-Value ρ vV)
      (mapInstantiationSpine χ spine) ≡ pendingRank vV spine
rank-map-rename χ ρ vV spine =
  cong₃ inst-rank (nameFrames-map χ spine)
    (expPotential-map-rename χ ρ vV spine)
    (spineLength-map χ spine)


lambda-rank-decreases : ∀ {Δ} {B : Ty (suc Δ)}
    {E : Ty Δ} {V : CT.Term (suc Δ)} {X : TyVar Δ}
    (vV : CT.Value V)
    (vChild : CT.Value
      (V CT.↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗))
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → pendingRank vChild
      (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
      <ʳ
      pendingRank (CT.Λ vV)
        (name-type-app-frame B X refl refl ▻ⁱ spine)
lambda-rank-decreases {X = X} vV vChild spine
    rewrite nameFrames-map (bind (＇ X)) spine =
  rank-name< (n<1+n (nameFrames spine))


reveal-rank-decreases : ∀ {Δ} {B C : Ty (suc Δ)}
    {E : Ty Δ} {V : CT.Term Δ} {X : TyVar Δ}
    {c : Conv↑ (suc Δ) C B}
    (vV : CT.Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → pendingRank (renameᵗᵐ-preserves-Value wk↪ᵗ vV)
      (name-type-app-frame (applyBody (bind (＇ X)) C)
          Fin.zero refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        reveal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
      <ʳ
      pendingRank (vV CT.↑ CT.all {c = c})
        (name-type-app-frame B X refl refl ▻ⁱ spine)
reveal-rank-decreases {X = X} vV spine
    rewrite value-conversion-units-rename wk↪ᵗ vV
          | nameFrames-map (bind (＇ X)) spine
          | spine-conversion-potential-map (bind (＇ X)) spine =
  rank-exp< refl
    (conversion-wrapper-expansion-decreases
      (valueConversionUnits vV)
      (nameFrames spine)
      (spineConversionPotential spine))


conceal-rank-decreases : ∀ {Δ} {B C : Ty (suc Δ)}
    {E : Ty Δ} {V : CT.Term Δ} {X : TyVar Δ}
    {c : Conv↓ (suc Δ) C B}
    (vV : CT.Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → pendingRank (renameᵗᵐ-preserves-Value wk↪ᵗ vV)
      (name-type-app-frame (applyBody (bind (＇ X)) C)
          Fin.zero refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        conceal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
      <ʳ
      pendingRank (vV CT.↓ CT.all {c = c})
        (name-type-app-frame B X refl refl ▻ⁱ spine)
conceal-rank-decreases {X = X} vV spine
    rewrite value-conversion-units-rename wk↪ᵗ vV
          | nameFrames-map (bind (＇ X)) spine
          | spine-conversion-potential-map (bind (＇ X)) spine =
  rank-exp< refl
    (conversion-wrapper-expansion-decreases
      (valueConversionUnits vV)
      (nameFrames spine)
      (spineConversionPotential spine))


cast-frame-rank-decreases : ∀ {Δ A B E V μ}
    {c : μ Consistency.⊢ A ∼ B}
    (vV : CT.Value {Δ = Δ} V) (inert : CT.Inert c)
    (spine : InstantiationSpine B E)
  → pendingRank (vV CT.《 inert 》) spine <ʳ
      pendingRank vV (cast-frame c ▻ⁱ spine)
cast-frame-rank-decreases vV inert spine =
  rank-length< refl refl (n<1+n (spineLength spine))


reveal-frame-value-rank-decreases : ∀ {Δ A B E V}
    {c : Conv↑ Δ A B}
    (vV : CT.Value V) (rv : CT.RevealValue c)
    (spine : InstantiationSpine B E)
  → pendingRank (vV CT.↑ rv) spine <ʳ
      pendingRank vV (reveal-frame c ▻ⁱ spine)
reveal-frame-value-rank-decreases vV rv spine =
  rank-length< refl
    (frame-wrapper-potential-same
      (valueConversionUnits vV)
      (nameFrames spine)
      (spineConversionPotential spine))
    (n<1+n (spineLength spine))


reveal-frame-value-rank-decreases-any : ∀ {Δ A B E V}
    {c : Conv↑ Δ A B}
    (vV : CT.Value V) (child : CT.Value (V CT.↑ c))
    (spine : InstantiationSpine B E)
  → pendingRank child spine <ʳ
      pendingRank vV (reveal-frame c ▻ⁱ spine)
reveal-frame-value-rank-decreases-any vV (vW CT.↑ rv) spine
    rewrite value-conversion-units-irrel vW vV =
  rank-length< refl
    (frame-wrapper-potential-same
      (valueConversionUnits vV)
      (nameFrames spine)
      (spineConversionPotential spine))
    (n<1+n (spineLength spine))


conceal-frame-value-rank-decreases : ∀ {Δ A B E V}
    {c : Conv↓ Δ A B}
    (vV : CT.Value V) (cv : CT.ConcealValue c)
    (spine : InstantiationSpine B E)
  → pendingRank (vV CT.↓ cv) spine <ʳ
      pendingRank vV (conceal-frame c ▻ⁱ spine)
conceal-frame-value-rank-decreases vV cv spine =
  rank-length< refl
    (frame-wrapper-potential-same
      (valueConversionUnits vV)
      (nameFrames spine)
      (spineConversionPotential spine))
    (n<1+n (spineLength spine))


conceal-frame-value-rank-decreases-any : ∀ {Δ A B E V}
    {c : Conv↓ Δ A B}
    (vV : CT.Value V) (child : CT.Value (V CT.↓ c))
    (spine : InstantiationSpine B E)
  → pendingRank child spine <ʳ
      pendingRank vV (conceal-frame c ▻ⁱ spine)
conceal-frame-value-rank-decreases-any vV (vW CT.↓ cv) spine
    rewrite value-conversion-units-irrel vW vV =
  rank-length< refl
    (frame-wrapper-potential-same
      (valueConversionUnits vV)
      (nameFrames spine)
      (spineConversionPotential spine))
    (n<1+n (spineLength spine))


reveal-frame-id-rank-decreases : ∀ {Δ A B E V}
    {c : Conv↑ Δ A B}
    (vV : CT.Value V) (spine : InstantiationSpine B E)
  → pendingRank vV (mapInstantiationSpine keep spine) <ʳ
      pendingRank vV (reveal-frame c ▻ⁱ spine)
reveal-frame-id-rank-decreases vV spine
    rewrite nameFrames-map keep spine
          | spine-conversion-potential-map keep spine =
  rank-exp< refl
    (frame-potential-decreases
      (valueConversionUnits vV)
      (nameFrames spine)
      (spineConversionPotential spine))


reveal-frame-conceal-rank-decreases : ∀ {Δ A B C E V}
    {c : Conv↑ Δ A B} {d : Conv↓ Δ C A}
    (vV : CT.Value V) (cv : CT.ConcealValue d)
    (spine : InstantiationSpine B E)
  → pendingRank vV (mapInstantiationSpine keep spine) <ʳ
      pendingRank (vV CT.↓ cv) (reveal-frame c ▻ⁱ spine)
reveal-frame-conceal-rank-decreases vV cv spine
    rewrite nameFrames-map keep spine
          | spine-conversion-potential-map keep spine =
  rank-exp< refl
    (conceal-reveal-potential-decreases
      (valueConversionUnits vV)
      (nameFrames spine)
      (spineConversionPotential spine))


conceal-frame-id-rank-decreases : ∀ {Δ A B E V}
    {c : Conv↓ Δ A B}
    (vV : CT.Value V) (spine : InstantiationSpine B E)
  → pendingRank vV (mapInstantiationSpine keep spine) <ʳ
      pendingRank vV (conceal-frame c ▻ⁱ spine)
conceal-frame-id-rank-decreases vV spine
    rewrite nameFrames-map keep spine
          | spine-conversion-potential-map keep spine =
  rank-exp< refl
    (frame-potential-decreases
      (valueConversionUnits vV)
      (nameFrames spine)
      (spineConversionPotential spine))
