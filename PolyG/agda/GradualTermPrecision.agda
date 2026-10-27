module GradualTermPrecision where

-- File Charter:
--   * Term precision for PolyGν (thesis Fig. 10.24), ∀ν fragment, as a
--     relation between typing derivations: Δ⊑ ∣ Γ⊑ ⊢ d ⊑ᴳ d′ ⦂ p, with
--     the more precise term on the left.
--   * The rules are structural: both sides use the same rule, and each
--     sub-derivation is related.  Where the thesis computes the result
--     precision with a metafunction (cod, un∀ν, meet), the rule instead
--     takes a derivation of the result types; derivations are unique,
--     so this is the same.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

open import Types
open import GradualTerms
open import TermPrecision using
  (PEnv; PCtx; absᵖ; knownᵖ; psize; _∋_≅ᵖ_; _∋_⦂ᵖ_; ⤊ᵖ; ⇑ᵖ) public

infix 4 _∣_⊢_⊑ᴳ_⦂_

data _∣_⊢_⊑ᴳ_⦂_ (Δ⊑ : PEnv) (Γ⊑ : PCtx) :
    ∀ {Δ Δ′ Γ Γ′ M M′ A A′} →
    Δ ∣ Γ ⊢ᴳ M ⦂ A → Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ A′ → Prec → Set where

  ⊑` : ∀ {Δ Δ′ Γ Γ′ x A A′ p}
         {x∈ : Γ ∋ x ⦂ A} {x∈′ : Γ′ ∋ x ⦂ A′} →
    Γ⊑ ∋ x ⦂ᵖ p →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢` {Δ = Δ} x∈ ⊑ᴳ ⊢` {Δ = Δ′} x∈′ ⦂ p

  ⊑⦂⦂ : ∀ {Δ Δ′ Γ Γ′ M M′ A A′ B B′ p q}
          {⊢M : Δ ∣ Γ ⊢ᴳ M ⦂ A} {⊢M′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ A′}
          {A∼B : A ∼ B} {A′∼B′ : A′ ∼ B′}
          {wfB : WfTy (tsize Δ) B} {wfB′ : WfTy (tsize Δ′) B′} →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢M ⊑ᴳ ⊢M′ ⦂ p →
    psize Δ⊑ ⊢ q ⦂ B ⊑ B′ →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢⦂⦂ ⊢M A∼B wfB ⊑ᴳ ⊢⦂⦂ ⊢M′ A′∼B′ wfB′ ⦂ q

  ⊑seal : ∀ {Δ Δ′ Γ Γ′ X M M′ A A′ B B′ p q}
            {X≅A : Δ ∋ X ≅ A} {X≅A′ : Δ′ ∋ X ≅ A′}
            {⊢M : Δ ∣ Γ ⊢ᴳ M ⦂ B} {⊢M′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ B′}
            {B∼A : B ∼ A} {B′∼A′ : B′ ∼ A′} →
    Δ⊑ ∋ X ≅ᵖ q →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢M ⊑ᴳ ⊢M′ ⦂ p →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢seal X≅A ⊢M B∼A ⊑ᴳ ⊢seal X≅A′ ⊢M′ B′∼A′ ⦂ ‵⊑ (tvar X)

  ⊑unseal : ∀ {Δ Δ′ Γ Γ′ X M M′ A A′ B B′ p q}
              {X≅A : Δ ∋ X ≅ A} {X≅A′ : Δ′ ∋ X ≅ A′}
              {⊢M : Δ ∣ Γ ⊢ᴳ M ⦂ B} {⊢M′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ B′}
              {B∼X : B ∼ ‵ tvar X} {B′∼X : B′ ∼ ‵ tvar X} →
    Δ⊑ ∋ X ≅ᵖ q →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢M ⊑ᴳ ⊢M′ ⦂ p →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢unseal X≅A ⊢M B∼X ⊑ᴳ ⊢unseal X≅A′ ⊢M′ B′∼X ⦂ q

  ⊑is : ∀ {Δ Δ′ Γ Γ′ G M M′ A A′ p}
          {wfG : WfGround (tsize Δ) G} {wfG′ : WfGround (tsize Δ′) G}
          {⊢M : Δ ∣ Γ ⊢ᴳ M ⦂ A} {⊢M′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ A′} →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢M ⊑ᴳ ⊢M′ ⦂ p →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢is wfG ⊢M ⊑ᴳ ⊢is wfG′ ⊢M′ ⦂ 𝔹⊑

  ⊑true : ∀ {Δ Δ′ Γ Γ′} →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢true {Δ = Δ} {Γ = Γ} ⊑ᴳ ⊢true {Δ = Δ′} {Γ = Γ′} ⦂ 𝔹⊑

  ⊑false : ∀ {Δ Δ′ Γ Γ′} →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢false {Δ = Δ} {Γ = Γ} ⊑ᴳ ⊢false {Δ = Δ′} {Γ = Γ′} ⦂ 𝔹⊑

  ⊑if : ∀ {Δ Δ′ Γ Γ′ L L′ M M′ N N′ A A′ Bt Bt′ Bf Bf′ B B′ pL pM pN r}
          {⊢L : Δ ∣ Γ ⊢ᴳ L ⦂ A} {⊢L′ : Δ′ ∣ Γ′ ⊢ᴳ L′ ⦂ A′}
          {A∼𝔹 : A ∼ 𝔹} {A′∼𝔹 : A′ ∼ 𝔹}
          {⊢M : Δ ∣ Γ ⊢ᴳ M ⦂ Bt} {⊢M′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ Bt′}
          {⊢N : Δ ∣ Γ ⊢ᴳ N ⦂ Bf} {⊢N′ : Δ′ ∣ Γ′ ⊢ᴳ N′ ⦂ Bf′}
          {m : Meet Bt Bf B} {m′ : Meet Bt′ Bf′ B′} →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢L ⊑ᴳ ⊢L′ ⦂ pL →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢M ⊑ᴳ ⊢M′ ⦂ pM →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢N ⊑ᴳ ⊢N′ ⦂ pN →
    psize Δ⊑ ⊢ r ⦂ B ⊑ B′ →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢if ⊢L A∼𝔹 ⊢M ⊢N m ⊑ᴳ ⊢if ⊢L′ A′∼𝔹 ⊢M′ ⊢N′ m′ ⦂ r

  ⊑ƛ : ∀ {Δ Δ′ Γ Γ′ A A′ B B′ M M′ p q}
         {wfA : WfTy (tsize Δ) A} {wfA′ : WfTy (tsize Δ′) A′}
         {⊢M : Δ ∣ (A ∷ Γ) ⊢ᴳ M ⦂ B} {⊢M′ : Δ′ ∣ (A′ ∷ Γ′) ⊢ᴳ M′ ⦂ B′} →
    psize Δ⊑ ⊢ p ⦂ A ⊑ A′ →
    Δ⊑ ∣ (p ∷ Γ⊑) ⊢ ⊢M ⊑ᴳ ⊢M′ ⦂ q →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢ƛ wfA ⊢M ⊑ᴳ ⊢ƛ wfA′ ⊢M′ ⦂ p ⇒⊑ q

  ⊑· : ∀ {Δ Δ′ Γ Γ′ L L′ M M′ A A′ A₁ A₁′ A₂ A₂′ B B′ pL pM r}
         {⊢L : Δ ∣ Γ ⊢ᴳ L ⦂ A} {⊢L′ : Δ′ ∣ Γ′ ⊢ᴳ L′ ⦂ A′}
         {shp : AsFun A A₁ A₂} {shp′ : AsFun A′ A₁′ A₂′}
         {⊢M : Δ ∣ Γ ⊢ᴳ M ⦂ B} {⊢M′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ B′}
         {B∼A₁ : B ∼ A₁} {B′∼A₁′ : B′ ∼ A₁′} →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢L ⊑ᴳ ⊢L′ ⦂ pL →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢M ⊑ᴳ ⊢M′ ⦂ pM →
    psize Δ⊑ ⊢ r ⦂ A₂ ⊑ A₂′ →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢· ⊢L shp ⊢M B∼A₁ ⊑ᴳ ⊢· ⊢L′ shp′ ⊢M′ B′∼A₁′ ⦂ r

  ⊑letv : ∀ {Δ Δ′ Γ Γ′ M M′ N N′ A A′ B B′ p q}
            {⊢M : Δ ∣ Γ ⊢ᴳ M ⦂ A} {⊢M′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ A′}
            {⊢N : Δ ∣ (A ∷ Γ) ⊢ᴳ N ⦂ B} {⊢N′ : Δ′ ∣ (A′ ∷ Γ′) ⊢ᴳ N′ ⦂ B′} →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢M ⊑ᴳ ⊢M′ ⦂ p →
    Δ⊑ ∣ (p ∷ Γ⊑) ⊢ ⊢N ⊑ᴳ ⊢N′ ⦂ q →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢letv ⊢M ⊢N ⊑ᴳ ⊢letv ⊢M′ ⊢N′ ⦂ q

  ⊑Λν : ∀ {Δ Δ′ Γ Γ′ M M′ A A′ p}
          {⊢M : (abs ∷ Δ) ∣ ⤊ Γ ⊢ᴳ M ⦂ A}
          {⊢M′ : (abs ∷ Δ′) ∣ ⤊ Γ′ ⊢ᴳ M′ ⦂ A′} →
    (absᵖ ∷ Δ⊑) ∣ ⤊ᵖ Γ⊑ ⊢ ⊢M ⊑ᴳ ⊢M′ ⦂ p →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢Λν ⊢M ⊑ᴳ ⊢Λν ⊢M′ ⦂ ∀⊑ p

  ⊑inst : ∀ {Δ Δ′ Γ Γ′ M M′ N N′ A A′ A₀ A₀′ B B′ C C′ pM pX q r}
            {⊢M : Δ ∣ Γ ⊢ᴳ M ⦂ A} {⊢M′ : Δ′ ∣ Γ′ ⊢ᴳ M′ ⦂ A′}
            {shp : AsForall A A₀} {shp′ : AsForall A′ A₀′}
            {wfB : WfTy (tsize Δ) B} {wfB′ : WfTy (tsize Δ′) B′}
            {⊢N : (known B ∷ Δ) ∣ (A₀ ∷ ⤊ Γ) ⊢ᴳ N ⦂ ⇑ᵗ C}
            {⊢N′ : (known B′ ∷ Δ′) ∣ (A₀′ ∷ ⤊ Γ′) ⊢ᴳ N′ ⦂ ⇑ᵗ C′}
            {wfC : WfTy (tsize Δ) C} {wfC′ : WfTy (tsize Δ′) C′} →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢M ⊑ᴳ ⊢M′ ⦂ pM →
    psize Δ⊑ ⊢ q ⦂ B ⊑ B′ →
    suc (psize Δ⊑) ⊢ pX ⦂ A₀ ⊑ A₀′ →
    (knownᵖ q ∷ Δ⊑) ∣ (pX ∷ ⤊ᵖ Γ⊑) ⊢ ⊢N ⊑ᴳ ⊢N′ ⦂ ⇑ᵖ r →
    psize Δ⊑ ⊢ r ⦂ C ⊑ C′ →
    Δ⊑ ∣ Γ⊑ ⊢ ⊢inst ⊢M shp wfB ⊢N wfC ⊑ᴳ ⊢inst ⊢M′ shp′ wfB′ ⊢N′ wfC′ ⦂ r
