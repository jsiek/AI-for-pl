module proof.DGG.CompilePreservesImprecision where

-- File Charter:
--   * Proves that compiling related gradual terms produces related cast
--     terms at the same type-imprecision index.
--   * Uses the gradual relation's typing projections to invoke the compiler.
--   * Depends on Compile, GradualTermImprecision, and the typed cast-term
--     imprecision relation.

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Fin using (zero)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst)

open import Types
open import TyStore using (TyStore; store-lift)
open import TermCtx using (TermCtx; ⇑ᶜ)
open import Consistency using (_∼_; id; _↦_; ？_; symᶜ)
open import Imprecision
open import GradualTerms using
  (GTerm; _∣_⊢_⦂_; `_; ƛ_⇒_; _·[_]_; Λ_; _`[_]; $_;
   _⊕[_at_]_; ⊢`; ⊢ƛ; ⊢·; ⊢·★; ⊢Λ; ⊢•; ⊢$; ⊢⊕)
import GradualTerms as G
open import Primitives using (primArgTy)
import CastTerms as C
open C using () renaming (Λ_ to Λᵀ_)
open import Compile using (compile; compile-value)
import GradualTermImprecision as GTI
open import GradualTermImprecision using
  (CtxImp; _∣_⊢ᴳ_⊑_⦂_⊑_∶_)
import proof.DGG.CastTermImprecision as CTI
open CTI using (_∣_⊢ᶜ_⊑_∶_)
open import proof.ImprecisionConsistency using (refl⊑)

dynamic-function-cast : ∀ {Δ} → _∼_ {Δ} ★ (★ ⇒ ★)
dynamic-function-cast = ？ (id ★ ↦ id ★)

compile-context-subst : ∀ {Δ} {Σ : TyStore Δ}
    {Γ Γ′ : TermCtx Δ} {M : GTerm Δ} {A : Ty Δ}
  → (Γ≡Γ′ : Γ ≡ Γ′)
  → (M⊢ : Δ ∣ Γ ⊢ M ⦂ A)
  → proj₁ (compile {Σ = Σ}
      (subst (λ Γ₀ → Δ ∣ Γ₀ ⊢ M ⦂ A) Γ≡Γ′ M⊢))
    ≡ proj₁ (compile {Σ = Σ} M⊢)
compile-context-subst refl M⊢ = refl

compile-Λ-term : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {M : GTerm (Nat.suc Δ)} {A : Ty (Nat.suc Δ)}
    {zero∈A : zero ∈ᵗ A}
  → (vM : G.Value M)
  → (M⊢ : Nat.suc Δ ∣ ⇑ᶜ Γ ⊢ M ⦂ A)
  → proj₁ (compile {Σ = Σ} (G.⊢Λ {zero∈A = zero∈A} vM M⊢))
    ≡ Λᵀ (proj₁ (compile {Σ = store-lift Σ} M⊢))
compile-Λ-term {Σ = Σ} vM M⊢
    with compile {Σ = store-lift Σ} M⊢
       | compile-value {Σ = store-lift Σ} vM M⊢
compile-Λ-term {Σ = Σ} vM M⊢ | N , N⊢ | vN = refl

compile-preserves-imprecision : ∀ {Δ} {ρ : CTI.StoreImp Δ}
    {γ : CtxImp (CTI.impEnvⁱ ρ)} {M M′ A B p}
  → (M⊑M′ : CTI.impEnvⁱ ρ ∣ γ
      ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p)
  → ρ ∣ γ ⊢ᶜ
      proj₁ (compile {Σ = CTI.sourceStoreⁱ ρ}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ proj₁ (compile {Σ = CTI.targetStoreⁱ ρ}
        (GTI.gradual-term-imprecision-target-typing M⊑M′))
      ∶ p
compile-preserves-imprecision (GTI.x⊑xᴳ x∈) =
  CTI.x⊑xᶜ x∈
compile-preserves-imprecision {ρ = ρ} (GTI.ƛ⊑ƛᴳ N⊑N′)
    with compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing N⊑N′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing N⊑N′)
       | compile-preserves-imprecision {ρ = ρ} N⊑N′
compile-preserves-imprecision {ρ = ρ} (GTI.ƛ⊑ƛᴳ N⊑N′)
    | N , N⊢ | N′ , N′⊢ | N⊑N′ᶜ =
  CTI.ƛ⊑ƛᶜ N⊑N′ᶜ
compile-preserves-imprecision
    {ρ = ρ}
    (GTI.·⊑·ᴳ {pA = pA} L⊑L′ M⊑M′ A∼C A′∼C′)
    with compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
       | compile-preserves-imprecision {ρ = ρ} L⊑L′
       | compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
       | compile-preserves-imprecision {ρ = ρ} M⊑M′
compile-preserves-imprecision
    {ρ = ρ}
    (GTI.·⊑·ᴳ {pA = pA} L⊑L′ M⊑M′ A∼C A′∼C′)
    | L , L⊢ | L′ , L′⊢ | L⊑L′ᶜ
    | M , M⊢ | M′ , M′⊢ | M⊑M′ᶜ =
  CTI.·⊑·ᶜ L⊑L′ᶜ
    (CTI.cast⊑castᶜ (symᶜ A∼C) (symᶜ A′∼C′) M⊑M′ᶜ pA)
compile-preserves-imprecision
    {ρ = ρ}
    (GTI.·⊑·★ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C C′∼★)
    with compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
       | compile-preserves-imprecision {ρ = ρ} L⊑L′
       | compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
       | compile-preserves-imprecision {ρ = ρ} M⊑M′
compile-preserves-imprecision
    {ρ = ρ}
    (GTI.·⊑·★ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C C′∼★)
    | L , L⊢ | L′ , L′⊢ | L⊑L′ᶜ
    | M , M⊢ | M′ , M′⊢ | M⊑M′ᶜ =
  CTI.·⊑·ᶜ
    (CTI.⊑castᶜ dynamic-function-cast L⊑L′ᶜ (⇒⊑⇒ pA pB))
    (CTI.cast⊑castᶜ (symᶜ A∼C) C′∼★ M⊑M′ᶜ pA)
compile-preserves-imprecision
    {ρ = ρ} (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    with compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
       | compile-preserves-imprecision {ρ = ρ} L⊑L′
       | compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
       | compile-preserves-imprecision {ρ = ρ} M⊑M′
compile-preserves-imprecision
    {ρ = ρ} (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    | L , L⊢ | L′ , L′⊢ | L⊑L′ᶜ
    | M , M⊢ | M′ , M′⊢ | M⊑M′ᶜ =
  CTI.·⊑·ᶜ
    (CTI.cast⊑castᶜ dynamic-function-cast dynamic-function-cast
      L⊑L′ᶜ (⇒⊑⇒ ★⊑★ ★⊑★))
    (CTI.cast⊑castᶜ C∼★ C′∼★ M⊑M′ᶜ ★⊑★)
compile-preserves-imprecision
    {ρ = ρ} {γ = γ}
    (GTI.Λ⊑Λᴳ liftγ vV vV′ zero∈A zero∈B V⊑V′)
    rewrite compile-Λ-term {Σ = CTI.sourceStoreⁱ ρ}
      {Γ = GTI.srcCtxⁱ γ}
      {zero∈A = zero∈A} vV
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _) (GTI.srcCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-source-typing V⊑V′))
      | compile-Λ-term {Σ = CTI.targetStoreⁱ ρ}
      {Γ = GTI.tgtCtxⁱ γ}
      {zero∈A = zero∈B} vV′
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _) (GTI.tgtCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-target-typing V⊑V′))
      | compile-context-subst
      {Σ = store-lift (CTI.sourceStoreⁱ ρ)}
      (GTI.srcCtxⁱ-lift liftγ)
      (GTI.gradual-term-imprecision-source-typing V⊑V′)
      | compile-context-subst
      {Σ = store-lift (CTI.targetStoreⁱ ρ)}
      (GTI.tgtCtxⁱ-lift liftγ)
      (GTI.gradual-term-imprecision-target-typing V⊑V′) =
  CTI.Λ⊑Λᶜ liftγ
    (compile-value {Σ = store-lift (CTI.sourceStoreⁱ ρ)} vV
      (GTI.gradual-term-imprecision-source-typing V⊑V′))
    (compile-value {Σ = store-lift (CTI.targetStoreⁱ ρ)} vV′
      (GTI.gradual-term-imprecision-target-typing V⊑V′))
    (compile-preserves-imprecision
      {ρ = CTI.liftStoreImp X⊑X ρ} V⊑V′)
compile-preserves-imprecision
    {ρ = ρ} {γ = γ}
    (GTI.Λ⊑ᴳ Anv zero∈A liftγ vV V⊑N′)
    rewrite compile-Λ-term {Σ = CTI.sourceStoreⁱ ρ}
      {Γ = GTI.srcCtxⁱ γ}
      {zero∈A = zero∈A} vV
      (subst (λ Γ → _ ∣ Γ ⊢ _ ⦂ _) (GTI.srcCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-source-typing V⊑N′))
      | compile-context-subst
      {Σ = store-lift (CTI.sourceStoreⁱ ρ)}
      (GTI.srcCtxⁱ-lift liftγ)
      (GTI.gradual-term-imprecision-source-typing V⊑N′) =
  CTI.Λ⊑ᶜ Anv zero∈A liftγ
    (compile-value {Σ = store-lift (CTI.sourceStoreⁱ ρ)} vV
      (GTI.gradual-term-imprecision-source-typing V⊑N′))
    (compile-preserves-imprecision
      {ρ = CTI.liftStoreImp X⊑★ ρ} V⊑N′)
compile-preserves-imprecision {ρ = ρ} (GTI.[]⊑[]ᴳ M⊑M′ q r)
    with compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
       | compile-preserves-imprecision {ρ = ρ} M⊑M′
compile-preserves-imprecision {ρ = ρ} (GTI.[]⊑[]ᴳ M⊑M′ q r)
    | M , M⊢ | M′ , M′⊢ | M⊑M′ᶜ =
  CTI.•⊑•ᶜ M⊑M′ᶜ q r
compile-preserves-imprecision {ρ = ρ} (GTI.[]⊑ᴳ M⊑M′ q r)
    with compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
       | compile-preserves-imprecision {ρ = ρ} M⊑M′
compile-preserves-imprecision {ρ = ρ} (GTI.[]⊑ᴳ M⊑M′ q r)
    | M , M⊢ | M′ , M′⊢ | M⊑M′ᶜ =
  CTI.•⊑ᶜ M⊑M′ᶜ q r
compile-preserves-imprecision {ρ = ρ} (GTI.κ⊑κᴳ κ) =
  CTI.κ⊑κᶜ κ (GTI.constTy-⊑ (CTI.impEnvⁱ ρ) κ)
compile-preserves-imprecision
    {ρ = ρ}
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
      B∼arg B′∼arg)
    with compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
       | compile-preserves-imprecision {ρ = ρ} L⊑L′
       | compile {Σ = CTI.sourceStoreⁱ ρ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile {Σ = CTI.targetStoreⁱ ρ}
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
       | compile-preserves-imprecision {ρ = ρ} M⊑M′
compile-preserves-imprecision
    {ρ = ρ}
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
      B∼arg B′∼arg)
    | L , L⊢ | L′ , L′⊢ | L⊑L′ᶜ
    | M , M⊢ | M′ , M′⊢ | M⊑M′ᶜ =
  CTI.⊕⊑⊕ᶜ op
    (CTI.cast⊑castᶜ A∼arg A′∼arg L⊑L′ᶜ
      (refl⊑ (primArgTy op)))
    (CTI.cast⊑castᶜ B∼arg B′∼arg M⊑M′ᶜ
      (refl⊑ (primArgTy op)))
    (GTI.primResultTy-⊑ (CTI.impEnvⁱ ρ) op)
