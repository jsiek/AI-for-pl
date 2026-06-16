-- File Charter:
--   * Compilation from source consistency and typing evidence to coercions and
--     typed coercion terms.
--   * Primary exports are `~⇒coercion` and `compile`.
--   * Depends on labels, types, coercions, consistency, source terms, and target
--     coercion terms.

module Compile where

open import Data.Fin.Subset using (Subset; Side; inside; outside; _∈_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Label using (Label)
open import Types
open import Coercions
open import Consistency
open import Terms as SRC
import CoercionTerms as TGT

~⇒coercion : ∀ {Δ}{Ψ : Subset Δ}{ℓ : Label}{A B : Ty Δ}
  → Ψ ∣ ℓ ⊢ A ~ B
  → Σ (Coercion Δ) λ s →
      Δ ∣ Ψ ⊢ s ∶ A =⇒ B

~⇒coercion X~X = id _ , cast-id
~⇒coercion (α~✯ X∈Ψ) = unseal _ `★ , cast-unseal X∈Ψ
~⇒coercion (✯~α X∈Ψ) = seal `★ _ , cast-seal X∈Ψ
~⇒coercion ι~ι = id _ , cast-id
~⇒coercion ★~★ = id _ , cast-id
~⇒coercion {ℓ = ℓ} (★~ι {ι = ι}) =
  ((‵ ι) ？ ℓ) , cast-untag (‵ ι)
~⇒coercion {Δ} {Ψ} (ι~★ {ι = ι}) =
  ((‵ ι) !) , cast-tag (‵ ι)
~⇒coercion {ℓ = ℓ} (★~⇒ A~★ ★~B)
  with ~⇒coercion A~★ | ~⇒coercion ★~B
... | s , s⊢ | t , t⊢ =
  (((`★ ⇒ `★) ？ ℓ) ︔ (s ↦ t)) ,
  cast-seq (cast-untag ★⇒★) (cast-fun s⊢ t⊢)
~⇒coercion {Δ} {Ψ} (⇒~★ ★~A B~★)
  with ~⇒coercion ★~A | ~⇒coercion B~★
... | s , s⊢ | t , t⊢ =
  ((s ↦ t) ︔ ((`★ ⇒ `★) !)) ,
  cast-seq (cast-fun s⊢ t⊢) (cast-tag ★⇒★)
~⇒coercion (⇒~⇒ A′~A B~B′)
  with ~⇒coercion A′~A | ~⇒coercion B~B′
... | s , s⊢ | t , t⊢ = (s ↦ t) , cast-fun s⊢ t⊢
~⇒coercion (∀~∀ A~B) with ~⇒coercion A~B
... | s , s⊢ = `∀ s , cast-all s⊢
~⇒coercion (∀~ _ A~B) with ~⇒coercion A~B
... | s , s⊢ = inst _ s , cast-inst s⊢
~⇒coercion (~∀ _ A~B) with ~⇒coercion A~B
... | s , s⊢ = gen _ s , cast-gen s⊢


compile : ∀  {Δ : TyCtx} {Ψ : Subset Δ} {Γ : SRC.ExCtx Δ} {T : Ty Δ}
  → SRC.Ex{Δ}{Ψ} Γ T
  → TGT.Ex{Δ}{Ψ} Γ T
compile (` x) = TGT.` x
compile (cst b) = TGT.cst b
compile (λx: T ⇒ e) = TGT.λx: T ⇒ (compile e)
compile {Δ = Δ} {Ψ = Ψ} {Γ = Γ}
        (app {S = sTy} {T = tTy} {U = uTy} {V = vTy}
             e S~T⇒U e′ V~T)
  with ~⇒coercion S~T⇒U | ~⇒coercion V~T
... | s , s⊢ | t , t⊢ =
  TGT.app {Γ = Γ} {T = tTy} {U = uTy}
          (TGT.capp (compile e) s⊢) (TGT.capp (compile e′) t⊢)
compile (ΛX e) = TGT.ΛX (compile e)
compile {Ψ = Ψ} {Γ = Γ} (tapp {T = tTy} e S~∀T U)
  with ~⇒coercion S~∀T
... | s , s⊢ =
  TGT.tapp {Γ = Γ} {T = tTy}
           (TGT.capp (compile e) s⊢) U
