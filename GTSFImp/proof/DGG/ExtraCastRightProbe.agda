module proof.DGG.ExtraCastRightProbe where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (suc)
open import Data.Fin using (zero)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _↪ᵗ_; id; _↦_; ∀ᶜ_; _!; ？_; keep; skip;
   wk↪ᵗ; toRenameᵗ; instᵐ; inst_; gen_; bot-elim; bot-intro;
   ↑ᶜ_; close-instᶜ)
import Consistency as C
open import Conversion using (〖_,_↑_〗)
open import CastTerms using
  (Term; Value; _⊢_⦂_; ⟨_,_,_⟩; Λ_; _⦂∀_[_]; _⟨_⟩; _↑_;
   Inert; inj; fun; all; genᵥ; renameᵗᵐ; ⇑ᵗᵐ)
open import Imprecision using (_⊢_⊑_)
import Imprecision as I
import Reduction as R
import GradualTermImprecision as GTI
import proof.DGG.CastTermImprecision as CTI
import proof.DGG.ExtraCastRight as ECR
open CTI using (_∣_⊢ᶜ_⊑_∶_; _∣_∣_∣_⊢ᶜ_⊑_∶_)
import proof.Imprecision as PI
import proof.TypeSafety.Progress as Prog
open import proof.TypeSafety.Progress using (gen-safe)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)

extra-cast-right-top-partial : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : CTI.StoreImp Δ} {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δ} {B B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {p : CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B}
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (c′ : ν ⊢ B ∼ B′)
  → (q : CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ χs ∈ R.StoreChanges Δᴿ Δᴿ′ ]
    Σ[ ηᴸ′ ∈ Δᴸ ↪ᵗ Δ′ ] Σ[ ηᴿ′ ∈ Δᴿ′ ↪ᵗ Δ′ ]
    Σ[ ρ′ ∈ CTI.StoreImp Δ′ ]
    Σ[ γ′ ∈ GTI.CtxImp (CTI.impEnvⁱ ρ′) ]
    Σ[ A′ ∈ Ty Δ′ ] Σ[ B″ ∈ Ty Δᴿ′ ]
    Σ[ q′ ∈ CTI.impEnvⁱ ρ′ ⊢ A′ ⊑ renameᵗ (toRenameᵗ ηᴿ′) B″ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      ((M′ ⟨ c′ ⟩ R.—↠[ χs ] N′)
       × (ηᴸ′ ∣ ηᴿ′ ∣ ρ′ ∣ γ′ ⊢ᶜ M ⊑ N′ ∶ q′))
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (id a) q
    with ECR.extra-cast-right-idᶜ M⊑M′ vM vM′ a q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (id a) q
    | M′c′↠N′ , M⊑N′ =
  Δᴿ , Δ , _ , ηᴸ , ηᴿ , ρ , γ , A , B′ , q , _ ,
  M′c′↠N′ , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (c ↦ d) q
    with ECR.extra-cast-right-inertᶜ M⊑M′ vM vM′ (c ↦ d) fun q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (c ↦ d) q
    | vN′ , M⊑N′ =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , B′ , q , _ ,
  R.↠-refl , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (∀ᶜ c) q
    with ECR.extra-cast-right-inertᶜ M⊑M′ vM vM′ (∀ᶜ c) all q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (∀ᶜ c) q
    | vN′ , M⊑N′ =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , B′ , q , _ ,
  R.↠-refl , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    with Prog.to-ground g match c
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same
    rewrite nonStar-unique Bns (C.ground-nonstar g)
          | C.groundMatch-unique match (C.ground-match g)
    with ECR.extra-cast-right-inertᶜ M⊑M′ vM vM′
      (_! ⦃ g = g ⦄ (C.idᵍ g)
        ⦃ Ans = C.ground-nonstar g ⦄
        ⦃ match = C.ground-match g ⦄)
      (inj ⦃ g = g ⦄ ⦃ Gns = C.ground-nonstar g ⦄
           ⦃ match = C.ground-match g ⦄)
      q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vN′ , M⊑N′ =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , ★ , q , _ ,
  R.↠-refl , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.other B≢G
    with ECR.extra-cast-right-groundᶜ M⊑M′ vM vM′
      c Bns match B≢G q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.other B≢G | M′c′↠N′ , M⊑N′ =
  Δᴿ , Δ , R.keep R.∷ R.[] , ηᴸ , ηᴿ , ρ , γ , A , ★ ,
  q , _ , M′c′↠N′ , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (？_ {B = B′} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    with Prog.from-ground g match c
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (？_ {B = B′} ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same =
  {!!}
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (？_ {B = B′} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.other B≢G
    with ECR.extra-cast-right-expandᶜ M⊑M′ vM vM′
      c Bns match (λ eq → B≢G (sym eq)) q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (？_ {B = B′} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.other B≢G | M′c′↠N′ , M⊑N′ =
  Δᴿ , Δ , R.keep R.∷ R.[] , ηᴸ , ηᴿ , ρ , γ , A , B′ ,
  q , _ , M′c′↠N′ , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ}
    {M = M} {M′ = M′} {A = Asrc} {B′ = Btgt}
    M⊑M′ vM vM′
    (inst_ {A = Body} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) q =
  suc Δᴿ , suc Δ , R.bind ★ R.∷ R.[] ,
  skip ηᴸ , keep ηᴿ , CTI.rightOnly★StoreImp ρ , {!!} ,
  ⇑ᵗ Asrc , ⇑ᵗ Btgt , {!!} ,
  (⇑ᵗᵐ M′ ⦂∀ R.applyBody (R.bind ★) Body [ ＇ zero ]
    ↑ 〖 zero , ★ ↑ Body 〗)
    ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩ ,
  R.↠-step (R.β-inst vM′ B≢★) R.↠-refl ,
  {!!}
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) q
    with ECR.extra-cast-right-inertᶜ M⊑M′ vM vM′
      (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
      (genᵥ A≢★ (gen-safe c A≢★ Bnv z∈B)) q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) q
    | vN′ , M⊑N′ =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , B′ , q , _ ,
  R.↠-refl , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ bot-elim q =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , B′ , q , _ ,
  R.↠-refl , ECR.extra-cast-rightᶜ M⊑M′ vM vM′ bot-elim q
extra-cast-right-top-partial {ηᴸ = ηᴸ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    with q
extra-cast-right-top-partial {ηᴸ = ηᴸ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    | I.∀⊑∀ qbody
    rewrite PI.imprecision-to-fresh qbody
    with M⊑M′
extra-cast-right-top-partial {ηᴸ = ηᴸ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    | I.∀⊑∀ qbody | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ =
  ⊥-elim
    (Prog.no-bot-value (renameᵗᵐ-preserves-Value ηᴸ vM)
      (CTI.cast-term-imprecision-source-typing M⊑M′ᶜ))
extra-cast-right-top-partial {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    | I.∀⊑ Anv zero∈A qbody =
  ⊥-elim (PI.imprecision-no-star-to-bot refl qbody zero∈A)

β-inst-body-hole : ∀ {Δ}
    {ρ : CTI.StoreImp Δ}
    {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {γ∀ : GTI.CtxImp (I.extᵐ (CTI.impEnvⁱ ρ))}
    {γ★ : GTI.CtxImp (I.instᵐ (CTI.impEnvⁱ ρ))}
    {γbody : GTI.CtxImp (I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ)))}
    {V V′ : Term (suc Δ)}
    {A B : Ty (suc Δ)}
    {A★ : Ty (suc (suc Δ))}
    {B′ : Ty (suc Δ)}
    {M : Term (suc Δ)}
    {p : I.extᵐ (CTI.impEnvⁱ ρ) ⊢ A ⊑ B}
    {pBody : I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ))
      ⊢ A★ ⊑ ⇑ᵗ B′}
  → (Anv★ : NonVar A★)
  → (zero∈A★ : zero ∈ᵗ A★)
  → GTI.LiftCtxⁱ (I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ))) γ★ γbody
  → Value V
  → Value V′
  → CTI.liftStoreImp I.X⊑X ρ ∣ γ∀ ⊢ᶜ V ⊑ V′ ∶ p
  → ⟨ suc Δ , CTI.targetStoreⁱ (CTI.rightOnly★StoreImp ρ) ,
        GTI.tgtCtxⁱ γ★ ⟩ ⊢ M ⦂ B′
  → CTI.rightOnly★StoreImp ρ ∣ γ★
      ⊢ᶜ Λ (renameᵗᵐ (keep wk↪ᵗ) V) ⊑ M
      ∶ I.∀⊑ Anv★ zero∈A★ pBody
β-inst-body-hole Anv★ zero∈A★ liftγbody vV vV′ V⊑V′ M⊢ =
  CTI.Λ⊑ᶜ Anv★ zero∈A★ liftγbody
    (renameᵗᵐ-preserves-Value (keep wk↪ᵗ) vV)
    M⊢
    {!!}

β-inst-extra-cast-right-partial : ∀ {Δ}
    {ρ : CTI.StoreImp Δ}
    {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {γ∀ : GTI.CtxImp (I.extᵐ (CTI.impEnvⁱ ρ))}
    {γ★ : GTI.CtxImp (I.instᵐ (CTI.impEnvⁱ ρ))}
    {γbody : GTI.CtxImp (I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ)))}
    {V V′ : Term (suc Δ)}
    {A B : Ty (suc Δ)}
    {B′ : Ty Δ}
    {A★ : Ty (suc (suc Δ))}
    {ν : Env∼ Δ}
    ⦃ Bnv : NonVar B ⦄
    ⦃ zero∈B : zero ∈ᵗ B ⦄
    {c : instᵐ ν ⊢ B ∼ ⇑ᵗ B′}
    {B′≢★ : B′ ≢ ★}
    {p : I.extᵐ (CTI.impEnvⁱ ρ) ⊢ A ⊑ B}
    {pBody : I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ))
      ⊢ A★ ⊑ ⇑ᵗ (⇑ᵗ B′)}
  → (Anv★ : NonVar A★)
  → (zero∈A★ : zero ∈ᵗ A★)
  → GTI.LiftCtxⁱ (I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ))) γ★ γbody
  → Value V
  → Value V′
  → CTI.liftStoreImp I.X⊑X ρ ∣ γ∀ ⊢ᶜ V ⊑ V′ ∶ p
  → ⟨ suc Δ , CTI.targetStoreⁱ (CTI.rightOnly★StoreImp ρ) ,
        GTI.tgtCtxⁱ γ★ ⟩
      ⊢ (⇑ᵗᵐ (Λ V′) ⦂∀ R.applyBody (R.bind ★) B [ ＇ zero ]
          ↑ 〖 zero , ★ ↑ B 〗)
        ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩ ⦂ ⇑ᵗ B′
  → ((Λ V′) ⟨ (inst c) B′≢★ ⟩
       R.—↠[ R.bind ★ R.∷ R.[] ]
     (⇑ᵗᵐ (Λ V′) ⦂∀ R.applyBody (R.bind ★) B [ ＇ zero ]
       ↑ 〖 zero , ★ ↑ B 〗)
       ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩)
    ×
    (CTI.rightOnly★StoreImp ρ ∣ γ★
      ⊢ᶜ Λ (renameᵗᵐ (keep wk↪ᵗ) V)
        ⊑ (⇑ᵗᵐ (Λ V′) ⦂∀ R.applyBody (R.bind ★) B [ ＇ zero ]
             ↑ 〖 zero , ★ ↑ B 〗)
           ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩
        ∶ I.∀⊑ Anv★ zero∈A★ pBody)
β-inst-extra-cast-right-partial {B′≢★ = B′≢★}
    Anv★ zero∈A★ liftγbody vV vV′ V⊑V′ reduct⊢ =
  R.↠-step (R.β-inst (Λ vV′) B′≢★) R.↠-refl
  , CTI.Λ⊑ᶜ Anv★ zero∈A★ liftγbody
      (renameᵗᵐ-preserves-Value (keep wk↪ᵗ) vV)
      reduct⊢
      {!!}
