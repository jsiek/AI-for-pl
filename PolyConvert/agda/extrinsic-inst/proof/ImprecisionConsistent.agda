module proof.ImprecisionConsistent where

-- File Charter:
--   * Properties that involve Imprecision and Consistency

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (_∨_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; zero; suc; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Imprecision
open import Consistency
open import Types
open import proof.ConsistencyProperties
  using
    ( cong-~
    ; occurs-rename-ext-raise-zero
    ; length-leftICtx
    ; length-rightICtx
    ; length-extend-X~X[]
    ; drop-neither-~
    )
open import proof.ImprecisionProperties
  using
    ( _≤ᵢ_
    ; ModeLe
    ; []≤ᵢ
    ; _∷≤ᵢ_
    ; ≤ᵢ-refl
    ; ≤ᵢ-length
    ; ≤ᵢ-ν-lookup
    ; ⊑-src-wf
    ; ⊑-tgt-wf
    ; cong-⊢⊑
    ; cong-⊢⊑-raw
    ; dropTyFrom-raise-same
    ; rename⊑-cong
    ; plain-source-occurs-target
    ; plain-target-occurs-source
    ; src⊑-correct
    ; tgt⊑-correct
    ; wf-length-cast
    ; wkImpAt
    ; X⊑X≤X⊑X
    ; X⊑X≤ν
    ; ν≤ν
    ; trans-ctx-⊑
    )
open import proof.TypeProperties
  using
    ( ground-upper-unique-⊑
    ; ground-upper-unique-chain-non∀-⊑
    ; raise-ext
    ; raiseVarFrom-injective
    ; rename-raise-ext
    ; rename-raise-⇑ᵗ
    ; renameᵗ-ground
    ; renameᵗ-ground-id
    ; renameᵗ-preserves-Non∀
    )

leftICtx-extend-X~X[] : ∀ Δ → leftICtx (extend-X~X Δ []) ≡ extend-X⊑X Δ []
leftICtx-extend-X~X[] zero = refl
leftICtx-extend-X~X[] (suc Δ) = cong (X⊑X ∷_) (leftICtx-extend-X~X[] Δ)

rightICtx-extend-X~X[] : ∀ Δ → rightICtx (extend-X~X Δ []) ≡ extend-X⊑X Δ []
rightICtx-extend-X~X[] zero = refl
rightICtx-extend-X~X[] (suc Δ) = cong (X⊑X ∷_) (rightICtx-extend-X~X[] Δ)

wf-leftICtx :
  ∀ {Γ A} →
  WfTy (length Γ) 0 A →
  WfTy (length (leftICtx Γ)) 0 A
wf-leftICtx {Γ = Γ} wfA =
  subst (λ Δ → WfTy Δ 0 _) (sym (length-leftICtx Γ)) wfA

wf-rightICtx :
  ∀ {Γ A} →
  WfTy (length Γ) 0 A →
  WfTy (length (rightICtx Γ)) 0 A
wf-rightICtx {Γ = Γ} wfA =
  subst (λ Δ → WfTy Δ 0 _) (sym (length-rightICtx Γ)) wfA

left-lookup-left :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ X~★ →
  leftICtx Γ ∋ X ∶ X⊑X
left-lookup-left here = here
left-lookup-left (there x∈) = there (left-lookup-left x∈)

right-lookup-left :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ X~★ →
  rightICtx Γ ∋ X ∶ X⊑★
right-lookup-left here = here
right-lookup-left (there x∈) = there (right-lookup-left x∈)

left-lookup-right :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ ★~X →
  leftICtx Γ ∋ X ∶ X⊑★
left-lookup-right here = here
left-lookup-right (there x∈) = there (left-lookup-right x∈)

right-lookup-right :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ ★~X →
  rightICtx Γ ∋ X ∶ X⊑X
right-lookup-right here = here
right-lookup-right (there x∈) = there (right-lookup-right x∈)

left-lookup-both :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ X~X →
  leftICtx Γ ∋ X ∶ X⊑X
left-lookup-both here = here
left-lookup-both (there x∈) = there (left-lookup-both x∈)

right-lookup-both : 
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ X~X →
  rightICtx Γ ∋ X ∶ X⊑X
right-lookup-both here = here
right-lookup-both (there x∈) = there (right-lookup-both x∈)

insert-mode-∋ᶜ :
  ∀ {d : CMode} {m} {Φ Γ : CCtx} {X} →
  (Φ ++ Γ) ∋ᶜ X ∶ m →
  (Φ ++ d ∷ Γ) ∋ᶜ raiseVarFrom (length Φ) X ∶ m
insert-mode-∋ᶜ {Φ = []} x∈ = there x∈
insert-mode-∋ᶜ {Φ = m₀ ∷ Φ} here = here
insert-mode-∋ᶜ {Φ = m₀ ∷ Φ} (there x∈) =
  there (insert-mode-∋ᶜ {Φ = Φ} x∈)

insert-mode-< :
  ∀ {d : CMode} {Φ Γ : CCtx} {X} →
  X < length (Φ ++ Γ) →
  raiseVarFrom (length Φ) X < length (Φ ++ d ∷ Γ)
insert-mode-< {Φ = []} X<Γ = s<s X<Γ
insert-mode-< {Φ = m ∷ Φ} {X = zero} z<s = z<s
insert-mode-< {Φ = m ∷ Φ} {X = suc X} (s<s X<Γ) =
  s<s (insert-mode-< {Φ = Φ} X<Γ)

insert-mode-WfTy :
  ∀ {d : CMode} {Φ Γ : CCtx} {A} →
  WfTy (length (Φ ++ Γ)) 0 A →
  WfTy (length (Φ ++ d ∷ Γ)) 0
    (renameᵗ (raiseVarFrom (length Φ)) A)
insert-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = ＇ X} (wfVar X<Γ) =
  wfVar (insert-mode-< {d = d} {Φ = Φ} {Γ = Γ} {X = X} X<Γ)
insert-mode-WfTy {A = ｀ α} (wfSeal α<Ψ) = wfSeal α<Ψ
insert-mode-WfTy {A = ‵ ι} wfBase = wfBase
insert-mode-WfTy {A = ★} wf★ = wf★
insert-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = A ⇒ B} (wf⇒ wfA wfB) =
  wf⇒ (insert-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = A} wfA)
       (insert-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = B} wfB)
insert-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = `∀ A} (wf∀ wfA) =
  wf∀
    (subst (λ B → WfTy (length ((X~X ∷ Φ) ++ d ∷ Γ)) 0 B)
      (sym (rename-raise-ext (length Φ) A))
      (insert-mode-WfTy {d = d} {Φ = X~X ∷ Φ} {Γ = Γ} {A = A}
        wfA))

drop-mode-∋ :
  ∀ {m m′ : VarPrec} {Φ Γ : VarPrecCtx} {X} →
  (Φ ++ m′ ∷ Γ) ∋ raiseVarFrom (length Φ) X ∶ m →
  (Φ ++ Γ) ∋ X ∶ m
drop-mode-∋ {Φ = []} (there x∈) = x∈
drop-mode-∋ {Φ = m₀ ∷ Φ} {X = zero} here = here
drop-mode-∋ {Φ = m₀ ∷ Φ} {X = suc X} (there x∈) =
  there (drop-mode-∋ {Φ = Φ} x∈)

drop-mode-∋-eq :
  ∀ {m m′ : VarPrec} {Φ Γ : VarPrecCtx} {X Y} →
  Y ≡ raiseVarFrom (length Φ) X →
  (Φ ++ m′ ∷ Γ) ∋ Y ∶ m →
  (Φ ++ Γ) ∋ X ∶ m
drop-mode-∋-eq {Φ = Φ} refl x∈ = drop-mode-∋ {Φ = Φ} x∈

drop-mode-<ᵢ :
  ∀ {m : VarPrec} {Φ Γ : VarPrecCtx} {X} →
  raiseVarFrom (length Φ) X < length (Φ ++ m ∷ Γ) →
  X < length (Φ ++ Γ)
drop-mode-<ᵢ {Φ = []} (s<s X<Γ) = X<Γ
drop-mode-<ᵢ {Φ = m₀ ∷ Φ} {X = zero} z<s = z<s
drop-mode-<ᵢ {Φ = m₀ ∷ Φ} {X = suc X} (s<s X<Γ) =
  s<s (drop-mode-<ᵢ {Φ = Φ} X<Γ)

drop-mode-WfTyᵢ :
  ∀ {Ψ} {m : VarPrec} {Φ Γ : VarPrecCtx} {A} →
  WfTy (length (Φ ++ m ∷ Γ)) Ψ
    (renameᵗ (raiseVarFrom (length Φ)) A) →
  WfTy (length (Φ ++ Γ)) Ψ A
drop-mode-WfTyᵢ {Φ = Φ} {Γ = Γ} {A = ＇ X} (wfVar X<Γ) =
  wfVar (drop-mode-<ᵢ {Φ = Φ} {Γ = Γ} {X = X} X<Γ)
drop-mode-WfTyᵢ {A = ｀ α} (wfSeal α<Ψ) = wfSeal α<Ψ
drop-mode-WfTyᵢ {A = ‵ ι} wfBase = wfBase
drop-mode-WfTyᵢ {A = ★} wf★ = wf★
drop-mode-WfTyᵢ {Ψ = Ψ} {m = m} {Φ = Φ} {Γ = Γ} {A = A ⇒ B}
    (wf⇒ wfA wfB) =
  wf⇒ (drop-mode-WfTyᵢ {Ψ = Ψ} {m = m} {Φ = Φ} {Γ = Γ} {A = A} wfA)
       (drop-mode-WfTyᵢ {Ψ = Ψ} {m = m} {Φ = Φ} {Γ = Γ} {A = B} wfB)
drop-mode-WfTyᵢ {Ψ = Ψ} {m = m} {Φ = Φ} {Γ = Γ} {A = `∀ A}
    (wf∀ wfA) =
  wf∀
    (drop-mode-WfTyᵢ {Ψ = Ψ} {m = m} {Φ = X⊑X ∷ Φ} {Γ = Γ} {A = A}
      (subst (λ B → WfTy (length ((X⊑X ∷ Φ) ++ m ∷ Γ)) Ψ B)
        (rename-raise-ext (length Φ) A)
        wfA))

＇-injective : ∀ {X Y : TyVar} → _≡_ {A = Ty} (＇ X) (＇ Y) → X ≡ Y
＇-injective refl = refl

idₓ-lookup :
  ∀ {Ψ} {Γ : VarPrecCtx} {X A B} →
  Ψ ∣ Γ ⊢ idₓ X ⦂ A ⊑ B →
  Γ ∋ X ∶ X⊑X
idₓ-lookup (⊢X-⊑-X x∈) = x∈

drop-mode-⊑ :
  ∀ {Ψ m Φ Γ A B p} →
  Ψ ∣ Φ ++ m ∷ Γ ⊢ p ⦂
    renameᵗ (raiseVarFrom (length Φ)) A ⊑
    renameᵗ (raiseVarFrom (length Φ)) B →
  ∃[ q ] Ψ ∣ Φ ++ Γ ⊢ q ⦂ A ⊑ B
drop-mode-⊑ {A = ★} {B = ★} ⊢★-⊑-★ = id★ , ⊢★-⊑-★
drop-mode-⊑ {Φ = Φ} {Γ = Γ} {A = ＇ X} {B = ★} (⊢X-⊑-★ xν) =
  ‵ X ! , ⊢X-⊑-★ (drop-mode-∋ {Φ = Φ} {Γ = Γ} xν)
drop-mode-⊑ {A = A} {B = ★} (⊢A-⊑-★ g p⊢)
    with drop-mode-⊑ {A = A} {B = _}
      (cong-⊢⊑ refl (sym (renameᵗ-ground-id g)) p⊢)
... | q , q⊢ =
  q ! , ⊢A-⊑-★ g q⊢
drop-mode-⊑ {Φ = Φ} {Γ = Γ} {A = ＇ X} {B = ＇ Y} {p = idₓ z} p⊢ =
  idₓ X ,
  cong-⊢⊑ refl (cong ＇_ eqXY)
    (⊢X-⊑-X (drop-mode-∋-eq {Φ = Φ} eqZX (idₓ-lookup p⊢)))
  where
    eqZX : z ≡ raiseVarFrom (length Φ) X
    eqZX = ＇-injective (src⊑-correct p⊢)

    eqZY : z ≡ raiseVarFrom (length Φ) Y
    eqZY = ＇-injective (tgt⊑-correct p⊢)

    eqXY : X ≡ Y
    eqXY = raiseVarFrom-injective (length Φ) (trans (sym eqZX) eqZY)
drop-mode-⊑ {Ψ = Ψ} {m = m} {Φ = Φ} {Γ = Γ} {A = ｀ α} {B = ｀ α}
    (⊢α-⊑-α wfα) =
  idₛ α ,
  ⊢α-⊑-α (drop-mode-WfTyᵢ {Ψ = Ψ} {m = m} {Φ = Φ} {Γ = Γ}
    {A = ｀ α} wfα)
drop-mode-⊑ {A = ‵ ι} {B = ‵ ι} ⊢ι-⊑-ι =
  idι ι , ⊢ι-⊑-ι
drop-mode-⊑ {A = A ⇒ B} {B = A′ ⇒ B′}
    (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
    with drop-mode-⊑ {A = A} {B = A′} p⊢
       | drop-mode-⊑ {A = B} {B = B′} q⊢
... | p , p⊢′ | q , q⊢′ =
  p ↦ q , ⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′
drop-mode-⊑ {m = m} {Φ = Φ} {Γ = Γ} {A = `∀ A} {B = `∀ B}
    (⊢∀A-⊑-∀B p⊢)
    with drop-mode-⊑ {m = m} {Φ = X⊑X ∷ Φ} {Γ = Γ} {A = A} {B = B}
      (cong-⊢⊑ (rename-raise-ext (length Φ) A)
        (rename-raise-ext (length Φ) B) p⊢)
... | q , q⊢ =
  ‵∀ q , ⊢∀A-⊑-∀B q⊢
drop-mode-⊑ {Ψ = Ψ} {m = m} {Φ = Φ} {Γ = Γ} {A = `∀ A} {B = B}
    (⊢∀A-⊑-B occA wfB p⊢)
    with drop-mode-⊑ {m = m} {Φ = X⊑★ ∷ Φ} {Γ = Γ} {A = A} {B = ⇑ᵗ B}
      (cong-⊢⊑ (rename-raise-ext (length Φ) A)
        (sym (rename-raise-⇑ᵗ (length Φ) B)) p⊢)
... | q , q⊢ =
  ν q ,
  ⊢∀A-⊑-B
    (trans (sym (occurs-rename-ext-raise-zero (length Φ) A)) occA)
    (drop-mode-WfTyᵢ {Ψ = Ψ} {m = m} {Φ = Φ} {Γ = Γ} {A = B} wfB)
    q⊢

renameᵗ-preserves-Non★ : ∀ {ρ A} → Non★ A → Non★ (renameᵗ ρ A)
renameᵗ-preserves-Non★ non★-＇ = non★-＇
renameᵗ-preserves-Non★ non★-｀ = non★-｀
renameᵗ-preserves-Non★ non★-‵ = non★-‵
renameᵗ-preserves-Non★ non★-⇒ = non★-⇒
renameᵗ-preserves-Non★ non★-∀ = non★-∀

height~ : ∀ {Γ A B} → Γ ⊢ A ~ B → ℕ
height~ ★-~-★ = suc zero
height~ (X-~-X x∈) = suc zero
height~ ι-~-ι = suc zero
height~ (⇒-~-⇒ A~B C~D) = suc (height~ A~B + height~ C~D)
height~ (∀-~-∀ A~B) = suc (height~ A~B)
height~ (A-~-★ n★ n∀ g A~G) = suc (height~ A~G)
height~ (★-~-B n★ n∀ h G~B) = suc (height~ G~B)
height~ (νX-~-★ x∈) = suc zero
height~ (★-~-νX x∈) = suc zero
height~ (∀-~-B occA wfB A~⇑B) = suc (height~ A~⇑B)
height~ (A-~-∀ occB wfA ⇑A~B) = suc (height~ ⇑A~B)

heightImp : Imp → ℕ
heightImp id★ = suc zero
heightImp (‵ X !) = suc zero
heightImp (p !) = suc (heightImp p)
heightImp (idₓ X) = suc zero
heightImp (idₛ α) = suc zero
heightImp (idι ι) = suc zero
heightImp (p ↦ q) = suc (heightImp p + heightImp q)
heightImp (‵∀ p) = suc (heightImp p)
heightImp (ν p) = suc (heightImp p)

height⊑ : ∀ {Ψ Φ p A B} → Ψ ∣ Φ ⊢ p ⦂ A ⊑ B → ℕ
height⊑ ⊢★-⊑-★ = suc zero
height⊑ (⊢X-⊑-★ xν) = suc zero
height⊑ (⊢A-⊑-★ g p⊢) = suc (height⊑ p⊢)
height⊑ (⊢X-⊑-X x∈) = suc zero
height⊑ (⊢α-⊑-α wfα) = suc zero
height⊑ ⊢ι-⊑-ι = suc zero
height⊑ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  suc (height⊑ p⊢ + height⊑ q⊢)
height⊑ (⊢∀A-⊑-∀B p⊢) = suc (height⊑ p⊢)
height⊑ (⊢∀A-⊑-B occA wfB p⊢) = suc (height⊑ p⊢)

height-cong-⊢⊑-raw :
  ∀ {Ψ Φ p p′ A A′ B B′} →
  (eqp : p ≡ p′) →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (p⊢ : Ψ ∣ Φ ⊢ p ⦂ A ⊑ B) →
  height⊑ (cong-⊢⊑-raw eqp eqA eqB p⊢) ≡ height⊑ p⊢
height-cong-⊢⊑-raw refl refl refl p⊢ = refl

height-wkImpAt :
  ∀ {Ψ Φ Γ p A B m′} →
  (p⊢ : Ψ ∣ (Φ ++ Γ) ⊢ p ⦂ A ⊑ B) →
  height⊑ (wkImpAt {Φ = Φ} {m′ = m′} p⊢) ≡ height⊑ p⊢
height-wkImpAt ⊢★-⊑-★ = refl
height-wkImpAt (⊢X-⊑-★ xν) = refl
height-wkImpAt {Φ = Φ} {Γ = Γ} {m′ = m′} (⊢A-⊑-★ g p⊢)
  rewrite height-wkImpAt {Φ = Φ} {Γ = Γ} {m′ = m′} p⊢ = refl
height-wkImpAt (⊢X-⊑-X x∈) = refl
height-wkImpAt (⊢α-⊑-α (wfSeal α<Ψ)) = refl
height-wkImpAt ⊢ι-⊑-ι = refl
height-wkImpAt {Φ = Φ} {Γ = Γ} {m′ = m′}
    (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
  rewrite height-wkImpAt {Φ = Φ} {Γ = Γ} {m′ = m′} p⊢
        | height-wkImpAt {Φ = Φ} {Γ = Γ} {m′ = m′} q⊢ = refl
height-wkImpAt {Φ = Φ} {Γ = Γ} {m′ = m′} (⊢∀A-⊑-∀B p⊢)
  rewrite height-cong-⊢⊑-raw
            (sym (rename⊑-cong (raise-ext (length Φ)) _))
            (sym (rename-raise-ext (length Φ) _))
            (sym (rename-raise-ext (length Φ) _))
            (wkImpAt {Φ = X⊑X ∷ Φ} {Γ = Γ} {m′ = m′} p⊢)
        | height-wkImpAt {Φ = X⊑X ∷ Φ} {Γ = Γ} {m′ = m′} p⊢ = refl
height-wkImpAt {Φ = Φ} {Γ = Γ} {m′ = m′}
    (⊢∀A-⊑-B {A = A} {B = B} occA wfB p⊢)
  rewrite height-cong-⊢⊑-raw
            (sym (rename⊑-cong (raise-ext (length Φ)) _))
            (sym (rename-raise-ext (length Φ) A))
            (rename-raise-⇑ᵗ (length Φ) B)
            (wkImpAt {Φ = X⊑★ ∷ Φ} {Γ = Γ} {m′ = m′} p⊢)
        | height-wkImpAt {Φ = X⊑★ ∷ Φ} {Γ = Γ} {m′ = m′} p⊢ = refl

infix 4 _<lex_
data _<lex_ : ℕ × ℕ → ℕ × ℕ → Set where
  lex-left :
    ∀ {m n m′ n′} →
    m < m′ →
    (m , n) <lex (m′ , n′)
  lex-right :
    ∀ {m n n′} →
    n < n′ →
    (m , n) <lex (m , n′)

glb-measure :
  ∀ {Γ Φ A C B′ pA pC} →
  Γ ⊢ A ~ C →
  0 ∣ Φ ⊢ pA ⦂ B′ ⊑ A →
  0 ∣ Φ ⊢ pC ⦂ B′ ⊑ C →
  ℕ × ℕ
glb-measure A~C pA⊢ pC⊢ =
  height~ A~C , height⊑ pA⊢ + height⊑ pC⊢

insert-mode-~ :
  ∀ {d : CMode} {Φ Γ : CCtx} {A B} →
  Φ ++ Γ ⊢ A ~ B →
  Φ ++ d ∷ Γ ⊢ renameᵗ (raiseVarFrom (length Φ)) A ~
                   renameᵗ (raiseVarFrom (length Φ)) B
insert-mode-~ ★-~-★ = ★-~-★
insert-mode-~ (X-~-X x∈) = X-~-X (insert-mode-∋ᶜ x∈)
insert-mode-~ ι-~-ι = ι-~-ι
insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (⇒-~-⇒ A~B C~D) =
  ⇒-~-⇒ (insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} A~B)
         (insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} C~D)
insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (∀-~-∀ A~B) =
  ∀-~-∀
    (cong-~ (sym (rename-raise-ext (length Φ) _))
            (sym (rename-raise-ext (length Φ) _))
      (insert-mode-~ {d = d} {Φ = X~X ∷ Φ} {Γ = Γ} A~B))
insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (A-~-★ n★ n∀ g A~G) =
  A-~-★ (renameᵗ-preserves-Non★ n★) (renameᵗ-preserves-Non∀ _ n∀)
    (renameᵗ-ground _ g)
    (insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} A~G)
insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (★-~-B n★ n∀ g G~B) =
  ★-~-B (renameᵗ-preserves-Non★ n★) (renameᵗ-preserves-Non∀ _ n∀)
    (renameᵗ-ground _ g)
    (insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} G~B)
insert-mode-~ (νX-~-★ x∈) = νX-~-★ (insert-mode-∋ᶜ x∈)
insert-mode-~ (★-~-νX x∈) = ★-~-νX (insert-mode-∋ᶜ x∈)
insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (∀-~-B {A = A} occA wfB A~⇑B) =
  ∀-~-B
    (trans (occurs-rename-ext-raise-zero (length Φ) A) occA)
    (insert-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} wfB)
    (cong-~ (sym (rename-raise-ext (length Φ) _))
            (rename-raise-⇑ᵗ (length Φ) _)
      (insert-mode-~ {d = d} {Φ = X~★ ∷ Φ} {Γ = Γ} A~⇑B))
insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (A-~-∀ {B = B} occB wfA ⇑A~B) =
  A-~-∀
    (trans (occurs-rename-ext-raise-zero (length Φ) B) occB)
    (insert-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} wfA)
    (cong-~ (rename-raise-⇑ᵗ (length Φ) _)
            (sym (rename-raise-ext (length Φ) _))
      (insert-mode-~ {d = d} {Φ = ★~X ∷ Φ} {Γ = Γ} ⇑A~B))

height-cong-~ :
  ∀ {Γ A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (A~B : Γ ⊢ A ~ B) →
  height~ (cong-~ eqA eqB A~B) ≡ height~ A~B
height-cong-~ refl refl A~B = refl

height-insert-mode-~ :
  ∀ {d : CMode} {Φ Γ : CCtx} {A B} →
  (A~B : Φ ++ Γ ⊢ A ~ B) →
  height~ (insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} A~B) ≡ height~ A~B
height-insert-mode-~ ★-~-★ = refl
height-insert-mode-~ (X-~-X x∈) = refl
height-insert-mode-~ ι-~-ι = refl
height-insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (⇒-~-⇒ A~B C~D)
  rewrite height-insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} A~B
        | height-insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} C~D = refl
height-insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (∀-~-∀ A~B)
  rewrite height-cong-~
            (sym (rename-raise-ext (length Φ) _))
            (sym (rename-raise-ext (length Φ) _))
            (insert-mode-~ {d = d} {Φ = X~X ∷ Φ} {Γ = Γ} A~B)
        | height-insert-mode-~ {d = d} {Φ = X~X ∷ Φ} {Γ = Γ} A~B = refl
height-insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (A-~-★ n★ n∀ g A~G)
  rewrite height-insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} A~G = refl
height-insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (★-~-B n★ n∀ g G~B)
  rewrite height-insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} G~B = refl
height-insert-mode-~ (νX-~-★ x∈) = refl
height-insert-mode-~ (★-~-νX x∈) = refl
height-insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (∀-~-B occA wfB A~⇑B)
  rewrite height-cong-~
            (sym (rename-raise-ext (length Φ) _))
            (rename-raise-⇑ᵗ (length Φ) _)
            (insert-mode-~ {d = d} {Φ = X~★ ∷ Φ} {Γ = Γ} A~⇑B)
        | height-insert-mode-~ {d = d} {Φ = X~★ ∷ Φ} {Γ = Γ} A~⇑B = refl
height-insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} (A-~-∀ occB wfA ⇑A~B)
  rewrite height-cong-~
            (rename-raise-⇑ᵗ (length Φ) _)
            (sym (rename-raise-ext (length Φ) _))
            (insert-mode-~ {d = d} {Φ = ★~X ∷ Φ} {Γ = Γ} ⇑A~B)
        | height-insert-mode-~ {d = d} {Φ = ★~X ∷ Φ} {Γ = Γ} ⇑A~B = refl

coerce-⊒-cong-~ :
  ∀ {Γ A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (A~B : Γ ⊢ A ~ B) →
  coerce-⊒ (cong-~ eqA eqB A~B) ≡ coerce-⊒ A~B
coerce-⊒-cong-~ refl refl A~B = refl

coerce-⊑-cong-~ :
  ∀ {Γ A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (A~B : Γ ⊢ A ~ B) →
  coerce-⊑ (cong-~ eqA eqB A~B) ≡ coerce-⊑ A~B
coerce-⊑-cong-~ refl refl A~B = refl

coerce-⊒-insert-mode :
  ∀ {d : CMode} {Φ Γ : CCtx} {A B} →
  (A~B : Φ ++ Γ ⊢ A ~ B) →
  rename⊑ (raiseVarFrom (length Φ)) (coerce-⊒ A~B) ≡
  coerce-⊒ (insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} A~B)
coerce-⊑-insert-mode :
  ∀ {d : CMode} {Φ Γ : CCtx} {A B} →
  (A~B : Φ ++ Γ ⊢ A ~ B) →
  rename⊑ (raiseVarFrom (length Φ)) (coerce-⊑ A~B) ≡
  coerce-⊑ (insert-mode-~ {d = d} {Φ = Φ} {Γ = Γ} A~B)

coerce-⊒-insert-mode ★-~-★ = refl
coerce-⊒-insert-mode (X-~-X x∈) = refl
coerce-⊒-insert-mode ι-~-ι = refl
coerce-⊒-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (⇒-~-⇒ A~B C~D) =
  cong₂ _↦_ (coerce-⊒-insert-mode {d = d} {Φ = Φ} {Γ = Γ} A~B)
             (coerce-⊒-insert-mode {d = d} {Φ = Φ} {Γ = Γ} C~D)
coerce-⊒-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (∀-~-∀ A~B) =
  cong (λ p → ‵∀ p)
    (trans (rename⊑-cong (raise-ext (length Φ)) (coerce-⊒ A~B))
      (trans
        (coerce-⊒-insert-mode {d = d} {Φ = X~X ∷ Φ} {Γ = Γ} A~B)
        (sym (coerce-⊒-cong-~
          (sym (rename-raise-ext (length Φ) _))
          (sym (rename-raise-ext (length Φ) _))
          (insert-mode-~ {d = d} {Φ = X~X ∷ Φ} {Γ = Γ} A~B)))))
coerce-⊒-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (A-~-★ n★ n∀ g A~G) =
  coerce-⊒-insert-mode {d = d} {Φ = Φ} {Γ = Γ} A~G
coerce-⊒-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (★-~-B n★ n∀ g G~B) =
  cong (λ p → p !)
    (coerce-⊒-insert-mode {d = d} {Φ = Φ} {Γ = Γ} G~B)
coerce-⊒-insert-mode (νX-~-★ x∈) = refl
coerce-⊒-insert-mode (★-~-νX x∈) = refl
coerce-⊒-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (∀-~-B occA wfB A~⇑B) =
  cong (λ p → ‵∀ p)
    (trans (rename⊑-cong (raise-ext (length Φ)) (coerce-⊒ A~⇑B))
      (trans
        (coerce-⊒-insert-mode {d = d} {Φ = X~★ ∷ Φ} {Γ = Γ} A~⇑B)
        (sym (coerce-⊒-cong-~
          (sym (rename-raise-ext (length Φ) _))
          (rename-raise-⇑ᵗ (length Φ) _)
          (insert-mode-~ {d = d} {Φ = X~★ ∷ Φ} {Γ = Γ} A~⇑B)))))
coerce-⊒-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (A-~-∀ occB wfA ⇑A~B) =
  cong (λ p → ν p)
    (trans (rename⊑-cong (raise-ext (length Φ)) (coerce-⊒ ⇑A~B))
      (trans
        (coerce-⊒-insert-mode {d = d} {Φ = ★~X ∷ Φ} {Γ = Γ} ⇑A~B)
        (sym (coerce-⊒-cong-~
          (rename-raise-⇑ᵗ (length Φ) _)
          (sym (rename-raise-ext (length Φ) _))
          (insert-mode-~ {d = d} {Φ = ★~X ∷ Φ} {Γ = Γ} ⇑A~B)))))

coerce-⊑-insert-mode ★-~-★ = refl
coerce-⊑-insert-mode (X-~-X x∈) = refl
coerce-⊑-insert-mode ι-~-ι = refl
coerce-⊑-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (⇒-~-⇒ A~B C~D) =
  cong₂ _↦_ (coerce-⊑-insert-mode {d = d} {Φ = Φ} {Γ = Γ} A~B)
             (coerce-⊑-insert-mode {d = d} {Φ = Φ} {Γ = Γ} C~D)
coerce-⊑-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (∀-~-∀ A~B) =
  cong (λ p → ‵∀ p)
    (trans (rename⊑-cong (raise-ext (length Φ)) (coerce-⊑ A~B))
      (trans
        (coerce-⊑-insert-mode {d = d} {Φ = X~X ∷ Φ} {Γ = Γ} A~B)
        (sym (coerce-⊑-cong-~
          (sym (rename-raise-ext (length Φ) _))
          (sym (rename-raise-ext (length Φ) _))
          (insert-mode-~ {d = d} {Φ = X~X ∷ Φ} {Γ = Γ} A~B)))))
coerce-⊑-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (A-~-★ n★ n∀ g A~G) =
  cong (λ p → p !)
    (coerce-⊑-insert-mode {d = d} {Φ = Φ} {Γ = Γ} A~G)
coerce-⊑-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (★-~-B n★ n∀ g G~B) =
  coerce-⊑-insert-mode {d = d} {Φ = Φ} {Γ = Γ} G~B
coerce-⊑-insert-mode (νX-~-★ x∈) = refl
coerce-⊑-insert-mode (★-~-νX x∈) = refl
coerce-⊑-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (∀-~-B occA wfB A~⇑B) =
  cong (λ p → ν p)
    (trans (rename⊑-cong (raise-ext (length Φ)) (coerce-⊑ A~⇑B))
      (trans
        (coerce-⊑-insert-mode {d = d} {Φ = X~★ ∷ Φ} {Γ = Γ} A~⇑B)
        (sym (coerce-⊑-cong-~
          (sym (rename-raise-ext (length Φ) _))
          (rename-raise-⇑ᵗ (length Φ) _)
          (insert-mode-~ {d = d} {Φ = X~★ ∷ Φ} {Γ = Γ} A~⇑B)))))
coerce-⊑-insert-mode {d = d} {Φ = Φ} {Γ = Γ} (A-~-∀ occB wfA ⇑A~B) =
  cong (λ p → ‵∀ p)
    (trans (rename⊑-cong (raise-ext (length Φ)) (coerce-⊑ ⇑A~B))
      (trans
        (coerce-⊑-insert-mode {d = d} {Φ = ★~X ∷ Φ} {Γ = Γ} ⇑A~B)
        (sym (coerce-⊑-cong-~
          (rename-raise-⇑ᵗ (length Φ) _)
          (sym (rename-raise-ext (length Φ) _))
          (insert-mode-~ {d = d} {Φ = ★~X ∷ Φ} {Γ = Γ} ⇑A~B)))))

coerce-wt : ∀ {Γ A C} →
  (A~C : Γ ⊢ A ~ C) →
    ∃[ B ]
    (0 ∣ leftICtx Γ ⊢ proj₁ (coerce A~C) ⦂ A ⊒ B) ×
    (0 ∣ rightICtx Γ ⊢ proj₂ (coerce A~C) ⦂ B ⊑ C)
coerce-wt ★-~-★ =
  ★ , ⊢★-⊑-★ , ⊢★-⊑-★
coerce-wt (X-~-X {X} x∈) =
  ＇ X ,
  ⊢X-⊑-X (left-lookup-both x∈) ,
  ⊢X-⊑-X (right-lookup-both x∈)
coerce-wt ι-~-ι =
  ‵ _ , ⊢ι-⊑-ι , ⊢ι-⊑-ι
coerce-wt (⇒-~-⇒ A~A′ B~B′)
    with coerce A~A′ | coerce B~B′ | coerce-wt A~A′ | coerce-wt B~B′
coerce-wt (⇒-~-⇒ A~A′ B~B′)
    | pA⊒ , pA⊑
    | pB⊒ , pB⊑
    | Aₘ , pA⊒⊢ , pA⊑⊢
    | Bₘ , pB⊒⊢ , pB⊑⊢ =
  Aₘ ⇒ Bₘ ,
  ⊢A⇒B-⊑-A′⇒B′ pA⊒⊢ pB⊒⊢ ,
  ⊢A⇒B-⊑-A′⇒B′ pA⊑⊢ pB⊑⊢
coerce-wt (∀-~-∀ A~B) with coerce A~B | coerce-wt A~B
coerce-wt (∀-~-∀ A~B) | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊢∀A-⊑-∀B p⊒⊢ , ⊢∀A-⊑-∀B p⊑⊢
coerce-wt (A-~-★ n★ n∀ g A~G) with coerce A~G | coerce-wt A~G
coerce-wt (A-~-★ n★ n∀ g A~G) | p⊒ , p⊑ | B , p⊒⊢ , p⊑⊢ =
  B ,
  p⊒⊢ , ⊢A-⊑-★ g p⊑⊢
coerce-wt (★-~-B n★ n∀ h H~B) with coerce H~B | coerce-wt H~B
coerce-wt (★-~-B n★ n∀ h H~B) | p⊒ , p⊑ | B , p⊒⊢ , p⊑⊢ =
  B ,
  ⊢A-⊑-★ h p⊒⊢ , p⊑⊢
coerce-wt (νX-~-★ {X} x∈) =
  ＇ X ,
  ⊢X-⊑-X (left-lookup-left x∈) ,
  ⊢X-⊑-★ (right-lookup-left x∈)
coerce-wt (★-~-νX {X} x∈) =
  ＇ X ,
  ⊢X-⊑-★ (left-lookup-right x∈) ,
  ⊢X-⊑-X (right-lookup-right x∈)
coerce-wt {Γ = Γ} (∀-~-B {B = B} occA wfB A~⇑B)
    with coerce A~⇑B | coerce-wt A~⇑B
coerce-wt {Γ = Γ} (∀-~-B {B = B} occA wfB A~⇑B)
    | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊢∀A-⊑-∀B p⊒⊢ ,
  ⊢∀A-⊑-B (plain-target-occurs-source here p⊒⊢ occA)
    (wf-rightICtx {Γ = Γ} wfB) p⊑⊢
coerce-wt {Γ = Γ} (A-~-∀ {A = A} occB wfA ⇑A~B)
    with coerce ⇑A~B | coerce-wt ⇑A~B
coerce-wt {Γ = Γ} (A-~-∀ {A = A} occB wfA ⇑A~B)
    | p⊒ , p⊑ | Bₘ , p⊒⊢ , p⊑⊢ =
  `∀ Bₘ ,
  ⊢∀A-⊑-B (plain-target-occurs-source here p⊑⊢ occB)
    (wf-leftICtx {Γ = Γ} wfA) p⊒⊢ ,
  ⊢∀A-⊑-∀B p⊑⊢

coerce-wt-extend-X⊑X :
  ∀ {Δ A C} →
  (A~C : extend-X~X Δ [] ⊢ A ~ C) →
  ∃[ B ]
    ((0 ∣ extend-X⊑X Δ [] ⊢ coerce-⊒ A~C ⦂ A ⊒ B) ×
     (0 ∣ extend-X⊑X Δ [] ⊢ coerce-⊑ A~C ⦂ B ⊑ C))
coerce-wt-extend-X⊑X {Δ = Δ} A~C with coerce-wt A~C
coerce-wt-extend-X⊑X {Δ = Δ} A~C | B , p⊒⊢ , p⊑⊢
  rewrite leftICtx-extend-X~X[] Δ | rightICtx-extend-X~X[] Δ =
  B , p⊒⊢ , p⊑⊢

coerce-⊒-tgt :
  ∀ {Γ A C} →
  (A~C : Γ ⊢ A ~ C) →
  tgt⊑ (coerce-⊒ A~C) ≡ A
coerce-⊒-tgt ★-~-★ = refl
coerce-⊒-tgt (X-~-X x∈) = refl
coerce-⊒-tgt ι-~-ι = refl
coerce-⊒-tgt (⇒-~-⇒ A~A′ B~B′) =
  cong₂ _⇒_ (coerce-⊒-tgt A~A′) (coerce-⊒-tgt B~B′)
coerce-⊒-tgt (∀-~-∀ A~B) =
  cong `∀ (coerce-⊒-tgt A~B)
coerce-⊒-tgt (A-~-★ n★ n∀ g A~G) =
  coerce-⊒-tgt A~G
coerce-⊒-tgt (★-~-B n★ n∀ g G~B) = refl
coerce-⊒-tgt (νX-~-★ x∈) = refl
coerce-⊒-tgt (★-~-νX x∈) = refl
coerce-⊒-tgt (∀-~-B occA wfB A~⇑B) =
  cong `∀ (coerce-⊒-tgt A~⇑B)
coerce-⊒-tgt {A = A} (A-~-∀ occB wfA ⇑A~B) =
  trans (cong (dropTyFrom zero) (coerce-⊒-tgt ⇑A~B))
        (dropTyFrom-raise-same zero A)

coerce-⊑-tgt :
  ∀ {Γ A C} →
  (A~C : Γ ⊢ A ~ C) →
  tgt⊑ (coerce-⊑ A~C) ≡ C
coerce-⊑-tgt ★-~-★ = refl
coerce-⊑-tgt (X-~-X x∈) = refl
coerce-⊑-tgt ι-~-ι = refl
coerce-⊑-tgt (⇒-~-⇒ A~A′ B~B′) =
  cong₂ _⇒_ (coerce-⊑-tgt A~A′) (coerce-⊑-tgt B~B′)
coerce-⊑-tgt (∀-~-∀ A~B) =
  cong `∀ (coerce-⊑-tgt A~B)
coerce-⊑-tgt (A-~-★ n★ n∀ g A~G) = refl
coerce-⊑-tgt (★-~-B n★ n∀ g G~B) =
  coerce-⊑-tgt G~B
coerce-⊑-tgt (νX-~-★ x∈) = refl
coerce-⊑-tgt (★-~-νX x∈) = refl
coerce-⊑-tgt {C = C} (∀-~-B occA wfC A~⇑C) =
  trans (cong (dropTyFrom zero) (coerce-⊑-tgt A~⇑C))
        (dropTyFrom-raise-same zero C)
coerce-⊑-tgt (A-~-∀ occB wfA ⇑A~B) =
  cong `∀ (coerce-⊑-tgt ⇑A~B)

mutual
  right-consistent-star-⊑ :
    ∀ {Γ Φ A} →
    Γ ⊢ A ~ ★ →
    rightICtx Γ ≤ᵢ Φ →
    ∃[ p ] 0 ∣ Φ ⊢ p ⦂ A ⊑ ★
  right-consistent-star-⊑ ★-~-★ Γ≤Φ =
    id★ , ⊢★-⊑-★
  right-consistent-star-⊑ (A-~-★ n★′ n∀ g A~G) Γ≤Φ
      with right-consistent-ground-⊑ n★′ n∀ g A~G Γ≤Φ
  ... | p , p⊢ = p ! , ⊢A-⊑-★ g p⊢
  right-consistent-star-⊑ (νX-~-★ x∈) Γ≤Φ =
    ‵ _ ! , ⊢X-⊑-★ (≤ᵢ-ν-lookup Γ≤Φ (right-lookup-left x∈))
  right-consistent-star-⊑ (∀-~-B {B = ★} occA wf★ A~⇑★) Γ≤Φ
      with right-consistent-star-⊑ A~⇑★ (ν≤ν ∷≤ᵢ Γ≤Φ)
  ... | p , p⊢ =
    ν p , ⊢∀A-⊑-B occA wf★ p⊢

  left-consistent-star-⊑ :
    ∀ {Γ Φ B} →
    Γ ⊢ ★ ~ B →
    leftICtx Γ ≤ᵢ Φ →
    ∃[ p ] 0 ∣ Φ ⊢ p ⦂ B ⊑ ★
  left-consistent-star-⊑ ★-~-★ Γ≤Φ =
    id★ , ⊢★-⊑-★
  left-consistent-star-⊑ (★-~-B n★′ n∀ g G~B) Γ≤Φ
      with left-consistent-ground-⊑ n★′ n∀ g G~B Γ≤Φ
  ... | p , p⊢ = p ! , ⊢A-⊑-★ g p⊢
  left-consistent-star-⊑ (★-~-νX x∈) Γ≤Φ =
    ‵ _ ! , ⊢X-⊑-★ (≤ᵢ-ν-lookup Γ≤Φ (left-lookup-right x∈))
  left-consistent-star-⊑ (A-~-∀ {A = ★} occB wf★ ★~B) Γ≤Φ
      with left-consistent-star-⊑ ★~B (ν≤ν ∷≤ᵢ Γ≤Φ)
  ... | p , p⊢ =
    ν p , ⊢∀A-⊑-B occB wf★ p⊢

  right-consistent-ground-⊑ :
    ∀ {Γ Φ A G} →
    Non★ A →
    Non∀ A →
    Ground G →
    Γ ⊢ A ~ G →
    rightICtx Γ ≤ᵢ Φ →
    ∃[ p ] 0 ∣ Φ ⊢ p ⦂ A ⊑ G
  right-consistent-ground-⊑ non★-‵ non∀-‵ (‵ ι) ι-~-ι Γ≤Φ =
    idι ι , ⊢ι-⊑-ι
  right-consistent-ground-⊑ {G = ★ ⇒ ★} non★-⇒ non∀-⇒ ★⇒★
      (⇒-~-⇒ A~★ B~★) Γ≤Φ
      with right-consistent-star-⊑ A~★ Γ≤Φ
         | right-consistent-star-⊑ B~★ Γ≤Φ
  ... | p , p⊢ | q , q⊢ =
    p ↦ q , ⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢

  left-consistent-ground-⊑ :
    ∀ {Γ Φ G B} →
    Non★ B →
    Non∀ B →
    Ground G →
    Γ ⊢ G ~ B →
    leftICtx Γ ≤ᵢ Φ →
    ∃[ p ] 0 ∣ Φ ⊢ p ⦂ B ⊑ G
  left-consistent-ground-⊑ non★-‵ non∀-‵ (‵ ι) ι-~-ι Γ≤Φ =
    idι ι , ⊢ι-⊑-ι
  left-consistent-ground-⊑ {G = ★ ⇒ ★} non★-⇒ non∀-⇒ ★⇒★
      (⇒-~-⇒ ★~A ★~B) Γ≤Φ
      with left-consistent-star-⊑ ★~A Γ≤Φ
         | left-consistent-star-⊑ ★~B Γ≤Φ
  ... | p , p⊢ | q , q⊢ =
    p ↦ q , ⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢

sameCCtx : VarPrecCtx → CCtx

leftICtx-sameCCtx : ∀ Φ → leftICtx (sameCCtx Φ) ≡ Φ

rightICtx-sameCCtx : ∀ Φ → rightICtx (sameCCtx Φ) ≡ Φ

coerce-glbᶜ :
  ∀ {Γ Φ A C B B′ p⊒ p⊑ pA pC} →
  (A~C : Γ ⊢ A ~ C) →
  leftICtx Γ ≤ᵢ Φ →
  rightICtx Γ ≤ᵢ Φ →
  0 ∣ leftICtx Γ ⊢ p⊒ ⦂ B ⊑ A →
  0 ∣ rightICtx Γ ⊢ p⊑ ⦂ B ⊑ C →
  0 ∣ Φ ⊢ pA ⦂ B′ ⊑ A →
  0 ∣ Φ ⊢ pC ⦂ B′ ⊑ C →
  p⊒ ≡ coerce-⊒ A~C →
  p⊑ ≡ coerce-⊑ A~C →
  ∃[ r ] 0 ∣ Φ ⊢ r ⦂ B′ ⊑ B

mode-at : VarPrecCtx → TyVar → VarPrec
mode-at [] X = X⊑X
mode-at (m ∷ Φ) zero = m
mode-at (m ∷ Φ) (suc X) = mode-at Φ X

mode-at-∋ :
  ∀ {Φ X m} →
  Φ ∋ X ∶ m →
  mode-at Φ X ≡ m
mode-at-∋ here = refl
mode-at-∋ (there x∈) = mode-at-∋ x∈

mode-at-< :
  ∀ {Φ X} →
  X < length Φ →
  Φ ∋ X ∶ mode-at Φ X
mode-at-< {Φ = []} ()
mode-at-< {Φ = m ∷ Φ} {X = zero} z<s = here
mode-at-< {Φ = m ∷ Φ} {X = suc X} (s<s X<Φ) =
  there (mode-at-< X<Φ)

mode-at-≤ᵢ :
  ∀ {Φ Φ′ X} →
  Φ ≤ᵢ Φ′ →
  ModeLe (mode-at Φ X) (mode-at Φ′ X)
mode-at-≤ᵢ []≤ᵢ = X⊑X≤X⊑X
mode-at-≤ᵢ {X = zero} (m≤m′ ∷≤ᵢ Φ≤Φ′) = m≤m′
mode-at-≤ᵢ {X = suc X} (m≤m′ ∷≤ᵢ Φ≤Φ′) =
  mode-at-≤ᵢ {X = X} Φ≤Φ′

X⊑X≢X⊑★ : X⊑X ≡ X⊑★ → ⊥
X⊑X≢X⊑★ ()

map-ν-vars : VarPrecCtx → Ty → Ty
map-ν-vars Φ (＇ X) with mode-at Φ X
... | X⊑X = ＇ X
... | X⊑★ = ★
map-ν-vars Φ (｀ α) = ｀ α
map-ν-vars Φ (‵ ι) = ‵ ι
map-ν-vars Φ ★ = ★
map-ν-vars Φ (A ⇒ B) = map-ν-vars Φ A ⇒ map-ν-vars Φ B
map-ν-vars Φ (`∀ A) = `∀ (map-ν-vars (X⊑X ∷ Φ) A)

data TargetOk (Γ : VarPrecCtx) : Ty → Set where
  ok-X : ∀ {X} → Γ ∋ X ∶ X⊑X → TargetOk Γ (＇ X)
  ok-｀ : ∀ {α} → TargetOk Γ (｀ α)
  ok-‵ : ∀ {ι} → TargetOk Γ (‵ ι)
  ok-★ : TargetOk Γ ★
  ok-⇒ : ∀ {A B} → TargetOk Γ A → TargetOk Γ B → TargetOk Γ (A ⇒ B)
  ok-∀ : ∀ {A} → TargetOk (X⊑X ∷ Γ) A → TargetOk Γ (`∀ A)

dropTargetVar :
  ∀ n {Γ X} →
  extend-X⊑X n (X⊑★ ∷ Γ) ∋ X ∶ X⊑X →
  TyVar
dropTargetVar zero (there {X = X} x∈) = X
dropTargetVar (suc n) here = zero
dropTargetVar (suc n) (there x∈) = suc (dropTargetVar n x∈)

dropTargetVar∈ :
  ∀ n {Γ X}
    (x∈ : extend-X⊑X n (X⊑★ ∷ Γ) ∋ X ∶ X⊑X) →
  extend-X⊑X n Γ ∋ dropTargetVar n x∈ ∶ X⊑X
dropTargetVar∈ zero (there x∈) = x∈
dropTargetVar∈ (suc n) here = here
dropTargetVar∈ (suc n) (there x∈) =
  there (dropTargetVar∈ n x∈)

dropTargetVar-eq :
  ∀ n {Γ X}
    (x∈ : extend-X⊑X n (X⊑★ ∷ Γ) ∋ X ∶ X⊑X) →
  X ≡ raiseVarFrom n (dropTargetVar n x∈)
dropTargetVar-eq zero (there x∈) = refl
dropTargetVar-eq (suc n) here = refl
dropTargetVar-eq (suc n) (there x∈) =
  cong suc (dropTargetVar-eq n x∈)

dropTargetFrom :
  ∀ n {Γ A} →
  TargetOk (extend-X⊑X n (X⊑★ ∷ Γ)) A →
  Ty
dropTargetFrom n (ok-X x∈) = ＇ (dropTargetVar n x∈)
dropTargetFrom n (ok-｀ {α = α}) = ｀ α
dropTargetFrom n (ok-‵ {ι = ι}) = ‵ ι
dropTargetFrom n ok-★ = ★
dropTargetFrom n (ok-⇒ okA okB) =
  dropTargetFrom n okA ⇒ dropTargetFrom n okB
dropTargetFrom n (ok-∀ okA) = `∀ (dropTargetFrom (suc n) okA)

dropTargetFrom-ok :
  ∀ n {Γ A}
    (ok : TargetOk (extend-X⊑X n (X⊑★ ∷ Γ)) A) →
  TargetOk (extend-X⊑X n Γ) (dropTargetFrom n ok)
dropTargetFrom-ok n (ok-X x∈) = ok-X (dropTargetVar∈ n x∈)
dropTargetFrom-ok n ok-｀ = ok-｀
dropTargetFrom-ok n ok-‵ = ok-‵
dropTargetFrom-ok n ok-★ = ok-★
dropTargetFrom-ok n (ok-⇒ okA okB) =
  ok-⇒ (dropTargetFrom-ok n okA) (dropTargetFrom-ok n okB)
dropTargetFrom-ok n (ok-∀ okA) = ok-∀ (dropTargetFrom-ok (suc n) okA)

dropTargetFrom-WfTy :
  ∀ n {Γ Ψ A} →
  WfTy (length (extend-X⊑X n (X⊑★ ∷ Γ))) Ψ A →
  (ok : TargetOk (extend-X⊑X n (X⊑★ ∷ Γ)) A) →
  WfTy (length (extend-X⊑X n Γ)) Ψ (dropTargetFrom n ok)
dropTargetFrom-WfTy n wfA (ok-X x∈) =
  wfVar (∋→< (dropTargetVar∈ n x∈))
dropTargetFrom-WfTy n (wfSeal α<Ψ) (ok-｀ {α = α}) = wfSeal α<Ψ
dropTargetFrom-WfTy n wfBase (ok-‵ {ι = ι}) = wfBase
dropTargetFrom-WfTy n wf★ ok-★ = wf★
dropTargetFrom-WfTy n (wf⇒ wfA wfB) (ok-⇒ okA okB) =
  wf⇒ (dropTargetFrom-WfTy n wfA okA)
      (dropTargetFrom-WfTy n wfB okB)
dropTargetFrom-WfTy n (wf∀ wfA) (ok-∀ okA) =
  wf∀ (dropTargetFrom-WfTy (suc n) wfA okA)

dropTargetFrom-eq :
  ∀ n {Γ A}
    (ok : TargetOk (extend-X⊑X n (X⊑★ ∷ Γ)) A) →
  A ≡ renameᵗ (raiseVarFrom n) (dropTargetFrom n ok)
dropTargetFrom-eq n (ok-X x∈) =
  cong ＇_ (dropTargetVar-eq n x∈)
dropTargetFrom-eq n (ok-｀ {α = α}) = refl
dropTargetFrom-eq n (ok-‵ {ι = ι}) = refl
dropTargetFrom-eq n ok-★ = refl
dropTargetFrom-eq n (ok-⇒ okA okB) =
  cong₂ _⇒_ (dropTargetFrom-eq n okA) (dropTargetFrom-eq n okB)
dropTargetFrom-eq n (ok-∀ okA) =
  cong `∀ (trans (dropTargetFrom-eq (suc n) okA)
    (sym (rename-raise-ext n (dropTargetFrom (suc n) okA))))

occurs-map-ν-vars-preserve-X⊑X :
  ∀ {Φ A X} →
  mode-at Φ X ≡ X⊑X →
  occurs X (map-ν-vars Φ A) ≡ occurs X A
occurs-map-ν-vars-preserve-X⊑X {Φ = Φ} {A = ＇ Y} {X = X} mX
    with mode-at Φ Y in eqY | X ≟ Y
occurs-map-ν-vars-preserve-X⊑X {A = ＇ Y} {X = X} mX
    | X⊑X | yes refl rewrite mX with Y ≟ Y
occurs-map-ν-vars-preserve-X⊑X {A = ＇ Y} {X = Y} mX
    | X⊑X | yes refl | yes refl = refl
occurs-map-ν-vars-preserve-X⊑X {A = ＇ Y} {X = Y} mX
    | X⊑X | yes refl | no neq = ⊥-elim (neq refl)
occurs-map-ν-vars-preserve-X⊑X {A = ＇ Y} {X = X} mX
    | X⊑X | no neq with X ≟ Y
occurs-map-ν-vars-preserve-X⊑X {A = ＇ Y} {X = X} mX
    | X⊑X | no neq | yes eq = ⊥-elim (neq eq)
occurs-map-ν-vars-preserve-X⊑X {A = ＇ Y} {X = X} mX
    | X⊑X | no neq | no neq′ = refl
occurs-map-ν-vars-preserve-X⊑X {Φ = Φ} {A = ＇ Y} {X = X} mX
    | X⊑★ | yes refl =
  ⊥-elim (X⊑X≢X⊑★ (trans (sym mX) eqY))
occurs-map-ν-vars-preserve-X⊑X {A = ＇ Y} {X = X} mX
    | X⊑★ | no neq with X ≟ Y
occurs-map-ν-vars-preserve-X⊑X {A = ＇ Y} {X = X} mX
    | X⊑★ | no neq | yes eq = ⊥-elim (neq eq)
occurs-map-ν-vars-preserve-X⊑X {A = ＇ Y} {X = X} mX
    | X⊑★ | no neq | no neq′ = refl
occurs-map-ν-vars-preserve-X⊑X {A = ｀ α} mX = refl
occurs-map-ν-vars-preserve-X⊑X {A = ‵ ι} mX = refl
occurs-map-ν-vars-preserve-X⊑X {A = ★} mX = refl
occurs-map-ν-vars-preserve-X⊑X {A = A ⇒ B} {X = X} mX =
  cong₂ _∨_
    (occurs-map-ν-vars-preserve-X⊑X {A = A} {X = X} mX)
    (occurs-map-ν-vars-preserve-X⊑X {A = B} {X = X} mX)
occurs-map-ν-vars-preserve-X⊑X {Φ = Φ} {A = `∀ A} {X = X} mX =
  occurs-map-ν-vars-preserve-X⊑X
    {Φ = X⊑X ∷ Φ}
    {A = A}
    {X = suc X}
    mX

wfVar-cast :
  ∀ {Γ Γ′ X} →
  Γ ≤ᵢ Γ′ →
  X < length Γ →
  X < length Γ′
wfVar-cast {X = X} Γ≤Γ′ X<Γ =
  subst (λ n → X < n) (≤ᵢ-length Γ≤Γ′) X<Γ

map-ν-vars-upper-wf :
  ∀ {Φ A} →
  WfTy (length Φ) 0 A →
  ∃[ p ] 0 ∣ Φ ⊢ p ⦂ A ⊑ map-ν-vars Φ A
map-ν-vars-upper-wf {Φ = Φ} {A = ＇ X} (wfVar X<Φ)
    with mode-at Φ X in eqX
... | X⊑X =
  idₓ X ,
  ⊢X-⊑-X (subst (λ m → Φ ∋ X ∶ m) eqX (mode-at-< X<Φ))
... | X⊑★ =
  ‵ X ! ,
  ⊢X-⊑-★ (subst (λ m → Φ ∋ X ∶ m) eqX (mode-at-< X<Φ))
map-ν-vars-upper-wf {A = ｀ α} (wfSeal wfα) =
  idₛ α , ⊢α-⊑-α (wfSeal wfα)
map-ν-vars-upper-wf {A = ‵ ι} wfBase =
  idι ι , ⊢ι-⊑-ι
map-ν-vars-upper-wf {A = ★} wf★ =
  id★ , ⊢★-⊑-★
map-ν-vars-upper-wf {Φ = Φ} {A = A ⇒ B} (wf⇒ wfA wfB)
    with map-ν-vars-upper-wf {Φ = Φ} {A = A} wfA
       | map-ν-vars-upper-wf {Φ = Φ} {A = B} wfB
... | pA , pA⊢ | pB , pB⊢ =
  pA ↦ pB , ⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢
map-ν-vars-upper-wf {Φ = Φ} {A = `∀ A} (wf∀ wfA)
    with map-ν-vars-upper-wf {Φ = X⊑X ∷ Φ} {A = A} wfA
... | pA , pA⊢ =
  ‵∀ pA , ⊢∀A-⊑-∀B pA⊢

map-ν-vars-mono-wf :
  ∀ {Φ Φ′ A} →
  Φ ≤ᵢ Φ′ →
  WfTy (length Φ) 0 A →
  ∃[ p ] 0 ∣ Φ′ ⊢ p ⦂ map-ν-vars Φ A ⊑ map-ν-vars Φ′ A
map-ν-vars-mono-wf {Φ = Φ} {Φ′ = Φ′} {A = ＇ X} Φ≤Φ′ (wfVar X<Φ)
    with mode-at Φ X
       | mode-at Φ′ X in eqX′
       | mode-at-≤ᵢ {Φ = Φ} {Φ′ = Φ′} {X = X} Φ≤Φ′
       | mode-at-< (wfVar-cast Φ≤Φ′ X<Φ)
map-ν-vars-mono-wf {Φ′ = Φ′} {A = ＇ X} Φ≤Φ′ (wfVar X<Φ)
    | X⊑X | X⊑X | X⊑X≤X⊑X | x∈ =
  idₓ X , ⊢X-⊑-X (subst (λ m → Φ′ ∋ X ∶ m) eqX′ x∈)
map-ν-vars-mono-wf {Φ′ = Φ′} {A = ＇ X} Φ≤Φ′ (wfVar X<Φ)
    | X⊑X | X⊑★ | X⊑X≤ν | x∈ =
  ‵ X ! , ⊢X-⊑-★ (subst (λ m → Φ′ ∋ X ∶ m) eqX′ x∈)
map-ν-vars-mono-wf {A = ＇ X} Φ≤Φ′ (wfVar X<Φ)
    | X⊑★ | X⊑★ | ν≤ν | x∈ =
  id★ , ⊢★-⊑-★
map-ν-vars-mono-wf {A = ｀ α} Φ≤Φ′ (wfSeal wfα) =
  idₛ α , ⊢α-⊑-α (wfSeal wfα)
map-ν-vars-mono-wf {A = ‵ ι} Φ≤Φ′ wfBase =
  idι ι , ⊢ι-⊑-ι
map-ν-vars-mono-wf {A = ★} Φ≤Φ′ wf★ =
  id★ , ⊢★-⊑-★
map-ν-vars-mono-wf {Φ = Φ} {Φ′ = Φ′} {A = A ⇒ B} Φ≤Φ′ (wf⇒ wfA wfB)
    with map-ν-vars-mono-wf {Φ = Φ} {Φ′ = Φ′} {A = A} Φ≤Φ′ wfA
       | map-ν-vars-mono-wf {Φ = Φ} {Φ′ = Φ′} {A = B} Φ≤Φ′ wfB
... | pA , pA⊢ | pB , pB⊢ =
  pA ↦ pB , ⊢A⇒B-⊑-A′⇒B′ pA⊢ pB⊢
map-ν-vars-mono-wf {Φ = Φ} {Φ′ = Φ′} {A = `∀ A} Φ≤Φ′ (wf∀ wfA)
    with map-ν-vars-mono-wf
      {Φ = X⊑X ∷ Φ}
      {Φ′ = X⊑X ∷ Φ′}
      {A = A}
      (X⊑X≤X⊑X ∷≤ᵢ Φ≤Φ′)
      wfA
... | pA , pA⊢ =
  ‵∀ pA , ⊢∀A-⊑-∀B pA⊢

map-ν-vars-to-target :
  ∀ {Φ A B p} →
  0 ∣ Φ ⊢ p ⦂ A ⊑ B →
  ∃[ q ] 0 ∣ Φ ⊢ q ⦂ map-ν-vars Φ A ⊑ B
map-ν-vars-to-target ⊢★-⊑-★ =
  id★ , ⊢★-⊑-★
map-ν-vars-to-target (⊢X-⊑-★ {X = X} xν)
    rewrite mode-at-∋ xν =
  id★ , ⊢★-⊑-★
map-ν-vars-to-target (⊢A-⊑-★ g p⊢)
    with map-ν-vars-to-target p⊢
... | q , q⊢ =
  q ! , ⊢A-⊑-★ g q⊢
map-ν-vars-to-target (⊢X-⊑-X {X = X} x∈)
    rewrite mode-at-∋ x∈ =
  idₓ X , ⊢X-⊑-X x∈
map-ν-vars-to-target (⊢α-⊑-α {α = α} wfα) =
  idₛ α , ⊢α-⊑-α wfα
map-ν-vars-to-target (⊢ι-⊑-ι {ι = ι}) =
  idι ι , ⊢ι-⊑-ι
map-ν-vars-to-target (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
    with map-ν-vars-to-target p⊢
       | map-ν-vars-to-target q⊢
... | p′ , p′⊢ | q′ , q′⊢ =
  p′ ↦ q′ , ⊢A⇒B-⊑-A′⇒B′ p′⊢ q′⊢
map-ν-vars-to-target (⊢∀A-⊑-∀B p⊢)
    with map-ν-vars-to-target p⊢
... | p′ , p′⊢ =
  ‵∀ p′ , ⊢∀A-⊑-∀B p′⊢
map-ν-vars-to-target {Φ = Φ} (⊢∀A-⊑-B {A = Aν} {B = B} occA wfB p⊢)
    with map-ν-vars-to-target p⊢
       | map-ν-vars-mono-wf
           {Φ = X⊑X ∷ Φ}
           {Φ′ = X⊑★ ∷ Φ}
           {A = Aν}
           (X⊑X≤ν ∷≤ᵢ ≤ᵢ-refl)
           (⊑-src-wf p⊢)
map-ν-vars-to-target {Φ = Φ}
    (⊢∀A-⊑-B {A = Aν} {B = B} occA wfB p⊢)
    | q , q⊢ | m , m⊢
    with trans-ctx-⊑ ≤ᵢ-refl m⊢ q⊢
... | r , r⊢ =
  ν r ,
  ⊢∀A-⊑-B
    (trans
      (occurs-map-ν-vars-preserve-X⊑X
        {Φ = X⊑X ∷ Φ}
        {A = Aν}
        {X = zero}
        refl)
      occA)
    wfB
    r⊢

strip-∀ : VarPrecCtx → Ty → Ty
strip-∀ Φ (＇ X) = map-ν-vars Φ (＇ X)
strip-∀ Φ (｀ α) = map-ν-vars Φ (｀ α)
strip-∀ Φ (‵ ι) = map-ν-vars Φ (‵ ι)
strip-∀ Φ ★ = map-ν-vars Φ ★
strip-∀ Φ (A ⇒ B) = map-ν-vars Φ (A ⇒ B)
strip-∀ Φ (`∀ A) = dropTyFrom zero (strip-∀ (X⊑★ ∷ Φ) A)

strip-∀-drop-eq :
  ∀ {Φ A} →
  (ok : TargetOk (X⊑★ ∷ Φ) A) →
  dropTyFrom zero A ≡ dropTargetFrom zero ok
strip-∀-drop-eq ok =
  trans
    (cong (dropTyFrom zero) (dropTargetFrom-eq zero ok))
    (dropTyFrom-raise-same zero (dropTargetFrom zero ok))

strip-∀-shift-eq :
  ∀ {Φ A} →
  (ok : TargetOk (X⊑★ ∷ Φ) A) →
  A ≡ ⇑ᵗ (dropTyFrom zero A)
strip-∀-shift-eq ok =
  trans
    (dropTargetFrom-eq zero ok)
    (cong (renameᵗ suc) (sym (strip-∀-drop-eq ok)))

map-ν-vars-target-ok-wf :
  ∀ {Φ A} →
  WfTy (length Φ) 0 A →
  TargetOk Φ (map-ν-vars Φ A)
map-ν-vars-target-ok-wf {Φ = Φ} {A = ＇ X} (wfVar X<Φ)
    with mode-at Φ X in eqX
... | X⊑X =
  ok-X (subst (λ m → Φ ∋ X ∶ m) eqX (mode-at-< X<Φ))
... | X⊑★ = ok-★
map-ν-vars-target-ok-wf {A = ｀ α} (wfSeal wfα) = ok-｀
map-ν-vars-target-ok-wf {A = ‵ ι} wfBase = ok-‵
map-ν-vars-target-ok-wf {A = ★} wf★ = ok-★
map-ν-vars-target-ok-wf {Φ = Φ} {A = A ⇒ B} (wf⇒ wfA wfB) =
  ok-⇒ (map-ν-vars-target-ok-wf {Φ = Φ} {A = A} wfA)
       (map-ν-vars-target-ok-wf {Φ = Φ} {A = B} wfB)
map-ν-vars-target-ok-wf {Φ = Φ} {A = `∀ A} (wf∀ wfA) =
  ok-∀ (map-ν-vars-target-ok-wf {Φ = X⊑X ∷ Φ} {A = A} wfA)

strip-∀-target-ok-wf :
  ∀ {Φ A} →
  WfTy (length Φ) 0 A →
  TargetOk Φ (strip-∀ Φ A)
strip-∀-target-ok-wf {A = ＇ X} wfA = map-ν-vars-target-ok-wf wfA
strip-∀-target-ok-wf {A = ｀ α} wfA = map-ν-vars-target-ok-wf wfA
strip-∀-target-ok-wf {A = ‵ ι} wfA = map-ν-vars-target-ok-wf wfA
strip-∀-target-ok-wf {A = ★} wfA = map-ν-vars-target-ok-wf wfA
strip-∀-target-ok-wf {A = A ⇒ B} wfA = map-ν-vars-target-ok-wf wfA
strip-∀-target-ok-wf {Φ = Φ} {A = `∀ A} (wf∀ wfA)
    with strip-∀-target-ok-wf {Φ = X⊑★ ∷ Φ} {A = A} wfA
... | okA =
  subst (TargetOk Φ)
    (sym (strip-∀-drop-eq okA))
    (dropTargetFrom-ok zero okA)

dropTyFrom-preserves-Non∀ :
  ∀ {k A} →
  Non∀ A →
  Non∀ (dropTyFrom k A)
dropTyFrom-preserves-Non∀ non∀-＇ = non∀-＇
dropTyFrom-preserves-Non∀ non∀-｀ = non∀-｀
dropTyFrom-preserves-Non∀ non∀-‵ = non∀-‵
dropTyFrom-preserves-Non∀ non∀-★ = non∀-★
dropTyFrom-preserves-Non∀ non∀-⇒ = non∀-⇒

ground-Non∀ : ∀ {G} → Ground G → Non∀ G
ground-Non∀ (｀ α) = non∀-｀
ground-Non∀ (‵ ι) = non∀-‵
ground-Non∀ ★⇒★ = non∀-⇒

strip-∀-non∀ : ∀ Φ A → Non∀ (strip-∀ Φ A)
strip-∀-non∀ Φ (＇ X) with mode-at Φ X
... | X⊑X = non∀-＇
... | X⊑★ = non∀-★
strip-∀-non∀ Φ (｀ α) = non∀-｀
strip-∀-non∀ Φ (‵ ι) = non∀-‵
strip-∀-non∀ Φ ★ = non∀-★
strip-∀-non∀ Φ (A ⇒ B) = non∀-⇒
strip-∀-non∀ Φ (`∀ A) =
  dropTyFrom-preserves-Non∀ (strip-∀-non∀ (X⊑★ ∷ Φ) A)

target-refl-⊑ :
  ∀ {Φ B A p} →
  0 ∣ Φ ⊢ p ⦂ B ⊑ A →
  ∃[ q ] 0 ∣ Φ ⊢ q ⦂ A ⊑ A
target-refl-⊑ ⊢★-⊑-★ =
  id★ , ⊢★-⊑-★
target-refl-⊑ (⊢X-⊑-★ xν) =
  id★ , ⊢★-⊑-★
target-refl-⊑ (⊢A-⊑-★ g p⊢) =
  id★ , ⊢★-⊑-★
target-refl-⊑ (⊢X-⊑-X {X = X} x∈) =
  idₓ X , ⊢X-⊑-X x∈
target-refl-⊑ (⊢α-⊑-α {α = α} wfα) =
  idₛ α , ⊢α-⊑-α wfα
target-refl-⊑ (⊢ι-⊑-ι {ι = ι}) =
  idι ι , ⊢ι-⊑-ι
target-refl-⊑ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
    with target-refl-⊑ p⊢ | target-refl-⊑ q⊢
... | p′ , p′⊢ | q′ , q′⊢ =
  p′ ↦ q′ , ⊢A⇒B-⊑-A′⇒B′ p′⊢ q′⊢
target-refl-⊑ (⊢∀A-⊑-∀B p⊢)
    with target-refl-⊑ p⊢
... | p′ , p′⊢ =
  ‵∀ p′ , ⊢∀A-⊑-∀B p′⊢
target-refl-⊑ {Φ = Φ} {A = B} (⊢∀A-⊑-B {B = B} occA wfB p⊢)
    with target-refl-⊑ p⊢
... | p′ , p′⊢
    with drop-mode-⊑ {m = X⊑★} {Φ = []} {Γ = Φ} {A = B} {B = B} p′⊢
... | q , q⊢ =
  q , q⊢

peel-∀-to-non∀ :
  ∀ {Φ B A p} →
  0 ∣ Φ ⊢ p ⦂ B ⊑ A →
  Non∀ A →
  ∃[ pB ] ∃[ pA ]
    Non∀ (strip-∀ Φ B) ×
    (0 ∣ Φ ⊢ pB ⦂ B ⊑ strip-∀ Φ B) ×
    (0 ∣ Φ ⊢ pA ⦂ strip-∀ Φ B ⊑ A)
peel-∀-to-non∀ ⊢★-⊑-★ non∀-★ =
  id★ , id★ , non∀-★ , ⊢★-⊑-★ , ⊢★-⊑-★
peel-∀-to-non∀ (⊢X-⊑-★ {X = X} xν) non∀-★
    rewrite mode-at-∋ xν =
  ‵ X ! , id★ , non∀-★ , ⊢X-⊑-★ xν , ⊢★-⊑-★
peel-∀-to-non∀ (⊢A-⊑-★ {G = G} g p⊢) non∀-★
    with peel-∀-to-non∀ p⊢ (ground-Non∀ g)
... | pB , pA , non∀Core , pB⊢ , pA⊢ =
  pB , pA ! ,
  non∀Core , pB⊢ , ⊢A-⊑-★ g pA⊢
peel-∀-to-non∀ (⊢X-⊑-X {X = X} x∈) non∀-＇
    rewrite mode-at-∋ x∈ =
  idₓ X , idₓ X , non∀-＇ , ⊢X-⊑-X x∈ , ⊢X-⊑-X x∈
peel-∀-to-non∀ (⊢α-⊑-α {α = α} wfα) non∀-｀ =
  idₛ α , idₛ α ,
  non∀-｀ , ⊢α-⊑-α wfα , ⊢α-⊑-α wfα
peel-∀-to-non∀ (⊢ι-⊑-ι {ι = ι}) non∀-‵ =
  idι ι , idι ι ,
  non∀-‵ , ⊢ι-⊑-ι , ⊢ι-⊑-ι
peel-∀-to-non∀ {Φ = Φ} {B = A ⇒ B} (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) non∀-⇒
    with map-ν-vars-upper-wf (⊑-src-wf p⊢)
       | map-ν-vars-upper-wf (⊑-src-wf q⊢)
       | map-ν-vars-to-target p⊢
       | map-ν-vars-to-target q⊢
... | pB₁ , pB₁⊢ | pB₂ , pB₂⊢ | pA₁ , pA₁⊢ | pA₂ , pA₂⊢ =
  pB₁ ↦ pB₂ ,
  pA₁ ↦ pA₂ ,
  non∀-⇒ ,
  ⊢A⇒B-⊑-A′⇒B′ pB₁⊢ pB₂⊢ ,
  ⊢A⇒B-⊑-A′⇒B′ pA₁⊢ pA₂⊢
peel-∀-to-non∀ (⊢∀A-⊑-∀B p⊢) ()
peel-∀-to-non∀ {Φ = Φ} (⊢∀A-⊑-B {A = A} {B = B} occA wfB p⊢) non∀A
    with peel-∀-to-non∀ p⊢ (renameᵗ-preserves-Non∀ suc non∀A)
       | strip-∀-target-ok-wf {Φ = X⊑★ ∷ Φ} {A = A} (⊑-src-wf p⊢)
... | pB′ , pA′ , _ , pB′⊢ , pA′⊢ | okStrip
    with target-refl-⊑ pB′⊢
... | stripRefl , stripRefl⊢
    with trans-ctx-⊑ ≤ᵢ-refl
      pB′⊢
      (cong-⊢⊑ refl (strip-∀-shift-eq okStrip) stripRefl⊢)
... | pBinner , pBinner⊢
    with trans-ctx-⊑ ≤ᵢ-refl
      (cong-⊢⊑ (strip-∀-shift-eq okStrip) refl stripRefl⊢)
      pA′⊢
... | pAinner , pAinner⊢
    with drop-mode-⊑
      {m = X⊑★}
      {Φ = []}
      {Γ = Φ}
      {A = dropTyFrom zero (strip-∀ (X⊑★ ∷ Φ) A)}
      {B = B}
      pAinner⊢
... | pAfinal , pAfinal⊢ =
  ν pBinner ,
  pAfinal ,
  strip-∀-non∀ Φ (`∀ A) ,
  ⊢∀A-⊑-B
    occA
    (subst
      (λ T → WfTy (length Φ) 0 T)
      (sym (strip-∀-drop-eq okStrip))
      (dropTargetFrom-WfTy zero
        (⊑-tgt-wf pB′⊢)
        okStrip))
    pBinner⊢ ,
  pAfinal⊢

arrow-core-inv :
  ∀ {Φ T A₁ A₂ p} →
  Non∀ T →
  0 ∣ Φ ⊢ p ⦂ T ⊑ A₁ ⇒ A₂ →
  ∃[ T₁ ] ∃[ T₂ ] ∃[ p′ ]
    (T ≡ T₁ ⇒ T₂) ×
    (0 ∣ Φ ⊢ p′ ⦂ T₁ ⇒ T₂ ⊑ A₁ ⇒ A₂)
arrow-core-inv non∀-⇒
    (⊢A⇒B-⊑-A′⇒B′ {A = T₁} {B = T₂} {p = p₁} {q = p₂} p₁⊢ p₂⊢) =
  T₁ , T₂ , p₁ ↦ p₂ , refl , ⊢A⇒B-⊑-A′⇒B′ p₁⊢ p₂⊢

arrow-lower-bound-inv :
  ∀ {Φ B′ A₁ A₂ C₁ C₂ pA pC} →
  0 ∣ Φ ⊢ pA ⦂ B′ ⊑ A₁ ⇒ A₂ →
  0 ∣ Φ ⊢ pC ⦂ B′ ⊑ C₁ ⇒ C₂ →
  ∃[ B′₁ ] ∃[ B′₂ ] ∃[ pB′ ] ∃[ pA′ ] ∃[ pC′ ]
    (0 ∣ Φ ⊢ pB′ ⦂ B′ ⊑ B′₁ ⇒ B′₂) ×
    (0 ∣ Φ ⊢ pA′ ⦂ B′₁ ⇒ B′₂ ⊑ A₁ ⇒ A₂) ×
    (0 ∣ Φ ⊢ pC′ ⦂ B′₁ ⇒ B′₂ ⊑ C₁ ⇒ C₂)
arrow-lower-bound-inv {Φ = Φ} {B′ = B′} pA⊢ pC⊢
    with peel-∀-to-non∀ pA⊢ non∀-⇒
       | peel-∀-to-non∀ pC⊢ non∀-⇒
... | pB′ , pAcore , non∀Core , pB′⊢ , pAcore⊢
    | _ , pCcore , _ , _ , pCcore⊢
    with arrow-core-inv non∀Core pAcore⊢
... | B′₁ , B′₂ , pA′ , eqCore , pA′⊢ =
  B′₁ , B′₂ , pB′ , pA′ , pCcore ,
  cong-⊢⊑ refl eqCore pB′⊢ ,
  pA′⊢ ,
  cong-⊢⊑ eqCore refl pCcore⊢

promote-head-X⊑X-to-ν :
  ∀ {Φ A B p q} →
  0 ∣ X⊑X ∷ Φ ⊢ p ⦂ A ⊑ B →
  0 ∣ X⊑★ ∷ Φ ⊢ q ⦂ B ⊑ B →
  ∃[ r ] 0 ∣ X⊑★ ∷ Φ ⊢ r ⦂ A ⊑ B
promote-head-X⊑X-to-ν {Φ = Φ} p⊢ q⊢ =
  trans-ctx-⊑ (X⊑X≤ν ∷≤ᵢ ≤ᵢ-refl) p⊢ q⊢

coerce-glbᶜ′ :
  ∀ {Γ Φ A C B B′ pA pC} →
  (A~C : Γ ⊢ A ~ C) →
  leftICtx Γ ≤ᵢ Φ →
  rightICtx Γ ≤ᵢ Φ →
  0 ∣ leftICtx Γ ⊢ coerce-⊒ A~C ⦂ B ⊑ A →
  0 ∣ rightICtx Γ ⊢ coerce-⊑ A~C ⦂ B ⊑ C →
  0 ∣ Φ ⊢ pA ⦂ B′ ⊑ A →
  0 ∣ Φ ⊢ pC ⦂ B′ ⊑ C →
  ∃[ r ] 0 ∣ Φ ⊢ r ⦂ B′ ⊑ B
coerce-glbᶜ′ ★-~-★ Γ≤Φ Γ′≤Φ ⊢★-⊑-★ ⊢★-⊑-★ pA⊢ pC⊢ =
  _ , pA⊢
coerce-glbᶜ′ (X-~-X x∈) Γ≤Φ Γ′≤Φ (⊢X-⊑-X _) (⊢X-⊑-X _)
    pA⊢ pC⊢ =
  _ , pA⊢
coerce-glbᶜ′ ι-~-ι Γ≤Φ Γ′≤Φ ⊢ι-⊑-ι ⊢ι-⊑-ι pA⊢ pC⊢ =
  _ , pA⊢
coerce-glbᶜ′ (νX-~-★ x∈) Γ≤Φ Γ′≤Φ (⊢X-⊑-X _) (⊢X-⊑-★ _)
    pA⊢ pC⊢ =
  _ , pA⊢
coerce-glbᶜ′ (★-~-νX x∈) Γ≤Φ Γ′≤Φ (⊢X-⊑-★ _) (⊢X-⊑-X _)
    pA⊢ pC⊢ =
  _ , pC⊢
coerce-glbᶜ′ (⇒-~-⇒ A~C B~D) Γ≤Φ Γ′≤Φ
    (⊢A⇒B-⊑-A′⇒B′ p⊒₁⊢ p⊒₂⊢)
    (⊢A⇒B-⊑-A′⇒B′ p⊑₁⊢ p⊑₂⊢)
    (⊢A⇒B-⊑-A′⇒B′ pA₁⊢ pA₂⊢)
    (⊢A⇒B-⊑-A′⇒B′ pC₁⊢ pC₂⊢)
    with coerce-glbᶜ′ A~C Γ≤Φ Γ′≤Φ p⊒₁⊢ p⊑₁⊢ pA₁⊢ pC₁⊢
       | coerce-glbᶜ′ B~D Γ≤Φ Γ′≤Φ p⊒₂⊢ p⊑₂⊢ pA₂⊢ pC₂⊢
... | r₁ , r₁⊢ | r₂ , r₂⊢ =
  r₁ ↦ r₂ , ⊢A⇒B-⊑-A′⇒B′ r₁⊢ r₂⊢
coerce-glbᶜ′ (⇒-~-⇒{A = A₁}{C₁}{A₂}{C₂} A₁~C₁ A₂~C₂) Γ≤Φ Γ′≤Φ
    (⊢A⇒B-⊑-A′⇒B′{A = B₁}{B = B₂} p⊒₁⊢ p⊒₂⊢)
    (⊢A⇒B-⊑-A′⇒B′ p⊑₁⊢ p⊑₂⊢)
    (⊢∀A-⊑-B{A = B′} occA wfA pA⊢)
    (⊢∀A-⊑-B{A = B′} occC wfC pC⊢)
    with arrow-lower-bound-inv
           (⊢∀A-⊑-B{A = B′} occA wfA pA⊢)
           (⊢∀A-⊑-B{A = B′} occC wfC pC⊢)
coerce-glbᶜ′ (⇒-~-⇒{A = A₁}{C₁}{A₂}{C₂} A₁~C₁ A₂~C₂) Γ≤Φ Γ′≤Φ
    (⊢A⇒B-⊑-A′⇒B′{A = B₁}{B = B₂} p⊒₁⊢ p⊒₂⊢)
    (⊢A⇒B-⊑-A′⇒B′ p⊑₁⊢ p⊑₂⊢)
    (⊢∀A-⊑-B{A = B′} occA wfA pA⊢)
    (⊢∀A-⊑-B{A = B′} occC wfC pC⊢)
    | B′₁ , B′₂ , pB′ , pA′ , pC′ , pB′⊢ , pA′⊢ , pC′⊢
    with pA′⊢ | pC′⊢
coerce-glbᶜ′ (⇒-~-⇒{A = A₁}{C₁}{A₂}{C₂} A₁~C₁ A₂~C₂) Γ≤Φ Γ′≤Φ
    (⊢A⇒B-⊑-A′⇒B′{A = B₁}{B = B₂} p⊒₁⊢ p⊒₂⊢)
    (⊢A⇒B-⊑-A′⇒B′ p⊑₁⊢ p⊑₂⊢)
    (⊢∀A-⊑-B{A = B′} occA wfA pA⊢)
    (⊢∀A-⊑-B{A = B′} occC wfC pC⊢)
    | B′₁ , B′₂ , pB′ , pA′ , pC′ , pB′⊢ , pA′⊢ , pC′⊢
    | ⊢A⇒B-⊑-A′⇒B′ pA₁⊢ pA₂⊢
    | ⊢A⇒B-⊑-A′⇒B′ pC₁⊢ pC₂⊢
    with coerce-glbᶜ′ A₁~C₁ Γ≤Φ Γ′≤Φ p⊒₁⊢ p⊑₁⊢ pA₁⊢ pC₁⊢
       | coerce-glbᶜ′ A₂~C₂ Γ≤Φ Γ′≤Φ p⊒₂⊢ p⊑₂⊢ pA₂⊢ pC₂⊢
coerce-glbᶜ′ (⇒-~-⇒{A = A₁}{C₁}{A₂}{C₂} A₁~C₁ A₂~C₂) Γ≤Φ Γ′≤Φ
    (⊢A⇒B-⊑-A′⇒B′{A = B₁}{B = B₂} p⊒₁⊢ p⊒₂⊢)
    (⊢A⇒B-⊑-A′⇒B′ p⊑₁⊢ p⊑₂⊢)
    (⊢∀A-⊑-B{A = B′} occA wfA pA⊢)
    (⊢∀A-⊑-B{A = B′} occC wfC pC⊢)
    | B′₁ , B′₂ , pB′ , pA′ , pC′ , pB′⊢ , pA′⊢ , pC′⊢
    | ⊢A⇒B-⊑-A′⇒B′ pA₁⊢ pA₂⊢
    | ⊢A⇒B-⊑-A′⇒B′ pC₁⊢ pC₂⊢
    | r₁ , r₁⊢ | r₂ , r₂⊢
    with trans-ctx-⊑ ≤ᵢ-refl pB′⊢ (⊢A⇒B-⊑-A′⇒B′ r₁⊢ r₂⊢)
coerce-glbᶜ′ (⇒-~-⇒{A = A₁}{C₁}{A₂}{C₂} A₁~C₁ A₂~C₂) Γ≤Φ Γ′≤Φ
    (⊢A⇒B-⊑-A′⇒B′{A = B₁}{B = B₂} p⊒₁⊢ p⊒₂⊢)
    (⊢A⇒B-⊑-A′⇒B′ p⊑₁⊢ p⊑₂⊢)
    (⊢∀A-⊑-B{A = B′} occA wfA pA⊢)
    (⊢∀A-⊑-B{A = B′} occC wfC pC⊢)
    | B′₁ , B′₂ , pB′ , pA′ , pC′ , pB′⊢ , pA′⊢ , pC′⊢
    | ⊢A⇒B-⊑-A′⇒B′ pA₁⊢ pA₂⊢
    | ⊢A⇒B-⊑-A′⇒B′ pC₁⊢ pC₂⊢
    | r₁ , r₁⊢ | r₂ , r₂⊢
    | r , r⊢ =
  r , r⊢
coerce-glbᶜ′ (A-~-★ n★ n∀ g A~G) Γ≤Φ Γ′≤Φ p⊒⊢
    (⊢A-⊑-★ h p⊑⊢) pA⊢ pC⊢
    with right-consistent-ground-⊑ n★ n∀ g A~G Γ′≤Φ
coerce-glbᶜ′ (A-~-★ n★ n∀ g A~G) Γ≤Φ Γ′≤Φ p⊒⊢
    (⊢A-⊑-★ h p⊑⊢) pA⊢ pC⊢
    | A⊑G , A⊑G⊢
    with trans-ctx-⊑ ≤ᵢ-refl pA⊢ A⊑G⊢
... | B′⊑G , B′⊑G⊢ =
  coerce-glbᶜ′ A~G Γ≤Φ Γ′≤Φ p⊒⊢
    (cong-⊢⊑ refl
      (trans (sym (tgt⊑-correct p⊑⊢)) (coerce-⊑-tgt A~G))
      p⊑⊢)
    pA⊢ B′⊑G⊢
coerce-glbᶜ′ (★-~-B n★ n∀ h H~B) Γ≤Φ Γ′≤Φ
    (⊢A-⊑-★ g p⊒⊢) p⊑⊢ pA⊢ pC⊢
    with left-consistent-ground-⊑ n★ n∀ h H~B Γ≤Φ
coerce-glbᶜ′ (★-~-B n★ n∀ h H~B) Γ≤Φ Γ′≤Φ
    (⊢A-⊑-★ g p⊒⊢) p⊑⊢ pA⊢ pC⊢
    | B⊑H , B⊑H⊢
    with trans-ctx-⊑ ≤ᵢ-refl pC⊢ B⊑H⊢
... | B′⊑H , B′⊑H⊢ =
  coerce-glbᶜ′ H~B Γ≤Φ Γ′≤Φ
    (cong-⊢⊑ refl
      (trans (sym (tgt⊑-correct p⊒⊢)) (coerce-⊒-tgt H~B))
      p⊒⊢)
    p⊑⊢ B′⊑H⊢ pC⊢
coerce-glbᶜ′ (∀-~-∀ A~C) Γ≤Φ Γ′≤Φ
    (⊢∀A-⊑-∀B p⊒⊢) (⊢∀A-⊑-∀B p⊑⊢)
    (⊢∀A-⊑-∀B pA⊢) (⊢∀A-⊑-∀B pC⊢)
    with coerce-glbᶜ′ A~C
      (X⊑X≤X⊑X ∷≤ᵢ Γ≤Φ)
      (X⊑X≤X⊑X ∷≤ᵢ Γ′≤Φ)
      p⊒⊢ p⊑⊢ pA⊢ pC⊢
... | r , r⊢ =
  ‵∀ r , ⊢∀A-⊑-∀B r⊢
coerce-glbᶜ′ (∀-~-∀{A = A}{C} A~C) Γ≤Φ Γ′≤Φ
    (⊢∀A-⊑-∀B{A = B}{B = A} B⊑A) (⊢∀A-⊑-∀B{A = B}{B = C} B⊑C)
    (⊢∀A-⊑-∀B{A = B′} B′⊑A) (⊢∀A-⊑-B{A = B′} occC wfC B′⊑∀C)
    =
  {!!}
coerce-glbᶜ′ (∀-~-∀ A~C) Γ≤Φ Γ′≤Φ
    (⊢∀A-⊑-∀B p⊒⊢) (⊢∀A-⊑-∀B p⊑⊢)
    (⊢∀A-⊑-B occA wfA pA⊢)
    (⊢∀A-⊑-∀B pC⊢)
    =
  {!!}
coerce-glbᶜ′ (∀-~-∀ A~C) Γ≤Φ Γ′≤Φ
    (⊢∀A-⊑-∀B p⊒⊢) (⊢∀A-⊑-∀B p⊑⊢)
    (⊢∀A-⊑-B occA wfA pA⊢) (⊢∀A-⊑-B occC wfC pC⊢)
    =
  {!!}
coerce-glbᶜ′ (∀-~-B occC wfC A~⇑C) Γ≤Φ Γ′≤Φ
    (⊢∀A-⊑-∀B p⊒⊢) (⊢∀A-⊑-B occC′ wfC′ p⊑⊢) pA⊢ pC⊢
    =
  {!!}
coerce-glbᶜ′ (A-~-∀ occA wfA ⇑A~C) Γ≤Φ Γ′≤Φ
    (⊢∀A-⊑-B occA′ wfA′ p⊒⊢) (⊢∀A-⊑-∀B p⊑⊢) pA⊢ pC⊢
    =
  {!!}

coerce-glbᶜ A~C Γ≤Φ Γ′≤Φ p⊒⊢ p⊑⊢ pA⊢ pC⊢ eq⊒ eq⊑
  rewrite eq⊒ | eq⊑ =
  coerce-glbᶜ′ A~C Γ≤Φ Γ′≤Φ p⊒⊢ p⊑⊢ pA⊢ pC⊢

left-right-plain :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ X⊑X →
  rightICtx Γ ∋ X ∶ X⊑X →
  Γ ∋ᶜ X ∶ X~X
left-right-plain {Γ = X~★ ∷ Γ} here ()
left-right-plain {Γ = X~★ ∷ Γ} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = ★~X ∷ Γ} () here
left-right-plain {Γ = ★~X ∷ Γ} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = X~X ∷ Γ} here here = here
left-right-plain {Γ = X~X ∷ Γ} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = neither ∷ Γ} {X = zero} () ()
left-right-plain {Γ = neither ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)

left-ν-right-plain :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ X⊑★ →
  rightICtx Γ ∋ X ∶ X⊑X →
  Γ ∋ᶜ X ∶ ★~X
left-ν-right-plain {Γ = X~★ ∷ Γ} {X = zero} ()
left-ν-right-plain {Γ = X~★ ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = ★~X ∷ Γ} here here = here
left-ν-right-plain {Γ = ★~X ∷ Γ} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = X~X ∷ Γ} {X = zero} () here
left-ν-right-plain {Γ = X~X ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = neither ∷ Γ} {X = zero} here ()
left-ν-right-plain {Γ = neither ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)

left-plain-right-ν :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ X⊑X →
  rightICtx Γ ∋ X ∶ X⊑★ →
  Γ ∋ᶜ X ∶ X~★
left-plain-right-ν {Γ = X~★ ∷ Γ} here here = here
left-plain-right-ν {Γ = X~★ ∷ Γ} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = ★~X ∷ Γ} {X = zero} () ()
left-plain-right-ν {Γ = ★~X ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = X~X ∷ Γ} {X = zero} here ()
left-plain-right-ν {Γ = X~X ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = neither ∷ Γ} {X = zero} () here
left-plain-right-ν {Γ = neither ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)

postulate
  lower-bounds-star-leftᶜ :
    ∀ {Γ A C p q G} →
    Ground G →
    0 ∣ leftICtx Γ ⊢ p ⦂ A ⊑ G →
    0 ∣ rightICtx Γ ⊢ q ⦂ A ⊑ C →
    Γ ⊢ ★ ~ C

  lower-bounds-star-rightᶜ :
    ∀ {Γ A B p q G} →
    Ground G →
    0 ∣ leftICtx Γ ⊢ p ⦂ A ⊑ B →
    0 ∣ rightICtx Γ ⊢ q ⦂ A ⊑ G →
    Γ ⊢ B ~ ★

lower-bounds-consistentᶜ :
  ∀ {Γ A B C p q} →
  0 ∣ leftICtx Γ ⊢ p ⦂ A ⊑ B →
  0 ∣ rightICtx Γ ⊢ q ⦂ A ⊑ C →
  Γ ⊢ B ~ C

lower-bounds-consistentᶜ (⊢A-⊑-★ g p⊢) q⊢ =
  lower-bounds-star-leftᶜ g p⊢ q⊢
lower-bounds-consistentᶜ p⊢ (⊢A-⊑-★ g q⊢) =
  lower-bounds-star-rightᶜ g p⊢ q⊢
lower-bounds-consistentᶜ ⊢★-⊑-★ ⊢★-⊑-★ = ★-~-★
lower-bounds-consistentᶜ (⊢X-⊑-★ xν) (⊢X-⊑-★ yν) = ★-~-★
lower-bounds-consistentᶜ (⊢X-⊑-★ xν) (⊢X-⊑-X y∈) =
  ★-~-νX (left-ν-right-plain xν y∈)
lower-bounds-consistentᶜ (⊢X-⊑-X x∈) (⊢X-⊑-★ yν) =
  νX-~-★ (left-plain-right-ν x∈ yν)
lower-bounds-consistentᶜ (⊢X-⊑-X x∈) (⊢X-⊑-X y∈) =
  X-~-X (left-right-plain x∈ y∈)
lower-bounds-consistentᶜ (⊢α-⊑-α (wfSeal ())) q⊢
lower-bounds-consistentᶜ ⊢ι-⊑-ι ⊢ι-⊑-ι = ι-~-ι
lower-bounds-consistentᶜ (⊢A⇒B-⊑-A′⇒B′ p₁⊢ p₂⊢) (⊢A⇒B-⊑-A′⇒B′ q₁⊢ q₂⊢) =
  ⇒-~-⇒ (lower-bounds-consistentᶜ p₁⊢ q₁⊢)
         (lower-bounds-consistentᶜ p₂⊢ q₂⊢)
lower-bounds-consistentᶜ {Γ = Γ} (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-∀B q⊢) =
  ∀-~-∀ (lower-bounds-consistentᶜ {Γ = X~X ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} {C = C} (⊢∀A-⊑-∀B p⊢)
    (⊢∀A-⊑-B occA wfC q⊢) =
  ∀-~-B
    (plain-source-occurs-target here p⊢ occA)
    (subst (λ n → WfTy n 0 C) (length-rightICtx Γ) wfC)
    (lower-bounds-consistentᶜ {Γ = X~★ ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} {B = B}
    (⊢∀A-⊑-B occA wfB p⊢) (⊢∀A-⊑-∀B q⊢) =
  A-~-∀
    (plain-source-occurs-target here q⊢ occA)
    (subst (λ n → WfTy n 0 B) (length-leftICtx Γ) wfB)
    (lower-bounds-consistentᶜ {Γ = ★~X ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} (⊢∀A-⊑-B occA wfB p⊢)
    (⊢∀A-⊑-B occC wfC q⊢) =
  drop-neither-~ (lower-bounds-consistentᶜ {Γ = neither ∷ Γ} p⊢ q⊢)

lower-bounds-consistent :
  ∀ {Δ A B C p q} →
  0 ∣ extend-X⊑X Δ [] ⊢ p ⦂ A ⊑ B →
  0 ∣ extend-X⊑X Δ [] ⊢ q ⦂ A ⊑ C →
  extend-X~X Δ [] ⊢ B ~ C
lower-bounds-consistent
    {Δ = Δ} {A = A} {B = B} {C = C} {p = p} {q = q} p⊢ q⊢ =
  lower-bounds-consistentᶜ {Γ = extend-X~X Δ []}
    (subst (λ Φ → 0 ∣ Φ ⊢ p ⦂ A ⊑ B) (sym (leftICtx-extend-X~X[] Δ)) p⊢)
    (subst (λ Φ → 0 ∣ Φ ⊢ q ⦂ A ⊑ C) (sym (rightICtx-extend-X~X[] Δ)) q⊢)

sameCCtx [] = []
sameCCtx (X⊑X ∷ Φ) = X~X ∷ sameCCtx Φ
sameCCtx (X⊑★ ∷ Φ) = neither ∷ sameCCtx Φ

leftICtx-sameCCtx [] = refl
leftICtx-sameCCtx (X⊑X ∷ Φ) = cong (X⊑X ∷_) (leftICtx-sameCCtx Φ)
leftICtx-sameCCtx (X⊑★ ∷ Φ) = cong (X⊑★ ∷_) (leftICtx-sameCCtx Φ)

rightICtx-sameCCtx [] = refl
rightICtx-sameCCtx (X⊑X ∷ Φ) = cong (X⊑X ∷_) (rightICtx-sameCCtx Φ)
rightICtx-sameCCtx (X⊑★ ∷ Φ) = cong (X⊑★ ∷_) (rightICtx-sameCCtx Φ)

length-sameCCtx : ∀ Φ → length (sameCCtx Φ) ≡ length Φ
length-sameCCtx [] = refl
length-sameCCtx (X⊑X ∷ Φ) = cong suc (length-sameCCtx Φ)
length-sameCCtx (X⊑★ ∷ Φ) = cong suc (length-sameCCtx Φ)

length-same-to-plain :
  ∀ Ω Φ →
  length (Ω ++ sameCCtx Φ) ≡
  length (Ω ++ extend-X~X (length Φ) [])
length-same-to-plain [] Φ =
  trans (length-sameCCtx Φ) (sym (length-extend-X~X[] (length Φ)))
length-same-to-plain (d ∷ Ω) Φ = cong suc (length-same-to-plain Ω Φ)

same-to-plain-X~X∋ᶜ :
  ∀ {Ω Φ X} →
  Ω ++ sameCCtx Φ ∋ᶜ X ∶ X~X →
  Ω ++ extend-X~X (length Φ) [] ∋ᶜ X ∶ X~X
same-to-plain-X~X∋ᶜ {Ω = []} {Φ = []} ()
same-to-plain-X~X∋ᶜ {Ω = []} {Φ = X⊑X ∷ Φ} here = here
same-to-plain-X~X∋ᶜ {Ω = []} {Φ = X⊑X ∷ Φ} (there x∈) =
  there (same-to-plain-X~X∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-X~X∋ᶜ {Ω = []} {Φ = X⊑★ ∷ Φ} (there x∈) =
  there (same-to-plain-X~X∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-X~X∋ᶜ {Ω = d ∷ Ω} here = here
same-to-plain-X~X∋ᶜ {Ω = d ∷ Ω} (there x∈) =
  there (same-to-plain-X~X∋ᶜ {Ω = Ω} x∈)

same-to-plain-X~★∋ᶜ :
  ∀ {Ω Φ X} →
  Ω ++ sameCCtx Φ ∋ᶜ X ∶ X~★ →
  Ω ++ extend-X~X (length Φ) [] ∋ᶜ X ∶ X~★
same-to-plain-X~★∋ᶜ {Ω = []} {Φ = []} ()
same-to-plain-X~★∋ᶜ {Ω = []} {Φ = X⊑X ∷ Φ} (there x∈) =
  there (same-to-plain-X~★∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-X~★∋ᶜ {Ω = []} {Φ = X⊑★ ∷ Φ} (there x∈) =
  there (same-to-plain-X~★∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-X~★∋ᶜ {Ω = d ∷ Ω} here = here
same-to-plain-X~★∋ᶜ {Ω = d ∷ Ω} (there x∈) =
  there (same-to-plain-X~★∋ᶜ {Ω = Ω} x∈)

same-to-plain-★~X∋ᶜ :
  ∀ {Ω Φ X} →
  Ω ++ sameCCtx Φ ∋ᶜ X ∶ ★~X →
  Ω ++ extend-X~X (length Φ) [] ∋ᶜ X ∶ ★~X
same-to-plain-★~X∋ᶜ {Ω = []} {Φ = []} ()
same-to-plain-★~X∋ᶜ {Ω = []} {Φ = X⊑X ∷ Φ} (there x∈) =
  there (same-to-plain-★~X∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-★~X∋ᶜ {Ω = []} {Φ = X⊑★ ∷ Φ} (there x∈) =
  there (same-to-plain-★~X∋ᶜ {Ω = []} {Φ = Φ} x∈)
same-to-plain-★~X∋ᶜ {Ω = d ∷ Ω} here = here
same-to-plain-★~X∋ᶜ {Ω = d ∷ Ω} (there x∈) =
  there (same-to-plain-★~X∋ᶜ {Ω = Ω} x∈)

same-to-plain-WfTy :
  ∀ {Ω Φ A} →
  WfTy (length (Ω ++ sameCCtx Φ)) 0 A →
  WfTy (length (Ω ++ extend-X~X (length Φ) [])) 0 A
same-to-plain-WfTy {Ω = Ω} {Φ = Φ} wfA =
  subst (λ n → WfTy n 0 _) (length-same-to-plain Ω Φ) wfA

same-to-plain-~ :
  ∀ {Ω Φ A B} →
  Ω ++ sameCCtx Φ ⊢ A ~ B →
  Ω ++ extend-X~X (length Φ) [] ⊢ A ~ B
same-to-plain-~ ★-~-★ = ★-~-★
same-to-plain-~ {Ω = Ω} {Φ = Φ} (X-~-X x∈) =
  X-~-X (same-to-plain-X~X∋ᶜ {Ω = Ω} {Φ = Φ} x∈)
same-to-plain-~ ι-~-ι = ι-~-ι
same-to-plain-~ {Ω = Ω} {Φ = Φ} (⇒-~-⇒ A~A′ B~B′) =
  ⇒-~-⇒ (same-to-plain-~ {Ω = Ω} {Φ = Φ} A~A′)
         (same-to-plain-~ {Ω = Ω} {Φ = Φ} B~B′)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (∀-~-∀ A~B) =
  ∀-~-∀ (same-to-plain-~ {Ω = X~X ∷ Ω} {Φ = Φ} A~B)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (A-~-★ n★ n∀ g A~G) =
  A-~-★ n★ n∀ g (same-to-plain-~ {Ω = Ω} {Φ = Φ} A~G)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (★-~-B n★ n∀ g G~B) =
  ★-~-B n★ n∀ g (same-to-plain-~ {Ω = Ω} {Φ = Φ} G~B)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (νX-~-★ x∈) =
  νX-~-★ (same-to-plain-X~★∋ᶜ {Ω = Ω} {Φ = Φ} x∈)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (★-~-νX x∈) =
  ★-~-νX (same-to-plain-★~X∋ᶜ {Ω = Ω} {Φ = Φ} x∈)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (∀-~-B occA wfB A~⇑B) =
  ∀-~-B occA (same-to-plain-WfTy {Ω = Ω} {Φ = Φ} wfB)
    (same-to-plain-~ {Ω = X~★ ∷ Ω} {Φ = Φ} A~⇑B)
same-to-plain-~ {Ω = Ω} {Φ = Φ} (A-~-∀ occB wfA ⇑A~B) =
  A-~-∀ occB (same-to-plain-WfTy {Ω = Ω} {Φ = Φ} wfA)
    (same-to-plain-~ {Ω = ★~X ∷ Ω} {Φ = Φ} ⇑A~B)

lower-bounds-consistentᵢ :
  ∀ {Φ A B C p q} →
  0 ∣ Φ ⊢ p ⦂ A ⊑ B →
  0 ∣ Φ ⊢ q ⦂ A ⊑ C →
  extend-X~X (length Φ) [] ⊢ B ~ C
lower-bounds-consistentᵢ {Φ = Φ} {A = A} {B = B} {C = C} {p = p} {q = q} p⊢ q⊢ =
  same-to-plain-~ {Ω = []} {Φ = Φ}
    (lower-bounds-consistentᶜ {Γ = sameCCtx Φ}
      (subst (λ Ψ → 0 ∣ Ψ ⊢ p ⦂ A ⊑ B) (sym (leftICtx-sameCCtx Φ)) p⊢)
      (subst (λ Ψ → 0 ∣ Ψ ⊢ q ⦂ A ⊑ C) (sym (rightICtx-sameCCtx Φ)) q⊢))

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

plain≤ᵢ :
  ∀ {Δ Φ} →
  length Φ ≡ Δ →
  extend-X⊑X Δ [] ≤ᵢ Φ
plain≤ᵢ {Δ = zero} {Φ = []} refl = []≤ᵢ
plain≤ᵢ {Δ = zero} {Φ = X⊑X ∷ Φ} ()
plain≤ᵢ {Δ = zero} {Φ = X⊑★ ∷ Φ} ()
plain≤ᵢ {Δ = suc Δ} {Φ = []} ()
plain≤ᵢ {Δ = suc Δ} {Φ = X⊑X ∷ Φ} len =
  X⊑X≤X⊑X ∷≤ᵢ plain≤ᵢ (suc-injective len)
plain≤ᵢ {Δ = suc Δ} {Φ = X⊑★ ∷ Φ} len =
  X⊑X≤ν ∷≤ᵢ plain≤ᵢ (suc-injective len)

coerce-glbᵢ :
  ∀ {Φ A C B B′ p⊒ p⊑ pA pC} →
  (A~C : extend-X~X (length Φ) [] ⊢ A ~ C) →
  0 ∣ extend-X⊑X (length Φ) [] ⊢ p⊒ ⦂ B ⊑ A →
  0 ∣ extend-X⊑X (length Φ) [] ⊢ p⊑ ⦂ B ⊑ C →
  0 ∣ Φ ⊢ pA ⦂ B′ ⊑ A →
  0 ∣ Φ ⊢ pC ⦂ B′ ⊑ C →
  p⊒ ≡ coerce-⊒ A~C →
  p⊑ ≡ coerce-⊑ A~C →
  ∃[ r ] 0 ∣ Φ ⊢ r ⦂ B′ ⊑ B
coerce-glbᵢ {Φ = Φ} {A = A} {C = C} {B = B}
    {B′ = B′} {p⊒ = p⊒} {p⊑ = p⊑} A~C p⊒⊢ p⊑⊢ pA⊢ pC⊢
    eq⊒ eq⊑ =
  coerce-glbᶜ {Γ = extend-X~X (length Φ) []} {Φ = Φ}
    A~C
    (subst (λ Ψ → Ψ ≤ᵢ Φ)
      (sym (leftICtx-extend-X~X[] (length Φ))) (plain≤ᵢ refl))
    (subst (λ Ψ → Ψ ≤ᵢ Φ)
      (sym (rightICtx-extend-X~X[] (length Φ))) (plain≤ᵢ refl))
    (subst (λ Ψ → 0 ∣ Ψ ⊢ p⊒ ⦂ B ⊑ A)
      (sym (leftICtx-extend-X~X[] (length Φ))) p⊒⊢)
    (subst (λ Ψ → 0 ∣ Ψ ⊢ p⊑ ⦂ B ⊑ C)
      (sym (rightICtx-extend-X~X[] (length Φ))) p⊑⊢)
    pA⊢ pC⊢ eq⊒ eq⊑

app-consistencyᵢ :
  ∀ {Δ Φ A A′ B B′ p q} →
  length Φ ≡ Δ →
  0 ∣ Φ ⊢ p ⦂ A ⊑ B →
  extend-X~X Δ [] ⊢ A ~ A′ →
  0 ∣ Φ ⊢ q ⦂ A′ ⊑ B′ →
  extend-X~X Δ [] ⊢ B ~ B′
app-consistencyᵢ {Δ = Δ} {Φ = Φ} len p⊢ A~A′ q⊢
    with coerce-wt-extend-X⊑X A~A′
app-consistencyᵢ {Δ = Δ} {Φ = Φ} len p⊢ A~A′ q⊢ | C , C⊑A , C⊑A′
    with trans-ctx-⊑ (plain≤ᵢ len) C⊑A p⊢
       | trans-ctx-⊑ (plain≤ᵢ len) C⊑A′ q⊢
app-consistencyᵢ {Φ = Φ} len p⊢ A~A′ q⊢ | C , C⊑A , C⊑A′
    | r , C⊑B | s , C⊑B′ =
  subst (λ n → extend-X~X n [] ⊢ _ ~ _) len
    (lower-bounds-consistentᵢ C⊑B C⊑B′)
