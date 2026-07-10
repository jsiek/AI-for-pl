module Compile where

-- File Charter:
--   * Compilation from source gradual GTSF terms to target explicit-coercion
--     terms.
--   * Exports the common-lower-bound cast-plan specification, `compile`, and
--     `compile-value`.
--   * The store is empty at compile time; target reduction allocates store
--     cells later for polymorphic/seal behavior.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Types
open import Ctx using (CtxWf; ctxWf-∷; ⤊ᵗ)
open import Coercions
  using
    ( Coercion
    ; _∣_⊢_∶_=⇒_
    ; _∣_∣_⊢_∶_=⇒_
    ; reveal
    ; id-onlyᵈ
    ; id-only≤tag-or-idᵈ
    ; tag-or-idᵈ
    )
open import Conversion using (_∣_∣_⊢_∶_↑ˢ_; reveal-conversion-env)
open import Imprecision using (_⊢_~_; idᵢ; id★; _↦_; tag_⇛_)
import ImprecisionWf as IWF
open import Primitives using (Const; Prim; constTy)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  ; narrow-mode-relax
  ; widen-mode-relax
  )
open import proof.CompileCoercions using
  ( coerce-upʷ
  ; coerce-downⁿ
  ; realizes-idᵢᴺᵂ-id-only
  )
open import proof.CastImprecision
  using (castᵢ-id-only; narrowing⇒⊑ᵢ; widening⇒⊑ᵢ)
open import proof.CoercionProperties
  using
    ( RevealEnv
    ; reveal-typing-env
    ; rv-hit
    ; rv-miss
    ; singleSealᵈ
    ; singleSealMode
    )
open import proof.ImprecisionProperties
  using (⊑-src-wf-idᵢ; ⊑-tgt-wf-idᵢ; ~-sym)
open import proof.MaximalLowerBoundsWf
  using
    ( mlb-type-from-lowerᵢ
    ; mlb-type-from-lower-commonᵢ
    ; mlb-type-from-lower-common-oldᵢ
    ; old⊑→wf-idᵢ
    )
open import proof.NarrowWidenProperties using (StoreDetWf)
open import proof.NuTermProperties using (CtxWf-⤊)
open import proof.TypeProperties
  using
    ( TySubstWf
    ; TyRenameWf-suc
    ; renameᵗ-id
    ; rename-subst
    ; renameᵗ-preserves-WfTy
    ; subst-cong
    )

open import GradualTerms
  using (GTerm)
  renaming
    ( `_ to `ᴳ_
    ; ƛ_⇒_ to ƛᴳ_⇒_
    ; _·[_]_ to _·ᴳ[_]_
    ; Λ_ to Λᴳ_
    ; _`[_] to _`ᴳ[_]
    ; $ to $ᴳ
    ; _⊕[_at_]_ to _⊕ᴳ[_at_]_
    ; Value to Valueᴳ
    ; _∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_
    ; ⊢` to ⊢ᴳ`
    ; ⊢ƛ to ⊢ᴳƛ
    ; ⊢· to ⊢ᴳ·
    ; ⊢·★ to ⊢ᴳ·★
    ; ⊢Λ to ⊢ᴳΛ
    ; ⊢• to ⊢ᴳ•
    ; ⊢$ to ⊢ᴳ$
    ; ⊢⊕ to ⊢ᴳ⊕
    )
open import NuTerms
  using (Term)
  renaming
    ( `_ to `ᵀ_
    ; ƛ_ to ƛᵀ_
    ; _·_ to _·ᵀ_
    ; Λ_ to Λᵀ_
    ; ν to νᵀ
    ; $ to $ᵀ
    ; _⊕[_]_ to _⊕ᵀ[_]_
    ; _⟨_⟩ to _⟨ᵀ_⟩
    ; Value to Valueᵀ
    ; _∣_∣_⊢_⦂_ to _∣_∣_⊢ᵀ_⦂_
    ; ⊢` to ⊢ᵀ`
    ; ⊢ƛ to ⊢ᵀƛ
    ; ⊢· to ⊢ᵀ·
    ; ⊢Λ to ⊢ᵀΛ
    ; ⊢ν to ⊢ᵀν
    ; ⊢$ to ⊢ᵀ$
    ; ⊢⊕ to ⊢ᵀ⊕
    ; ⊢⟨⟩ to ⊢ᵀ⟨⟩
    )
import TermTyping as TT

storeDetWf-[] :
  ∀ {Δ} →
  StoreDetWf Δ []
storeDetWf-[] =
  record
    { at = record { bound = λ (); wfTy = λ () }
    ; wfOlder = λ ()
    ; unique = λ ()
    }

seal★-id-only :
  ∀ {Σ} →
  TT.SealModeStore★ id-onlyᵈ Σ
seal★-id-only α ()

------------------------------------------------------------------------
-- Nu coercion for source type application
------------------------------------------------------------------------

ν-subst : Ty → Substᵗ
ν-subst A zero = ⇑ᵗ A
ν-subst A (suc X) = ＇ suc X

ν-subst-target :
  ∀ A B →
  substᵗ (ν-subst A) B ≡ ⇑ᵗ (B [ A ]ᵗ)
ν-subst-target A B =
  trans
    (sym (subst-cong env-eq B))
    (sym (rename-subst suc (singleTyEnv A) B))
  where
    env-eq :
      ∀ X →
      renameᵗ suc (singleTyEnv A X) ≡ ν-subst A X
    env-eq zero = refl
    env-eq (suc X) = refl

ν-subst-wf :
  ∀ {Δ A} →
  WfTy Δ A →
  TySubstWf (suc Δ) (suc Δ) (ν-subst A)
ν-subst-wf hA {zero} z<s =
  renameᵗ-preserves-WfTy hA TyRenameWf-suc
ν-subst-wf hA {suc X} (s<s X<Δ) =
  wfVar (s<s X<Δ)

ν-reveal-env :
  ∀ {Δ A} →
  RevealEnv (suc Δ) zero (⇑ᵗ A) (λ X → X) (ν-subst A)
ν-reveal-env {X = zero} z<s =
  rv-hit refl refl
ν-reveal-env {X = suc X} (s<s X<Δ) =
  rv-miss (λ ()) refl

ν-reveal-typing :
  ∀ {Δ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  singleSealᵈ zero ∣ suc Δ ∣ (zero , ⇑ᵗ A) ∷ []
    ⊢ reveal B zero (⇑ᵗ A) ∶ B =⇒ ⇑ᵗ (B [ A ]ᵗ)
ν-reveal-typing {A = A} {B = B} hA hB =
  subst
    (λ T →
      singleSealᵈ zero ∣ _ ∣ _ ⊢ reveal B zero (⇑ᵗ A)
        ∶ B =⇒ T)
    (ν-subst-target A B)
    revealed
  where
    revealed′ :
      singleSealᵈ zero ∣ _ ∣ _ ⊢
        reveal (renameᵗ (λ X → X) B) zero (⇑ᵗ A)
        ∶ renameᵗ (λ X → X) B =⇒ substᵗ (ν-subst A) B
    revealed′ =
      reveal-typing-env
        hB
        (λ X<Δ → X<Δ)
        (ν-subst-wf hA)
        ν-reveal-env
        (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
        (here refl)
        singleSealMode

    revealed :
      singleSealᵈ zero ∣ _ ∣ _ ⊢ reveal B zero (⇑ᵗ A)
        ∶ B =⇒ substᵗ (ν-subst A) B
    revealed =
      subst
        (λ S →
          singleSealᵈ zero ∣ _ ∣ _ ⊢ reveal S zero (⇑ᵗ A)
            ∶ S =⇒ substᵗ (ν-subst A) B)
        (renameᵗ-id B)
        revealed′

ν-reveal-conversion :
  ∀ {Δ A B} →
  WfTy Δ A →
  WfTy (suc Δ) B →
  singleSealᵈ zero ∣ suc Δ ∣ (zero , ⇑ᵗ A) ∷ []
    ⊢ reveal B zero (⇑ᵗ A) ∶ B ↑ˢ ⇑ᵗ (B [ A ]ᵗ)
ν-reveal-conversion {A = A} {B = B} hA hB =
  subst
    (λ T →
      singleSealᵈ zero ∣ _ ∣ _ ⊢ reveal B zero (⇑ᵗ A)
        ∶ B ↑ˢ T)
    (ν-subst-target A B)
    revealed
  where
    revealed′ :
      singleSealᵈ zero ∣ _ ∣ _ ⊢
        reveal (renameᵗ (λ X → X) B) zero (⇑ᵗ A)
        ∶ renameᵗ (λ X → X) B ↑ˢ substᵗ (ν-subst A) B
    revealed′ =
      reveal-conversion-env
        hB
        (λ X<Δ → X<Δ)
        (ν-subst-wf hA)
        ν-reveal-env
        (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
        (here refl)
        singleSealMode

    revealed :
      singleSealᵈ zero ∣ _ ∣ _ ⊢ reveal B zero (⇑ᵗ A)
        ∶ B ↑ˢ substᵗ (ν-subst A) B
    revealed =
      subst
        (λ S →
          singleSealᵈ zero ∣ _ ∣ _ ⊢ reveal S zero (⇑ᵗ A)
            ∶ S ↑ˢ substᵗ (ν-subst A) B)
        (renameᵗ-id B)
        revealed′

------------------------------------------------------------------------
-- Cast plans for compiling consistency
------------------------------------------------------------------------

record CastPlan (Δ : TyCtx) (Σ : Store) (A B : Ty) : Set₁ where
  field
    -- Consistency witnesses are built from `idᵢ`, so the cast evidence is
    -- kept in `id-onlyᵈ` and relaxed only at the term-typing boundary.
    lower : Ty
    down : Coercion
    down⊢ : Δ ∣ Σ ⊢ down ∶ A =⇒ lower
    down⊒ : id-onlyᵈ ∣ Δ ∣ Σ ⊢ down ∶ A ⊒ lower
    lower⊑source :
      IWF._∣_⊢_⊑_⊣_ (idᵢ Δ) Δ lower A Δ

    up : Coercion
    up⊢ : Δ ∣ Σ ⊢ up ∶ lower =⇒ B
    up⊑ : id-onlyᵈ ∣ Δ ∣ Σ ⊢ up ∶ lower ⊑ B
    lower⊑target :
      IWF._∣_⊢_⊑_⊣_ (idᵢ Δ) Δ lower B Δ

open CastPlan public

consistency-cast-planᵢ :
  ∀ {Δ A B} →
  Label →
  (Σ[ C ∈ Ty ]
    (IWF._∣_⊢_⊑_⊣_ (idᵢ Δ) Δ C A Δ ×
     IWF._∣_⊢_⊑_⊣_ (idᵢ Δ) Δ C B Δ)) →
  CastPlan Δ [] A B
consistency-cast-planᵢ {Δ = Δ} ℓ (C , C⊑A , C⊑B)
    with mlb-type-from-lower-commonᵢ C⊑A C⊑B
       | mlb-type-from-lower-common-oldᵢ C⊑A C⊑B
consistency-cast-planᵢ {Δ = Δ} ℓ (C , C⊑A , C⊑B)
    | lower⊑source , lower⊑target
    | lower⊑source-old , lower⊑target-old
    with coerce-downⁿ ℓ
           (IWF.⊑-src-wf lower⊑source)
           (IWF.⊑-tgt-wf lower⊑source)
           (realizes-idᵢᴺᵂ-id-only Δ)
           lower⊑source-old
       | coerce-upʷ ℓ
           (IWF.⊑-src-wf lower⊑target)
           (IWF.⊑-tgt-wf lower⊑target)
           (realizes-idᵢᴺᵂ-id-only Δ)
           lower⊑target-old
consistency-cast-planᵢ {Δ = Δ} ℓ (C , C⊑A , C⊑B)
    | lower⊑source , lower⊑target
    | lower⊑source-old , lower⊑target-old
    | down , down⊒ | up , up⊑ =
  record
    { lower = mlb-type-from-lowerᵢ C⊑A C⊑B
    ; down = down
    ; down⊢ = id-onlyᵈ , proj₁ down⊒
    ; down⊒ = down⊒
    ; lower⊑source = lower⊑source
    ; up = up
    ; up⊢ = id-onlyᵈ , proj₁ up⊑
    ; up⊑ = up⊑
    ; lower⊑target = lower⊑target
    }

consistency-cast-plan :
  ∀ {Δ A B} →
  Label →
  Δ ⊢ A ~ B →
  CastPlan Δ [] A B
consistency-cast-plan ℓ (C , C⊑A , C⊑B) =
  consistency-cast-planᵢ ℓ
    (C , old⊑→wf-idᵢ C⊑A , old⊑→wf-idᵢ C⊑B)

arrow★-consistent :
  ∀ {Δ A} →
  Δ ⊢ A ~ ★ →
  Δ ⊢ (A ⇒ ★) ~ ★
arrow★-consistent (C , C⊑A , C⊑★) =
  C ⇒ ★ , (C⊑A ↦ id★) , (tag C⊑★ ⇛ id★)

cast :
  ∀ {Δ A B} →
  CastPlan Δ [] A B →
  Term →
  Term
cast plan M =
  (M ⟨ᵀ down plan ⟩) ⟨ᵀ up plan ⟩

cast⊢ :
  ∀ {Δ Γ A B M} →
  (plan : CastPlan Δ [] A B) →
  Δ ∣ [] ∣ Γ ⊢ᵀ M ⦂ A →
  Δ ∣ [] ∣ Γ ⊢ᵀ cast plan M ⦂ B
cast⊢ plan M⊢ with down⊢ plan | up⊢ plan
cast⊢ plan M⊢ | _ , down⊢ᵐ | _ , up⊢ᵐ =
  ⊢ᵀ⟨⟩ up⊢ᵐ (⊢ᵀ⟨⟩ down⊢ᵐ M⊢)

seal★-tag-or-id :
  ∀ {Σ} →
  TT.SealModeStore★ tag-or-idᵈ Σ
seal★-tag-or-id α ()

cast⊢ᵀ :
  ∀ {Δ Γ A B M} →
  (plan : CastPlan Δ [] A B) →
  TT._∣_∣_⊢_⦂_ Δ [] Γ M A →
  TT._∣_∣_⊢_⦂_ Δ [] Γ (cast plan M) B
cast⊢ᵀ plan M⊢ =
  TT.⊢⟨⟩⊑ TT.cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ (up⊑ plan))
    (TT.⊢⟨⟩⊒ TT.cast-tag-or-id seal★-tag-or-id
      (narrow-mode-relax id-only≤tag-or-idᵈ (down⊒ plan)) M⊢)

------------------------------------------------------------------------
-- Compilation
------------------------------------------------------------------------

compile :
  ∀ {Δ Γ M A} →
  CtxWf Δ Γ →
  Δ ∣ Γ ⊢ᴳ M ⦂ A →
  Σ[ N ∈ Term ] Δ ∣ [] ∣ Γ ⊢ᵀ N ⦂ A

compile-value :
  ∀ {Δ Γ M A} →
  (hΓ : CtxWf Δ Γ) →
  (vM : Valueᴳ M) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  Valueᵀ (proj₁ (compile hΓ M⊢))

compile hΓ (⊢ᴳ` x∈) =
  `ᵀ _ , ⊢ᵀ` x∈
compile hΓ (⊢ᴳƛ wfA M⊢) with compile (ctxWf-∷ wfA hΓ) M⊢
compile hΓ (⊢ᴳƛ wfA M⊢) | N , N⊢ =
  ƛᵀ N , ⊢ᵀƛ wfA N⊢
compile hΓ (⊢ᴳ· {ℓ = ℓ} L⊢ M⊢ A~A′)
    with compile hΓ L⊢ | compile hΓ M⊢
       | consistency-cast-plan ℓ (~-sym A~A′)
compile hΓ (⊢ᴳ· L⊢ M⊢ A~A′)
    | L′ , L′⊢ | M′ , M′⊢ | plan =
  L′ ·ᵀ cast plan M′ ,
  ⊢ᵀ· L′⊢ (cast⊢ plan M′⊢)
compile hΓ (⊢ᴳ·★ {ℓ = ℓ} L⊢ M⊢ A′~★)
    with compile hΓ L⊢ | compile hΓ M⊢
       | consistency-cast-plan ℓ (~-sym (arrow★-consistent A′~★))
compile hΓ (⊢ᴳ·★ L⊢ M⊢ A′~★)
    | L′ , L′⊢ | M′ , M′⊢ | plan =
  cast plan L′ ·ᵀ M′ ,
  ⊢ᵀ· (cast⊢ plan L′⊢) M′⊢
compile hΓ (⊢ᴳΛ {occ = occ} vM M⊢)
    with compile (CtxWf-⤊ hΓ) M⊢
       | compile-value (CtxWf-⤊ hΓ) vM M⊢
compile hΓ (⊢ᴳΛ {occ = occ} vM M⊢) | N , N⊢ | vN =
  Λᵀ N , ⊢ᵀΛ vN N⊢
compile hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA)
    with compile hΓ M⊢
compile hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA) | M′ , M′⊢ =
  νᵀ A M′ (reveal B zero (⇑ᵗ A)) ,
  ⊢ᵀν wfA M′⊢ (ν-reveal-typing wfA wfB)
compile hΓ (⊢ᴳ$ κ) =
  $ᵀ κ , ⊢ᵀ$ κ
compile hΓ (⊢ᴳ⊕ {ℓ = ℓ} L⊢ A~ℕ op M⊢ B~ℕ)
    with compile hΓ L⊢ | compile hΓ M⊢
       | consistency-cast-plan ℓ A~ℕ | consistency-cast-plan ℓ B~ℕ
compile hΓ (⊢ᴳ⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L′ , L′⊢ | M′ , M′⊢ | planL | planM =
  cast planL L′ ⊕ᵀ[ op ] cast planM M′ ,
  ⊢ᵀ⊕ (cast⊢ planL L′⊢) op (cast⊢ planM M′⊢)

compile-value hΓ (ƛᴳ A ⇒ M) (⊢ᴳƛ wfA M⊢)
    with compile (ctxWf-∷ wfA hΓ) M⊢
compile-value hΓ (ƛᴳ A ⇒ M) (⊢ᴳƛ wfA M⊢) | N , N⊢ =
  ƛᵀ N
compile-value hΓ ($ᴳ κ) (⊢ᴳ$ .κ) =
  $ᵀ κ
compile-value hΓ (Λᴳ M) (⊢ᴳΛ vM M⊢)
    with compile (CtxWf-⤊ hΓ) M⊢
       | compile-value (CtxWf-⤊ hΓ) vM M⊢
compile-value hΓ (Λᴳ M) (⊢ᴳΛ vM M⊢) | N , N⊢ | vN =
  Λᵀ vN

------------------------------------------------------------------------
-- Refined compilation for the DGG path
------------------------------------------------------------------------

compileᵀ :
  ∀ {Δ Γ M A} →
  CtxWf Δ Γ →
  Δ ∣ Γ ⊢ᴳ M ⦂ A →
  Σ[ N ∈ Term ] TT._∣_∣_⊢_⦂_ Δ [] Γ N A

compileᵀ-value :
  ∀ {Δ Γ M A} →
  (hΓ : CtxWf Δ Γ) →
  (vM : Valueᴳ M) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  Valueᵀ (proj₁ (compileᵀ hΓ M⊢))

compileᵀ hΓ (⊢ᴳ` x∈) =
  `ᵀ _ , TT.⊢` x∈
compileᵀ hΓ (⊢ᴳƛ wfA M⊢) with compileᵀ (ctxWf-∷ wfA hΓ) M⊢
compileᵀ hΓ (⊢ᴳƛ wfA M⊢) | N , N⊢ =
  ƛᵀ N , TT.⊢ƛ wfA N⊢
compileᵀ hΓ (⊢ᴳ· {ℓ = ℓ} L⊢ M⊢ A~A′)
    with compileᵀ hΓ L⊢ | compileᵀ hΓ M⊢
       | consistency-cast-plan ℓ (~-sym A~A′)
compileᵀ hΓ (⊢ᴳ· L⊢ M⊢ A~A′)
    | L′ , L′⊢ | M′ , M′⊢ | plan =
  L′ ·ᵀ cast plan M′ ,
  TT.⊢· L′⊢ (cast⊢ᵀ plan M′⊢)
compileᵀ hΓ (⊢ᴳ·★ {ℓ = ℓ} L⊢ M⊢ A′~★)
    with compileᵀ hΓ L⊢ | compileᵀ hΓ M⊢
       | consistency-cast-plan ℓ (~-sym (arrow★-consistent A′~★))
compileᵀ hΓ (⊢ᴳ·★ L⊢ M⊢ A′~★)
    | L′ , L′⊢ | M′ , M′⊢ | plan =
  cast plan L′ ·ᵀ M′ ,
  TT.⊢· (cast⊢ᵀ plan L′⊢) M′⊢
compileᵀ hΓ (⊢ᴳΛ {occ = occ} vM M⊢)
    with compileᵀ (CtxWf-⤊ hΓ) M⊢
       | compileᵀ-value (CtxWf-⤊ hΓ) vM M⊢
compileᵀ hΓ (⊢ᴳΛ {occ = occ} vM M⊢) | N , N⊢ | vN =
  Λᵀ N , TT.⊢Λ vN N⊢
compileᵀ hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA)
    with compileᵀ hΓ M⊢
compileᵀ hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA) | M′ , M′⊢ =
  νᵀ A M′ (reveal B zero (⇑ᵗ A)) ,
  TT.⊢ν↑ wfA M′⊢ (ν-reveal-conversion wfA wfB)
compileᵀ hΓ (⊢ᴳ$ κ) =
  $ᵀ κ , TT.⊢$ κ
compileᵀ hΓ (⊢ᴳ⊕ {ℓ = ℓ} L⊢ A~ℕ op M⊢ B~ℕ)
    with compileᵀ hΓ L⊢ | compileᵀ hΓ M⊢
       | consistency-cast-plan ℓ A~ℕ | consistency-cast-plan ℓ B~ℕ
compileᵀ hΓ (⊢ᴳ⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L′ , L′⊢ | M′ , M′⊢ | planL | planM =
  cast planL L′ ⊕ᵀ[ op ] cast planM M′ ,
  TT.⊢⊕ (cast⊢ᵀ planL L′⊢) op (cast⊢ᵀ planM M′⊢)

compileᵀ-value hΓ (ƛᴳ A ⇒ M) (⊢ᴳƛ wfA M⊢)
    with compileᵀ (ctxWf-∷ wfA hΓ) M⊢
compileᵀ-value hΓ (ƛᴳ A ⇒ M) (⊢ᴳƛ wfA M⊢) | N , N⊢ =
  ƛᵀ N
compileᵀ-value hΓ ($ᴳ κ) (⊢ᴳ$ .κ) =
  $ᵀ κ
compileᵀ-value hΓ (Λᴳ M) (⊢ᴳΛ vM M⊢)
    with compileᵀ (CtxWf-⤊ hΓ) M⊢
       | compileᵀ-value (CtxWf-⤊ hΓ) vM M⊢
compileᵀ-value hΓ (Λᴳ M) (⊢ᴳΛ vM M⊢) | N , N⊢ | vN =
  Λᵀ vN
