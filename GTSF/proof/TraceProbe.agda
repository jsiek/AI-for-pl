module proof.TraceProbe where

-- File Charter:
--   * Diagnostic probe for the standalone
--     `shifted-source-catchup-Λ-inversion` postulate in `proof.Catchup`.
--   * Constructs a beta-after-type-application trace whose shifted final
--     relation is admissible, but whose unshifted conclusion would require
--     typing a shifted function coercion outside its type context.
--   * The final theorem derives `⊥` from that postulate, showing the
--     standalone statement is too broad.  This does not refute the original
--     `⊒Λ` catchup-lemma case, because the probe does not satisfy its
--     premise-aware inner term-narrowing hypothesis.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import NarrowingExamples
open import proof.NuTermProperties using (renameᵗᵐ-preserves-Value)
open import proof.ReductionProperties using (value-no-step)
open import proof.Catchup using (shifted-source-catchup-Λ-inversion)

right-star-store-narrowing :
  1 ⊢ (0 ꞉= ★ ⊒) ∷ [] ꞉ [] ⊒ˢ ((0 , ★) ∷ [])
right-star-store-narrowing =
  ⊒ˢ-right wf★ ⊒ˢ-nil

id-var0-fun-right-≈ :
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ⊢
    id (＇ 0) ↦ id (＇ 0)
      ≈ (id (＇ 0) ↦ id (＇ 0))
        ⨾ⁿ (id (＇ 0) ↦ id (＇ 0))
      ∶ (＇ 0 ⇒ ＇ 0) ⊒ (＇ 0 ⇒ ＇ 0)
id-var0-fun-right-≈ =
  compose-rightⁿ empty-store-det id-var0-fun-empty⊒ id-var0-fun-empty⊒
    (endpointsⁿ refl refl refl refl
      right-star-store-narrowing
      wf-var0
      wf-var0
      (tag-or-idᵈ , id-var0-fun-star⊒)
      (_ , proj₂ (_⨟ⁿ_ {wfΣ = empty-store-det}
        id-var0-fun-empty⊒ id-var0-fun-empty⊒)))
  where
    wf-var0 :
      ∀ {Σ} →
      EndpointWf 1 Σ (＇ 0 ⇒ ＇ 0) (＇ 0 ⇒ ＇ 0)
    wf-var0 =
      ( wf⇒ˢ (wfVarᵗ z<s) (wfVarᵗ z<s)
      , wf⇒ˢ (wfVarᵗ z<s) (wfVarᵗ z<s)
      )

    id-var0-fun-empty⊒ =
      id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} {Σ = []} refl

    id-var0-fun-star⊒ =
      id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl

probe-c : Coercion
probe-c = id (＇ 0) ↦ id (＇ 0)

probe-body : Term
probe-body = (ƛ (` 0)) ⟨ probe-c ⟩

probe-N : Term
probe-N = (Λ probe-body) •

probe-V′ : Term
probe-V′ = ƛ (` 0)

probe-body⊒ :
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ probe-body ⊒ probe-V′ ∶ probe-c
probe-body⊒ =
  cast-⊒ id-var0-fun-cast id-var0-fun-right-≈
    (ƛ⊒ƛ id-var0-fun-cast (x⊒x id-var0-cast Z))

probe-W : Term
probe-W = (renameᵗᵐ (extᵗ suc) probe-body) [ zero ]ᵀ

probe-red :
  ⇑ᵗᵐ probe-N —↠[ keep ∷ [] ] probe-W
probe-red =
  ↠-step (pure-step (β-Λ• (renameᵗᵐ-preserves-Value (extᵗ suc)
    ((ƛ _) ⟨ _ ↦ _ ⟩)))) ↠-refl

probe-W-value : Value probe-W
probe-W-value = (ƛ _) ⟨ _ ↦ _ ⟩

no-probe-inner-premise :
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ ⇑ᵗᵐ probe-N ⊒ probe-V′ ∶ probe-c →
  ⊥
no-probe-inner-premise ()

no-wf-var1-empty :
  WfTyˢ 1 [] (＇ 1) →
  ⊥
no-wf-var1-empty (wfVarᵗ (s<s ()))
no-wf-var1-empty (wfVarˢ ())

no-wf-var1 :
  WfTy 1 (＇ 1) →
  ⊥
no-wf-var1 (wfVar (s<s ()))

no-shifted-probe-c :
  ∀ {μ Σ A B} →
  μ ∣ 1 ∣ Σ ⊢ ⇑ᶜ probe-c ∶ A ⊒ B →
  ⊥
no-shifted-probe-c (cast-fun (cast-id h ok) t⊢ , cross (sʷ ↦ tⁿ)) =
  no-wf-var1 h

no-probe-compose :
  ∀ {A B r p} →
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ⊢
    r ≈ ⇑ᶜ probe-c ⨾ⁿ p ∶ A ⊒ B →
  ⊥
no-probe-compose (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  no-shifted-probe-c t⊒

fun-left : Coercion → Coercion
fun-left (id A) = id A
fun-left (c ︔ d) = c ︔ d
fun-left (c ↦ d) = c
fun-left (`∀ c) = `∀ c
fun-left (A !) = A !
fun-left (A ？) = A ？
fun-left (seal A α) = seal A α
fun-left (unseal α A) = unseal α A
fun-left (gen A c) = gen A c
fun-left (inst B c) = inst B c

no-dual-id-var1-widen :
  ∀ {μ Σ c A B} →
  - c ≡ id (＇ 1) →
  μ ∣ 1 ∣ Σ ⊢ c ∶ A ⊑ B →
  ⊥
no-dual-id-var1-widen {c = id A} refl (cast-id h ok , cross (id-＇ .1)) =
  no-wf-var1 h
no-dual-id-var1-widen {c = c ︔ d} () c⊑
no-dual-id-var1-widen {c = c ↦ d} () c⊑
no-dual-id-var1-widen {c = `∀ c} () c⊑
no-dual-id-var1-widen {c = (＇ X) !} () c⊑
no-dual-id-var1-widen {c = (‵ ι) !} () c⊑
no-dual-id-var1-widen {c = ★ !} () c⊑
no-dual-id-var1-widen {c = (A ⇒ B) !} () c⊑
no-dual-id-var1-widen {c = `∀ A !} () c⊑
no-dual-id-var1-widen {c = (＇ X) ？} () c⊑
no-dual-id-var1-widen {c = (‵ ι) ？} () c⊑
no-dual-id-var1-widen {c = ★ ？} () c⊑
no-dual-id-var1-widen {c = (A ⇒ B) ？} () c⊑
no-dual-id-var1-widen {c = `∀ A ？} () c⊑
no-dual-id-var1-widen {c = seal A α} () c⊑
no-dual-id-var1-widen {c = unseal α A} () c⊑
no-dual-id-var1-widen {c = gen A c} () c⊑
no-dual-id-var1-widen {c = inst B c} () c⊑

no-dual-shifted-probe-c :
  ∀ {μ Σ t A B} →
  - t ≡ ⇑ᶜ probe-c →
  μ ∣ 1 ∣ Σ ⊢ t ∶ A ⊒ B →
  ⊥
no-dual-shifted-probe-c {t = t₁ ↦ t₂} eq
    (cast-fun t₁⊢ t₂⊢ , cross (t₁ʷ ↦ t₂ⁿ)) =
  no-dual-id-var1-widen (cong fun-left eq) (t₁⊢ , t₁ʷ)

no-probe-compose-dual :
  ∀ {A B r t p} →
  - t ≡ ⇑ᶜ probe-c →
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  ⊥
no-probe-compose-dual eq (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  no-dual-shifted-probe-c eq t⊒

no-probe-conclusion-aux :
  ∀ {c} →
  c ≡ ⇑ᶜ probe-c →
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ c ⟩ ⊒ probe-V′ ∶ probe-c →
  ⊥
no-probe-conclusion-aux eq (cast+⊒ pᶜ r≈t⨟p M⊒M′) =
  no-probe-compose-dual eq r≈t⨟p
no-probe-conclusion-aux refl (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  no-probe-compose r≈t⨟p

no-probe-conclusion :
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ ⇑ᶜ probe-c ⟩ ⊒ probe-V′ ∶ probe-c →
  ⊥
no-probe-conclusion =
  no-probe-conclusion-aux refl

shifted-source-catchup-Λ-inversion-counterexample : ⊥
shifted-source-catchup-Λ-inversion-counterexample
    with shifted-source-catchup-Λ-inversion
      {Δ = 0} {σ = []} {χs = keep ∷ []} {W = probe-W}
      {Δ′ = 1} {Π = []} {Π′ = []} {π = []}
      {N = probe-N} {V′ = probe-V′} {p = probe-c}
      probe-W-value
      probe-red
      refl
      refl
      refl
      ⊒ˢ-nil
      probe-body⊒
shifted-source-catchup-Λ-inversion-counterexample
    | χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , N↠W′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body
    with N↠W′
shifted-source-catchup-Λ-inversion-counterexample
    | χs′ , .probe-N , Δ″ , Π″ , Π″′ , π′ ,
      () , _ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body
    | ↠-refl
shifted-source-catchup-Λ-inversion-counterexample
    | χs″ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , _ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body
    | ↠-step (pure-step (β-Λ• vBody)) body↠W′
    with body↠W′
shifted-source-catchup-Λ-inversion-counterexample
    | .(keep ∷ []) , .probe-W , .0 , .[] , .[] , .[] ,
      vW′ , _ , refl , refl , refl , ⊒ˢ-nil , body
    | ↠-step (pure-step (β-Λ• vBody)) body↠W′
    | ↠-refl =
  no-probe-conclusion body
shifted-source-catchup-Λ-inversion-counterexample
    | χs″ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , _ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body
    | ↠-step (pure-step (β-Λ• vBody)) body↠W′
    | ↠-step body→N N↠W′ =
  ⊥-elim (value-no-step probe-W-value body→N)
