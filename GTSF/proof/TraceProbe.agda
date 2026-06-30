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
--     premise-aware inner term-narrowing hypothesis.  In particular,
--     `no-probe-gen-premise` shows that `probe-c` cannot be used as the body
--     of the real empty-context `gen` coercion premise.
--   * Also includes small checked witnesses/exclusions that fence off failed
--     proof strategies for the real `⊒Λ` replay branch.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import NarrowingExamples
open import proof.CoercionProperties using (coercion-src-tgtᵐ)
open import proof.NarrowWidenProperties using (StoreDetWf)
open import proof.NuTermProperties using
  ( open0-ext-suc-cancelᵐ
  ; renameᵗᵐ-preserves-Value
  )
open import proof.ReductionProperties using
  ( ⇒-injective-left
  ; cast-term-injective-right
  ; value-no-step
  )
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

id-var1-fun : Coercion
id-var1-fun = id (＇ 1) ↦ id (＇ 1)

var1-fun : Coercion
var1-fun =
  ((＇ 1) !) ↦ ((＇ 1) ？)

var1-fun≢var0-fun :
  ＇ 1 ⇒ ＇ 1 ≡ ＇ 0 ⇒ ＇ 0 →
  ⊥
var1-fun≢var0-fun eq
    with ⇒-injective-left eq
... | ()

var1-fun≢star-fun :
  ＇ 1 ⇒ ＇ 1 ≡ ★ ⇒ ★ →
  ⊥
var1-fun≢star-fun ()

source-first-star-narrowing :
  2 ⊢ ((⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ []) ꞉
    ((zero , ★) ∷ []) ⊒ˢ ((suc zero , ★) ∷ [])
source-first-star-narrowing =
  ⊒ˢ-left (⊒ˢ-right wf★ ⊒ˢ-nil)

star0-store-det2 :
  StoreDetWf 2 ((zero , ★) ∷ [])
star0-store-det2 =
  record
    { at = record
        { bound = λ { (here refl) → z<s }
        ; wfTy = λ { (here refl) → wf★ }
        }
    ; wfOlder = λ { (here refl) → wf★ }
    ; unique = λ { (here refl) (here refl) → refl }
    }

wf-var1-fun :
  ∀ {Σ} →
  EndpointWf 2 Σ (＇ 1 ⇒ ＇ 1) (＇ 1 ⇒ ＇ 1)
wf-var1-fun =
  ( wf⇒ˢ (wfVarᵗ (s<s z<s)) (wfVarᵗ (s<s z<s))
  , wf⇒ˢ (wfVarᵗ (s<s z<s)) (wfVarᵗ (s<s z<s))
  )

wf-star-var1-fun :
  ∀ {Σ} →
  EndpointWf 2 Σ (★ ⇒ ★) (＇ 1 ⇒ ＇ 1)
wf-star-var1-fun =
  ( wf⇒ˢ wf★ˢ wf★ˢ
  , wf⇒ˢ (wfVarᵗ (s<s z<s)) (wfVarᵗ (s<s z<s))
  )

id-var1-fun-narrowingᵐ :
  ∀ {Σ} →
  tag-or-idᵈ ∣ 2 ∣ Σ ⊢ id-var1-fun ∶
    (＇ 1 ⇒ ＇ 1) ⊒ (＇ 1 ⇒ ＇ 1)
id-var1-fun-narrowingᵐ =
  cast-fun
    (cast-id (wfVar (s<s z<s)) refl)
    (cast-id (wfVar (s<s z<s)) refl) ,
  cross (cross (id-＇ 1) ↦ cross (id-＇ 1))

var1-fun-narrowingᵐ :
  ∀ {Σ} →
  tag-or-idᵈ ∣ 2 ∣ Σ ⊢ var1-fun ∶
    (★ ⇒ ★) ⊒ (＇ 1 ⇒ ＇ 1)
var1-fun-narrowingᵐ =
  cast-fun
    (cast-tag (wfVar (s<s z<s)) (＇ 1) refl)
    (cast-untag (wfVar (s<s z<s)) (＇ 1) refl) ,
  cross (tag (＇ 1) ↦ untag (＇ 1))

source-first-id-var1-right-≈ :
  2 ∣ (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ [] ⊢
    id-var1-fun ≈ id-var1-fun ⨾ⁿ id-var1-fun
      ∶ (＇ 1 ⇒ ＇ 1) ⊒ (＇ 1 ⇒ ＇ 1)
source-first-id-var1-right-≈ =
  compose-rightⁿ star0-store-det2
    id-var1-fun-narrowingᵐ
    id-var1-fun-narrowingᵐ
    (endpointsⁿ refl refl refl refl
      source-first-star-narrowing
      wf-var1-fun
      wf-var1-fun
      (tag-or-idᵈ , id-var1-fun-narrowingᵐ)
      (_ , proj₂ (_⨟ⁿ_ {wfΣ = star0-store-det2}
        id-var1-fun-narrowingᵐ
        id-var1-fun-narrowingᵐ)))

id-var1-cast :
  ∀ {Σ} →
  2 ∣ Σ ⊢ id (＇ 1) ∶ᶜ ＇ 1 ⊒ ＇ 1
id-var1-cast =
  cast-id (wfVar (s<s z<s)) refl , cross (id-＇ 1)

id-var1-fun-cast :
  ∀ {Σ} →
  2 ∣ Σ ⊢ id-var1-fun ∶ᶜ
    (＇ 1 ⇒ ＇ 1) ⊒ (＇ 1 ⇒ ＇ 1)
id-var1-fun-cast =
  id-var1-fun-narrowingᵐ

var1-fun-cast :
  ∀ {Σ} →
  2 ∣ Σ ⊢ var1-fun ∶ᶜ
    (★ ⇒ ★) ⊒ (＇ 1 ⇒ ＇ 1)
var1-fun-cast =
  var1-fun-narrowingᵐ

source-first-var1-fun-right-≈ :
  2 ∣ (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ [] ⊢
    var1-fun ≈ var1-fun ⨾ⁿ id-var1-fun
      ∶ (★ ⇒ ★) ⊒ (＇ 1 ⇒ ＇ 1)
source-first-var1-fun-right-≈ =
  compose-rightⁿ star0-store-det2
    var1-fun-narrowingᵐ
    id-var1-fun-narrowingᵐ
    (endpointsⁿ refl refl refl refl
      source-first-star-narrowing
      wf-star-var1-fun
      wf-star-var1-fun
      (tag-or-idᵈ , var1-fun-narrowingᵐ)
      (_ , proj₂ (_⨟ⁿ_ {wfΣ = star0-store-det2}
        var1-fun-narrowingᵐ
        id-var1-fun-narrowingᵐ)))

source-first-id-var1-cast-value :
  Value ((ƛ (` 0)) ⟨ id-var1-fun ⟩)
source-first-id-var1-cast-value =
  (ƛ (` 0)) ⟨ id (＇ 1) ↦ id (＇ 1) ⟩

source-first-id-var1-cast⊒ :
  2 ∣ (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ id-var1-fun ⟩ ⊒ ƛ (` 0) ∶ id-var1-fun
source-first-id-var1-cast⊒ =
  cast-⊒ id-var1-fun-cast source-first-id-var1-right-≈
    (ƛ⊒ƛ id-var1-fun-cast (x⊒x id-var1-cast Z))

source-first-var1-source-cast⊒ :
  2 ∣ (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ - var1-fun ⟩ ⊒ ƛ (` 0) ∶ var1-fun
source-first-var1-source-cast⊒ =
  cast+⊒
    {p = id-var1-fun}
    {r = var1-fun}
    {t = var1-fun}
    id-var1-fun-cast
    source-first-var1-fun-right-≈
    (ƛ⊒ƛ id-var1-fun-cast (x⊒x id-var1-cast Z))

target-first-id-var1-probe-compose⊥ :
  ∀ {A B r} →
  2 ∣ (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ [] ⊢
    r ≈ id-var1-fun ⨾ⁿ probe-c ∶ A ⊒ B →
  ⊥
target-first-id-var1-probe-compose⊥
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  var1-fun≢var0-fun
    (trans (proj₂ (coercion-src-tgtᵐ (proj₁ t⊒)))
      (sym (proj₁ (coercion-src-tgtᵐ (proj₁ p⊒)))))

mixed-id-var1-target-compose⊥ :
  2 ∣ (zero ꞉= ★ ⊒) ∷ (⊒ suc zero ꞉=☆) ∷ [] ⊢
    probe-c ≈ id-var1-fun ⨾ⁿ probe-c
      ∶ (＇ 0 ⇒ ＇ 0) ⊒ (＇ 0 ⇒ ＇ 0) →
  ⊥
mixed-id-var1-target-compose⊥
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  var1-fun≢var0-fun (proj₁ (coercion-src-tgtᵐ (proj₁ t⊒)))

no-id-var1-shifted-var0-compose :
  ∀ {A B r} →
  2 ∣ (⊒ zero ꞉=☆) ∷ (suc zero ꞉= ★ ⊒) ∷ [] ⊢
    r ≈ id-var1-fun ⨾ⁿ ⇑ᶜ var0-fun ∶ A ⊒ B →
  ⊥
no-id-var1-shifted-var0-compose
    (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  var1-fun≢star-fun
    (trans (proj₂ (coercion-src-tgtᵐ (proj₁ t⊒)))
      (sym (proj₁ (coercion-src-tgtᵐ (proj₁ p⊒)))))

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

probe-W≡body : probe-W ≡ probe-body
probe-W≡body = open0-ext-suc-cancelᵐ probe-body

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

no-wf-var0 :
  WfTy 0 (＇ 0) →
  ⊥
no-wf-var0 (wfVar ())

no-shift-var0 :
  ∀ {A} →
  ⇑ᵗ A ≡ ＇ 0 →
  ⊥
no-shift-var0 {A = ＇ X} ()
no-shift-var0 {A = ‵ ι} ()
no-shift-var0 {A = ★} ()
no-shift-var0 {A = A ⇒ B} ()
no-shift-var0 {A = `∀ A} ()

no-shift-var0-fun :
  ∀ {A} →
  ⇑ᵗ A ≡ ＇ 0 ⇒ ＇ 0 →
  ⊥
no-shift-var0-fun {A = ＇ X} ()
no-shift-var0-fun {A = ‵ ι} ()
no-shift-var0-fun {A = ★} ()
no-shift-var0-fun {A = A ⇒ B} eq =
  no-shift-var0 (⇒-injective-left eq)
no-shift-var0-fun {A = `∀ A} ()

no-shift-var0-fun-left :
  ∀ {A B} →
  ⇑ᵗ A ≡ ＇ 0 ⇒ B →
  ⊥
no-shift-var0-fun-left {A = ＇ X} ()
no-shift-var0-fun-left {A = ‵ ι} ()
no-shift-var0-fun-left {A = ★} ()
no-shift-var0-fun-left {A = A ⇒ B} eq =
  no-shift-var0 (⇒-injective-left eq)
no-shift-var0-fun-left {A = `∀ A} ()

no-probe-c-empty :
  ∀ {μ Σ A B} →
  μ ∣ 0 ∣ Σ ⊢ probe-c ∶ A ⊒ B →
  ⊥
no-probe-c-empty (cast-fun (cast-id h ok) t⊢ ,
                   cross (sʷ ↦ tⁿ)) =
  no-wf-var0 h

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

no-probe-compose-empty :
  ∀ {A B r p} →
  0 ∣ [] ⊢ r ≈ probe-c ⨾ⁿ p ∶ A ⊒ B →
  ⊥
no-probe-compose-empty (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  no-probe-c-empty t⊒

no-id-var0-fun-shift-source :
  ∀ {μ S T A} →
  μ ∣ 1 ∣ [] ⊢ id (＇ 0) ↦ id (＇ 0) ∶ S =⇒ T →
  S ≡ ⇑ᵗ A →
  ⊥
no-id-var0-fun-shift-source (cast-fun (cast-id h ok) t⊢) eq =
  no-shift-var0-fun-left (sym eq)

no-probe-gen-body-source :
  ∀ {μ A B} →
  μ ∣ 1 ∣ [] ⊢ probe-c ∶ ⇑ᵗ A =⇒ B →
  ⊥
no-probe-gen-body-source body⊢ =
  no-id-var0-fun-shift-source body⊢ refl

no-probe-gen-premise :
  ∀ {A B} →
  0 ∣ [] ⊢ gen A probe-c ∶ᶜ A ⊒ `∀ B →
  ⊥
no-probe-gen-premise (cast-gen hA occ body⊢ , gen bodyⁿ) =
  no-probe-gen-body-source body⊢

no-id-var1-fun-gen-target :
  ∀ {Δ Σ A} →
  Δ ∣ Σ ⊢ gen A id-var1-fun ∶ᶜ A ⊒ `∀ (＇ 1 ⇒ ＇ 1) →
  ⊥
no-id-var1-fun-gen-target (cast-gen hA () body⊢ , gen bodyⁿ)

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

no-widen-var0-untag :
  ∀ {μ Δ Σ A B} →
  μ ∣ Δ ∣ Σ ⊢ (＇ 0) ？ ∶ A ⊑ B →
  ⊥
no-widen-var0-untag ((cast-untag hG gG ok) , cross ())

no-dual-var0-tag-widen :
  ∀ {μ Δ Σ c A B} →
  - c ≡ (＇ 0) ! →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  ⊥
no-dual-var0-tag-widen {c = id A} () c⊑
no-dual-var0-tag-widen {c = c ︔ d} () c⊑
no-dual-var0-tag-widen {c = c ↦ d} () c⊑
no-dual-var0-tag-widen {c = `∀ c} () c⊑
no-dual-var0-tag-widen {c = (＇ X) !} () c⊑
no-dual-var0-tag-widen {c = (‵ ι) !} () c⊑
no-dual-var0-tag-widen {c = ★ !} () c⊑
no-dual-var0-tag-widen {c = (A ⇒ B) !} () c⊑
no-dual-var0-tag-widen {c = `∀ A !} () c⊑
no-dual-var0-tag-widen {c = (＇ X) ？} refl c⊑ =
  no-widen-var0-untag c⊑
no-dual-var0-tag-widen {c = (‵ ι) ？} () c⊑
no-dual-var0-tag-widen {c = ★ ？} () c⊑
no-dual-var0-tag-widen {c = (A ⇒ B) ？} () c⊑
no-dual-var0-tag-widen {c = `∀ A ？} () c⊑
no-dual-var0-tag-widen {c = seal A α} () c⊑
no-dual-var0-tag-widen {c = unseal α A} () c⊑
no-dual-var0-tag-widen {c = gen A c} () c⊑
no-dual-var0-tag-widen {c = inst B c} () c⊑

no-dual-var0-fun-narrow :
  ∀ {μ Δ Σ t A B} →
  - t ≡ var0-fun →
  μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ B →
  ⊥
no-dual-var0-fun-narrow {t = id A} () t⊒
no-dual-var0-fun-narrow {t = t₁ ︔ t₂} () t⊒
no-dual-var0-fun-narrow {t = t₁ ↦ t₂} eq
    (cast-fun t₁⊢ t₂⊢ , cross (t₁ʷ ↦ t₂ⁿ)) =
  no-dual-var0-tag-widen (cong fun-left eq) (t₁⊢ , t₁ʷ)
no-dual-var0-fun-narrow {t = `∀ t} () t⊒
no-dual-var0-fun-narrow {t = (＇ X) !} () t⊒
no-dual-var0-fun-narrow {t = (‵ ι) !} () t⊒
no-dual-var0-fun-narrow {t = ★ !} () t⊒
no-dual-var0-fun-narrow {t = (A ⇒ B) !} () t⊒
no-dual-var0-fun-narrow {t = `∀ A !} () t⊒
no-dual-var0-fun-narrow {t = (＇ X) ？} () t⊒
no-dual-var0-fun-narrow {t = (‵ ι) ？} () t⊒
no-dual-var0-fun-narrow {t = ★ ？} () t⊒
no-dual-var0-fun-narrow {t = (A ⇒ B) ？} () t⊒
no-dual-var0-fun-narrow {t = `∀ A ？} () t⊒
no-dual-var0-fun-narrow {t = seal A α} () t⊒
no-dual-var0-fun-narrow {t = unseal α A} () t⊒
no-dual-var0-fun-narrow {t = gen A t} () t⊒
no-dual-var0-fun-narrow {t = inst B t} () t⊒

star-fun≢var0-fun :
  ★ ⇒ ★ ≡ ＇ 0 ⇒ ＇ 0 →
  ⊥
star-fun≢var0-fun ()

no-var0-fun-self-compose :
  ∀ {A B r} →
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ⊢
    r ≈ var0-fun ⨾ⁿ var0-fun ∶ A ⊒ B →
  ⊥
no-var0-fun-self-compose
    (compose-rightⁿ wfΣ
      (t⊢@(cast-fun t₁⊢ t₂⊢) , cross (t₁ʷ ↦ t₂ⁿ))
      (p⊢@(cast-fun p₁⊢ p₂⊢) , cross (p₁ʷ ↦ p₂ⁿ))
      r≈t⨟p) =
  star-fun≢var0-fun
    (trans (proj₁ (coercion-src-tgtᵐ p⊢))
      (sym (proj₂ (coercion-src-tgtᵐ t⊢))))

no-legal-target-cast-body-aux :
  ∀ {c} →
  c ≡ var0-fun →
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ c ⟩ ⊒ ƛ (` 0) ∶ var0-fun →
  ⊥
no-legal-target-cast-body-aux eq
    (cast+⊒ {t = t} pᶜ
      (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) M⊒M′) =
  no-dual-var0-fun-narrow eq t⊒
no-legal-target-cast-body-aux refl
    (cast-⊒ pᶜ r≈t⨟p M⊒M′) =
  no-var0-fun-self-compose r≈t⨟p

no-legal-target-cast-body :
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ var0-fun ⟩ ⊒ ƛ (` 0) ∶ var0-fun →
  ⊥
no-legal-target-cast-body =
  no-legal-target-cast-body-aux refl

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

no-dual-id-var0-widen :
  ∀ {μ Σ c A B} →
  - c ≡ id (＇ 0) →
  μ ∣ 0 ∣ Σ ⊢ c ∶ A ⊑ B →
  ⊥
no-dual-id-var0-widen {c = id A} refl (cast-id h ok , cross (id-＇ .0)) =
  no-wf-var0 h
no-dual-id-var0-widen {c = c ︔ d} () c⊑
no-dual-id-var0-widen {c = c ↦ d} () c⊑
no-dual-id-var0-widen {c = `∀ c} () c⊑
no-dual-id-var0-widen {c = (＇ X) !} () c⊑
no-dual-id-var0-widen {c = (‵ ι) !} () c⊑
no-dual-id-var0-widen {c = ★ !} () c⊑
no-dual-id-var0-widen {c = (A ⇒ B) !} () c⊑
no-dual-id-var0-widen {c = `∀ A !} () c⊑
no-dual-id-var0-widen {c = (＇ X) ？} () c⊑
no-dual-id-var0-widen {c = (‵ ι) ？} () c⊑
no-dual-id-var0-widen {c = ★ ？} () c⊑
no-dual-id-var0-widen {c = (A ⇒ B) ？} () c⊑
no-dual-id-var0-widen {c = `∀ A ？} () c⊑
no-dual-id-var0-widen {c = seal A α} () c⊑
no-dual-id-var0-widen {c = unseal α A} () c⊑
no-dual-id-var0-widen {c = gen A c} () c⊑
no-dual-id-var0-widen {c = inst B c} () c⊑

no-dual-shifted-probe-c :
  ∀ {μ Σ t A B} →
  - t ≡ ⇑ᶜ probe-c →
  μ ∣ 1 ∣ Σ ⊢ t ∶ A ⊒ B →
  ⊥
no-dual-shifted-probe-c {t = id A} () t⊒
no-dual-shifted-probe-c {t = t₁ ︔ t₂} () t⊒
no-dual-shifted-probe-c {t = t₁ ↦ t₂} eq
    (cast-fun t₁⊢ t₂⊢ , cross (t₁ʷ ↦ t₂ⁿ)) =
  no-dual-id-var1-widen (cong fun-left eq) (t₁⊢ , t₁ʷ)
no-dual-shifted-probe-c {t = `∀ t} () t⊒
no-dual-shifted-probe-c {t = (＇ X) !} () t⊒
no-dual-shifted-probe-c {t = (‵ ι) !} () t⊒
no-dual-shifted-probe-c {t = ★ !} () t⊒
no-dual-shifted-probe-c {t = (A ⇒ B) !} () t⊒
no-dual-shifted-probe-c {t = `∀ A !} () t⊒
no-dual-shifted-probe-c {t = (＇ X) ？} () t⊒
no-dual-shifted-probe-c {t = (‵ ι) ？} () t⊒
no-dual-shifted-probe-c {t = ★ ？} () t⊒
no-dual-shifted-probe-c {t = (A ⇒ B) ？} () t⊒
no-dual-shifted-probe-c {t = `∀ A ？} () t⊒
no-dual-shifted-probe-c {t = seal A α} () t⊒
no-dual-shifted-probe-c {t = unseal α A} () t⊒
no-dual-shifted-probe-c {t = gen A t} () t⊒
no-dual-shifted-probe-c {t = inst B t} () t⊒

no-dual-probe-c-empty :
  ∀ {μ Σ t A B} →
  - t ≡ probe-c →
  μ ∣ 0 ∣ Σ ⊢ t ∶ A ⊒ B →
  ⊥
no-dual-probe-c-empty {t = id A} () t⊒
no-dual-probe-c-empty {t = t₁ ︔ t₂} () t⊒
no-dual-probe-c-empty {t = t₁ ↦ t₂} eq
    (cast-fun t₁⊢ t₂⊢ , cross (t₁ʷ ↦ t₂ⁿ)) =
  no-dual-id-var0-widen (cong fun-left eq) (t₁⊢ , t₁ʷ)
no-dual-probe-c-empty {t = `∀ t} () t⊒
no-dual-probe-c-empty {t = (＇ X) !} () t⊒
no-dual-probe-c-empty {t = (‵ ι) !} () t⊒
no-dual-probe-c-empty {t = ★ !} () t⊒
no-dual-probe-c-empty {t = (A ⇒ B) !} () t⊒
no-dual-probe-c-empty {t = `∀ A !} () t⊒
no-dual-probe-c-empty {t = (＇ X) ？} () t⊒
no-dual-probe-c-empty {t = (‵ ι) ？} () t⊒
no-dual-probe-c-empty {t = ★ ？} () t⊒
no-dual-probe-c-empty {t = (A ⇒ B) ？} () t⊒
no-dual-probe-c-empty {t = `∀ A ？} () t⊒
no-dual-probe-c-empty {t = seal A α} () t⊒
no-dual-probe-c-empty {t = unseal α A} () t⊒
no-dual-probe-c-empty {t = gen A t} () t⊒
no-dual-probe-c-empty {t = inst B t} () t⊒

no-probe-compose-dual :
  ∀ {A B r t p} →
  - t ≡ ⇑ᶜ probe-c →
  1 ∣ (0 ꞉= ★ ⊒) ∷ [] ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  ⊥
no-probe-compose-dual eq (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  no-dual-shifted-probe-c eq t⊒

no-probe-compose-dual-empty :
  ∀ {A B r t p} →
  - t ≡ probe-c →
  0 ∣ [] ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  ⊥
no-probe-compose-dual-empty eq (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  no-dual-probe-c-empty eq t⊒

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

no-probe-outer-by-eq :
  ∀ {M} →
  M ≡ (ƛ (` 0)) ⟨ probe-c ⟩ →
  0 ∣ [] ∣ [] ⊢ M ⊒ Λ probe-V′ ∶ gen (★ ⇒ ★) probe-c →
  ⊥
no-probe-outer-by-eq eq (⊒Λ pᶜ body) =
  no-probe-conclusion
    (subst
      (λ S → 1 ∣ (0 ꞉= ★ ⊒) ∷ [] ∣ []
        ⊢ ⇑ᵗᵐ S ⊒ probe-V′ ∶ probe-c)
      eq
      body)
no-probe-outer-by-eq eq
    (cast+⊒ {t = t} pᶜ r≈t⨟p M⊒M′) =
  no-probe-compose-dual-empty (cast-term-injective-right eq) r≈t⨟p
no-probe-outer-by-eq eq
    (cast-⊒ {t = t} pᶜ r≈t⨟p M⊒M′) =
  no-probe-compose-empty
    (subst
      (λ t₀ → 0 ∣ [] ⊢ _ ≈ t₀ ⨾ⁿ _ ∶ _ ⊒ _)
      (cast-term-injective-right eq)
      r≈t⨟p)

no-probe-outer-explicit :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ probe-c ⟩
      ⊒ Λ probe-V′ ∶ gen (★ ⇒ ★) probe-c →
  ⊥
no-probe-outer-explicit =
  no-probe-outer-by-eq refl

no-probe-outer-conclusion :
  0 ∣ [] ∣ []
    ⊢ probe-W ⊒ Λ probe-V′ ∶ gen (★ ⇒ ★) probe-c →
  ⊥
no-probe-outer-conclusion body =
  no-probe-outer-explicit
    (subst
      (λ S → 0 ∣ [] ∣ []
        ⊢ S ⊒ Λ probe-V′ ∶ gen (★ ⇒ ★) probe-c)
      probe-W≡body
      body)

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
      vW′ , noW′ , N↠W′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body
    with N↠W′
shifted-source-catchup-Λ-inversion-counterexample
    | χs′ , .probe-N , Δ″ , Π″ , Π″′ , π′ ,
      () , _ , _ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body
    | ↠-refl
shifted-source-catchup-Λ-inversion-counterexample
    | χs″ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , noW′ , _ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body
    | ↠-step (pure-step (β-Λ• vBody)) body↠W′
    with body↠W′
shifted-source-catchup-Λ-inversion-counterexample
    | .(keep ∷ []) , .probe-W , .0 , .[] , .[] , .[] ,
      vW′ , noW′ , _ , refl , refl , refl , ⊒ˢ-nil , body
    | ↠-step (pure-step (β-Λ• vBody)) body↠W′
    | ↠-refl =
  no-probe-conclusion body
shifted-source-catchup-Λ-inversion-counterexample
    | χs″ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , noW′ , _ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body
    | ↠-step (pure-step (β-Λ• vBody)) body↠W′
    | ↠-step body→N N↠W′ =
  ⊥-elim (value-no-step probe-W-value body→N)
