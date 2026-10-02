module examples.Eval where

-- File Charter:
--   * (GTNF) FORKED FROM strong-rep-nu.Eval.  New: every cast and
--     blame rule in the redex search (`castRedex`, `instX?`, the IdDyn
--     clauses of `bdyRedex`), the `blamed` final state, `Answer` (a run
--     may end in a value or in blame) as `Reaches`' `endAnswer`, and
--     §11 `evalRules`, the names of the rules a run fired.
--   * THE STEP FUNCTION AND THE EVALUATOR BUILT ON IT.  §1 decides the
--     classifications the rules guard on; §2 assembles each boundary
--     rule's side conditions; §3 is the redex search by head shape;
--     §4 `step`, leftmost-outermost, returning the contractum, the
--     allocation and the step derivation; §5 `stepTo`/`Steps`;
--     §6–§7 `Trace` and `eval`; §8–§9 reading a trace; §10 `Report`
--     and `Reaches`.
--   * NO METATHEORY IS NEEDED AND NONE IS CLAIMED.  `step` RETURNS THE
--     DERIVATION, so soundness is its type; a `nothing` means only
--     that this search found no redex — that other half is `progress`.
--   * WHAT A RUN ASSERTS.  `eval` is `step ⨟ check⊢` iterated with
--     fuel: the contractum is CHECKED, not retyped by preservation.
--     `illtyped` is the ONLY way a type is lost along a `Trace`, and
--     `Checked tr` is the unit record exactly when none occurs — so a
--     concrete run's subject reduction is checked, not proved.
-- Commentary (νF): SystemF/agda/strong-rep-nu/Commentary.md § Eval.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.Empty using (⊥)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Types
  using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀; _≟ᵗ_; Base; base-ℕ; base-𝔹)
open import Relation.Nullary using (yes; no)
open import Ctx
open import Conversion
open import Boundary
open import Coercion
open import Terms
open import TermSubst
open import Reduction
open import examples.TypeCheck
  using (interior?; conversion?; ∋:=?; read?; convTy?;
         rebase?; weaken?; weakenᵀ?; check⊢; inert?; inertTail?;
         simple?; value?; groundNV?; fresh-name?)

------------------------------------------------------------------------
-- 1. Deciding the classifications the rules guard on
------------------------------------------------------------------------

base? : (A : Ty) → Maybe (Base A)
base? (` X)   = nothing
base? `ℕ      = just base-ℕ
base? `𝔹      = just base-𝔹
base? ★       = nothing
base? (A ⇒ B) = nothing
base? (`∀ A)  = nothing

-- `blame?` recognizes the blame term, for the Blame rules
blame? : (M : Term) → Maybe (∃[ ℓ ] (M ≡ blame ℓ))
blame? (blame ℓ)        = just (ℓ , refl)
blame? (` x)            = nothing
blame? ($ n)            = nothing
blame? `true            = nothing
blame? `false           = nothing
blame? (ƛ A ∙ N)        = nothing
blame? (L · M)          = nothing
blame? (Λ N)            = nothing
blame? (ν A · L ⟨ c ⟩)  = nothing
blame? (M ⟪ Θ , c ⟫)    = nothing
blame? (M ⟨ μ ∣ p ⟩)    = nothing

-- `inert?`, `inertTail?`, `simple?`, `value?`, `inertC?`, `groundNV?`
-- and `fresh-name?` live in TypeCheck and are used here through its
-- `open import`.

------------------------------------------------------------------------
-- 2. The side conditions the boundary rules carry
------------------------------------------------------------------------

-- `Merge`'s premises: the three readings, and both conversions
-- weakened onto the merged frame's conversion context.
MergePremises : Ctxᵗ → Boundary → Boundary → Tail → Conv → Set
MergePremises Δ Θ₁ Θ₂ t₁ c₂ =
  Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δ₁ᶜ ∈ Ctxᵗ ] Σ[ Δ₂ᶜ ∈ Ctxᵗ ] Σ[ Δ⋉ᶜ ∈ Ctxᵗ ]
    Σ[ t₁′ ∈ Tail ] Σ[ c₂′ ∈ Conv ]
      ((Δ ⊢ⁱ Θ₂ ⇒ Δᵢ) × (Δᵢ ⊢ᶜ Θ₁ ⇒ Δ₁ᶜ) × (Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ)
        × (Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ)
        × SameConv Δ⋉ᶜ (tail t₁′) Δ₁ᶜ (tail t₁)
        × SameConv Δ⋉ᶜ c₂′ Δ₂ᶜ c₂)

mergePremises? : (Δ : Ctxᵗ) (Θ₁ Θ₂ : Boundary) (t₁ : Tail) (c₂ : Conv)
  → Maybe (MergePremises Δ Θ₁ Θ₂ t₁ c₂)
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ with interior? Δ Θ₂
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | nothing = nothing
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | just (Δᵢ , ri) with conversion? Δᵢ Θ₁
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | just (Δᵢ , ri) | nothing = nothing
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  with conversion? Δ Θ₂
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | nothing = nothing
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ₂ᶜ , r₂) with conversion? Δ (Θ₁ ++ Θ₂)
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ₂ᶜ , r₂) | nothing = nothing
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ₂ᶜ , r₂) | just (Δ⋉ᶜ , r⋉)
  with weakenᵀ? (names Δ₁ᶜ) (names Δ⋉ᶜ) t₁
     | weaken? (names Δ₂ᶜ) (names Δ⋉ᶜ) c₂
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ₂ᶜ , r₂) | just (Δ⋉ᶜ , r⋉)
  | just (t₁′ , r , p , q) | just (c₂′ , sc₂) =
  just (Δᵢ , Δ₁ᶜ , Δ₂ᶜ , Δ⋉ᶜ , t₁′ , c₂′ , ri , r₁ , r₂ , r⋉
       , (tail r , sameᶜ-tail p , sameᶜ-tail q) , sc₂)
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ₂ᶜ , r₂) | just (Δ⋉ᶜ , r⋉)
  | just (t₁′ , r , p , q) | nothing = nothing
mergePremises? Δ Θ₁ Θ₂ t₁ c₂ | just (Δᵢ , ri) | just (Δ₁ᶜ , r₁)
  | just (Δ₂ᶜ , r₂) | just (Δ⋉ᶜ , r⋉)
  | nothing | m = nothing

-- `Wrap`'s crossing premises.  The redex fixes only Δ, Θ and `s`; the
-- dual's conversion context is built here.
CrossPremises : Ctxᵗ → Boundary → Conv → Set
CrossPremises Δ Θ s =
  Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δᵈ ∈ Ctxᵗ ] Σ[ s′ ∈ Conv ]
    ((Δ ⊢ᶜ Θ ⇒ Δᶜ) × (Δ ⊢ⁱ Θ ⇒ Δᵢ) × (Δᵢ ⊢ᶜ dual Θ ⇒ Δᵈ)
      × SameConv Δᵈ s′ Δᶜ s)

crossPremises? : (Δ : Ctxᵗ) (Θ : Boundary) (s : Conv)
  → Maybe (CrossPremises Δ Θ s)
crossPremises? Δ Θ s with conversion? Δ Θ
crossPremises? Δ Θ s | nothing = nothing
crossPremises? Δ Θ s | just (Δᶜ , rc) with interior? Δ Θ
crossPremises? Δ Θ s | just (Δᶜ , rc) | nothing = nothing
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri)
  with conversion? Δᵢ (dual Θ)
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri)
  | nothing = nothing
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri) | just (Δᵈ , rd)
  with weaken? (names Δᶜ) (names Δᵈ) s
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri) | just (Δᵈ , rd)
  | nothing = nothing
crossPremises? Δ Θ s | just (Δᶜ , rc) | just (Δᵢ , ri) | just (Δᵈ , rd)
  | just (s′ , sc) = just (Δᶜ , Δᵢ , Δᵈ , s′ , rc , ri , rd , sc)

-- (GTNF) `IdDyn-var`'s premises: the two readings of the scope, and
-- the conversion context's spelling `Xᶜ` of the interior name X.
IdDynPremises : Ctxᵗ → Boundary → ℕ → Set
IdDynPremises Δ Θ X =
  Σ[ Δᵢ ∈ Ctxᵗ ] Σ[ Δᶜ ∈ Ctxᵗ ] Σ[ Xᶜ ∈ ℕ ]
    ((Δ ⊢ⁱ Θ ⇒ Δᵢ) × (Δ ⊢ᶜ Θ ⇒ Δᶜ) × (Δᵢ ⊢ ` X ≈ ` Xᶜ ⊣ Δᶜ))

idDynPremises? : (Δ : Ctxᵗ) (Θ : Boundary) (X : ℕ)
  → Maybe (IdDynPremises Δ Θ X)
idDynPremises? Δ Θ X with interior? Δ Θ | conversion? Δ Θ
idDynPremises? Δ Θ X | just (Δᵢ , ri) | just (Δᶜ , rc)
  with rebase? (names Δᵢ) (names Δᶜ) (` X)
idDynPremises? Δ Θ X | just (Δᵢ , ri) | just (Δᶜ , rc)
  | just (` Xᶜ , R , p , q) = just (Δᵢ , Δᶜ , Xᶜ , ri , rc , R , q , p)
idDynPremises? Δ Θ X | just (Δᵢ , ri) | just (Δᶜ , rc)
  | just (A , R , p , q) = nothing
idDynPremises? Δ Θ X | just (Δᵢ , ri) | just (Δᶜ , rc) | nothing =
  nothing
idDynPremises? Δ Θ X | just (Δᵢ , ri) | nothing = nothing
idDynPremises? Δ Θ X | nothing | rc = nothing

------------------------------------------------------------------------
-- 3. The redexes, by the shape of the head
------------------------------------------------------------------------

-- An application whose two sides are values.  Matching on the head's
-- VALUE derivation is what refines its shape.
appRedex : (Δ : Ctxᵗ) {L M : Term} → Value L → Value M
  → Maybe (∃[ N ] ∃[ δ ] (Δ ⊢ L · M -→ N ∣ δ))
appRedex Δ (V-simple S-ƛ) vM = just (_ , none , Beta vM)
appRedex Δ (V-⟪⟫ {Θ = Θ} u (I-fun {s = s})) vM
  with crossPremises? Δ Θ s
appRedex Δ (V-⟪⟫ {Θ = Θ} u (I-fun {s = s})) vM
  | just (Δᶜ , Δᵢ , Δᵈ , s′ , rc , ri , rd , sc) =
  just (_ , none , Wrap u vM rc ri rd sc)
appRedex Δ (V-⟪⟫ {Θ = Θ} u (I-fun {s = s})) vM | nothing = nothing
appRedex Δ (V-simple (S-cast v I-↦)) vM =
  just (_ , none , CastFun v vM)
appRedex Δ (V-simple (S-cast v I-tag)) vM = nothing
appRedex Δ (V-simple (S-cast v I-∀ᵖ)) vM = nothing
appRedex Δ (V-simple (S-cast v I-gen)) vM = nothing
appRedex Δ (V-⟪⟫ u I-idv)      vM = nothing
appRedex Δ (V-⟪⟫ u I-all)      vM = nothing
appRedex Δ (V-⟪⟫ u I-seal)     vM = nothing
appRedex Δ (V-⟪⟫ u I-seal-seq) vM = nothing
appRedex Δ (V-fresh v fr)      vM = nothing
appRedex Δ (V-simple (S-Λ v))  vM = nothing
appRedex Δ (V-simple S-$)      vM = nothing
appRedex Δ (V-simple S-true)   vM = nothing
appRedex Δ (V-simple S-false)  vM = nothing

-- `inst_X` as a function on value derivations: one clause per canonical
-- ∀-value layer (design.md §6.2), nothing for the rest.
mutual
  instX? : {V : Term} → Value V → Maybe (∃[ N ] InstX V N)
  instX? (V-simple u) = instXˢ? u
  instX? (V-⟪⟫ u I-all) with instXˢ? u
  instX? (V-⟪⟫ u I-all) | just (N , i) = just (_ , inst-⟪⟫ u i)
  instX? (V-⟪⟫ u I-all) | nothing      = nothing
  instX? (V-⟪⟫ u I-idv)      = nothing
  instX? (V-⟪⟫ u I-fun)      = nothing
  instX? (V-⟪⟫ u I-seal)     = nothing
  instX? (V-⟪⟫ u I-seal-seq) = nothing
  instX? (V-fresh v fr)      = nothing

  instXˢ? : {U : Term} → Simple U → Maybe (∃[ N ] InstX U N)
  instXˢ? (S-Λ vN)          = just (_ , inst-Λ vN)
  instXˢ? (S-cast v I-gen)  = just (_ , inst-gen v)
  instXˢ? (S-cast v I-∀ᵖ) with instX? v
  instXˢ? (S-cast v I-∀ᵖ) | just (N , i) = just (_ , inst-∀ v i)
  instXˢ? (S-cast v I-∀ᵖ) | nothing      = nothing
  instXˢ? (S-cast v I-tag)  = nothing
  instXˢ? (S-cast v I-↦)    = nothing
  instXˢ? S-$               = nothing
  instXˢ? S-true            = nothing
  instXˢ? S-false           = nothing
  instXˢ? S-ƛ               = nothing

-- A `ν` whose body is a ∀-value: `TyBeta`, through `InstX`.
nuRedex : (Δ : Ctxᵗ) {L : Term} (A : Ty) (c : Conv) → Value L
  → Maybe (∃[ N ] ∃[ δ ] (Δ ⊢ ν A · L ⟨ c ⟩ -→ N ∣ δ))
nuRedex Δ A c vL with instX? vL | read? (names Δ) A
nuRedex Δ A c vL | just (N , i) | just (R , same) =
  just (_ , new R , TyBeta vL i same)
nuRedex Δ A c vL | just (N , i) | nothing = nothing
nuRedex Δ A c vL | nothing | r = nothing

-- A boundary.  `Merge` fires at ANY boundary over a boundary value,
-- `Id` at a simple value under an identity at a base type, and (GTNF)
-- `IdDyn`/`IdDyn-var` at a tagged value under `id ★` whose tag the
-- exterior sees; `Blame-⟪⟫` at blame.  Everything else is either a
-- congruence or stuck, which is the caller's business.
bdyRedex : (Δ : Ctxᵗ) (M : Term) (Θ : Boundary) (c : Conv)
  → Maybe (∃[ N ] ∃[ δ ] (Δ ⊢ M ⟪ Θ , c ⟫ -→ N ∣ δ))
bdyRedex Δ (blame ℓ) Θ c = just (_ , none , Blame-⟪⟫)
bdyRedex Δ (U ⟪ Θ₁ , tail t₁ ⟫) Θ c₂ with value? (U ⟪ Θ₁ , tail t₁ ⟫)
bdyRedex Δ (U ⟪ Θ₁ , tail t₁ ⟫) Θ c₂ | just v
  with mergePremises? Δ Θ₁ Θ t₁ c₂
bdyRedex Δ (U ⟪ Θ₁ , tail t₁ ⟫) Θ c₂ | just v
  | just (Δᵢ , Δ₁ᶜ , Δ₂ᶜ , Δ⋉ᶜ , t₁′ , c₂′ , ri , r₁ , r₂ , r⋉ , sc₁ , sc₂)
  = just (_ , none , Merge v ri r₁ r₂ r⋉ sc₁ sc₂)
bdyRedex Δ (U ⟪ Θ₁ , tail t₁ ⟫) Θ c₂ | just v | nothing = nothing
bdyRedex Δ (U ⟪ Θ₁ , tail t₁ ⟫) Θ c₂ | nothing = nothing
bdyRedex Δ (V ⟨ μ ∣ (` X) ! ⟩) Θ (tail (mid (id ★)))
  with value? V | toExt Θ X in eq
bdyRedex Δ (V ⟨ μ ∣ (` X) ! ⟩) Θ (tail (mid (id ★)))
  | just v | just X′ with idDynPremises? Δ Θ X
bdyRedex Δ (V ⟨ μ ∣ (` X) ! ⟩) Θ (tail (mid (id ★)))
  | just v | just X′ | just (Δᵢ , Δᶜ , Xᶜ , ri , rc , sm) =
  just (_ , none , IdDyn-var v eq ri rc sm)
bdyRedex Δ (V ⟨ μ ∣ (` X) ! ⟩) Θ (tail (mid (id ★)))
  | just v | just X′ | nothing = nothing
bdyRedex Δ (V ⟨ μ ∣ (` X) ! ⟩) Θ (tail (mid (id ★)))
  | just v | nothing = nothing
bdyRedex Δ (V ⟨ μ ∣ (` X) ! ⟩) Θ (tail (mid (id ★)))
  | nothing | e = nothing
bdyRedex Δ (V ⟨ μ ∣ G ! ⟩) Θ (tail (mid (id ★)))
  with value? V | groundNV? G
bdyRedex Δ (V ⟨ μ ∣ G ! ⟩) Θ (tail (mid (id ★))) | just v | just g =
  just (_ , none , IdDyn v g)
bdyRedex Δ (V ⟨ μ ∣ G ! ⟩) Θ (tail (mid (id ★))) | just v | nothing =
  nothing
bdyRedex Δ (V ⟨ μ ∣ G ! ⟩) Θ (tail (mid (id ★))) | nothing | g =
  nothing
bdyRedex Δ U Θ (tail (mid (id A))) with simple? U | base? A
bdyRedex Δ U Θ (tail (mid (id A))) | just u  | just b  =
  just (_ , none , Id u b)
bdyRedex Δ U Θ (tail (mid (id A))) | just u  | nothing = nothing
bdyRedex Δ U Θ (tail (mid (id A))) | nothing | b       = nothing
bdyRedex Δ M Θ c = nothing

-- (GTNF) A cast over a value: CastId, CastSeq, CastSeq?, Inst,
-- BlameBotIntro by
-- the coercion; at a check, TagUntag/TagUntagBad on a tagged value and
-- TagUntagBad-⟪⟫ on the fresh-tag value.  An inert coercion is a value
-- (no redex), and `bot-elim` meets no value (design.md §6.3).
castRedex : (Δ : Ctxᵗ) {M : Term} (μ : ModeEnv) (p : Coercion) → Value M
  → Maybe (∃[ N ] ∃[ δ ] (Δ ⊢ M ⟨ μ ∣ p ⟩ -→ N ∣ δ))
castRedex Δ μ (idᵖ A) vM       = just (_ , none , CastId vM)
castRedex Δ μ (p ︔ G !) vM     = just (_ , none , CastSeq vM)
castRedex Δ μ (G ？ ℓ ︔ p) vM   = just (_ , none , CastSeq? vM)
castRedex Δ μ (instᵖ p) vM     = just (_ , none , Inst vM)
castRedex Δ μ (bot-intro ℓ) vM = just (_ , none , BlameBotIntro vM)
castRedex Δ μ (H ？ ℓ) (V-simple (S-cast {P = G !} v I-tag)) with G ≟ᵗ H
castRedex Δ μ (H ？ ℓ) (V-simple (S-cast {P = G !} v I-tag)) | yes refl =
  just (_ , none , TagUntag v)
castRedex Δ μ (H ？ ℓ) (V-simple (S-cast {P = G !} v I-tag)) | no ne =
  just (_ , none , TagUntagBad v ne)
castRedex Δ μ (H ？ ℓ) (V-fresh v fr) =
  just (_ , none , TagUntagBad-⟪⟫ v fr)
castRedex Δ μ (H ？ ℓ) vM = nothing
castRedex Δ μ (G !) vM      = nothing
castRedex Δ μ (p ↦ᵖ q) vM   = nothing
castRedex Δ μ (∀ᵖ p) vM     = nothing
castRedex Δ μ (genᵖ p) vM   = nothing
castRedex Δ μ bot-elim vM   = nothing

------------------------------------------------------------------------
-- 4. The step function
------------------------------------------------------------------------

StepResult : Ctxᵗ → Term → Set
StepResult Δ M = ∃[ M′ ] ∃[ δ ] (Δ ⊢ M -→ M′ ∣ δ)

-- Leftmost-outermost, with the rules' own `Value` premises deciding where
-- a congruence stops: at each node the subterms a rule needs as values
-- are tried first, then blame in a frame, then the head redex.  Values
-- do not step (`value-¬step`), so a congruence and a head redex never
-- both apply.
step : (Δ : Ctxᵗ) (M : Term) → Maybe (StepResult Δ M)
step Δ (` x)     = nothing
step Δ ($ n)     = nothing
step Δ `true     = nothing
step Δ `false    = nothing
step Δ (ƛ A ∙ N) = nothing
step Δ (Λ N)     = nothing        -- no ξ-Λ: a type abstraction is a value
step Δ (blame ℓ) = nothing
step Δ (blame ℓ · M) = just (blame ℓ , none , Blame-·₁)
step Δ (L · M) with step Δ L
step Δ (L · M) | just (L′ , δ , st) =
  just (L′ · ↑ᴹ[ δ ] M , δ , ξ-·₁ st)
step Δ (L · M) | nothing with value? L
step Δ (L · M) | nothing | nothing = nothing
step Δ (L · M) | nothing | just vL with step Δ M
step Δ (L · M) | nothing | just vL | just (M′ , δ , st) =
  just (↑ᴹ[ δ ] L · M′ , δ , ξ-·₂ vL st)
step Δ (L · M) | nothing | just vL | nothing with blame? M
step Δ (L · M) | nothing | just vL | nothing | just (ℓ , refl) =
  just (blame ℓ , none , Blame-·₂ vL)
step Δ (L · M) | nothing | just vL | nothing | nothing with value? M
step Δ (L · M) | nothing | just vL | nothing | nothing | nothing =
  nothing
step Δ (L · M) | nothing | just vL | nothing | nothing | just vM =
  appRedex Δ vL vM
step Δ (ν A · L ⟨ c ⟩) with step Δ L
step Δ (ν A · L ⟨ c ⟩) | just (L′ , δ , st) =
  just (ν A · L′ ⟨ c ⟩ , δ , ξ-ν st)
step Δ (ν A · L ⟨ c ⟩) | nothing with blame? L
step Δ (ν A · L ⟨ c ⟩) | nothing | just (ℓ , refl) =
  just (blame ℓ , none , Blame-ν)
step Δ (ν A · L ⟨ c ⟩) | nothing | nothing with value? L
step Δ (ν A · L ⟨ c ⟩) | nothing | nothing | nothing = nothing
step Δ (ν A · L ⟨ c ⟩) | nothing | nothing | just vL = nuRedex Δ A c vL
step Δ (M ⟪ Θ , c ⟫) with bdyRedex Δ M Θ c
step Δ (M ⟪ Θ , c ⟫) | just r = just r
step Δ (M ⟪ Θ , c ⟫) | nothing with interior? Δ Θ
step Δ (M ⟪ Θ , c ⟫) | nothing | nothing = nothing
step Δ (M ⟪ Θ , c ⟫) | nothing | just (Δᵢ , rel) with step Δᵢ M
step Δ (M ⟪ Θ , c ⟫) | nothing | just (Δᵢ , rel)
  | just (M′ , δ , st) =
  just (M′ ⟪ ↑ᴮ[ δ ] Θ , c ⟫ , δ , ξ-⟪⟫ rel st)
step Δ (M ⟪ Θ , c ⟫) | nothing | just (Δᵢ , rel) | nothing = nothing
step Δ (M ⟨ μ ∣ p ⟩) with step Δ M
step Δ (M ⟨ μ ∣ p ⟩) | just (M′ , δ , st) =
  just (M′ ⟨ μ ∣ p ⟩ , δ , ξ-cast st)
step Δ (M ⟨ μ ∣ p ⟩) | nothing with blame? M
step Δ (M ⟨ μ ∣ p ⟩) | nothing | just (ℓ , refl) =
  just (blame ℓ , none , Blame-cast)
step Δ (M ⟨ μ ∣ p ⟩) | nothing | nothing with value? M
step Δ (M ⟨ μ ∣ p ⟩) | nothing | nothing | just vM = castRedex Δ μ p vM
step Δ (M ⟨ μ ∣ p ⟩) | nothing | nothing | nothing = nothing

------------------------------------------------------------------------
-- 5. Reading a step off
------------------------------------------------------------------------

-- The contractum alone, for stating what a recorded trace expects.  The
-- derivation is still what `step` returns; this only forgets it.
stepTo : (Δ : Ctxᵗ) (M : Term) → Maybe Term
stepTo Δ M = map proj₁ (step Δ M)

-- `Steps Δ M N` is what a regression check asserts, and `refl` proves it.
Steps : Ctxᵗ → Term → Term → Set
Steps Δ M N = stepTo Δ M ≡ just N

-- The derivation behind such a check, when a caller wants it rather than
-- the equation.
stepDeriv : ∀ {Δ M} (r : StepResult Δ M)
  → Δ ⊢ M -→ proj₁ r ∣ proj₁ (proj₂ r)
stepDeriv r = proj₂ (proj₂ r)

------------------------------------------------------------------------
-- 6. Traces
------------------------------------------------------------------------

-- Why the run stopped, said of the state it stopped at.  `no-redex` is
-- the honest one: it is where progress would say something and cannot
-- yet, so the evaluator reports "this search found nothing" rather than
-- claiming the term is stuck.
data Final (M : Term) : Set where
  value       : Value M → Final M
  blamed      : ∀ {ℓ} → M ≡ blame ℓ → Final M
  no-redex    : Final M
  out-of-fuel : Final M

-- A run from M that is supposed to keep the type A.  Each step stores its
-- own derivation AND a typing derivation for the contractum, because
-- `eval` re-checks after every step; `illtyped` records a step whose
-- contractum the checker REJECTED, and is the only way the type can be
-- lost along a trace.
infixr 5 _◅⟨_⟩_
data Trace (Δ : Ctxᵗ) (A : Ty) : Term → Set where
  stop   : ∀ {M} → Final M → Trace Δ A M
  illtyped  : ∀ {M M′ δ} → Δ ⊢ M -→ M′ ∣ δ → Trace Δ A M
  _◅⟨_⟩_ : ∀ {M M′ δ} → Δ ⊢ M -→ M′ ∣ δ
    → apply δ Δ ∣ [] ⊢ M′ ⦂ A
    → Trace (apply δ Δ) A M′
    → Trace Δ A M

------------------------------------------------------------------------
-- 7. The evaluator
------------------------------------------------------------------------

-- `step ⨟ check⊢`, iterated with fuel.  The contractum is CHECKED, not
-- retyped by preservation — the executable form of subject reduction.
-- νF Commentary.md § Eval.agda / What a run asserts
eval : ∀ {Δ A} (k : ℕ) (M : Term) → Δ ∣ [] ⊢ M ⦂ A → Trace Δ A M
eval {Δ} {A} zero M ⊢M with value? M
eval {Δ} {A} zero M ⊢M | just v  = stop (value v)
eval {Δ} {A} zero M ⊢M | nothing = stop out-of-fuel
eval {Δ} {A} (suc k) M ⊢M with step Δ M
eval {Δ} {A} (suc k) M ⊢M | nothing with value? M | blame? M
eval {Δ} {A} (suc k) M ⊢M | nothing | just v  | b = stop (value v)
eval {Δ} {A} (suc k) M ⊢M | nothing | nothing | just (ℓ , eq) =
  stop (blamed eq)
eval {Δ} {A} (suc k) M ⊢M | nothing | nothing | nothing = stop no-redex
eval {Δ} {A} (suc k) M ⊢M | just (M′ , δ , r)
  with check⊢ (apply δ Δ) [] M′ A
eval {Δ} {A} (suc k) M ⊢M | just (M′ , δ , r) | just ⊢M′ =
  r ◅⟨ ⊢M′ ⟩ eval k M′ ⊢M′
eval {Δ} {A} (suc k) M ⊢M | just (M′ , δ , r) | nothing = illtyped r

------------------------------------------------------------------------
-- 8. Reading a trace
------------------------------------------------------------------------

traceEnd : ∀ {Δ A M} → Trace Δ A M → Term
traceEnd {M = M} (stop f)            = M
traceEnd         (illtyped {M′ = M′} r) = M′
traceEnd         (r ◅⟨ ⊢M′ ⟩ tr)     = traceEnd tr

-- The context in which the final state lives.  Allocating steps change this
-- index even though the trace itself remains a run from its initial context.
traceCtx : ∀ {Δ A M} → Trace Δ A M → Ctxᵗ
traceCtx {Δ = Δ} (stop f) = Δ
traceCtx {Δ = Δ} (illtyped {δ = δ} r) = apply δ Δ
traceCtx (r ◅⟨ ⊢M′ ⟩ tr) = traceCtx tr

-- the states, the first one included
traceTerms : ∀ {Δ A M} → Trace Δ A M → List Term
traceTerms {M = M} (stop f)            = M ∷ []
traceTerms {M = M} (illtyped {M′ = M′} r) = M ∷ M′ ∷ []
traceTerms {M = M} (r ◅⟨ ⊢M′ ⟩ tr)     = M ∷ traceTerms tr

traceLen : ∀ {Δ A M} → Trace Δ A M → ℕ
traceLen (stop f)        = zero
traceLen (illtyped r)       = suc zero
traceLen (r ◅⟨ ⊢M′ ⟩ tr) = suc (traceLen tr)

evalTerms : ∀ {Δ A M} (k : ℕ) → Δ ∣ [] ⊢ M ⦂ A → List Term
evalTerms k ⊢M = traceTerms (eval k _ ⊢M)

------------------------------------------------------------------------
-- 9. What a trace proves
------------------------------------------------------------------------

-- The states really are a run: the `_⊢_-→_` derivations are stored, so
-- this only reassembles them.
trace-sound : ∀ {Δ A M} (tr : Trace Δ A M) → Δ ⊢ M -→* traceEnd tr
trace-sound (stop f)        = done
trace-sound (illtyped r)       = r then done
trace-sound (r ◅⟨ ⊢M′ ⟩ tr) = r then trace-sound tr

eval-sound : ∀ {Δ A M} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
  → Δ ⊢ M -→* traceEnd (eval k M ⊢M)
eval-sound k ⊢M = trace-sound (eval k _ ⊢M)

-- `Checked tr` is the unit RECORD exactly when no step along `tr` lost the
-- type, so Agda discharges it by eta at a concrete run and an `illtyped`
-- anywhere leaves an unsolvable `⊥`.
Checked : ∀ {Δ A M} → Trace Δ A M → Set
Checked (stop f)        = ⊤
Checked (illtyped r)       = ⊥
Checked (r ◅⟨ ⊢M′ ⟩ tr) = Checked tr

-- SUBJECT REDUCTION, FOR THIS RUN.  Not proved — checked, state by
-- state, by the derivations the trace stores.
trace-⦂ : ∀ {Δ A M} → Δ ∣ [] ⊢ M ⦂ A → (tr : Trace Δ A M)
  → Checked tr → traceCtx tr ∣ [] ⊢ traceEnd tr ⦂ A
trace-⦂ ⊢M (stop f)        c = ⊢M
trace-⦂ ⊢M (illtyped r)       ()
trace-⦂ ⊢M (r ◅⟨ ⊢M′ ⟩ tr) c = trace-⦂ ⊢M′ tr c

eval-⦂ : ∀ {Δ A M} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
  → Checked (eval k M ⊢M)
  → traceCtx (eval k M ⊢M) ∣ [] ⊢ traceEnd (eval k M ⊢M) ⦂ A
eval-⦂ k ⊢M c = trace-⦂ ⊢M (eval k _ ⊢M) c

-- and `Checked` really bites: an `illtyped` trace has no such proof, so
-- the `_` a caller writes for it is a proof only because every state the
-- run passed through was checked.
illtyped-unchecked : ∀ {Δ A M M′ δ} (r : Δ ⊢ M -→ M′ ∣ δ)
  → Checked {Δ} {A} (illtyped r) → ⊥
illtyped-unchecked r c = c

------------------------------------------------------------------------
-- 10. What a recorded example asserts
------------------------------------------------------------------------

-- ONE PASS OVER THE RUN: Agda shares nothing between occurrences of a
-- term, so `report` walks the trace once and `Reaches` mentions the run
-- ONCE.  `bump` matches on the triple rather than projecting out of it,
-- and `Report` is a DATA type rather than a triple, for the same reason.
-- νF Commentary.md § Eval.agda / §10
data Report : Set where
  reported : Term → ℕ → Bool → Report

repEnd : Report → Term
repEnd (reported V n b) = V

repKept : Report → Bool
repKept (reported V n b) = b

bump : Report → Report
bump (reported V n b) = reported V (suc n) b

report : ∀ {Δ A M} → Trace Δ A M → Report
report {M = M} (stop f)            = reported M zero true
report         (illtyped {M′ = M′} r) = reported M′ (suc zero) false
report         (r ◅⟨ ⊢M′ ⟩ tr)     = bump (report tr)

report-end : ∀ {Δ A M} (tr : Trace Δ A M)
  → repEnd (report tr) ≡ traceEnd tr
report-end (stop f)  = refl
report-end (illtyped r) = refl
report-end (r ◅⟨ ⊢M′ ⟩ tr) with report tr | report-end tr
report-end (r ◅⟨ ⊢M′ ⟩ tr) | reported V n b | eq = eq

report-kept : ∀ {Δ A M} (tr : Trace Δ A M)
  → repKept (report tr) ≡ true → Checked tr
report-kept (stop f)  eq = tt
report-kept (illtyped r) ()
report-kept (r ◅⟨ ⊢M′ ⟩ tr) eq with report tr | report-kept tr
report-kept (r ◅⟨ ⊢M′ ⟩ tr) eq | reported V n b | h = h eq

-- (GTNF) An ANSWER is a value or blame: the two ways a run may end.
data Answer : Term → Set where
  ans-value : ∀ {V} → Value V → Answer V
  ans-blame : ∀ {ℓ} → Answer (blame ℓ)

-- One statement per example: with fuel `k` the evaluator reaches `V` in
-- exactly `n` steps, no state lost the type, and `V` is an answer.  A
-- RECORD, so that `k`, `n` and `⊢M` are recoverable from the type.
-- νF Commentary.md § Eval.agda / §10
record Reaches {Δ A M} (k n : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A) (V : Term)
  : Set where
  constructor reaches
  field
    ran       : report (eval k M ⊢M) ≡ reported V n true
    endAnswer : Answer V
open Reaches public

-- What an example's `Reaches` yields.  None of these re-runs the term.
reaches-end : ∀ {Δ A M V k n} {⊢M : Δ ∣ [] ⊢ M ⦂ A}
  → Reaches k n ⊢M V → traceEnd (eval k M ⊢M) ≡ V
reaches-end {k = k} {⊢M = ⊢M} r =
  trans (sym (report-end (eval k _ ⊢M))) (cong repEnd (ran r))

reaches-checked : ∀ {Δ A M V k n} {⊢M : Δ ∣ [] ⊢ M ⦂ A}
  → Reaches k n ⊢M V → Checked (eval k M ⊢M)
reaches-checked {k = k} {⊢M = ⊢M} r =
  report-kept (eval k _ ⊢M) (cong repKept (ran r))

-- The multi-step run, with the endpoint NAMED.  `eval-sound` already
-- gives `Δ ⊢ M -→* traceEnd …`; this is that, with the endpoint read off
-- an equation.
eval-run : ∀ {Δ A M V} (k : ℕ) (⊢M : Δ ∣ [] ⊢ M ⦂ A)
  → traceEnd (eval k M ⊢M) ≡ V → Δ ⊢ M -→* V
eval-run k ⊢M refl = eval-sound k ⊢M

-- the run, in the object language's own relation
reaches-run : ∀ {Δ A M V k n} {⊢M : Δ ∣ [] ⊢ M ⦂ A}
  → Reaches k n ⊢M V → Δ ⊢ M -→* V
reaches-run {k = k} {⊢M = ⊢M} r = eval-run k ⊢M (reaches-end r)

-- and the endpoint's typing: SUBJECT REDUCTION for this run, checked
reaches-⦂ : ∀ {Δ A M V k n} {⊢M : Δ ∣ [] ⊢ M ⦂ A}
  → Reaches k n ⊢M V
  → traceCtx (eval k M ⊢M) ∣ [] ⊢ V ⦂ A
reaches-⦂ {A = A} {k = k} {⊢M = ⊢M} r =
  subst (λ W → _ ∣ [] ⊢ W ⦂ A) (reaches-end r)
    (eval-⦂ k ⊢M (reaches-checked r))

------------------------------------------------------------------------
-- 11. (GTNF) Which rule fired: a run's rule names, congruences peeled
------------------------------------------------------------------------

ruleName : ∀ {Δ M N δ} → Δ ⊢ M -→ N ∣ δ → String
ruleName (TyBeta v i r)             = "TyBeta"
ruleName (Beta v)                   = "Beta"
ruleName (Wrap u v rc ri rd sc)     = "Wrap"
ruleName (Merge v ri r₁ r₂ r⋉ s t) = "Merge"
ruleName (Id u b)                   = "Id"
ruleName (CastId v)                 = "CastId"
ruleName (CastSeq v)                = "CastSeq"
ruleName (CastSeq? v)               = "CastSeq?"
ruleName (CastFun v w)              = "CastFun"
ruleName (Inst v)                   = "Inst"
ruleName (TagUntag v)               = "TagUntag"
ruleName (TagUntagBad v ne)         = "TagUntagBad"
ruleName (IdDyn v g)                = "IdDyn"
ruleName (IdDyn-var v e ri rc sm)   = "IdDyn"
ruleName (TagUntagBad-⟪⟫ v fr)      = "TagUntagBad-⟪⟫"
ruleName (BlameBotIntro v)          = "BlameBotIntro"
ruleName Blame-·₁                   = "Blame"
ruleName (Blame-·₂ v)               = "Blame"
ruleName Blame-ν                    = "Blame"
ruleName Blame-⟪⟫                   = "Blame"
ruleName Blame-cast                 = "Blame"
ruleName (ξ-·₁ st)                  = ruleName st
ruleName (ξ-·₂ v st)                = ruleName st
ruleName (ξ-ν st)                   = ruleName st
ruleName (ξ-⟪⟫ rel st)              = ruleName st
ruleName (ξ-cast st)                = ruleName st

traceRules : ∀ {Δ A M} → Trace Δ A M → List String
traceRules (stop f)          = []
traceRules (illtyped r)      = ruleName r ∷ "ILLTYPED" ∷ []
traceRules (r ◅⟨ ⊢M′ ⟩ tr)   = ruleName r ∷ traceRules tr

evalRules : ∀ {Δ A M} (k : ℕ) → Δ ∣ [] ⊢ M ⦂ A → List String
evalRules k ⊢M = traceRules (eval k _ ⊢M)
