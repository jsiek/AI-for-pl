module Pretty.Narrowings where

-- File Charter:
--   * Renders checked narrowing and contravariant widening proof trees.
--   * Prints the active type/seal context on every judgment.
--   * Derives every rule label, coercion, and endpoint type from checked
--     `Coercions` and `NarrowWiden` evidence.

open import Agda.Builtin.String using (String)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)

open import Coercions
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import Pretty.Coercions using (renderCoercionWith)
open import Pretty.Names
open import Pretty.Strings using (_++ˢ_)
open import Pretty.Types using (renderTypeWith)

ContextNames : Set
ContextNames = List String

renderContext : ContextNames → String
renderContext [] = "∅"
renderContext (entry ∷ []) = entry
renderContext (entry ∷ entries) =
  entry ++ˢ ", " ++ˢ renderContext entries

extendContext : ContextNames → String → ContextNames
extendContext context entry = context ++ (entry ∷ [])

renderNarrowingJudgmentWith : ∀ {μ Δ Σ c A B}
  → List TypeName
  → ContextNames
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B
  → String
renderNarrowingJudgmentWith {c = c} {A = A} {B = B}
    names context derivation =
  renderContext context ++ˢ " ⊢ " ++ˢ renderTypeWith names A ++ˢ
  " ⊒ " ++ˢ renderTypeWith names B ++ˢ " : " ++ˢ
  renderCoercionWith names c

renderWideningJudgmentWith : ∀ {μ Δ Σ c A B}
  → List TypeName
  → ContextNames
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B
  → String
renderWideningJudgmentWith {c = c} {A = A} {B = B}
    names context derivation =
  renderContext context ++ˢ " ⊢ " ++ˢ renderTypeWith names A ++ˢ
  " ⊑ " ++ˢ renderTypeWith names B ++ˢ " : " ++ˢ
  renderCoercionWith names c

ruleLine : String → String
ruleLine rule = "-------------------------------- [" ++ˢ rule ++ˢ "]"

finishNarrowing : ∀ {μ Δ Σ c A B}
  → List TypeName
  → ContextNames
  → String
  → List String
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B
  → List String
finishNarrowing names context rule premises derivation =
  premises ++
  (ruleLine rule ∷
   renderNarrowingJudgmentWith names context derivation ∷ [])

finishWidening : ∀ {μ Δ Σ c A B}
  → List TypeName
  → ContextNames
  → String
  → List String
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B
  → List String
finishWidening names context rule premises derivation =
  premises ++
  (ruleLine rule ∷
   renderWideningJudgmentWith names context derivation ∷ [])

mutual
  renderNarrowingDerivationWith : ∀ {μ Δ Σ c A B}
    → List TypeName
    → ContextNames
    → μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B
    → List String
  renderNarrowingDerivationWith names context
      derivation@(cast-id hA ok , NW.cross (NW.id-＇ α)) =
    finishNarrowing names context "N-ID-VAR" [] derivation
  renderNarrowingDerivationWith names context
      derivation@(cast-id hA ok , NW.cross (NW.id-‵ ι)) =
    finishNarrowing names context "N-ID-BASE" [] derivation
  renderNarrowingDerivationWith names context
      derivation@(cast-fun s⊢ t⊢ , NW.cross (sʷ NW.↦ tⁿ)) =
    finishNarrowing names context "N-FUN"
      (renderWideningDerivationWith names context (s⊢ , sʷ) ++
       renderNarrowingDerivationWith names context (t⊢ , tⁿ))
      derivation
  renderNarrowingDerivationWith names context
      derivation@(cast-all s⊢ , NW.cross (NW.`∀ sⁿ)) =
    finishNarrowing names context "N-ALL"
      (renderNarrowingDerivationWith
        (type-binder X ∷ names) (extendContext context X) (s⊢ , sⁿ))
      derivation
    where
      X = freshTypeName names
  renderNarrowingDerivationWith names context
      derivation@(cast-id hA ok , NW.id★) =
    finishNarrowing names context "N-ID★" [] derivation
  renderNarrowingDerivationWith names context
      derivation@(cast-gen hA occ s⊢ , NW.gen safe) =
    finishNarrowing names context "N-GEN"
      (renderNarrowingDerivationWith
        (seal-binder α ∷ names)
        (extendContext context (α ++ˢ " := ★"))
        (s⊢ , NW.genSafe→narrowing safe))
      derivation
    where
      α = freshSealName names
  renderNarrowingDerivationWith names context
      derivation@(cast-untag hG gG ok , NW.untag ground) =
    finishNarrowing names context "N-UNTAG" [] derivation
  renderNarrowingDerivationWith {μ = μ} names context
      derivation@(cast-seq first⊢@(cast-untag hG gG ok) s⊢ ,
                           ground NW.？︔ strict) =
    finishNarrowing names context "N-UNTAG-SEQ"
      (renderNarrowingDerivationWith names context
        (first⊢ , NW.untag ground) ++
       renderNarrowingDerivationWith names context
        (s⊢ , NW.cross (NW.strictCrossⁿ→cross strict)))
      derivation
  renderNarrowingDerivationWith {μ = μ} names context
      derivation@(cast-seq first⊢@(cast-untag hG gG ok)
                           (cast-gen hA occ s⊢) ,
                           NW.fun-untag-gen safe) =
    finishNarrowing names context "N-FUN-UNTAG-GEN"
      (renderNarrowingDerivationWith names context
        (first⊢ , NW.untag gG) ++
       renderNarrowingDerivationWith names context
        (cast-gen hA occ s⊢ , NW.gen safe))
      derivation
  renderNarrowingDerivationWith names context
      derivation@(cast-seal hA α∈Σ ok , NW.sealⁿ A α) =
    finishNarrowing names context "N-SEAL" [] derivation
  renderNarrowingDerivationWith {μ = μ} names context
      derivation@(cast-seq s⊢ (cast-seal {A = A} hA α∈Σ ok) ,
                           strict NW.︔seal α) =
    finishNarrowing names context "N-SEAL-SEQ"
      (renderNarrowingDerivationWith names context
        (s⊢ , NW.strictⁿ→narrow strict) ++
       renderNarrowingDerivationWith names context
        (cast-seal {μ = μ} hA α∈Σ ok , NW.sealⁿ A α))
      derivation

  renderWideningDerivationWith : ∀ {μ Δ Σ c A B}
    → List TypeName
    → ContextNames
    → μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B
    → List String
  renderWideningDerivationWith names context
      derivation@(cast-id hA ok , NW.cross (NW.id-＇ α)) =
    finishWidening names context "W-ID-VAR" [] derivation
  renderWideningDerivationWith names context
      derivation@(cast-id hA ok , NW.cross (NW.id-‵ ι)) =
    finishWidening names context "W-ID-BASE" [] derivation
  renderWideningDerivationWith names context
      derivation@(cast-fun s⊢ t⊢ , NW.cross (sⁿ NW.↦ tʷ)) =
    finishWidening names context "W-FUN"
      (renderNarrowingDerivationWith names context (s⊢ , sⁿ) ++
       renderWideningDerivationWith names context (t⊢ , tʷ))
      derivation
  renderWideningDerivationWith names context
      derivation@(cast-all s⊢ , NW.cross (NW.`∀ sʷ)) =
    finishWidening names context "W-ALL"
      (renderWideningDerivationWith
        (type-binder X ∷ names) (extendContext context X) (s⊢ , sʷ))
      derivation
    where
      X = freshTypeName names
  renderWideningDerivationWith names context
      derivation@(cast-id hA ok , NW.id★) =
    finishWidening names context "W-ID★" [] derivation
  renderWideningDerivationWith names context
      derivation@(cast-inst hB occ s⊢ , NW.inst safe) =
    finishWidening names context "W-INST"
      (renderWideningDerivationWith
        (seal-binder α ∷ names)
        (extendContext context (α ++ˢ " := ★"))
        (s⊢ , NW.instSafe→widening safe))
      derivation
    where
      α = freshSealName names
  renderWideningDerivationWith names context
      derivation@(cast-tag hG gG ok , NW.tag ground) =
    finishWidening names context "W-TAG" [] derivation
  renderWideningDerivationWith {μ = μ} names context
      derivation@(cast-seq s⊢ second⊢@(cast-tag hG gG ok) ,
                           strict NW.︔ ground !) =
    finishWidening names context "W-TAG-SEQ"
      (renderWideningDerivationWith names context
        (s⊢ , NW.cross (NW.strictCrossʷ→cross strict)) ++
       renderWideningDerivationWith names context
        (second⊢ , NW.tag ground))
      derivation
  renderWideningDerivationWith {μ = μ} names context
      derivation@(cast-seq (cast-inst hB occ s⊢)
                           second⊢@(cast-tag hG gG ok) ,
                           NW.inst-fun-tag safe) =
    finishWidening names context "W-INST-FUN-TAG"
      (renderWideningDerivationWith names context
        (cast-inst hB occ s⊢ , NW.inst safe) ++
       renderWideningDerivationWith names context
        (second⊢ , NW.tag gG))
      derivation
  renderWideningDerivationWith names context
      derivation@(cast-unseal hA α∈Σ ok , NW.unsealʷ α A) =
    finishWidening names context "W-UNSEAL" [] derivation
  renderWideningDerivationWith {μ = μ} names context
      derivation@(cast-seq (cast-unseal {A = A} hA α∈Σ ok) s⊢ ,
                           NW.unseal︔_ α strict) =
    finishWidening names context "W-UNSEAL-SEQ"
      (renderWideningDerivationWith names context
        (cast-unseal {μ = μ} hA α∈Σ ok , NW.unsealʷ α A) ++
       renderWideningDerivationWith names context
        (s⊢ , NW.strictʷ→widen strict))
      derivation

renderNarrowingDerivation : ∀ {μ Δ Σ c A B}
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B
  → List String
renderNarrowingDerivation = renderNarrowingDerivationWith [] []

renderWideningDerivation : ∀ {μ Δ Σ c A B}
  → μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B
  → List String
renderWideningDerivation = renderWideningDerivationWith [] []
