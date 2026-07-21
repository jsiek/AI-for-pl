module proof.NuImprecisionSourceTagCancellationProof where

-- File Charter:
--   * Proves exact cancellation of one terminal source ground tag.
--   * Uses ground-value quotient elimination only at quotient-up boundaries.
--   * Recurses structurally through target casts and allocation prefixes.

open import Data.List using ([])
open import Data.Product using (_,_)
import Coercions as C
open import ImprecisionWf using (id★)
import NarrowWiden as NW
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; no•-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  ; quotient-cast-widening
  ; quotient-id-widening
  ; up⊑upᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( _∣_∣_⊢_⦂_
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  )
import Types as T
open import proof.NuImprecisionAtomicTargetReindex using
  (atomic-target-value-reindexᵀ)
open import
  proof.NuImprecisionGroundValueQuotientEliminationDef using
  (GroundValueQuotientEliminationᵀ)
open import proof.NuImprecisionSourceTagCancellationDef using
  (SourceTagCancellationᵀ)
open import proof.NuImprecisionSourceTagQuotientUpProof using
  (source-tag-quotient-up-cancellationᵀ)


source-tag-typing⁻¹ :
  ∀ {Δ Σ Γ V G} →
  Δ ∣ Σ ∣ Γ ⊢ V ⟨ G C.! ⟩ ⦂ T.★ →
  Δ ∣ Σ ∣ Γ ⊢ V ⦂ G
source-tag-typing⁻¹ (⊢⟨⟩↑ () V⊢)
source-tag-typing⁻¹ (⊢⟨⟩↓ () V⊢)
source-tag-typing⁻¹
    (⊢⟨⟩⊒ mode seal★ (c⊢ , NW.cross ()) V⊢)
source-tag-typing⁻¹
    (⊢⟨⟩⊑ mode seal★
      (C.cast-tag hG gG ok , NW.tag gG′) V⊢) =
  V⊢


source-tag-cancellation-proofᵀ :
  GroundValueQuotientEliminationᵀ →
  SourceTagCancellationᵀ
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV vW noW
    (up⊑upᵀ inner
      widening@(quotient-id-widening
        (C.cast-tag hG gG⊢ ok , NW.tag gG′) u′⊑)
      oldq)
    q =
  source-tag-quotient-up-cancellationᵀ
    eliminate gG vV vW noW inner widening q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV vW noW
    (up⊑upᵀ inner
      widening@(quotient-cast-widening
        mode seal★ (C.cast-tag hG gG⊢ ok , NW.tag gG′)
        mode′ seal★′ u′⊑)
      oldq)
    q =
  source-tag-quotient-up-cancellationᵀ
    eliminate gG vV vW noW inner widening q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV vW noW
    (cast⊒⊑ᵀ mode seal★ (c⊢ , NW.cross ()) inner oldq) q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV vW noW
    (cast⊑⊑ᵀ mode seal★
      (C.cast-tag hG gG⊢ ok , NW.tag gG′) inner oldq)
    q =
  atomic-target-value-reindexᵀ T.★ vW inner q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV vW noW
    (conv⊑convᵀ
      (paired-conversion (paired-reveal corr () c′↑)) inner)
    q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV vW noW
    (conv⊑convᵀ
      (paired-conversion (paired-conceal corr () c′↓)) inner)
    q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) noW
    (conv⊑convᵀ
      (paired-widening
        mode seal★ (C.cast-tag hG gG⊢ ok , NW.tag gG′)
        mode′ seal★′ c′⊑ _)
      inner)
    q =
  ⊑cast⊑ᵀ mode′ seal★′ c′⊑ inner q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV vW noW (conv↑⊑ᵀ () inner oldq) q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV vW noW (conv↓⊑ᵀ () inner oldq) q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) (no•-⟨⟩ noM)
    (⊑cast⊒ᵀ {p = p} mode′ seal★′ c′⊒ inner oldq) q
    with p
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) (no•-⟨⟩ noM)
    (⊑cast⊒ᵀ {p = p} mode′ seal★′ c′⊒ inner oldq) q
    | id★ =
  ⊑cast⊒ᵀ mode′ seal★′ c′⊒
    (source-tag-cancellation-proofᵀ
      eliminate gG vV vM noM inner q)
    q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) (no•-⟨⟩ noM)
    (⊑cast⊑ᵀ {p = p} mode′ seal★′ c′⊑ inner oldq) q
    with p
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) (no•-⟨⟩ noM)
    (⊑cast⊑ᵀ {p = p} mode′ seal★′ c′⊑ inner oldq) q
    | id★ =
  ⊑cast⊑ᵀ mode′ seal★′ c′⊑
    (source-tag-cancellation-proofᵀ
      eliminate gG vV vM noM inner q)
    q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) (no•-⟨⟩ noM)
    (⊑cast⊑idᵀ {p = p} seal★′ c′⊑ inner oldq) q
    with p
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) (no•-⟨⟩ noM)
    (⊑cast⊑idᵀ {p = p} seal★′ c′⊑ inner oldq) q
    | id★ =
  ⊑cast⊑idᵀ seal★′ c′⊑
    (source-tag-cancellation-proofᵀ
      eliminate gG vV vM noM inner q)
    q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) (no•-⟨⟩ noM)
    (⊑conv↑ᵀ {p = p} c′↑ inner oldq) q
    with p
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) (no•-⟨⟩ noM)
    (⊑conv↑ᵀ {p = p} c′↑ inner oldq) q
    | id★ =
  ⊑conv↑ᵀ c′↑
    (source-tag-cancellation-proofᵀ
      eliminate gG vV vM noM inner q)
    q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) (no•-⟨⟩ noM)
    (⊑conv↓ᵀ {p = p} c′↓ inner oldq) q
    with p
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV (vM ⟨ inert′ ⟩) (no•-⟨⟩ noM)
    (⊑conv↓ᵀ {p = p} c′↓ inner oldq) q
    | id★ =
  ⊑conv↓ᵀ c′↓
    (source-tag-cancellation-proofᵀ
      eliminate gG vV vM noM inner q)
    q
source-tag-cancellation-proofᵀ eliminate {p = id★}
    gG vV vW noW
    (allocation-prefixᵀ prefix inner Vtag⊢ W⊢) q =
  allocation-prefixᵀ prefix
    (source-tag-cancellation-proofᵀ
      eliminate gG vV vW noW inner q)
    (source-tag-typing⁻¹ Vtag⊢) W⊢
