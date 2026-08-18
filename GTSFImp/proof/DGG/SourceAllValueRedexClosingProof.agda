module proof.DGG.SourceAllValueRedexClosingProof where

-- File Charter:
--   * Exposes the source-only all-value redex closing proof name.
--   * The live branch lacks the top-down M5 source-only redex assembly rows,
--     so the proof is kept as an explicit residual module parameter.
--   * Contains no proof term beyond forwarding the residual parameter.

open import proof.DGG.SourceAllValueRedexClosingDef
  using (SourceAllValueRedexClosingᵀ)


module _
    (source-all-value-redex-closing-residual :
      SourceAllValueRedexClosingᵀ)
  where

  source-all-value-redex-closing :
    SourceAllValueRedexClosingᵀ
  source-all-value-redex-closing =
    source-all-value-redex-closing-residual
