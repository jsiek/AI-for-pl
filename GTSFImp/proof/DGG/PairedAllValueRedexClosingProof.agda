module proof.DGG.PairedAllValueRedexClosingProof where

-- File Charter:
--   * Exposes the paired all-value redex closing proof name.
--   * The live branch lacks the top-down M5 redex assembly rows, so the
--     proof is kept as an explicit residual module parameter.
--   * Contains no proof term beyond forwarding the residual parameter.

open import proof.DGG.PairedAllValueRedexClosingDef
  using (PairedAllValueRedexClosingᵀ)


module _
    (paired-all-value-redex-closing-residual :
      PairedAllValueRedexClosingᵀ)
  where

  paired-all-value-redex-closing :
    PairedAllValueRedexClosingᵀ
  paired-all-value-redex-closing =
    paired-all-value-redex-closing-residual
