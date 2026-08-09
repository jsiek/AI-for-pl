Round 18 stopped while trying to build `seal-transfer-packaged`.

Branch:

  `source-seal-cast-package`, source-side seal branch

  D :
    W ∣ γ ⊢² P ↓ seal X ★ ⊑ U ∶ q

  D =
    CTI2.conceal⊑²
      (CTI2.seal-partner-ok
        (CTI2.star-rep-target {Xᴿ? = just Yᵖ} partner))
      mono
      (CTI2.tag-rebase-varᴸ {Xᴿ = Yʳ} rb)
      sc
      (CTI2.⊢↓-sealˣ source∈)
      prem
      q

where the rule surface gives no equality between `Yᵖ` and `Yʳ`.

Needed package:

  Σ[ Xᴿ? ∈ Maybe (TyVar Δᴿ) ]
    STC.TaggedTransferOutput W γ
      ((P ↓ seal X ★) ⟨ c ⟩) U X Xᴿ?

Local evidence provides two incompatible candidate indices:

1. The branch partner is indexed at `just Yᵖ`:

   partner :
     CTI2.Rep★PartnerOK Wᵖ X P (just Yᵖ) U

   To package at `just Yᵖ`, we would need:

   STC.PremisePartnerAt W X (just Yᵖ)

   i.e. `CTI2.CenterAligned W X Yᵖ`.  The rebase `rb` only gives
   `CTI2.CenterAligned W X Yʳ`.

2. The rebase pivot gives the output-world pedigree at `just Yʳ`:

   STC.PremisePartnerAt W X (just Yʳ)

   But packaging at `just Yʳ` requires a partner for the same target term:

   CTI2.Rep★PartnerOK W X ((P ↓ seal X ★) ⟨ c ⟩) (just Yʳ) U

   If `U` is a variable tag at `Yᵖ`, rebuilding at `Yʳ` changes the target
   term unless `Yᵖ ≡ Yʳ`, and no such equality is available locally.

The attempted Agda refinement was rejected exactly at this mismatch:

  Yᵖ != Yᵖ₁ of type Fin.Fin Δᴿ
  when checking that all occurrences of pattern variable Yᵖ have the
  same value

This is not the source-seal sub-head modeled in `Tighten8PreflightScratch`:
there the local rebase is already

  rbᵖ : CTI2.RebaseAt W₃ W₂ X Yᵖ

so `transport-rep★-partner-ok rbᵖ partner` builds the package at
`just Yᵖ` without comparing against the outer conclusion target.  In this
live `conceal⊑²` branch, the source-conceal partner index and the source
tag-rebase pivot are independent in the constructor surface, so the package
cannot be built from local evidence without an additional invariant tying
them together or a different branch result that carries such evidence.
