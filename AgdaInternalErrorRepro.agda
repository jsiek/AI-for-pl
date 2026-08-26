module AgdaInternalErrorRepro where

-- Minimal repository-local reproducer for Agda 2.7.0.1:
-- checking this old dispatcher shape hits
-- __IMPOSSIBLE__ at CompiledClause/Compile.hs:170.

import proof.DGG.CastTermImprecision as CTI2
open import proof.DGG.Inversion.SourceStripDef using (SourceSpineStrip)
open import proof.DGG.Inversion.SpineValueDef using
  (sv-Λ; sv-cast; sv-conceal-all; sv-conceal-fun; sv-reveal-all;
   sv-reveal-fun; sv-seal)
open import proof.DGG.Inversion.SourceStripWorkerProof using
  (source-spine-direct-cast; source-spine-strip-worker-seal-cast;
   source-spine-strip-worker-seal-nonvar;
   source-spine-strip-worker-seal-source)

source-spine-strip-worker-seal-repro : SourceSpineStrip
{-# NON_COVERING #-}
source-spine-strip-worker-seal-repro (sv-seal sv) vU mono rb sc
    source∈ target∈ D@(CTI2.⊑cast² cY prem p) =
  source-spine-direct-cast (sv-seal sv) vU mono rb sc
    source∈ target∈ D
source-spine-strip-worker-seal-repro (sv-seal (sv-cast sv inert)) vU
    mono rb sc source∈ target∈
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.cast⊑cast² c cY prem pᵢ) p) =
  source-spine-strip-worker-seal-cast
    (sv-seal (sv-cast sv inert)) vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-repro (sv-seal (sv-cast sv inert)) vU
    mono rb sc source∈ target∈
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.cast⊑² c prem pᵢ) p) =
  source-spine-strip-worker-seal-cast
    (sv-seal (sv-cast sv inert)) vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-repro (sv-seal (sv-Λ sv)) vU mono
    rb sc source∈ target∈
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ prem pᵢ) p) =
  source-spine-strip-worker-seal-nonvar (sv-seal (sv-Λ sv))
    vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-repro (sv-seal (sv-reveal-fun sv)) vU
    mono rb sc source∈ target∈
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.reveal⊑² monoᵣ rbᵣ scᵣ c⊢ᵣ prem pᵢ) p) =
  source-spine-strip-worker-seal-nonvar
    (sv-seal (sv-reveal-fun sv)) vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-repro (sv-seal (sv-conceal-fun sv)) vU
    mono rb sc source∈ target∈
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.conceal⊑² okᵣ monoᵣ rbᵣ scᵣ c⊢ᵣ prem pᵢ) p) =
  source-spine-strip-worker-seal-nonvar
    (sv-seal (sv-conceal-fun sv)) vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-repro (sv-seal (sv-reveal-all sv)) vU
    mono rb sc source∈ target∈
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.reveal⊑² monoᵣ rbᵣ scᵣ c⊢ᵣ prem pᵢ) p) =
  source-spine-strip-worker-seal-nonvar
    (sv-seal (sv-reveal-all sv)) vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-repro (sv-seal (sv-conceal-all sv)) vU
    mono rb sc source∈ target∈
    D@(CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ c⊢
      (CTI2.conceal⊑² okᵣ monoᵣ rbᵣ scᵣ c⊢ᵣ prem pᵢ) p) =
  source-spine-strip-worker-seal-nonvar
    (sv-seal (sv-conceal-all sv)) vU mono rb sc source∈ target∈ D
source-spine-strip-worker-seal-repro (sv-seal sv) vU mono rb sc
    source∈ target∈
    (CTI2.conceal⊑² ok monoᵢ rbᵢ scᵢ
      (CTI2.⊢↓-sealˣ X∈) prem p) =
  source-spine-strip-worker-seal-source sv vU mono
    rb sc source∈ target∈ monoᵢ rbᵢ scᵢ X∈ ok prem
