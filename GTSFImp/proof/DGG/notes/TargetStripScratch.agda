module TargetStripScratch where

open import proof.DGG.Inversion.TargetStripDef using
  (TargetStripAt★; TargetStripAt★Data; target-strip★-data)
import proof.DGG.CastTermImprecision as CTI2

target-strip-at★-scratch : TargetStripAt★
target-strip-at★-scratch sv vU mono rb sc target∈ D with D
target-strip-at★-scratch sv vU mono rb sc target∈ D
    | CTI2.⊑cast² c prem q = {!!}
target-strip-at★-scratch sv vU mono rb sc target∈ D
    | CTI2.cast⊑cast² c c′ prem q = {!!}
target-strip-at★-scratch sv vU mono rb sc target∈ D
    | CTI2.blame⊑² target⊢ p = {!!}
