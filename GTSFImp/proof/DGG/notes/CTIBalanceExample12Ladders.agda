{-# OPTIONS --safe #-}

module proof.DGG.notes.CTIBalanceExample12Ladders where

-- File Charter:
--   * Generates the two focused Imp Ladders used by the CTI balance packet.
--   * The first isolates Example 12's second target reveal and current lambda.
--   * The second isolates the matching beta conceal scope at checkpoint 12.
--   * Depends only on the live trusted Example 12 derivations.

import Data.Fin as Fin
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (＇_)
import Imprecision as I
import CastTerms as C
import TermCtx as TC
import Conversion
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.ImpLadder using (impLadderDefault)
open import proof.DGG.SourceRebase using (source-rebase-now)
import proof.DGG.Examples.Example12 as Ex


checkpoint₁-current-lambda :
  Ex.checkpoint₁-beta-current CTI.⊢²
    C.ƛ (C.` 0) ⊑ C.ƛ (C.` 0)
      ∶ I.⇒⊑⇒ I.X⊑X I.X⊑X
checkpoint₁-current-lambda =
  CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.X⊑X}
    (CTI.x⊑x² {A = ＇ Fin.zero} {B = ＇ Fin.zero}
      {p = I.X⊑X} TC.Z TC.Z)


checkpoint₁-second-reveal :
  Ex.checkpoint₁-alpha-current CTI.⊢²
    C.ƛ (C.` 0) ⊑
      (C.ƛ (C.` 0)) C.↑
        (Conversion.seal Fin.zero (＇ (Fin.suc Fin.zero))
          Conversion.↦↑
         Conversion.unseal Fin.zero (＇ (Fin.suc Fin.zero)))
      ∶ I.⇒⊑⇒ I.X⊑X I.X⊑X
checkpoint₁-second-reveal =
  CTI.⊑reveal-rebase² Ex.checkpoint₁-beta-reveal⊢
    (source-rebase-now Ex.checkpoint₁-beta-ok
      Ex.checkpoint₁-beta-representation)
    checkpoint₁-current-lambda
    (I.⇒⊑⇒ I.X⊑X I.X⊑X)


checkpoint₁-second-reveal-ladder : String
checkpoint₁-second-reveal-ladder =
  impLadderDefault checkpoint₁-second-reveal

checkpoint₁-second-reveal-ladder-pinned :
  checkpoint₁-second-reveal-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦＇X ⊑[X⊑★] Y′↦★⟩\n" ++
    "openFramesᶜ γ = [X ↔ Y′]\n" ++
    "source term  A        ηᴸA      ⊑ costs                       ηᴿB      B          target term\n" ++
    "───────────  ───────  ───────  ────────────────────────────  ───────  ─────────  ───────────────────\n" ++
    "─            (X ⇒ X)  (Z ⇒ Z)  Z ≈ Z, Z ≈ Z + source rebase  (Z ⇒ Z)  (Y′ ⇒ Y′)  □ ↑ unseal X′ ⇒-rev\n" ++
    "λx. □        (X ⇒ X)  (Y ⇒ Y)  Y ≈ Y, Y ≈ Y                  (Y ⇒ Y)  (X′ ⇒ X′)  λx. □\n" ++
    "x            X        Y        Y ≈ Y                         Y        X′         x"
checkpoint₁-second-reveal-ladder-pinned = refl


checkpoint₁₂-beta-conceal-ladder : String
checkpoint₁₂-beta-conceal-ladder =
  impLadderDefault Ex.checkpoint₁₂-beta-concealed

checkpoint₁₂-beta-conceal-ladder-pinned :
  checkpoint₁₂-beta-conceal-ladder ≡
    "⟨X: ─ ⊑[X⊑★] X′↦ℕ │ Y: X↦ℕ ⊑[X⊑★] Y′↦＇Z′ │ Z: ─ ⊑[X⊑★] Z′↦★⟩\n" ++
    "openFramesᶜ γ = [X ↔ Y′, X ↔ Z′]\n" ++
    "source term  A  ηᴸA  ⊑ costs                          ηᴿB  B   target term\n" ++
    "───────────  ─  ───  ───────────────────────────────  ───  ──  ───────────\n" ++
    "─            X  Y    Y ≈ Y + source rebase            Y    Y′  □ ↓ seal Y′\n" ++
    "─            X  Z    Z ≈ Z + source rebase            Z    Z′  □ ↓ seal Z′\n" ++
    "─            X  X    mark X⊑★ at X                    ★    ★   □ ⟨ X′↦★ ⟩\n" ++
    "□ ↓ seal X   X  X    X ≈ X + matched conceal partner  X    X′  □ ↓ seal X′\n" ++
    "7            ℕ  ℕ    ℕ⊑ℕ                              ℕ    ℕ   7"
checkpoint₁₂-beta-conceal-ladder-pinned = refl
