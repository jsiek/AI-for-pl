NS-4 stage 1f exponential administration rank calibration

Date: 2026-08-14

Surface:

  Statement-first calibration of the revised secondary rank below
  `pendingCastMass`.

Rank:

  `rank = (nameFrames, expPotential, spineLength)`

  `expPotential` sums `3 ^ crossings` over every reveal/conceal wrapper on
  the value and every reveal/conceal frame in the pending spine.

  A value wrapper crosses every pending `name-type-app-frame` in the spine.
  A reveal/conceal frame crosses the pending `name-type-app-frame`s after it
  in the spine.  `type-transport-frame` and `cast-frame` do not charge.

Calibration against the stage 1e child spines:

  Let `n = nameFrames spine` for the caller tail.

  `allv-Λ`:

    Parent spine:

      `name-type-app-frame B X refl refl ▻ⁱ spine`

    Peeled child spine:

      `type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
       mapInstantiationSpine (bind (＇ X)) spine`

    The head name frame is consumed, so `nameFrames` drops from `suc n` to
    `n`.  Lower components are irrelevant.

  `allv-reveal`:

    Parent state:

      value: `V ↑ `∀↑ c`
      spine: `name-type-app-frame B X refl refl ▻ⁱ spine`

    Parent wrapper charge: `3 ^ (n + 1)`.

    Peeled child spine:

      `name-type-app-frame (applyBody (bind (＇ X)) C) zero refl refl ▻ⁱ
       type-transport-frame (applyBody-open-zero C) ▻ⁱ
       reveal-frame c ▻ⁱ
       reveal-frame (〖 zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
       type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
       mapInstantiationSpine (bind (＇ X)) spine`

    The two generated reveal frames sit after the inner name frame, so each
    charges `3 ^ n`.  The type-transport frames charge `0`.

    `3 ^ (n + 1) = 3 * 3 ^ n > 2 * 3 ^ n`.

  `allv-conceal`:

    The child spine is the same as `allv-reveal`, except the first exposed
    conversion frame is `conceal-frame c`:

      `name-type-app-frame (applyBody (bind (＇ X)) C) zero refl refl ▻ⁱ
       type-transport-frame (applyBody-open-zero C) ▻ⁱ
       conceal-frame c ▻ⁱ
       reveal-frame (〖 zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
       type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
       mapInstantiationSpine (bind (＇ X)) spine`

    The same arithmetic applies:

      `3 ^ (n + 1) > 2 * 3 ^ n`.

  Conversion frame discharge:

    Moving a head reveal/conceal frame onto a value preserves the charged
    crossing set.  If the frame steps, `mapInstantiationSpine keep` preserves
    frame classes and order.  `expPotential` is unchanged and `spineLength`
    strictly decreases.

  Inert cast absorption:

    Cast frames are not conversion units.  Moving the cast syntax from the
    spine to the value preserves `expPotential`, and `spineLength` strictly
    decreases.

  `mapInstantiationSpine`:

    `keep` and `bind` preserve frame classes and order.  Therefore they
    preserve `nameFrames`, `expPotential`, and `spineLength`.

  `allv-∀`, `allv-gen`, and safe-inst:

    The primary `pendingCastMass` decreases by the existing cast-mass lemmas,
    so the secondary rank is not consulted.

Outcome:

  The revised base `3` closes the refuted stage 1e cells.  No larger weight is
  needed for these concrete peels: a wrapper at `k = n + 1` crossings expands
  to two frames at `k - 1 = n` crossings, and `2 * 3 ^ n < 3 ^ (n + 1)`.
