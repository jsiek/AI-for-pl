module
  proof.Left.AllocationRuntime.NuImprecisionLeftSourceAllocationRuntimeTransportLemma
  where

-- File Charter:
--   * Supplies the canonical bullet-free left-renaming dependency to the
--     source-allocation runtime transport proof.
--   * Exposes the assembled ordinary and quotient runtime transport maps.
--   * Contains no carrier, postulate, hole, permissive option, compatibility
--     shim, or termination bypass.

open import proof.Left.Core.NuImprecisionLeftRenameNoBulletProof using
  (left-rename-no-bullet)
open import proof.Left.AllocationRuntime.NuImprecisionLeftSourceAllocationRuntimeTransportDef using
  (LeftSourceAllocationRuntimeTransport)
open import proof.Left.AllocationRuntime.NuImprecisionLeftSourceAllocationRuntimeTransportProof using
  (left-source-allocation-runtime-transport-proof)


left-source-allocation-runtime-transport :
  LeftSourceAllocationRuntimeTransport
left-source-allocation-runtime-transport =
  left-source-allocation-runtime-transport-proof left-rename-no-bullet
