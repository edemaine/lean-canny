/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelCoefficientSpace
public import LeanCanny.Algebra.IntegralMixedOriginalSpatialLeaves
/-! # Actual mixed critical leaves for an appended-level original source

The two costs are the old original coefficient reader and the original
integer level coefficient modulo the current modulus. Both are charged
in space; neither is assumed to be a polynomial-time integer word.
-/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelOriginalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralMixedOriginalSpatialTermBits
open scoped Classical
attribute [local irreducible] IntegralMixedPhysicalOriginalBits.scalar IntegralMixedVirtualOriginalBits.scalar

theorem physical (F : IntegralMixedPhysicalCriticalBits.Family)
    (I : IntegralMixedPhysicalCriticalBits.Indices F) (h : IntegralMixedPhysicalCriticalBits.Metadata F I)
    (old : (q : List Bool) → MvPolynomial (Fin (F.ambient q)) ℤ) (A : List Bool → ℤ)
    (hlow : ∀ q, (F.spatial q).low = FermatLevelCoefficientBits.polynomial F.ambient old A q)
    (EO : SpaceFunction (IntegralOriginalTermCoefficientBits.scalar F.ambient (fun q => (F.spatial q).degree.size) I.modulus old))
    (EA : SpaceFunction (fun q => residueBits (A q : ZMod (I.modulus q)))) :
    SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar F I) := by
  have E := FermatLevelCoefficientBits.evaluator F.ambient (fun q => (F.spatial q).degree.size) I.modulus
    h.ambient (IntegralMixedPhysicalCriticalBits.sourceWidth_unary F I h) h.modulus I.modulus_ne_zero old A EO EA
  apply E.congr
  funext p
  rw [physical_source_scalar]
  unfold IntegralOriginalTermCoefficientBits.scalar
  rw [hlow]

theorem virtual (F : IntegralMixedCutSource.Family)
    (I : IntegralMixedVirtualSweepSource.Indices F) (h : IntegralMixedVirtualNativeBits.Metadata F I)
    (old : (q : List Bool) → MvPolynomial (Fin (F.ambient q)) ℤ) (A : List Bool → ℤ)
    (hlow : ∀ q, (F.spatial q).low = FermatLevelCoefficientBits.polynomial F.ambient old A q)
    (EO : SpaceFunction (IntegralOriginalTermCoefficientBits.scalar F.ambient (fun q => (F.spatial q).degree.size) I.modulus old))
    (EA : SpaceFunction (fun q => residueBits (A q : ZMod (I.modulus q)))) :
    SpaceFunction (IntegralMixedVirtualOriginalBits.scalar F I) := by
  have E := FermatLevelCoefficientBits.evaluator F.ambient (fun q => (F.spatial q).degree.size) I.modulus
    h.ambient (IntegralMixedVirtualNativeBits.sourceWidth_unary F I h) h.modulus I.modulus_ne_zero old A EO EA
  apply E.congr
  funext p
  rw [virtual_source_scalar]
  unfold IntegralOriginalTermCoefficientBits.scalar
  rw [hlow]

end LeanCanny.Algebra.FermatLevelOriginalBits
