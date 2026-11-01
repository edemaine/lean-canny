/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalOriginalLeaf
/-! # Primitive physical coefficient reads use immutable original integers

The scalar leaf contains no bank, sampler, basis, height, denominator, or
creating-leading computation. Only the original spatial integer polynomial
and its bounded fixed-width exponent query occur in this identity.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalOriginalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedPhysicalCriticalBits
set_option backward.isDefEq.respectTransparency false

theorem scalar_immutable (F : Family) (I : Indices F) (p : List Bool) :
    scalar F I p = residueBits (((F.spatial (pairFst p)).low.coeff
      (RationalSubstitution.Indexed.exponentVector (F.ambient (pairFst p) + 1)
        (entry (F.spatial (pairFst p)).degree.size (Nat.fromBitsLE (pairSnd p)))) :
      ZMod (I.modulus (pairFst p)))) := rfl
end LeanCanny.Algebra.IntegralMixedPhysicalOriginalBits
