/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualNativeAccess
public import LeanCanny.Algebra.IntegralCriticalFlatOriginalCoefficient
/-! # Exact original integer coefficient leaves of virtual sweep arithmetic

The leaf reads the immutable spatial integer polynomial. Its scalar diagonal
matrix identity holds in the actual nilpotent coefficient algebra. Native
query formatting and charged scalar computation remain separate.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualOriginalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedCutSource IntegralMixedVirtualSweepSource IntegralMixedVirtualNativeBits
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev original (F : Family) (I : Indices F) := (arithmetic F I).toGradient.toFrozen.toSource

noncomputable def integer (F : Family) (I : Indices F) (q : List Bool) :
    MvPolynomial (Fin ((original F I).arity q)) ℤ := (F.spatial q).low

theorem mapped (F : Family) (I : Indices F) (q : List Bool) :
    letI := (original F I).ring q
    (original F I).polynomial q = (integer F I q).map (Int.castRingHom ((original F I).carrier q)) := rfl

noncomputable def coefficient (F : Family) (I : Indices F) (q : List Bool) (k : ℕ) : ℤ :=
  IntegralCriticalFlatOriginalCoefficientBits.coefficient (original F I) (integer F I) q k

noncomputable def scalar (F : Family) (I : Indices F) (p : List Bool) : List Bool :=
  residueBits (coefficient F I (pairFst p) (Nat.fromBitsLE (pairSnd p)) : ZMod (I.modulus (pairFst p)))

theorem scalar_packet (F : Family) (I : Indices F) (q : List Bool) (k : ℕ) :
    scalar F I (pair q (BinaryNatCode.encode k)) =
      residueBits (coefficient F I q k : ZMod (I.modulus q)) := by
  generalize HP : pair q (BinaryNatCode.encode k) = p
  have HB : pairFst p = q := by rw [← HP, pairFst_pair]
  have HK : Nat.fromBitsLE (pairSnd p) = k := by
    rw [← HP, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst q
  unfold scalar
  rw [HK]

theorem reader_packet (F : Family) (I : Indices F) (q : List Bool) (k : ℕ)
    (r t : Fin (count (F.birth q + 1) (F.width q))) :
    IntegralCriticalOriginalCoefficientBits.reader (scalar F I)
      (pair (IntegralClearedCoefficientBits.context q r.val t.val) (BinaryNatCode.encode k)) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        (((F.spatial q).low.map (Int.castRingHom (Coefficient F q))).coeff
          (RationalSubstitution.Indexed.exponentVector (F.ambient q + 1)
            (entry (F.spatial q).degree.size k))) r t : ℤ) : ZMod (I.modulus q)) :=
  IntegralCriticalFlatOriginalCoefficientBits.reader_packet (original F I) (integer F I)
    (mapped F I) (scalar F I) (scalar_packet F I) q k r t

theorem access_coefficient_packet (F : Family) (I : Indices F) (h : Metadata F I)
    (q : List Bool) (k : ℕ) (r t : Fin (count (F.birth q + 1) (F.width q))) :
    (arithmeticAccess F I h).coefficient
      (pair (IntegralClearedCoefficientBits.context q r.val t.val) (BinaryNatCode.encode k)) =
      IntegralCriticalOriginalCoefficientBits.reader (scalar F I)
        (pair (IntegralClearedCoefficientBits.context q r.val t.val) (BinaryNatCode.encode k)) :=
  ((arithmeticAccess F I h).coefficient_eq q k r t).trans (reader_packet F I q k r t).symm

noncomputable def value (P : IntegralCriticalHistoryTask.Parameters) (F : Family) (I : Indices F) :=
  IntegralCriticalFlatOriginalCoefficientBits.value P (original F I) (scalar F I)

theorem value_actual (P : IntegralCriticalHistoryTask.Parameters) (F : Family) (I : Indices F) (q : List Bool) :
    value P F I q = residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      (((F.spatial q).low.map (Int.castRingHom (Coefficient F q))).coeff
        (RationalSubstitution.Indexed.exponentVector (F.ambient q + 1)
          (entry (F.spatial q).degree.size (IntegralCriticalHistoryTask.get P .sourceIndex q))))
      (IntegralCriticalFlatOriginalCoefficientBits.index P (original F I) .row q)
      (IntegralCriticalFlatOriginalCoefficientBits.index P (original F I) .col q) : ℤ) : ZMod (I.modulus q)) :=
  IntegralCriticalFlatOriginalCoefficientBits.actual_value P (original F I) (integer F I)
    (mapped F I) (scalar F I) (scalar_packet F I) q

theorem value_space (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Family) (I : Indices F) (h : Metadata F I) (hs : SpaceFunction (scalar F I)) :
    SpaceFunction (value P F I) :=
  IntegralCriticalFlatOriginalCoefficientBits.value_space P a (original F I)
    (arithmeticAccess F I h).toGradient.toFrozen.toAccess (scalar F I) hs

theorem value_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Family) (I : Indices F) (h : Metadata F I) (hs : scalar F I ∈ FP) : value P F I ∈ FP :=
  IntegralCriticalFlatOriginalCoefficientBits.value_FP P a (original F I)
    (arithmeticAccess F I h).toGradient.toFrozen.toAccess (scalar F I) hs
end LeanCanny.Algebra.IntegralMixedVirtualOriginalBits
