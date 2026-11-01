/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeOriginal
public import LeanCanny.Algebra.IntegralMixedPhysicalSnapshot
/-! # Original and bumped derivative coefficient models of the physical source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalSnapshotBits
set_option backward.isDefEq.respectTransparency false

noncomputable def originalAt (F : Family) (key : List Bool) (k r t m : ℕ) (hm : m ≠ 0) : List Bool := by
  let S := (sourceAt F key 0 0 0 r t m hm).toEuler
  let := S.ring []
  exact residueBits ((Algebra.leftMulMatrix (S.basis [])
    ((S.polynomial []).coeff (RationalSubstitution.Indexed.exponentVector (S.arity [])
      (FixedWidthPolynomial.entry (S.sourceWidth []) k))) (S.row []) (S.col []) : ℤ) : ZMod m)

noncomputable def derivativeAt (F : Family) (key : List Bool) (j k r t m : ℕ) (hm : m ≠ 0) : List Bool := by
  let S := (sourceAt F key 0 0 0 r t m hm).toEuler
  let := S.ring []
  exact residueBits ((Algebra.leftMulMatrix (S.basis [])
    ((MvPolynomial.pderiv (IntegralCriticalGradientBits.freeIndex S.toGradient []
      ⟨j % S.free [], Nat.mod_lt _ (S.free_pos [])⟩) (S.polynomial [])).coeff
      (RationalSubstitution.Indexed.exponentVector (S.arity []) (FixedWidthPolynomial.entry (S.sourceWidth []) k)))
      (S.row []) (S.col []) : ℤ) : ZMod m)

noncomputable def derivative (P : Parameters) (F : Family) (q : List Bool) :=
  derivativeAt F (IntegralMixedPhysicalTaskBits.saved P q) (get P .derivative q) (get P .sourceIndex q)
    (get P .row q) (get P .col q) (modulus P q) (modulus_ne_zero P q)

noncomputable abbrev source (P : Parameters) (F : Family) :=
  IntegralCriticalFlatDerivativeBits.eulerSource P (IntegralMixedPhysicalTaskBits.arithmetic P F)
noncomputable abbrev access (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F) :=
  IntegralCriticalFlatDerivativeBits.eulerAccess P a (IntegralMixedPhysicalTaskBits.arithmetic P F) (IntegralMixedPhysicalTaskBits.access P a F h).toEuler

theorem original_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedPhysicalNativeLowerBits.original P F q =
      originalAt F (IntegralMixedPhysicalTaskBits.saved P q) (get P .sourceIndex q) (get P .row q) (get P .col q)
        (modulus P q) (modulus_ne_zero P q) := by
  dsimp only [IntegralMixedPhysicalNativeLowerBits.original]
  rw [IntegralMixedPhysicalOriginalBits.value_actual]
  rfl

theorem originalAt_congr (F : Family) (key key' : List Bool) (k r t m k' r' t' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (hk : k = k') (hr : r = r') (ht : t = t') (hmod : m = m') :
    originalAt F key k r t m hm = originalAt F key' k' r' t' m' hm' := by
  subst key'; subst k'; subst r'; subst t'; subst m'
  rfl

theorem derivative_packet (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F) (q : List Bool) :
    IntegralDerivativeBits.value (source P F) (access P a F h)
      (IntegralCriticalFlatDerivativeBits.input P (source P F) q) = derivative P F q := by
  exact IntegralDerivativeBits.packet (source P F) (access P a F h) q (get P .sourceIndex q)
    (IntegralCriticalFlatOriginalCoefficientBits.index P (source P F).toSource .row q)
    (IntegralCriticalFlatOriginalCoefficientBits.index P (source P F).toSource .col q)
end LeanCanny.Algebra.IntegralMixedPhysicalCoefficientBits
