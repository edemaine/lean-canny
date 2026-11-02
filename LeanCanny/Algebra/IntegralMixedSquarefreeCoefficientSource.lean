/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientValue
public import LeanCanny.Algebra.IntegralMixedNormalizationRawQuery
/-! # The native squarefree kernel supplies the actual truncated raw-cut entries

The exact selected-kind equality is an explicit decoder validation. It
identifies the same old parent, coordinate and PSC index. Truncation
uses the original recorded scalar degree; no absolute norm is recomputed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical
attribute [local irreducible] IntegralMixedCutMatrix.coefficientMatrix

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool := residueBits
  (IntegralCriticalTotalSnapshotBits.integerEntry
    ((source F).coefficient (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q))
    (get P .row q) (get P .col q) : ZMod (modulus P q))

theorem value_rawCut (P : Parameters) (F : Family) (q : List Bool) :
    value P F q = IntegralMixedNormalizationTopBits.rawCutValue P F q := rfl

theorem value_eq (P : Parameters) (F : Family) (q : List Bool)
    (hkind : F.kind (IntegralMixedVirtualTaskBits.saved P q) =
      IntegralMixedSquarefreeCoefficientSnapshot.kind F (IntegralMixedVirtualTaskBits.saved P q)
        (get P .slot13 q) (get P .slot8 q)) :
    value P F q = if get P .coefficient q ≤ F.degree (IntegralMixedVirtualTaskBits.saved P q) then
      IntegralMixedSquarefreeCoefficientValue.value P F q else [] := by
  unfold value
  rw [source_coefficient, hkind]
  by_cases hd : get P .coefficient q ≤ F.degree (IntegralMixedVirtualTaskBits.saved P q)
  · rw [ite_eq_left hd, ite_eq_left hd]
    rfl
  · rw [ite_eq_right hd, ite_eq_right hd]
    change residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
      (0 : Matrix (Fin (FixedWidthPolynomial.count (F.birth (IntegralMixedVirtualTaskBits.saved P q))
        (F.width (IntegralMixedVirtualTaskBits.saved P q))))
        (Fin (FixedWidthPolynomial.count (F.birth (IntegralMixedVirtualTaskBits.saved P q))
          (F.width (IntegralMixedVirtualTaskBits.saved P q)))) ℤ)
      (get P .row q) (get P .col q) : ZMod (modulus P q)) = []
    simp only [IntegralCriticalTotalSnapshotBits.integerEntry, Matrix.zero_apply, dite_eq_ite,
      ite_self, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem degree_guard_FP (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree) :
    FPPred (fun q => get P .coefficient q ≤ F.degree (IntegralMixedVirtualTaskBits.saved P q)) :=
  (get_binary P a .coefficient).le (hd.comp (IntegralMixedVirtualTaskBits.saved_FP P a))

end LeanCanny.Algebra.IntegralMixedSquarefreeCoefficientSource
