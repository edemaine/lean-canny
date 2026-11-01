/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueTaskBounds
public import LeanCanny.Algebra.IntegralMixedFullRowMultiplier

/-! # Actual restored original-row entries at the value-system width

The original-row child reads the full original equation or gradient,
including the free Fermat term. Its spatial width is the fixed value Gram
width; the lower-row controller separately repacks to the critical width.
The snapshot names the literal parent, coordinate, exponent and basis
indices, so fresh task readbacks suffice to identify the requested entry.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRestoredSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps IntegralMixedValueHomogeneousQueries
open scoped Classical

noncomputable def entryAt (F : Family) (key : List Bool) (j e r t : ℕ) : ℤ :=
  Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state key)).finBasis
    ((IntegralMixedVirtualOriginalRows.row F key
      ⟨j % (F.ambient key - (F.rule key).critical.offset.val + 1), Nat.mod_lt _ (by omega)⟩).coeff
        (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial key) (F.rule key)) e))
    ⟨r % count (F.birth key + 1) (F.width key), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % count (F.birth key + 1) (F.width key), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (entryAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
    (get P .target q) (get P .row q) (get P .col q) : ZMod (modulus P q))

theorem original_child (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool)
    (hr : HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q)) :
    value P F (originalTask P F q) =
      residueBits (entryAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
        (originalTarget P F q) (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [value, originalTask_saved, originalTask_modulus]
  simp only [originalTask_get, reduceCtorEq, ite_false, ite_true,
    min_eq_left (IntegralMixedValueTaskBounds.originalTarget_cap P F h q hr)]

theorem value_full_row (P : Parameters) (F : Family) (q : List Bool) :
    value P F q = residueBits ((Algebra.leftMulMatrix
      (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis
      ((IntegralMixedVirtualOriginalRows.row (IntegralMixedVirtualTaskBits.family P F) q
        ((IntegralMixedVirtualTaskBits.indices P F).coordinate q)).coeff
          (IntegralMixedFullRowMultiplier.exponent (IntegralMixedVirtualTaskBits.family P F)
            (IntegralMixedVirtualTaskBits.indices P F)
            (fun q => IntegralMixedGridValue.width ((IntegralMixedVirtualTaskBits.family P F).spatial q)
              ((IntegralMixedVirtualTaskBits.family P F).rule q)) q))
      ((IntegralMixedVirtualTaskBits.indices P F).row q) ((IntegralMixedVirtualTaskBits.indices P F).col q) : ℤ) :
        ZMod (modulus P q)) := rfl

theorem canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P F q := ⟨_, rfl⟩

end LeanCanny.Algebra.IntegralMixedValueRestoredSource
