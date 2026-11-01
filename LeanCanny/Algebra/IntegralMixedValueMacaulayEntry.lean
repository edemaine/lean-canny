/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueGramEntry
public import LeanCanny.Algebra.MacaulayIntegralEntryRequest

/-! # Actual mapped value-system coefficients feed native Macaulay entries

Every degree and exponent width comes from the original spatial source.
The lower replies are coefficients of the actual double-nilpotent system,
not entries of an assumed Macaulay or Gram matrix.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueMacaulayEntry
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource
open IntegralMixedVirtualSweepSource IntegralMixedVirtualNativeBits
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis

noncomputable def layout (F : Family) : MacaulayFullBoxBits.Layout where
  arity q := F.ambient q - (F.rule q).critical.offset.val + 1 + 1
  width q := IntegralMixedGridValue.width (F.spatial q) (F.rule q)
  level q := Macaulay.level (RelativeProjectiveValueGram.degrees
    (fun _ : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) =>
      IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)) (F.spatial q).degree)
  degree q j := if j = 0 then (F.spatial q).degree else
    IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)

theorem layout_controls (F : Family) (I : Indices F) (h : Metadata F I) : (layout F).Controls where
  arity := (free_unary F I h).add (UnaryFn.const 1)
  width := IntegralMixedValueDeterminantMetadata.width_unary F I h
  level := IntegralMixedValueDeterminantMetadata.level_binary F I h
  degree := BinaryFn.ite ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0))
    (h.degree.comp pairFst_mem_FP)
    ((IntegralMixedValueDeterminantMetadata.coordinateDegree_binary F I h).comp pairFst_mem_FP)

theorem degrees_eq (F : Family) (q : List Bool) :
    (fun j : Fin ((layout F).arity q) => (layout F).degree q j.val) =
      RelativeProjectiveValueGram.degrees
        (fun _ : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) =>
          IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q))
          (F.spatial q).degree := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [layout, Fin.val_zero, ite_true, RelativeProjectiveValueGram.degrees, Fin.cases_zero]
  · simp only [layout, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
      RelativeProjectiveValueGram.degrees, Fin.cases_succ]

noncomputable abbrev program (F : Family) (I : Indices F) :=
  MacaulayIntegralEntryRequest.program (layout F) I.modulus

theorem controls (F : Family) (I : Indices F) (h : Metadata F I) : (program F I).Controls :=
  MacaulayIntegralEntryRequest.controls _ (layout_controls F I h) _ h.modulus

theorem entry_value (F : Family) (I : Indices F) (reply : List Bool → List Bool) (q : List Bool)
    (r t : Fin (count (F.birth q + 2) (F.width q)))
    (ha : ∀ (j : Fin ((layout F).arity q)) k, reply
      (pair q (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode k)
        (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
        ((IntegralMixedValueDoubleSystem.mappedSystem F q (I.coordinate q) j).coeff
          (RationalSubstitution.Indexed.exponentVector ((layout F).arity q)
            (entry ((layout F).width q) k))) r t : ℤ) : ZMod (I.modulus q)))
    (a : MacaulayFullBox.Row ((layout F).arity q) ((layout F).width q))
    (b : MacaulayFullBox.Column ((layout F).arity q) ((layout F).width q)) :
    (program F I).value reply
        (MacaulayFullBoxBits.entryPacket q (MacaulayFullBoxBits.rowNumber _ _ a) b.val r.val t.val) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
        (MacaulayFullBox.matrix (IntegralMixedValueDoubleSystem.mappedSystem F q (I.coordinate q))
          (RelativeProjectiveValueGram.degrees
            (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q))
              (F.spatial q).degree)
          (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) a b) r t : ℤ) : ZMod (I.modulus q)) := by
  have H := MacaulayIntegralEntryRequest.actual_value (IntegralMixedValueDoubleNilpotent.basis (F.state q))
    (layout F) I.modulus reply q (IntegralMixedValueDoubleSystem.mappedSystem F q (I.coordinate q))
    (by rw [degrees_eq]; rfl) (Nat.pos_of_ne_zero (I.modulus_ne_zero q)) r t ha a b
  rw [degrees_eq] at H
  exact H

end LeanCanny.Algebra.IntegralMixedValueMacaulayEntry
