/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscEntryProgram
/-! # Exact finite PSC entries and native-address validity -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
attribute [local irreducible] IntegralMixedCutNilpotent.basis IntegralMixedSquarefreeMatrixSource.coordinateImage
attribute [local irreducible] matrixCoefficient

def Labels (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  get P .slot9 q < dimension P F q ∧ get P .slot10 q < dimension P F q ∧
    get P .row q < rank P F q ∧ get P .col q < rank P F q

theorem packet_row (P : Parameters) (q : List Bool) : PrincipalDerivativeEntryRequest.row (packet P q) = get P .slot9 q := by
  simp only [PrincipalDerivativeEntryRequest.row, packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
theorem packet_col (P : Parameters) (q : List Bool) : PrincipalDerivativeEntryRequest.col (packet P q) = get P .slot10 q := by
  simp only [PrincipalDerivativeEntryRequest.col, packet, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
theorem packet_dimension (P : Parameters) (F : Family) (q : List Bool) :
    PrincipalDerivativeEntryRequest.firstBlock (parameters P F) (packet P q) +
      PrincipalDerivativeEntryRequest.secondBlock (parameters P F) (packet P q) = dimension P F q := by
  simp only [PrincipalDerivativeEntryRequest.firstBlock, PrincipalDerivativeEntryRequest.secondBlock, packet_original]
  rfl

theorem request_labels (P : Parameters) (F : Family) (q : List Bool) (hr : Request P F q) : Labels P F q := by
  refine ⟨?_, ?_, hr.2.1, hr.2.2⟩
  · simpa only [packet_row, packet_dimension] using hr.1.1
  · simpa only [packet_col, packet_dimension] using hr.1.2.1

theorem coefficient_finite (P : Parameters) (F : Family) (q : List Bool)
    (r t : Fin ((source P F).rank q)) (hr : get P .row q = r.val) (ht : get P .col q = t.val) :
    coefficientValue P F q = Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis
      ((IntegralMixedSquarefreeMatrixSource.coordinateImage ((IntegralMixedVirtualTaskBits.family P F).state q)
        ((IntegralMixedVirtualTaskBits.family P F).birth_bound q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
        ((IntegralMixedVirtualTaskBits.indices P F).coordinate q)).coeff (requestedCoefficient P F q)) r t := by
  let R := (source P F).rank q
  have hR : 0 < R := Nat.pow_pos (Nat.two_pow_pos _)
  let ri : Fin R := ⟨get P .row q % R, Nat.mod_lt _ hR⟩
  let ti : Fin R := ⟨get P .col q % R, Nat.mod_lt _ hR⟩
  let read (a b : Fin R) : ℤ := Algebra.leftMulMatrix
    (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis
      ((IntegralMixedSquarefreeMatrixSource.coordinateImage ((IntegralMixedVirtualTaskBits.family P F).state q)
        ((IntegralMixedVirtualTaskBits.family P F).birth_bound q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
        ((IntegralMixedVirtualTaskBits.indices P F).coordinate q)).coeff (requestedCoefficient P F q)) a b
  have HI : ri = r := by
    apply Fin.ext
    change get P .row q % R = r.val
    rw [hr]
    exact Nat.mod_eq_of_lt r.isLt
  have HT : ti = t := by
    apply Fin.ext
    change get P .col q % R = t.val
    rw [ht]
    exact Nat.mod_eq_of_lt t.isLt
  have H : coefficientValue P F q = read ri ti := by
    unfold coefficientValue
    rw [← IntegralMixedVirtualQueryBits.matrix_pull F (IntegralMixedVirtualTaskBits.saved P) q]
    exact IntegralMixedValueCoordinateChild.matrixCoefficient_eq (IntegralMixedVirtualTaskBits.family P F)
      q (get P .slot13 q) (requestedCoefficient P F q) (get P .row q) (get P .col q)
  exact H.trans (congrArg₂ read HI HT)

theorem matrix_entry (P : Parameters) (F : Family) (q : List Bool)
    (i j : Fin ((source P F).dimension q)) (r t : Fin ((source P F).rank q))
    (hi : get P .slot9 q = i.val) (hj : get P .slot10 q = j.val)
    (hr : get P .row q = r.val) (ht : get P .col q = t.val) :
    (source P F).entryMatrix q i j r t =
      if PrincipalDerivativeEntryRequest.valid (parameters P F) (packet P q) then coefficientValue P F q *
        (PrincipalDerivativeEntryRequest.multiplier (parameters P F) (packet P q) : ℤ) else 0 := by
  let p := IntegralMixedSquarefreeMatrixSource.coordinateImage ((IntegralMixedVirtualTaskBits.family P F).state q)
    ((IntegralMixedVirtualTaskBits.family P F).birth_bound q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
    ((IntegralMixedVirtualTaskBits.indices P F).coordinate q)
  have H := PrincipalDerivativeEntryRequest.matrix_entry (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis (parameters P F) p q i j r t
  have HP : pair (IntegralBlockMomentBits.context q r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) = packet P q := by
    rw [← hi, ← hj, ← hr, ← ht]
    rfl
  dsimp only at H
  rw [HP] at H
  change (source P F).entryMatrix q i j r t =
    if PrincipalDerivativeEntryRequest.valid (parameters P F) (packet P q) then
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis (p.coeff (requestedCoefficient P F q)) r t *
        (PrincipalDerivativeEntryRequest.multiplier (parameters P F) (packet P q) : ℤ) else 0 at H
  rw [← coefficient_finite P F q r t hr ht] at H
  exact H

end LeanCanny.Algebra.IntegralMixedPscEntryBits
