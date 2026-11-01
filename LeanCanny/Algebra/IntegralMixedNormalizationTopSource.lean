/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutNormalizedSource
public import LeanCanny.Algebra.IntegralMixedRoutineContextQuery
public import LeanCanny.Algebra.IntegralMixedVirtualCaps
public import LeanCanny.Algebra.IntegralBerkowitzBlockSource
public import LeanCanny.Algebra.IntegralCriticalTotalMatrixSnapshot
/-! # The actual leading-coefficient matrix as an integer characteristic source

Its coefficient algebra is ℤ of rank one. The matrix retains the selected
old prefix and cut kind; arithmetic indices and caller moduli do not select it.
No matrix evaluator or normalization reader is a metadata premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

def dimension (F : Family) (key : List Bool) : ℕ := count (F.birth key) (F.width key)

noncomputable def top (F : Family) (key : List Bool) : Matrix (Fin (dimension F key)) (Fin (dimension F key)) ℤ :=
  IntegralMixedCutMatrix.coefficientMatrix (F.state key) (F.birth_bound key) (F.rule key) (F.kind key) (F.degree key)

noncomputable def source (P : Parameters) (F : Family) : Source where
  dimension q := dimension F (IntegralMixedVirtualTaskBits.saved P q)
  rank _ := 1
  carrier _ := ℤ
  ring _ := inferInstance
  nontrivial _ := inferInstance
  basis _ := Module.Basis.singleton (Fin 1) ℤ
  matrix q := top F (IntegralMixedVirtualTaskBits.saved P q)
  modulus := modulus P
  modulus_ne_zero := modulus_ne_zero P
  coefficient := get P .coefficient
  basisRow _ := 0
  basisCol _ := 0

theorem dimension_binary (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    BinaryFn (fun q => dimension F (IntegralMixedVirtualTaskBits.saved P q)) :=
  BinaryFn.of_bits (mem_FP_of_eq
    (countCode_mem_FP (h.birth.comp (IntegralMixedVirtualTaskBits.saved_FP P a))
      (h.width.comp (IntegralMixedVirtualTaskBits.saved_FP P a)))
    (fun q => countCode_code _ _ q))

noncomputable def entry (P : Parameters) (F : Family) (p : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
    (top F (IntegralMixedVirtualTaskBits.saved P (original p)))
    (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p)) (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p)) :
      ZMod (modulus P (original p)))

theorem singleton_entry (z : ℤ) (r t : Fin 1) :
    Algebra.leftMulMatrix (Module.Basis.singleton (Fin 1) ℤ) z r t = z := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.singleton_apply, mul_one, Module.Basis.singleton_repr]

noncomputable def access (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    IntegralBerkowitzBlockBits.Access (source P F) where
  dimension := dimension_binary P a F h
  rank := BinaryFn.const 1
  modulus := modulus_binary P a
  coefficient := get_binary P a .coefficient
  basisRow := BinaryFn.const 0
  basisCol := BinaryFn.const 0
  entry := entry P F
  entry_eq q i j r t := by
    let p := pair (IntegralBlockMomentBits.context q r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
    have HP : original p = q := by simp only [p, original, IntegralBlockMomentBits.context, pairFst_pair]
    have HI : MatrixMoment.EntryBits.rowIndex p = BinaryNatCode.encode i.val := by
      simp only [p, MatrixMoment.EntryBits.rowIndex, pairFst_pair, pairSnd_pair]
    have HJ : MatrixMoment.EntryBits.colIndex p = BinaryNatCode.encode j.val := by
      simp only [p, MatrixMoment.EntryBits.colIndex, pairSnd_pair]
    change entry P F p = _
    unfold entry
    rw [HP, HI, HJ]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [IntegralCriticalTotalSnapshotBits.integerEntry_fin]
    exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) (singleton_entry _ r t).symm

theorem value_coefficient (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).value q = residueBits
      ((top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly.coeff (get P .coefficient q) : ZMod (modulus P q)) := by
  unfold Source.value Source.coefficientMatrix
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) (singleton_entry _ _ _)

theorem top_normalized_leading (F : Family) (key : List Bool) :
    IntegralMixedHistory.normalizedScalarLeading (F.state key)
      (IntegralMixedCutMatrix.raw (F.state key) (F.birth_bound key) (F.rule key) (F.kind key) (F.degree key)) (F.degree key) =
      IntegralParameterInverse.denominator (top F key).charpoly :=
  IntegralMixedCutMatrix.leading_eq _ _ _ _ _

theorem dimension_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    dimension F (IntegralMixedVirtualTaskBits.saved P q) ≤ numericCap P (RankedHistoryTask.root q) := by
  exact (IntegralMixedVirtualCaps.auxiliary_rank_le P F g q hv 0 (by decide)).trans
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.1

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
