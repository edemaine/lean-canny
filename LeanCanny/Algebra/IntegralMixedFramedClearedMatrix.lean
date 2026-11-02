/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightSpace
public import LeanCanny.Algebra.IntegralMixedBankCoordinateBounds
/-! # Actual cleared bank matrices share one old prefix rank

The saved key and retained index are separate arguments. Thus all coordinates
of one bank have the same matrix index type, before sums and powers are formed.
Inactive native births and invalid retained indices have their literal zero
extension. No interpreted matrix reader is supplied.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedClearedMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev family (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedHistoryFamilyBits.family P D H
noncomputable def rank (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :=
  FixedWidthPolynomial.count ((family P D H).birth key) ((family P D H).width key)

theorem rank_pos (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    0<rank P D H key := pow_pos (Nat.two_pow_pos _) _

theorem birth_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (fun key=>(family P D H).birth key) :=
  (IntegralMixedFullHistoryFamilyBits.prefix_unary P a).of_eq (fun key=>(IntegralMixedFramedHistoryFamilyBits.family_birth P D H key).symm)

theorem rank_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : BinaryFn (rank P D H) :=
  ((BinaryFn.const 2).powUnary (a.width.comp pairFst_mem_FP)).powUnary (birth_unary P a D H)

def Active (P : Parameters) (key : List Bool) := IntegralMixedFramedHistoryFamilyBits.prefixLength P key<P.cap (pairFst key)

noncomputable def matrix (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : ℕ) : Matrix (Fin (rank P D H key)) (Fin (rank P D H key)) ℤ :=
  fun r t=>if Active P key then IntegralMixedFramedOldHeightBankBits.sourceEntry P D H key i r.val t.val else 0

noncomputable def wrap (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : ℕ) : Fin (rank P D H key) := ⟨i%rank P D H key,Nat.mod_lt _ (rank_pos P D H key)⟩

theorem sourceEntry_clamp (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i r t : ℕ) :
    IntegralMixedFramedOldHeightBankBits.sourceEntry P D H key (min i ((family P D H).birth key)) r t=
      IntegralMixedFramedOldHeightBankBits.sourceEntry P D H key i r t := by
  by_cases hi : i<(family P D H).birth key
  · rw [min_eq_left hi.le]
  · rw [min_eq_right (Nat.le_of_not_gt hi)]
    unfold IntegralMixedFramedOldHeightBankBits.sourceEntry
    rw [dite_eq_right (fun hv=>(Nat.lt_irrefl ((family P D H).birth key)) hv.1),dite_eq_right (fun hv=>hi hv.1)]

theorem matrix_actual (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (ha : Active P key) (i : Fin ((family P D H).birth key)) :
    matrix P D H key i.val=IntegralMixedBankCoordinatePolynomial.matrix ((family P D H).state key) i := by
  funext r t
  rw [matrix,ite_eq_left ha]
  unfold IntegralMixedFramedOldHeightBankBits.sourceEntry
  rw [dite_eq_left ⟨i.isLt,r.isLt,t.isLt⟩]
  rfl

attribute [local irreducible] matrix rank IntegralMixedFramedOldHeightBankBits.sourceEntry

def packet (key : List Bool) (i : ℕ) (mw : List Bool) (r t : ℕ) :=
  pair (pair (pair key mw) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))) (BinaryNatCode.encode i)

theorem finite_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key mw : List Bool) (i : ℕ) (r t : Fin (rank P D H key)) :
    IntegralMixedFramedOldHeightQueryBits.value P D H (packet key i mw r.val t.val)=
      residueBits (matrix P D H key i r t : ZMod (Nat.fromBitsLE mw+1)) := by
  have HR : FixedWidthPolynomial.count (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (P.width (pairFst key))=rank P D H key := by
    rw [rank,IntegralMixedFramedHistoryFamilyBits.family_birth]
    rfl
  have HM : IntegralMixedFramedOldHeightQueryBits.callerModulus (packet key i mw r.val t.val)=Nat.fromBitsLE mw+1 := by
    simp only [packet,IntegralMixedFramedOldHeightQueryBits.callerModulus,IntegralMixedFramedOldHeightQueryBits.source,
      IntegralMixedFramedCompanionQueryBits.callerModulus,PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
  unfold IntegralMixedFramedOldHeightQueryBits.value
  rw [HM]
  simp only [packet,IntegralMixedFramedOldHeightQueryBits.Active,
    IntegralMixedFramedOldHeightQueryBits.sourceBirth,IntegralMixedFramedOldHeightQueryBits.key,
    IntegralMixedFramedOldHeightQueryBits.root,IntegralMixedFramedOldHeightQueryBits.source,
    IntegralMixedFramedOldHeightQueryBits.retainedIndex,IntegralMixedFramedOldHeightQueryBits.rowIndex,
    IntegralMixedFramedOldHeightQueryBits.colIndex,IntegralMixedFramedOldHeightQueryBits.sourceRank,
    PaddedIntegralGeneratorSource.base,PaddedIntegralGeneratorSource.row,PaddedIntegralGeneratorSource.col,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,HR,
    Nat.mod_eq_of_lt r.isLt,Nat.mod_eq_of_lt t.isLt]
  by_cases ha : Active P key
  · have HA : IntegralMixedFramedHistoryFamilyBits.prefixLength P key<P.cap (pairFst key) := ha
    rw [ite_eq_left HA,matrix,ite_eq_left ha,←IntegralMixedFramedHistoryFamilyBits.family_birth P D H key,sourceEntry_clamp]
  · have HA : ¬IntegralMixedFramedHistoryFamilyBits.prefixLength P key<P.cap (pairFst key) := ha
    rw [ite_eq_right HA,matrix,ite_eq_right ha,Int.cast_zero]
    exact ArithmeticBits.zero_residueBits _

end LeanCanny.Algebra.IntegralMixedFramedClearedMatrixBits
