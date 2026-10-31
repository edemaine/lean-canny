/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralEulerRequerySpace
public import LeanCanny.Algebra.IntegralBerkowitzBlockSource

/-! # Original-reader access to every actual critical lower coefficient

The reduction-reader protocol carries the saved source, both old basis
indices, a critical row, and a spatial exponent. Binary normalization of
indices is total; the specification covers every valid row and old basis
pair and every spatial rank. All four original reader costs are charged.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralEulerLowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralEulerBits
open IntegralBerkowitzBlockBits (original basisRowCode basisColCode)
set_option backward.isDefEq.respectTransparency false

def target (q : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairSnd q))
theorem target_binary : BinaryFn target := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

def row (S : Source) (q : List Bool) : Fin (S.rank (original q)) :=
  ⟨Nat.fromBitsLE (basisRowCode q) % S.rank (original q), Nat.mod_lt _
    ((Nat.zero_le (S.row (original q)).val).trans_lt (S.row (original q)).isLt)⟩
def col (S : Source) (q : List Bool) : Fin (S.rank (original q)) :=
  ⟨Nat.fromBitsLE (basisColCode q) % S.rank (original q), Nat.mod_lt _
    ((Nat.zero_le (S.col (original q)).val).trans_lt (S.col (original q)).isLt)⟩
def selected (S : Source) (q : List Bool) : Fin (S.free (original q)) :=
  ⟨Nat.fromBitsLE (pairFst (pairSnd q)) % S.free (original q), Nat.mod_lt _ (S.free_pos (original q))⟩

theorem row_binary (S : Source) (a : Access S) : BinaryFn (fun q => (row S q).val) := by
  have HR : BinaryFn (fun q => S.rank (original q)) := a.rank.comp IntegralBerkowitzBlockBits.original_FP
  exact (BinaryFn.fromBits IntegralBerkowitzBlockBits.basisRowCode_FP).mod HR

theorem col_binary (S : Source) (a : Access S) : BinaryFn (fun q => (col S q).val) := by
  have HR : BinaryFn (fun q => S.rank (original q)) := a.rank.comp IntegralBerkowitzBlockBits.original_FP
  exact (BinaryFn.fromBits IntegralBerkowitzBlockBits.basisColCode_FP).mod HR

theorem selected_binary (S : Source) (a : Access S) : BinaryFn (fun q => (selected S q).val) := by
  have HF : BinaryFn (fun q => S.free (original q)) := (BinaryFn.ofUnary a.free).comp IntegralBerkowitzBlockBits.original_FP
  exact (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)).mod HF

noncomputable def value (S : Source) : List Bool → List Bool :=
  (S.requery original target (row S) (col S)).lowerValue (selected S)

theorem evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) (EA : SpaceFunction a.leading) :
    SpaceFunction (value S) :=
  requery_lower_evaluator S a original target (row S) (col S) (selected S)
    IntegralBerkowitzBlockBits.original_FP target_binary (row_binary S a) (col_binary S a)
    (selected_binary S a) EC EH EQ EA

theorem packet (S : Source) (c : List Bool) (i : Fin (S.free c)) (k : ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    value S (pair (IntegralBlockMomentBits.context c r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) =
      residueBits ((Algebra.leftMulMatrix (S.basis c) ((S.lowerPolynomial c i).coeff
        (RationalSubstitution.Indexed.exponentVector (S.free c) (FixedWidthPolynomial.entry (S.targetWidth c) k)))
        r t : ℤ) : ZMod (S.modulus c)) := by
  generalize hz : pair (IntegralBlockMomentBits.context c r.val t.val)
    (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k)) = q
  have HO : original q = c := by
    rw [← hz]
    simp only [original, IntegralBlockMomentBits.context, pairFst_pair]
  have HR : Nat.fromBitsLE (basisRowCode q) = r.val := by
    rw [← hz]
    simp only [basisRowCode, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HT : Nat.fromBitsLE (basisColCode q) = t.val := by
    rw [← hz]
    simp only [basisColCode, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HI : Nat.fromBitsLE (pairFst (pairSnd q)) = i.val := by
    rw [← hz, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HK : target q = k := by
    rw [← hz, target, pairSnd_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst c
  let := S.ring (original q)
  let := (S.requery original target (row S) (col S)).ring q
  have RR : row S q = r := by
    apply Fin.ext
    change Nat.fromBitsLE (basisRowCode q) % S.rank (original q) = r.val
    rw [HR, Nat.mod_eq_of_lt r.isLt]
  have RT : col S q = t := by
    apply Fin.ext
    change Nat.fromBitsLE (basisColCode q) % S.rank (original q) = t.val
    rw [HT, Nat.mod_eq_of_lt t.isLt]
  have RI : selected S q = i := by
    apply Fin.ext
    change Nat.fromBitsLE (pairFst (pairSnd q)) % S.free (original q) = i.val
    rw [HI, Nat.mod_eq_of_lt i.isLt]
  change residueBits ((Algebra.leftMulMatrix (S.basis (original q))
    (((S.requery original target (row S) (col S)).lowerPolynomial q (selected S q)).coeff
      (RationalSubstitution.Indexed.exponentVector (S.free (original q))
        (FixedWidthPolynomial.entry (S.targetWidth (original q)) (target q))))
      (row S q) (col S q) : ℤ) : ZMod (S.modulus (original q))) = _
  rw [requery_lower_polynomial, RR, RT, RI, HK]
  rfl

end LeanCanny.Algebra.IntegralEulerLowBits
