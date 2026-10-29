/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourcePositive
public import LeanCanny.Encoding.FlatFullSourceRowCoefficientCorrect
public import LeanCanny.Algebra.FixedWidthBlockRenameSpace

/-! # Native coefficients of the positive-dimensional flat system

Original rows are embedded in the old coordinate prefix. A native guard
rejects nonzero dummy exponents in those rows. The last row is the dummy
coordinate itself, including when there are no original rows. Raw row and
modulus words are retained, and all direction computation remains charged.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourcePositiveCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatFullSourceTower (Inputs count degree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceTower.system

def query (row target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  pair (pair c (pair (row c) (target c))) (modulus c)

theorem query_FP {row target modulus : List Bool → List Bool}
    (hr : row ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) : query row target modulus ∈ FP :=
  mem_FP_pair (mem_FP_pair id_mem_FP (mem_FP_pair hr ht)) hm

theorem query_packet (F : Inputs) (W : List Bool → ℕ) (row target modulus : List Bool → List Bool)
    (c : List Bool) (i : Fin (count F c)) (hi : Nat.fromBitsLE (row c) = i.val)
    (hW : degree F c < 2 ^ W c) :
    FlatFullSourceRowCoefficient.value F W (query row target modulus c) = MatrixPower.residueBits
      (((FlatFullSourceTower.system F c i).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F c))) (W c)
          (Nat.fromBitsLE (target c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  generalize hq : query row target modulus c = q
  have hc : FlatFullSourceRowQuery.source q = c := by
    rw [← hq, query, FlatFullSourceRowQuery.source, pairFst_pair, pairFst_pair]
  have hr : FlatFullSourceRowQuery.rawRow q = Nat.fromBitsLE (row c) := by
    rw [← hq, query, FlatFullSourceRowQuery.rawRow, FlatFullSourceRowQuery.rowWord,
      pairFst_pair, pairSnd_pair, pairFst_pair]
  have ht : FlatFullSourceRowQuery.target q = target c := by
    rw [← hq, query, FlatFullSourceRowQuery.target, pairFst_pair, pairSnd_pair, pairSnd_pair]
  have hm : FlatFullSourceRowQuery.modulus q = modulus c := by
    rw [← hq, query, FlatFullSourceRowQuery.modulus, pairSnd_pair]
  subst c
  have H := FlatFullSourceRowCoefficient.value_at_row F W q i (hr.trans hi) hW
  rw [ht, hm] at H
  exact H

-- Unlike the stage context, the outer pair here is only a monomial query.
-- The original source context must be restored before calling the row reader.
def restoreQuery (row modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (pair (pairFst z) (pair (row (pairFst z)) (pairSnd z))) (modulus (pairFst z))

theorem restoreQuery_FP {row modulus : List Bool → List Bool} (hr : row ∈ FP) (hm : modulus ∈ FP) :
    restoreQuery row modulus ∈ FP :=
  mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_pair (mem_FP_comp pairFst_mem_FP hr) pairSnd_mem_FP))
    (mem_FP_comp pairFst_mem_FP hm)

noncomputable def reader (F : Inputs) (W : List Bool → ℕ) (row modulus : List Bool → List Bool) :
    List Bool → List Bool := FlatFullSourceRowCoefficient.value F W ∘ restoreQuery row modulus

theorem reader_evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    {row modulus : List Bool → List Bool} (hr : row ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (reader F W row modulus) :=
  (FlatFullSourceRowCoefficient.evaluator h hW).precompose _ (restoreQuery_FP hr hm)

theorem reader_packet (F : Inputs) (W : List Bool → ℕ) (row modulus : List Bool → List Bool)
    (c : List Bool) (i : Fin (count F c)) (hi : Nat.fromBitsLE (row c) = i.val)
    (hW : degree F c < 2 ^ W c) (r : ℕ) : reader F W row modulus (pair c (BinaryNatCode.encode r)) =
      MatrixPower.residueBits (((FlatFullSourceTower.system F c i).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F c))) (W c) r) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  simp only [reader, Function.comp_apply, restoreQuery, pairFst_pair, pairSnd_pair]
  have H := query_packet F W row (fun _ => BinaryNatCode.encode r) modulus c i hi hW
  simpa only [query, MacaulayBits.fromBits_encode] using H

noncomputable def embedded (F : Inputs) (W : List Bool → ℕ) (row target modulus : List Bool → List Bool) :
    List Bool → List Bool :=
  FixedWidthBlockRenameBits.value (count F) (FlatFullSourcePositive.count F) (fun _ => 0) W target
    (reader F W row modulus)

theorem embedded_evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    {row target modulus : List Bool → List Bool} (hr : row ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (embedded F W row target modulus) :=
  FixedWidthBlockRenameBits.evaluator _ _ _ _ _ (reader_evaluator h hW hr hm)
    (FlatFullSourceTower.count_unary h) (FlatFullSourcePositive.count_unary h) (UnaryFn.const 0) hW ht

noncomputable def dummy (F : Inputs) (W : List Bool → ℕ) (target modulus : List Bool → List Bool) :
    List Bool → List Bool :=
  FixedWidthLinearCoefficientBits.value (FlatFullSourcePositive.count F) W (count F) target
    (FlatFullSourceCriticalCoefficient.modulusCode modulus)

theorem dummy_FP {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) : dummy F W target modulus ∈ FP :=
  FixedWidthLinearCoefficientBits.value_FP _ _ _ _ _ (FlatFullSourcePositive.count_unary h) hW
    (BinaryFn.ofUnary (FlatFullSourceTower.count_unary h)) ht (FlatFullSourceCriticalCoefficient.modulusCode_FP hm)

noncomputable def value (F : Inputs) (W : List Bool → ℕ) (row target modulus : List Bool → List Bool)
    (c : List Bool) : List Bool :=
  if Nat.fromBitsLE (row c) = count F c then dummy F W target modulus c
  else if Nat.fromBitsLE (row c) < count F c then embedded F W row target modulus c else []

theorem evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    {row target modulus : List Bool → List Bool} (hr : row ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value F W row target modulus) := by
  have hn := BinaryFn.ofUnary (FlatFullSourceTower.count_unary h)
  have hb := BinaryFn.fromBits hr
  have H := SpaceFunction.branch _ (hb.eq hn).flag_mem_FP (SpaceFunction.ofFP _ (dummy_FP h hW ht hm))
    (SpaceFunction.branch _ (hb.lt hn).flag_mem_FP (embedded_evaluator h hW hr ht hm)
      (SpaceFunction.ofFP _ (constFn_mem_FP [])))
  exact H.congr (funext fun _ => by simp only [value, decide_eq_true_eq])

end LeanCanny.Encoding.FlatFullSourcePositiveCoefficient
