/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberProbeBounds
public import LeanCanny.Algebra.IntegerPolynomialMatrixSpace
public import LeanCanny.Algebra.IntegerSignumSpace
public import LeanCanny.Algebra.InfinitesimalSignSpace

/-! # Native coefficients and signs of pointwise signature probes

The first determinant coefficient is read modulo arbitrary positive moduli.
Its binary bit budget and the existing CRT sign evaluator produce a sign
tag without materializing the potentially exponential-length coefficient.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberProbeCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open MatrixPower
open scoped Classical

noncomputable def family (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) : IntegerPolynomialMatrixBits.Family where
  dimension := BoundedAlgebraicFiberProbeEntries.dimension
  matrix := BoundedAlgebraicFiberProbeEntries.matrix P F unit

noncomputable def code (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (q : List Bool) : List Bool :=
  SignStatisticBits.integerCode (BoundedAlgebraicFiberProbeEntries.coefficient P F unit q)

theorem code_correct (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) : IntegerPolynomialMatrixBits.EntryCorrect (family P F unit) (code P F unit) := by
  intro z i j d
  apply congrArg SignStatisticBits.integerCode
  exact BoundedAlgebraicFiberProbeEntries.coefficient_packet P F unit z i j d

noncomputable def value (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) : List Bool → List Bool := IntegerPolynomialMatrixBits.value (family P F unit)
theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (unit : Bool) : SpaceFunction (value P F unit) :=
  IntegerPolynomialMatrixBits.evaluator (family P F unit) (BoundedAlgebraicFiberProbeEntries.evaluator h A ha unit)
    (code_correct P F unit) BoundedAlgebraicFiberProbeEntries.dimension_binary

theorem value_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (z : List Bool) (k : ℕ) (m : List Bool) :
    value P F unit (pair (pair z (BinaryNatCode.encode k)) m) =
      residueBits ((((BoundedAlgebraicFiberProbeEntries.matrix P F unit z).det.coeff k : ℤ)) : ZMod (Nat.fromBitsLE m + 1)) :=
  IntegerPolynomialMatrixBits.value_packet (family P F unit) z k m

def firstQuery (q : List Bool) : List Bool := pair (pair (pairFst q) (BinaryNatCode.encode 1)) (pairSnd q)
theorem firstQuery_FP : firstQuery ∈ FP := mem_FP_pair (mem_FP_pair pairFst_mem_FP (constFn_mem_FP _)) pairSnd_mem_FP

noncomputable def firstCoefficient (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (z : List Bool) : ℤ :=
  (BoundedAlgebraicFiberProbeEntries.matrix P F unit z).det.coeff 1
noncomputable def residue (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) : List Bool → List Bool := value P F unit ∘ firstQuery
theorem residue_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (unit : Bool) : SpaceFunction (residue P F unit) :=
  (evaluator h A ha unit).precompose firstQuery firstQuery_FP

theorem residue_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (z m : List Bool) :
    residue P F unit (pair z m) = residueBits ((firstCoefficient P F unit z : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  rw [residue, Function.comp_apply, firstQuery, pairFst_pair, pairSnd_pair, value_packet]
  rfl

attribute [local irreducible] firstCoefficient residue value

theorem sign_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (unit : Bool) :
    SpaceFunction (fun z => InfinitesimalSign.encode (SignType.sign (firstCoefficient P F unit z))) := by
  have hb := BinaryFn.bits_mem_FP (BoundedAlgebraicFiberProbeBounds.budget_binary A)
  have E := IntegerSignumBits.evaluator (residue_evaluator h A ha unit)
    (fun z => BinaryNatCode.encode (BoundedAlgebraicFiberProbeBounds.budget F z)) hb (firstCoefficient P F unit)
    (by
      intro z
      rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      unfold firstCoefficient
      exact BoundedAlgebraicFiberProbeBounds.determinant_bits P F unit z 1)
    (by
      intro z m hm
      generalize hw : BinaryNatCode.encode (m - 1) = w
      have he : Nat.fromBitsLE w + 1 = m := by
        rw [← hw]
        simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
        omega
      subst m
      exact residue_packet P F unit z w)
  exact E.congr (funext fun z => InfinitesimalSign.tag_eq_encode (firstCoefficient P F unit z))

end LeanCanny.Encoding.BoundedAlgebraicFiberProbeCoefficient
