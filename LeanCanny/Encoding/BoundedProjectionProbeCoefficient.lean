/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionProbeBounds
public import LeanCanny.Algebra.IntegerPolynomialMatrixSpace
public import LeanCanny.Algebra.IntegerSignumSpace
public import LeanCanny.Algebra.InfinitesimalSignSpace

/-! # Native coefficients and signs of pointwise signature probes

The first determinant coefficient is read modulo arbitrary positive moduli.
Its binary bit budget and the existing CRT sign evaluator produce a sign
tag without materializing the potentially exponential-length coefficient.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionProbeCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open MatrixPower
open scoped Classical

noncomputable def family (P : Readers) (unit : Bool) : IntegerPolynomialMatrixBits.Family where
  dimension := BoundedProjectionProbeEntries.dimension
  matrix := BoundedProjectionProbeEntries.matrix P unit

noncomputable def code (P : Readers) (unit : Bool) (q : List Bool) : List Bool :=
  SignStatisticBits.integerCode (BoundedProjectionProbeEntries.coefficient P unit q)

theorem code_correct (P : Readers) (unit : Bool) : IntegerPolynomialMatrixBits.EntryCorrect (family P unit) (code P unit) := by
  intro z i j d
  apply congrArg SignStatisticBits.integerCode
  exact BoundedProjectionProbeEntries.coefficient_packet P unit z i j d

noncomputable def value (P : Readers) (unit : Bool) : List Bool → List Bool := IntegerPolynomialMatrixBits.value (family P unit)
theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (unit : Bool) : SpaceFunction (value P unit) :=
  IntegerPolynomialMatrixBits.evaluator (family P unit) (BoundedProjectionProbeEntries.evaluator h ha unit)
    (code_correct P unit) BoundedProjectionProbeEntries.dimension_binary

theorem value_packet (P : Readers) (unit : Bool) (z : List Bool) (k : ℕ) (m : List Bool) :
    value P unit (pair (pair z (BinaryNatCode.encode k)) m) =
      residueBits ((((BoundedProjectionProbeEntries.matrix P unit z).det.coeff k : ℤ)) : ZMod (Nat.fromBitsLE m + 1)) :=
  IntegerPolynomialMatrixBits.value_packet (family P unit) z k m

def firstQuery (q : List Bool) : List Bool := pair (pair (pairFst q) (BinaryNatCode.encode 1)) (pairSnd q)
theorem firstQuery_FP : firstQuery ∈ FP := mem_FP_pair (mem_FP_pair pairFst_mem_FP (constFn_mem_FP _)) pairSnd_mem_FP

noncomputable def firstCoefficient (P : Readers) (unit : Bool) (z : List Bool) : ℤ :=
  (BoundedProjectionProbeEntries.matrix P unit z).det.coeff 1
noncomputable def residue (P : Readers) (unit : Bool) : List Bool → List Bool := value P unit ∘ firstQuery
theorem residue_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (unit : Bool) : SpaceFunction (residue P unit) :=
  (evaluator h ha unit).precompose firstQuery firstQuery_FP

theorem residue_packet (P : Readers) (unit : Bool) (z m : List Bool) :
    residue P unit (pair z m) = residueBits ((firstCoefficient P unit z : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  rw [residue, Function.comp_apply, firstQuery, pairFst_pair, pairSnd_pair, value_packet]
  rfl

attribute [local irreducible] firstCoefficient residue value

theorem sign_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (unit : Bool) :
    SpaceFunction (fun z => InfinitesimalSign.encode (SignType.sign (firstCoefficient P unit z))) := by
  have hb := BinaryFn.bits_mem_FP (BoundedProjectionProbeBounds.budget_binary h)
  have E := IntegerSignumBits.evaluator (residue_evaluator h ha unit)
    (fun z => BinaryNatCode.encode (BoundedProjectionProbeBounds.budget P z)) hb (firstCoefficient P unit)
    (by
      intro z
      rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      unfold firstCoefficient
      exact BoundedProjectionProbeBounds.determinant_bits P unit z 1)
    (by
      intro z m hm
      generalize hw : BinaryNatCode.encode (m - 1) = w
      have he : Nat.fromBitsLE w + 1 = m := by
        rw [← hw]
        simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
        omega
      subst m
      exact residue_packet P unit z w)
  exact E.congr (funext fun z => InfinitesimalSign.tag_eq_encode (firstCoefficient P unit z))

end LeanCanny.Encoding.BoundedProjectionProbeCoefficient
