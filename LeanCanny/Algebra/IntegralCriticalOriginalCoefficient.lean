/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalScriptQuery
public import LeanCanny.Algebra.IntegralClearedCoefficientSource

/-! # Original integer coefficient leaves for critical histories

The primitive leaf reads the original integer spatial coefficient modulo
the caller modulus. Its actual multiplication matrix is diagonal, so
basis indices need no algebraic history query. The wrapper accepts either
an FP or a polynomial-space certificate for the original coefficient leaf.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalOriginalCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScriptQueryBits
set_option backward.isDefEq.respectTransparency false

def original (p : List Bool) : List Bool := pairFst (pairFst p)
def rowWord (p : List Bool) : List Bool := pairFst (pairSnd (pairFst p))
def colWord (p : List Bool) : List Bool := pairSnd (pairSnd (pairFst p))
def scalarQuery (p : List Bool) : List Bool := pair (original p) (pairSnd p)

theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem rowWord_FP : rowWord ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem colWord_FP : colWord ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem scalarQuery_FP : scalarQuery ∈ FP := mem_FP_pair original_FP pairSnd_mem_FP

def sameIndex (p : List Bool) : Prop := Nat.fromBitsLE (rowWord p) = Nat.fromBitsLE (colWord p)
instance (p : List Bool) : Decidable (sameIndex p) := inferInstanceAs (Decidable (_ = _))

theorem sameIndex_FP : FPPred sameIndex :=
  (BinaryFn.fromBits rowWord_FP).eq (BinaryFn.fromBits colWord_FP)

def reader (scalar : List Bool → List Bool) (p : List Bool) : List Bool :=
  if sameIndex p then scalar (scalarQuery p) else []

theorem reader_FP (scalar : List Bool → List Bool) (hs : scalar ∈ FP) : reader scalar ∈ FP :=
  sameIndex_FP.ite_mem_FP (mem_FP_comp scalarQuery_FP hs) (constFn_mem_FP [])

theorem reader_space (scalar : List Bool → List Bool) (hs : SpaceFunction scalar) : SpaceFunction (reader scalar) :=
  (SpaceFunction.branch (fun p => decide (sameIndex p)) sameIndex_FP.flag_mem_FP
    (hs.precompose scalarQuery scalarQuery_FP) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext (fun p => by simp only [reader, decide_eq_true_eq, Function.comp_apply]))

noncomputable def coefficient (F : Families) (c : List Bool) (k : ℕ) : ℤ :=
  ((F c).data []).low.coeff
    (RationalSubstitution.Indexed.exponentVector ((F c).ambient [] + 1)
      (FixedWidthPolynomial.entry ((F c).sourceWidth []) k))

theorem reader_packet (F : Families) (q : Queries F) (scalar : List Bool → List Bool)
    (hs : ∀ c k, scalar (pair c (BinaryNatCode.encode k)) =
      residueBits (coefficient F c k : ZMod (q.modulus c)))
    (c : List Bool) (k : ℕ) (r t : Fin (count ((F c).birth []) ((F c).width []))) :
    reader scalar (pair (IntegralClearedCoefficientBits.context c r.val t.val) (BinaryNatCode.encode k)) =
      letI := (IntegralHistoryCriticalBits.original (family F q)).ring c
      residueBits ((Algebra.leftMulMatrix ((IntegralHistoryCriticalBits.original (family F q)).basis c)
        (((IntegralHistoryCriticalBits.original (family F q)).polynomial c).coeff
          (RationalSubstitution.Indexed.exponentVector ((F c).ambient [] + 1)
            (FixedWidthPolynomial.entry ((F c).sourceWidth []) k))) r t : ℤ) : ZMod (q.modulus c)) := by
  rw [original_coefficient_matrix]
  simp only [reader, sameIndex, rowWord, colWord, scalarQuery, original,
    IntegralClearedCoefficientBits.context, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  by_cases h : r = t
  · subst t
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact hs c k
  · rw [ite_eq_right (fun he => h (Fin.ext he)), ite_eq_right h]
    simpa only [ArithmeticBits.zero, Int.cast_zero] using (ArithmeticBits.zero_residueBits (q.modulus c))

end LeanCanny.Algebra.IntegralCriticalOriginalCoefficientBits
