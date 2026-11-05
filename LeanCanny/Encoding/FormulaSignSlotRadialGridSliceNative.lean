/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialGridSlice
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficientNative
public import LeanCanny.Algebra.IntegerParameterCoefficientSpace
/-! # Original-only coefficients of the actual target/radius grid slice

The perturbation choice is datum. Target and radius exponents are taken
from the queried monomial; every center exponent and caller modulus survive.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialGridSliceNative
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def origin (q : List Bool) := pairFst (RationalSubstitution.IntegerBits.context q)
def tau (q : List Bool) := pairSnd (RationalSubstitution.IntegerBits.context q)
def target := RationalSubstitution.IntegerBits.selectedDegree
noncomputable def width (q : List Bool) := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth (origin q)
noncomputable def eta (q : List Bool) := IntegerParameterCoefficientBits.parameter width target q
noncomputable def rest (q : List Bool) := IntegerParameterCoefficientBits.spatial width target q
noncomputable def radius (q : List Bool) := IntegerParameterCoefficientBits.parameter width rest q
noncomputable def centers (q : List Bool) := IntegerParameterCoefficientBits.spatial width rest q
noncomputable def query (q : List Bool) := pair (pair (pair (origin q) (WordList.encode [tau q,eta q,radius q]))
  (centers q)) (pairSnd q)

theorem origin_FP : origin ∈ FP := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP
theorem tau_FP : tau ∈ FP := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP
theorem width_unary : UnaryFn width := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth_unary.comp origin_FP
theorem eta_FP : eta ∈ FP := IntegerParameterCoefficientBits.parameter_mem_FP width target width_unary
  RationalSubstitution.IntegerBits.selectedDegree_mem_FP
theorem rest_FP : rest ∈ FP := IntegerParameterCoefficientBits.spatial_mem_FP width target width_unary
  RationalSubstitution.IntegerBits.selectedDegree_mem_FP
theorem radius_FP : radius ∈ FP := IntegerParameterCoefficientBits.parameter_mem_FP width rest width_unary rest_FP
theorem centers_FP : centers ∈ FP := IntegerParameterCoefficientBits.spatial_mem_FP width rest width_unary rest_FP
theorem query_FP : query ∈ FP := by
  have HI : (fun q => WordList.encode [tau q,eta q,radius q]) ∈ FP :=
    mem_FP_pair tau_FP (mem_FP_pair eta_FP (mem_FP_pair radius_FP (constFn_mem_FP [])))
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair origin_FP HI) centers_FP) pairSnd_mem_FP

noncomputable def value := FormulaSignSlotRadialCenterCoefficientNative.value ∘ query
theorem evaluator : SpaceFunction value := FormulaSignSlotRadialCenterCoefficientNative.evaluator.precompose query query_FP

private theorem coefficient_any (c : List Bool) (s : ℕ) (f : Fin (d (pairFst c)+2) →₀ ℕ) :
    (FormulaSignSlotRadialGridSlice.polynomial c s).coeff f =
      (FormulaSignSlotRadialCenterCoefficient.polynomial c s (f 0) (f.tail 0)).coeff f.tail.tail := by
  have HE : (f.tail.tail.cons (f.tail 0)).cons (f 0)=f := by rw [Finsupp.cons_tail,Finsupp.cons_tail]
  exact (congrArg (fun e => (FormulaSignSlotRadialGridSlice.polynomial c s).coeff e) HE).symm.trans
    (FormulaSignSlotRadialGridSlice.coefficient c s _ _ _)

private noncomputable def entry (c : List Bool) (s t r : ℕ) (bits modulus : List Bool) :=
  residueBits (((FormulaSignSlotRadialCenterCoefficient.polynomial c s t r).coeff
    (nativeExponent (Equiv.refl (Fin (d (pairFst c))))
      (FormulaSignSlotRadialEliminantPackingLayout.parameterWidth c) (Nat.fromBitsLE bits)) : ℤ) :
        ZMod (Nat.fromBitsLE modulus+1))
private theorem native_entry (q : List Bool) : FormulaSignSlotRadialCenterCoefficientNative.value q =
    entry (FormulaSignSlotRadialCenterCoefficientNative.origin q)
      (FormulaSignSlotRadialCenterCoefficientNative.selected 0 q)
      (FormulaSignSlotRadialCenterCoefficientNative.selected 1 q)
      (FormulaSignSlotRadialCenterCoefficientNative.selected 2 q)
      (FormulaSignSlotRadialCenterCoefficientNative.target q) (pairSnd q) :=
  FormulaSignSlotRadialCenterCoefficientNative.correct q
attribute [local irreducible] entry

private theorem tail_native (n : ℕ) (q : List Bool) (t : List Bool → List Bool) :
    (nativeExponent (Equiv.refl (Fin (n+1))) (width q) (Nat.fromBitsLE (t q))).tail =
      nativeExponent (Equiv.refl (Fin n)) (width q)
        (Nat.fromBitsLE (IntegerParameterCoefficientBits.spatial width t q)) := by
  ext i
  exact congrArg (fun e => e i) (IntegerParameterCoefficientBits.tail_nativeExponent width t n q)

theorem correct (q : List Bool) : value q = residueBits
    (((FormulaSignSlotRadialGridSlice.polynomial (origin q) (Nat.fromBitsLE (tau q))).coeff
      (nativeExponent (Equiv.refl _) (width q) (Nat.fromBitsLE (target q))) : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q)+1)) := by
  rw [value, Function.comp_apply, native_entry]
  simp only [query, FormulaSignSlotRadialCenterCoefficientNative.origin,
    FormulaSignSlotRadialCenterCoefficientNative.selected, FormulaSignSlotRadialCenterCoefficientNative.slot,
    FormulaSignSlotRadialCenterCoefficientNative.indices, FormulaSignSlotRadialCenterCoefficientNative.target,
    RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
    pairFst_pair,pairSnd_pair,WordList.get_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  unfold entry
  rw [coefficient_any, tail_native, IntegerParameterCoefficientBits.parameter_nativeExponent width target]
  rw [show IntegerParameterCoefficientBits.spatial width target q = rest q from rfl]
  rw [IntegerParameterCoefficientBits.parameter_nativeExponent width rest, tail_native]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialGridSliceNative
