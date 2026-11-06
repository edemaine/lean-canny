/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusHead
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficientNative
public import LeanCanny.Algebra.IntegerParameterCoefficientSpace
/-! # Original-only coefficients of an actual radius head

Perturbation and target degree are datum. The radius exponent is taken
from the queried monomial; every center exponent and caller modulus survive.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadNative
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def origin (q : List Bool) := pairFst (RationalSubstitution.IntegerBits.context q)
def tau (q : List Bool) := pairFst (pairSnd (RationalSubstitution.IntegerBits.context q))
def eta (q : List Bool) := pairSnd (pairSnd (RationalSubstitution.IntegerBits.context q))
def target := RationalSubstitution.IntegerBits.selectedDegree
noncomputable def width (q : List Bool) := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth (origin q)
noncomputable def radius (q : List Bool) := IntegerParameterCoefficientBits.parameter width target q
noncomputable def centers (q : List Bool) := IntegerParameterCoefficientBits.spatial width target q
noncomputable def query (q : List Bool) := pair (pair (pair (origin q) (WordList.encode [tau q,eta q,radius q]))
  (centers q)) (pairSnd q)

theorem origin_FP : origin ∈ FP := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP
theorem tau_FP : tau ∈ FP := mem_FP_comp (f := RationalSubstitution.IntegerBits.context)
  (g := fun z => pairFst (pairSnd z)) RationalSubstitution.IntegerBits.context_mem_FP
  (mem_FP_comp (f := pairSnd) (g := pairFst) pairSnd_mem_FP pairFst_mem_FP)
theorem eta_FP : eta ∈ FP := mem_FP_comp (f := RationalSubstitution.IntegerBits.context)
  (g := fun z => pairSnd (pairSnd z)) RationalSubstitution.IntegerBits.context_mem_FP
  (mem_FP_comp (f := pairSnd) (g := pairSnd) pairSnd_mem_FP pairSnd_mem_FP)
theorem width_unary : UnaryFn width := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth_unary.comp origin_FP
theorem radius_FP : radius ∈ FP := IntegerParameterCoefficientBits.parameter_mem_FP width target width_unary
  RationalSubstitution.IntegerBits.selectedDegree_mem_FP
theorem centers_FP : centers ∈ FP := IntegerParameterCoefficientBits.spatial_mem_FP width target width_unary
  RationalSubstitution.IntegerBits.selectedDegree_mem_FP
theorem query_FP : query ∈ FP := by
  have HI : (fun q => WordList.encode [tau q,eta q,radius q]) ∈ FP :=
    mem_FP_pair tau_FP (mem_FP_pair eta_FP (mem_FP_pair radius_FP (constFn_mem_FP [])))
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair origin_FP HI) centers_FP) pairSnd_mem_FP

noncomputable def value := FormulaSignSlotRadialCenterCoefficientNative.value ∘ query
theorem evaluator : SpaceFunction value := FormulaSignSlotRadialCenterCoefficientNative.evaluator.precompose query query_FP

private theorem coefficient_any (c : List Bool) (s t : ℕ) (f : Fin (d (pairFst c)+1) →₀ ℕ) :
    (FormulaSignSlotRadialRadiusHead.polynomial c s t).coeff f =
      (FormulaSignSlotRadialCenterCoefficient.polynomial c s t (f 0)).coeff f.tail := by
  have HE : f.tail.cons (f 0)=f := Finsupp.cons_tail f
  exact (congrArg (fun e => (FormulaSignSlotRadialRadiusHead.polynomial c s t).coeff e) HE).symm.trans
    (FormulaSignSlotRadialRadiusHead.coefficient c s t _ _)

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
    (((FormulaSignSlotRadialRadiusHead.polynomial (origin q) (Nat.fromBitsLE (tau q)) (Nat.fromBitsLE (eta q))).coeff
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
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadNative
