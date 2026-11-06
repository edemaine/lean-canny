/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueSource
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
public import LeanCanny.Algebra.IntegerParameterCoefficientSpace
/-! # The actual value cut polynomial retains radius and all center variables -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialValueRadiusSource
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] LeanCanny.Encoding.FormulaSignSlotSource.dimension
  LeanCanny.Encoding.FormulaSignSlotMargin.initialDimension
  LeanCanny.Encoding.FormulaSignSlotMargin.initialPolynomial

def family (c : List Bool) := pairFst c
def order (c : List Bool) := Nat.fromBitsLE (pairSnd c)
noncomputable def arity (c : List Bool) := FormulaSignSlotRadialCenterValuePacking.arity (family c)
noncomputable def width (c : List Bool) := FormulaSignSlotRadialCenterValuePacking.width (family c)
noncomputable def degree (c : List Bool) := FormulaSignSlotRadialCenterValuePacking.degree (family c)
noncomputable def mass (c : List Bool) := FormulaSignSlotRadialCenterValueMass.budget (family c)
noncomputable def polynomial (c : List Bool) := TriplePolynomialParameterFlatten.one
  ((FormulaSignSlotRadialCenterValuePacking.source (family c)).coeff (order c))

theorem arity_unary : UnaryFn arity := FormulaSignSlotRadialCenterValuePacking.arity_unary.comp pairFst_mem_FP
theorem width_unary : UnaryFn width := FormulaSignSlotRadialCenterValuePacking.width_unary.comp pairFst_mem_FP
theorem degree_binary : BinaryFn degree := FormulaSignSlotRadialCenterValuePacking.degree_binary.comp pairFst_mem_FP
theorem mass_binary : BinaryFn mass := FormulaSignSlotRadialCenterValueMass.budget_binary.comp pairFst_mem_FP

theorem degree_fit (c : List Bool) : degree c < 2 ^ width c := by
  exact FormulaSignSlotRadialCenterValuePacking.degree_fit (family c)

def context := RationalSubstitution.IntegerBits.context
def target := RationalSubstitution.IntegerBits.selectedDegree
noncomputable def queryWidth (z : List Bool) := width (context z)
noncomputable def radiusBits (z : List Bool) := IntegerParameterCoefficientBits.parameter queryWidth target z
noncomputable def centerBits (z : List Bool) := IntegerParameterCoefficientBits.spatial queryWidth target z

noncomputable def query (z : List Bool) := pair (pair
  (pair (family (context z)) (pair (pairSnd (context z)) (radiusBits z))) (centerBits z)) (pairSnd z)

theorem query_FP : query ∈ FP := by
  have HC : context ∈ FP := RationalSubstitution.IntegerBits.context_mem_FP
  have HT : target ∈ FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have HW : UnaryFn queryWidth := width_unary.comp HC
  have HR := IntegerParameterCoefficientBits.parameter_mem_FP queryWidth target HW HT
  have HS := IntegerParameterCoefficientBits.spatial_mem_FP queryWidth target HW HT
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair (mem_FP_comp HC pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp HC pairSnd_mem_FP) HR)) HS) pairSnd_mem_FP

noncomputable def coefficient := FormulaSignSlotRadialCenterValueSource.coefficient ∘ query
theorem evaluator : SpaceFunction coefficient := FormulaSignSlotRadialCenterValueSource.evaluator.precompose query query_FP

private theorem joined_exponent (W : List Bool → ℕ) (t : List Bool → List Bool) (n : ℕ) (q : List Bool) :
    (nativeExponent (Equiv.refl (Fin n)) (W q)
      (Nat.fromBitsLE (IntegerParameterCoefficientBits.spatial W t q))).cons
        (Nat.fromBitsLE (IntegerParameterCoefficientBits.parameter W t q)) =
      nativeExponent (Equiv.refl (Fin (n+1))) (W q) (Nat.fromBitsLE (t q)) := by
  rw [← IntegerParameterCoefficientBits.tail_nativeExponent,
    ← IntegerParameterCoefficientBits.parameter_nativeExponent W t n q]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Finsupp.cons_zero]
  · rw [Finsupp.cons_succ]
    rfl

attribute [local irreducible] FormulaSignSlotRadialCenterValuePacking.source
  FormulaSignSlotRadialCenterValuePacking.degree FormulaSignSlotRadialCenterValuePacking.width
  FormulaSignSlotRadialCenterValueCoefficient.polynomial
  FormulaSignSlotRadialCenterValueLayout.original

private noncomputable def center_entry (c:List Bool) (j r:ℕ) (bits modulus:List Bool):List Bool:=
  residueBits (((FormulaSignSlotRadialCenterValueCoefficient.polynomial c j r).coeff
    (nativeExponent (Equiv.refl (Fin (d (FormulaSignSlotRadialCenterValueLayout.original c))))
      (FormulaSignSlotRadialCenterValuePacking.width c) (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1))

private theorem source_entry_value (z bits modulus:List Bool):
    residueBits (((FormulaSignSlotRadialCenterValueSource.polynomial z).coeff
      (nativeExponent (Equiv.refl (Fin (FormulaSignSlotRadialCenterValueSource.arity z)))
        (FormulaSignSlotRadialCenterValueSource.width z) (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1))=
      center_entry (pairFst z) (FormulaSignSlotRadialCenterValueSource.order z)
        (FormulaSignSlotRadialCenterValueSource.radius z) bits modulus:=rfl

private theorem center_entry_value (c:List Bool) (j r:ℕ) (bits modulus:List Bool):
    center_entry c j r bits modulus=residueBits (((TriplePolynomialParameterFlatten.one
      ((FormulaSignSlotRadialCenterValuePacking.source c).coeff j)).coeff
        ((nativeExponent (Equiv.refl (Fin (d (FormulaSignSlotRadialCenterValueLayout.original c))))
          (FormulaSignSlotRadialCenterValuePacking.width c) (Nat.fromBitsLE bits)).cons r):ℤ):
            ZMod (Nat.fromBitsLE modulus+1)):=by
  exact congrArg (fun a:ℤ=>residueBits (a:ZMod (Nat.fromBitsLE modulus+1)))
    (FormulaSignSlotRadialCenterValueCoefficient.coefficient c j r _)

attribute [local irreducible] center_entry

private theorem original_entry (c j r bits modulus : List Bool) :
    FormulaSignSlotRadialCenterValueSource.coefficient
      (pair (pair (pair c (pair j r)) bits) modulus) =
    residueBits (((TriplePolynomialParameterFlatten.one
      ((FormulaSignSlotRadialCenterValuePacking.source c).coeff (Nat.fromBitsLE j))).coeff
      ((nativeExponent (Equiv.refl _) (FormulaSignSlotRadialCenterValuePacking.width c)
        (Nat.fromBitsLE bits)).cons (Nat.fromBitsLE r)) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  have H:=(FormulaSignSlotRadialCenterValueSource.packet (pair c (pair j r)) bits modulus).trans
    (source_entry_value (pair c (pair j r)) bits modulus)
  simp only [FormulaSignSlotRadialCenterValueSource.order,FormulaSignSlotRadialCenterValueSource.radius,
    pairFst_pair,pairSnd_pair] at H
  exact H.trans (center_entry_value c (Nat.fromBitsLE j) (Nat.fromBitsLE r) bits modulus)

private theorem query_packet (c bits modulus:List Bool):
    query (pair (pair c bits) modulus)=pair (pair
      (pair (family c) (pair (pairSnd c) (radiusBits (pair (pair c bits) modulus))))
        (centerBits (pair (pair c bits) modulus))) modulus:=by
  simp only [query,context,RationalSubstitution.IntegerBits.context,pairFst_pair,pairSnd_pair]

theorem packet (c bits modulus : List Bool) : coefficient (pair (pair c bits) modulus) =
    residueBits (((polynomial c).coeff (nativeExponent (Equiv.refl _) (width c)
      (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  let z := pair (pair c bits) modulus
  rw [coefficient,Function.comp_apply,query_packet,original_entry]
  have HE := joined_exponent queryWidth target
    (d (FormulaSignSlotRadialCenterValueLayout.original (family c))) z
  have HW:queryWidth z=width c:=by
    simp only [queryWidth,context,RationalSubstitution.IntegerBits.context,z,pairFst_pair]
  have HT:target z=bits:=by
    simp only [target,RationalSubstitution.IntegerBits.selectedDegree,z,pairFst_pair,pairSnd_pair]
  have HX:(nativeExponent (Equiv.refl (Fin (d (FormulaSignSlotRadialCenterValueLayout.original (family c)))))
      (width c) (Nat.fromBitsLE (centerBits z))).cons (Nat.fromBitsLE (radiusBits z))=
        nativeExponent (Equiv.refl (Fin (arity c))) (width c) (Nat.fromBitsLE bits):=by
    simpa only [arity,FormulaSignSlotRadialCenterValuePacking.arity,centerBits,radiusBits,HW,HT] using HE
  exact congrArg (fun a : ℤ => residueBits (a : ZMod (Nat.fromBitsLE modulus + 1)))
    (congrArg (polynomial c).coeff HX)

noncomputable def source : IntegralFramedBankPolynomialModel.Source where
  arity := arity
  width := width
  degree := degree
  mass := mass
  polynomial := polynomial
  fit c i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((FormulaSignSlotRadialCenterValuePacking.source_degree (family c) (order c)).trans_lt
      (FormulaSignSlotRadialCenterValuePacking.degree_fit (family c)))
  polynomial_degree c := FormulaSignSlotRadialCenterValuePacking.source_degree (family c) (order c)
  polynomial_mass c := FormulaSignSlotRadialCenterValueMass.mass (family c) (order c)

noncomputable def access : IntegralFramedBankPolynomialModel.Access source where
  arity := arity_unary
  width := width_unary
  degree := degree_binary
  mass := mass_binary
  coefficient := coefficient
  evaluator := evaluator
  packet := packet

end LeanCanny.Encoding.FormulaSignSlotRadialValueRadiusSource
