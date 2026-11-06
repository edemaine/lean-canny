/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalSource
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
public import LeanCanny.Algebra.IntegerParameterCoefficientSpace
/-! # The actual principal cut polynomial retains radius and all center variables -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialPrincipalRadiusSource
open LeanCanny.Connectivity LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] LeanCanny.Encoding.FormulaSignSlotSource.dimension
  LeanCanny.Encoding.FormulaSignSlotMargin.initialDimension
  LeanCanny.Encoding.FormulaSignSlotMargin.initialPolynomial

def family (c : List Bool) := pairFst c
def order (c : List Bool) := Nat.fromBitsLE (pairSnd c)
noncomputable def arity (c : List Bool) := FormulaSignSlotRadialCenterPrincipalFamily.arity (family c)
noncomputable def width (c : List Bool) := FormulaSignSlotRadialCenterPrincipalFamily.width (family c)
noncomputable def degree (c : List Bool) := FormulaSignSlotRadialCenterPrincipalFamily.degreeBound (family c)
noncomputable def mass (c : List Bool) := FormulaSignSlotRadialCenterPrincipalMass.budget (family c)
noncomputable def polynomial (c : List Bool) : MvPolynomial (Fin (arity c)) ℤ := FormulaSignSlotRadialCenterPrincipalFamily.principal (family c) (order c)

theorem arity_unary : UnaryFn arity := FormulaSignSlotRadialCenterPrincipalFamily.arity_unary.comp pairFst_mem_FP
theorem width_unary : UnaryFn width := FormulaSignSlotRadialCenterPrincipalFamily.width_unary.comp pairFst_mem_FP
theorem degree_binary : BinaryFn degree := FormulaSignSlotRadialCenterPrincipalFamily.degreeBound_binary.comp pairFst_mem_FP
theorem mass_binary : BinaryFn mass := FormulaSignSlotRadialCenterPrincipalMass.budget_binary.comp pairFst_mem_FP

theorem degree_fit (c : List Bool) : degree c < 2 ^ width c := by
  exact (Nat.le_add_right _ _).trans_lt (Nat.lt_size_self _)

theorem polynomial_degree (c:List Bool):(polynomial c).totalDegree≤degree c:=
  FormulaSignSlotRadialCenterPrincipalFamily.principal_degree (family c) (order c)
theorem polynomial_mass (c:List Bool):MvMass.mass (polynomial c)≤2^mass c:=
  FormulaSignSlotRadialCenterPrincipalMass.mass (family c) (order c)
attribute [local irreducible] FormulaSignSlotRadialCenterPrincipalFamily.principal
  FormulaSignSlotRadialCenterPrincipalFamily.width FormulaSignSlotRadialCenterPrincipalFamily.degreeBound

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

noncomputable def coefficient := FormulaSignSlotRadialCenterPrincipalSource.coefficient ∘ query
theorem evaluator : SpaceFunction coefficient := FormulaSignSlotRadialCenterPrincipalSource.evaluator.precompose query query_FP

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

private noncomputable def center_entry (c:List Bool) (j r:ℕ) (bits modulus:List Bool):=
  residueBits (((FormulaSignSlotRadialCenterPrincipalCoefficient.polynomial c j r).coeff
    (nativeExponent (Equiv.refl _) (FormulaSignSlotRadialCenterPrincipalFamily.width c)
      (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1))
private theorem center_entry_value (c:List Bool) (j r:ℕ) (bits modulus:List Bool):
    center_entry c j r bits modulus=residueBits
      (((FormulaSignSlotRadialCenterPrincipalFamily.principal c j).coeff
        ((nativeExponent (Equiv.refl _) (FormulaSignSlotRadialCenterPrincipalFamily.width c)
          (Nat.fromBitsLE bits)).cons r):ℤ):ZMod (Nat.fromBitsLE modulus+1)):=
  congrArg (fun a:ℤ=>residueBits (a:ZMod (Nat.fromBitsLE modulus+1)))
    (FormulaSignSlotRadialCenterPrincipalCoefficient.coefficient c j r _)
private theorem source_entry_value (z bits modulus:List Bool):
    residueBits (((FormulaSignSlotRadialCenterPrincipalSource.polynomial z).coeff
      (nativeExponent (Equiv.refl (Fin (FormulaSignSlotRadialCenterPrincipalSource.arity z)))
        (FormulaSignSlotRadialCenterPrincipalSource.width z) (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1))=
    center_entry (pairFst z) (FormulaSignSlotRadialCenterPrincipalSource.order z)
      (FormulaSignSlotRadialCenterPrincipalSource.radius z) bits modulus:=rfl
attribute [local irreducible] center_entry

private theorem original_entry (c j r bits modulus : List Bool) :
    FormulaSignSlotRadialCenterPrincipalSource.coefficient
      (pair (pair (pair c (pair j r)) bits) modulus) =
    residueBits (((FormulaSignSlotRadialCenterPrincipalFamily.principal c (Nat.fromBitsLE j)).coeff
      ((nativeExponent (Equiv.refl _) (FormulaSignSlotRadialCenterPrincipalFamily.width c)
        (Nat.fromBitsLE bits)).cons (Nat.fromBitsLE r)) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  have H := (FormulaSignSlotRadialCenterPrincipalSource.packet (pair c (pair j r)) bits modulus).trans
    (source_entry_value (pair c (pair j r)) bits modulus)
  simp only [FormulaSignSlotRadialCenterPrincipalSource.order,FormulaSignSlotRadialCenterPrincipalSource.radius,
    pairFst_pair,pairSnd_pair] at H
  exact H.trans (center_entry_value c (Nat.fromBitsLE j) (Nat.fromBitsLE r) bits modulus)

theorem packet (c bits modulus : List Bool) : coefficient (pair (pair c bits) modulus) =
    residueBits (((polynomial c).coeff (nativeExponent (Equiv.refl _) (width c)
      (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  let z := pair (pair c bits) modulus
  have HQ :query z=pair (pair (pair (family c) (pair (pairSnd c) (radiusBits z))) (centerBits z)) modulus:=by
    simp only [query,z,context,RationalSubstitution.IntegerBits.context,pairFst_pair,pairSnd_pair]
  rw [coefficient,Function.comp_apply,HQ,original_entry]
  have HE := joined_exponent queryWidth target
    (d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original (family c)))) z
  have HX :
      (nativeExponent (Equiv.refl (Fin (d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original (family c))))))
        (width c) (Nat.fromBitsLE (centerBits z))).cons (Nat.fromBitsLE (radiusBits z))=
      nativeExponent (Equiv.refl (Fin (d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original (family c)))+1)))
        (width c) (Nat.fromBitsLE bits):=by
    simpa only [queryWidth,radiusBits,centerBits,target,context,z,RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair] using HE
  exact congrArg (fun a : ℤ => residueBits (a : ZMod (Nat.fromBitsLE modulus + 1)))
    (congrArg (polynomial c).coeff HX)

noncomputable def source : IntegralFramedBankPolynomialModel.Source where
  arity := arity
  width := width
  degree := degree
  mass := mass
  polynomial := polynomial
  fit c i := (MvPolynomial.degreeOf_le_totalDegree (polynomial c) i).trans_lt
    ((polynomial_degree c).trans_lt (degree_fit c))
  polynomial_degree := polynomial_degree
  polynomial_mass := polynomial_mass

noncomputable def access : IntegralFramedBankPolynomialModel.Access source where
  arity := arity_unary
  width := width_unary
  degree := degree_binary
  mass := mass_binary
  coefficient := coefficient
  evaluator := evaluator
  packet := packet

end LeanCanny.Encoding.FormulaSignSlotRadialPrincipalRadiusSource
