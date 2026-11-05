/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutPacked
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutCoefficient
/-! # Closed arbitrary-modulus coefficients of the actual branch-cut center coefficients -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutCoefficientNative
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialCenterBranchCutFamily.polynomial
  FormulaSignSlotRadialCenterBranchCutCoefficient.polynomial

def context := RationalSubstitution.IntegerBits.context
def origin (q : List Bool) := pairFst (context q)
def order (q : List Bool) := Nat.fromBitsLE (pairFst (pairSnd (context q)))
def radius (q : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd (context q)))
def target := RationalSubstitution.IntegerBits.selectedDegree
noncomputable def centers (q : List Bool) := d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original (origin q)))
noncomputable def width (q : List Bool) := FormulaSignSlotRadialCenterBranchCutFamily.width (origin q)
noncomputable def centerWord := FixedWidthQuery.repack centers width centers width target
noncomputable def word := FixedWidthParameterConsBits.prepend width radius centerWord
noncomputable def query (q : List Bool) := pair (pair (pair (origin q) (BinaryNatCode.encode (order q))) (word q)) (pairSnd q)

theorem context_FP : context ∈ FP := RationalSubstitution.IntegerBits.context_mem_FP
theorem origin_FP : origin ∈ FP := mem_FP_comp context_FP pairFst_mem_FP
theorem order_binary : BinaryFn order := BinaryFn.fromBits
  (mem_FP_comp (mem_FP_comp context_FP pairSnd_mem_FP) pairFst_mem_FP)
theorem radius_binary : BinaryFn radius := BinaryFn.fromBits
  (mem_FP_comp (mem_FP_comp context_FP pairSnd_mem_FP) pairSnd_mem_FP)
theorem target_FP : target ∈ FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP
theorem centers_unary : UnaryFn centers := FormulaSignSlotSource.dimension_unary.comp
  (mem_FP_comp (mem_FP_comp origin_FP FormulaSignSlotRadialCenterPrincipalFamily.original_FP) pairFst_mem_FP)
theorem width_unary : UnaryFn width := FormulaSignSlotRadialCenterBranchCutFamily.width_unary.comp origin_FP
theorem centerWord_FP : centerWord ∈ FP := FixedWidthQuery.repack_mem_FP
  centers_unary width_unary centers_unary width_unary target_FP
theorem word_FP : word ∈ FP := FixedWidthParameterConsBits.prepend_FP _ _ _ width_unary radius_binary centerWord_FP
theorem query_FP : query ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_pair origin_FP order_binary.bits_mem_FP) word_FP) pairSnd_mem_FP

attribute [local irreducible] FormulaSignSlotRadialCenterBranchCutPacked.encoded
  width PrimitivePairBits.coefficient
  FormulaSignSlotRadialCenterBranchCutPacked.polynomial FormulaSignSlotRadialCenterBranchCutFamily.width

noncomputable def Fits (q : List Bool) := radius q < 2 ^ width q
theorem fits_FP : FPPred Fits := radius_binary.lt ((BinaryFn.const 2).powUnary width_unary)
noncomputable def value (q : List Bool) := if Fits q then
  PrimitivePairBits.coefficient FormulaSignSlotRadialCenterBranchCutPacked.polynomial (query q) else []
theorem evaluator : SpaceFunction value := by
  have E := SpaceFunction.branch (fun q => decide (Fits q)) fits_FP.flag_mem_FP
    (FormulaSignSlotRadialCenterBranchCutPacked.evaluator.precompose query query_FP)
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

private theorem word_length (q : List Bool) : (word q).length = (centers q + 1) * width q := by
  simp only [word, FixedWidthParameterConsBits.prepend, List.length_append,
    FixedWidthNatVector.length_encode, centerWord, FixedWidthQuery.repack_length]
  ring

private theorem word_fit (q : List Bool) : Nat.fromBitsLE (word q) < count (centers q + 1) (width q) := by
  have H := Nat.fromBitsLE_lt_pow_length (word q)
  rw [word_length] at H
  simpa only [count, ← pow_mul, Nat.mul_comm] using H

private theorem repack_dynamic (A W : List Bool → ℕ) (bits : List Bool → List Bool) (q : List Bool) :
    nativeExponent (Equiv.refl (Fin (A q))) (W q)
      (Nat.fromBitsLE (FixedWidthQuery.repack A W A W bits q)) =
        nativeExponent (Equiv.refl (Fin (A q))) (W q) (Nat.fromBitsLE (bits q)) := by
  have H := nativeExponent_repack (Equiv.refl (Fin (A q))) W W bits q le_rfl
  have HR : FixedWidthQuery.repack A W A W bits q =
      FixedWidthQuery.repack (fun _ => A q) W (fun _ => A q) W bits q := by
    unfold FixedWidthQuery.repack
    apply congrArg (FixedWidthNatVector.encode (A q) (W q))
    funext i
    rfl
  rw [HR]
  exact H

private theorem coefficient_encode (A W : ℕ) (p : MvPolynomial (Fin A) ℤ) (k : ℕ)
    (hk : k < count A W) (hp : p.totalDegree < 2 ^ W) :
    (FixedWidthKronecker.encode A W p).coeff k = p.coeff (nativeExponent (Equiv.refl _) W k) := by
  have H := FixedWidthKronecker.native_coefficient (Equiv.refl _) W p.totalDegree p le_rfl hp k hk
  simpa [FixedWidthKronecker.native] using H

private theorem word_exponent (q : List Bool) (h : Fits q) :
    nativeExponent (Equiv.refl (Fin (centers q + 1))) (width q) (Nat.fromBitsLE (word q)) =
      (nativeExponent (Equiv.refl (Fin (centers q))) (width q) (Nat.fromBitsLE (target q))).cons (radius q) := by
  rw [word, FixedWidthParameterConsBits.prepend, FixedWidthParameterConsBits.nativeExponent_prepend _ _ _ _ h]
  apply congrArg (Finsupp.cons (radius q))
  exact repack_dynamic centers width target q

private theorem cut_fit (c : List Bool) (k : ℕ) :
    (FormulaSignSlotRadialCenterBranchCutFamily.polynomial c k).totalDegree <
      2 ^ FormulaSignSlotRadialCenterBranchCutFamily.width c := by
  apply (FormulaSignSlotRadialCenterBranchCutFamily.polynomial_degree c k).trans_lt
  unfold FormulaSignSlotRadialCenterBranchCutFamily.width
  exact Nat.lt_size_self _

private theorem packed_packet (c modulus target : List Bool) (k : ℕ) :
    PrimitivePairBits.coefficient FormulaSignSlotRadialCenterBranchCutPacked.polynomial
      (pair (pair (pair c (BinaryNatCode.encode k)) target) modulus) = residueBits
        (((FixedWidthKronecker.encode (FormulaSignSlotRadialCenterPrincipalFamily.arity c)
          (FormulaSignSlotRadialCenterBranchCutFamily.width c)
          (FormulaSignSlotRadialCenterBranchCutFamily.polynomial c k)).coeff (Nat.fromBitsLE target) : ℤ) :
            ZMod (Nat.fromBitsLE modulus + 1)) := by
  unfold PrimitivePairBits.coefficient RationalSubstitution.IntegerBits.coefficientResidue
  apply congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m))
  · simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
      pairFst_pair, pairSnd_pair]
    unfold FormulaSignSlotRadialCenterBranchCutPacked.polynomial FormulaSignSlotRadialCenterBranchCutPacked.order
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    unfold FormulaSignSlotRadialCenterBranchCutPacked.encoded
    rfl
  · simp only [RationalSubstitution.IntegerBits.mValue, pairSnd_pair]

private theorem query_value (q : List Bool) :
    PrimitivePairBits.coefficient FormulaSignSlotRadialCenterBranchCutPacked.polynomial (query q) =
      residueBits ((((FormulaSignSlotRadialCenterBranchCutFamily.polynomial (origin q) (order q)).coeff
        (nativeExponent (Equiv.refl _) (width q) (Nat.fromBitsLE (word q)))) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  rw [query, packed_packet]
  apply congrArg (fun a : ℤ => residueBits (a : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
  unfold width
  apply coefficient_encode
  · simpa only [centers, width, FormulaSignSlotRadialCenterPrincipalFamily.arity] using word_fit q
  · exact cut_fit (origin q) (order q)

theorem correct (q : List Bool) : value q = residueBits
    ((((FormulaSignSlotRadialCenterBranchCutCoefficient.polynomial (origin q) (order q) (radius q)).coeff
      (nativeExponent (Equiv.refl (Fin (centers q))) (width q) (Nat.fromBitsLE (target q)))) : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  by_cases h : Fits q
  · rw [value, ite_eq_left h, query_value]
    erw [word_exponent q h, ← FormulaSignSlotRadialCenterBranchCutCoefficient.coefficient]
  · have HZ : FormulaSignSlotRadialCenterBranchCutCoefficient.polynomial (origin q) (order q) (radius q) = 0 := by
      unfold FormulaSignSlotRadialCenterBranchCutCoefficient.polynomial
      apply MvTwoParameterCoefficient.one_eq_zero
      have HR : 2 ^ FormulaSignSlotRadialCenterBranchCutFamily.width (origin q) ≤ radius q := by
        have HH : ¬radius q < 2 ^ width q := h
        unfold width at HH
        exact Nat.le_of_not_gt HH
      exact (cut_fit (origin q) (order q)).trans_le HR
    rw [value, ite_eq_right h, HZ]
    rfl

private noncomputable def entry (c : List Bool) (j r W : ℕ) (bits modulus : List Bool) := residueBits
  ((((FormulaSignSlotRadialCenterBranchCutCoefficient.polynomial c j r).coeff
    (nativeExponent (Equiv.refl (Fin (d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original c)))))
      W (Nat.fromBitsLE bits))) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1))
private theorem correct_entry (q : List Bool) : value q = entry (origin q) (order q) (radius q)
    (width q) (target q) (pairSnd q) := correct q
attribute [local irreducible] entry

theorem packet (z bits modulus : List Bool) : value (pair (pair z bits) modulus) = residueBits
    ((((FormulaSignSlotRadialCenterBranchCutCoefficient.polynomial (pairFst z)
      (Nat.fromBitsLE (pairFst (pairSnd z))) (Nat.fromBitsLE (pairSnd (pairSnd z)))).coeff
        (nativeExponent (Equiv.refl (Fin (d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original (pairFst z))))))
          (FormulaSignSlotRadialCenterBranchCutFamily.width (pairFst z)) (Nat.fromBitsLE bits))) : ℤ) :
            ZMod (Nat.fromBitsLE modulus + 1)) := by
  rw [correct_entry]
  simp only [origin, order, radius, width, context, target, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair]
  unfold entry
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutCoefficientNative
