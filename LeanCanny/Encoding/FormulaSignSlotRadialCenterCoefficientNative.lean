/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficient
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantSpace
public import LeanCanny.Algebra.FixedWidthParameterCons
/-! # A closed native reader for the actual retained-center coefficients

Context is the original eliminant context paired with three binary indices.
Every caller modulus is retained. Oversized indices return the actual zero
polynomial rather than wrapping into the coefficient box.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficientNative
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotRadialEliminantPackingLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant
  FormulaSignSlotRadialEliminantPacked.eliminant FormulaSignSlotRadialEliminantParameterRows.eliminant
  FormulaSignSlotRadialCenterCoefficient.polynomial FormulaSignSlotRadialEliminantSpace.value

def origin (q : List Bool) := pairFst (RationalSubstitution.IntegerBits.context q)
def indices (q : List Bool) := pairSnd (RationalSubstitution.IntegerBits.context q)
def slot (i : ℕ) (q : List Bool) := WordList.get (indices q) i
def selected (i : ℕ) (q : List Bool) := Nat.fromBitsLE (slot i q)
noncomputable def arity (q : List Bool) := d (pairFst (origin q))
noncomputable def width (q : List Bool) := parameterWidth (origin q)
def target (q : List Bool) := RationalSubstitution.IntegerBits.selectedDegree q

theorem origin_FP : origin ∈ FP := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP
theorem indices_FP : indices ∈ FP := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP
theorem slot_FP (i : ℕ) : slot i ∈ FP := by
  apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair indices_FP
    (constFn_mem_FP (BinaryNatCode.encode i))) WordList.reader_FP)
  intro q
  simp only [Function.comp_apply, slot, WordList.reader_packet]

theorem selected_binary (i : ℕ) : BinaryFn (selected i) := BinaryFn.fromBits (slot_FP i)
theorem arity_unary : UnaryFn arity :=
  FormulaSignSlotSource.dimension_unary.comp (mem_FP_comp origin_FP pairFst_mem_FP)
theorem width_unary : UnaryFn width := parameterWidth_unary.comp origin_FP
theorem target_FP : target ∈ FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP

noncomputable def centerWord := FixedWidthQuery.repack arity width arity width target
def pack (a w s t r : ℕ) (bits : List Bool) :=
  FixedWidthNatVector.encode 1 w (fun _ => s) ++
    (FixedWidthNatVector.encode 1 w (fun _ => t) ++
      (FixedWidthNatVector.encode 1 w (fun _ => r) ++
        FixedWidthQuery.repack (fun _ => a) (fun _ => w) (fun _ => a) (fun _ => w) (fun _ => bits) []))
noncomputable def word (q : List Bool) :=
  pack (arity q) (width q) (selected 0 q) (selected 1 q) (selected 2 q) (target q)
noncomputable def query (q : List Bool) := pair (pair (origin q) (word q)) (pairSnd q)

theorem centerWord_FP : centerWord ∈ FP :=
  FixedWidthQuery.repack_mem_FP arity_unary width_unary arity_unary width_unary target_FP

private theorem repack_at (A W : List Bool → ℕ) (target : List Bool → List Bool) (q : List Bool) :
    FixedWidthQuery.repack A W A W target q =
      FixedWidthQuery.repack (fun _ => A q) (fun _ => W q) (fun _ => A q) (fun _ => W q)
        (fun _ => target q) [] := by
  unfold FixedWidthQuery.repack
  apply congrArg (FixedWidthNatVector.encode (A q) (W q))
  funext i
  rfl

theorem word_FP : word ∈ FP := by
  apply mem_FP_of_eq (FixedWidthParameterConsBits.prepend_FP _ _ _ width_unary (selected_binary 0)
    (FixedWidthParameterConsBits.prepend_FP _ _ _ width_unary (selected_binary 1)
      (FixedWidthParameterConsBits.prepend_FP _ _ _ width_unary (selected_binary 2) centerWord_FP)))
  intro q
  dsimp only [word, pack, FixedWidthParameterConsBits.prepend, centerWord]
  rw [repack_at arity width target q]
theorem query_FP : query ∈ FP := mem_FP_pair (mem_FP_pair origin_FP word_FP) pairSnd_mem_FP

noncomputable def Fits (q : List Bool) := selected 0 q < 2 ^ width q ∧
  selected 1 q < 2 ^ width q ∧ selected 2 q < 2 ^ width q
theorem fits_FP : FPPred Fits :=
  ((selected_binary 0).lt ((BinaryFn.const 2).powUnary width_unary)).and
    (((selected_binary 1).lt ((BinaryFn.const 2).powUnary width_unary)).and
      ((selected_binary 2).lt ((BinaryFn.const 2).powUnary width_unary)))

noncomputable def value (q : List Bool) : List Bool :=
  if Fits q then FormulaSignSlotRadialEliminantSpace.value (query q) else []

theorem evaluator : SpaceFunction value := by
  have E := SpaceFunction.branch (fun q => decide (Fits q)) fits_FP.flag_mem_FP
    (FormulaSignSlotRadialEliminantSpace.evaluator.precompose query query_FP)
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun q => by
    by_cases h : Fits q <;> simp only [Function.comp_apply, value, h, decide_true, decide_false, ite_true, ite_false,
      Bool.false_eq_true])

private theorem prepend_three (a w s t r : ℕ) (bits : List Bool)
    (hs : s < 2 ^ w) (ht : t < 2 ^ w) (hr : r < 2 ^ w) :
    nativeExponent (Equiv.refl (Fin (a + 3))) w (Nat.fromBitsLE
      (FixedWidthNatVector.encode 1 w (fun _ => s) ++
        (FixedWidthNatVector.encode 1 w (fun _ => t) ++
          (FixedWidthNatVector.encode 1 w (fun _ => r) ++ bits)))) =
      TriplePolynomialParameterFlatten.exponent s t r
        (nativeExponent (Equiv.refl (Fin a)) w (Nat.fromBitsLE bits)) := by
  rw [FixedWidthParameterConsBits.nativeExponent_prepend (a + 2) w s _ hs,
    FixedWidthParameterConsBits.nativeExponent_prepend (a + 1) w t _ ht,
    FixedWidthParameterConsBits.nativeExponent_prepend a w r _ hr]
  rfl

private theorem repack_same (a w : ℕ) (bits : List Bool) :
    nativeExponent (Equiv.refl (Fin a)) w (Nat.fromBitsLE
      (FixedWidthQuery.repack (fun _ => a) (fun _ => w) (fun _ => a) (fun _ => w) (fun _ => bits) [])) =
        nativeExponent (Equiv.refl (Fin a)) w (Nat.fromBitsLE bits) :=
  nativeExponent_repack (Equiv.refl (Fin a)) (fun _ => w) (fun _ => w) (fun _ => bits) [] le_rfl

private theorem pack_exponent (a w s t r : ℕ) (bits : List Bool)
    (hs : s < 2 ^ w) (ht : t < 2 ^ w) (hr : r < 2 ^ w) :
    nativeExponent (Equiv.refl (Fin (a + 3))) w (Nat.fromBitsLE (pack a w s t r bits)) =
      TriplePolynomialParameterFlatten.exponent s t r
        (nativeExponent (Equiv.refl (Fin a)) w (Nat.fromBitsLE bits)) := by
  rw [pack, prepend_three _ _ _ _ _ _ hs ht hr, repack_same]

private theorem word_exponent (q : List Bool) (h : Fits q) :
    nativeExponent (Equiv.refl (Fin (arity q + 3))) (width q) (Nat.fromBitsLE (word q)) =
      TriplePolynomialParameterFlatten.exponent (selected 0 q) (selected 1 q) (selected 2 q)
        (nativeExponent (Equiv.refl (Fin (arity q))) (width q) (Nat.fromBitsLE (target q))) := by
  exact pack_exponent _ _ _ _ _ _ h.1 h.2.1 h.2.2

private theorem read_value (c bits modulus : List Bool) :
    FormulaSignSlotRadialEliminantSpace.value (pair (pair c bits) modulus) =
      residueBits (((FormulaSignSlotRadialEliminantPacked.eliminant c).coeff (Nat.fromBitsLE bits) : ℤ) :
        ZMod (Nat.fromBitsLE modulus + 1)) := by
  unfold FormulaSignSlotRadialEliminantSpace.value PrimitivePairBits.coefficient
  simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
    RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair]
  rfl

theorem correct (q : List Bool) : value q = residueBits
    ((((FormulaSignSlotRadialCenterCoefficient.polynomial (origin q)
      (selected 0 q) (selected 1 q) (selected 2 q)).coeff
        (nativeExponent (Equiv.refl (Fin (arity q))) (width q) (Nat.fromBitsLE (target q)))) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  by_cases h : Fits q
  · have HL : (word q).length = (arity q + 3) * width q := by
      simp only [word, pack, List.length_append,
        FixedWidthNatVector.length_encode, FixedWidthQuery.repack_length]
      ring
    have HK : Nat.fromBitsLE (word q) < FormulaSignSlotRadialEliminantPacked.parameterBox (origin q) := by
      have H := Nat.fromBitsLE_lt_pow_length (word q)
      rw [HL] at H
      simpa only [FormulaSignSlotRadialEliminantPacked.parameterBox, count, arity, width, ← pow_mul,
        Nat.mul_comm] using H
    rw [value, ite_eq_left h, query, read_value]
    apply congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    rw [FormulaSignSlotRadialEliminantPacked.eliminant_coefficient (origin q)
      ⟨Nat.fromBitsLE (word q), HK⟩]
    rw [← entry_vector, ← nativeExponent_refl]
    erw [word_exponent q h]
    rw [FormulaSignSlotRadialEliminantParameterRows.eliminant,
      TriplePolynomialParameterFlatten.coefficient]
    rw [FormulaSignSlotRadialCenterCoefficient.polynomial]
  · have HF := FormulaSignSlotRadialEliminantPacked.result_fit (origin q)
    have HZ : FormulaSignSlotRadialCenterCoefficient.polynomial (origin q)
        (selected 0 q) (selected 1 q) (selected 2 q) = 0 := by
      apply FormulaSignSlotRadialCenterCoefficient.zero_of_large_index
      change ¬(selected 0 q < 2 ^ width q ∧ selected 1 q < 2 ^ width q ∧
        selected 2 q < 2 ^ width q) at h
      change FormulaSignSlotRadialEliminantPacked.resultDegree (origin q) < 2 ^ width q at HF
      omega
    rw [value, ite_eq_right h, HZ]
    rfl

end LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficientNative
