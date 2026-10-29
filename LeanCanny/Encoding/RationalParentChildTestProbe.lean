/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildTestMoments
public import LeanCanny.Encoding.RationalParentChildProbeSource
public import LeanCanny.Encoding.RationalParentChildProbeBounds
public import LeanCanny.Algebra.IntegerPolynomialMatrixSign

/-! # Native determinant probes for arbitrary polynomial test signs -/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildTestProbe
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open RationalParentChildTestMoments
open RationalParentChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildRecords.length RationalParentChildThom.labelWidth
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildQueries.roots RationalParentChildRegularCount.count

def linearQuery (e : List Bool) : List Bool := pair
  (RationalParentChildWeightedMoments.original (RationalParentChildProbeEntries.hashContext (pairFst e))) (pairSnd e)
theorem linearQuery_FP : linearQuery ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP RationalParentChildProbeEntries.hashContext_FP)
    RationalParentChildWeightedMoments.original_FP
  exact mem_FP_pair hc pairSnd_mem_FP

noncomputable def linear (P : Inputs) (T : Test) (e : List Bool) : ℤ := moment P T (linearQuery e)
theorem linear_evaluator {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) :
    SpaceFunction (fun e => SignStatisticBits.integerCode (linear P T e)) :=
  (RationalParentChildTestMoments.evaluator h A).precompose linearQuery linearQuery_FP

noncomputable def coefficient (P : Inputs) (T : Test) (q : List Bool) : ℤ :=
  if Nat.fromBitsLE (pairSnd q) = 0 then RationalParentChildProbeEntries.constant P (pairFst q)
  else if Nat.fromBitsLE (pairSnd q) = 1 then linear P T (pairFst q) else 0

attribute [local irreducible] coefficient linear RationalParentChildProbeEntries.constant

theorem coefficient_evaluator {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (coefficient P T q)) := by
  have C := (RationalParentChildProbeEntries.constant_evaluator h).precompose pairFst pairFst_mem_FP
  have L := (linear_evaluator h A).precompose pairFst pairFst_mem_FP
  have h0 := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)).flag_mem_FP
  have h1 := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 1)).flag_mem_FP
  have H := SpaceFunction.branch _ h0 C (SpaceFunction.branch _ h1 L
    (SpaceFunction.ofFP _ (constFn_mem_FP (SignStatisticBits.integerCode 0))))
  apply H.congr
  funext q
  simp only [coefficient, Function.comp_apply, decide_eq_true_eq]
  split_ifs <;> rfl

noncomputable def matrix (P : Inputs) (T : Test) (z : List Bool) :
    Matrix (Fin (RationalParentChildProbeEntries.dimension z)) (Fin (RationalParentChildProbeEntries.dimension z)) ℤ[X] := fun i j =>
  C (RationalParentChildProbeEntries.constant P (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) +
    C (linear P T (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) * X

theorem coefficient_packet (P : Inputs) (T : Test) (z : List Bool)
    (i j : Fin (RationalParentChildProbeEntries.dimension z)) (k : ℕ) :
    coefficient P T (pair (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (BinaryNatCode.encode k)) =
      (matrix P T z i j).coeff k := by
  simp only [coefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    matrix, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  by_cases h0 : k = 0
  · simp only [h0, one_ne_zero, ite_false, ite_true, mul_zero, add_zero]
  · by_cases h1 : k = 1
    · simp only [h1, one_ne_zero, ite_false, ite_true, mul_one, zero_add]
    · simp only [h0, h1, Ne.symm h1, ite_false, mul_zero, add_zero]

theorem linear_bound (P : Inputs) (T : Test) (e : List Bool) :
    (linear P T e).natAbs ≤ 2 ^ RationalParentChildProbeBounds.bits P (pairFst e) := by
  unfold linear
  have H := moment_bound P T (linearQuery e)
  simp only [linearQuery, pairFst_pair] at H
  exact H.trans (Nat.pow_le_pow_right (by decide)
    (by unfold RationalParentChildProbeBounds.bits RationalParentChildPencilBounds.bits; omega))

theorem entry_mass (P : Inputs) (T : Test) (z : List Bool) (i j : Fin (RationalParentChildProbeEntries.dimension z)) :
    coefficientMass (matrix P T z i j) ≤ 2 ^ (RationalParentChildProbeBounds.bits P z + 1) := by
  let e := pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hc := RationalParentChildProbeBounds.constant_bound P e
  have hl := linear_bound P T e
  have he : pairFst e = z := pairFst_pair _ _
  rw [he] at hc hl
  have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
  change coefficientMass (C (RationalParentChildProbeEntries.constant P e) + C (linear P T e) * X) ≤ _
  calc
    _ ≤ coefficientMass (C (RationalParentChildProbeEntries.constant P e)) + coefficientMass (C (linear P T e) * X) := coefficientMass_add_le _ _
    _ ≤ coefficientMass (C (RationalParentChildProbeEntries.constant P e)) + coefficientMass (C (linear P T e)) * coefficientMass X :=
      Nat.add_le_add_left (coefficientMass_mul_le _ _) _
    _ = (RationalParentChildProbeEntries.constant P e).natAbs + (linear P T e).natAbs := by
      rw [coefficientMass_C, coefficientMass_C, hx, Nat.mul_one]
    _ ≤ 2 ^ RationalParentChildProbeBounds.bits P z + 2 ^ RationalParentChildProbeBounds.bits P z := Nat.add_le_add hc hl
    _ = 2 ^ (RationalParentChildProbeBounds.bits P z + 1) := by rw [pow_succ]; omega

theorem determinant_bits (P : Inputs) (T : Test) (z : List Bool) (k : ℕ) :
    ((matrix P T z).det.coeff k).natAbs.size ≤ RationalParentChildProbeBounds.budget P z := by
  have hd := det_coefficientMass_le_pow (matrix P T z) (RationalParentChildProbeBounds.bits P z + 1) (entry_mass P T z)
  have hs := Nat.size_le_size ((coeff_natAbs_le_coefficientMass (matrix P T z).det k).trans hd)
  simpa only [Fintype.card_fin, Nat.size_pow, RationalParentChildProbeBounds.budget, CharacteristicIntegerBounds.budget] using hs

noncomputable def family (P : Inputs) (T : Test) : IntegerPolynomialMatrixBits.Family where
  dimension := RationalParentChildProbeEntries.dimension
  matrix := matrix P T

theorem code_correct (P : Inputs) (T : Test) : IntegerPolynomialMatrixBits.EntryCorrect (family P T)
    (fun q => SignStatisticBits.integerCode (coefficient P T q)) := by
  intro z i j k
  exact congrArg SignStatisticBits.integerCode (coefficient_packet P T z i j k)

noncomputable def firstCoefficient (P : Inputs) (T : Test) (z : List Bool) : ℤ := (matrix P T z).det.coeff 1
theorem sign_evaluator {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) :
    SpaceFunction (fun z => InfinitesimalSign.encode (SignType.sign (firstCoefficient P T z))) :=
  IntegerPolynomialMatrixBits.firstSign_evaluator (family P T) (coefficient_evaluator h A)
    (code_correct P T) RationalParentChildProbeEntries.dimension_binary (RationalParentChildProbeBounds.budget P)
    (RationalParentChildProbeBounds.budget_binary h) (fun z => determinant_bits P T z 1)

end LeanCanny.Encoding.RationalParentChildTestProbe
