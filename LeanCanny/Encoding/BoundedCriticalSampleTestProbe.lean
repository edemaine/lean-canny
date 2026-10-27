/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleTestMoments
public import LeanCanny.Encoding.BoundedCriticalSampleProbeSource
public import LeanCanny.Encoding.BoundedCriticalSampleProbeBounds
public import LeanCanny.Algebra.IntegerPolynomialMatrixSign

/-! # Native determinant probes for arbitrary polynomial test signs -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleTestProbe
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleTestMoments
open scoped Classical

def linearQuery (e : List Bool) : List Bool := pair
  (BoundedCriticalSampleWeightedMoments.original (BoundedCriticalSampleProbeEntries.hashContext (pairFst e))) (pairSnd e)
theorem linearQuery_FP : linearQuery ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP BoundedCriticalSampleProbeEntries.hashContext_FP)
    BoundedCriticalSampleWeightedMoments.original_FP
  exact mem_FP_pair hc pairSnd_mem_FP

noncomputable def linear (P : Readers) (T : Test) (e : List Bool) : ℤ := moment P T (linearQuery e)
theorem linear_evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun e => SignStatisticBits.integerCode (linear P T e)) :=
  (BoundedCriticalSampleTestMoments.evaluator h A ha).precompose linearQuery linearQuery_FP

noncomputable def coefficient (P : Readers) (T : Test) (q : List Bool) : ℤ :=
  if Nat.fromBitsLE (pairSnd q) = 0 then BoundedCriticalSampleProbeEntries.constant P (pairFst q)
  else if Nat.fromBitsLE (pairSnd q) = 1 then linear P T (pairFst q) else 0

attribute [local irreducible] coefficient linear BoundedCriticalSampleProbeEntries.constant

theorem coefficient_evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (coefficient P T q)) := by
  have C := (BoundedCriticalSampleProbeEntries.constant_evaluator h ha).precompose pairFst pairFst_mem_FP
  have L := (linear_evaluator h A ha).precompose pairFst pairFst_mem_FP
  have h0 := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)).flag_mem_FP
  have h1 := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 1)).flag_mem_FP
  have H := SpaceFunction.branch _ h0 C (SpaceFunction.branch _ h1 L
    (SpaceFunction.ofFP _ (constFn_mem_FP (SignStatisticBits.integerCode 0))))
  apply H.congr
  funext q
  simp only [coefficient, Function.comp_apply, decide_eq_true_eq]
  split_ifs <;> rfl

noncomputable def matrix (P : Readers) (T : Test) (z : List Bool) :
    Matrix (Fin (BoundedCriticalSampleProbeEntries.dimension z)) (Fin (BoundedCriticalSampleProbeEntries.dimension z)) ℤ[X] := fun i j =>
  C (BoundedCriticalSampleProbeEntries.constant P (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) +
    C (linear P T (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) * X

theorem coefficient_packet (P : Readers) (T : Test) (z : List Bool)
    (i j : Fin (BoundedCriticalSampleProbeEntries.dimension z)) (k : ℕ) :
    coefficient P T (pair (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (BinaryNatCode.encode k)) =
      (matrix P T z i j).coeff k := by
  simp only [coefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    matrix, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  by_cases h0 : k = 0
  · simp only [h0, one_ne_zero, ite_false, ite_true, mul_zero, add_zero]
  · by_cases h1 : k = 1
    · simp only [h1, one_ne_zero, ite_false, ite_true, mul_one, zero_add]
    · simp only [h0, h1, Ne.symm h1, ite_false, mul_zero, add_zero]

theorem linear_bound (P : Readers) (T : Test) (e : List Bool) :
    (linear P T e).natAbs ≤ 2 ^ BoundedCriticalSampleProbeBounds.bits P (pairFst e) := by
  unfold linear
  have H := moment_bound P T (linearQuery e)
  simp only [linearQuery, pairFst_pair] at H
  exact H.trans (Nat.pow_le_pow_right (by decide)
    (by unfold BoundedCriticalSampleProbeBounds.bits BoundedCriticalSamplePencilBounds.bits; omega))

theorem entry_mass (P : Readers) (T : Test) (z : List Bool) (i j : Fin (BoundedCriticalSampleProbeEntries.dimension z)) :
    coefficientMass (matrix P T z i j) ≤ 2 ^ (BoundedCriticalSampleProbeBounds.bits P z + 1) := by
  let e := pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hc := BoundedCriticalSampleProbeBounds.constant_bound P e
  have hl := linear_bound P T e
  have he : pairFst e = z := pairFst_pair _ _
  rw [he] at hc hl
  have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
  change coefficientMass (C (BoundedCriticalSampleProbeEntries.constant P e) + C (linear P T e) * X) ≤ _
  calc
    _ ≤ coefficientMass (C (BoundedCriticalSampleProbeEntries.constant P e)) + coefficientMass (C (linear P T e) * X) := coefficientMass_add_le _ _
    _ ≤ coefficientMass (C (BoundedCriticalSampleProbeEntries.constant P e)) + coefficientMass (C (linear P T e)) * coefficientMass X :=
      Nat.add_le_add_left (coefficientMass_mul_le _ _) _
    _ = (BoundedCriticalSampleProbeEntries.constant P e).natAbs + (linear P T e).natAbs := by
      rw [coefficientMass_C, coefficientMass_C, hx, Nat.mul_one]
    _ ≤ 2 ^ BoundedCriticalSampleProbeBounds.bits P z + 2 ^ BoundedCriticalSampleProbeBounds.bits P z := Nat.add_le_add hc hl
    _ = 2 ^ (BoundedCriticalSampleProbeBounds.bits P z + 1) := by rw [pow_succ]; omega

theorem determinant_bits (P : Readers) (T : Test) (z : List Bool) (k : ℕ) :
    ((matrix P T z).det.coeff k).natAbs.size ≤ BoundedCriticalSampleProbeBounds.budget P z := by
  have hd := det_coefficientMass_le_pow (matrix P T z) (BoundedCriticalSampleProbeBounds.bits P z + 1) (entry_mass P T z)
  have hs := Nat.size_le_size ((coeff_natAbs_le_coefficientMass (matrix P T z).det k).trans hd)
  simpa only [Fintype.card_fin, Nat.size_pow, BoundedCriticalSampleProbeBounds.budget, CharacteristicIntegerBounds.budget] using hs

noncomputable def family (P : Readers) (T : Test) : IntegerPolynomialMatrixBits.Family where
  dimension := BoundedCriticalSampleProbeEntries.dimension
  matrix := matrix P T

theorem code_correct (P : Readers) (T : Test) : IntegerPolynomialMatrixBits.EntryCorrect (family P T)
    (fun q => SignStatisticBits.integerCode (coefficient P T q)) := by
  intro z i j k
  exact congrArg SignStatisticBits.integerCode (coefficient_packet P T z i j k)

noncomputable def firstCoefficient (P : Readers) (T : Test) (z : List Bool) : ℤ := (matrix P T z).det.coeff 1
theorem sign_evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun z => InfinitesimalSign.encode (SignType.sign (firstCoefficient P T z))) :=
  IntegerPolynomialMatrixBits.firstSign_evaluator (family P T) (coefficient_evaluator h A ha)
    (code_correct P T) BoundedCriticalSampleProbeEntries.dimension_binary (BoundedCriticalSampleProbeBounds.budget P)
    (BoundedCriticalSampleProbeBounds.budget_binary h) (fun z => determinant_bits P T z 1)

end LeanCanny.Encoding.BoundedCriticalSampleTestProbe
