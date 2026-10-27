/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberTestMoments
public import LeanCanny.Encoding.BoundedCriticalSampleFiberProbeSource
public import LeanCanny.Algebra.IntegerPolynomialMatrixSign

/-! # Native determinant probes for arbitrary polynomial test signs -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberTestProbe
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleFiberTestMoments
open scoped Classical

def linearQuery (e : List Bool) : List Bool := pair
  (BoundedCriticalSampleFiberWeightedMoments.original (BoundedCriticalSampleFiberProbeEntries.hashContext (pairFst e))) (pairSnd e)
theorem linearQuery_FP : linearQuery ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP BoundedCriticalSampleFiberProbeEntries.hashContext_FP)
    BoundedCriticalSampleFiberWeightedMoments.original_FP
  exact mem_FP_pair hc pairSnd_mem_FP

noncomputable def linear (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (e : List Bool) : ℤ := moment P F G (linearQuery e)
theorem linear_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access) {G : BoundedAlgebraicSlice.Family} (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun e => SignStatisticBits.integerCode (linear P F G e)) :=
  (BoundedCriticalSampleFiberTestMoments.evaluator h A B ha).precompose linearQuery linearQuery_FP

noncomputable def coefficient (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (q : List Bool) : ℤ :=
  if Nat.fromBitsLE (pairSnd q) = 0 then BoundedCriticalSampleFiberProbeEntries.constant P F (pairFst q)
  else if Nat.fromBitsLE (pairSnd q) = 1 then linear P F G (pairFst q) else 0

attribute [local irreducible] coefficient linear BoundedCriticalSampleFiberProbeEntries.constant

theorem coefficient_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access) {G : BoundedAlgebraicSlice.Family} (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (coefficient P F G q)) := by
  have C := (BoundedCriticalSampleFiberProbeEntries.constant_evaluator h A ha).precompose pairFst pairFst_mem_FP
  have L := (linear_evaluator h A B ha).precompose pairFst pairFst_mem_FP
  have h0 := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)).flag_mem_FP
  have h1 := ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 1)).flag_mem_FP
  have H := SpaceFunction.branch _ h0 C (SpaceFunction.branch _ h1 L
    (SpaceFunction.ofFP _ (constFn_mem_FP (SignStatisticBits.integerCode 0))))
  apply H.congr
  funext q
  simp only [coefficient, Function.comp_apply, decide_eq_true_eq]
  split_ifs <;> rfl

noncomputable def matrix (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (z : List Bool) :
    Matrix (Fin (BoundedCriticalSampleFiberProbeEntries.dimension z)) (Fin (BoundedCriticalSampleFiberProbeEntries.dimension z)) ℤ[X] := fun i j =>
  C (BoundedCriticalSampleFiberProbeEntries.constant P F (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) +
    C (linear P F G (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) * X

theorem coefficient_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (z : List Bool)
    (i j : Fin (BoundedCriticalSampleFiberProbeEntries.dimension z)) (k : ℕ) :
    coefficient P F G (pair (pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (BinaryNatCode.encode k)) =
      (matrix P F G z i j).coeff k := by
  simp only [coefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    matrix, coeff_add, coeff_C, coeff_C_mul, coeff_X]
  by_cases h0 : k = 0
  · simp only [h0, one_ne_zero, ite_false, ite_true, mul_zero, add_zero]
  · by_cases h1 : k = 1
    · simp only [h1, one_ne_zero, ite_false, ite_true, mul_one, zero_add]
    · simp only [h0, h1, Ne.symm h1, ite_false, mul_zero, add_zero]

theorem linear_bound (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (e : List Bool) :
    (linear P F G e).natAbs ≤ 2 ^ BoundedCriticalSampleFiberProbeBounds.bits F (pairFst e) := by
  unfold linear
  have H := moment_bound P F G (linearQuery e)
  simp only [linearQuery, pairFst_pair] at H
  exact (H.trans (Nat.lt_size_self _).le).trans (Nat.pow_le_pow_right (by decide)
    (by unfold BoundedCriticalSampleFiberProbeBounds.bits BoundedCriticalSampleFiberPencilBounds.bits; omega))

theorem entry_mass (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (z : List Bool) (i j : Fin (BoundedCriticalSampleFiberProbeEntries.dimension z)) :
    coefficientMass (matrix P F G z i j) ≤ 2 ^ (BoundedCriticalSampleFiberProbeBounds.bits F z + 1) := by
  let e := pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hc := BoundedCriticalSampleFiberProbeBounds.constant_bound P F e
  have hl := linear_bound P F G e
  have he : pairFst e = z := pairFst_pair _ _
  rw [he] at hc hl
  have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
  change coefficientMass (C (BoundedCriticalSampleFiberProbeEntries.constant P F e) + C (linear P F G e) * X) ≤ _
  calc
    _ ≤ coefficientMass (C (BoundedCriticalSampleFiberProbeEntries.constant P F e)) + coefficientMass (C (linear P F G e) * X) := coefficientMass_add_le _ _
    _ ≤ coefficientMass (C (BoundedCriticalSampleFiberProbeEntries.constant P F e)) + coefficientMass (C (linear P F G e)) * coefficientMass X :=
      Nat.add_le_add_left (coefficientMass_mul_le _ _) _
    _ = (BoundedCriticalSampleFiberProbeEntries.constant P F e).natAbs + (linear P F G e).natAbs := by
      rw [coefficientMass_C, coefficientMass_C, hx, Nat.mul_one]
    _ ≤ 2 ^ BoundedCriticalSampleFiberProbeBounds.bits F z + 2 ^ BoundedCriticalSampleFiberProbeBounds.bits F z := Nat.add_le_add hc hl
    _ = 2 ^ (BoundedCriticalSampleFiberProbeBounds.bits F z + 1) := by rw [pow_succ]; omega

theorem determinant_bits (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (z : List Bool) (k : ℕ) :
    ((matrix P F G z).det.coeff k).natAbs.size ≤ BoundedCriticalSampleFiberProbeBounds.budget F z := by
  have hd := det_coefficientMass_le_pow (matrix P F G z) (BoundedCriticalSampleFiberProbeBounds.bits F z + 1) (entry_mass P F G z)
  have hs := Nat.size_le_size ((coeff_natAbs_le_coefficientMass (matrix P F G z).det k).trans hd)
  simpa only [Fintype.card_fin, Nat.size_pow, BoundedCriticalSampleFiberProbeBounds.budget, CharacteristicIntegerBounds.budget] using hs

noncomputable def family (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) : IntegerPolynomialMatrixBits.Family where
  dimension := BoundedCriticalSampleFiberProbeEntries.dimension
  matrix := matrix P F G

theorem code_correct (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) : IntegerPolynomialMatrixBits.EntryCorrect (family P F G)
    (fun q => SignStatisticBits.integerCode (coefficient P F G q)) := by
  intro z i j k
  exact congrArg SignStatisticBits.integerCode (coefficient_packet P F G z i j k)

noncomputable def firstCoefficient (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (z : List Bool) : ℤ := (matrix P F G z).det.coeff 1
theorem sign_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access) {G : BoundedAlgebraicSlice.Family} (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun z => InfinitesimalSign.encode (SignType.sign (firstCoefficient P F G z))) :=
  IntegerPolynomialMatrixBits.firstSign_evaluator (family P F G) (coefficient_evaluator h A B ha)
    (code_correct P F G) BoundedCriticalSampleFiberProbeEntries.dimension_binary (BoundedCriticalSampleFiberProbeBounds.budget F)
    (BoundedCriticalSampleFiberProbeBounds.budget_binary A) (fun z => determinant_bits P F G z 1)

end LeanCanny.Encoding.BoundedCriticalSampleFiberTestProbe
