/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceTarskiPSPACE

/-! # Native scalar tests and squares in algebraic slices

Integer univariate tests lift as parameter-constant bivariate families. A
square is built from the original bivariate reader, with derived degree and
mass bounds. These operations supply the three moments used for root counts.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice
open LeanCanny.Algebra LeanCanny.Computation Polynomial MatrixPower
open BoundedProjectionTestMoments
open scoped Classical

noncomputable def ofTest (T : Test) : Family where
  polynomial c := (T.polynomial c).map (Polynomial.C : ℤ →+* ℤ[X])
  degree := T.degree
  parameterDegree _ := 0
  mass := T.mass
  polynomial_degree c := Polynomial.natDegree_map_le.trans (T.polynomial_degree c)
  coefficient_degree c i := by simp only [Polynomial.coeff_map, Polynomial.natDegree_C, le_refl]
  coefficient_mass c i := by
    rw [Polynomial.coeff_map, coefficientMass_C]
    exact (coeff_natAbs_le_coefficientMass (T.polynomial c) i).trans (T.polynomial_mass c)

def testQuery (z : List Bool) : List Bool := pair
  (pair (pairFst (pairFst z)) (BinaryNat.normalize (pairSnd (pairSnd z))))
  (BinaryNat.normalize (pairSnd (pairFst z)))
theorem testQuery_FP : testQuery ∈ FP := by polytime [testQuery]
def innerZero (z : List Bool) : Prop := Nat.fromBitsLE (pairFst (pairSnd z)) = 0
instance (z : List Bool) : Decidable (innerZero z) := inferInstanceAs (Decidable (_ = _))
theorem innerZero_fppred : FPPred innerZero :=
  (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)).eq (BinaryFn.const 0)

noncomputable def testReader {T : Test} (A : T.Access) : CertifiedPolynomial.BivariateReader (ofTest T).polynomial where
  coefficient z := if innerZero z then A.coefficient (testQuery z) else []
  evaluator := by
    have E := SpaceFunction.branch (fun z => decide (innerZero z)) innerZero_fppred.flag_mem_FP
      (A.evaluator.precompose testQuery testQuery_FP) (SpaceFunction.ofFP _ (constFn_mem_FP []))
    exact E.congr (funext fun z => by simp only [Function.comp_apply, decide_eq_true_eq])
  coefficient_eq q u v := by
    have hi : innerZero (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) ↔ u = 0 := by
      simp only [innerZero, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp only [hi]
    by_cases hu : u = 0
    · rw [ite_eq_left hu]
      simp only [testQuery, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      have H := A.coefficient_eq (pairFst q) v (Nat.fromBitsLE (pairSnd q) + 1) (by omega)
      simp only [Nat.add_sub_cancel] at H
      refine H.trans ?_
      exact congrArg residueBits (by
        simp only [ofTest, Polynomial.coeff_map, Polynomial.coeff_C, hu, ite_true])
    · rw [ite_eq_right hu]
      simp only [ofTest, Polynomial.coeff_map, Polynomial.coeff_C, hu, ite_false, Int.cast_zero]
      simp [residueBits, BinaryNatCode.encode]

noncomputable def ofTestAccess {T : Test} (A : T.Access) : (ofTest T).Access where
  reader := testReader A
  degree_binary := A.degree_binary
  parameterDegree_binary := BinaryFn.const 0
  mass_binary := A.mass_binary

theorem ofTest_slice (T : Test) (c : List Bool) (t : ℝ) :
    (ofTest T).slice c t = (T.polynomial c).map (Int.castRingHom ℝ) := by
  rw [Family.slice, ofTest, Polynomial.map_map]
  congr 1
  ext z
  simp [ParameterTarski.evalHom]

noncomputable def square (F : Family) : Family where
  polynomial c := F.polynomial c ^ 2
  degree c := 2 * F.degree c
  parameterDegree c := 2 * F.parameterDegree c
  mass c := 2 * (F.mass c + (F.degree c + 1).size)
  polynomial_degree c := (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left 2 (F.polynomial_degree c))
  coefficient_degree c i := by
    simpa only [pow_two, two_mul] using PseudoRemainder.mul_parameter_degree (F.polynomial c) (F.polynomial c)
      (F.parameterDegree c) (F.parameterDegree c) (F.coefficient_degree c) (F.coefficient_degree c) i
  coefficient_mass c i := by
    have hm := NestedMass.le_pow (F.polynomial c) (F.degree c) (F.mass c) (F.polynomial_degree c) (F.coefficient_mass c)
    calc
      _ ≤ NestedMass.mass (F.polynomial c ^ 2) := NestedMass.coeff_le _ _
      _ ≤ NestedMass.mass (F.polynomial c) ^ 2 := NestedMass.pow_le _ _
      _ ≤ (2 ^ (F.mass c + (F.degree c + 1).size)) ^ 2 := Nat.pow_le_pow_left hm 2
      _ = _ := by rw [← pow_mul, Nat.mul_comm _ 2]

noncomputable def squareAccess {F : Family} (A : F.Access) : (square F).Access where
  reader := {
    coefficient := (CertifiedPolynomial.BivariateProduct.reader A.reader A.reader).coefficient
    evaluator := (CertifiedPolynomial.BivariateProduct.reader A.reader A.reader).evaluator
    coefficient_eq q u v := by simpa only [square, pow_two] using
      (CertifiedPolynomial.BivariateProduct.reader A.reader A.reader).coefficient_eq q u v }
  degree_binary := (BinaryFn.const 2).mul A.degree_binary
  parameterDegree_binary := (BinaryFn.const 2).mul A.parameterDegree_binary
  mass_binary := (BinaryFn.const 2).mul (A.mass_binary.add ((A.degree_binary.add (BinaryFn.const 1)).size))

theorem square_specialized (P : BoundedFullWriter.Readers) (F : Family) (u : List Bool) :
    specialized P (square F) u = specialized P F u ^ 2 := by
  by_cases hu : u ∈ valid P
  · simp only [specialized, ite_eq_left hu, Family.slice, square, Polynomial.map_pow]
  · simp only [specialized, ite_eq_right hu, zero_pow (by decide : 2 ≠ 0)]

end LeanCanny.Encoding.BoundedAlgebraicSlice
