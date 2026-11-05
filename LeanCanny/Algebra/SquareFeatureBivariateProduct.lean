/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SquareFeaturePackedReader
public import LeanCanny.Algebra.PolynomialBinaryProductSpace
public import LeanCanny.Algebra.BivariateQueryProductSpace
/-! # The actual binary-sized squared-feature product has a streamed reader

The feature variables are packed and the auxiliary product variable remains
outermost. This reuses the existing bivariate finite-product backend.
-/
@[expose] public section
namespace LeanCanny.Algebra.SquareFeatureBivariateProduct
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Polynomial
open SquareFeatureProductFamily
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def box (F : Family) (c : List Bool) := FixedWidthPolynomial.count (F.arity c) (width F c)
noncomputable def factor (F : Family) (c : List Bool) (i : ℕ) : (ℤ[X])[X] :=
  X+C (SquareFeaturePackedReader.packed F (pair c (BinaryNatCode.encode i)) ^ 2)
theorem box_binary (F : Family) (A : Access F) : BinaryFn (box F) := by
  have HB := (BinaryFn.const 2).powUnary (A.arity.mul (width_unary F A))
  exact HB.of_eq (fun c => by simp only [box, FixedWidthPolynomial.count, ←pow_mul, Nat.mul_comm])

theorem factor_degree (F : Family) (c : List Bool) (i : ℕ) : (factor F c i).natDegree ≤ 1 :=
  (natDegree_add_le _ _).trans (max_le (by simp) (by simp))
theorem factor_coefficient_degree (F : Family) (c : List Bool) (i j : ℕ) :
    ((factor F c i).coeff j).natDegree ≤ 2*box F c := by
  have HD := SquareFeaturePackedReader.packed_degree F (pair c (BinaryNatCode.encode i))
  rw [pairFst_pair] at HD
  have HS : (SquareFeaturePackedReader.packed F (pair c (BinaryNatCode.encode i)) ^ 2).natDegree ≤ 2*box F c :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 2 HD)
  by_cases H0 : j=0
  · subst j
    simpa only [factor, coeff_add, coeff_X_zero, coeff_C_zero, zero_add, Nat.mul_comm] using HS
  · by_cases H1 : j=1
    · subst j; simp only [factor, coeff_add, coeff_X_one, coeff_C_succ, add_zero, natDegree_one]; omega
    · have H10 : 1 ≠ j := Ne.symm H1
      simp only [factor, coeff_add, coeff_X, H10, ite_false, coeff_C, H0, ite_false, add_zero, natDegree_zero]
      exact Nat.zero_le _
theorem factor_coefficient_mass (F : Family) (c : List Bool) (i j : ℕ) :
    coefficientMass ((factor F c i).coeff j) ≤ 2^(2*F.mass c) := by
  have HM := SquareFeaturePackedReader.packed_mass F (pair c (BinaryNatCode.encode i))
  rw [pairFst_pair] at HM
  have HS := (coefficientMass_pow_le (SquareFeaturePackedReader.packed F (pair c (BinaryNatCode.encode i))) 2).trans
    (Nat.pow_le_pow_left HM 2)
  have HE : (2^F.mass c)^2 = 2^(2*F.mass c) := by rw [←pow_mul, Nat.mul_comm]
  rw [HE] at HS
  by_cases H0 : j=0
  · subst j
    simpa only [factor, coeff_add, coeff_X_zero, coeff_C_zero, zero_add] using HS
  · by_cases H1 : j=1
    · subst j
      simpa only [factor, coeff_add, coeff_X_one, coeff_C_succ, add_zero, show (1 : ℤ[X]) = C 1 from rfl, coefficientMass_C, Int.natAbs_one] using Nat.one_le_two_pow (n := 2*F.mass c)
    · have H10 : 1 ≠ j := Ne.symm H1
      simp only [factor, coeff_add, coeff_X, H10, ite_false, coeff_C, H0, ite_false, add_zero, coefficientMass_zero]
      exact Nat.zero_le _

noncomputable def family (F : Family) : BivariateQueryProductBits.Family where
  polynomial := factor F
  exponent _ _ := 1
  count := F.count
  degree _ := 1
  parameterDegree c := 2*box F c
  mass c := 2*F.mass c
  polynomial_degree := factor_degree F
  coefficient_degree := factor_coefficient_degree F
  coefficient_mass := factor_coefficient_mass F

def squareQuery (z : List Bool) := pair (pair (BivariateQueryProductBits.origin z)
  (BivariateQueryProductBits.innerWord z)) (BivariateQueryProductBits.modulus z)
theorem squareQuery_FP : squareQuery ∈ FP := mem_FP_pair
  (mem_FP_pair BivariateQueryProductBits.origin_FP BivariateQueryProductBits.innerWord_FP)
  BivariateQueryProductBits.modulus_FP
def oneCode (z : List Bool) := ArithmeticBits.one (BinaryNat.succ (BivariateQueryProductBits.modulus z))
theorem oneCode_FP : oneCode ∈ FP := mem_FP_comp
  (mem_FP_comp (f := BivariateQueryProductBits.modulus) (g := BinaryNat.succ) BivariateQueryProductBits.modulus_FP BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP
noncomputable def coefficient (F : Family) (z : List Bool) :=
  if Nat.fromBitsLE (BivariateQueryProductBits.outerWord z)=0 then
    PrimitivePairBits.coefficient (fun q => SquareFeaturePackedReader.packed F q*SquareFeaturePackedReader.packed F q)
      (squareQuery z)
  else if Nat.fromBitsLE (BivariateQueryProductBits.outerWord z)=1 ∧
      Nat.fromBitsLE (BivariateQueryProductBits.innerWord z)=0 then oneCode z else []

theorem coefficient_evaluator (F : Family) (A : Access F) : SpaceFunction (coefficient F) := by
  have EP := SquareFeaturePackedReader.packed_evaluator F A
  have ES := (PolynomialBinaryProductBits.evaluator _ _ EP EP).precompose squareQuery squareQuery_FP
  have HV := BinaryFn.fromBits BivariateQueryProductBits.outerWord_FP
  have HU := BinaryFn.fromBits BivariateQueryProductBits.innerWord_FP
  have E1 := SpaceFunction.branch (fun z => decide (Nat.fromBitsLE (BivariateQueryProductBits.outerWord z)=1 ∧
      Nat.fromBitsLE (BivariateQueryProductBits.innerWord z)=0))
    ((HV.eq (BinaryFn.const 1)).and (HU.eq (BinaryFn.const 0))).flag_mem_FP
    (SpaceFunction.ofFP oneCode oneCode_FP) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have E0 := SpaceFunction.branch (fun z => decide (Nat.fromBitsLE (BivariateQueryProductBits.outerWord z)=0))
    (HV.eq (BinaryFn.const 0)).flag_mem_FP ES E1
  exact E0.congr (funext fun z => by simp only [coefficient, decide_eq_true_eq, Function.comp_apply])

private noncomputable def packedAt (F : Family) (c : List Bool) (i : ℕ) : ℤ[X] :=
  FixedWidthKronecker.encode (F.arity c) (width F c) (if i<F.count c then F.feature c i else 0)
private theorem packed_at (F : Family) (c : List Bool) (i : ℕ) :
    SquareFeaturePackedReader.packed F (pair c (BinaryNatCode.encode i)) = packedAt F c i := by
  change packedAt F (pairFst (pair c (BinaryNatCode.encode i)))
    (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode i)))) = _
  rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
private theorem packed_canonical (F : Family) (q : List Bool) :
    SquareFeaturePackedReader.packed F (pair (pairFst q) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)))) =
      SquareFeaturePackedReader.packed F q := by
  rw [packed_at]
  rfl

theorem coefficient_packet (F : Family) (q : List Bool) (u v : ℕ) :
    coefficient F (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      residueBits (((factor F (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd (pairFst q)))).coeff v).coeff u :
        ZMod (Nat.fromBitsLE (pairSnd q)+1)) := by
  simp only [coefficient, BivariateQueryProductBits.outerWord, BivariateQueryProductBits.innerWord,
    pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  by_cases HV : v=0
  · subst v
    simp only [ite_true, squareQuery, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
      BivariateQueryProductBits.origin, BivariateQueryProductBits.innerWord, BivariateQueryProductBits.modulus,
      pairFst_pair, pairSnd_pair, Nat.fromBitsLE_bits]
    simp only [factor, coeff_add, coeff_X_zero, coeff_C_zero, zero_add, pow_two, packed_canonical]
    rfl
  · rw [ite_eq_right HV]
    by_cases H1 : v=1
    · subst v
      simp only [factor, coeff_add, coeff_X_one, coeff_C_succ, add_zero]
      by_cases HU : u=0
      · subst u
        simp only [and_self, ite_true, oneCode, BivariateQueryProductBits.modulus,
          pairFst_pair, BinaryNat.succ_eq_bits, coeff_one_zero]
        exact ArithmeticBits.one_residueBits _
      · simp only [HU, and_false, ite_false, coeff_one, ite_false, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]
    · have H10 : 1 ≠ v := Ne.symm H1
      simp only [H1, false_and, ite_false, factor, coeff_add, coeff_X, H10, ite_false,
        coeff_C, HV, ite_false, add_zero, coeff_zero, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

noncomputable def factorReader (F : Family) (A : Access F) : CertifiedPolynomial.BivariateReader
    (fun q => factor F (pairFst q) (Nat.fromBitsLE (pairSnd q))) where
  coefficient := coefficient F
  evaluator := coefficient_evaluator F A
  coefficient_eq := coefficient_packet F

noncomputable def access (F : Family) (A : Access F) : BivariateQueryProductBits.Access (family F) where
  reader := factorReader F A
  exponent _ := [true]
  exponent_eq _ _ := by change [true] = BinaryNatCode.encode 1; decide
  exponent_FP := constFn_mem_FP _
  count_binary := A.count
  degree_binary := BinaryFn.const 1
  parameterDegree_binary := (BinaryFn.const 2).mul (box_binary F A)
  mass_binary := (BinaryFn.const 2).mul A.mass

noncomputable def reader (F : Family) (A : Access F) : CertifiedPolynomial.BivariateReader (family F).product :=
  BivariateQueryProductBits.reader (access F A)

private theorem rename_tail (n : ℕ) (p : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.finSuccEquiv ℤ n (MvPolynomial.rename Fin.succ p) = C p := by
  have HE : (MvPolynomial.finSuccEquiv ℤ n).toRingEquiv.toRingHom.comp
      (MvPolynomial.rename (Fin.succ : Fin n → Fin (n+1))).toRingHom = C := by
    apply MvPolynomial.ringHom_ext
    · intro z; simp
    · intro i; simp [MvPolynomial.finSuccEquiv_apply]
  exact congrArg (fun f => f p) HE

/-- The backend reads the literal formal product, not an auxiliary norm. -/
theorem product_map (F : Family) (c : List Bool) : (family F).product c =
    ((MvPolynomial.finSuccEquiv ℤ (F.arity c)) (SquareFeatureProductFamily.polynomial F c)).map
      (FixedWidthKronecker.encode (F.arity c) (width F c)) := by
  have HL : (family F).product c = ∏ i ∈ Finset.range (F.count c), factor F c i := by
    change (∏ i : Fin (F.count c), factor F c i.val ^ (1 : ℕ)) = _
    simp only [pow_one]
    exact Fin.prod_univ_eq_prod_range (fun i => factor F c i) _
  rw [HL, SquareFeatureProductFamily.polynomial, map_prod, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [SquareFeatureProductFamily.factor, map_add, map_pow, MvPolynomial.finSuccEquiv_X_zero,
    rename_tail, Polynomial.map_add, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_C]
  rw [factor, packed_at]
  simp only [packedAt, ite_eq_left (Finset.mem_range.mp hi)]
  rw [map_pow]

end LeanCanny.Algebra.SquareFeatureBivariateProduct
