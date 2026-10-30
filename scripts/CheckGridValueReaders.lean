import LeanCanny.Geometry.IntegerGridValueReader
import LeanCanny.Algebra.ModularResidueReaders

/-! Native grid readers retain parameter coefficients and repeated roots.
Run with `lake env lean -DwarningAsError=true scripts/CheckGridValueReaders.lean`.
-/

open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

namespace GridValueReaderRegression
noncomputable section

private def modulus (q : List Bool) := pairSnd (pairFst q)
private lemma modulus_FP : modulus ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

private lemma oneEvaluator : SpaceFunction (fun q => residueBits (1 : ZMod (Nat.fromBitsLE (modulus q) + 1))) := by
  have E := SpaceFunction.ofFP _ (mem_FP_comp
    (mem_FP_pair (constFn_mem_FP [true]) (mem_FP_comp modulus_FP BinaryNat.succ_mem_FP)) BinaryNat.mod_mem_FP)
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, BinaryNat.mod_pair, BinaryNat.succ_eq_bits,
    Nat.fromBitsLE_bits, residueBits, BinaryNatCode.encode, ZMod.val_one_eq_one_mod]
  rfl

private lemma monomialEvaluator (a b : ℕ) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient
      (fun _ => Polynomial.monomial a (Polynomial.monomial b (1 : ℤ)))) := by
  have hu := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hv := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have h := (hv.eq (BinaryFn.const a)).and (hu.eq (BinaryFn.const b))
  have E := ModularResidueReaders.maskEvaluator h oneEvaluator
  refine E.congr (funext fun q => ?_)
  simp only [ModularResidueReaders.maskValue, SymbolicFixedTableEntryBits.coefficient,
    Polynomial.coeff_monomial, SymbolicFixedTableEntryBits.integerResidue]
  by_cases ha : Nat.fromBitsLE (pairSnd (pairSnd q)) = a
  · by_cases hb : Nat.fromBitsLE (pairFst (pairSnd q)) = b
    · simp [ha, hb, modulus]
      rfl
    · simp [ha, hb, Ne.symm hb, Polynomial.coeff_monomial, residueBits, BinaryNatCode.encode]
  · simp [ha, Ne.symm ha, residueBits, BinaryNatCode.encode]

-- X² + T has a repeated coordinate root at the specialization T = 0.
private def P : Polynomial (Polynomial ℤ) :=
  Polynomial.monomial 2 (Polynomial.monomial 0 1) + Polynomial.monomial 0 (Polynomial.monomial 1 1)

private lemma polynomialEvaluator :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (fun _ => P)) := by
  have E := ModularResidueReaders.addEvaluator modulus_FP (monomialEvaluator 2 0) (monomialEvaluator 0 1)
  refine E.congr (funext fun q => ?_)
  rw [ModularResidueReaders.addValue_eq modulus _ _ q _ _ rfl rfl]
  simp only [SymbolicFixedTableEntryBits.coefficient, P, Polynomial.coeff_add,
    SymbolicFixedTableEntryBits.integerResidue, Int.cast_add]
  rfl

private lemma P_inner (k : ℕ) : (P.coeff k).natDegree ≤ 1 := by
  rw [P, Polynomial.coeff_add]
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le <;> simp only [Polynomial.coeff_monomial] <;> split_ifs <;> simp

private lemma P_degree : P.natDegree = 2 := by
  rw [P, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simp)]
  simp

-- Exponents in a different coordinate are rejected before the original reader.
example : (P.toMvPolynomial (0 : Fin 2)).coeff (Finsupp.single 1 1) = 0 := by
  rw [DiagonalParameterBits.coefficient, ite_eq_right]
  intro h
  have hh := h 1 (by decide)
  simp at hh

private def F : IntegerGridValueGramBits.Family where
  arity _ := 1
  width _ := 3
  degree _ _ := 2
  testDegree _ := 3
  coordinate _ _ := P
  test _ := 0

private lemma controls : F.affine.homogeneous.layout.Controls := by
  refine ⟨UnaryFn.const 2, UnaryFn.const 3, (BinaryFn.const 4).of_eq ?_, ?_⟩
  · intro c
    change 4 = (∑ i : Fin 2, (ProjectiveValueGram.degrees (fun _ : Fin 1 => 2) 3 i - 1)) + 1
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    rfl
  · have hz := (BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)
    exact (BinaryFn.ite hz (BinaryFn.const 3) (BinaryFn.const 2)).of_eq (fun _ => rfl)

private lemma coordinateEvaluator : SpaceFunction (SymbolicFixedTableEntryBits.coefficient
    (DiagonalParameterBits.selected F.arity F.coordinate)) := by
  have hi := BinaryFn.fromBits (mem_FP_comp
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  have E := ModularResidueReaders.maskEvaluator (hi.lt (BinaryFn.const 1)) polynomialEvaluator
  have hs (z : List Bool) : DiagonalParameterBits.selected F.arity F.coordinate z =
      if Nat.fromBitsLE (pairSnd z) < 1 then P else 0 := by
    rfl
  refine E.congr (funext fun q => ?_)
  simp only [ModularResidueReaders.maskValue, SymbolicFixedTableEntryBits.coefficient,
    hs, Function.comp_apply]
  by_cases hq : Nat.fromBitsLE (pairSnd (pairFst (pairFst q))) < 1
  · simp only [hq, ite_true]
  · simp [hq, SymbolicFixedTableEntryBits.integerResidue, residueBits, BinaryNatCode.encode]

private lemma testEvaluator : SpaceFunction F.testCoefficient := by
  refine (SpaceFunction.ofFP _ (constFn_mem_FP [])).congr (funext fun q => ?_)
  change [] = residueBits ((0 : ℤ) : ZMod _)
  simp [residueBits, BinaryNatCode.encode]

-- This reader starts with two explicit monomial programs. No homogeneous,
-- determinant, or annihilator reader is supplied.
example : CertifiedPolynomial.BivariateReader F.affine.homogeneous.annihilator := by
  apply F.reader controls (fun _ => 1) (BinaryFn.const 1) _ _ coordinateEvaluator testEvaluator
  · intro c i k
    exact P_inner k
  · intro c u
    change (0 : Polynomial ℤ).natDegree ≤ 1
    simp

-- The exceptional specialization with a repeated root is retained.
example : (F.affine.homogeneous.annihilator []).eval₂
    (Polynomial.eval₂RingHom (Int.castRingHom ℝ) 0) 0 = 0 := by
  apply F.eval_eq_zero [] (Polynomial.eval₂RingHom (Int.castRingHom ℝ) 0) (fun _ => 0)
  · intro i
    apply (Polynomial.natDegree_add_le _ _).trans
    simp [F, P]
  · simp [F]
  · norm_num [ProjectiveValueGramBits.Family.layout, F, IntegerGridValueGramBits.Family.affine,
      AffineValueGramBits.Family.homogeneous, Macaulay.level, ProjectiveValueGram.degrees, Fin.sum_univ_succ]
  · intro i
    simp [F, P]

-- The same native polynomial is nonzero despite the repeated special fiber.
example : F.affine.homogeneous.annihilator [] ≠ 0 := by
  apply F.ne_zero [] (fun _ => P_degree.symm) (fun _ => by
    change 0 < P.natDegree
    rw [P_degree]
    decide) (by decide)
  norm_num [ProjectiveValueGramBits.Family.layout, F, IntegerGridValueGramBits.Family.affine,
    AffineValueGramBits.Family.homogeneous, Macaulay.level, ProjectiveValueGram.degrees, Fin.sum_univ_succ]

end
end GridValueReaderRegression
