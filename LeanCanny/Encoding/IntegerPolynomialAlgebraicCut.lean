/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialSampleSliceRootCount
public import LeanCanny.Algebra.ModularAddFP

/-! # Native root ranks at complete algebraic thresholds

Count roots of an implicit integer polynomial below a separately labeled
algebraic number. The linear slice test uses the same complete base label.
Repeated threshold roots are retained and invalid labels return zero.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialAlgebraicCut
open LeanCanny.Algebra LeanCanny.Computation Polynomial MatrixPower
open IntegerPolynomialRootQueriesBits (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def cut : BoundedAlgebraicSlice.Family where
  polynomial _ := Polynomial.X - Polynomial.C Polynomial.X
  degree _ := 1
  parameterDegree _ := 1
  mass _ := 1
  polynomial_degree _ := by exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  coefficient_degree _ i := by
    simp only [Polynomial.coeff_sub]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · by_cases hi : i = 1 <;> simp [Polynomial.coeff_X, hi, eq_comm]
    · by_cases hi : i = 0 <;> simp [Polynomial.coeff_C, hi]
  coefficient_mass _ i := by
    have hm1 : coefficientMass (1 : ℤ[X]) = 1 := by rw [← Polynomial.C_1, coefficientMass_C]; rfl
    have hmX : coefficientMass (Polynomial.X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
    simp only [Polynomial.coeff_sub]
    apply (coefficientMass_sub_le _ _).trans
    have hX : coefficientMass ((Polynomial.X : (ℤ[X])[X]).coeff i) ≤ 1 := by
      by_cases hi : i = 1 <;> simp [Polynomial.coeff_X, hi, eq_comm, hm1]
    have hC : coefficientMass ((Polynomial.C Polynomial.X : (ℤ[X])[X]).coeff i) ≤ 1 := by
      by_cases hi : i = 0 <;> simp [Polynomial.coeff_C, hi, hmX]
    omega

def positive (z : List Bool) : Prop := Nat.fromBitsLE (pairFst (pairSnd z)) = 0 ∧ Nat.fromBitsLE (pairSnd (pairSnd z)) = 1
def negative (z : List Bool) : Prop := Nat.fromBitsLE (pairFst (pairSnd z)) = 1 ∧ Nat.fromBitsLE (pairSnd (pairSnd z)) = 0
instance (z : List Bool) : Decidable (positive z) := inferInstanceAs (Decidable (_ ∧ _))
instance (z : List Bool) : Decidable (negative z) := inferInstanceAs (Decidable (_ ∧ _))

theorem positive_pred : FPPred positive :=
  ((BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)).eq (BinaryFn.const 0)).and
    ((BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)).eq (BinaryFn.const 1))
theorem negative_pred : FPPred negative :=
  ((BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)).eq (BinaryFn.const 1)).and
    ((BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)).eq (BinaryFn.const 0))

def modulus (z : List Bool) : List Bool := BinaryNat.succ (pairSnd (pairFst z))
theorem modulus_FP : modulus ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP

noncomputable def coefficient (z : List Bool) : List Bool := ArithmeticBits.addMod (pair (modulus z)
  (pair (if positive z then ArithmeticBits.one (modulus z) else [])
    (ArithmeticBits.negate (pair (modulus z) (if negative z then ArithmeticBits.one (modulus z) else [])))))

theorem coefficient_FP : coefficient ∈ FP := by
  have hp := positive_pred.ite_mem_FP (mem_FP_comp modulus_FP ArithmeticBits.one_mem_FP) (constFn_mem_FP [])
  have hn := negative_pred.ite_mem_FP (mem_FP_comp modulus_FP ArithmeticBits.one_mem_FP) (constFn_mem_FP [])
  have hneg := mem_FP_comp (mem_FP_pair modulus_FP hn) ArithmeticBits.negate_mem_FP
  exact mem_FP_of_eq (mem_FP_comp (mem_FP_pair modulus_FP (mem_FP_pair hp hneg)) ArithmeticBits.addMod_mem_FP)
    (fun z => by simp only [coefficient, Function.comp_apply])

noncomputable def reader : CertifiedPolynomial.BivariateReader cut.polynomial where
  coefficient := coefficient
  evaluator := SpaceFunction.ofFP _ coefficient_FP
  coefficient_eq q u v := by
    let m := Nat.fromBitsLE (pairSnd q) + 1
    let : NeZero m := ⟨by dsimp [m]; omega⟩
    have hm : modulus (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) = BinaryNatCode.encode m := by
      simp only [modulus, pairFst_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode, m]
    have ep : (((Polynomial.X : (ℤ[X])[X]).coeff v).coeff u) = if u = 0 ∧ v = 1 then 1 else 0 := by
      by_cases hu : u = 0 <;> by_cases hv : v = 1 <;> simp [hu, hv, Polynomial.coeff_X, Polynomial.coeff_one, eq_comm]
    have en : (((Polynomial.C Polynomial.X : (ℤ[X])[X]).coeff v).coeff u) = if u = 1 ∧ v = 0 then 1 else 0 := by
      by_cases hu : u = 1 <;> by_cases hv : v = 0 <;> simp [hu, hv, Polynomial.coeff_C, Polynomial.coeff_X, eq_comm]
    have hp : (if positive (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) then
        ArithmeticBits.one (modulus (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))) else []) =
        residueBits (((((Polynomial.X : (ℤ[X])[X]).coeff v).coeff u) : ℤ) : ZMod m) := by
      rw [ep, hm]
      simp only [positive, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      split_ifs
      · exact (ArithmeticBits.one_residueBits m).trans (congrArg residueBits Int.cast_one.symm)
      · simp [residueBits, BinaryNatCode.encode]
    have hn : (if negative (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) then
        ArithmeticBits.one (modulus (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))) else []) =
        residueBits (((((Polynomial.C Polynomial.X : (ℤ[X])[X]).coeff v).coeff u) : ℤ) : ZMod m) := by
      rw [en, hm]
      simp only [negative, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      split_ifs
      · exact (ArithmeticBits.one_residueBits m).trans (congrArg residueBits Int.cast_one.symm)
      · simp [residueBits, BinaryNatCode.encode]
    rw [coefficient, hp, hn, hm, ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits]
    congr 1
    have he : (((Polynomial.X - Polynomial.C Polynomial.X : (ℤ[X])[X]).coeff v).coeff u) =
        (((Polynomial.X : (ℤ[X])[X]).coeff v).coeff u) -
          (((Polynomial.C Polynomial.X : (ℤ[X])[X]).coeff v).coeff u) := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub]
    change (((((Polynomial.X : (ℤ[X])[X]).coeff v).coeff u) : ZMod m) +
      -(((((Polynomial.C Polynomial.X : (ℤ[X])[X]).coeff v).coeff u) : ZMod m))) =
        (((((Polynomial.X - Polynomial.C Polynomial.X : (ℤ[X])[X]).coeff v).coeff u)) : ZMod m)
    rw [he, Int.cast_sub, sub_eq_add_neg]

noncomputable def cutAccess : cut.Access := ⟨reader, BinaryFn.const 1, BinaryFn.const 1, BinaryFn.const 1⟩

noncomputable def head (Q : Source) : BoundedAlgebraicSlice.Family :=
  (BoundedAlgebraicSlice.ofTest (IntegerPolynomialTestSource.test Q)).comp pairFst

noncomputable def headAccess {Q : Source} (B : IntegerPolynomialRootQueriesBits.Access Q) : (head Q).Access :=
  (BoundedAlgebraicSlice.ofTestAccess (IntegerPolynomialTestSource.testAccess B)).comp pairFst pairFst_mem_FP

noncomputable def count (S Q : Source) (u : List Bool) : ℕ :=
  IntegerPolynomialSampleSlice.RootCount.signCount S (head Q) cut .neg u

theorem evaluator {S Q : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    (B : IntegerPolynomialRootQueriesBits.Access Q) : SpaceFunction (fun u => BinaryNatCode.encode (count S Q u)) :=
  IntegerPolynomialSampleSlice.RootCount.signCount_evaluator A (headAccess B) cutAccess .neg

theorem signCount_filter (S Q : Source) (u : List Bool) (hu : u ∈ IntegerPolynomialSampleSlice.valid S) (s : SignType) :
    IntegerPolynomialSampleSlice.RootCount.signCount S (head Q) cut s u =
      ((IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst u))).filter
        (fun x => SignType.sign (x - IntegerPolynomialSampleSlice.point S u) = s)).card := by
  have hHead : (head Q).slice (IntegerPolynomialSampleSlice.context u) (IntegerPolynomialSampleSlice.point S u) =
      (Q.polynomial (pairFst (pairFst u))).map (Int.castRingHom ℝ) := by
    rw [head, BoundedAlgebraicSlice.Family.slice_comp, BoundedAlgebraicSlice.ofTest_slice]
    simp only [IntegerPolynomialTestSource.test, IntegerPolynomialSampleSlice.context, pairFst_pair]
  have hCut : cut.slice (IntegerPolynomialSampleSlice.context u) (IntegerPolynomialSampleSlice.point S u) =
      Polynomial.X - Polynomial.C (IntegerPolynomialSampleSlice.point S u) := by
    simp only [BoundedAlgebraicSlice.Family.slice, cut, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      ParameterTarski.evalHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [IntegerPolynomialSampleSlice.RootCount.signCount, IntegerPolynomialSampleSlice.specialized, ite_eq_left hu,
    IntegerPolynomialSampleSlice.specialized, ite_eq_left hu, hHead, hCut]
  unfold RootSignQueries.singleSignCount
  congr 1
  ext x
  simp only [IntegerPolynomialRootQueriesBits.rootSet, algebraMap_int_eq, Finset.mem_filter,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

theorem count_below (S Q : Source) (u : List Bool) (hu : u ∈ IntegerPolynomialSampleSlice.valid S) :
    count S Q u = ((IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst u))).filter
      (fun x => x < IntegerPolynomialSampleSlice.point S u)).card := by
  rw [count, signCount_filter S Q u hu]
  congr 1
  ext x
  simp only [Finset.mem_filter, show SignType.neg = (-1 : SignType) from rfl, sign_eq_neg_one_iff, sub_neg]

noncomputable def zeroCount (S Q : Source) (u : List Bool) : ℕ :=
  IntegerPolynomialSampleSlice.RootCount.signCount S (head Q) cut 0 u

theorem zeroEvaluator {S Q : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    (B : IntegerPolynomialRootQueriesBits.Access Q) : SpaceFunction (fun u => BinaryNatCode.encode (zeroCount S Q u)) :=
  IntegerPolynomialSampleSlice.RootCount.signCount_evaluator A (headAccess B) cutAccess 0

theorem zeroCount_pos_iff (S Q : Source) (u : List Bool) (hu : u ∈ IntegerPolynomialSampleSlice.valid S) :
    0 < zeroCount S Q u ↔ IntegerPolynomialSampleSlice.point S u ∈ IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst u)) := by
  rw [zeroCount, signCount_filter S Q u hu, Finset.card_pos]
  simp only [Finset.filter_nonempty_iff, sign_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro ⟨x, hx, he⟩
    exact he ▸ hx
  · intro ht
    exact ⟨_, ht, rfl⟩

theorem zeroCount_eq_zero_iff (S Q : Source) (u : List Bool) (hu : u ∈ IntegerPolynomialSampleSlice.valid S) :
    zeroCount S Q u = 0 ↔ IntegerPolynomialSampleSlice.point S u ∉ IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst u)) := by
  rw [← zeroCount_pos_iff S Q u hu]
  omega

end LeanCanny.Encoding.IntegerPolynomialAlgebraicCut
