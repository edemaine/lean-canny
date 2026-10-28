/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalCoordinateFamilyReaders
public import LeanCanny.Algebra.ClearingMatrixSpace
public import LeanCanny.Encoding.BoundedCriticalSampleBlockCodes

/-! # Free-block substitution at native rational parents

The parent interface supplies rational coordinates without requiring a
full-writer parent. Free coordinates are Kronecker monomials; frozen
coordinates retain the exact parent family. Their native readers include
the parent's coefficient computations.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentBlockCodes
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open RationalCoordinateFamily BoundedCriticalSampleBlockSource
open BoundedCriticalSampleBlockCodes (power span)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def base (A : Family) (b : Bool) (u : List Bool) (i : ℕ) : ℤ[X] :=
  if b then RationalCoordinateFamily.numerator A u i else RationalCoordinateFamily.denominator A u i

noncomputable def coordinate (A : Family) (offset dim : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) :
    MvPolynomial (Fin (dim u + 1)) ℤ :=
  if hi : InBlock (offset u) (dim u) i then if b then MvPolynomial.X (freeVariable _ _ _ hi) else 1
  else IndexedMultivariateRational.parameter (dim u) (base A b u i)

theorem coordinate_degree (A : Family) (offset dim : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) :
    (coordinate A offset dim b u i).totalDegree ≤ max (A.degree u) 1 := by
  unfold coordinate
  split_ifs
  · simpa only [MvPolynomial.totalDegree_X] using Nat.le_max_right (A.degree u) 1
  · simp only [MvPolynomial.totalDegree_one, Nat.zero_le]
  · apply (IndexedMultivariateRational.parameter_degree _ _).trans
    apply le_trans _ (Nat.le_max_left _ _)
    have H := A.degree_le (pair u (BinaryNatCode.encode i))
    simp only [pairFst_pair, UnivariateRational.Coordinate.degree] at H
    cases b
    · exact (le_max_right _ _).trans H
    · exact (le_max_left _ _).trans H

noncomputable def free (W offset dim : List Bool → ℕ) : Family where
  coordinate q := ⟨X ^ power W offset dim (pairFst q) (Nat.fromBitsLE (pairSnd q)), 1⟩
  degree u := 2 ^ span W dim u
  mass _ := 0
  degree_le q := by
    simp only [UnivariateRational.Coordinate.degree, natDegree_X_pow, natDegree_one, max_zero]
    apply Nat.pow_le_pow_right (by decide)
    unfold span
    nlinarith [Nat.min_le_right (Nat.fromBitsLE (pairSnd q) - offset (pairFst q)) (dim (pairFst q))]
  numerator_mass q := by simp only [coefficientMass_X_pow, pow_zero, le_refl]
  denominator_mass q := by simp only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one, pow_zero, le_refl]

theorem free_access {W offset dim : List Bool → ℕ} (hW : UnaryFn W) (ho : BinaryFn offset) (hk : UnaryFn dim) :
    Access (free W offset dim) := by
  have hi := (BinaryFn.fromBits pairSnd_mem_FP).sub (ho.comp pairFst_mem_FP)
  have hm := UnaryFn.fromBitsLE_min hi.bits_mem_FP (hk.comp pairFst_mem_FP)
  have hp : BinaryFn (fun q => power W offset dim (pairFst q) (Nat.fromBitsLE (pairSnd q))) := by
    apply BinaryFn.of_eq ((BinaryFn.const 2).powUnary
      ((hm.add (UnaryFn.const 1)).mul (hW.comp pairFst_mem_FP)))
    intro q
    simp only [power, BinaryNatCode.encode, Nat.fromBitsLE_bits, Function.comp_apply]
  exact ⟨(BinaryFn.const 2).powUnary (hW.mul (hk.add (UnaryFn.const 1))), BinaryFn.const 0,
    ClearingMatrixBits.monomialEvaluator _ hp, DyadicConstantBits.oneCoefficientEvaluator⟩

noncomputable def encodedFamily (A : Family) (W offset dim : List Bool → ℕ) : Family :=
  choose (fun q => InBlock (offset (pairFst q)) (dim (pairFst q)) (Nat.fromBitsLE (pairSnd q)))
    (free W offset dim) A

theorem encoded_access {A : Family} (a : Access A) {W offset dim : List Bool → ℕ}
    (hW : UnaryFn W) (ho : BinaryFn offset) (hk : UnaryFn dim) : Access (encodedFamily A W offset dim) := by
  have hi := BinaryFn.fromBits pairSnd_mem_FP
  have hO : BinaryFn (fun q => offset (pairFst q)) := ho.comp pairFst_mem_FP
  have hK : BinaryFn (fun q => dim (pairFst q)) := (BinaryFn.ofUnary hk).comp pairFst_mem_FP
  exact choose_access ((hO.le hi).and (hi.lt (hO.add hK))) (free_access hW ho hk) a

noncomputable def encoded (A : Family) (W offset dim : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) : ℤ[X] :=
  if InBlock (offset u) (dim u) i then if b then X ^ power W offset dim u i else 1 else base A b u i

theorem encode_coordinate (A : Family) (W offset dim : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) :
    FixedWidthKronecker.encode (dim u + 1) (W u) (coordinate A offset dim b u i) = encoded A W offset dim b u i := by
  by_cases hi : InBlock (offset u) (dim u) i
  · have hm : min (i - offset u) (dim u) = i - offset u := Nat.min_eq_left (by unfold InBlock at hi; omega)
    cases b
    · simp only [coordinate, encoded, hi, dite_true, ite_true, Bool.false_eq_true, ite_false, map_one]
    · simp only [coordinate, encoded, hi, dite_true, ite_true, FixedWidthKronecker.encode,
        MvPolynomial.eval₂Hom_X', freeVariable, power, hm]
  · simp only [coordinate, encoded, hi, dite_false, ite_false, IndexedMultivariateRational.encode_parameter]

theorem encoded_eq (A : Family) (W offset dim : List Bool → ℕ) (u : List Bool) (i : ℕ) :
    (encodedFamily A W offset dim).coordinate (pair u (BinaryNatCode.encode i)) =
      ⟨encoded A W offset dim true u i, encoded A W offset dim false u i⟩ := by
  simp only [encodedFamily, choose, free, encoded, base, RationalCoordinateFamily.numerator,
    RationalCoordinateFamily.denominator, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    ite_true, Bool.false_eq_true, ite_false]
  split_ifs <;> rfl

theorem encoded_mass (A : Family) (W offset dim : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) :
    coefficientMass (encoded A W offset dim b u i) ≤ 2 ^ A.mass u := by
  cases b
  · have H := (encodedFamily A W offset dim).denominator_mass (pair u (BinaryNatCode.encode i))
    rw [encoded_eq] at H
    simpa only [encodedFamily, choose, free, pairFst_pair, Nat.zero_add] using H
  · have H := (encodedFamily A W offset dim).numerator_mass (pair u (BinaryNatCode.encode i))
    rw [encoded_eq] at H
    simpa only [encodedFamily, choose, free, pairFst_pair, Nat.zero_add] using H

noncomputable def readers {A : Family} (a : Access A) {W offset dim : List Bool → ℕ}
    (hW : UnaryFn W) (ho : BinaryFn offset) (hk : UnaryFn dim) (arity : List Bool → ℕ) :
    RationalSubstitution.IntegerBits.CoordinateReaders arity
      (encoded A W offset dim true) (encoded A W offset dim false) := by
  have R := RationalCoordinateFamily.readers (encoded_access a hW ho hk) arity
  have hn : RationalCoordinateFamily.numerator (encodedFamily A W offset dim) = encoded A W offset dim true :=
    funext fun u => funext fun i => congrArg UnivariateRational.Coordinate.numerator (encoded_eq A W offset dim u i)
  have hd : RationalCoordinateFamily.denominator (encodedFamily A W offset dim) = encoded A W offset dim false :=
    funext fun u => funext fun i => congrArg UnivariateRational.Coordinate.denominator (encoded_eq A W offset dim u i)
  rw [hn, hd] at R
  exact R

end LeanCanny.Encoding.RationalParentBlockCodes
