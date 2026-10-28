/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateRationalCompositionWith
public import LeanCanny.Algebra.PreparedPolynomialContext
public import LeanCanny.Algebra.DyadicConstantCoefficient

/-! # Native families of rational parent coordinates

A query is `pair context coordinateIndex`. Binary degree and mass controls
and native coefficient readers suffice for substitution; no original source
syntax is part of the interface. Reindexing, composition, and guarded choice
preserve this interface and charge all constituent readers.
-/

@[expose] public section
namespace LeanCanny.Algebra.RationalCoordinateFamily
open LeanCanny.Encoding LeanCanny.Computation UnivariateRational
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  coordinate : List Bool → Coordinate
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  degree_le : ∀ q, (coordinate q).degree ≤ degree (pairFst q)
  numerator_mass : ∀ q, coefficientMass (coordinate q).numerator ≤ 2 ^ mass (pairFst q)
  denominator_mass : ∀ q, coefficientMass (coordinate q).denominator ≤ 2 ^ mass (pairFst q)

structure Access (F : Family) : Prop where
  degree : BinaryFn F.degree
  mass : BinaryFn F.mass
  numerator : SpaceFunction (PrimitivePairBits.coefficient (fun q => (F.coordinate q).numerator))
  denominator : SpaceFunction (PrimitivePairBits.coefficient (fun q => (F.coordinate q).denominator))

noncomputable def point (F : Family) (u : List Bool) (theta : ℝ) (i : ℕ) : ℝ :=
  (F.coordinate (pair u (BinaryNatCode.encode i))).eval theta

def Defined (F : Family) (u : List Bool) (theta : ℝ) : Prop :=
  ∀ i, (F.coordinate (pair u (BinaryNatCode.encode i))).denominator.eval₂ (Int.castRingHom ℝ) theta ≠ 0

def reindex (F : Family) (context query : List Bool → List Bool)
    (hq : ∀ q, pairFst (query q) = context (pairFst q)) : Family where
  coordinate := F.coordinate ∘ query
  degree := F.degree ∘ context
  mass := F.mass ∘ context
  degree_le q := by simpa only [Function.comp_apply, hq] using F.degree_le (query q)
  numerator_mass q := by simpa only [Function.comp_apply, hq] using F.numerator_mass (query q)
  denominator_mass q := by simpa only [Function.comp_apply, hq] using F.denominator_mass (query q)

theorem reindex_access {F : Family} (A : Access F) (context query : List Bool → List Bool)
    (hq : ∀ q, pairFst (query q) = context (pairFst q))
    (hc : context ∈ FP) (hp : query ∈ FP) : Access (reindex F context query hq) :=
  ⟨A.degree.comp hc, A.mass.comp hc,
    PrimitivePairBits.withContextEvaluator _ query (SpaceFunction.ofFP _ hp) A.numerator,
    PrimitivePairBits.withContextEvaluator _ query (SpaceFunction.ofFP _ hp) A.denominator⟩

noncomputable def compose (outer inner : Family) : Family where
  coordinate q := (outer.coordinate q).compWith (outer.degree (pairFst q)) (inner.coordinate q)
  degree u := outer.degree u * inner.degree u
  mass u := outer.mass u + outer.degree u * inner.mass u
  degree_le q := (Coordinate.compWith_degree _ _ _).trans (Nat.mul_le_mul_left _ (inner.degree_le q))
  numerator_mass q := (Coordinate.compWith_mass _ _ _ (outer.degree_le q) _ _
    (outer.numerator_mass q) (outer.denominator_mass q) (inner.numerator_mass q) (inner.denominator_mass q)).1
  denominator_mass q := (Coordinate.compWith_mass _ _ _ (outer.degree_le q) _ _
    (outer.numerator_mass q) (outer.denominator_mass q) (inner.numerator_mass q) (inner.denominator_mass q)).2

theorem compose_access {outer inner : Family} (A : Access outer) (B : Access inner) :
    Access (compose outer inner) := by
  have E := RationalCoordinateBits.evaluatorsWithBound outer.coordinate inner.coordinate
    (outer.degree ∘ pairFst) (A.degree.comp pairFst_mem_FP)
    A.numerator A.denominator B.numerator B.denominator
  exact ⟨A.degree.mul B.degree, A.mass.add (A.degree.mul B.mass), E.1, E.2⟩

noncomputable def choose (P : List Bool → Prop) (left right : Family) : Family where
  coordinate q := if P q then left.coordinate q else right.coordinate q
  degree u := left.degree u + right.degree u
  mass u := left.mass u + right.mass u
  degree_le q := by
    split_ifs
    · exact (left.degree_le q).trans (Nat.le_add_right _ _)
    · exact (right.degree_le q).trans (Nat.le_add_left _ _)
  numerator_mass q := by
    split_ifs
    · exact (left.numerator_mass q).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
    · exact (right.numerator_mass q).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  denominator_mass q := by
    split_ifs
    · exact (left.denominator_mass q).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
    · exact (right.denominator_mass q).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

theorem choose_access {P : List Bool → Prop} (hP : FPPred P) {left right : Family}
    (A : Access left) (B : Access right) : Access (choose P left right) := by
  have hp := hP.comp RationalSubstitution.IntegerBits.context_mem_FP
  have hn := SpaceFunction.branch _ hp.flag_mem_FP A.numerator B.numerator
  have hd := SpaceFunction.branch _ hp.flag_mem_FP A.denominator B.denominator
  refine ⟨A.degree.add B.degree, A.mass.add B.mass, hn.congr ?_, hd.congr ?_⟩ <;>
    funext q <;> simp only [choose, PrimitivePairBits.coefficient, decide_eq_true_eq] <;>
    split_ifs <;> rfl

noncomputable def zero : Family where
  coordinate _ := ⟨0, 1⟩
  degree _ := 0
  mass _ := 0
  degree_le _ := by simp [Coordinate.degree]
  numerator_mass _ := by simp
  denominator_mass _ := by simp only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one, pow_zero, le_refl]

theorem zero_access : Access zero := by
  refine ⟨BinaryFn.const 0, BinaryFn.const 0, ?_, DyadicConstantBits.oneCoefficientEvaluator⟩
  apply (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])).congr
  funext q
  simp only [PrimitivePairBits.coefficient, zero, Polynomial.coeff_zero,
    RationalSubstitution.IntegerBits.coefficientResidue, Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero]
  rfl

noncomputable def extend (F : Family) (dim : List Bool → ℕ) : Family :=
  choose (fun q => Nat.fromBitsLE (pairSnd q) < dim (pairFst q)) F zero

theorem extend_access {F : Family} (A : Access F) {dim : List Bool → ℕ} (hd : BinaryFn dim) :
    Access (extend F dim) :=
  choose_access ((BinaryFn.fromBits pairSnd_mem_FP).lt (hd.comp pairFst_mem_FP)) A zero_access

theorem extend_defined (F : Family) (dim : List Bool → ℕ) (u : List Bool) (theta : ℝ)
    (hd : ∀ i < dim u, (F.coordinate (pair u (BinaryNatCode.encode i))).denominator.eval₂
      (Int.castRingHom ℝ) theta ≠ 0) : Defined (extend F dim) u theta := by
  intro i
  simp only [extend, choose, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs with hi
  · exact hd i hi
  · simp only [zero, Polynomial.eval₂_one, ne_eq, one_ne_zero, not_false_eq_true]

theorem extend_point (F : Family) (dim : List Bool → ℕ) (u : List Bool) (theta : ℝ) (i : ℕ) :
    point (extend F dim) u theta i = if i < dim u then point F u theta i else 0 := by
  simp only [point, extend, choose, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs
  · rfl
  · simp only [zero, Coordinate.eval, Polynomial.eval₂_zero, Polynomial.eval₂_one, zero_div]

end LeanCanny.Algebra.RationalCoordinateFamily
