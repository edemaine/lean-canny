/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildEquationCount
public import LeanCanny.Encoding.RationalParentChildRegularFilter

/-! # Native counting of singular child candidates

One extra zero test imposes the cleared joint Jacobian. Subtracting this
count from the joint-equation count will retain precisely regular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildSingularCount
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open MatrixPower
open RationalParentChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildCoordinates.parameter
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildFilters.polynomial RationalParentChildRegularFilter.polynomial
  RationalParentChildFilters.degree RationalParentChildFilters.mass
  RationalParentChildRegularFilter.degree RationalParentChildRegularFilter.mass

noncomputable def test (F : Inputs) (w : List Bool) : Polynomial ℤ :=
  if Nat.fromBitsLE (pairSnd w) < RationalParentChildSource.count F (pairFst w) then
    RationalParentChildFilters.polynomial F w
  else RationalParentChildRegularFilter.polynomial F (pairFst w)

attribute [local irreducible] test

noncomputable def degree (F : Inputs) (u : List Bool) : ℕ :=
  max (RationalParentChildFilters.degree F u) (RationalParentChildRegularFilter.degree F u)
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ :=
  max (RationalParentChildFilters.mass F u) (RationalParentChildRegularFilter.mass F u)

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) :=
  BivariateRationalTermReader.max_binary (RationalParentChildFilters.degree_binary h)
    (RationalParentChildRegularFilter.degree_binary h)
theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) :=
  BivariateRationalTermReader.max_binary (RationalParentChildFilters.mass_binary h)
    (RationalParentChildRegularFilter.mass_binary h)

theorem test_degree (F : Inputs) (w : List Bool) : (test F w).natDegree ≤ degree F (pairFst w) := by
  unfold test
  split
  · exact (RationalParentChildFilters.polynomial_degree F w).trans (Nat.le_max_left _ _)
  · exact (RationalParentChildRegularFilter.polynomial_degree F (pairFst w)).trans (Nat.le_max_right _ _)

theorem test_mass (F : Inputs) (w : List Bool) : coefficientMass (test F w) ≤ 2 ^ mass F (pairFst w) := by
  unfold test
  split
  · exact (RationalParentChildFilters.polynomial_mass F w).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  · exact (RationalParentChildRegularFilter.polynomial_mass F (pairFst w)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

theorem test_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (PrimitivePairBits.coefficient (test F)) := by
  let context := RationalSubstitution.IntegerBits.context
  have hc : context ∈ FP := RationalSubstitution.IntegerBits.context_mem_FP
  have H := (BinaryFn.fromBits (mem_FP_comp hc pairSnd_mem_FP)).lt
    ((BinaryFn.ofUnary (RationalParentChildSource.count_unary h)).comp (mem_FP_comp hc pairFst_mem_FP))
  have R := PrimitivePairBits.withContextEvaluator _ pairFst (SpaceFunction.ofFP _ pairFst_mem_FP)
    (RationalParentChildRegularFilter.evaluator h)
  exact (SpaceFunction.branch _ H.flag_mem_FP (RationalParentChildFilters.evaluator h) R).congr
    (funext fun q => by
      simp only [decide_eq_true_eq, Function.comp_apply, PrimitivePairBits.coefficient,
        RationalSubstitution.IntegerBits.coefficientResidue,
        test, context]
      split <;> rfl)

noncomputable def family (F : Inputs) : SignPatternBits.Family where
  root := RationalParentChildCoordinates.parameter F
  polynomial c i := test F (pair c (BinaryNatCode.encode i))
  pattern _ _ := 0
  count c := BinaryNatCode.encode (RationalParentChildSource.count F c + 1)
  rootDegree c := BinaryNatCode.encode (RationalParentChildCoordinates.parameterDegree F c + 1)
  degree c := BinaryNatCode.encode (degree F c)
  rootMass c := BinaryNatCode.encode (RationalParentChildCoordinates.baseHeight F c)
  mass c := BinaryNatCode.encode (mass F c)
  rootDegree_pos c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega
  root_degree c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (RationalParentChildCoordinates.parameter_bounds F c).1.trans (Nat.le_succ _)
  root_mass c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (RationalParentChildCoordinates.parameter_bounds F c).2
  polynomial_degree c i _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair] using test_degree F (pair c (BinaryNatCode.encode i))
  polynomial_mass c i _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair] using test_mass F (pair c (BinaryNatCode.encode i))

theorem controls {F : Inputs} (h : F.Access) : SignPatternBits.ControlsPolyTime (family F) := by
  constructor
  · exact (BinaryFn.ofUnary ((RationalParentChildSource.count_unary h).add (UnaryFn.const 1))).bits_mem_FP
  · simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      (RationalParentChildSource.count_unary h).add (UnaryFn.const 1)
  · exact ((RationalParentChildCoordinates.parameterDegree_binary h).add (BinaryFn.const 1)).bits_mem_FP
  · exact (degree_binary h).bits_mem_FP
  · exact (RationalParentChildCoordinates.baseHeight_binary h).bits_mem_FP
  · exact (mass_binary h).bits_mem_FP

noncomputable def access (F : Inputs) : SignPatternBits.Access (family F) where
  rootCoefficient := (RationalParentChildEquationCount.access F).rootCoefficient
  polynomialCoefficient := PrimitivePairBits.coefficient (test F) ∘ RationalParentChildReaders.query
  pattern _ := InfinitesimalSign.encode 0
  root_eq := (RationalParentChildEquationCount.access F).root_eq
  polynomial_eq c i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient,
      RationalSubstitution.IntegerBits.coefficientResidue, IntegerTarskiSeedBits.integerResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [RationalParentChildReaders.query, RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [RationalParentChildReaders.query, RationalSubstitution.IntegerBits.mValue,
        pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  pattern_eq _ _ := rfl

theorem evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (fun c => BinaryNatCode.encode (SignPatternBits.rootCount (family F) c)) := by
  have R : SpaceFunction ((access F).rootCoefficient) :=
    RationalParentChildCoordinates.parameter_coefficient_evaluator h
  have P : SpaceFunction ((access F).polynomialCoefficient) :=
    (test_evaluator h).precompose RationalParentChildReaders.query RationalParentChildReaders.query_FP
  exact SignPatternBits.rootCountEvaluator (access F) (controls h)
    (constFn_mem_FP (InfinitesimalSign.encode 0)) R P

theorem tests_zero_iff (F : Inputs) (u : List Bool) (theta : ℝ) :
    (∀ i : Fin (RationalParentChildSource.count F u + 1),
      (test F (pair u (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ) theta = 0) ↔
    (∀ i : Fin (RationalParentChildSource.count F u),
      (RationalParentChildFilters.polynomial F (pair u (BinaryNatCode.encode i.val))).eval₂
        (Int.castRingHom ℝ) theta = 0) ∧
      (RationalParentChildRegularFilter.polynomial F u).eval₂ (Int.castRingHom ℝ) theta = 0 := by
  constructor
  · intro H
    constructor
    · intro i
      simpa only [test, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
        Fin.val_castSucc, ite_eq_left i.isLt] using H i.castSucc
    · simpa only [test, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
        Fin.val_last, Nat.lt_irrefl, ite_false] using H (Fin.last _)
  · rintro ⟨H, hr⟩ i
    by_cases hi : i.val < RationalParentChildSource.count F u
    · simpa only [test, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
        ite_eq_left hi] using H ⟨i.val, hi⟩
    · simpa only [test, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
        ite_eq_right hi] using hr

end LeanCanny.Encoding.RationalParentChildSingularCount
