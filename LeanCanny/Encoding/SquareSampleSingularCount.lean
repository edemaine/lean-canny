/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleEquationCount
public import LeanCanny.Encoding.SquareSampleRegularFilter

/-! # Native counting of singular square-system candidates

One extra zero test imposes the cleared square-system Jacobian. Subtracting this
count from the system equation count will retain precisely regular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleSingularCount
open LeanCanny.Algebra LeanCanny.Computation
open MatrixPower
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleCoordinates.parameter
  SquareSampleCoordinates.parameterDegree SquareSampleCoordinates.baseHeight
  SquareSampleFilters.polynomial SquareSampleRegularFilter.polynomial
  SquareSampleFilters.degree SquareSampleFilters.mass
  SquareSampleRegularFilter.degree SquareSampleRegularFilter.mass

noncomputable def test (F : Inputs) (w : List Bool) : Polynomial ℤ :=
  if Nat.fromBitsLE (pairSnd w) < SquareSampleSource.count F (pairFst w) then
    SquareSampleFilters.polynomial F w
  else SquareSampleRegularFilter.polynomial F (pairFst w)

attribute [local irreducible] test

noncomputable def degree (F : Inputs) (u : List Bool) : ℕ :=
  max (SquareSampleFilters.degree F u) (SquareSampleRegularFilter.degree F u)
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ :=
  max (SquareSampleFilters.mass F u) (SquareSampleRegularFilter.mass F u)

theorem max_binary {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun u => max (f u) (g u)) :=
  (BinaryFn.ite (hf.le hg) hg hf).of_eq (fun _ => (max_def _ _).symm)

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) :=
  max_binary (SquareSampleFilters.degree_binary h)
    (SquareSampleRegularFilter.degree_binary h)
theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) :=
  max_binary (SquareSampleFilters.mass_binary h)
    (SquareSampleRegularFilter.mass_binary h)

theorem test_degree (F : Inputs) (w : List Bool) : (test F w).natDegree ≤ degree F (pairFst w) := by
  unfold test
  split
  · exact (SquareSampleFilters.polynomial_degree F w).trans (Nat.le_max_left _ _)
  · exact (SquareSampleRegularFilter.polynomial_degree F (pairFst w)).trans (Nat.le_max_right _ _)

theorem test_mass (F : Inputs) (w : List Bool) : coefficientMass (test F w) ≤ 2 ^ mass F (pairFst w) := by
  unfold test
  split
  · exact (SquareSampleFilters.polynomial_mass F w).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  · exact (SquareSampleRegularFilter.polynomial_mass F (pairFst w)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))

theorem test_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (PrimitivePairBits.coefficient (test F)) := by
  let context := RationalSubstitution.IntegerBits.context
  have hc : context ∈ FP := RationalSubstitution.IntegerBits.context_mem_FP
  have H := (BinaryFn.fromBits (mem_FP_comp hc pairSnd_mem_FP)).lt
    ((BinaryFn.ofUnary (SquareSampleSource.count_unary h)).comp (mem_FP_comp hc pairFst_mem_FP))
  have R := PrimitivePairBits.withContextEvaluator _ pairFst (SpaceFunction.ofFP _ pairFst_mem_FP)
    (SquareSampleRegularFilter.evaluator h)
  exact (SpaceFunction.branch _ H.flag_mem_FP (SquareSampleFilters.evaluator h) R).congr
    (funext fun q => by
      simp only [decide_eq_true_eq, Function.comp_apply, PrimitivePairBits.coefficient,
        RationalSubstitution.IntegerBits.coefficientResidue,
        test, context]
      split <;> rfl)

noncomputable def family (F : Inputs) : SignPatternBits.Family where
  root := SquareSampleCoordinates.parameter F
  polynomial c i := test F (pair c (BinaryNatCode.encode i))
  pattern _ _ := 0
  count c := BinaryNatCode.encode (SquareSampleSource.count F c + 1)
  rootDegree c := BinaryNatCode.encode (SquareSampleCoordinates.parameterDegree F c + 1)
  degree c := BinaryNatCode.encode (degree F c)
  rootMass c := BinaryNatCode.encode (SquareSampleCoordinates.baseHeight F c)
  mass c := BinaryNatCode.encode (mass F c)
  rootDegree_pos c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega
  root_degree c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (SquareSampleCoordinates.parameter_bounds F c).1.trans (Nat.le_succ _)
  root_mass c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (SquareSampleCoordinates.parameter_bounds F c).2
  polynomial_degree c i _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair] using test_degree F (pair c (BinaryNatCode.encode i))
  polynomial_mass c i _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits, pairFst_pair] using test_mass F (pair c (BinaryNatCode.encode i))

theorem controls {F : Inputs} (h : F.Access) : SignPatternBits.ControlsPolyTime (family F) := by
  constructor
  · exact (BinaryFn.ofUnary ((SquareSampleSource.count_unary h).add (UnaryFn.const 1))).bits_mem_FP
  · simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      (SquareSampleSource.count_unary h).add (UnaryFn.const 1)
  · exact ((SquareSampleCoordinates.parameterDegree_binary h).add (BinaryFn.const 1)).bits_mem_FP
  · exact (degree_binary h).bits_mem_FP
  · exact (SquareSampleCoordinates.baseHeight_binary h).bits_mem_FP
  · exact (mass_binary h).bits_mem_FP

noncomputable def access (F : Inputs) : SignPatternBits.Access (family F) where
  rootCoefficient := (SquareSampleEquationCount.access F).rootCoefficient
  polynomialCoefficient := PrimitivePairBits.coefficient (test F) ∘ SquareSampleReaders.query
  pattern _ := InfinitesimalSign.encode 0
  root_eq := (SquareSampleEquationCount.access F).root_eq
  polynomial_eq c i _ k m hm := by
    simp only [Function.comp_apply, PrimitivePairBits.coefficient,
      RationalSubstitution.IntegerBits.coefficientResidue, IntegerTarskiSeedBits.integerResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [SquareSampleReaders.query, RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [SquareSampleReaders.query, RationalSubstitution.IntegerBits.mValue,
        pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  pattern_eq _ _ := rfl

theorem evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (fun c => BinaryNatCode.encode (SignPatternBits.rootCount (family F) c)) := by
  have R : SpaceFunction ((access F).rootCoefficient) :=
    SquareSampleCoordinates.parameter_coefficient_evaluator h
  have P : SpaceFunction ((access F).polynomialCoefficient) :=
    (test_evaluator h).precompose SquareSampleReaders.query SquareSampleReaders.query_FP
  exact SignPatternBits.rootCountEvaluator (access F) (controls h)
    (constFn_mem_FP (InfinitesimalSign.encode 0)) R P

theorem tests_zero_iff (F : Inputs) (u : List Bool) (theta : ℝ) :
    (∀ i : Fin (SquareSampleSource.count F u + 1),
      (test F (pair u (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ) theta = 0) ↔
    (∀ i : Fin (SquareSampleSource.count F u),
      (SquareSampleFilters.polynomial F (pair u (BinaryNatCode.encode i.val))).eval₂
        (Int.castRingHom ℝ) theta = 0) ∧
      (SquareSampleRegularFilter.polynomial F u).eval₂ (Int.castRingHom ℝ) theta = 0 := by
  constructor
  · intro H
    constructor
    · intro i
      simpa only [test, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
        Fin.val_castSucc, ite_eq_left i.isLt] using H i.castSucc
    · simpa only [test, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
        Fin.val_last, Nat.lt_irrefl, ite_false] using H (Fin.last _)
  · rintro ⟨H, hr⟩ i
    by_cases hi : i.val < SquareSampleSource.count F u
    · simpa only [test, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
        ite_eq_left hi] using H ⟨i.val, hi⟩
    · simpa only [test, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
        ite_eq_right hi] using hr

end LeanCanny.Encoding.SquareSampleSingularCount
