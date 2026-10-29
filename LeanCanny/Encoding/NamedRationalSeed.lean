/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.NamedRationalParents
public import LeanCanny.Algebra.ClearingMatrixSpace
public import LeanCanny.Algebra.LinearCoefficientBounds

/-! # A concrete native seed for named-parent sampling

The parameter equation is X, the unique root is zero, every ambient coordinate
is zero, and the unique descriptor is empty. This supplies an unconditional
base for the named-parent validity and derivative interfaces.
-/

@[expose] public section
namespace LeanCanny.Encoding.NamedRationalSeed
open LeanCanny.Algebra LeanCanny.Computation Polynomial Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def equation : SeparablePolynomialFamily.Source where
  polynomial _ := X
  degree _ := 1
  mass _ := 0
  degree_le _ := by simp only [natDegree_X, le_refl]
  mass_le _ := by simpa only [pow_one, pow_zero] using (coefficientMass_X_pow 1).le
  separable _ := by simpa only [Polynomial.map_X] using (Polynomial.separable_X (R := ℚ))

theorem equation_access : SeparablePolynomialFamily.Access equation := by
  refine ⟨BinaryFn.const 1, BinaryFn.const 0, ?_⟩
  simpa only [equation, pow_one] using ClearingMatrixBits.monomialEvaluator (fun _ => 1) (BinaryFn.const 1)

def derivativeValue (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) = 1 then InfinitesimalSign.encode 1 else InfinitesimalSign.encode 0

theorem derivative_FP : derivativeValue ∈ FP :=
  ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 1)).ite_mem_FP
    (constFn_mem_FP (InfinitesimalSign.encode 1)) (constFn_mem_FP (InfinitesimalSign.encode 0))

noncomputable def source : NamedRationalParents.Source where
  equation := equation
  coordinates := RationalCoordinateFamily.zero
  roots _ := {theta | theta = 0}
  root_zero _ theta ht := by simpa only [equation, Polynomial.eval₂_X, Set.mem_ofPred_eq] using ht
  defined _ theta _ := by
    intro i
    simp only [RationalCoordinateFamily.zero, Polynomial.eval₂_one, ne_eq, one_ne_zero, not_false_eq_true]
  descriptor _ _ := []
  descriptor_injective _ := by
    intro x y _
    exact Subtype.ext (x.property.trans y.property.symm)
  width _ := 0
  descriptor_length _ _ := Nat.le_refl 0
  derivativeValue := derivativeValue
  derivative_packet u x k := by
    have hx : x.val = 0 := x.property
    change derivativeValue (pair (pair u []) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign ((Polynomial.derivative^[k] (X : ℤ[X])).eval₂ (Int.castRingHom ℝ) x.val))
    rw [hx]
    by_cases h0 : k = 0
    · subst k
      norm_num [derivativeValue, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.fromBitsLE_cons, show Nat.fromBitsLE [] = 0 from rfl]
    · by_cases h1 : k = 1
      · subst k
        norm_num [derivativeValue, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.fromBitsLE_cons, show Nat.fromBitsLE [] = 0 from rfl]
      · rw [Polynomial.iterate_derivative_X (by omega : 1 < k)]
        simp only [derivativeValue, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, h1,
          ite_false, Polynomial.eval₂_zero, sign_zero]

theorem language_iff (q : List Bool) : q ∈ NamedRationalParents.language source ↔ pairSnd q = [] := by
  change (∃ _ : {theta : ℝ // theta = 0}, [] = pairSnd q) ↔ _
  constructor
  · rintro ⟨_, h⟩
    exact h.symm
  · intro h
    exact ⟨⟨0, rfl⟩, h.symm⟩

theorem decider : SpaceDecider (NamedRationalParents.language source) := by
  have V := SpaceFunction.ofFP (fun q => [decide (pairSnd q = [])])
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply V.decider (fun z => decide (z = [true])) (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  rw [language_iff]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]

theorem access : NamedRationalParents.Access source :=
  ⟨equation_access, RationalCoordinateFamily.zero_access, UnaryFn.const 0, decider,
    SpaceFunction.ofFP _ derivative_FP⟩

end LeanCanny.Encoding.NamedRationalSeed
