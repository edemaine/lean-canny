/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDenseMetadata

/-! # Polynomial-space access to dense tube summands

The source power is embedded in the point coordinates, optionally multiplied
by one shift variable. FP degree and shift-pattern guards reject zero queries.
The complete source-power routine handles every remaining coefficient.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDense
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding
open Algebra.RationalSubstitution.Indexed Algebra.MatrixPower
open scoped Classical

noncomputable def coefficient (base : List Bool → List Bool) (k : ℕ) (W : List Bool → ℕ)
    (target : List Bool → List Bool) (s : Option Bool) (c : List Bool) : ℤ :=
  (TubePolynomial.integerSpatial (polynomial base c ^ k) * MvPolynomial.monomial (shiftVector (arity base c) s) 1).coeff
    (TubeZeroQuery.exponent (arity base) W target c)

theorem coefficient_formula (base : List Bool → List Bool) (k : ℕ) (W : List Bool → ℕ)
    (target : List Bool → List Bool) (s : Option Bool) (c : List Bool) :
    coefficient base k W target s c = if Pattern (arity base) W target s c then
      (polynomial base c ^ k).coeff (exponentVector (arity base c) (FixedWidthQuery.entry (arity base) W target c)) else 0 := by
  classical
  have h := Algebra.EmbeddedCoefficient.coeff_rename_mul_monomial TubePolynomial.spatialEmbedding
    TubePolynomial.spatialEmbedding_injective (polynomial base c ^ k) (TubeZeroQuery.exponent (arity base) W target c)
    (shiftVector (arity base c) s) (shiftVector_point (arity base c) s)
  have hpiff := pattern_iff (arity base) W target s c
  by_cases hp : Pattern (arity base) W target s c
  · rw [ite_eq_left (hpiff.mpr hp), point_exponent] at h
    unfold TubePolynomial.spatialEmbedding at h
    simpa only [coefficient, TubePolynomial.integerSpatial, ite_eq_left hp] using h
  · rw [ite_eq_right (fun he => hp (hpiff.mp he))] at h
    unfold TubePolynomial.spatialEmbedding at h
    simpa only [coefficient, TubePolynomial.integerSpatial, ite_eq_right hp] using h

theorem coefficient_eq_zero_of_not_pattern (base : List Bool → List Bool) (k : ℕ) (W : List Bool → ℕ)
    (target : List Bool → List Bool) (s : Option Bool) (c : List Bool) (h : ¬ Pattern (arity base) W target s c) :
    coefficient base k W target s c = 0 := by rw [coefficient_formula, ite_eq_right h]

theorem coefficient_eq_zero_of_not_bounded (base : List Bool → List Bool) (k : ℕ) (hk : 0 < k) (W : List Bool → ℕ)
    (target : List Bool → List Bool) (s : Option Bool) (c : List Bool)
    (h : ¬ FixedWidthQuery.Bounded (arity base) W target (degreeBudget base k) c) : coefficient base k W target s c = 0 := by
  classical
  by_contra hne
  have hp : Pattern (arity base) W target s c := by
    by_contra hp
    exact hne (coefficient_eq_zero_of_not_pattern base k W target s c hp)
  rw [coefficient_formula, ite_eq_left hp] at hne
  apply h
  intro i hi
  have hj := MvPolynomial.monomial_le_degreeOf (⟨i, hi⟩ : Fin (arity base c)) (MvPolynomial.mem_support_iff.mpr hne)
  have he := hj.trans ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (polynomial_power_degree base k hk c))
  simpa only [exponentVector, Finsupp.coe_equivFunOnFinite_symm, FixedWidthQuery.entry, hi, ite_true] using he

def Allowed (base : List Bool → List Bool) (k : ℕ) (W : List Bool → ℕ) (target : List Bool → List Bool)
    (s : Option Bool) (c : List Bool) : Prop :=
  Pattern (arity base) W target s c ∧ FixedWidthQuery.Bounded (arity base) W target (degreeBudget base k) c

theorem allowed_fppred {base target : List Bool → List Bool} {W : List Bool → ℕ}
    (hb : base ∈ FP) (hW : UnaryFn W) (ht : target ∈ FP) (k : ℕ) (s : Option Bool) : FPPred (Allowed base k W target s) :=
  (pattern_fppred (arity_unary hb) hW ht s).and
    (FixedWidthQuery.bounded_fppred (arity_unary hb) hW (degreeBudget_unary hb k) ht)

theorem coefficient_eq_zero_of_not_allowed (base : List Bool → List Bool) (k : ℕ) (hk : 0 < k) (W : List Bool → ℕ)
    (target : List Bool → List Bool) (s : Option Bool) (c : List Bool) (h : ¬ Allowed base k W target s c) :
    coefficient base k W target s c = 0 := by
  by_cases hp : Pattern (arity base) W target s c
  · exact coefficient_eq_zero_of_not_bounded base k hk W target s c (fun hb => h ⟨hp, hb⟩)
  · exact coefficient_eq_zero_of_not_pattern base k W target s c hp

noncomputable def repacked (base : List Bool → List Bool) (k : ℕ) (W : List Bool → ℕ) (target : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthQuery.repack (arity base) W (size base k) (width base k) target

theorem repacked_mem_FP {base target : List Bool → List Bool} {W : List Bool → ℕ}
    (hb : base ∈ FP) (hW : UnaryFn W) (ht : target ∈ FP) (k : ℕ) : repacked base k W target ∈ FP :=
  FixedWidthQuery.repack_mem_FP (arity_unary hb) hW (size_unary hb k) (width_unary hb k) ht

theorem child_correct (base : List Bool → List Bool) (k : ℕ) (hk : 0 < k) (W : List Bool → ℕ)
    (target modulus : List Bool → List Bool) (c : List Bool)
    (h : FixedWidthQuery.Bounded (arity base) W target (degreeBudget base k) c) :
    CompactPowerCoefficient.value base (repacked base k W target) modulus (fun _ => k) c = residueBits
      (((polynomial base c ^ k).coeff (exponentVector (arity base c) (FixedWidthQuery.entry (arity base) W target c)) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  apply CompactPowerCoefficient.value_eq_original base (repacked base k W target) modulus (fun _ => k) c hk
    (FixedWidthQuery.entry (arity base) W target c) rfl
  · intro i _
    exact (FixedWidthQuery.entry_le_of_bounded _ _ _ _ c h i).trans_lt (budget_lt_width base k c)
  · intro i hi
    unfold FixedWidthQuery.entry
    exact ite_eq_right (by exact Nat.not_lt.mpr hi)

noncomputable def value (base : List Bool → List Bool) (k : ℕ) (W : List Bool → ℕ)
    (target modulus : List Bool → List Bool) (s : Option Bool) (c : List Bool) : List Bool :=
  residueBits ((coefficient base k W target s c : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

noncomputable def evaluator (base : List Bool → List Bool) (k : ℕ) (hk : 0 < k) (W : List Bool → ℕ)
    (target modulus : List Bool → List Bool) (s : Option Bool)
    (hb : base ∈ FP) (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) : SpaceFunction (value base k W target modulus s) := by
  let R := CompactPowerCoefficient.evaluator base (repacked base k W target) modulus (fun _ => k) hb
    (repacked_mem_FP hb hW ht k) hm (UnaryFn.const k)
  let E := SpaceFunction.branch (fun c => decide (Allowed base k W target s c)) (allowed_fppred hb hW ht k s).flag_mem_FP R
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine E.congr (funext fun c => ?_)
  by_cases h : Allowed base k W target s c
  · have he : coefficient base k W target s c =
        (polynomial base c ^ k).coeff (exponentVector (arity base c) (FixedWidthQuery.entry (arity base) W target c)) := by
      rw [coefficient_formula, ite_eq_left h.1]
    have hr := child_correct base k hk W target modulus c h.2
    rw [← he] at hr
    simpa [h, value] using hr
  · have hz := coefficient_eq_zero_of_not_allowed base k hk W target s c h
    simp [h, value, hz, residueBits, BinaryNatCode.encode]

theorem coefficient_none (base : List Bool → List Bool) (k : ℕ) (W : List Bool → ℕ)
    (target : List Bool → List Bool) (c : List Bool) : coefficient base k W target none c =
      TubePolynomial.spatialCoefficient (polynomial base c ^ k) (TubeZeroQuery.exponent (arity base) W target c) := by
  simpa only [coefficient, shiftVector, MvPolynomial.monomial_zero', map_one, mul_one] using
    TubePolynomial.coeff_integerSpatial (polynomial base c ^ k) (TubeZeroQuery.exponent (arity base) W target c)

theorem coefficient_some (base : List Bool → List Bool) (W : List Bool → ℕ)
    (target : List Bool → List Bool) (b : Bool) (c : List Bool) : coefficient base 1 W target (some b) c =
      TubePolynomial.shiftedSpatialCoefficient (polynomial base c) (TubeZeroQuery.exponent (arity base) W target c) b := by
  unfold coefficient
  rw [pow_one]
  simp only [shiftVector]
  change (TubePolynomial.integerSpatial (polynomial base c) * (MvPolynomial.X (.inl (.inr (.inl b))) : MvPolynomial (Coordinate (arity base c)) ℤ)).coeff _ = _
  rw [MvPolynomial.coeff_mul_X']
  unfold TubePolynomial.shiftedSpatialCoefficient
  split_ifs <;> simp only [TubePolynomial.coeff_integerSpatial]

end LeanCanny.ETR.TubeDense
