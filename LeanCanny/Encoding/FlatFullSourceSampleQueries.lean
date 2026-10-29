/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleRegularCount
public import LeanCanny.Algebra.FilteredSignProducts
public import LeanCanny.Algebra.IntegerDifferenceSpace

/-! # Native sign queries on regular flat candidates

Sign-pattern counts and products of polynomially many selected signs are
computed over regular flat parameter roots. Subtracting the singular
contribution preserves arbitrary signed probes. This supplies the queries
needed to identify the full flat tuple and to construct flat descriptors.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleQueries
open LeanCanny.Algebra LeanCanny.Computation
open FlatFullSourceTower (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleCoordinates.parameter
  FlatFullSourceSampleFilters.polynomial FlatFullSourceSampleRegularFilter.polynomial
  FlatFullSourceSampleSingularCount.test PrimitivePairBits.coefficient

noncomputable def roots (F : Inputs) (u : List Bool) : Finset ℝ :=
  (FlatFullSourceSampleRegularCount.equationRoots F u).filter (fun theta =>
    (FlatFullSourceSampleRegularFilter.polynomial F u).eval₂ (Int.castRingHom ℝ) theta ≠ 0)

theorem mem_roots (F : Inputs) (u : List Bool) (theta : ℝ) :
    theta ∈ roots F u ↔
      (FlatFullSourceSampleCoordinates.parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
      (∀ i, (FlatFullSourcePositive.system F u i).eval₂ (Int.castRingHom ℝ)
        (FlatFullSourceSampleParameters.decode F u theta) = 0) ∧
      (fderiv ℝ (fun y => fun i => (FlatFullSourcePositive.system F u i).eval₂
        (Int.castRingHom ℝ) y) (FlatFullSourceSampleParameters.decode F u theta)).IsInvertible := by
  rw [roots, Finset.mem_filter, FlatFullSourceSampleRegularCount.mem_equationRoots]
  exact FlatFullSourceSampleRegularFilter.regular_iff F u theta

theorem roots_card (F : Inputs) (u : List Bool) :
    (roots F u).card = FlatFullSourceSampleRegularCount.count F u := by
  calc
    _ = Nat.card {theta : ℝ // theta ∈ roots F u} := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = _ := Nat.card_congr (Equiv.subtypeEquivRight (mem_roots F u))

theorem equation_accepted (F : Inputs) (u : List Bool) :
    SignPatternBits.acceptedRoots (FlatFullSourceSampleEquationCount.family F) u =
      FlatFullSourceSampleRegularCount.equationRoots F u := by
  ext theta
  rw [FlatFullSourceSampleRegularCount.mem_equationRoots, FlatFullSourceSampleFilters.valid_iff_filters]
  simp only [SignPatternBits.acceptedRoots, FlatFullSourceSampleEquationCount.family,
    Finset.mem_filter, Multiset.mem_toFinset, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  rw [hm, Polynomial.mem_roots ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr
    (FlatFullSourceSampleCoordinates.parameter_ne_zero F u))]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_map, sign_eq_zero_iff, Fin.forall_iff]

theorem singular_accepted (F : Inputs) (u : List Bool) :
    SignPatternBits.acceptedRoots (FlatFullSourceSampleSingularCount.family F) u =
      (FlatFullSourceSampleRegularCount.equationRoots F u).filter (fun theta =>
        (FlatFullSourceSampleRegularFilter.polynomial F u).eval₂ (Int.castRingHom ℝ) theta = 0) := by
  ext theta
  rw [Finset.mem_filter, FlatFullSourceSampleRegularCount.mem_equationRoots,
    FlatFullSourceSampleFilters.valid_iff_filters]
  simp only [SignPatternBits.acceptedRoots, FlatFullSourceSampleSingularCount.family,
    Finset.mem_filter, Multiset.mem_toFinset, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  rw [hm, Polynomial.mem_roots ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr
    (FlatFullSourceSampleCoordinates.parameter_ne_zero F u))]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_map, sign_eq_zero_iff, Fin.forall_iff]
  have H := FlatFullSourceSampleSingularCount.tests_zero_iff F u theta
  simp only [Fin.forall_iff, BinaryNatCode.encode] at H
  rw [H]
  exact and_assoc.symm

def constraints (G : SignPatternBits.Family) (u : List Bool) (theta : ℝ) : Prop :=
  ∀ i, i < Nat.fromBitsLE (G.count u) →
    SignType.sign (((G.polynomial u i).map (algebraMap ℤ ℝ)).eval theta) = G.pattern u i

theorem append_accepted (G H : SignPatternBits.Family) (u : List Bool) :
    SignPatternBits.acceptedRoots (G.append H) u =
      (SignPatternBits.acceptedRoots G u).filter (constraints H u) := by
  ext theta
  simp only [SignPatternBits.acceptedRoots, Finset.mem_filter]
  rw [SignPatternBits.append_signs]
  exact and_assoc.symm

noncomputable def patternCount (F : Inputs) (G : SignPatternBits.Family) (u : List Bool) : ℕ :=
  ((roots F u).filter (constraints G u)).card

theorem patternCount_eq_difference (F : Inputs) (G : SignPatternBits.Family) (u : List Bool) :
    patternCount F G u = SignPatternBits.rootCount ((FlatFullSourceSampleEquationCount.family F).append G) u -
      SignPatternBits.rootCount ((FlatFullSourceSampleSingularCount.family F).append G) u := by
  rw [SignPatternBits.rootCount_eq_card, SignPatternBits.rootCount_eq_card, append_accepted, append_accepted,
    equation_accepted, singular_accepted]
  have H := ((FlatFullSourceSampleRegularCount.equationRoots F u).filter (constraints G u)).card_filter_add_card_filter_not
    (fun theta => (FlatFullSourceSampleRegularFilter.polynomial F u).eval₂ (Int.castRingHom ℝ) theta = 0)
  have H' : (((FlatFullSourceSampleRegularCount.equationRoots F u).filter (fun theta =>
      (FlatFullSourceSampleRegularFilter.polynomial F u).eval₂ (Int.castRingHom ℝ) theta = 0)).filter
        (constraints G u)).card + patternCount F G u =
      ((FlatFullSourceSampleRegularCount.equationRoots F u).filter (constraints G u)).card := by
    simpa only [patternCount, roots, Finset.filter_filter, ne_eq, and_comm] using H
  omega

theorem patternCount_evaluator {F : Inputs} (h : F.Access) {G : SignPatternBits.Family}
    (A : SignPatternBits.Access G) (hG : SignPatternBits.ControlsPolyTime G)
    (hs : A.pattern ∈ FP) (Q : SpaceFunction A.polynomialCoefficient) :
    SpaceFunction (fun u => BinaryNatCode.encode (patternCount F G u)) := by
  have R := FlatFullSourceSampleCoordinates.parameter_coefficient_evaluator h
  have P := (FlatFullSourceSampleFilters.evaluator h).precompose
    FlatFullSourceSampleEquationCount.filterQuery FlatFullSourceSampleEquationCount.filterQuery_FP
  have S := (FlatFullSourceSampleSingularCount.test_evaluator h).precompose
    FlatFullSourceSampleReaders.query FlatFullSourceSampleReaders.query_FP
  have E := SignPatternBits.appendCountEvaluator (FlatFullSourceSampleEquationCount.access F) A
    (FlatFullSourceSampleEquationCount.controls h) hG (constFn_mem_FP _) hs R P Q
  have T := SignPatternBits.appendCountEvaluator (FlatFullSourceSampleSingularCount.access F) A
    (FlatFullSourceSampleSingularCount.controls h) hG (constFn_mem_FP _) hs R S Q
  exact ((E.pairOutputs T).postcompose BinaryNat.sub BinaryNat.sub_mem_FP).congr (funext fun u => by
    simp only [Function.comp_apply, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact congrArg Nat.bits (patternCount_eq_difference F G u).symm)

def patternLanguage (F : Inputs) (G : SignPatternBits.Family) : Language :=
  {u | ∃ theta ∈ roots F u, constraints G u theta}

theorem patternDecider {F : Inputs} (h : F.Access) {G : SignPatternBits.Family}
    (A : SignPatternBits.Access G) (hG : SignPatternBits.ControlsPolyTime G)
    (hs : A.pattern ∈ FP) (Q : SpaceFunction A.polynomialCoefficient) : SpaceDecider (patternLanguage F G) := by
  apply (patternCount_evaluator h A hG hs Q).decider (fun z => decide (0 < Nat.fromBitsLE z))
    (((BinaryFn.const 0).lt (BinaryFn.fromBits id_mem_FP)).flag_mem_FP)
  intro u
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq, patternCount,
    Finset.card_pos, Finset.filter_nonempty_iff, patternLanguage, Set.mem_ofPred_eq]

noncomputable def product (G : SignPatternBits.Family) (u : List Bool) (theta : ℝ) : ℤ :=
  ∏ i ∈ Finset.range (Nat.fromBitsLE (G.count u)),
    (SignType.sign (((G.polynomial u i).map (algebraMap ℤ ℝ)).eval theta) : ℤ)

noncomputable def moment (F : Inputs) (G : SignPatternBits.Family) (u : List Bool) : ℤ :=
  ∑ theta ∈ roots F u, product G u theta

theorem moment_eq_difference (F : Inputs) (G : SignPatternBits.Family) (u : List Bool) :
    moment F G u = FilteredSignProductBits.value (FlatFullSourceSampleEquationCount.family F) G u -
      FilteredSignProductBits.value (FlatFullSourceSampleSingularCount.family F) G u := by
  simp only [FilteredSignProductBits.value, equation_accepted, singular_accepted]
  have H := Finset.sum_filter_add_sum_filter_not (FlatFullSourceSampleRegularCount.equationRoots F u)
    (fun theta => (FlatFullSourceSampleRegularFilter.polynomial F u).eval₂ (Int.castRingHom ℝ) theta = 0)
    (product G u)
  change (∑ theta ∈ roots F u, product G u theta) =
    (∑ theta ∈ FlatFullSourceSampleRegularCount.equationRoots F u, product G u theta) -
      ∑ theta ∈ (FlatFullSourceSampleRegularCount.equationRoots F u).filter
    (fun theta => (FlatFullSourceSampleRegularFilter.polynomial F u).eval₂ (Int.castRingHom ℝ) theta = 0), product G u theta
  unfold roots
  simp only [ne_eq]
  omega

theorem moment_evaluator {F : Inputs} (h : F.Access) {G : SignPatternBits.Family}
    (A : SignPatternBits.Access G) (hG : SignPatternBits.ControlsPolyTime G)
    (Q : SpaceFunction A.polynomialCoefficient) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (moment F G u)) := by
  have R := FlatFullSourceSampleCoordinates.parameter_coefficient_evaluator h
  have P := (FlatFullSourceSampleFilters.evaluator h).precompose
    FlatFullSourceSampleEquationCount.filterQuery FlatFullSourceSampleEquationCount.filterQuery_FP
  have S := (FlatFullSourceSampleSingularCount.test_evaluator h).precompose
    FlatFullSourceSampleReaders.query FlatFullSourceSampleReaders.query_FP
  have E := FilteredSignProductBits.evaluator (FlatFullSourceSampleEquationCount.access F) A
    (FlatFullSourceSampleEquationCount.controls h) hG (constFn_mem_FP _) R P Q
  have T := FilteredSignProductBits.evaluator (FlatFullSourceSampleSingularCount.access F) A
    (FlatFullSourceSampleSingularCount.controls h) hG (constFn_mem_FP _) R S Q
  exact (IntegerDifferenceBits.evaluator E T).congr (funext fun u =>
    congrArg SignStatisticBits.integerCode (moment_eq_difference F G u).symm)

theorem moment_bound (F : Inputs) (G : SignPatternBits.Family) (u : List Bool) :
    (moment F G u).natAbs ≤ FlatFullSourceSampleRegularCount.count F u := by
  rw [← roots_card, moment]
  apply (Int.natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _theta ∈ roots F u, 1 := by
      apply Finset.sum_le_sum
      intro theta _
      change Int.natAbsHom _ ≤ 1
      rw [product, map_prod]
      apply (Finset.prod_le_prod (fun i _ => ?_)).trans_eq (Finset.prod_const_one)
      cases SignType.sign (((G.polynomial u i).map (algebraMap ℤ ℝ)).eval theta) <;> decide
    _ = _ := by simp

end LeanCanny.Encoding.FlatFullSourceSampleQueries
