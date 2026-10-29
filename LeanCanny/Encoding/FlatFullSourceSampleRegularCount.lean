/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleSingularCount

/-! # Native counts and existence decisions for regular flat candidates

The flat-equation count minus the singular count counts exactly regular
parameter roots, hence exactly regular flat candidates. No promise that all
candidate roots are regular is needed. All ancestral equations are included in the complete flat system.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleRegularCount
open LeanCanny.Algebra LeanCanny.Computation
open FlatFullSourceTower (Inputs)
open FlatFullSourceSampleParameters (RegularParameters Candidates)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleCoordinates.parameter
  FlatFullSourceSampleFilters.polynomial FlatFullSourceSampleRegularFilter.polynomial

noncomputable def equationRoots (F : Inputs) (u : List Bool) : Finset ℝ :=
  ((FlatFullSourceSampleCoordinates.parameter F u).map (algebraMap ℤ ℝ)).roots.toFinset.filter
    (FlatFullSourceSampleFilters.Valid F u)

theorem mem_equationRoots (F : Inputs) (u : List Bool) (theta : ℝ) :
    theta ∈ equationRoots F u ↔ FlatFullSourceSampleFilters.Valid F u theta := by
  have hp := (Polynomial.map_ne_zero_iff (show Function.Injective (algebraMap ℤ ℝ) from Int.cast_injective)).mpr
    (FlatFullSourceSampleCoordinates.parameter_ne_zero F u)
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  rw [hm] at hp
  simp only [equationRoots, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hp,
    Polynomial.IsRoot.def, Polynomial.eval_map, hm]
  exact and_iff_right_of_imp (fun H => H.1)

theorem equationCount_eq_card (F : Inputs) (u : List Bool) :
    FlatFullSourceSampleEquationCount.count F u = (equationRoots F u).card := by
  calc
    _ = Nat.card {theta : ℝ // theta ∈ equationRoots F u} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun theta => (mem_equationRoots F u theta).symm))
    _ = _ := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

theorem singularCount_eq_card (F : Inputs) (u : List Bool) :
    SignPatternBits.rootCount (FlatFullSourceSampleSingularCount.family F) u =
      ((equationRoots F u).filter (fun theta =>
        (FlatFullSourceSampleRegularFilter.polynomial F u).eval₂ (Int.castRingHom ℝ) theta = 0)).card := by
  have hm : algebraMap ℤ ℝ = Int.castRingHom ℝ := RingHom.ext_int _ _
  unfold SignPatternBits.rootCount RootSignQueries.signCount
  simp only [FlatFullSourceSampleSingularCount.family]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode (FlatFullSourceSampleSource.count F u + 1)) =
    FlatFullSourceSampleSource.count F u + 1 from Nat.fromBitsLE_bits _]
  congr 1
  ext theta
  rw [Finset.mem_filter, Finset.mem_filter, mem_equationRoots]
  simp only [Polynomial.eval_map, hm, sign_eq_zero_iff]
  rw [FlatFullSourceSampleSingularCount.tests_zero_iff]
  rw [FlatFullSourceSampleFilters.valid_iff_filters]
  have hp := (Polynomial.map_ne_zero_iff (show Function.Injective (algebraMap ℤ ℝ) from Int.cast_injective)).mpr
    (FlatFullSourceSampleCoordinates.parameter_ne_zero F u)
  rw [hm] at hp
  simp only [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def, Polynomial.eval_map]
  exact and_assoc.symm

noncomputable def count (F : Inputs) (u : List Bool) : ℕ := Nat.card (RegularParameters F u)

theorem count_eq_difference (F : Inputs) (u : List Bool) :
    count F u = FlatFullSourceSampleEquationCount.count F u -
      SignPatternBits.rootCount (FlatFullSourceSampleSingularCount.family F) u := by
  let p := fun theta : ℝ => (FlatFullSourceSampleRegularFilter.polynomial F u).eval₂ (Int.castRingHom ℝ) theta = 0
  have hc : count F u = ((equationRoots F u).filter (fun theta => ¬p theta)).card := by
    calc
      _ = Nat.card {theta : ℝ // theta ∈ (equationRoots F u).filter (fun theta => ¬p theta)} := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro theta
        simp only [Finset.mem_filter, mem_equationRoots]
        exact (FlatFullSourceSampleRegularFilter.regular_iff F u theta).symm
      _ = _ := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hc, equationCount_eq_card, singularCount_eq_card]
  have H := (equationRoots F u).card_filter_add_card_filter_not p
  change _ = _ - ((equationRoots F u).filter p).card
  omega

theorem count_eq_candidates (F : Inputs) (u : List Bool) : count F u = Nat.card (Candidates F u) :=
  Nat.card_congr (FlatFullSourceSampleParameters.regularEquiv F u)

theorem count_eq_original_candidates (F : Inputs) (u : List Bool) :
    count F u = Nat.card (FlatFullSourceSampleParameters.OriginalCandidates F u) :=
  Nat.card_congr (FlatFullSourceSampleParameters.originalEquiv F u)

theorem count_le (F : Inputs) (u : List Bool) :
    count F u ≤ 2 ^ FlatFullSourceSampleParameters.labelWidth F u :=
  (FlatFullSourceSampleParameters.finite_regular_parameters F u).2

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (fun u => BinaryNatCode.encode (count F u)) := by
  have E := ((FlatFullSourceSampleEquationCount.evaluator h).pairOutputs
    (FlatFullSourceSampleSingularCount.evaluator h)).postcompose BinaryNat.sub BinaryNat.sub_mem_FP
  exact E.congr (funext fun u => by
    simp only [Function.comp_apply, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact congrArg Nat.bits (count_eq_difference F u).symm)

def language (F : Inputs) : Language := {u | Nonempty (RegularParameters F u)}

theorem language_iff_candidates (F : Inputs) (u : List Bool) : u ∈ language F ↔ Nonempty (Candidates F u) :=
  (FlatFullSourceSampleParameters.regularEquiv F u).nonempty_congr

theorem decider {F : Inputs} (h : F.Access) : SpaceDecider (language F) := by
  apply (evaluator h).decider (fun z => decide (0 < Nat.fromBitsLE z))
    (((BinaryFn.const 0).lt (BinaryFn.fromBits id_mem_FP)).flag_mem_FP)
  intro u
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]
  change Nonempty (RegularParameters F u) ↔ 0 < Nat.card (RegularParameters F u)
  exact ⟨fun H => Nat.card_pos_iff.mpr ⟨H, (FlatFullSourceSampleParameters.finite_regular_parameters F u).1⟩,
    fun H => (Nat.card_pos_iff.mp H).1⟩

theorem language_mem_PSPACE {F : Inputs} (h : F.Access) : language F ∈ PSPACE := (decider h).mem_PSPACE

end LeanCanny.Encoding.FlatFullSourceSampleRegularCount
