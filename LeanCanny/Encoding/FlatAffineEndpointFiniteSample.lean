/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteBounds
public import LeanCanny.Encoding.FlatAffineEndpointFiniteGrid
public import LeanCanny.Encoding.GuardedSquareSampleInput

/-! # Native complete sampling of jointly retained midpoint tuples

All square rows, coordinate annihilators, binary budgets, and degree-record
checks come from the original affine source. Complete short labels retain
singular joint roots. The guarded language rejects malformed records.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteSample
open LeanCanny.Algebra LeanCanny.Computation MatrixPower Polynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def data (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : GuardedSquareSampleInput.Data where
  count := FlatAffineEndpointFiniteFrame.arity F
  degree := FlatAffineEndpointFiniteBounds.rowDegree F
  mass := FlatAffineEndpointFiniteBounds.integerExponent F
  system := FlatAffineEndpointFiniteFrame.system F height
  annihilator := FlatAffineEndpointFiniteGram.annihilator F height
  annDegree := FlatAffineEndpointFiniteBounds.coordinateDegree F
  annHeight := FlatAffineEndpointFiniteBounds.heightBound F
  good := {s | FlatAffineEndpointFiniteFrame.Valid F height s}
  count_pos _ := Nat.zero_lt_succ _
  system_degree s hs := FlatAffineEndpointFiniteBounds.row_degree_le F height s hs
  system_mass s _ := FlatAffineEndpointFiniteBounds.integer_mass F hcone height s
  ann_nonzero s hs := FlatAffineEndpointFiniteGram.ne_zero F hcone height s hs
  ann_degree s _ := FlatAffineEndpointFiniteBounds.annihilator_degree F height s
  ann_height s _ := FlatAffineEndpointFiniteBounds.annihilator_height F hcone height s
  ann_root s hs := FlatAffineEndpointFiniteGram.root F height s hs

def annQuery (q : List Bool) : List Bool := pair
  (pair (pair (SquareSampleInput.source q) (SquareSampleInput.indexWord q)) (SquareSampleInput.rankWord q))
    (SquareSampleInput.modulusWord q)
theorem annQuery_FP : annQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair SquareSampleInput.source_FP SquareSampleInput.indexWord_FP) SquareSampleInput.rankWord_FP)
    SquareSampleInput.modulusWord_FP

theorem annEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (GuardedSquareSampleInput.annCoefficient (data F hcone height)) := by
  have E := (FlatAffineEndpointFiniteGrid.evaluator h height hh).precompose annQuery annQuery_FP
  refine E.congr (funext fun q => ?_)
  have hi : FlatAffineEndpointFiniteDegree.rowAt F (SquareSampleInput.source q) (Nat.fromBitsLE (SquareSampleInput.indexWord q)) =
      GuardedSquareSampleInput.selected (data F hcone height) (SquareSampleInput.source q) (SquareSampleInput.indexWord q) := Fin.ext rfl
  have hp : FlatAffineEndpointFiniteGrid.annihilator F height (pair (SquareSampleInput.source q) (SquareSampleInput.indexWord q)) =
      FlatAffineEndpointFiniteGram.annihilator F height (SquareSampleInput.source q)
        (GuardedSquareSampleInput.selected (data F hcone height) (SquareSampleInput.source q) (SquareSampleInput.indexWord q)) :=
    (FlatAffineEndpointFiniteGrid.packet F height _ _).trans
      (congrArg (FlatAffineEndpointFiniteGram.annihilator F height (SquareSampleInput.source q)) hi)
  simp only [Function.comp_apply, annQuery, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair]
  rw [hp]
  rfl

theorem access {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : (data F hcone height).Access := by
  refine ⟨FlatAffineEndpointFiniteFrame.arity_unary h, FlatAffineEndpointFiniteBounds.rowDegree_binary h,
    FlatAffineEndpointFiniteBounds.integerExponent_binary h height, FlatAffineEndpointFiniteBounds.coordinateDegree_binary h height,
    FlatAffineEndpointFiniteBounds.heightBound_binary h height, FlatAffineEndpointFiniteFrame.validDecider h hcone height hh,
    ?_, annEvaluator h hcone height hh⟩
  exact (FlatAffineEndpointFiniteRows.access h height hh).coefficient.congr (funext fun _ => rfl)

noncomputable def input (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : SquareSampleInput.Inputs := GuardedSquareSampleInput.input (data F hcone height)

theorem sampleAccess {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : (input F hcone height).Access :=
  GuardedSquareSampleInput.access (access h hcone height hh)

theorem complete (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : SquareSampleComplete.Complete (input F hcone height) :=
  GuardedSquareSampleInput.complete (data F hcone height)

theorem mem_PSPACE {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    GuardedSquareSampleInput.language (data F hcone height) ∈ PSPACE := GuardedSquareSampleInput.mem_PSPACE (access h hcone height hh)

theorem width_unary {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    UnaryFn (SquareSampleCompleteVertices.width (input F hcone height)) := GuardedSquareSampleInput.width_unary (access h hcone height hh)

end LeanCanny.Encoding.FlatAffineEndpointFiniteSample
