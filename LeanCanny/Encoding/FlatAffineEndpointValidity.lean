/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointRows

/-! # Native validity of prepared endpoint degree records

The record's degree field is checked against the original exceptional reader
in polynomial space. Correct records give degree bounds and infinity exclusion
for the actual frozen systems, without requiring regular endpoint roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointValidity
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def Valid (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : Prop :=
  FlatAffineEndpointPreparation.degree r = (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)).natDegree

theorem record_valid (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    Valid F height (FlatAffineEndpointPreparation.record F height u) := by
  simp only [Valid, FlatAffineEndpointPreparation.record, FlatAffineEndpointPreparation.degree,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def compare (z : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairSnd (pairFst z)) = Nat.fromBitsLE (pairSnd z))

theorem compare_FP : (fun z => [compare z]) ∈ FP :=
  ((BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)).eq (BinaryFn.fromBits pairSnd_mem_FP)).flag_mem_FP

theorem decider {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceDecider {r | Valid F height r} := by
  have E := ((FlatAffineEndpointPreparation.degreeEvaluator h hcone height hh).precompose pairFst pairFst_mem_FP).withInput
  apply E.decider compare compare_FP
  intro r
  simp only [Valid, FlatAffineEndpointPreparation.degree, Set.mem_ofPred_eq, compare,
    pairFst_pair, pairSnd_pair, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem degree_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (hr : Valid F height r) (i : Fin (FlatAffineEndpointRows.arity F r)) :
    (FlatAffineEndpointPreparation.system F height r i).totalDegree ≤ FlatAffineEndpointPreparation.degrees F r i := by
  have H := FrozenAffineCopies.degree_bound (FlatAffinePowerPositive.system F (pairFst r))
    (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) (height (pairFst r)) FlatAffineEndpointPreparation.frozen
    (FlatAffinePowerPositive.degree F (pairFst r)) (FlatAffinePowerPositive.polynomial_degree F (pairFst r))
    (FlatAffinePowerPositive.degree_pos F (pairFst r)) i
  change _ ≤ FrozenAffineCopies.degrees (FlatAffinePowerPositive.degree F (pairFst r)) (FlatAffineEndpointPreparation.degree r) i
  rw [hr]
  exact H

theorem degree_pos (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : Valid F height r) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) :
    0 < FlatAffineEndpointPreparation.degree r := by
  rw [hr]
  exact Polynomial.natDegree_pos_of_eval₂_root (FlatAffineHeightSlabExceptional.ne_zero F hcone height (pairFst r))
    (Int.castRingHom ℝ) ha (by intro z hz; change (z : ℝ) = 0 at hz; exact Int.cast_eq_zero.mp hz)

theorem degrees_pos (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : Valid F height r) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (i : Fin (FlatAffineEndpointRows.arity F r)) : 0 < FlatAffineEndpointPreparation.degrees F r i :=
  FrozenAffineCopies.degrees_pos _ _ (FlatAffinePowerPositive.degree_pos F (pairFst r)) (degree_pos F hcone height r hr a ha) i

theorem noInfinity (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : Valid F height r) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) :
    AffineFiniteCoordinates.NoInfinity (FlatAffineEndpointPreparation.system F height r) (FlatAffineEndpointPreparation.degrees F r) := by
  have H := FrozenAffineCopies.noInfinity (FlatAffinePowerPositive.system F (pairFst r))
    (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) (height (pairFst r)) FlatAffineEndpointPreparation.frozen
    (FlatAffinePowerPositive.degree F (pairFst r)) (hr ▸ degree_pos F hcone height r hr a ha)
    (FlatAffinePowerPositive.noInfinity F hcone (pairFst r))
  change AffineFiniteCoordinates.NoInfinity _ (FrozenAffineCopies.degrees (FlatAffinePowerPositive.degree F (pairFst r))
    (FlatAffineEndpointPreparation.degree r))
  rw [hr]
  exact H

end LeanCanny.Encoding.FlatAffineEndpointValidity
