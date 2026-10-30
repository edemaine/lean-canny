/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointAdjacentComplete
public import LeanCanny.Algebra.FrozenAffineLift

/-! # A finite integer frame for jointly labeled midpoint comparisons

Retain a sample or exceptional height as one more variable around the frozen
endpoint system. The resulting square integer system contains the current
point and two endpoint candidates simultaneously. Exact retained degrees
are computed in space and stored in a checked record. Positive valid degree
records exclude infinity without any regularity assumptions.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteFrame
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def retained (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : Polynomial ℤ :=
  FlatAffineEndpointExceptional.polynomial F height r * (FlatAffineEndpointExceptional.polynomial F height r).derivative

noncomputable def record (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : List Bool :=
  pair r (BinaryNatCode.encode (retained F height r).natDegree)

def degree (s : List Bool) : ℕ := Nat.fromBitsLE (pairSnd s)
theorem degree_binary : BinaryFn degree := BinaryFn.fromBits pairSnd_mem_FP

theorem degreeEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun r => BinaryNatCode.encode (retained F height r).natDegree) := by
  let S := FlatAffineEndpointSamples.source F hcone height
  have A := FlatAffineEndpointSamples.access h hcone height hh
  exact IntegerPolynomialBits.degreeEvaluator S.polynomial A.coefficient S.degree S.mass A.degree A.mass S.degree_bound S.mass_bound

theorem recordEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (record F height) := (degreeEvaluator h hcone height hh).withInput

noncomputable def Valid (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool) : Prop :=
  FlatAffineEndpointValidity.Valid F height (pairFst s) ∧ 0 < FlatAffineEndpointPreparation.degree (pairFst s) ∧
    degree s = (retained F height (pairFst s)).natDegree ∧ 0 < degree s

theorem validDecider {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceDecider {s | Valid F height s} := by
  have A := ((FlatAffineEndpointValidity.decider h hcone height hh).precompose pairFst pairFst_mem_FP).flagEvaluator
  have D : SpaceDecider {s | degree s = (retained F height (pairFst s)).natDegree} := by
    apply (((degreeEvaluator h hcone height hh).precompose pairFst pairFst_mem_FP).withInput).decider
      FlatAffineEndpointValidity.compare FlatAffineEndpointValidity.compare_FP
    intro s
    simp only [degree, FlatAffineEndpointValidity.compare, Set.mem_ofPred_eq, Function.comp_apply,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]
  have hOld := (BinaryFn.const 0).lt (FlatAffineEndpointPreparation.degree_binary.comp pairFst_mem_FP)
  have hNew := (BinaryFn.const 0).lt degree_binary
  have E := (A.andFlags (SpaceFunction.ofFP _ hOld.flag_mem_FP)).andFlags
    (D.flagEvaluator.andFlags (SpaceFunction.ofFP _ hNew.flag_mem_FP))
  apply E.decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro s
  simp only [Valid, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq, and_assoc, Function.comp_apply]

def arity (F : Inputs) (s : List Bool) : ℕ := 1 * FlatAffineEndpointRows.arity F (pairFst s) + 1
theorem arity_unary {F : Inputs} (h : F.Access) : UnaryFn (arity F) :=
  ((UnaryFn.const 1).mul ((FlatAffineEndpointRows.arity_unary h).comp pairFst_mem_FP)).add (UnaryFn.const 1)

noncomputable def system (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool) :
    Fin (arity F s) → MvPolynomial (Fin (arity F s)) ℤ :=
  FrozenAffineCopies.system (FlatAffineEndpointPreparation.system F height (pairFst s))
    (retained F height (pairFst s)) (FlatAffineEndpointGram.active F height (pairFst s)) (fun _ : Fin 1 => true)

noncomputable def degrees (F : Inputs) (s : List Bool) : Fin (arity F s) → ℕ :=
  FrozenAffineCopies.degrees (FlatAffineEndpointPreparation.degrees F (pairFst s)) (degree s)

theorem inner_degrees_pos (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (hs : Valid F height s) (i : Fin (FlatAffineEndpointRows.arity F (pairFst s))) :
    0 < FlatAffineEndpointPreparation.degrees F (pairFst s) i :=
  FrozenAffineCopies.degrees_pos _ _ (FlatAffinePowerPositive.degree_pos F (pairFst (pairFst s))) hs.2.1 i

theorem degree_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (hs : Valid F height s) (i : Fin (arity F s)) : (system F height s i).totalDegree ≤ degrees F s i := by
  have H := FrozenAffineCopies.degree_bound (FlatAffineEndpointPreparation.system F height (pairFst s))
    (retained F height (pairFst s)) (FlatAffineEndpointGram.active F height (pairFst s)) (fun _ : Fin 1 => true)
    (FlatAffineEndpointPreparation.degrees F (pairFst s))
    (FlatAffineEndpointValidity.degree_bound F height (pairFst s) hs.1) (inner_degrees_pos F height s hs) i
  change _ ≤ FrozenAffineCopies.degrees (FlatAffineEndpointPreparation.degrees F (pairFst s)) (degree s) i
  rw [hs.2.2.1]
  exact H

theorem degrees_pos (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (hs : Valid F height s) (i : Fin (arity F s)) : 0 < degrees F s i :=
  FrozenAffineCopies.degrees_pos _ _ (inner_degrees_pos F height s hs) hs.2.2.2 i

theorem inner_noInfinity (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (hs : Valid F height s) :
    AffineFiniteCoordinates.NoInfinity (FlatAffineEndpointPreparation.system F height (pairFst s))
      (FlatAffineEndpointPreparation.degrees F (pairFst s)) := by
  have H := FrozenAffineCopies.noInfinity (FlatAffinePowerPositive.system F (pairFst (pairFst s)))
    (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) (height (pairFst (pairFst s)))
    FlatAffineEndpointPreparation.frozen (FlatAffinePowerPositive.degree F (pairFst (pairFst s)))
    (hs.1 ▸ hs.2.1) (FlatAffinePowerPositive.noInfinity F hcone (pairFst (pairFst s)))
  change AffineFiniteCoordinates.NoInfinity _ (FrozenAffineCopies.degrees
    (FlatAffinePowerPositive.degree F (pairFst (pairFst s))) (FlatAffineEndpointPreparation.degree (pairFst s)))
  rw [hs.1]
  exact H

theorem noInfinity (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (hs : Valid F height s) :
    AffineFiniteCoordinates.NoInfinity (system F height s) (degrees F s) := by
  have H := FrozenAffineCopies.noInfinity (FlatAffineEndpointPreparation.system F height (pairFst s))
    (retained F height (pairFst s)) (FlatAffineEndpointGram.active F height (pairFst s)) (fun _ : Fin 1 => true)
    (FlatAffineEndpointPreparation.degrees F (pairFst s)) (hs.2.2.1 ▸ hs.2.2.2) (inner_noInfinity F hcone height s hs)
  change AffineFiniteCoordinates.NoInfinity _ (FrozenAffineCopies.degrees (FlatAffineEndpointPreparation.degrees F (pairFst s)) (degree s))
  rw [hs.2.2.1]
  exact H

end LeanCanny.Encoding.FlatAffineEndpointFiniteFrame
