/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightCells
public import LeanCanny.Algebra.IntegerPolynomialDegreeSpace
public import LeanCanny.Algebra.FrozenAffineCopies

/-! # Native exact-degree preparation for frozen endpoint systems

The exceptional polynomial's actual degree is computed in space, then stored
beside its original source context. Reading that record is FP; computing it
is charged. Genuine endpoint roots force a positive actual degree.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointPreparation
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option maxHeartbeats 300000

noncomputable def record (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool) : List Bool :=
  pair u (BinaryNatCode.encode (FlatAffineHeightSlabExceptional.polynomial F height u).natDegree)

theorem degreeEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun u => BinaryNatCode.encode (FlatAffineHeightSlabExceptional.polynomial F height u).natDegree) :=
  IntegerPolynomialBits.degreeEvaluator _ (FlatAffineHeightSlabExceptional.evaluator h height hh)
    _ _ (FlatAffineHeightSlabExceptional.degreeBound_binary h height)
    (FlatAffineHeightSlabExceptional.massBound_binary h height)
    (FlatAffineHeightSlabExceptional.degree_bound F hcone height)
    (FlatAffineHeightSlabExceptional.mass_bound F height)

theorem recordEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (record F height) :=
  (degreeEvaluator h hcone height hh).withInput

def degree (r : List Bool) : ℕ := Nat.fromBitsLE (pairSnd r)
theorem degree_binary : BinaryFn degree := BinaryFn.fromBits pairSnd_mem_FP

theorem degree_record (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    degree (record F height u) = (FlatAffineHeightSlabExceptional.polynomial F height u).natDegree := by
  simp only [degree, record, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem coefficientEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (PrimitivePairBits.coefficient
      (FlatAffineHeightSlabExceptional.polynomial F height ∘ pairFst)) :=
  PolynomialFamilyProductBits.reindexEvaluator (FlatAffineHeightSlabExceptional.evaluator h height hh) pairFst pairFst_mem_FP

theorem degree_pos_of_root (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height u) = 0) :
    0 < degree (record F height u) := by
  rw [degree_record]
  exact Polynomial.natDegree_pos_of_eval₂_root (FlatAffineHeightSlabExceptional.ne_zero F hcone height u)
    (Int.castRingHom ℝ) ha (by intro z hz; change (z : ℝ) = 0 at hz; exact Int.cast_eq_zero.mp hz)

def frozen (k : Fin 3) : Bool := decide (k.val ≠ 0)

noncomputable def system (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool) :
    Fin (3 * count F (pairFst r) + 1) → MvPolynomial (Fin (3 * count F (pairFst r) + 1)) ℤ :=
  FrozenAffineCopies.system (FlatAffinePowerPositive.system F (pairFst r))
    (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) (height (pairFst r)) frozen

noncomputable def degrees (F : Inputs) (r : List Bool) : Fin (3 * count F (pairFst r) + 1) → ℕ :=
  FrozenAffineCopies.degrees (FlatAffinePowerPositive.degree F (pairFst r)) (degree r)

theorem noInfinity_record (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height u) = 0) :
    AffineFiniteCoordinates.NoInfinity (system F height (record F height u)) (degrees F (record F height u)) := by
  have he : pairFst (record F height u) = u := by simp only [record, pairFst_pair]
  have hd := degree_record F height u
  change AffineFiniteCoordinates.NoInfinity (FrozenAffineCopies.system (FlatAffinePowerPositive.system F _)
    (FlatAffineHeightSlabExceptional.polynomial F height _) (height _) frozen)
      (FrozenAffineCopies.degrees (FlatAffinePowerPositive.degree F _) (degree (record F height u)))
  rw [he, hd]
  apply FrozenAffineCopies.noInfinity _ _ _ _ _ _ (FlatAffinePowerPositive.noInfinity F hcone u)
  exact Polynomial.natDegree_pos_of_eval₂_root (FlatAffineHeightSlabExceptional.ne_zero F hcone height u)
    (Int.castRingHom ℝ) ha (by intro z hz; change (z : ℝ) = 0 at hz; exact Int.cast_eq_zero.mp hz)

end LeanCanny.Encoding.FlatAffineEndpointPreparation
