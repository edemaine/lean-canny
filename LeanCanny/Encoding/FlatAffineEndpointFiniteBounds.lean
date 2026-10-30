/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteGram
public import LeanCanny.Algebra.FrozenAffineMass

/-! # Source-derived budgets for joint finite midpoint sampling

The original retained equation, the sample/boundary equation, and the
embedded tower supply binary row and Gram bounds. Complete coordinate
annihilators therefore need no degree or coefficient-height oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteBounds
open LeanCanny.Algebra LeanCanny.Computation MatrixPower Polynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def zero (F : Inputs) (s : List Bool) : Fin (FlatAffineEndpointFiniteFrame.arity F s) := ⟨0, Nat.zero_lt_succ _⟩

noncomputable def rowDegree (F : Inputs) (s : List Bool) : ℕ :=
  FlatAffineEndpointFiniteFrame.degree s + FlatAffineEndpointPreparation.degree (pairFst s) +
    FlatAffineFullSourceTower.degree F (pairFst (pairFst s)) + 1

noncomputable def retainedMass (F : Inputs) (r : List Bool) : ℕ :=
  FlatAffineEndpointExceptional.massBound F r +
    ((FlatAffineEndpointExceptional.degreeBound F r).size + FlatAffineEndpointExceptional.massBound F r)
noncomputable def integerExponent (F : Inputs) (s : List Bool) : ℕ :=
  FlatAffineEndpointValueBounds.integerExponent F (pairFst s) + retainedMass F (pairFst s) + 1
noncomputable def coordinateDegree (F : Inputs) (s : List Bool) : ℕ :=
  ProjectiveValueGram.dimension (FlatAffineEndpointFiniteFrame.arity F s)
    (AffineRingCoordinates.width (FlatAffineEndpointFiniteFrame.degrees F s)) + 1
noncomputable def coordinateExponent (F : Inputs) (s : List Bool) : ℕ :=
  ProjectiveValueGram.massExponent (FlatAffineEndpointFiniteFrame.arity F s)
    (AffineRingCoordinates.width (FlatAffineEndpointFiniteFrame.degrees F s)) (integerExponent F s)
noncomputable def heightBound (F : Inputs) (s : List Bool) : ℕ := coordinateExponent F s + 1

theorem rowDegree_binary {F : Inputs} (h : F.Access) : BinaryFn (rowDegree F) :=
  ((FlatAffineEndpointFiniteFrame.degree_binary.add (FlatAffineEndpointPreparation.degree_binary.comp pairFst_mem_FP)).add
    ((FlatAffineFullSourceTower.degree_binary h).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))).add (BinaryFn.const 1)

theorem retainedMass_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) : BinaryFn (retainedMass F) :=
  (FlatAffineEndpointExceptional.massBound_binary h height).add
    ((FlatAffineEndpointExceptional.degreeBound_binary h height).size.add (FlatAffineEndpointExceptional.massBound_binary h height))

theorem integerExponent_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) : BinaryFn (integerExponent F) := by
  have hp : BinaryFn (fun s => FlatAffineEndpointValueBounds.integerExponent F (pairFst s)) :=
    (FlatAffineEndpointValueBounds.integerExponent_binary h height).comp pairFst_mem_FP
  have he : BinaryFn (fun s => retainedMass F (pairFst s)) := (retainedMass_binary h height).comp pairFst_mem_FP
  exact (hp.add he).add (BinaryFn.const 1)

theorem coordinateDegree_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) : BinaryFn (coordinateDegree F) :=
  (FlatAffineEndpointFiniteGram.family F height (zero F)).coordinateDegree_binary (FlatAffineEndpointFiniteFrame.arity_unary h)
    (FlatAffineEndpointFiniteDegree.degree_binary h) (FlatAffineEndpointFiniteGram.width_eq F height (zero F))

theorem coordinateExponent_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) : BinaryFn (coordinateExponent F) := by
  have hn := (FlatAffineEndpointFiniteGram.family F height (zero F)).parameter.affine.homogeneous.dimension_binary
    (FlatAffineEndpointFiniteGram.controls h height (zero F))
  have hb := integerExponent_binary h height
  exact (hn.size.mul hn).add (hn.mul (hn.size.add ((BinaryFn.const 2).mul (hb.add (BinaryFn.const 1)))))

theorem heightBound_binary {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u)) : BinaryFn (heightBound F) :=
  (coordinateExponent_binary h height).add (BinaryFn.const 1)

private theorem frozen_degree_le {n m : ℕ} (d : Fin n → ℕ) (e B : ℕ) (hd : ∀ i, d i ≤ B)
    (i : Fin (m * n + 1)) : FrozenAffineCopies.degrees d e i ≤ e + B := by
  refine Fin.cases (by change e ≤ e + B; omega) (fun j => ?_) i
  exact (hd (finProdFinEquiv.symm j).2).trans (by omega)

theorem mixed_degree_le (F : Inputs) (s : List Bool) (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) :
    FlatAffineEndpointFiniteFrame.degrees F s i ≤ rowDegree F s := by
  have hInner := frozen_degree_le (m := 3) (FlatAffinePowerPositive.degree F (pairFst (pairFst s)))
    (FlatAffineEndpointPreparation.degree (pairFst s)) (FlatAffineFullSourceTower.degree F (pairFst (pairFst s)))
    (FlatAffinePowerPositive.degree_le F (pairFst (pairFst s)))
  have H := frozen_degree_le (m := 1) (FlatAffineEndpointPreparation.degrees F (pairFst s))
    (FlatAffineEndpointFiniteFrame.degree s)
    (FlatAffineEndpointPreparation.degree (pairFst s) + FlatAffineFullSourceTower.degree F (pairFst (pairFst s))) hInner i
  exact H.trans (by dsimp only [rowDegree]; omega)

theorem row_degree_le (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s) (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) :
    (FlatAffineEndpointFiniteFrame.system F height s i).totalDegree ≤ rowDegree F s :=
  (FlatAffineEndpointFiniteFrame.degree_bound F height s hs i).trans (mixed_degree_le F s i)

theorem retained_mass (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) :
    coefficientMass (FlatAffineEndpointFiniteFrame.retained F height r) ≤ 2 ^ retainedMass F r :=
  (FlatAffineEndpointSamples.source F hcone height).mass_bound r

theorem integer_mass (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) :
    MvMass.mass (FlatAffineEndpointFiniteFrame.system F height s i) ≤ 2 ^ integerExponent F s :=
  FrozenAffineCopies.system_mass _ _ _ _ _ _ (FlatAffineEndpointValueBounds.integer_mass_bound F height (pairFst s))
    (retained_mass F hcone height (pairFst s)) i

theorem source_mass (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) (e : Fin (FlatAffineEndpointFiniteFrame.arity F s) →₀ ℕ) :
    coefficientMass ((AffineConstantParameterShift.system (FlatAffineEndpointFiniteFrame.system F height s) (fun _ => 0) i).coeff e) ≤
      2 ^ integerExponent F s := by
  rw [AffineConstantParameterShift.coefficient]
  simpa only [ite_self, sub_zero, coefficientMass_C] using
    (MvMass.coeff_le (FlatAffineEndpointFiniteFrame.system F height s i) e).trans (integer_mass F hcone height s i)

theorem coordinate_mass (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) :
    NestedMass.mass (FlatAffineEndpointFiniteGram.coordinate F height s i) ≤ 2 ^ coordinateExponent F s := by
  change NestedMass.mass (AffineRingGramEliminant.annihilator
    (AffineRingCoordinates.homogeneousRows (AffineConstantParameterShift.system (FlatAffineEndpointFiniteFrame.system F height s)
      (fun _ => 0)) (FlatAffineEndpointFiniteFrame.degrees F s)) (FlatAffineEndpointFiniteFrame.degrees F s)
      (AffineRingCoordinates.width (FlatAffineEndpointFiniteFrame.degrees F s)) i.succ) ≤ _
  rw [← AffineParameterCoordinateBits.coordinate_value_eq]
  apply ProjectiveValueGram.annihilator_mass_le_two_pow
  · intro j e
    exact AffineValueGramBits.homogenized_mass_bound _ _ _ (source_mass F hcone height s j) e
  · intro e
    simp only [MvPolynomial.coeff_X]
    split_ifs
    · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ 2 ^ integerExponent F s
      rw [coefficientMass_C]
      exact Nat.one_le_pow _ _ (by decide)
    · simp

theorem annihilator_degree (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) :
    (FlatAffineEndpointFiniteGram.annihilator F height s i).natDegree ≤ coordinateDegree F s := by
  apply Polynomial.natDegree_map_le.trans
  exact Geometry.AffineShiftCoordinates.coordinate_degree_le _ _ _ i

theorem annihilator_height (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (i : Fin (FlatAffineEndpointFiniteFrame.arity F s)) (k : ℕ) :
    ((FlatAffineEndpointFiniteGram.annihilator F height s i).coeff k).natAbs.size ≤ heightBound F s := by
  have hm := ((coeff_natAbs_le_coefficientMass ((FlatAffineEndpointFiniteGram.coordinate F height s i).coeff k) 0).trans
    ((NestedMass.coeff_le _ _).trans (coordinate_mass F hcone height s i)))
  have H := Nat.size_le_size hm
  rw [FlatAffineEndpointFiniteGram.annihilator, Polynomial.coeff_map]
  change (((FlatAffineEndpointFiniteGram.coordinate F height s i).coeff k).coeff 0).natAbs.size ≤ heightBound F s
  simpa only [heightBound, Nat.size_pow] using H

end LeanCanny.Encoding.FlatAffineEndpointFiniteBounds
