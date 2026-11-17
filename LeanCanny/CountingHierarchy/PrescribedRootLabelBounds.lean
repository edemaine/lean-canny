/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FingerprintLabelBounds
public import LeanCanny.CountingHierarchy.CoordinateFingerprintSelection

/-! # Source-only budgets for all bounded prescribed-root labels -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped BigOperators Classical

def fingerprintWeightBudget (D : ℕ) : ℕ := D * (2 * (D ^ 3 + 2))

def prescribedRootLabelDegreeBound (D b : ℕ) : ℕ :=
  fingerprintLabelDegreeBound D (algebraicTestPrecision D D b (derivativeTestMassExponent D b))
    (16 * (1 + fingerprintWeightBudget D)) D

def prescribedRootLabelMassExponent (D b : ℕ) : ℕ :=
  fingerprintLabelMassExponent D (algebraicTestPrecision D D b (derivativeTestMassExponent D b))
    (16 * (1 + fingerprintWeightBudget D)) (derivativeTestMassExponent D b) (fingerprintWeightBudget D)

theorem fingerprintTests_bounds (p b₀ : Polynomial ℤ) (D b : ℕ)
    (hD : p.natDegree ≤ D) (hb₀ : b₀.natDegree ≤ D)
    (hpm : coefficientMass p ≤ 2 ^ b) (hb₀m : coefficientMass b₀ ≤ 2 ^ b)
    (i : Fin (D + 1)) : (fingerprintTests p b₀ D i).natDegree ≤ D ∧
      coefficientMass (fingerprintTests p b₀ D i) ≤ 2 ^ derivativeTestMassExponent D b := by
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨hb₀, hb₀m.trans (Nat.pow_le_pow_right (by decide) ?_)⟩
    unfold derivativeTestMassExponent
    omega
  · exact ⟨(Polynomial.natDegree_iterate_derivative p _).trans ((Nat.sub_le _ _).trans hD),
      iterated_derivative_mass_le p D b hD hpm _⟩

/-- Both budgets depend only on the source degree and mass, uniformly over
all allowed fingerprint triples and independently of their separating behavior. -/
theorem fingerprintIntegerRootLabel_bounds (p b₀ : Polynomial ℤ) (D b : ℕ)
    (L : FingerprintLabelData) (hL : L.Bounded D)
    (hD : p.natDegree ≤ D) (hb₀ : b₀.natDegree ≤ D)
    (hpm : coefficientMass p ≤ 2 ^ b) (hb₀m : coefficientMass b₀ ≤ 2 ^ b) :
    (fingerprintIntegerRootLabel p b₀ D b L.modulus L.parameter L.target).natDegree ≤
        prescribedRootLabelDegreeBound D b ∧
      coefficientMass (fingerprintIntegerRootLabel p b₀ D b L.modulus L.parameter L.target) ≤
        2 ^ prescribedRootLabelMassExponent D b := by
  have hmu : 0 < L.modulus := by have := hL.1; omega
  have hW : D * L.modulus ≤ fingerprintWeightBudget D := Nat.mul_le_mul_left D hL.2.1
  have hs : 16 * (1 + D * L.modulus) ≤ 16 * (1 + fingerprintWeightBudget D) := by omega
  have hw : ∑ i : Fin D, fingerprintWeight L.modulus L.parameter i.val ≤ fingerprintWeightBudget D := by
    calc
      _ ≤ ∑ _i : Fin D, L.modulus := Finset.sum_le_sum (fun i _ => (Nat.mod_lt _ hmu).le)
      _ = D * L.modulus := by simp
      _ ≤ _ := hW
  have ht : L.target.natAbs ≤ fingerprintWeightBudget D := hL.2.2.2.trans hW
  have htests := fingerprintTests_bounds p b₀ D b hD hb₀ hpm hb₀m
  let B := algebraicTestPrecision D D b (derivativeTestMassExponent D b)
  let s := 16 * (1 + D * L.modulus)
  have hd := fingerprintLabelPolynomial_degree_le B s D (derivativeTestMassExponent D b)
    (fingerprintTests p b₀ D) (fun i => fingerprintWeight L.modulus L.parameter i.val) L.target
    (fun i => (htests i).1) (fun i => (htests i).2)
  have hm := fingerprintLabelPolynomial_mass_le B s D (derivativeTestMassExponent D b) (fingerprintWeightBudget D)
    (fingerprintTests p b₀ D) (fun i => fingerprintWeight L.modulus L.parameter i.val) L.target
    (fun i => (htests i).1) (fun i => (htests i).2) hw ht
  constructor
  · apply hd.trans
    unfold prescribedRootLabelDegreeBound fingerprintLabelDegreeBound signTestDegreeBound
    gcongr
  · apply hm.trans
    apply Nat.pow_le_pow_right (by decide)
    unfold prescribedRootLabelMassExponent fingerprintLabelMassExponent signTestMassExponent
    gcongr

end LeanCanny.CountingHierarchy
