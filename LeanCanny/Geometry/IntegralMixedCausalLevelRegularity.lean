/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCausalLevelCapacity
public import LeanCanny.Algebra.FermatLevelDerivative
public import LeanCanny.Algebra.IntegralMixedCanonicalDilationRoot

/-! # Causal level capacity makes the actual free objective derivative negative

The capacity exponent is chosen from the old bank before the new source. It
already exceeds the fixed Fermat degree, so every bounded level lift is regular
in its free objective direction. No Hessian or critical-curve regularity follows.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCausalLevelCapacity
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedRetainedRealBound
open IntegralMixedCanonicalDilation IntegralMixedCriticalSweep
open scoped Classical

theorem coefficient_gt_degree (n D R G : ℕ) :
    (FixedLeadingTiltedSource.degree D:ℝ)<(coefficient n D R G:ℝ) := by
  have HH : 1≤height R G := by unfold height; omega
  have HE : FixedLeadingTiltedSource.degree D≤exponent n D R G := by
    unfold exponent
    nlinarith
  have HN : FixedLeadingTiltedSource.degree D<2^exponent n D R G :=
    (FixedLeadingTiltedSource.degree D).lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) HE)
  have HZ : (FixedLeadingTiltedSource.degree D:ℤ)<coefficient n D R G := by
    unfold coefficient
    exact_mod_cast HN
  exact_mod_cast HZ

variable {n : ℕ}

theorem level_derivative_neg (k D R G : ℕ) (u : Fin n) (t : ETR.Term) (ht : t.degreeBound≤D)
    (x : Fin (n+1) → ℝ) (v : ℝ) (hv : v∈Set.Icc (-1:ℝ) 1) :
    (MvPolynomial.pderiv (Fin.last (n+1)) (FermatLevelLift.polynomial (FermatLevelLift.source
      (FixedLeadingTiltedSource.source k D u t ht) (coefficient n D R G)))).eval₂
      (Int.castRingHom ℝ) (Fin.snoc x v)<0 :=
  FermatLevelLift.eval_derivative_last_neg _ _ rfl (coefficient_gt_degree n D R G) x v hv

theorem level_gradient_ne_zero (k D R G : ℕ) (u : Fin n) (t : ETR.Term) (ht : t.degreeBound≤D)
    (x : Fin (n+1) → ℝ) (v : ℝ) (hv : v∈Set.Icc (-1:ℝ) 1) :
    (fun i => (MvPolynomial.pderiv i (FermatLevelLift.polynomial (FermatLevelLift.source
      (FixedLeadingTiltedSource.source k D u t ht) (coefficient n D R G)))).eval₂
      (Int.castRingHom ℝ) (Fin.snoc x v))≠0 := by
  intro H
  have HL := level_derivative_neg k D R G u t ht x v hv
  have HZ := congrFun H (Fin.last (n+1))
  change _=0 at HZ
  linarith

theorem canonical_objective_neg (k D R G : ℕ) (u : Fin n) (t : ETR.Term) (ht : t.degreeBound≤D)
    (hkn : k≤n) {m : ℕ} (select : Fin k → Fin m)
    (x : Fin (n+1) → ℝ) (v : ℝ) (hv : v∈Set.Icc (-1:ℝ) 1) :
    (MvPolynomial.pderiv
      (ClearedCoordinateCritical.freeIndex (rule hkn select).critical.offset.val (fit (rule hkn select)).le
        (objective (rule hkn select)))
      (FermatLevelLift.polynomial (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht)
        (coefficient n D R G)))).eval₂ (Int.castRingHom ℝ) (Fin.snoc x v)<0 := by
  rw [free_objective hkn select]
  exact level_derivative_neg k D R G u t ht x v hv

end LeanCanny.Geometry.IntegralMixedCausalLevelCapacity
