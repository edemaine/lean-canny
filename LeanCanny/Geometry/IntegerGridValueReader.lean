/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerGridValueGramSpace
public import LeanCanny.Geometry.IntegerGridValueCertificate

/-! # Correctness of native coordinate-grid value readers

The polynomial computed from the original coordinate and test readers
annihilates every grid test value. Exact positive coordinate degrees ensure
nonvanishing; the test may use any positive degree allowance. Coordinate
specializations may have multiple roots or degree drops.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerGridValueGramBits
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem Family.eval_eq_zero (F : Family) (c : List Bool) {K : Type*} [Field K]
    (rho : Polynomial ℤ →+* K) (x : Fin (F.arity c) → K)
    (hp : ∀ i, (F.coordinate c i).natDegree ≤ F.degree c i.val)
    (hq : (F.test c).totalDegree ≤ F.testDegree c)
    (hW : F.affine.homogeneous.layout.level c < 2 ^ F.width c)
    (hx : ∀ i, (F.coordinate c i).eval₂ rho (x i) = 0) :
    (F.affine.homogeneous.annihilator c).eval₂ rho ((F.test c).eval₂ rho x) = 0 := by
  refine F.affine.eval_eq_zero c rho x ?_ hq hW ?_
  · intro i
    exact (UnivariateInfinity.degree_le (F.coordinate c i) i).trans (hp i)
  · intro i
    exact (Geometry.UnivariateRootFamily.eval _ _ _ _).trans (hx i)

theorem Family.ne_zero (F : Family) (c : List Bool)
    (hd : ∀ i : Fin (F.arity c), F.degree c i.val = (F.coordinate c i).natDegree)
    (hp : ∀ i, 0 < (F.coordinate c i).natDegree) (he : 0 < F.testDegree c)
    (hW : F.affine.homogeneous.layout.level c < 2 ^ F.width c) :
    F.affine.homogeneous.annihilator c ≠ 0 := by
  have hn (i : Fin (F.arity c)) : F.coordinate c i ≠ 0 := by
    intro hz
    have hi := hp i
    rw [hz, Polynomial.natDegree_zero] at hi
    omega
  obtain ⟨t, ht⟩ := Geometry.IntegerGridValueCertificate.exists_leading_specialization (F.coordinate c) hn
  apply F.affine.ne_zero c (fun i => by
    change 0 < F.degree c i.val
    rw [hd i]
    exact hp i) he hW
    (SymbolicScaledSquarefree.scalarEvaluation t)
  have hd' : (fun i : Fin (F.arity c) => F.degree c i.val) =
      (fun i => (F.coordinate c i).natDegree) := funext hd
  change AffineRingCoordinates.NoInfinity _ (fun i => (F.coordinate c i).toMvPolynomial i)
    (fun i : Fin (F.arity c) => F.degree c i.val)
  rw [hd']
  apply UnivariateInfinity.noInfinity (F.coordinate c) hp
  intro i hi
  exact ht i (Complex.ofReal_injective hi)

end LeanCanny.Algebra.IntegerGridValueGramBits
