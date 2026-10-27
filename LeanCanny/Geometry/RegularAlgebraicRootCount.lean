/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SquareSystemFinite
public import LeanCanny.Geometry.RegularAffineRootCount

/-! # Bounded regular roots over algebraically closed characteristic-zero fields

Algebraic finiteness supplies the premise for the existing bounded coordinate
eliminants. Their degrees bound the complete root set, including nonreal
solutions. No analytic regularity test or finite-root oracle is assumed.
-/

@[expose] public section
namespace LeanCanny.Geometry.RegularAlgebraicRootCount
open MvPolynomial LeanCanny.Algebra
open scoped Classical BigOperators

variable {n : ℕ} {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

abbrev Roots (q : Fin n → MvPolynomial (Fin n) ℤ) :=
  {x : Fin n → K // ∀ j, (q j).eval₂ (Int.castRingHom K) x = 0}

theorem map_jacobian {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (q : Fin n → MvPolynomial (Fin n) R) :
    (JacobianKernelCharts.jacobian q).map φ = JacobianKernelCharts.jacobian (fun j => (q j).map φ) := by
  unfold JacobianKernelCharts.jacobian
  rw [(MvPolynomial.map φ).map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, pderiv_map]

omit [IsAlgClosed K] in
theorem finite_roots (q : Fin n → MvPolynomial (Fin n) ℤ)
    (hregular : ∀ x : Roots (K := K) q, (JacobianKernelCharts.jacobian q).eval₂ (Int.castRingHom K) x.val ≠ 0) :
    {x : Fin n → K | ∀ j, (q j).eval₂ (Int.castRingHom K) x = 0}.Finite := by
  have H := SquareSystemFinite.finite_roots_of_regular (fun j => (q j).map (Int.castRingHom K)) (by
    intro x hx
    rw [← map_jacobian]
    simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, eval₂_map, RingHom.id_comp] using
      hregular ⟨x, by simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, eval₂_map, RingHom.id_comp] using hx⟩)
  simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, eval₂_map, RingHom.id_comp] using H

theorem finite_card_le (q : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j)
    (hregular : ∀ x : Roots (K := K) q, (JacobianKernelCharts.jacobian q).eval₂ (Int.castRingHom K) x.val ≠ 0) :
    Finite (Roots (K := K) q) ∧ Nat.card (Roots (K := K) q) ≤ UniformAffineCoordinates.count d ^ n := by
  let P := fun i => (AffineCoordinateEliminant.polynomial q d i (UniformAffineCoordinates.width d)).map (Int.castRingHom K)
  have hP (i : Fin n) : P i ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr (AffineCoordinateEliminant.ne_zero _ _ _ _)
  have hzero (x : Roots (K := K) q) (i : Fin n) : (P i).eval (x.val i) = 0 := by
    rw [Polynomial.eval_map]
    exact AffineCoordinateEliminant.eval_eq_zero_of_finite (Int.castRingHom K) q d hD hd i
      (UniformAffineCoordinates.width d) (Nat.lt_size_self _) (finite_roots q hregular) x.val x.property
  let R := fun i : Fin n => {x : K // x ∈ (P i).roots.toFinset}
  let enc : Roots (K := K) q → ∀ i, R i := fun x i =>
    ⟨x.val i, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hP i)).mpr (hzero x i))⟩
  have hinj : Function.Injective enc := by
    intro x y he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  have hfin : Finite (Roots (K := K) q) := Finite.of_injective enc hinj
  refine ⟨hfin, (Nat.card_le_card_of_injective enc hinj).trans ?_⟩
  rw [Nat.card_pi]
  calc
    _ ≤ ∏ i : Fin n, (P i).natDegree := by
      apply Finset.prod_le_prod
      intro i _
      change Nat.card {x : K // x ∈ (P i).roots.toFinset} ≤ _
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
    _ ≤ ∏ _i : Fin n, UniformAffineCoordinates.count d := Finset.prod_le_prod (fun i _ =>
      Polynomial.natDegree_map_le.trans (AffineCoordinateEliminant.degree_le _ _ _ _))
    _ = _ := by simp

theorem finite_card_le_uniform (q : Fin n → MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ D) (hpos : 0 < D)
    (hregular : ∀ x : Roots (K := K) q, (JacobianKernelCharts.jacobian q).eval₂ (Int.castRingHom K) x.val ≠ 0) :
    Finite (Roots (K := K) q) ∧ Nat.card (Roots (K := K) q) ≤ 2 ^ RegularAffineRootCount.labelWidth n D := by
  simpa only [RegularAffineRootCount.count_uniform] using finite_card_le q (fun _ => D) hD (fun _ => hpos) hregular

end LeanCanny.Geometry.RegularAlgebraicRootCount
