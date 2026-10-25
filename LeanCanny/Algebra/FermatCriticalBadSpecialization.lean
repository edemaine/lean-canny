/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalBadSystem
public import LeanCanny.Algebra.PolynomialCoefficientDegree

/-! # The homogeneous bad-root system in a fixed direction

Specializing the direction variables gives the homogenized spatial critical
equations and their actual spatial Jacobian. This operation is compatible
with coefficient maps and retains explicit sweep-parameter degree bounds.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatCriticalBadSpecialization
open MvPolynomial FermatCriticalHomogenization FermatCriticalBadSystem
open scoped Classical Matrix
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

noncomputable def jacobian (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) (v : Fin n → R) :
    MvPolynomial (Fin (n + 1)) R := Matrix.det (fun i j => pderiv j (spatial low a N v i))

noncomputable def rows (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) (v : Fin n → R)
    (j : Fin (n + 2)) : MvPolynomial (Fin (n + 2)) R :=
  rename layout (HomogeneousBadSystem.rows (spatial low a N v) (FermatCriticalInfinity.degrees n N)
    (jacobian low a N v) (jacobianDegree n N) (layout.symm j))

theorem homogeneous (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) (v : Fin n → R)
    (j : Fin (n + 2)) : (rows low a N v j).IsHomogeneous (nativeDegrees n N j) :=
  (HomogeneousBadSystem.homogeneous _ _ _ _ (layout.symm j)).rename_isHomogeneous

theorem map_jacobian (φ : R →+* S) (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (v : Fin n → R) : (jacobian low a N v).map φ = jacobian (low.map φ) (φ a) N (fun i => φ (v i)) := by
  rw [jacobian, RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change (pderiv j (spatial low a N v i)).map φ = _
  rw [← pderiv_map, map_spatial]

theorem map_rows (φ : R →+* S) (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (v : Fin n → R) (j : Fin (n + 2)) :
    (rows low a N v j).map φ = rows (low.map φ) (φ a) N (fun i => φ (v i)) j := by
  rw [rows, MvPolynomial.map_rename]
  apply congrArg (rename layout)
  cases h : layout.symm j <;>
    simp only [HomogeneousBadSystem.rows, WeightedHomogenization.map_homogenize, map_jacobian, map_spatial]

theorem specialize_equations (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (v : Fin n → R) (j : Fin (n + 1)) :
    (FermatCriticalBadSystem.equations low a N j).map (eval₂Hom (RingHom.id R) v) = spatial low a N v j := by
  let φ := eval₂Hom (RingHom.id R) v
  have hc : φ.comp C = RingHom.id R := by ext; simp [φ]
  rw [equations, map_spatial, map_map, hc, map_id]
  simp only [eval₂Hom_C, RingHom.id_apply, eval₂Hom_X']

theorem specialize_jacobian (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (v : Fin n → R) :
    (FermatCriticalBadSystem.jacobian low a N).map (eval₂Hom (RingHom.id R) v) = jacobian low a N v := by
  rw [FermatCriticalBadSystem.jacobian, RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change (pderiv j (equations low a N i)).map (eval₂Hom (RingHom.id R) v) = _
  rw [← pderiv_map, specialize_equations]

theorem specialize_rows (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ)
    (v : Fin n → R) (j : Fin (n + 2)) :
    (nativeRows low a N j).map (eval₂Hom (RingHom.id R) v) = rows low a N v j := by
  rw [nativeRows, MvPolynomial.map_rename]
  apply congrArg (rename layout)
  cases h : layout.symm j <;>
    simp only [FermatCriticalBadSystem.rows, HomogeneousBadSystem.rows,
      WeightedHomogenization.map_homogenize, specialize_jacobian, specialize_equations]

theorem spatial_parameter_degree (low : MvPolynomial (Fin (n + 1)) (Polynomial R))
    (a : R) (N E : ℕ) (hlow : PolynomialCoefficientDegree.Bound low E)
    (v : Fin n → R) (j : Fin (n + 1)) :
    PolynomialCoefficientDegree.Bound (spatial low (Polynomial.C a) N (fun i => Polynomial.C (v i)) j) E := by
  have hpow (i : Fin (n + 1)) : PolynomialCoefficientDegree.Bound
      (C (Polynomial.C a) * X i ^ N : MvPolynomial (Fin (n + 1)) (Polynomial R)) 0 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using PolynomialCoefficientDegree.mul
      (PolynomialCoefficientDegree.C (show (Polynomial.C a).natDegree ≤ 0 by simp))
      (PolynomialCoefficientDegree.pow (PolynomialCoefficientDegree.X i) N)
  have hp : PolynomialCoefficientDegree.Bound (polynomial low (Polynomial.C a) N) E := by
    apply PolynomialCoefficientDegree.add hlow
    rw [Finset.mul_sum]
    exact PolynomialCoefficientDegree.mono (PolynomialCoefficientDegree.sum _ _ _ fun i _ => hpow i) (Nat.zero_le E)
  refine Fin.cases hp (fun i => ?_) j
  apply PolynomialCoefficientDegree.sub (PolynomialCoefficientDegree.pderiv hp i.succ)
  simpa only [Nat.zero_add] using PolynomialCoefficientDegree.mul
    (PolynomialCoefficientDegree.C (show (Polynomial.C (v i)).natDegree ≤ 0 by simp))
    (PolynomialCoefficientDegree.pderiv hp 0)

theorem parameter_degree (low : MvPolynomial (Fin (n + 1)) (Polynomial R))
    (a : R) (N E : ℕ) (hlow : PolynomialCoefficientDegree.Bound low E)
    (v : Fin n → R) (j : Fin (n + 2)) :
    PolynomialCoefficientDegree.Bound (rows low (Polynomial.C a) N (fun i => Polynomial.C (v i)) j) ((n + 1) * E) := by
  have hsp := spatial_parameter_degree low a N E hlow v
  have hJ : PolynomialCoefficientDegree.Bound
      (jacobian low (Polynomial.C a) N (fun i => Polynomial.C (v i))) ((n + 1) * E) := by
    simpa only [jacobian, Fintype.card_fin] using PolynomialCoefficientDegree.det
      (fun i j => pderiv j (spatial low (Polynomial.C a) N (fun i => Polynomial.C (v i)) i)) E
      (fun i j => PolynomialCoefficientDegree.pderiv (hsp i) j)
  apply PolynomialCoefficientDegree.rename layout
  cases h : layout.symm j with
  | none => exact PolynomialCoefficientDegree.homogenize hJ _ _
  | some i =>
    exact PolynomialCoefficientDegree.mono (PolynomialCoefficientDegree.homogenize (hsp i) _ _)
      (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right E (show 1 ≤ n + 1 by omega))

end LeanCanny.Algebra.FermatCriticalBadSpecialization
