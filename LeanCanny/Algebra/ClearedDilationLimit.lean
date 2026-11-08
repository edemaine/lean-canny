/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ClearedDilatedCoordinatePolynomial
public import LeanCanny.Algebra.DeformationLowestCoefficient
public import Mathlib.Topology.Algebra.Polynomial

/-! # Selected-parent limit coordinates after denominator-cleared dilation

Specialize the coefficient parent first, then select its first surviving E
coefficient. The universal first coefficient need not survive that parent.
All possible selected coefficients lie in the original finite degree range.
-/
@[expose] public section
namespace LeanCanny.Algebra.ClearedDilationLimit
open Polynomial Filter
open scoped Topology
variable {R : Type*} [CommRing R]

theorem swap_eval {S : Type*} [CommRing S] (φ : R →+* S)
    (p : Polynomial (Polynomial R)) (e x : S) :
    eval₂ (eval₂RingHom φ x) e (Bivariate.swap p) = eval₂ (eval₂RingHom φ e) x p := by
  have HC : (eval₂RingHom φ x).comp C = φ := by ext r; simp
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,eval₂_add,hp,hq]
  | monomial n a =>
      simp only [Bivariate.swap_monomial,eval₂_mul,eval₂_map,HC,eval₂_C,eval₂_monomial]
      simp only [coe_eval₂RingHom,eval₂_pow,eval₂_X]

noncomputable def selected (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q : R) :
    Polynomial (Polynomial ℝ) :=
  (Bivariate.swap (ClearedDilatedCoordinatePolynomial.rescale p q)).map (mapRingHom φ)

theorem selected_value (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q : R) (e x : ℝ) :
    eval₂ (evalRingHom x) e (selected φ p q) =
      eval₂ (eval₂RingHom φ e) x (ClearedDilatedCoordinatePolynomial.rescale p q) := by
  have HC : (evalRingHom x).comp (mapRingHom φ) = eval₂RingHom φ x := by
    ext r
    · simp [RingHom.comp_apply,coe_mapRingHom]
    · simp [RingHom.comp_apply,coe_mapRingHom]
  rw [selected,eval₂_map,HC,swap_eval]

theorem top_coefficient (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q a : R)
    (hd : p.coeff p.natDegree = C a) :
    ((selected φ p q).coeff p.natDegree).coeff p.natDegree = φ a := by
  rw [selected,coeff_map,coe_mapRingHom,coeff_map,ClearedDilatedCoordinatePolynomial.swapped_coefficient,
    ite_eq_left (Nat.le_refl _),Nat.sub_self,hd,coeff_C_zero,pow_zero,mul_one]

theorem selected_ne_zero (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q a : R)
    (ha : φ a≠0) (hd : p.coeff p.natDegree = C a) : selected φ p q≠0 := by
  intro HZ
  have H := top_coefficient φ p q a hd
  rw [HZ,coeff_zero,coeff_zero] at H
  exact ha H.symm

theorem index_le (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q a : R)
    (ha : φ a≠0) (hd : p.coeff p.natDegree = C a) :
    (selected φ p q).natTrailingDegree ≤ p.natDegree := by
  apply natTrailingDegree_le_of_ne_zero
  intro HZ
  have H := congrArg (fun f : Polynomial ℝ => f.coeff p.natDegree) HZ
  rw [top_coefficient φ p q a hd,coeff_zero] at H
  exact ha H

noncomputable def coordinate (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q : R) : Polynomial ℝ :=
  (selected φ p q).trailingCoeff

theorem coordinate_ne_zero (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q a : R)
    (ha : φ a≠0) (hd : p.coeff p.natDegree = C a) : coordinate φ p q≠0 :=
  trailingCoeff_ne_zero.mpr (selected_ne_zero φ p q a ha hd)

theorem coordinate_eq_coefficient (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q : R) :
    coordinate φ p q =
      ((Bivariate.swap (ClearedDilatedCoordinatePolynomial.rescale p q)).coeff
        (selected φ p q).natTrailingDegree).map φ := by
  rw [coordinate,trailingCoeff,selected,coeff_map,coe_mapRingHom]

theorem coordinate_degree (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q a : R)
    (ha : φ a≠0) (hd : p.coeff p.natDegree = C a) :
    (coordinate φ p q).natDegree ≤ p.natDegree := by
  rw [coordinate_eq_coefficient]
  exact natDegree_map_le.trans ((ClearedDilatedCoordinatePolynomial.coefficient_degree p q _).trans
    (index_le φ p q a ha hd))

theorem limit_root {I : Type*} (l : Filter I) [NeBot l]
    (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q : R)
    (eta y x : I → ℝ) (a : ℝ) (heta : Tendsto eta l (𝓝 0)) (hx : Tendsto x l (𝓝 a))
    (hne : ∀ᶠ i in l, eta i≠0)
    (hy : ∀ᶠ i in l, φ q*y i=eta i*x i)
    (hp : ∀ᶠ i in l, eval₂ (eval₂RingHom φ (eta i)) (y i) p=0) :
    (coordinate φ p q).eval a=0 := by
  apply DeformationLowestCoefficient.trailingCoeff_eq_zero_of_tendsto (selected φ p q)
    (fun z => evalRingHom z) (fun r => r.continuous) l x eta a hx heta hne
  filter_upwards [hy,hp] with i hiy hip
  rw [selected_value]
  exact ClearedDilatedCoordinatePolynomial.root φ p q (eta i) (y i) (x i) hiy hip

end LeanCanny.Algebra.ClearedDilationLimit
