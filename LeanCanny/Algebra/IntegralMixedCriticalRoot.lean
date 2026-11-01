/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistory
/-! # Actual selected roots and fixed-degree bounds for ordinary mixed critical births -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCriticalRoot
open IntegralMixedHistory MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def objective (r : CriticalRule n) : Fin (n-r.offset.val+1) :=
  ⟨r.objective % (n-r.offset.val+1), Nat.mod_lt _ (by omega)⟩
def coordinate (r : CriticalRule n) : Fin (n-r.offset.val+1) :=
  ⟨r.coordinate % (n-r.offset.val+1), Nat.mod_lt _ (by omega)⟩
theorem fit (r : CriticalRule n) : r.offset.val+(n-r.offset.val+1)=n+1 := by have H := r.offset.isLt; omega

theorem equation (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) :
    criticalPolynomial x hm r = CoordinateFrozenCriticalElimination.polynomial P.degree (data x hm r).scales (data x hm r).heights
      r.offset.val (fit r) (P.low.map (Int.castRingHom x.sampler.scalarPrefix.carrier)) (P.leading : x.sampler.scalarPrefix.carrier)
      (objective r) (coordinate r) := IntegralHistoryCriticalBits.annihilator_eq (family x hm r) []

theorem integer_eval (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (p : MvPolynomial (Fin (n+1)) ℤ) (y : Fin (n+1) → ℝ) :
    (p.map (Int.castRingHom x.sampler.scalarPrefix.carrier)).eval₂ φ.toRingHom y = p.eval₂ (Int.castRingHom ℝ) y := by
  rw [eval₂_map]
  have H : φ.toRingHom.comp (Int.castRingHom x.sampler.scalarPrefix.carrier) = Int.castRingHom ℝ := RingHom.ext_int _ _
  rw [H]

theorem root (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (y : Fin (n+1) → ℝ)
    (hf : ∀ i, i.val < r.offset.val → ((data x hm r).scales i : ℝ) * y i = φ ((data x hm r).heights i))
    (hp : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y = 0)
    (hg : ∀ j : Fin (n-r.offset.val+1), j ≠ objective r →
      (pderiv (ClearedCoordinateCritical.freeIndex r.offset.val (fit r).le j)
        (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) y = 0) :
    (criticalPolynomial x hm r).eval₂ φ.toRingHom (y (ClearedCoordinateCritical.freeIndex r.offset.val (fit r).le (coordinate r))) = 0 := by
  rw [equation]
  have HE : FermatCriticalHomogenization.polynomial (P.low.map (Int.castRingHom x.sampler.scalarPrefix.carrier))
      (P.leading : x.sampler.scalarPrefix.carrier) P.degree =
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).map (Int.castRingHom x.sampler.scalarPrefix.carrier) :=
    (FermatCriticalHomogenization.map_polynomial _ _ _ _).symm
  apply CoordinateFrozenCriticalElimination.root φ.toRingHom P.degree P.degree_two (data x hm r).scales
    (data x hm r).scales_ne (data x hm r).heights r.offset.val (fit r) _ _
    ((PolynomialMapDegree.degree_le _ P.low).trans_lt P.low_degree) (objective r) y hf
  · rw [HE, integer_eval]
    exact hp
  · intro j hj
    rw [HE, pderiv_map, integer_eval]
    exact hg j hj

theorem selected_degree (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    ((criticalPolynomial x hm r).map φ.toRingHom).natDegree = criticalDegree x hm r := by
  rw [equation]
  apply CoordinateFrozenCriticalElimination.specialized_degree φ.toRingHom P.degree
    (by have H := P.degree_two; omega) (data x hm r).scales (data x hm r).scales_ne (data x hm r).heights
    r.offset.val (fit r) _ _ _ (objective r) (coordinate r)
  rw [map_intCast]
  exact Int.cast_ne_zero.mpr P.leading_ne_zero

theorem selected_nonzero (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) : (criticalPolynomial x hm r).map φ.toRingHom ≠ 0 := by
  intro HZ
  have HD := selected_degree x hm r φ
  rw [HZ, Polynomial.natDegree_zero] at HD
  have HP : 0 < criticalDegree x hm r := pow_pos (Nat.two_pow_pos _) _
  omega

theorem selected_degree_cap (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) : ((criticalPolynomial x hm r).map φ.toRingHom).natDegree ≤ 2^B := by
  rw [selected_degree]
  exact criticalDegree_cap x hm r

theorem finite_roots (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) : {t : ℝ | (criticalPolynomial x hm r).eval₂ φ.toRingHom t = 0}.Finite := by
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using Polynomial.finite_setOfPred_isRoot (selected_nonzero x hm r φ)

end LeanCanny.Algebra.IntegralMixedCriticalRoot
