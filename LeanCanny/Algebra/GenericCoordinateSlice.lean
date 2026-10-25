/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinateSlicePolynomial
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Extension-field regularity of a generic coordinate slice

A critical point of a coordinate projection on a regular hypersurface has an
algebraic sweep value. A transcendental sweep value therefore leaves a regular
slice, over every extension field of the generic coefficient field.
-/

@[expose] public section
namespace LeanCanny.Algebra.GenericCoordinateSlice
open MvPolynomial CoordinateSlicePolynomial
open scoped Classical

universe u
variable {n : ℕ} {K F L : Type u} [Field K] [CharZero K] [Field F] [Field L]

theorem regular_of_transcendental [Algebra K L]
    (q : MvPolynomial (Fin (n + 1)) K) (t : L) (ht : Transcendental K t)
    (x : Fin n → L)
    (hq : (family q).eval₂ (Polynomial.eval₂RingHom (algebraMap K L) t) x = 0)
    (hregular : ∃ j, aeval (Fin.cons t x) (pderiv j q) ≠ 0) :
    ∃ i, (pderiv i (family q)).eval₂ (Polynomial.eval₂RingHom (algebraMap K L) t) x ≠ 0 := by
  by_contra hn
  have htail (i : Fin n) : aeval (Fin.cons t x) (pderiv i.succ q) = 0 := by
    have he : (pderiv i (family q)).eval₂ (Polynomial.eval₂RingHom (algebraMap K L) t) x = 0 := by
      by_contra hi
      exact hn ⟨i, hi⟩
    rwa [pderiv_family, eval_family] at he
  have hbase : aeval (Fin.cons t x) (pderiv 0 q) ≠ 0 := by
    obtain ⟨j, hj⟩ := hregular
    revert hj
    refine Fin.cases (fun hj => hj) (fun j hj => (hj (htail j)).elim) j
  apply ht
  have ha := CoordinateCriticalValues.algebraic_coordinate q 0 (Fin.cons t x)
    (by rwa [eval_family] at hq) hbase (fun j hj => ?_)
  · simpa only [Fin.cons_zero] using ha
  · revert hj
    refine Fin.cases (fun hj => (hj rfl).elim) (fun j _ => htail j) j

/-- Any injective realization of the polynomial sweep parameter supplies a
regular slice over all extensions of its coefficient field. -/
theorem regular [Algebra K F] (ψ : Polynomial K →+* F) (hψ : Function.Injective ψ)
    (hψC : ψ.comp Polynomial.C = algebraMap K F)
    (q : MvPolynomial (Fin (n + 1)) K)
    (hregular : ∀ (E : Type u) [Field E] [Algebra K E] (z : Fin (n + 1) → E),
      aeval z q = 0 → ∃ j, aeval z (pderiv j q) ≠ 0)
    [Algebra F L] (x : Fin n → L)
    (hx : aeval x ((family q).map ψ) = 0) :
    ∃ i, aeval x (pderiv i ((family q).map ψ)) ≠ 0 := by
  let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  let φ : Polynomial K →ₐ[K] L :=
    { toRingHom := (algebraMap F L).comp ψ
      commutes' := by
        intro a
        change algebraMap F L (ψ (Polynomial.C a)) = algebraMap F L (algebraMap K F a)
        exact congrArg (algebraMap F L) (congrArg (fun f : K →+* F => f a) hψC) }
  have hφ : Function.Injective φ := (algebraMap F L).injective.comp hψ
  have ht : Transcendental K (φ Polynomial.X) := by
    intro ha
    exact Polynomial.transcendental_X K ((isAlgebraic_algHom_iff φ hφ).mp ha)
  have hparam : Polynomial.eval₂RingHom (algebraMap K L) (φ Polynomial.X) = φ.toRingHom := by
    ext a
    · simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.algebraMap_eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using (φ.commutes a).symm
    · simp
  have heval (r : MvPolynomial (Fin (n + 1)) K) :
      aeval x ((family r).map ψ) = aeval (Fin.cons (φ Polynomial.X) x) r := by
    change eval₂ (algebraMap F L) x ((family r).map ψ) = _
    rw [eval₂_map]
    change (family r).eval₂ φ.toRingHom x = _
    rw [← hparam, eval_family]
    rfl
  have hroot : aeval (Fin.cons (φ Polynomial.X) x) q = 0 := by rwa [← heval]
  obtain ⟨i, hi⟩ := regular_of_transcendental q (φ Polynomial.X) ht x
    (by rwa [eval_family]) (hregular L _ hroot)
  refine ⟨i, ?_⟩
  change eval₂ (algebraMap F L) x (pderiv i ((family q).map ψ)) ≠ 0
  rw [pderiv_map, eval₂_map]
  change (pderiv i (family q)).eval₂ φ.toRingHom x ≠ 0
  rwa [← hparam]

theorem fractionField_regular (q : MvPolynomial (Fin (n + 1)) K)
    (hregular : ∀ (E : Type u) [Field E] [Algebra K E] (z : Fin (n + 1) → E),
      aeval z q = 0 → ∃ j, aeval z (pderiv j q) ≠ 0)
    [Algebra (FractionRing (Polynomial K)) L] (x : Fin n → L)
    (hx : aeval x ((family q).map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))) = 0) :
    ∃ i, aeval x (pderiv i ((family q).map (algebraMap (Polynomial K) (FractionRing (Polynomial K))))) ≠ 0 :=
  regular _ (IsFractionRing.injective _ _) (IsScalarTower.algebraMap_eq K (Polynomial K) _).symm
    q hregular x hx

end LeanCanny.Algebra.GenericCoordinateSlice
