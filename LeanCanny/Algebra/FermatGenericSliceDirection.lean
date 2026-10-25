/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GenericCoordinateSlice
public import LeanCanny.Algebra.FermatBoundedCriticalDirection

/-! # Bounded critical directions for the actual generic slice family

A regular pure-power leading hypersurface has a regular generic coordinate
slice of the same leading degree. The integer direction allowance therefore
applies to this family without a separate slice regularity assumption.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatGenericSliceDirection
open MvPolynomial FermatCriticalHomogenization
open scoped Classical

universe u
variable {n : ℕ} {K : Type u} [Field K] [CharZero K]

abbrev GenericField (K : Type u) [Field K] := FractionRing (Polynomial K)

noncomputable def lower (low : MvPolynomial (Fin (n + 2)) K) (a : K) (N : ℕ) :
    MvPolynomial (Fin (n + 1)) (GenericField K) :=
  (CoordinateSlicePolynomial.family low + C (Polynomial.C a * Polynomial.X ^ N)).map
    (algebraMap (Polynomial K) (GenericField K))

omit [CharZero K] in
theorem lower_degree (low : MvPolynomial (Fin (n + 2)) K) (a : K) (N : ℕ)
    (hlow : low.totalDegree < N) : (lower low a N).totalDegree < N :=
  (PolynomialMapDegree.degree_le _ _).trans_lt
    (CoordinateSlicePolynomial.fermat_lower_degree low a N hlow)

omit [CharZero K] in
theorem polynomial_eq (low : MvPolynomial (Fin (n + 2)) K) (a : K) (N : ℕ) :
    polynomial (lower low a N) (algebraMap K (GenericField K) a) N =
      (CoordinateSlicePolynomial.family (polynomial low a N)).map
        (algebraMap (Polynomial K) (GenericField K)) := by
  rw [CoordinateSlicePolynomial.family_fermat, map_polynomial]
  congr 1

theorem regular (low : MvPolynomial (Fin (n + 2)) K) (a : K) (N : ℕ)
    (hregular : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 2) → L),
      aeval x (polynomial low a N) = 0 → ∃ j, aeval x (pderiv j (polynomial low a N)) ≠ 0)
    (L : Type u) [Field L] [Algebra (GenericField K) L] (x : Fin (n + 1) → L)
    (hx : aeval x (polynomial (lower low a N) (algebraMap K (GenericField K) a) N) = 0) :
    ∃ j, aeval x (pderiv j (polynomial (lower low a N) (algebraMap K (GenericField K) a) N)) ≠ 0 := by
  rw [polynomial_eq] at hx ⊢
  exact GenericCoordinateSlice.fractionField_regular _ hregular x hx

theorem exists_bounded (low : MvPolynomial (Fin (n + 2)) K) (a : K) (ha : a ≠ 0)
    (N : ℕ) (hlow : low.totalDegree < N) (hN : 1 < N)
    (hregular : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 2) → L),
      aeval x (polynomial low a N) = 0 → ∃ j, aeval x (pderiv j (polynomial low a N)) ≠ 0) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ FermatBoundedCriticalDirection.allowance n N) ∧
      ∀ (L : Type u) [Field L] [Algebra (GenericField K) L] (x : Fin (n + 1) → L),
        (∀ j, (FermatCriticalBadSystem.equations (lower low a N) (algebraMap K (GenericField K) a) N j).eval₂
          (eval₂Hom (algebraMap (GenericField K) L) (fun i => (v i : L))) x = 0) →
        (FermatCriticalBadSystem.jacobian (lower low a N) (algebraMap K (GenericField K) a) N).eval₂
          (eval₂Hom (algebraMap (GenericField K) L) (fun i => (v i : L))) x ≠ 0 :=
  FermatBoundedCriticalDirection.exists_bounded (lower low a N) (algebraMap K (GenericField K) a)
    (fun hz => ha ((algebraMap K (GenericField K)).injective (hz.trans (map_zero _).symm)))
    N (lower_degree low a N hlow) hN (regular low a N hregular)

end LeanCanny.Algebra.FermatGenericSliceDirection
