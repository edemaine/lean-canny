/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FermatSweepCertificate
public import LeanCanny.Algebra.FermatBadRootCharts

/-! # Explicit kernel and infinity queries for the sampled sweep certificate

Certificate validity is equivalent to emptiness of two finite families of
complex affine queries. The first uses a normalized kernel vector for the
actual sampled spatial Jacobian. The second uses only pure-power leading
equations and a normalized spatial coordinate.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatSweepCertificate
open MvPolynomial
open LeanCanny.Algebra
open scoped Classical Matrix

variable {n : ℕ}

noncomputable def sampleMap (n N : ℕ) (record : List Bool) : Polynomial ℚ →+* ℂ :=
  Polynomial.eval₂RingHom (algebraMap ℚ ℂ) (sample n N record : ℂ)

noncomputable def sampledDirection (n N : ℕ) (record : List Bool) : Fin n → Polynomial ℚ :=
  fun i => Polynomial.C (direction n N record i : ℚ)

noncomputable def criticalRows (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ) (N : ℕ) (record : List Bool) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial ℚ) :=
  FermatCriticalHomogenization.spatial (FermatBoundedSweepSample.lower low a N)
    (Polynomial.C a) N (sampledDirection n N record)

def AffineBad (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ) (N : ℕ) (record : List Bool)
    (i : Fin (n + 1)) : Prop :=
  ∃ x u : Fin (n + 1) → ℂ, u i = 1 ∧
    (∀ j, (criticalRows low a N record j).eval₂ (sampleMap n N record) x = 0) ∧
      JacobianKernelCharts.matrix (sampleMap n N record) (criticalRows low a N record) x *ᵥ u = 0

def InfinityBad (a : ℚ) (N : ℕ) (record : List Bool) (i : Fin (n + 1)) : Prop :=
  ∃ x : Fin (n + 1) → ℂ, x i = 1 ∧
    ∀ j, (FermatCriticalInfinity.native (Polynomial.C a) N (sampledDirection n N record) j).eval₂
      (sampleMap n N record) x = 0

theorem valid_iff_no_bad_charts (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ) (N : ℕ)
    (hlow : low.totalDegree < N) (hN : 1 < N) (record : List Bool) :
    Valid low a N record ↔ (∀ i : Fin (n + 1), ¬ AffineBad low a N record i) ∧
      (∀ i : Fin (n + 1), ¬ InfinityBad a N record i) := by
  have hd : (FermatBoundedSweepSample.lower low a N).totalDegree < N :=
    CoordinateSlicePolynomial.fermat_lower_degree low a N hlow
  have h := FermatCriticalBadSpecialization.root_free_iff_kernel_infinity_charts (sampleMap n N record)
    (FermatBoundedSweepSample.lower low a N) (Polynomial.C a) N hd hN (sampledDirection n N record)
  have hv : (fun i => Polynomial.C (direction n N record i : ℚ)) = sampledDirection n N record := rfl
  simpa only [Valid, FermatBoundedSweepSample.rows, AffineBad, InfinityBad, criticalRows,
    sampleMap, hv] using h

theorem infinity_bad_iff (a : ℚ) (N : ℕ) (record : List Bool) (i : Fin (n + 1)) :
    InfinityBad a N record i ↔ ∃ x : Fin (n + 1) → ℂ, x i = 1 ∧
      (a : ℂ) * ∑ j : Fin (n + 1), x j ^ N = 0 ∧
      ∀ j : Fin n, (a : ℂ) * (N : ℂ) *
        (x j.succ ^ (N - 1) - (direction n N record j : ℂ) * x 0 ^ (N - 1)) = 0 := by
  simp only [InfinityBad, FermatCriticalInfinity.native, Fin.forall_fin_succ, Fin.cons_zero,
    Fin.cons_succ, eval₂_mul, eval₂_C, eval₂_sum, eval₂_pow, eval₂_X, eval₂_sub, eval₂_natCast,
    sampledDirection, sampleMap, map_mul, map_natCast, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, eq_ratCast]

theorem infinity_bad_iff_reduced (a : ℚ) (ha : a ≠ 0) (N : ℕ) (hN : 0 < N)
    (record : List Bool) (i : Fin (n + 1)) :
    InfinityBad a N record i ↔ ∃ x : Fin (n + 1) → ℂ, x i = 1 ∧
      (∑ j : Fin (n + 1), x j ^ N) = 0 ∧
      ∀ j : Fin n, x j.succ ^ (N - 1) - (direction n N record j : ℂ) * x 0 ^ (N - 1) = 0 := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [infinity_bad_iff, mul_eq_zero, ha', hN', false_or]

end LeanCanny.Encoding.FermatSweepCertificate
