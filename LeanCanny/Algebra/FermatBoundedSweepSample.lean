/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatGenericSliceDirection
public import LeanCanny.Algebra.FermatCriticalBadSpecialization
public import LeanCanny.Algebra.ProjectiveSweepGrid

/-! # Bounded direction and sweep-sample certificates for regular sources

The actual parameter-ring bad-root system has a root-free specialization at
bounded natural direction and sweep values. Testing that finite sample can
certify generic projective root-freeness without retaining a maximal minor.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatBoundedSweepSample
open MvPolynomial FermatCriticalHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

universe u
variable {n : ℕ} {K : Type u} [Field K] [CharZero K]

noncomputable def lower (low : MvPolynomial (Fin (n + 2)) K) (a : K) (N : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial K) :=
  CoordinateSlicePolynomial.family low + C (Polynomial.C a * Polynomial.X ^ N)

noncomputable def rows (low : MvPolynomial (Fin (n + 2)) K) (a : K) (N : ℕ)
    (v : Fin n → ℕ) (j : Fin (n + 2)) : MvPolynomial (Fin (n + 2)) (Polynomial K) :=
  FermatCriticalBadSpecialization.rows (lower low a N) (Polynomial.C a) N
    (fun i => Polynomial.C (v i : K)) j

def sampleAllowance (n N : ℕ) : ℕ :=
  FixedWidthPolynomial.count (n + 2) (FermatBoundedCriticalDirection.width n N) * ((n + 1) * N)

omit [CharZero K] in
theorem parameter_degree (low : MvPolynomial (Fin (n + 2)) K) (a : K) (N : ℕ)
    (hlow : low.totalDegree < N) (v : Fin n → ℕ) (j : Fin (n + 2)) :
    PolynomialCoefficientDegree.Bound (rows low a N v j) ((n + 1) * N) := by
  apply FermatCriticalBadSpecialization.parameter_degree
  apply PolynomialCoefficientDegree.add
  · exact PolynomialCoefficientDegree.mono (CoordinateSlicePolynomial.coefficient_degree low) hlow.le
  · apply PolynomialCoefficientDegree.C
    exact Polynomial.natDegree_mul_le.trans (by simp)

omit [CharZero K] in
theorem map_rows (low : MvPolynomial (Fin (n + 2)) K) (a : K) (N : ℕ) (v : Fin n → ℕ)
    (j : Fin (n + 2)) :
    (rows low a N v j).map (algebraMap (Polynomial K) (FermatGenericSliceDirection.GenericField K)) =
      FermatCriticalBadSpecialization.rows (FermatGenericSliceDirection.lower low a N)
        (algebraMap K (FermatGenericSliceDirection.GenericField K) a) N (fun i => (v i : _)) j := by
  rw [rows, FermatCriticalBadSpecialization.map_rows]
  have hC (r : K) : algebraMap (Polynomial K) (FermatGenericSliceDirection.GenericField K) (Polynomial.C r) =
      algebraMap K (FermatGenericSliceDirection.GenericField K) r :=
    (IsScalarTower.algebraMap_apply K (Polynomial K) _ r).symm
  simp only [hC, map_natCast]
  rfl

omit [CharZero K] in
theorem eval_specialized {F L : Type*} [Field F] [Field L] [Algebra F L]
    (low : MvPolynomial (Fin (n + 1)) F) (a : F) (N : ℕ) (v : Fin n → ℕ)
    (y : Fin (n + 2) → L) (j : Fin (n + 2)) :
    (FermatCriticalBadSpecialization.rows low a N (fun i => (v i : F)) j).eval₂ (algebraMap F L) y =
      (FermatCriticalBadSystem.nativeRows low a N j).eval₂
        (eval₂Hom (algebraMap F L) (fun i => (v i : L))) y := by
  rw [← FermatCriticalBadSpecialization.specialize_rows, eval₂_map]
  congr 1
  ext <;> simp

theorem exists_bounded (low : MvPolynomial (Fin (n + 2)) K) (a : K) (ha : a ≠ 0)
    (N : ℕ) (hlow : low.totalDegree < N) (hN : 1 < N)
    (hregular : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin (n + 2) → L),
      aeval x (polynomial low a N) = 0 → ∃ j, aeval x (pderiv j (polynomial low a N)) ≠ 0) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ FermatBoundedCriticalDirection.allowance n N) ∧
      ∃ t : ℕ, t ≤ sampleAllowance n N ∧
        ∀ (L : Type*) [Field L] [Algebra K L] (y : Fin (n + 2) → L),
          (∀ j, (rows low a N v j).eval₂ (Polynomial.eval₂RingHom (algebraMap K L) (t : L)) y = 0) → y = 0 := by
  obtain ⟨v, hv, hgood⟩ := FermatGenericSliceDirection.exists_bounded_root_free low a ha N hlow hN hregular
  let F := FermatGenericSliceDirection.GenericField K
  let L := AlgebraicClosure F
  let φ : Polynomial K →+* L := (algebraMap F L).comp (algebraMap (Polynomial K) F)
  have hroot (y : Fin (n + 2) → L) (hy : ∀ j, (rows low a N v j).eval₂ φ y = 0) : y = 0 := by
    apply hgood L y
    intro j
    have hj := hy j
    rw [← eval₂_map, map_rows, eval_specialized] at hj
    exact hj
  obtain ⟨t, ht, hsample⟩ := ProjectiveSweepGrid.exists_bounded (rows low a N v)
    (FermatCriticalBadSystem.nativeDegrees n N) (FermatBoundedCriticalDirection.width n N) ((n + 1) * N)
    (Nat.lt_size_self _) (FermatCriticalBadSpecialization.homogeneous _ _ _ _)
    (fun j => FermatCriticalBadSystem.degrees_pos N hN (FermatCriticalBadSystem.layout.symm j))
    (parameter_degree low a N hlow v) φ hroot
  exact ⟨v, hv, t, ht, hsample⟩

omit [CharZero K] in
/-- Any accepted root-free sample gives the generic root-free system. The
sample need not be the one selected by the existence proof. -/
theorem generic_of_sample {F L : Type*} [Field F] [IsAlgClosed F] [Algebra K F]
    [Field L] [Algebra (FermatGenericSliceDirection.GenericField K) L]
    (low : MvPolynomial (Fin (n + 2)) K) (a : K) (N : ℕ) (hN : 1 < N)
    (v : Fin n → ℕ) (t : ℕ)
    (hsample : ∀ z : Fin (n + 2) → F,
      (∀ j, (rows low a N v j).eval₂ (Polynomial.eval₂RingHom (algebraMap K F) (t : F)) z = 0) → z = 0)
    (y : Fin (n + 2) → L)
    (hy : ∀ j, (FermatCriticalBadSystem.nativeRows (FermatGenericSliceDirection.lower low a N)
      (algebraMap K (FermatGenericSliceDirection.GenericField K) a) N j).eval₂
        (eval₂Hom (algebraMap (FermatGenericSliceDirection.GenericField K) L) (fun i => (v i : L))) y = 0) : y = 0 := by
  let G := FermatGenericSliceDirection.GenericField K
  let ψ : Polynomial K →+* L := (algebraMap G L).comp (algebraMap (Polynomial K) G)
  apply ProjectiveSweepGrid.generic_of_sample (rows low a N v) (FermatCriticalBadSystem.nativeDegrees n N)
    (FermatBoundedCriticalDirection.width n N) (Nat.lt_size_self _)
    (FermatCriticalBadSpecialization.homogeneous _ _ _ _)
    (fun j => FermatCriticalBadSystem.degrees_pos N hN (FermatCriticalBadSystem.layout.symm j))
    _ hsample ψ ((algebraMap G L).injective.comp (IsFractionRing.injective _ _)) y
  intro j
  rw [← eval₂_map, map_rows, eval_specialized]
  exact hy j

omit [CharZero K] in
theorem regular_of_sample {F L : Type*} [Field F] [IsAlgClosed F] [Algebra K F]
    [Field L] [Algebra (FermatGenericSliceDirection.GenericField K) L]
    (low : MvPolynomial (Fin (n + 2)) K) (a : K) (N : ℕ)
    (hlow : low.totalDegree < N) (hN : 1 < N) (v : Fin n → ℕ) (t : ℕ)
    (hsample : ∀ z : Fin (n + 2) → F,
      (∀ j, (rows low a N v j).eval₂ (Polynomial.eval₂RingHom (algebraMap K F) (t : F)) z = 0) → z = 0)
    (x : Fin (n + 1) → L)
    (hx : ∀ j, (FermatCriticalBadSystem.equations (FermatGenericSliceDirection.lower low a N)
      (algebraMap K (FermatGenericSliceDirection.GenericField K) a) N j).eval₂
        (eval₂Hom (algebraMap (FermatGenericSliceDirection.GenericField K) L) (fun i => (v i : L))) x = 0) :
    (FermatCriticalBadSystem.jacobian (FermatGenericSliceDirection.lower low a N)
      (algebraMap K (FermatGenericSliceDirection.GenericField K) a) N).eval₂
        (eval₂Hom (algebraMap (FermatGenericSliceDirection.GenericField K) L) (fun i => (v i : L))) x ≠ 0 := by
  intro hJ
  let lo := FermatGenericSliceDirection.lower low a N
  let aG := algebraMap K (FermatGenericSliceDirection.GenericField K) a
  let φ := eval₂Hom (algebraMap (FermatGenericSliceDirection.GenericField K) L) (fun i => (v i : L))
  have hdeg := FermatGenericSliceDirection.lower_degree low a N hlow
  have hchart (i : Option (Fin (n + 1))) :
      (FermatCriticalBadSystem.rows lo aG N i).eval₂ φ (fun j => j.elim 1 x) = 0 :=
    HomogeneousBadSystem.chart_root φ (FermatCriticalBadSystem.equations lo aG N)
      (FermatCriticalInfinity.degrees n N) (FermatCriticalBadSystem.jacobian lo aG N)
      (FermatCriticalBadSystem.jacobianDegree n N) (FermatCriticalBadSystem.equations_degree lo aG N hdeg)
      (FermatCriticalBadSystem.jacobian_degree lo aG N hdeg) x hx hJ i
  let y : Fin (n + 2) → L := fun j => (FermatCriticalBadSystem.layout.symm j).elim 1 x
  have hy (j : Fin (n + 2)) : (FermatCriticalBadSystem.nativeRows lo aG N j).eval₂ φ y = 0 := by
    simpa only [FermatCriticalBadSystem.nativeRows, eval₂_rename, Function.comp_def, y,
      Equiv.symm_apply_apply] using hchart (FermatCriticalBadSystem.layout.symm j)
  have he := congrFun (generic_of_sample low a N hN v t hsample y hy) (FermatCriticalBadSystem.layout none)
  have h10 : (1 : L) = 0 := by simpa only [y, Equiv.symm_apply_apply, Option.elim_none, Pi.zero_apply] using he
  exact one_ne_zero h10

end LeanCanny.Algebra.FermatBoundedSweepSample
