/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.Algebra.Algebra.Operations

/-! # The Koszul exterior differential and its unit-combination homotopy

Contraction by the coefficient linear form gives the differential in every
exterior degree. If a linear combination of the inputs is one, exterior
multiplication by its coefficient vector is a contracting homotopy.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulExterior
open scoped BigOperators
variable {R I : Type*} [CommRing R] [Fintype I]

noncomputable def linearForm (p : I → R) : (I → R) →ₗ[R] R where
  toFun v := ∑ i, v i * p i
  map_add' v w := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a v := by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

abbrev Total (R I : Type*) [CommRing R] := ExteriorAlgebra R (I → R)

noncomputable def differential (p : I → R) : Total R I →ₗ[R] Total R I :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (I → R))) (linearForm p)

noncomputable def wedge (v : I → R) : Total R I →ₗ[R] Total R I :=
  LinearMap.mulLeft R (ExteriorAlgebra.ι R v)

theorem differential_square_zero (p : I → R) (x : Total R I) : differential p (differential p x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft (linearForm p) x

theorem differential_anticommute (p q : I → R) (x : Total R I) :
    differential p (differential q x) = -differential q (differential p x) :=
  CliffordAlgebra.contractLeft_comm (linearForm p) (linearForm q) x

theorem differential_ι_mul (p v : I → R) (x : Total R I) :
    differential p (ExteriorAlgebra.ι R v * x) = linearForm p v • x - ExteriorAlgebra.ι R v * differential p x :=
  CliffordAlgebra.contractLeft_ι_mul (linearForm p) v x

theorem homotopy_identity (p v : I → R) (x : Total R I) :
    differential p (wedge v x) + wedge v (differential p x) = linearForm p v • x := by
  change differential p (ExteriorAlgebra.ι R v * x) + ExteriorAlgebra.ι R v * differential p x = _
  rw [differential_ι_mul, sub_add_cancel]

theorem kernel_iff (p v : I → R) (hv : ∑ i, v i * p i = 1) (x : Total R I) :
    differential p x = 0 ↔ ∃ y : Total R I, differential p y = x := by
  constructor
  · intro hx
    refine ⟨wedge v x, ?_⟩
    have h := homotopy_identity p v x
    change differential p (wedge v x) + wedge v (differential p x) = (∑ i, v i * p i) • x at h
    simpa only [hx, map_zero, add_zero, hv, one_smul] using h
  · rintro ⟨y, rfl⟩
    exact differential_square_zero p y

omit [Fintype I] in
theorem wedge_mem (v : I → R) (k : ℕ) (x : Total R I)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R k (I → R)) :
    wedge v x ∈ ExteriorAlgebra.exteriorPower R (k + 1) (I → R) := by
  change ExteriorAlgebra.ι R v * x ∈ LinearMap.range (ExteriorAlgebra.ι R : (I → R) →ₗ[R] Total R I) ^ (k + 1)
  rw [pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) hx

private theorem differential_ιMulti_mem (p : I → R) (k : ℕ) (v : Fin (k + 1) → I → R) :
    differential p (ExteriorAlgebra.ιMulti R (k + 1) v) ∈ ExteriorAlgebra.exteriorPower R k (I → R) := by
  induction k with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, differential_ι_mul, ExteriorAlgebra.ιMulti_zero_apply]
    have hz : differential p (1 : Total R I) = 0 := CliffordAlgebra.contractLeft_one _ (linearForm p)
    rw [hz, mul_zero, sub_zero]
    change linearForm p (v 0) • (1 : Total R I) ∈
      LinearMap.range (ExteriorAlgebra.ι R : (I → R) →ₗ[R] Total R I) ^ 0
    rw [pow_zero]
    exact Submodule.mem_one.mpr ⟨linearForm p (v 0), Algebra.algebraMap_eq_smul_one _⟩
  | succ k ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, differential_ι_mul]
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range R (k + 1) ⟨Matrix.vecTail v, rfl⟩)
    · exact wedge_mem (v 0) k _ (ih (Matrix.vecTail v))

theorem differential_mem (p : I → R) (k : ℕ) (x : Total R I)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R (k + 1) (I → R)) :
    differential p x ∈ ExteriorAlgebra.exteriorPower R k (I → R) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R (k + 1)] at hx
  have hle : Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R (k + 1) (M := I → R))) ≤
      (ExteriorAlgebra.exteriorPower R k (I → R)).comap (differential p) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    exact differential_ιMulti_mem p k v
  exact hle hx

theorem differential_degree_zero (p : I → R) (x : Total R I)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R 0 (I → R)) : differential p x = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R 0] at hx
  have hle : Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R 0 (M := I → R))) ≤ LinearMap.ker (differential p) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change differential p (ExteriorAlgebra.ιMulti R 0 v) = 0
    rw [ExteriorAlgebra.ιMulti_zero_apply]
    exact CliffordAlgebra.contractLeft_one _ (linearForm p)
  exact hle hx

theorem graded_kernel_iff (p v : I → R) (hv : ∑ i, v i * p i = 1) (k : ℕ) (x : Total R I)
    (hx : x ∈ ExteriorAlgebra.exteriorPower R k (I → R)) :
    differential p x = 0 ↔ ∃ y : Total R I, y ∈ ExteriorAlgebra.exteriorPower R (k + 1) (I → R) ∧
      differential p y = x := by
  constructor
  · intro hz
    refine ⟨wedge v x, wedge_mem v k x hx, ?_⟩
    have h := homotopy_identity p v x
    change differential p (wedge v x) + wedge v (differential p x) = (∑ i, v i * p i) • x at h
    simpa only [hz, map_zero, add_zero, hv, one_smul] using h
  · rintro ⟨y, _, rfl⟩
    exact differential_square_zero p y

noncomputable def gradedDifferential (p : I → R) (k : ℕ) :
    ExteriorAlgebra.exteriorPower R (k + 1) (I → R) →ₗ[R] ExteriorAlgebra.exteriorPower R k (I → R) :=
  ((differential p).comp (ExteriorAlgebra.exteriorPower R (k + 1) (I → R)).subtype).codRestrict _
    (fun x => differential_mem p k x.val x.property)

theorem gradedDifferential_comp (p : I → R) (k : ℕ) :
    (gradedDifferential p k).comp (gradedDifferential p (k + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact differential_square_zero p x.val

theorem graded_exact (p v : I → R) (hv : ∑ i, v i * p i = 1) (k : ℕ) :
    LinearMap.ker (gradedDifferential p k) = LinearMap.range (gradedDifferential p (k + 1)) := by
  ext x
  constructor
  · intro hx
    have hz : differential p x.val = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy, he⟩ := (graded_kernel_iff p v hv (k + 1) x.val x.property).mp hz
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact differential_square_zero p y.val

theorem graded_zero_surjective (p v : I → R) (hv : ∑ i, v i * p i = 1) :
    Function.Surjective (gradedDifferential p 0) := by
  intro x
  obtain ⟨y, hy, he⟩ := (graded_kernel_iff p v hv 0 x.val x.property).mp (differential_degree_zero p x.val x.property)
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩

end LeanCanny.Algebra.KoszulExterior
