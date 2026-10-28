/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCriticalKernelPorts
public import LeanCanny.Algebra.FreeCoordinateSpecialization

/-! # Kernel queries detect all singular points in real coordinate slices

Every input after the free block is a frozen real coefficient. Specializing
these inputs commutes with the critical rows and their Jacobian. A normalized
complex kernel exists exactly when the resulting real derivative is singular.
This statement applies pointwise, including positive-dimensional zero sets.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CriticalKernel
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open scoped Classical BigOperators Matrix
variable {n : ℕ}

theorem specialize_critical {K : Type*} [CommRing K] (φ : ℤ →+* K) (frozen : ℕ → K)
    (p : MvPolynomial ℕ ℤ) (v : ℕ → ℤ) (j : Fin (n + 1)) :
    FreeCoordinateSpecialization.specialize φ frozen (CriticalSamples.criticalPolynomial p v j.val) =
      finiteRows (FreeCoordinateSpecialization.specialize φ frozen p) (fun i => (v i.val : K)) j := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [CriticalSamples.criticalPolynomial, selectedPolynomial, Fin.val_zero, ite_true,
      coefficient, C_0, zero_mul, add_zero, finiteRows, Fin.cons_zero]
  · simp only [CriticalSamples.criticalPolynomial, selectedPolynomial, Fin.val_succ,
      Nat.add_one_ne_zero, ite_false, coefficient, Nat.add_sub_cancel_right,
      finiteRows, Fin.cons_succ, map_add, map_mul]
    have hd := FreeCoordinateSpecialization.specialize_pderiv φ frozen p j.succ
    have hb := FreeCoordinateSpecialization.specialize_pderiv φ frozen p (0 : Fin (n + 1))
    simp only [Fin.val_succ] at hd
    simp only [Fin.val_zero] at hb
    rw [hd, hb]
    have hC : FreeCoordinateSpecialization.specialize (n := n + 1) φ frozen (C (-v j.val)) =
        C (-(v j.val : K)) := by
      rw [FreeCoordinateSpecialization.specialize, eval₂Hom_C, RingHom.comp_apply]
      simpa only [Int.cast_neg, Int.cast_id] using congrArg (C : K → MvPolynomial (Fin (n + 1)) K)
        (map_intCast φ (-v j.val))
    rw [hC]
    simp only [map_neg, neg_mul, sub_eq_add_neg]

theorem kernelValue_eq (p : MvPolynomial ℕ ℤ) (m : ℕ) (v : ℕ → ℤ) (x u : ℕ → ℂ) (j : ℕ) :
    kernelValue p m v x u j = ∑ k ∈ Finset.range m,
      (pderiv k (CriticalSamples.criticalPolynomial p v j)).eval₂ (Int.castRingHom ℂ) x * u k := by
  unfold kernelValue CriticalSamples.criticalPolynomial
  simp only [map_add, pderiv_C_mul, eval₂_add, eval₂_mul, eval₂_C]
  congr 1
  funext k
  unfold selectedPolynomial entryPolynomial
  split_ifs <;> rfl

noncomputable def realSlice (p : MvPolynomial ℕ ℤ) (x : ℕ → ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  FreeCoordinateSpecialization.specialize (Int.castRingHom ℝ) (fun i => x (n + 1 + i)) p

theorem criticalValue_real (p : MvPolynomial ℕ ℤ) (v : ℕ → ℤ) (x : ℕ → ℝ) (j : Fin (n + 1)) :
    criticalValue p v (fun i => (x i : ℂ)) j.val =
      (((finiteRows (realSlice (n := n) p x) (fun i => (v i.val : ℝ)) j).eval (fun i => x i.val)) : ℂ) := by
  have he : criticalValue p v (fun i => (x i : ℂ)) j.val =
      (CriticalSamples.criticalPolynomial p v j.val).eval₂ (Int.castRingHom ℂ) (fun i => (x i : ℂ)) := by
    simp only [criticalValue, CriticalSamples.criticalPolynomial, eval₂_add, eval₂_mul, eval₂_C, Int.coe_castRingHom]
  rw [he]
  rw [polynomial_eval_ofReal,
    ← FreeCoordinateSpecialization.eval_at (n := n + 1) (Int.castRingHom ℝ), specialize_critical]
  rfl

theorem kernelValue_real (p : MvPolynomial ℕ ℤ) (v : ℕ → ℤ) (x : ℕ → ℝ) (u : ℕ → ℂ) (j : Fin (n + 1)) :
    kernelValue p (n + 1) v (fun i => (x i : ℂ)) u j.val =
      ((PolynomialSystemRegularity.matrix (RingHom.id ℝ)
        (finiteRows (realSlice (n := n) p x) (fun i => (v i.val : ℝ))) (fun i => x i.val)).map Complex.ofRealHom *ᵥ
          (fun i => u i.val)) j := by
  rw [kernelValue_eq, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [polynomial_eval_ofReal,
    ← FreeCoordinateSpecialization.eval_at (n := n + 1) (Int.castRingHom ℝ),
    FreeCoordinateSpecialization.specialize_pderiv, specialize_critical]
  rfl

theorem at_iff_real_kernel (p : MvPolynomial ℕ ℤ) (v : ℕ → ℤ) (x : ℕ → ℝ) (chart : Fin (n + 1)) :
    At p (n + 1) v chart.val (fun i => (x i : ℂ)) ↔
      (∀ j, (finiteRows (realSlice (n := n) p x) (fun i => (v i.val : ℝ)) j).eval (fun i => x i.val) = 0) ∧
        ∃ u : Fin (n + 1) → ℂ, u chart = 1 ∧
          (PolynomialSystemRegularity.matrix (RingHom.id ℝ)
            (finiteRows (realSlice (n := n) p x) (fun i => (v i.val : ℝ))) (fun i => x i.val)).map Complex.ofRealHom *ᵥ u = 0 := by
  constructor
  · rintro ⟨u, hu, hroot⟩
    refine ⟨?_, (fun i => u i.val), hu, ?_⟩
    · intro j
      have h := (hroot j.val j.isLt).1
      rw [criticalValue_real] at h
      exact_mod_cast h
    · funext j
      exact (kernelValue_real p v x u j).symm.trans (hroot j.val j.isLt).2
  · rintro ⟨hroot, u, hu, hkernel⟩
    let extend : ℕ → ℂ := fun i => if h : i < n + 1 then u ⟨i, h⟩ else 0
    have he : (fun i : Fin (n + 1) => extend i.val) = u := by
      funext i
      simp only [extend, i.isLt, dite_true, Fin.eta]
    refine ⟨extend, ?_, fun j hj => ?_⟩
    · simpa only [extend, chart.isLt, dite_true, Fin.eta] using hu
    · constructor
      · rw [criticalValue_real p v x ⟨j, hj⟩, hroot, Complex.ofReal_zero]
      · have h := kernelValue_real p v x extend ⟨j, hj⟩
        rw [he, hkernel] at h
        exact h

theorem exists_chart_iff_singular (p : MvPolynomial ℕ ℤ) (v : ℕ → ℤ) (x : ℕ → ℝ) :
    (∃ chart : Fin (n + 1), At p (n + 1) v chart.val (fun i => (x i : ℂ))) ↔
      (∀ j, (finiteRows (realSlice (n := n) p x) (fun i => (v i.val : ℝ)) j).eval (fun i => x i.val) = 0) ∧
        ¬ (fderiv ℝ (fun y => fun j =>
          (finiteRows (realSlice (n := n) p x) (fun i => (v i.val : ℝ)) j).eval y) (fun i => x i.val)).IsInvertible := by
  let M := PolynomialSystemRegularity.matrix (RingHom.id ℝ)
    (finiteRows (realSlice (n := n) p x) (fun i => (v i.val : ℝ))) (fun i => x i.val)
  have hmap : (M.map Complex.ofRealHom).det = (M.det : ℂ) := (Complex.ofRealHom.map_det M).symm
  have hr := PolynomialSystemRegularity.isInvertible_iff (RingHom.id ℝ)
    (finiteRows (realSlice (n := n) p x) (fun i => (v i.val : ℝ))) (fun i => x i.val)
  simp only [eval₂_id] at hr
  rw [hr, not_not]
  constructor
  · rintro ⟨chart, h⟩
    obtain ⟨hz, u, hu, hk⟩ := (at_iff_real_kernel p v x chart).mp h
    have hd := (JacobianKernelCharts.det_zero_iff (M.map Complex.ofRealHom)).mpr ⟨chart, u, hu, hk⟩
    rw [hmap] at hd
    exact ⟨hz, by exact_mod_cast hd⟩
  · rintro ⟨hz, hd⟩
    have hdc : (M.map Complex.ofRealHom).det = 0 := by rw [hmap, hd, Complex.ofReal_zero]
    obtain ⟨chart, u, hu, hk⟩ := (JacobianKernelCharts.det_zero_iff (M.map Complex.ofRealHom)).mp hdc
    exact ⟨chart, (at_iff_real_kernel p v x chart).mpr ⟨hz, u, hu, hk⟩⟩

end LeanCanny.ETR.ComplexCircuit.CriticalKernel
