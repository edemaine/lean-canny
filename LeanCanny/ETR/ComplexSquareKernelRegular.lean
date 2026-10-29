/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexSquareKernelCorrect
public import LeanCanny.Algebra.JacobianKernelCharts

/-! # Empty square-system kernel charts characterize regularity

The matrix differentiates only the selected input block. Frozen inputs,
additional zero guards, input reality, and Boolean conditions retain their
original assignment. The equivalence includes systems with nonisolated roots.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.SquareKernel
open MvPolynomial
open scoped Classical BigOperators Matrix

noncomputable def matrix (wire : ℕ → MvPolynomial ℕ ℤ) (m offset : ℕ)
    (outputs : ℕ → ℕ) (x : ℕ → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun j k => (pderiv (offset + k.val) (wire (outputs j.val))).eval₂ (Int.castRingHom ℂ) x

theorem charts_iff_singular (wire : ℕ → MvPolynomial ℕ ℤ) (m offset : ℕ)
    (outputs : ℕ → ℕ) (guardCount : ℕ) (guardOutputs : ℕ → ℕ) (x : ℕ → ℂ) :
    (∃ i : Fin m, ∃ u : ℕ → ℂ, At wire m offset outputs guardCount guardOutputs i.val x u) ↔
      (∀ j < m, (wire (outputs j)).eval₂ (Int.castRingHom ℂ) x = 0) ∧
      (∀ j < guardCount, (wire (guardOutputs j)).eval₂ (Int.castRingHom ℂ) x = 0) ∧
      (matrix wire m offset outputs x).det = 0 := by
  constructor
  · rintro ⟨i, u, hn, hrows, hguards⟩
    refine ⟨fun j hj => (hrows j hj).1, hguards, ?_⟩
    apply (LeanCanny.Algebra.JacobianKernelCharts.det_zero_iff (matrix wire m offset outputs x)).mpr
    refine ⟨i, fun k => u k.val, hn, ?_⟩
    funext j
    change (∑ k : Fin m, (pderiv (offset + k.val) (wire (outputs j.val))).eval₂
      (Int.castRingHom ℂ) x * u k.val) = 0
    have H := (hrows j.val j.isLt).2
    rw [← Fin.sum_univ_eq_sum_range] at H
    exact H
  · rintro ⟨hrows, hguards, hdet⟩
    obtain ⟨i, v, hn, hv⟩ := (LeanCanny.Algebra.JacobianKernelCharts.det_zero_iff (matrix wire m offset outputs x)).mp hdet
    let u : ℕ → ℂ := fun k => if hk : k < m then v ⟨k, hk⟩ else 0
    refine ⟨i, u, ?_, fun j hj => ⟨hrows j hj, ?_⟩, hguards⟩
    · simpa only [u, dite_eq_left i.isLt, Fin.eta] using hn
    · have H := congrFun hv ⟨j, hj⟩
      change (∑ k : Fin m, (pderiv (offset + k.val) (wire (outputs j))).eval₂
        (Int.castRingHom ℂ) x * v k) = 0 at H
      rw [← Fin.sum_univ_eq_sum_range]
      simpa [u] using H

def Regular (wire : ℕ → MvPolynomial ℕ ℤ) (m offset : ℕ) (outputs : ℕ → ℕ)
    (guardCount : ℕ) (guardOutputs : ℕ → ℕ) (realInputs : ℕ) (p : Formula) : Prop :=
  ∀ x : ℕ → ℂ, (∀ i < realInputs, (x i).im = 0) → p.Holds (fun i => (x i).re) →
    (∀ j < m, (wire (outputs j)).eval₂ (Int.castRingHom ℂ) x = 0) →
    (∀ j < guardCount, (wire (guardOutputs j)).eval₂ (Int.castRingHom ℂ) x = 0) →
    (matrix wire m offset outputs x).det ≠ 0

theorem regular_iff_no_charts (wire : ℕ → MvPolynomial ℕ ℤ) (m offset : ℕ)
    (outputs : ℕ → ℕ) (guardCount : ℕ) (guardOutputs : ℕ → ℕ) (realInputs : ℕ) (p : Formula) :
    Regular wire m offset outputs guardCount guardOutputs realInputs p ↔
      ∀ i : Fin m, ¬ ∃ x u : ℕ → ℂ, At wire m offset outputs guardCount guardOutputs i.val x u ∧
        (∀ j < realInputs, (x j).im = 0) ∧ p.Holds (fun j => (x j).re) := by
  constructor
  · intro h i
    rintro ⟨x, u, hAt, hr, hp⟩
    obtain ⟨hx, hg, hd⟩ := (charts_iff_singular wire m offset outputs guardCount guardOutputs x).mp ⟨i, u, hAt⟩
    exact h x hr hp hx hg hd
  · intro h x hr hp hx hg hd
    obtain ⟨i, u, hAt⟩ := (charts_iff_singular wire m offset outputs guardCount guardOutputs x).mpr ⟨hx, hg, hd⟩
    exact h i ⟨x, u, hAt, hr, hp⟩

end LeanCanny.ETR.ComplexCircuit.SquareKernel
