/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.Operations

/-! # Prime ideals above finite affine zero sets are maximal

The Nullstellensatz identifies the radical ideal with the finite intersection
of point ideals. A prime containing that intersection contains one of its
maximal factors, so it is itself maximal. No smoothness is needed.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteZeroLocus

open MvPolynomial
open scoped Classical
variable {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
theorem isMaximal_of_finite_zeroLocus (I P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (hI : (zeroLocus K I).Finite) (hIP : I ≤ P) : P.IsMaximal := by
  let S := hI.toFinset
  have he : vanishingIdeal K (zeroLocus K I) = S.inf (fun x => vanishingIdeal K {x}) := by
    ext p
    simp only [Finset.inf_eq_iInf, Submodule.mem_iInf, MvPolynomial.mem_vanishingIdeal_iff]
    constructor
    · intro h x hx y hy
      exact (Set.mem_singleton_iff.mp hy) ▸ h x (hI.mem_toFinset.mp hx)
    · intro h x hx
      exact h x (hI.mem_toFinset.mpr hx) x rfl
  have hle : S.inf (fun x => vanishingIdeal K {x}) ≤ P := by
    rw [← he, vanishingIdeal_zeroLocus_eq_radical]
    simpa only [Ideal.IsPrime.radical] using Ideal.radical_mono hIP
  obtain ⟨x, _, hx⟩ := (Ideal.IsPrime.inf_le' (inferInstance : P.IsPrime)).mp hle
  have heq := Ideal.IsMaximal.eq_of_le
    (inferInstance : (vanishingIdeal K {x} : Ideal (MvPolynomial σ K)).IsMaximal)
    ((inferInstance : P.IsPrime).ne_top) hx
  rw [← heq]
  infer_instance

end LeanCanny.Algebra.FiniteZeroLocus
