/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Nullstellensatz

/-! # Testing polynomial root exclusion in one algebraically closed field

A system over a field has a root in an arbitrary extension only if it has
one in any algebraically closed extension. No finiteness or regularity
assumption on its zero set is required.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialRootTransfer
open MvPolynomial
open scoped Classical

variable {σ τ K L E : Type*} [Finite σ] [Field K] [Field L] [Algebra K L]
  [IsAlgClosed L] [Field E] [Algebra K E]

/-- Transfer existence, allowing singular roots and positive-dimensional systems. -/
theorem exists_root (p : τ → MvPolynomial σ K) (x : σ → E)
    (hx : ∀ j, aeval x (p j) = 0) :
    ∃ y : σ → L, ∀ j, aeval y (p j) = 0 := by
  let I : Ideal (MvPolynomial σ K) := Ideal.span (Set.range p)
  have hI : I ≤ RingHom.ker (aeval x : MvPolynomial σ K →ₐ[K] E).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hx j
  have htop : I ≠ ⊤ := by
    intro ht
    have h := hI (ht ▸ (show (1 : MvPolynomial σ K) ∈ (⊤ : Ideal _) from trivial))
    change aeval x 1 = 0 at h
    simp at h
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I htop
  obtain ⟨y, hy⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal L hP
  refine ⟨y, fun j => ?_⟩
  have hm : p j ∈ P := hIP (Ideal.subset_span (Set.mem_range_self j))
  rw [hy, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hm
  exact hm

/-- A root-free test over one algebraically closed extension is universal. -/
theorem no_root (p : τ → MvPolynomial σ K)
    (h : ¬ ∃ y : σ → L, ∀ j, aeval y (p j) = 0) :
    ¬ ∃ x : σ → E, ∀ j, aeval x (p j) = 0 := by
  rintro ⟨x, hx⟩
  exact h (exists_root p x hx)

/-- Include a bad-root equation without requiring the original fiber to be finite. -/
theorem nonvanishing (p : τ → MvPolynomial σ K) (J : MvPolynomial σ K)
    (h : ∀ y : σ → L, (∀ j, aeval y (p j) = 0) → aeval y J ≠ 0)
    (x : σ → E) (hx : ∀ j, aeval x (p j) = 0) : aeval x J ≠ 0 := by
  intro hJ
  let q : Option τ → MvPolynomial σ K := fun j => j.elim J p
  have hq : ∀ j, aeval x (q j) = 0 := by
    intro j
    cases j with
    | none => exact hJ
    | some j => exact hx j
  obtain ⟨y, hy⟩ := exists_root (L := L) q x hq
  exact h y (fun j => hy (some j)) (hy none)

/-- Nonzero-root exclusion transfers by adjoining one inverse-coordinate witness.
No homogeneity or norm-square argument is needed. -/
theorem no_nonzero_root (p : τ → MvPolynomial σ K)
    (h : ∀ y : σ → L, (∀ j, aeval y (p j) = 0) → y = 0)
    (x : σ → E) (hx : ∀ j, aeval x (p j) = 0) : x = 0 := by
  by_contra hzero
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hzero (funext hn)
  let q : Option τ → MvPolynomial (Option σ) K := fun j =>
    j.elim (X none * X (some i) - 1) (fun j => rename some (p j))
  let z : Option σ → E := fun j => j.elim (x i)⁻¹ x
  have hz : ∀ j, aeval z (q j) = 0 := by
    intro j
    cases j with
    | none => simp [q, z, hi]
    | some j => simpa only [q, z, Option.elim_some, aeval_rename, Function.comp_def] using hx j
  obtain ⟨w, hw⟩ := exists_root (L := L) q z hz
  have hp : ∀ j, aeval (fun k => w (some k)) (p j) = 0 := by
    intro j
    simpa only [q, Option.elim_some, aeval_rename, Function.comp_def] using hw (some j)
  have hwi := congrFun (h _ hp) i
  have hn := hw none
  simp [q, hwi] at hn

end LeanCanny.Algebra.PolynomialRootTransfer
