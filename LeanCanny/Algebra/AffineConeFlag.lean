/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineConeDirectionGeometry

/-! # Bounded extensions of transverse homogeneous-cone flags

The flag records independence of its old normals and independence of the
source/height constraints at every nonzero cone point. A bounded integer
normal extends this invariant over all coefficient-field extensions.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineConeFlag
open MvPolynomial GenericAffineCriticalJacobian GenericAffineConeFlag
open AffineConeDirectionGeometry AffineConeBoundedDirection
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} {n : ℕ} [Field K]

def Transverse {L : Type u} [Field L] [Algebra K L]
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (A : Fin n → Fin n → K) : Prop :=
  NormalIndependent (L := L) s A ∧ ∀ x : Fin n → L, aeval x p = 0 →
    (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0) → x ≠ 0 →
    ConstraintIndependent p s A x

theorem transverse_empty {L : Type u} [Field L] [Algebra K L]
    (p : MvPolynomial (Fin n) K) (A : Fin n → Fin n → K)
    (hgradient : ∀ x : Fin n → L, aeval x p = 0 → x ≠ 0 → ∃ i, aeval x (pderiv i p) ≠ 0) :
    Transverse (L := L) p ∅ A := by
  refine ⟨fun c hc _ r => hc r (by simp), ?_⟩
  intro x hp _ hx c0 c hc hz
  have hczero (r : Fin n) : c r = 0 := hc r (by simp)
  obtain ⟨i, hi⟩ := hgradient x hp hx
  have H := hz i
  simp only [hczero, zero_mul, Finset.sum_const_zero, add_zero] at H
  exact ⟨(mul_eq_zero.mp H).resolve_right hi, hczero⟩

theorem transverse_insert_of_root_free {L : Type u} [Field L] [Algebra K L]
    (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : p.IsHomogeneous D) (hD2 : 1 < D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (r : Fin n) (hr : r ∉ s) (v : Fin n → K)
    (hfree : CriticalRootFree p s A (fun i => algebraMap K L (v i))) :
    Transverse (L := L) p (insert r s) (Function.update A r v) := by
  refine ⟨normal_independent_insert p D hD hD2 s r A v hfree, ?_⟩
  intro x hp hl hx
  apply constraint_independent_insert p D hD hD2 s r A v x hfree hp ?_ hx
  intro j hj
  have hne : j ≠ r := by intro he; exact hr (he ▸ hj)
  simpa only [Function.update_of_ne hne] using hl j (Finset.mem_insert_of_mem hj)

variable [CharZero K]

/-- Extend any transverse cone flag by an integer normal of explicitly
bounded bit length. This preserves the invariant over every extension field. -/
theorem exists_bounded_extension (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (hD2 : 1 < D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K) (r : Fin n) (hr : r ∉ s)
    (hflag : ∀ (L : Type u) [Field L] [Algebra K L], Transverse (L := L) p s A) :
    ∃ v : Fin n → ℕ, (∀ i, v i < 2 ^ binaryWidth n D) ∧
      ∀ (L : Type u) [Field L] [Algebra K L],
        Transverse (L := L) p (insert r s) (Function.update A r (fun i => (v i : K))) := by
  obtain ⟨v, hv, hfree⟩ := AffineConeDirectionGeometry.exists_bounded p D hD hD2 s hs A
    (fun L _ _ => (hflag L).1) (fun L _ _ => (hflag L).2)
  refine ⟨v, hv, ?_⟩
  intro L _ _
  have hcrit : CriticalRootFree p s A (fun i => algebraMap K L (v i : K)) := by
    simpa only [map_natCast] using hfree L
  exact transverse_insert_of_root_free p D hD hD2 s A r hr (fun i => (v i : K)) hcrit

end LeanCanny.Algebra.AffineConeFlag
