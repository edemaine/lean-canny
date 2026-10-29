/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCriticalDirectionGeometry
public import LeanCanny.Algebra.PolynomialRootTransfer

/-! # Algebraically closed affine direction certificates

Testing the specialized projective bad system in one algebraically closed
extension suffices for original affine critical regularity and leading-cone
root exclusion over every extension. In particular, a complex existential
test can certify both geometric invariants.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineCriticalClosedCertificate
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u
variable {K L : Type u} {n : ℕ} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]

noncomputable def specialize (v : Fin n → ℕ) : MvPolynomial (Fin n) K →+* K :=
  eval₂Hom (RingHom.id K) (fun i => (v i : K))

omit [IsAlgClosed L] in
theorem eval_specialize {σ : Type*} (v : Fin n → ℕ)
    (q : MvPolynomial σ (MvPolynomial (Fin n) K)) (z : σ → L) :
    aeval z (q.map (specialize v)) =
      q.eval₂ (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z := by
  rw [aeval_def, eval₂_map]
  congr 1
  ext <;> simp [specialize]

/-- One algebraically closed test supplies the universal projective certificate. -/
theorem native_free (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (v : Fin n → ℕ)
    (hfree : ∀ z : Fin (2 * n + 2) → L,
      (∀ j, (AffineCriticalPowerBadSystem.nativeRows p D s A β j).eval₂
        (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z = 0) → z = 0)
    (E : Type u) [Field E] [Algebra K E] (z : Fin (2 * n + 2) → E)
    (hz : ∀ j, (AffineCriticalPowerBadSystem.nativeRows p D s A β j).eval₂
      (eval₂Hom (algebraMap K E) (fun i => (v i : E))) z = 0) : z = 0 := by
  let q := fun j => (AffineCriticalPowerBadSystem.nativeRows p D s A β j).map (specialize v)
  apply PolynomialRootTransfer.no_nonzero_root (L := L) q ?_ z ?_
  · intro y hy
    exact hfree y (fun j => (eval_specialize v _ y).symm.trans (hy j))
  · intro j
    exact (eval_specialize v _ z).trans (hz j)

/-- The finite-root Jacobian and the cone invariant are certified together.
The Jacobian is that of the original multiplier system. -/
theorem geometry (low H : MvPolynomial (Fin n) K) (D : ℕ)
    (hlow : low.totalDegree < D) (hH : H.IsHomogeneous D) (hD : 1 < D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (β : Fin n → K) (v : Fin n → ℕ)
    (hfree : ∀ z : Fin (2 * n + 2) → L,
      (∀ j, (AffineCriticalPowerBadSystem.nativeRows (low + H) D s A β j).eval₂
        (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z = 0) → z = 0)
    (E : Type u) [Field E] [Algebra K E] :
    AffineCriticalDirectionGeometry.CriticalRegular (low + H) s A β (fun i => (v i : E)) ∧
      AffineConeDirectionGeometry.CriticalRootFree H s A (fun i => (v i : E)) := by
  have hall := native_free (low + H) D s A β v hfree
  exact ⟨AffineCriticalDirectionGeometry.regular_of_native low H D hlow hH hD s A β v hall E,
    AffineCriticalDirectionGeometry.cone_free_of_native low H D hlow hH hD s A β v hall E⟩

end LeanCanny.Algebra.AffineCriticalClosedCertificate
