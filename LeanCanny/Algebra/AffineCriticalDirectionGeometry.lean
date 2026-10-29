/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCriticalBoundedDirection
public import LeanCanny.Algebra.FlatAffineGradientJacobian

/-! # Bounded critical directions in the original affine coordinates

Power-coordinate certificates imply regularity of every original Lagrange
root, including zero multipliers. The same certificate preserves the
leading-cone flag. Algebraic closures supply multiplier roots and injective
scalar maps return the original Jacobian conclusion to arbitrary fields.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineCriticalDirectionGeometry
open MvPolynomial FlatAffineCriticalStage GenericAffineCriticalJacobian
open AffineCriticalOriginalJacobian AffineCriticalBoundedDirection
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} {n : ℕ} [Field K]

def CriticalRegular {L : Type u} [Field L] [Algebra K L]
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (v : Fin n → L) : Prop :=
  ∀ (x : Fin n → L) (μ : Fin (n + 1) → L), aeval x p = 0 →
    (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = algebraMap K L (β r)) →
    (∀ i, aeval x (pderiv i p) = v i * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ) →
    (∀ r, r ∉ s → μ r.succ = 0) → (matrix p s A v x).det ≠ 0

theorem regular_of_power (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : 1 < D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (β : Fin n → K) (v : Fin n → ℕ)
    (hgood : ∀ (L : Type u) [Field L] [Algebra K L] (z : Variables n → L),
      (∀ j, (AffineCriticalPowerSystem.rows p D s A β j).eval₂
        (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z = 0) →
      (jacobian p s A).eval₂ (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z ≠ 0)
    (L : Type u) [Field L] [Algebra K L] : CriticalRegular p s A β (fun i => (v i : L)) := by
  intro x μ hp hl hg hu hbad
  let E := AlgebraicClosure L
  let f : L →+* E := algebraMap L E
  let _ : Algebra K E := Algebra.compHom E (algebraMap K L)
  have hf : f.comp (algebraMap K L) = algebraMap K E := rfl
  have hfapply (k : K) : f (algebraMap K L k) = algebraMap K E k := rfl
  let φL := eval₂Hom (algebraMap K L) (fun i => (v i : L))
  let φE := eval₂Hom (algebraMap K E) (fun i => (v i : E))
  have hφL : φL.comp C = algebraMap K L := by ext k; simp [φL]
  have hφE : φE.comp C = algebraMap K E := by ext k; simp [φE]
  have hφ : φE = f.comp φL := by ext <;> simp [φE, φL, hfapply]
  have hp' : aeval (fun i => f (x i)) p = 0 := by
    have H := congrArg f hp
    rw [map_aeval, hf, map_zero] at H
    simpa only [aeval_def, coe_eval₂Hom] using H
  have hl' (r : Fin n) (hr : r ∈ s) : ∑ i, algebraMap K E (A r i) * f (x i) = algebraMap K E (β r) := by
    have H := congrArg f (hl r hr)
    simp only [map_sum, map_mul, hfapply] at H
    exact H
  have hg' (i : Fin n) : aeval (fun i => f (x i)) (pderiv i p) =
      φE (X i) * f (μ 0) + ∑ r, algebraMap K E (A r i) * f (μ r.succ) := by
    have H := congrArg f (hg i)
    rw [map_aeval, hf] at H
    simpa only [aeval_def, coe_eval₂Hom, map_add, map_mul, map_natCast, map_sum,
      hfapply, φE, eval₂Hom_X'] using H
  have hu' (r : Fin n) (hr : r ∉ s) : f (μ r.succ) = 0 := by rw [hu r hr, map_zero]
  obtain ⟨z, hx, _, hz⟩ := AffineCriticalPowerSystem.lift_critical_root φE hφE p D hD s A β
    (fun i => f (x i)) (fun r => f (μ r)) hp' hl' hg' hu'
  apply hgood E z hz
  let z0 : Variables n → L := Sum.elim x μ
  have hJ0 : (jacobian p s A).eval₂ φL z0 = 0 := by
    rw [eval_jacobian φL hφL]
    simpa only [φL, eval₂Hom_X', z0, Function.comp_def, Sum.elim_inl] using hbad
  have hJ : (jacobian p s A).eval₂ φE (f ∘ z0) = 0 := by
    have H := congrArg f hJ0
    rw [eval₂_comp_left, ← hφ, map_zero] at H
    exact H
  have hsame : z ∘ Sum.inl = (f ∘ z0) ∘ Sum.inl := hx
  have he : (jacobian p s A).eval₂ φE z = (jacobian p s A).eval₂ φE (f ∘ z0) := by
    rw [eval_jacobian φE hφE, eval_jacobian φE hφE, hsame]
  exact he.trans hJ

theorem regular_of_native (low H : MvPolynomial (Fin n) K) (D : ℕ)
    (hlow : low.totalDegree < D) (hH : H.IsHomogeneous D) (hD : 1 < D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (β : Fin n → K) (v : Fin n → ℕ)
    (hfree : ∀ (L : Type u) [Field L] [Algebra K L] (z : Fin (2 * n + 2) → L),
      (∀ j, (AffineCriticalPowerBadSystem.nativeRows (low + H) D s A β j).eval₂
        (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z = 0) → z = 0)
    (L : Type u) [Field L] [Algebra K L] : CriticalRegular (low + H) s A β (fun i => (v i : L)) := by
  apply regular_of_power (low + H) D hD s A β v ?_ L
  intro E _ _ z hz
  exact AffineCriticalPowerBadSystem.affine_regular_of_native _ low H D hlow hH hD s A β (hfree E) z hz

theorem cone_free_of_native (low H : MvPolynomial (Fin n) K) (D : ℕ)
    (hlow : low.totalDegree < D) (hH : H.IsHomogeneous D) (hD : 1 < D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (β : Fin n → K) (v : Fin n → ℕ)
    (hfree : ∀ (L : Type u) [Field L] [Algebra K L] (z : Fin (2 * n + 2) → L),
      (∀ j, (AffineCriticalPowerBadSystem.nativeRows (low + H) D s A β j).eval₂
        (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z = 0) → z = 0)
    (L : Type u) [Field L] [Algebra K L] :
    AffineConeDirectionGeometry.CriticalRootFree H s A (fun i => (v i : L)) := by
  apply AffineConeDirectionGeometry.critical_root_free H D hD s A v ?_ L
  intro E _ _ z hz
  let φ := eval₂Hom (algebraMap K E) (fun i => (v i : E))
  have hr (j : Variables n) : (AffineCriticalConeSystem.rows H D s A j).eval₂ φ
      (z ∘ AffineCriticalConeSystem.layout n) = 0 := by
    simpa only [AffineCriticalConeSystem.nativeRows, eval₂_rename, Equiv.symm_apply_apply] using
      hz (AffineCriticalConeSystem.layout n j)
  have H := AffineCriticalPowerBadSystem.cone_free_of_native φ low H D hlow hH hD s A β (hfree E)
    (z ∘ AffineCriticalConeSystem.layout n) hr
  funext j
  have he := congrFun H ((AffineCriticalConeSystem.layout n).symm j)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using he

/-- The bounded-direction conclusion applies to the actual affine-stage
Jacobian with arbitrary ancestral level polynomials realizing the fixed levels. -/
theorem actual_stage_regular {L ι : Type u} [Field L] [Algebra K L]
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (A : Fin n → Fin n → K)
    (β : Fin n → K) (v : Fin n → L) (b : Fin n → MvPolynomial ι L)
    (hreg : CriticalRegular p s A β v) (z : (ι ⊕ Variables n) → L)
    (hz : ∀ j, (row (p.map (algebraMap K L)) s (FlatAffineGradientJacobian.directions A v) b j).eval₂
      (RingHom.id L) z = 0)
    (hb : ∀ r ∈ s, (b r).eval₂ (RingHom.id L) (z ∘ Sum.inl) = algebraMap K L (β r)) :
    (FlatAffineCriticalRegularity.matrix (RingHom.id L) (p.map (algebraMap K L)) s
      (FlatAffineGradientJacobian.directions A v) b z).det ≠ 0 := by
  obtain ⟨hp, hl, hg, hu⟩ := (FlatAffineCriticalStage.roots_iff (RingHom.id L)
    (p.map (algebraMap K L)) s (FlatAffineGradientJacobian.directions A v) b z).mp hz
  rw [FlatAffineGradientJacobian.matrix_eq]
  apply hreg (z ∘ ambient) (fun r => z (multiplier r))
  · simpa only [eval₂_map, RingHom.id_comp, aeval_def] using hp
  · intro r hr
    have H := hl r hr
    simp only [RingHom.id_apply, FlatAffineGradientJacobian.directions, Fin.cases_succ] at H
    exact H.trans (hb r hr)
  · intro i
    simpa only [pderiv_map, eval₂_map, RingHom.id_comp, aeval_def, RingHom.id_apply,
      Fin.sum_univ_succ, FlatAffineGradientJacobian.directions, Fin.cases_zero, Fin.cases_succ] using hg i
  · exact hu

variable [CharZero K]

/-- A single explicitly bounded integer direction gives regular original
affine critical roots and preserves the transverse cone flag simultaneously. -/
theorem exists_bounded (low H : MvPolynomial (Fin n) K) (D : ℕ)
    (hlow : low.totalDegree < D) (hH : H.IsHomogeneous D) (hD : 1 < D)
    (s : Finset (Fin n)) (hs : s.card < n) (A : Fin n → Fin n → K) (β : Fin n → K)
    (hcone : ∀ (L : Type u) [Field L] [Algebra K L], AffineConeFlag.Transverse (L := L) H s A)
    (hslice : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin n → L), aeval x (low + H) = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = algebraMap K L (β r)) →
      ConstraintIndependent (low + H) s A x) :
    ∃ v : Fin n → ℕ, (∀ i, v i < 2 ^ binaryWidth n D) ∧
      ∀ (L : Type u) [Field L] [Algebra K L], CriticalRegular (low + H) s A β (fun i => (v i : L)) ∧
        AffineConeDirectionGeometry.CriticalRootFree H s A (fun i => (v i : L)) := by
  obtain ⟨v, hv, hfree⟩ := exists_bounded_root_free low H D hlow hH hD s hs A β hcone hslice
  exact ⟨v, fun i => (hv i).trans_lt (allowance_lt_two_pow n D), fun L _ _ =>
    ⟨regular_of_native low H D hlow hH hD s A β v hfree L,
      cone_free_of_native low H D hlow hH hD s A β v hfree L⟩⟩

/-- A regular affine stage and the next transverse leading flag share the
same objective and the same source-controlled bit bound. -/
theorem exists_bounded_extension (low H : MvPolynomial (Fin n) K) (D : ℕ)
    (hlow : low.totalDegree < D) (hH : H.IsHomogeneous D) (hD : 1 < D)
    (s : Finset (Fin n)) (hs : s.card < n) (A : Fin n → Fin n → K) (β : Fin n → K)
    (r : Fin n) (hr : r ∉ s)
    (hcone : ∀ (L : Type u) [Field L] [Algebra K L], AffineConeFlag.Transverse (L := L) H s A)
    (hslice : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin n → L), aeval x (low + H) = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = algebraMap K L (β r)) →
      ConstraintIndependent (low + H) s A x) :
    ∃ v : Fin n → ℕ, (∀ i, v i < 2 ^ binaryWidth n D) ∧
      ∀ (L : Type u) [Field L] [Algebra K L], CriticalRegular (low + H) s A β (fun i => (v i : L)) ∧
        AffineConeFlag.Transverse (L := L) H (insert r s) (Function.update A r (fun i => (v i : K))) := by
  obtain ⟨v, hv, hgood⟩ := exists_bounded low H D hlow hH hD s hs A β hcone hslice
  refine ⟨v, hv, fun L _ _ => ⟨(hgood L).1, ?_⟩⟩
  apply AffineConeFlag.transverse_insert_of_root_free H D hH hD s A r hr (fun i => (v i : K))
  simpa only [map_natCast] using (hgood L).2

end LeanCanny.Algebra.AffineCriticalDirectionGeometry
