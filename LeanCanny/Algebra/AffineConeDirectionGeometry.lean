/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineConeBoundedDirection

/-! # Geometric consequences of bounded cone directions

The projective certificate excludes original Lagrange critical roots over
every coefficient-field extension. Passing to an algebraic closure supplies
all multiplier power roots; injectivity brings the result back to the
original field. Consequently the new normal preserves cone transversality.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineConeDirectionGeometry
open MvPolynomial AffineCriticalConeSystem GenericAffineCriticalJacobian
open GenericAffineConeFlag AffineConeBoundedDirection
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} {n : ℕ} [Field K]

def CriticalRootFree {L : Type u} [Field L] [Algebra K L]
    (p : MvPolynomial (Fin n) K) (s : Finset (Fin n)) (A : Fin n → Fin n → K) (v : Fin n → L) : Prop :=
  ∀ (x : Fin n → L) (μ : Fin (n + 1) → L), aeval x p = 0 →
    (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0) →
    (∀ i, aeval x (pderiv i p) = v i * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ) →
    (∀ r, r ∉ s → μ r.succ = 0) → x = 0 ∧ μ = 0

theorem critical_root_free (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : 1 < D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (v : Fin n → ℕ)
    (hfree : ∀ (L : Type u) [Field L] [Algebra K L] (z : Fin (2 * n + 1) → L),
      (∀ j, (nativeRows p D s A j).eval₂ (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z = 0) → z = 0)
    (L : Type u) [Field L] [Algebra K L] : CriticalRootFree p s A (fun i => (v i : L)) := by
  intro x μ hp hl hg hu
  let E := AlgebraicClosure L
  let f : L →+* E := algebraMap L E
  let : Algebra K E := Algebra.compHom E (algebraMap K L)
  have hf : f.comp (algebraMap K L) = algebraMap K E := rfl
  have hfapply (k : K) : f (algebraMap K L k) = algebraMap K E k := rfl
  let φ := eval₂Hom (algebraMap K E) (fun i => (v i : E))
  have hφ : φ.comp C = algebraMap K E := by ext k; simp [φ]
  have hp' : aeval (fun i => f (x i)) p = 0 := by
    have H := congrArg f hp
    rw [map_aeval, hf, map_zero] at H
    simpa only [aeval_def, coe_eval₂Hom] using H
  have hl' (r : Fin n) (hr : r ∈ s) : ∑ i, algebraMap K E (A r i) * f (x i) = 0 := by
    have H := congrArg f (hl r hr)
    simp only [map_sum, map_mul, map_zero] at H
    exact H
  have hg' (i : Fin n) : aeval (fun i => f (x i)) (pderiv i p) =
      φ (X i) * f (μ 0) + ∑ r, algebraMap K E (A r i) * f (μ r.succ) := by
    have H := congrArg f (hg i)
    rw [map_aeval, hf] at H
    simpa only [aeval_def, coe_eval₂Hom, map_add, map_mul, map_natCast, map_sum,
      hfapply, φ, eval₂Hom_X'] using H
  have hu' (r : Fin n) (hr : r ∉ s) : f (μ r.succ) = 0 := by rw [hu r hr, map_zero]
  obtain ⟨hx, hμ⟩ := critical_root_zero_of_native φ hφ p D hD s A (hfree E)
    (fun i => f (x i)) (fun r => f (μ r)) hp' hl' hg' hu'
  constructor
  · funext i
    apply f.injective
    simpa only [Pi.zero_apply, map_zero] using congrFun hx i
  · funext r
    apply f.injective
    simpa only [Pi.zero_apply, map_zero] using congrFun hμ r

variable {L : Type u} [Field L] [Algebra K L]

theorem normal_independent (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : p.IsHomogeneous D)
    (hD2 : 1 < D) (s : Finset (Fin n)) (A : Fin n → Fin n → K) (v : Fin n → L)
    (hfree : CriticalRootFree p s A v) (cv : L) (c : Fin n → L)
    (hc : ∀ r, r ∉ s → c r = 0)
    (hz : ∀ i, cv * v i + ∑ r, c r * algebraMap K L (A r i) = 0) :
    cv = 0 ∧ ∀ r, c r = 0 := by
  let μ : Fin (n + 1) → L := Fin.cases cv c
  have H := (hfree 0 μ (GenericAffineCriticalInfinity.origin_zero p D hD (by omega))
    (fun r _ => by simp) (fun i => ?_) (fun r hr => hc r hr)).2
  · exact ⟨congrFun H 0, fun r => congrFun H r.succ⟩
  · rw [GenericAffineCriticalInfinity.gradient_origin_zero p D hD hD2 i]
    simpa only [μ, Fin.cases_zero, Fin.cases_succ, mul_comm] using (hz i).symm

theorem extended_independent (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : p.IsHomogeneous D)
    (hD2 : 1 < D) (s : Finset (Fin n)) (A : Fin n → Fin n → K) (v x : Fin n → L)
    (hfree : CriticalRootFree p s A v) (hp : aeval x p = 0)
    (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0) (hx : x ≠ 0)
    (c0 cv : L) (c : Fin n → L) (hc : ∀ r, r ∉ s → c r = 0)
    (hz : ∀ i, c0 * aeval x (pderiv i p) + cv * v i +
      ∑ r, c r * algebraMap K L (A r i) = 0) :
    c0 = 0 ∧ cv = 0 ∧ ∀ r, c r = 0 := by
  by_cases hc0 : c0 = 0
  · refine ⟨hc0, normal_independent p D hD hD2 s A v hfree cv c hc ?_⟩
    intro i
    simpa only [hc0, zero_mul, zero_add] using hz i
  · exfalso
    let μ : Fin (n + 1) → L := Fin.cases (-cv / c0) (fun r => -c r / c0)
    have hg (i : Fin n) : aeval x (pderiv i p) = v i * μ 0 +
        ∑ r, algebraMap K L (A r i) * μ r.succ := by
      simp only [μ, Fin.cases_zero, Fin.cases_succ]
      simp_rw [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
      rw [← add_mul, ← div_eq_mul_inv]
      apply (eq_div_iff hc0).mpr
      have he : (∑ r, algebraMap K L (A r i) * -c r) =
          -(∑ r, c r * algebraMap K L (A r i)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro r _; ring
      rw [he]
      linear_combination hz i
    have hu (r : Fin n) (hr : r ∉ s) : μ r.succ = 0 := by simp [μ, hc r hr]
    exact hx (hfree x μ hp hl hg hu).1

/-- Split a row relation after replacing one unused normal by the new one. -/
theorem sum_update_normal (A : Fin n → Fin n → K) (r : Fin n) (v : Fin n → K)
    (c : Fin n → L) (i : Fin n) :
    (∑ j, c j * algebraMap K L (Function.update A r v j i)) =
      c r * algebraMap K L (v i) + ∑ j, Function.update c r 0 j * algebraMap K L (A j i) := by
  calc
    _ = ∑ j, ((if j = r then c r * algebraMap K L (v i) else 0) +
        Function.update c r 0 j * algebraMap K L (A j i)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = r <;> simp [hj]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem inactive_update (s : Finset (Fin n)) (r : Fin n) (c : Fin n → L)
    (hc : ∀ j, j ∉ insert r s → c j = 0) :
    ∀ j, j ∉ s → Function.update c r 0 j = 0 := by
  intro j hj
  by_cases he : j = r
  · simp [he]
  · simp only [Function.update_of_ne he]
    exact hc j (by simp [he, hj])

theorem normal_independent_insert (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (hD2 : 1 < D) (s : Finset (Fin n)) (r : Fin n)
    (A : Fin n → Fin n → K) (v : Fin n → K)
    (hfree : CriticalRootFree p s A (fun i => algebraMap K L (v i))) :
    NormalIndependent (L := L) (insert r s) (Function.update A r v) := by
  intro c hc hz
  have H := normal_independent p D hD hD2 s A (fun i => algebraMap K L (v i)) hfree
    (c r) (Function.update c r 0) (inactive_update s r c hc) (fun i => by
      simpa only [sum_update_normal A r v c i] using hz i)
  intro j
  by_cases hj : j = r
  · simpa only [hj] using H.1
  · simpa only [Function.update_of_ne hj] using H.2 j

theorem constraint_independent_insert (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (hD2 : 1 < D) (s : Finset (Fin n)) (r : Fin n)
    (A : Fin n → Fin n → K) (v : Fin n → K) (x : Fin n → L)
    (hfree : CriticalRootFree p s A (fun i => algebraMap K L (v i))) (hp : aeval x p = 0)
    (hl : ∀ j ∈ s, ∑ i, algebraMap K L (A j i) * x i = 0) (hx : x ≠ 0) :
    ConstraintIndependent p (insert r s) (Function.update A r v) x := by
  intro c0 c hc hz
  have H := extended_independent p D hD hD2 s A (fun i => algebraMap K L (v i)) x hfree hp hl hx
    c0 (c r) (Function.update c r 0) (inactive_update s r c hc) (fun i => by
      have H := hz i
      rw [sum_update_normal A r v c i] at H
      linear_combination H)
  refine ⟨H.1, fun j => ?_⟩
  by_cases hj : j = r
  · simpa only [hj] using H.2.1
  · simpa only [Function.update_of_ne hj] using H.2.2 j

variable [CharZero K]

/-- The explicit integer allowance gives transversality of the new normal
at every nonzero cone point over every extension of the coefficient field. -/
theorem exists_bounded (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (hD2 : 1 < D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K)
    (hA : ∀ (L : Type u) [Field L] [Algebra K L], NormalIndependent (L := L) s A)
    (hcone : ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin n → L), aeval x p = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0) → x ≠ 0 →
      ConstraintIndependent p s A x) :
    ∃ v : Fin n → ℕ, (∀ i, v i < 2 ^ binaryWidth n D) ∧
      ∀ (L : Type u) [Field L] [Algebra K L], CriticalRootFree p s A (fun i => (v i : L)) := by
  obtain ⟨v, hv, hfree⟩ := exists_bounded_root_free p D hD hD2 s hs A hA hcone
  exact ⟨v, fun i => (hv i).trans_lt (allowance_lt_two_pow n D), critical_root_free p D hD2 s A v hfree⟩

end LeanCanny.Algebra.AffineConeDirectionGeometry
