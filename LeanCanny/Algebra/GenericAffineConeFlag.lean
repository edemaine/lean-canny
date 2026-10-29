/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GenericAffineCriticalInfinity
public import LeanCanny.Algebra.AffineDirectionAvoidance

/-! # Transverse flags on a homogeneous cone

A generic new normal is independent of the source gradient and the old
normals at every nonzero regular point of the old cone slice. This also
preserves transversality after imposing the new zero-height equation.
-/

@[expose] public section
namespace LeanCanny.Algebra.GenericAffineConeFlag
open MvPolynomial GenericAffineCriticalJacobian
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K L : Type*} {n : ℕ} [Field K] [Field L] [Algebra K L]

theorem not_in_span (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K) (v : Fin n → L) (hind : AlgebraicIndependent K v) :
    ¬ ∃ c : s → L, ∀ i, v i = ∑ j : s, c j * algebraMap K L (A j.val i) := by
  obtain ⟨γ, hγ, hA⟩ := AffineDirectionAvoidance.exists_annihilator s hs A
  apply AffineDirectionAvoidance.not_in_span s A γ hA v
  rw [← aeval_def]
  intro he
  apply AffineDirectionAvoidance.ne_zero γ hγ
  apply hind
  simpa only [map_zero] using he

/-- Independence of the active old normal rows over the coordinate field. -/
def NormalIndependent (s : Finset (Fin n)) (A : Fin n → Fin n → K) : Prop :=
  ∀ c : Fin n → L, (∀ r, r ∉ s → c r = 0) →
    (∀ i, ∑ r, c r * algebraMap K L (A r i) = 0) → ∀ r, c r = 0

theorem normals_of_constraint (p : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (x : Fin n → L) (h : ConstraintIndependent p s A x) :
    NormalIndependent (L := L) s A := by
  intro c hc hz
  exact (h 0 c hc (fun i => by simpa only [zero_mul, zero_add] using hz i)).2

theorem normal_extended_independent (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K) (v : Fin n → L) (hind : AlgebraicIndependent K v)
    (hA : NormalIndependent (L := L) s A) (cv : L) (c : Fin n → L)
    (hc : ∀ r, r ∉ s → c r = 0)
    (hz : ∀ i, cv * v i + ∑ r, c r * algebraMap K L (A r i) = 0) :
    cv = 0 ∧ ∀ r, c r = 0 := by
  have hcv : cv = 0 := by
    by_contra hn
    apply not_in_span s hs A v hind
    refine ⟨fun j => -c j.val / cv, fun i => ?_⟩
    have H := hz i
    have hs' : (∑ r, c r * algebraMap K L (A r i)) =
        ∑ r : s, c r.val * algebraMap K L (A r.val i) := by
      calc
        _ = ∑ r ∈ s, c r * algebraMap K L (A r i) := by
          apply (Finset.sum_subset (Finset.subset_univ s) ?_).symm
          intro r _ hr
          rw [hc r hr, zero_mul]
        _ = _ := (Finset.sum_attach s (fun r => c r * algebraMap K L (A r i))).symm
    rw [hs'] at H
    apply mul_right_cancel₀ hn
    calc
      v i * cv = -∑ r : s, c r.val * algebraMap K L (A r.val i) := by linear_combination H
      _ = (∑ r : s, (-c r.val / cv) * algebraMap K L (A r.val i)) * cv := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro r _
        field_simp
  refine ⟨hcv, hA c hc (fun i => ?_)⟩
  simpa only [hcv, zero_mul, zero_add] using hz i

/-- Adding the new normal to the source gradient and active old normals
preserves independence at every nonzero regular point of the old cone. -/
theorem extended_independent [CharZero K] (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K) (v x : Fin n → L) (hind : AlgebraicIndependent K v)
    (hp : aeval x p = 0) (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0)
    (hx : x ≠ 0) (hconstraint : ConstraintIndependent p s A x)
    (c0 cv : L) (c : Fin n → L) (hc : ∀ r, r ∉ s → c r = 0)
    (hz : ∀ i, c0 * aeval x (pderiv i p) + cv * v i +
      ∑ r, c r * algebraMap K L (A r i) = 0) :
    c0 = 0 ∧ cv = 0 ∧ ∀ r, c r = 0 := by
  by_cases hcv : cv = 0
  · have H := hconstraint c0 c hc (fun i => by simpa only [hcv, zero_mul, add_zero] using hz i)
    exact ⟨H.1, hcv, H.2⟩
  · exfalso
    by_cases hc0 : c0 = 0
    · have H := normal_extended_independent s hs A v hind
        (normals_of_constraint p s A x hconstraint) cv c hc (fun i => by
          simpa only [hc0, zero_mul, zero_add] using hz i)
      exact hcv H.1
    · let μ : Fin (n + 1) → L := Fin.cases (-cv / c0) (fun r => -c r / c0)
      have hu (r : Fin n) (hr : r ∉ s) : μ r.succ = 0 := by simp [μ, hc r hr]
      have hμ : μ 0 ≠ 0 := by simpa only [μ, Fin.cases_zero] using div_ne_zero (neg_ne_zero.mpr hcv) hc0
      have hg (i : Fin n) : aeval x (pderiv i p) = v i * μ 0 +
          ∑ r, algebraMap K L (A r i) * μ r.succ := by
        simp only [μ, Fin.cases_zero, Fin.cases_succ]
        simp_rw [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
        rw [← add_mul, ← div_eq_mul_inv]
        apply (eq_div_iff hc0).mpr
        have H := hz i
        have he : (∑ r, algebraMap K L (A r i) * -c r) =
            -(∑ r, c r * algebraMap K L (A r i)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro r _; ring
        rw [he]
        linear_combination H
      exact hx (GenericAffineCriticalInfinity.ambient_zero p D hD s A v x μ hind hp hl hg hu hμ)

/-- No ambient or multiplier coordinate remains at a generic critical root
of a transverse homogeneous cone slice. -/
theorem critical_root_zero [CharZero K] (p : MvPolynomial (Fin n) K) (D : ℕ)
    (hD : p.IsHomogeneous D) (hD2 : 1 < D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : Fin n → Fin n → K) (v x : Fin n → L) (μ : Fin (n + 1) → L)
    (hind : AlgebraicIndependent K v) (hA : NormalIndependent (L := L) s A)
    (hcone : ∀ y : Fin n → L, aeval y p = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * y i = 0) → y ≠ 0 →
      ConstraintIndependent p s A y)
    (hp : aeval x p = 0) (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = 0)
    (hg : ∀ i, aeval x (pderiv i p) = v i * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0) : x = 0 ∧ μ = 0 := by
  have hx : x = 0 := by
    by_contra hn
    exact hn (GenericAffineCriticalInfinity.ambient_zero_of_independent p D hD s A v x μ
      hind hp hl hg hu (hcone x hp hl hn))
  have hμ := normal_extended_independent s hs A v hind hA (μ 0) (fun r => μ r.succ) hu (fun i => by
    have H := hg i
    rw [hx, GenericAffineCriticalInfinity.gradient_origin_zero p D hD hD2 i] at H
    simpa only [mul_comm] using H.symm)
  refine ⟨hx, ?_⟩
  funext j
  exact Fin.cases hμ.1 (fun r => hμ.2 r) j

end LeanCanny.Algebra.GenericAffineConeFlag
