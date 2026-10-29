/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCriticalConeSystem
public import LeanCanny.Algebra.PolynomialMapDegree

/-! # Affine-level critical equations in multiplier power coordinates

The source and its derivatives retain the ambient variables. Multipliers
are replaced by powers of degree D-1. Active old heights are constrained to
fixed coefficient-field levels. Splitting off a lower-degree source part
leaves exactly the homogeneous cone system plus strictly lower-degree rows.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineCriticalPowerSystem
open MvPolynomial FlatAffineCriticalStage AffineCriticalConeSystem
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K L : Type*} {n : ℕ} [Field K] [Field L] [Algebra K L]

noncomputable def spatial (p : MvPolynomial (Fin n) K) :
    MvPolynomial (Variables n) (MvPolynomial (Fin n) K) := lift (rename Sum.inl p)

def offset (s : Finset (Fin n)) (β : Fin n → K) : Variables n → K
  | .inl _ => 0
  | .inr j => Fin.cases 0 (fun r => if r ∈ s then β r else 0) j

noncomputable def rows (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (j : Variables n) :
    MvPolynomial (Variables n) (MvPolynomial (Fin n) K) :=
  AffineCriticalConeSystem.rows p D s A j - C (C (offset s β j))

noncomputable def lowerRows (low : MvPolynomial (Fin n) K) (s : Finset (Fin n))
    (β : Fin n → K) : Variables n → MvPolynomial (Variables n) (MvPolynomial (Fin n) K)
  | .inl i => spatial (pderiv i low)
  | .inr j => Fin.cases (spatial low) (fun r => if r ∈ s then -C (C (β r)) else 0) j

theorem split_rows (low H : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (j : Variables n) :
    rows (low + H) D s A β j = AffineCriticalConeSystem.rows H D s A j + lowerRows low s β j := by
  cases j with
  | inl i => simp [rows, AffineCriticalConeSystem.rows, lowerRows, offset, spatial, lift]; ring
  | inr j =>
    refine Fin.cases ?_ (fun r => ?_) j
    · simp [rows, AffineCriticalConeSystem.rows, lowerRows, offset, spatial, lift, add_comm]
    · by_cases hr : r ∈ s <;> simp [rows, AffineCriticalConeSystem.rows, lowerRows, offset, hr, sub_eq_add_neg]

theorem spatial_degree (p : MvPolynomial (Fin n) K) : (spatial p).totalDegree ≤ p.totalDegree :=
  (PolynomialMapDegree.degree_le C (rename Sum.inl p)).trans (totalDegree_rename_le _ _)

theorem lower_degree (low : MvPolynomial (Fin n) K) (D : ℕ) (hlow : low.totalDegree < D)
    (hD : 1 < D) (s : Finset (Fin n)) (β : Fin n → K) (j : Variables n) :
    (lowerRows low s β j).totalDegree < degrees D s j := by
  cases j with
  | inl i =>
    have H := (spatial_degree (pderiv i low)).trans (PartialDerivativeDegree.degree_le low i)
    change (spatial (pderiv i low)).totalDegree < D - 1
    omega
  | inr j =>
    refine Fin.cases ((spatial_degree low).trans_lt hlow) (fun r => ?_) j
    by_cases hr : r ∈ s <;> simp only [lowerRows, AffineCriticalConeSystem.degrees, Fin.cases_succ, hr, ite_true, ite_false,
      totalDegree_neg, totalDegree_C, totalDegree_zero] <;> omega

theorem degree_le (low H : MvPolynomial (Fin n) K) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (j : Variables n) :
    (rows (low + H) D s A β j).totalDegree ≤ degrees D s j := by
  rw [split_rows]
  exact (totalDegree_add _ _).trans (max_le (homogeneous H D hH s A j).totalDegree_le
    (lower_degree low D hlow hD s β j).le)

theorem parameter_degree (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (j : Variables n) :
    NestedTotalDegree.Bound (rows p D s A β j) 1 := by
  apply NestedTotalDegree.sub (AffineCriticalConeSystem.parameter_degree p D s A j)
  intro e
  rw [coeff_C]
  split_ifs <;> simp

theorem eval_spatial (φ : MvPolynomial (Fin n) K →+* L) (hφ : φ.comp C = algebraMap K L)
    (p : MvPolynomial (Fin n) K) (z : Variables n → L) :
    (spatial p).eval₂ φ z = aeval (z ∘ Sum.inl) p := by
  rw [spatial, eval_lift φ hφ, aeval_def, eval₂_rename, aeval_def]

theorem roots_iff (φ : MvPolynomial (Fin n) K →+* L) (hφ : φ.comp C = algebraMap K L)
    (p : MvPolynomial (Fin n) K) (D : ℕ) (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (β : Fin n → K) (z : Variables n → L) :
    (∀ j, (rows p D s A β j).eval₂ φ z = 0) ↔
      aeval (z ∘ Sum.inl) p = 0 ∧
      (∀ r ∈ s, ∑ i, algebraMap K L (A r i) * z (Sum.inl i) = algebraMap K L (β r)) ∧
      (∀ i, aeval (z ∘ Sum.inl) (pderiv i p) = φ (X i) * z (Sum.inr 0) ^ (D - 1) +
        ∑ r, algebraMap K L (A r i) * z (Sum.inr r.succ) ^ (D - 1)) ∧
      ∀ r, r ∉ s → z (Sum.inr r.succ) ^ (D - 1) = 0 := by
  have hgrad (i : Fin n) : (rows p D s A β (Sum.inl i)).eval₂ φ z = 0 ↔
      aeval (z ∘ Sum.inl) (pderiv i p) = φ (X i) * z (Sum.inr 0) ^ (D - 1) +
        ∑ r, algebraMap K L (A r i) * z (Sum.inr r.succ) ^ (D - 1) := by
    simp only [rows, offset, map_zero, sub_zero, AffineCriticalConeSystem.rows,
      eval₂_sub, eval₂_mul, eval₂_C, eval_lift φ hφ, aeval_def,
      eval₂_rename, oldGradient, eval₂_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
    constructor <;> intro h <;> linear_combination h
  have hsource : (rows p D s A β (Sum.inr 0)).eval₂ φ z = aeval (z ∘ Sum.inl) p := by
    simp only [rows, offset, Fin.cases_zero, map_zero, sub_zero, AffineCriticalConeSystem.rows,
      eval_lift φ hφ, aeval_def, eval₂_rename]
  have hheight (r : Fin n) (hr : r ∈ s) : (rows p D s A β (Sum.inr r.succ)).eval₂ φ z = 0 ↔
      (∑ i, algebraMap K L (A r i) * z (Sum.inl i)) = algebraMap K L (β r) := by
    have hβ : φ (C (β r)) = algebraMap K L (β r) := congrArg (fun f : K →+* L => f (β r)) hφ
    simp only [rows, offset, Fin.cases_succ, hr, ite_true, AffineCriticalConeSystem.rows,
      eval₂_sub, eval₂_C, hβ, eval_lift φ hφ, oldHeight, map_sum, map_mul, aeval_C, aeval_X, sub_eq_zero]
  have hunused (r : Fin n) (hr : r ∉ s) : (rows p D s A β (Sum.inr r.succ)).eval₂ φ z =
      z (Sum.inr r.succ) ^ (D - 1) := by
    simp only [rows, offset, Fin.cases_succ, hr, ite_false, map_zero, sub_zero,
      AffineCriticalConeSystem.rows, eval_lift φ hφ, map_pow, aeval_X]
  constructor
  · intro h
    exact ⟨hsource ▸ h (Sum.inr 0), fun r hr => (hheight r hr).mp (h (Sum.inr r.succ)),
      fun i => (hgrad i).mp (h (Sum.inl i)), fun r hr => hunused r hr ▸ h (Sum.inr r.succ)⟩
  · rintro ⟨hp, hl, hg, hu⟩ j
    cases j with
    | inl i => exact (hgrad i).mpr (hg i)
    | inr j =>
      refine Fin.cases (hsource.symm ▸ hp) (fun r => ?_) j
      by_cases hr : r ∈ s
      · exact (hheight r hr).mpr (hl r hr)
      · exact (hunused r hr).symm ▸ hu r hr

/-- Every original critical root lifts over an algebraically closed field,
without requiring its objective or old multipliers to be nonzero. -/
theorem lift_critical_root [IsAlgClosed L] (φ : MvPolynomial (Fin n) K →+* L)
    (hφ : φ.comp C = algebraMap K L) (p : MvPolynomial (Fin n) K) (D : ℕ) (hD : 1 < D)
    (s : Finset (Fin n)) (A : Fin n → Fin n → K) (β : Fin n → K)
    (x : Fin n → L) (μ : Fin (n + 1) → L) (hp : aeval x p = 0)
    (hl : ∀ r ∈ s, ∑ i, algebraMap K L (A r i) * x i = algebraMap K L (β r))
    (hg : ∀ i, aeval x (pderiv i p) = φ (X i) * μ 0 + ∑ r, algebraMap K L (A r i) * μ r.succ)
    (hu : ∀ r, r ∉ s → μ r.succ = 0) :
    ∃ z : Variables n → L, z ∘ Sum.inl = x ∧
      (∀ r, z (Sum.inr r) ^ (D - 1) = μ r) ∧ ∀ j, (rows p D s A β j).eval₂ φ z = 0 := by
  choose ν hν using fun r => IsAlgClosed.exists_pow_nat_eq (μ r) (by omega : 0 < D - 1)
  refine ⟨Sum.elim x ν, rfl, hν, (roots_iff φ hφ p D s A β (Sum.elim x ν)).mpr ?_⟩
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, hν] using And.intro hp (And.intro hl (And.intro hg hu))

end LeanCanny.Algebra.AffineCriticalPowerSystem
