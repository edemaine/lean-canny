/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerInfinity
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Retaining every original affine critical root in the power tower -/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {n k : ℕ}

lemma row_index_eq (t : Fin k) (j : Variables n) : rowEquiv n k (t, j) =
    TriangularPolynomialRows.block (width n) t.val k t.isLt (blockEquiv n j) := by
  apply Fin.ext
  change ((blockEquiv n) j).val + width n * t.val = t.val * width n + ((blockEquiv n) j).val
  ac_rfl

lemma current_eq (t : Fin k) (i : Fin n) : current t i =
    FlatAffineCriticalIndexedRows.current t.val t.isLt i := row_index_eq t (Sum.inl i)

lemma multiplier_eq (t : Fin k) (r : Fin (n + 1)) : multiplier t r =
    FlatAffineCriticalIndexedRows.multiplier t.val t.isLt r := row_index_eq t (Sum.inr r)

lemma current_function_eq (t : Fin k) : current (n := n) t =
    FlatAffineCriticalIndexedRows.current t.val t.isLt := funext (current_eq t)

noncomputable def powerPoint {K : Type*} [Monoid K] (D : ℕ) (z : Index n k → K) (j : Index n k) : K :=
  match ((rowEquiv n k).symm j).2 with
  | .inl _ => z j
  | .inr _ => z j ^ (D - 1)

@[simp] lemma powerPoint_current {K : Type*} [Monoid K] (D : ℕ) (z : Index n k → K)
    (t : Fin k) (i : Fin n) : powerPoint D z (current t i) = z (current t i) := by
  simp only [powerPoint, current, Equiv.symm_apply_apply]

@[simp] lemma powerPoint_multiplier {K : Type*} [Monoid K] (D : ℕ) (z : Index n k → K)
    (t : Fin k) (r : Fin (n + 1)) : powerPoint D z (multiplier t r) = z (multiplier t r) ^ (D - 1) := by
  simp only [powerPoint, multiplier, Equiv.symm_apply_apply]

lemma eval_height_powerPoint {K : Type*} [CommRing K] (phi : ℤ →+* K)
    (D : ℕ) (z : Index n k → K) (t : Fin k) (a : Fin n → ℤ) :
    (AffineHeightPolynomial.polynomial a (FlatAffineCriticalIndexedRows.current t.val t.isLt)).eval₂ phi (powerPoint D z) =
      (height t a).eval₂ phi z := by
  simp only [AffineHeightPolynomial.polynomial, height, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X,
    ← current_eq, powerPoint_current]

lemma eval_level_powerPoint {K : Type*} [CommRing K] (phi : ℤ →+* K)
    (D : ℕ) (z : Index n k → K) (t : Fin k) (b : Level n t.val ℤ) :
    (rename (FlatAffineCriticalIndexedRows.embedding t.val t.isLt) (rename Sum.inl b.polynomial)).eval₂ phi (powerPoint D z) =
      (levelPolynomial t b).eval₂ phi z := by
  rw [FlatAffineCriticalIndexedRows.rename_level]
  cases b with
  | constant c => simp only [levelPolynomial, levelLinear, levelConstant, zero_add, eval₂_C]
  | height j a =>
    simp only [levelPolynomial, levelLinear, levelConstant, map_zero, add_zero]
    exact eval_height_powerPoint phi D z ⟨j.val, j.isLt.trans t.isLt⟩ a
  | midpoint l r a =>
    simp only [levelPolynomial, levelLinear, levelConstant, map_zero, add_zero, eval₂_add]
    rw [eval_height_powerPoint phi D z ⟨l.val, l.isLt.trans t.isLt⟩ a,
      eval_height_powerPoint phi D z ⟨r.val, r.isLt.trans t.isLt⟩ a]

lemma row_zero_iff_original {K : Type*} [Field K] (phi : ℤ →+* K)
    (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : 1 < D) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → ℤ) (b : (t : ℕ) → Fin n → Level n t ℤ)
    (z : Index n k → K) (t : Fin k) (j : Variables n) :
    (row p D (fun t : Fin k => s t.val) (fun t => a t.val) (fun t => b t.val) t j).eval₂ phi z = 0 ↔
      (FlatAffineCriticalTower.system p s a b k (rowEquiv n k (t, j))).eval₂ phi (powerPoint D z) = 0 := by
  cases j with
  | inl i =>
    rw [show rowEquiv n k (t, Sum.inl i) = FlatAffineCriticalIndexedRows.current t.val t.isLt i from current_eq t i,
      FlatAffineCriticalIndexedRows.gradient_row]
    simp only [row, gradient, eval₂_sub, eval₂_rename, eval₂_sum, eval₂_mul, eval₂_C,
      eval₂_pow, eval₂_X, ← current_function_eq, ← multiplier_eq, powerPoint_multiplier]
    have he : powerPoint D z ∘ current t = z ∘ current t := by funext i; exact powerPoint_current D z t i
    rw [he]
  | inr r =>
    refine Fin.cases ?_ (fun r => ?_) r
    · rw [show rowEquiv n k (t, Sum.inr 0) = FlatAffineCriticalIndexedRows.multiplier t.val t.isLt 0 from multiplier_eq t 0,
        FlatAffineCriticalIndexedRows.source_row]
      simp only [row, Fin.cases_zero, eval₂_rename, ← current_function_eq]
      have he : powerPoint D z ∘ current t = z ∘ current t := by funext i; exact powerPoint_current D z t i
      rw [he]
    · rw [show rowEquiv n k (t, Sum.inr r.succ) = FlatAffineCriticalIndexedRows.multiplier t.val t.isLt r.succ from multiplier_eq t r.succ,
        FlatAffineCriticalIndexedRows.level_row]
      by_cases hr : r ∈ s t.val
      · simp only [row, Fin.cases_succ, hr, ite_true, eval₂_sub, eval_height_powerPoint, eval_level_powerPoint]
      · simp only [row, Fin.cases_succ, hr, ite_false, eval₂_X, ← multiplier_eq, powerPoint_multiplier]
        exact (pow_eq_zero_iff (by omega : D - 1 ≠ 0)).symm

theorem roots_iff_original {K : Type*} [Field K] (phi : ℤ →+* K)
    (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : 1 < D) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → ℤ) (b : (t : ℕ) → Fin n → Level n t ℤ)
    (z : Index n k → K) :
    (∀ i, (system p D (fun t : Fin k => s t.val) (fun t => a t.val) (fun t => b t.val) i).eval₂ phi z = 0) ↔
      ∀ i, (FlatAffineCriticalTower.system p s a b k i).eval₂ phi (powerPoint D z) = 0 := by
  constructor
  · intro h i
    obtain ⟨⟨t, j⟩, rfl⟩ := (rowEquiv n k).surjective i
    apply (row_zero_iff_original phi p D hD s a b z t j).mp
    simpa only [system_row] using h (rowEquiv n k (t, j))
  · intro h i
    obtain ⟨⟨t, j⟩, rfl⟩ := (rowEquiv n k).surjective i
    rw [system_row]
    exact (row_zero_iff_original phi p D hD s a b z t j).mpr (h _)

theorem powerPoint_surjective {K : Type*} [Field K] [IsAlgClosed K] (D : ℕ) (hD : 1 < D) :
    Function.Surjective (powerPoint (n := n) (k := k) (K := K) D) := by
  intro x
  choose nu hnu using fun j => IsAlgClosed.exists_pow_nat_eq (x j) (by omega : 0 < D - 1)
  let z : Index n k → K := fun j => match ((rowEquiv n k).symm j).2 with
    | .inl _ => x j
    | .inr _ => nu j
  refine ⟨z, ?_⟩
  funext j
  unfold powerPoint
  cases hj : ((rowEquiv n k).symm j).2 with
  | inl i => simp only [z, hj]
  | inr r => simpa only [z, hj] using hnu j

/-- Finiteness passes to the actual original Lagrange tower, including all
singular roots. Power substitution is used only to prove completeness. -/
theorem finite_original_roots (low H : MvPolynomial (Fin n) ℤ) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → ℤ) (b : (t : ℕ) → Fin n → Level n t ℤ)
    (hcone : ∀ t : Fin k, ConeRootFree H (s t.val) (a t.val)) :
    {z : Index n k → ℂ | ∀ i, (FlatAffineCriticalTower.system (low + H) s a b k i).eval₂ (Int.castRingHom ℂ) z = 0}.Finite := by
  have hf := finite_roots (K := ℂ) low H D hlow hH hD (fun t : Fin k => s t.val) (fun t => a t.val)
    (fun t => b t.val) hcone
  apply (hf.image (powerPoint D)).subset
  intro x hx
  obtain ⟨z, rfl⟩ := powerPoint_surjective (n := n) (k := k) D hD x
  exact ⟨z, (roots_iff_original (Int.castRingHom ℂ) (low + H) D hD s a b z).mpr hx, rfl⟩

theorem finite_real_original_roots (low H : MvPolynomial (Fin n) ℤ) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → ℤ) (b : (t : ℕ) → Fin n → Level n t ℤ)
    (hcone : ∀ t : Fin k, ConeRootFree H (s t.val) (a t.val)) :
    {z : Index n k → ℝ | ∀ i, (FlatAffineCriticalTower.system (low + H) s a b k i).eval₂ (Int.castRingHom ℝ) z = 0}.Finite := by
  let lift : (Index n k → ℝ) → (Index n k → ℂ) := fun z i => Complex.ofRealHom (z i)
  have hi : Function.Injective lift := by
    intro x y hxy
    funext i
    exact Complex.ofReal_injective (congrFun hxy i)
  have hf := finite_original_roots low H D hlow hH hD s a b hcone
  apply (hf.preimage hi.injOn).subset
  intro z hz i
  have he : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := Subsingleton.elim _ _
  have h := congrArg Complex.ofRealHom (hz i)
  rw [hom_eval₂, he, map_zero] at h
  exact h

end LeanCanny.Algebra.FlatAffinePowerTower
