/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalIndexedRows
public import LeanCanny.Algebra.FlatAffineTowerRegularity

/-! # Frozen equations when one last-stage height row varies -/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffineTowerPartialRoots
open MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n k : ℕ} {R K : Type*} [CommRing R] [CommRing K]

def ancestorPoint (z : Fin ((k + 1) * width n) → K) : Fin (k * width n) → K :=
  z ∘ TriangularPolynomialRows.prefixIndex (width n) k (k + 1) (by omega)

def current (z : Fin ((k + 1) * width n) → K) : Fin n → K :=
  z ∘ FlatAffineCriticalIndexedRows.current k (Nat.lt_succ_self k)

def multipliers (z : Fin ((k + 1) * width n) → K) : Fin (n + 1) → K :=
  z ∘ FlatAffineCriticalIndexedRows.multiplier k (Nat.lt_succ_self k)

omit [CommRing K] in
theorem stagePoint_eq (z : Fin ((k + 1) * width n) → K) :
    z ∘ FlatAffineCriticalIndexedRows.embedding k (Nat.lt_succ_self k) =
      Sum.elim (ancestorPoint z ∘ TriangularPolynomialIndexing.enumerate (width n) k)
        (Sum.elim (current z) (multipliers z)) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i <;> rfl

theorem stage_value (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → R)
    (b : (t : ℕ) → Fin n → Level n t R) (z : Fin ((k + 1) * width n) → K)
    (j : Variables n) :
    (row p (s k) (a k) (fun i => (b k i).polynomial) j).eval₂ φ
      (Sum.elim (ancestorPoint z ∘ TriangularPolynomialIndexing.enumerate (width n) k)
        (Sum.elim (current z) (multipliers z))) =
      (FlatAffineCriticalTower.system p s a b (k + 1)
        (TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n j))).eval₂ φ z := by
  rw [FlatAffineCriticalIndexedRows.stage_row, eval₂_rename, stagePoint_eq]

theorem prefix_roots (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → R)
    (b : (t : ℕ) → Fin n → Level n t R) (h : Fin n)
    (z : Fin ((k + 1) * width n) → K)
    (hz : ∀ i, i ≠ FlatAffineCriticalIndexedRows.multiplier k (Nat.lt_succ_self k) h.succ →
      (FlatAffineCriticalTower.system p s a b (k + 1) i).eval₂ φ z = 0) :
    ∀ i, (FlatAffineCriticalTower.system p s a b k i).eval₂ φ (ancestorPoint z) = 0 := by
  intro i
  have HN : TriangularPolynomialRows.prefixIndex (width n) k (k + 1) (by omega) i ≠
      FlatAffineCriticalIndexedRows.multiplier k (Nat.lt_succ_self k) h.succ := by
    intro he
    have HV := congrArg Fin.val he
    change i.val = k * width n + (blockEquiv n (Sum.inr h.succ)).val at HV
    have := i.isLt
    omega
  have HR := hz (TriangularPolynomialRows.prefixIndex (width n) k (k + 1) (by omega) i) HN
  rw [FlatAffineCriticalTower.system, TriangularPolynomialRows.old_row, eval₂_rename] at HR
  exact HR

theorem stage_roots (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → R)
    (b : (t : ℕ) → Fin n → Level n t R) (h : Fin n)
    (z : Fin ((k + 1) * width n) → K)
    (hz : ∀ i, i ≠ FlatAffineCriticalIndexedRows.multiplier k (Nat.lt_succ_self k) h.succ →
      (FlatAffineCriticalTower.system p s a b (k + 1) i).eval₂ φ z = 0) :
    ∀ j, j ≠ Sum.inr h.succ → (row p (s k) (a k) (fun i => (b k i).polynomial) j).eval₂ φ
      (Sum.elim (ancestorPoint z ∘ TriangularPolynomialIndexing.enumerate (width n) k)
        (Sum.elim (current z) (multipliers z))) = 0 := by
  intro j hj
  rw [stage_value]
  apply hz
  intro he
  apply hj
  have HV := congrArg Fin.val he
  change k * width n + (blockEquiv n j).val = k * width n + (blockEquiv n (Sum.inr h.succ)).val at HV
  exact (blockEquiv n).injective (Fin.ext (by omega))

theorem append_values (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → R)
    (b : (t : ℕ) → Fin n → Level n t R) (h : Fin n) (v : K)
    (x : Fin (k * width n) → K) (y : Variables n → K)
    (hx : ∀ i, (FlatAffineCriticalTower.system p s a b k i).eval₂ φ x = 0)
    (hy : ∀ j, (row p (s k) (a k) (fun i => (b k i).polynomial) j).eval₂ φ
      (Sum.elim (x ∘ TriangularPolynomialIndexing.enumerate (width n) k) y) =
        if j = Sum.inr h.succ then v else 0) :
    ∀ i, (FlatAffineCriticalTower.system p s a b (k + 1) i).eval₂ φ
      (FlatAffineTowerRegularity.appendPoint k x y) =
        if i = FlatAffineCriticalIndexedRows.multiplier k (Nat.lt_succ_self k) h.succ then v else 0 := by
  intro i
  obtain ⟨w, rfl⟩ := (TriangularPolynomialIndexing.enumerate (width n) (k + 1)).surjective i
  cases w with
  | inl w =>
    rw [← TriangularPolynomialStageRegularity.prefix_enumerate]
    have HN : TriangularPolynomialRows.prefixIndex (width n) k (k + 1) (by omega)
        (TriangularPolynomialIndexing.enumerate (width n) k w) ≠
          FlatAffineCriticalIndexedRows.multiplier k (Nat.lt_succ_self k) h.succ := by
      intro he
      have HV := congrArg Fin.val he
      change (TriangularPolynomialIndexing.enumerate (width n) k w).val =
        k * width n + (blockEquiv n (Sum.inr h.succ)).val at HV
      have := (TriangularPolynomialIndexing.enumerate (width n) k w).isLt
      omega
    rw [ite_eq_right HN, FlatAffineCriticalTower.system, TriangularPolynomialRows.old_row, eval₂_rename,
      FlatAffineTowerRegularity.appendPoint_prefix]
    exact hx _
  | inr w =>
    have HI : TriangularPolynomialIndexing.enumerate (width n) (k + 1) (Sum.inr w) =
        TriangularPolynomialRows.block (width n) k (k + 1) (by omega) w :=
      Fin.ext (TriangularPolynomialIndexing.enumerate_new (width n) k w)
    rw [HI]
    let j := (blockEquiv n).symm w
    have HW : w = blockEquiv n j := (Equiv.apply_symm_apply _ _).symm
    rw [HW, FlatAffineCriticalIndexedRows.stage_row, eval₂_rename]
    change (row p (s k) (a k) (fun i => (b k i).polynomial) j).eval₂ φ
      (FlatAffineTowerRegularity.stagePoint k (k + 1) (by omega)
        (FlatAffineTowerRegularity.appendPoint k x y)) = _
    rw [FlatAffineTowerRegularity.stagePoint_appendPoint, hy]
    have HE : TriangularPolynomialRows.block (width n) k (k + 1) (by omega) (blockEquiv n j) =
        FlatAffineCriticalIndexedRows.multiplier k (Nat.lt_succ_self k) h.succ ↔ j = Sum.inr h.succ := by
      constructor
      · intro he
        have HV := congrArg Fin.val he
        change k * width n + (blockEquiv n j).val = k * width n + (blockEquiv n (Sum.inr h.succ)).val at HV
        exact (blockEquiv n).injective (Fin.ext (by omega))
      · intro he
        simp only [he, FlatAffineCriticalIndexedRows.multiplier]
    simp only [HE]

end LeanCanny.Algebra.FlatAffineTowerPartialRoots
