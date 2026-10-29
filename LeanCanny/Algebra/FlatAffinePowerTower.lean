/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCriticalIndexedRows
public import LeanCanny.Algebra.AffineFiniteCoordinates
public import LeanCanny.Algebra.HomogenizationAtInfinity
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! # Multiplier-power towers with linear inactive rows

Inactive multipliers are constrained by X = 0, while gradient rows use their
(D-1)-st powers. Thus row degrees depend only on the source degree and row
position, independently of active flags. Old heights still reference the
original ambient blocks directly.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {n k : ℕ}

abbrev Index (n k : ℕ) := Fin (k * width n)

def rowEquiv (n k : ℕ) : (Fin k × Variables n) ≃ Index n k :=
  (Equiv.prodCongr (Equiv.refl _) (blockEquiv n)).trans finProdFinEquiv

def current (t : Fin k) (i : Fin n) : Index n k := rowEquiv n k (t, Sum.inl i)
def multiplier (t : Fin k) (r : Fin (n + 1)) : Index n k := rowEquiv n k (t, Sum.inr r)

noncomputable def height (t : Fin k) (a : Fin n → ℤ) : MvPolynomial (Index n k) ℤ :=
  ∑ i, C (a i) * X (current t i)

noncomputable def levelLinear (t : Fin k) : Level n t.val ℤ → MvPolynomial (Index n k) ℤ
  | .constant _ => 0
  | .height j a => height ⟨j.val, j.isLt.trans t.isLt⟩ a
  | .midpoint l r a => height ⟨l.val, l.isLt.trans t.isLt⟩ a + height ⟨r.val, r.isLt.trans t.isLt⟩ a

def levelConstant (t : Fin k) : Level n t.val ℤ → ℤ
  | .constant c => c
  | .height _ _ | .midpoint _ _ _ => 0

noncomputable def levelPolynomial (t : Fin k) (b : Level n t.val ℤ) : MvPolynomial (Index n k) ℤ :=
  levelLinear t b + C (levelConstant t b)

noncomputable def gradient (p : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (t : Fin k) (i : Fin n) : MvPolynomial (Index n k) ℤ :=
  rename (current t) (pderiv i p) - ∑ r, C (a t r i) * X (multiplier t r) ^ (D - 1)

noncomputable def row (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (t : Fin k) : Variables n → MvPolynomial (Index n k) ℤ
  | .inl i => gradient p D a t i
  | .inr r => Fin.cases (rename (current t) p)
      (fun j => if j ∈ s t then height t (a t j.succ) - levelPolynomial t (b t j)
        else X (multiplier t j.succ)) r

def rowDegree (D : ℕ) : Variables n → ℕ
  | .inl _ => D - 1
  | .inr r => Fin.cases D (fun _ => 1) r

noncomputable def system (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (j : Index n k) : MvPolynomial (Index n k) ℤ :=
  row p D s a b ((rowEquiv n k).symm j).1 ((rowEquiv n k).symm j).2

def degrees (D : ℕ) (j : Index n k) : ℕ := rowDegree D ((rowEquiv n k).symm j).2

lemma system_row (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (t : Fin k) (j : Variables n) : system p D s a b (rowEquiv n k (t, j)) = row p D s a b t j := by
  simp only [system, Equiv.symm_apply_apply]

lemma degrees_row (D : ℕ) (t : Fin k) (j : Variables n) :
    degrees D (rowEquiv n k (t, j)) = rowDegree D j := by
  simp only [degrees, Equiv.symm_apply_apply]

lemma degrees_pos (D : ℕ) (hD : 1 < D) (j : Index n k) : 0 < degrees D j := by
  unfold degrees
  cases ((rowEquiv n k).symm j).2 with
  | inl i => change 0 < D - 1; omega
  | inr r =>
    refine Fin.cases ?_ (fun _ => by change 0 < 1; decide) r
    change 0 < D
    omega

lemma height_homogeneous (t : Fin k) (a : Fin n → ℤ) : (height t a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_X (R := ℤ) (current t i)).C_mul _

lemma levelLinear_homogeneous (t : Fin k) (b : Level n t.val ℤ) : (levelLinear t b).IsHomogeneous 1 := by
  cases b with
  | constant c => exact isHomogeneous_zero _ _ _
  | height j a => exact height_homogeneous _ _
  | midpoint l r a => exact (height_homogeneous _ _).add (height_homogeneous _ _)

lemma gradient_homogeneous (H : MvPolynomial (Fin n) ℤ) (D : ℕ) (hH : H.IsHomogeneous D)
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (t : Fin k) (i : Fin n) :
    (gradient H D a t i).IsHomogeneous (D - 1) := by
  apply hH.pderiv.rename_isHomogeneous.sub
  apply IsHomogeneous.sum
  intro r _
  have hp : (X (multiplier t r) ^ (D - 1) : MvPolynomial (Index n k) ℤ).IsHomogeneous (D - 1) := by
    simpa only [one_mul] using (isHomogeneous_X (R := ℤ) (multiplier t r)).pow (D - 1)
  exact hp.C_mul _

lemma gradient_split (low H : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (t : Fin k) (i : Fin n) :
    gradient (low + H) D a t i = gradient H D a t i + rename (current t) (pderiv i low) := by
  simp only [gradient, map_add]
  ring

lemma lower_gradient_degree (low : MvPolynomial (Fin n) ℤ) (D : ℕ) (hlow : low.totalDegree < D)
    (hD : 1 < D) (t : Fin k) (i : Fin n) :
    (rename (current t) (pderiv i low)).totalDegree < D - 1 := by
  have h := (totalDegree_rename_le (current t) (pderiv i low)).trans (PartialDerivativeDegree.degree_le low i)
  omega

lemma row_degree (low H : MvPolynomial (Fin n) ℤ) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (t : Fin k) (j : Variables n) : (row (low + H) D s a b t j).totalDegree ≤ rowDegree D j := by
  cases j with
  | inl i =>
    rw [row, gradient_split]
    exact (totalDegree_add _ _).trans (max_le (gradient_homogeneous H D hH a t i).totalDegree_le
      (lower_gradient_degree low D hlow hD t i).le)
  | inr r =>
    refine Fin.cases ?_ (fun j => ?_) r
    · exact (totalDegree_rename_le _ _).trans ((totalDegree_add _ _).trans (max_le hlow.le hH.totalDegree_le))
    · simp only [row, Fin.cases_succ, rowDegree]
      split_ifs
      · apply (totalDegree_sub _ _).trans (max_le (height_homogeneous _ _).totalDegree_le ?_)
        exact (totalDegree_add _ _).trans (max_le (levelLinear_homogeneous _ _).totalDegree_le (by change (C (levelConstant t (b t j)) : MvPolynomial (Index n k) ℤ).totalDegree ≤ 1; simp only [totalDegree_C]; omega))
      · simp

lemma system_degree (low H : MvPolynomial (Fin n) ℤ) (D : ℕ) (hlow : low.totalDegree < D)
    (hH : H.IsHomogeneous D) (hD : 1 < D) (s : Fin k → Finset (Fin n))
    (a : Fin k → Fin (n + 1) → Fin n → ℤ) (b : (t : Fin k) → Fin n → Level n t.val ℤ)
    (j : Index n k) : (system (low + H) D s a b j).totalDegree ≤ degrees D j :=
  row_degree low H D hlow hH hD s a b _ _

end LeanCanny.Algebra.FlatAffinePowerTower
