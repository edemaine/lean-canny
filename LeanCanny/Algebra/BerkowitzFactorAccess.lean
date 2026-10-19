/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPower
public import LeanCanny.Algebra.MatrixMomentPower

/-!
# Direct access to a Berkowitz coefficient factor

The factor at position s uses the trailing principal block starting at s.
That block is accessed by adding s to the two indices in the original matrix;
no recursion through earlier factors or coefficient vectors is necessary.
The total direct accessor agrees with the previous recursive specification,
including its identity default after the final factor.

These are mathematical access formulas. Binary factor selection and field
writing remain separate obligations; `MatrixMomentFP` supplies the certified
scalar-moment child given encoded access to its input entries.
-/

@[expose] public section

noncomputable section

namespace LeanCanny.Algebra.Berkowitz
open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

def principalBlock (A : Matrix (Fin n) (Fin n) R) (s : ℕ) (hs : s < n) :
    Matrix (Fin (n - s - 1 + 1)) (Fin (n - s - 1 + 1)) R :=
  fun i j => A ⟨s + i.val, by have := i.isLt; omega⟩ ⟨s + j.val, by have := j.isLt; omega⟩

theorem factorAt_principalBlock (w : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (s : ℕ) (hs : s < n) : factorAt w A s = transformation w (principalBlock A s hs) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
      cases s with
      | zero =>
          rw [factorAt]
          apply congrArg (transformation w)
          ext i j
          simp [principalBlock]
      | succ s =>
          rw [factorAt, ih _ s (by omega)]
          congr 1
          · omega
          · apply (Fin.heq_fun₂_iff (α := R) (by omega) (by omega)).mpr
            intro i j
            simp only [principalBlock, Matrix.submatrix_apply]
            congr 1 <;> apply Fin.ext <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem factorAt_eq_one (w : ℕ) (A : Matrix (Fin n) (Fin n) R) (s : ℕ) (hs : n ≤ s) :
    factorAt w A s = 1 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      cases s with
      | zero => omega
      | succ s => exact ih _ s (by omega)

def factorDirect (w : ℕ) (A : Matrix (Fin n) (Fin n) R) (s : ℕ) :
    Matrix (Fin w) (Fin w) R :=
  if hs : s < n then transformation w (principalBlock A s hs) else 1

theorem factorDirect_eq (w : ℕ) (A : Matrix (Fin n) (Fin n) R) (s : ℕ) :
    factorDirect w A s = factorAt w A s := by
  by_cases hs : s < n
  · simp only [factorDirect, hs, ↓reduceDIte]
    exact (factorAt_principalBlock w A s hs).symm
  · simp only [factorDirect, hs, ↓reduceDIte]
    exact (factorAt_eq_one w A s (by omega)).symm

theorem factorDirect_apply (w : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (s : ℕ) (hs : s < n) (d k : Fin w) :
    factorDirect w A s d k = coefficientKernel (principalBlock A s hs) d.val k.val := by
  simp only [factorDirect, hs, ↓reduceDIte, transformation]

theorem coefficientKernel_cases {b : ℕ} (B : Matrix (Fin (b + 1)) (Fin (b + 1)) R)
    (d k : ℕ) : coefficientKernel B d k =
      if k + 1 = d then 1
      else if k = d then -B 0 0
      else if d < k ∧ k ≤ b then
        -borderMoment (fun i => B 0 i.succ) (fun i => B i.succ 0)
          (B.submatrix Fin.succ Fin.succ) (k - (d + 1))
      else 0 := by
  by_cases hs : k + 1 = d
  · have hd : k ≠ d := by omega
    have hm : ¬(d < k ∧ k ≤ b) := by omega
    simp [coefficientKernel, hs, hd, hm]
  by_cases hd : k = d
  · simp [coefficientKernel, hd]
  by_cases hm : d < k ∧ k ≤ b <;> simp [coefficientKernel, hs, hd, hm]

def factorMomentMatrix (A : Matrix (Fin n) (Fin n) R) (s : ℕ) (hs : s < n) :
    Matrix (Fin (n - s - 1 + 2)) (Fin (n - s - 1 + 2)) R :=
  let B := principalBlock A s hs
  MatrixMoment.matrixFin (fun i => B 0 i.succ) (fun i => B i.succ 0)
    (B.submatrix Fin.succ Fin.succ)

theorem factorDirect_moment (w : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (s : ℕ) (hs : s < n) (d k : Fin w) (hd : d.val < k.val) (hk : k.val ≤ n - s - 1) :
    factorDirect w A s d k =
      -(factorMomentMatrix A s hs ^ (k.val - (d.val + 1) + 2)) 0 (Fin.last (n - s - 1 + 1)) := by
  rw [factorDirect_apply w A s hs, coefficientKernel_cases]
  have hshift : k.val + 1 ≠ d.val := by omega
  have hdiag : k.val ≠ d.val := by omega
  simp only [hshift, hdiag, hd, hk, and_self, ↓reduceIte]
  rw [factorMomentMatrix, MatrixMoment.matrixFin_pow_moment]
  rfl

theorem powerMatrix_apply_direct (A : Matrix (Fin n) (Fin n) R)
    (p q : Fin ((n + 1) * (n + 1))) :
    powerMatrix A p q = if p.divNat.val + 1 = q.divNat.val then
      factorDirect (n + 1) A p.divNat.val p.modNat q.modNat else 0 := by
  simp only [powerMatrix, MatrixProduct.layeredFin_apply, factorDirect_eq]

end LeanCanny.Algebra.Berkowitz
