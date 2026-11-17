/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.Torsion.Basic

/-! # A common invariant line determines an algebra character -/

public section

namespace LeanCanny.CountingHierarchy

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Scalar actions on a nonzero common invariant line form an algebra
 homomorphism. The line need not contain the algebra's unit. -/
theorem exists_character_of_invariant_line (w : A) (hw : w ≠ 0)
    (hline : ∀ a : A, ∃ c : K, c • w = a * w) :
    ∃ χ : A →ₐ[K] K, ∀ a : A, χ a • w = a * w := by
  classical
  choose c hc using hline
  have hinj : Function.Injective (fun t : K => t • w) := smul_left_injective K hw
  have hzero : c 0 = 0 := hinj (by simpa only [zero_smul, zero_mul] using hc 0)
  have hone : c 1 = 1 := hinj (by simpa only [one_smul, one_mul] using hc 1)
  have hadd (a b : A) : c (a + b) = c a + c b := by
    apply hinj
    change c (a + b) • w = (c a + c b) • w
    rw [hc, add_smul, hc, hc, add_mul]
  have hmul (a b : A) : c (a * b) = c a * c b := by
    apply hinj
    calc
      c (a * b) • w = a * b * w := hc _
      _ = a * (b * w) := mul_assoc _ _ _
      _ = a * (c b • w) := by rw [hc]
      _ = c b • (a * w) := mul_smul_comm _ _ _
      _ = c b • (c a • w) := by rw [hc]
      _ = (c a * c b) • w := by rw [smul_smul, mul_comm]
  have hcomm (t : K) : c (algebraMap K A t) = t := by
    apply hinj
    change c (algebraMap K A t) • w = t • w
    rw [hc]
    exact (Algebra.smul_def t w).symm
  exact ⟨{ toFun := c
           map_zero' := hzero
           map_one' := hone
           map_add' := hadd
           map_mul' := hmul
           commutes' := hcomm }, hc⟩

end LeanCanny.CountingHierarchy
