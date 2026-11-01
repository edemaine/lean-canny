/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CommonHeightRecursivePass
public import LeanCanny.Algebra.IntegralMixedPhysicalQuery

/-! # Actual mixed-bank denominators through earlier-leading requests

The resumable pass reads the ACTUAL retained integer denominator table.
Each query identifies its literal newest-first index and producer birth.
An omitted valid index gives its actual complementary denominator; an
out-of-range omitted index gives the complete common denominator.
No integer/critical-only recurrence or FP leading shortcut is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalBankCofactor
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralMixedHistory IntegralMixedPhysicalCriticalBits
open scoped Classical BigOperators

noncomputable def scale (F : Family) (q : List Bool) (i : ℕ) : ℤ :=
  if hi : i < F.birth q then (F.state q).bank.denominator ⟨i, hi⟩ else 1

noncomputable def scalars (F : Family) (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0)
    (selected : List Bool → ℕ) : CommonHeightBits.Scalars where
  count := F.birth
  modulus := modulus
  modulus_ne_zero := hmod
  scale := scale F
  selected := selected

theorem controls (F : Family) (a : IntegralMixedPhysicalQueryBits.InputMetadata F) (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0)
    (hM : BinaryFn modulus) (selected : List Bool → ℕ) (hs : BinaryFn selected) :
    CommonHeightRecursivePass.Controls (scalars F modulus hmod selected) :=
  ⟨a.birth, hM, hs⟩

theorem denominator_eq (F : Family) (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0)
    (selected : List Bool → ℕ) (q : List Bool) :
    (scalars F modulus hmod selected).denominator q = commonDenominator (F.state q) := by
  unfold CommonHeightBits.Scalars.denominator
  rw [Finset.prod_range]
  change (∏ i : Fin (F.birth q), scale F q i.val) = _
  have HE (i : Fin (F.birth q)) : scale F q i.val = (F.state q).bank.denominator i := by
    rw [scale, dite_eq_left i.isLt]
  simp only [HE]
  rfl

theorem cofactor_eq (F : Family) (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0)
    (selected : List Bool → ℕ) (q : List Bool) (i : Fin (F.birth q)) (hi : selected q = i.val) :
    (scalars F modulus hmod selected).cofactor q =
      CommonIntegerDenominator.denominator (Finset.univ.erase i) (F.state q).bank.denominator := by
  change (∏ j ∈ Finset.range (F.birth q), if j = selected q then 1 else scale F q j) = _
  rw [hi, CommonHeightBits.cofactor_eq_erase]
  unfold CommonIntegerDenominator.denominator
  apply Finset.prod_congr rfl
  intro j _
  change (if hj : j.val < F.birth q then (F.state q).bank.denominator ⟨j.val, hj⟩ else 1) = _
  rw [dite_eq_left j.isLt]

theorem cofactor_outside (F : Family) (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0)
    (selected : List Bool → ℕ) (q : List Bool) (hi : F.birth q ≤ selected q) :
    (scalars F modulus hmod selected).cofactor q = commonDenominator (F.state q) := by
  rw [← denominator_eq F modulus hmod selected q]
  change (∏ j ∈ Finset.range (F.birth q), if j = selected q then 1 else scale F q j) =
    ∏ j ∈ Finset.range (F.birth q), scale F q j
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (by have := Finset.mem_range.mp hj; omega)

theorem program_value (F : Family) (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0)
    (selected : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool)
    (ha : ∀ i : Fin (F.birth q), answer (task (pair q
      (pair (BinaryNatCode.encode (F.birth q - 1 - i.val)) (BinaryNatCode.encode i.val)))) =
        residueBits ((F.state q).bank.denominator i : ZMod (modulus q))) :
    (CommonHeightRecursivePass.program (scalars F modulus hmod selected) task).value answer q =
      residueBits ((scalars F modulus hmod selected).cofactor q : ZMod (modulus q)) := by
  apply CommonHeightRecursivePass.value_eq
  intro i hi
  change i < F.birth q at hi
  change answer (task (pair q (pair (BinaryNatCode.encode (F.birth q - 1 - i)) (BinaryNatCode.encode i)))) =
    residueBits (scale F q i : ZMod (modulus q))
  rw [scale, dite_eq_left hi]
  exact ha ⟨i, hi⟩

end LeanCanny.Algebra.IntegralMixedPhysicalBankCofactor
