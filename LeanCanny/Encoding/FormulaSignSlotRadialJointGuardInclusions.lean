/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
/-! # Stable ordinal inclusions into the actual extended joint catalogue -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointGuardInclusions
open FormulaSignSlotRadialJointCoefficientCatalogue

theorem raw_index_lt (c : List Bool) (i : ℕ) (hi : i < count c) :
    i < family.count c := hi.trans_le (raw_count_le c)

theorem grid_index_lt (c : List Bool) (i : ℕ)
    (hi : i < FormulaSignSlotRadialJointGridCompleteCatalogue.family.count c) :
    count c + i < family.count c :=
  Nat.add_lt_add_left (hi.trans_le (FormulaSignSlotRadialJointGuardFeatures.grid_count_le c)) _

theorem tarski_index_lt (c : List Bool) (i : ℕ)
    (hi : i < FormulaSignSlotRadialJointRadiusTarskiCatalogue.family.count c) :
    count c + FormulaSignSlotRadialJointGridCompleteCatalogue.family.count c + i < family.count c := by
  have H : FormulaSignSlotRadialJointGridCompleteCatalogue.family.count c + i <
      FormulaSignSlotRadialJointGuardFeatures.baseFamily.count c := Nat.add_lt_add_left hi _
  change count c + FormulaSignSlotRadialJointGridCompleteCatalogue.family.count c + i <
    count c + FormulaSignSlotRadialJointGuardFeatures.family.count c
  have HB := H.trans_le (FormulaSignSlotRadialJointGuardFeatures.base_count_le c)
  omega

theorem principal_index_lt (c : List Bool) (i : ℕ)
    (hi : i < FormulaSignSlotRadialJointPrincipalWindowCatalogue.family.count c) :
    principalIndex c i < family.count c :=
  Nat.add_lt_add_left (FormulaSignSlotRadialJointGuardFeatures.principal_index_lt c i hi) _

theorem value_index_lt (c : List Bool) (i : ℕ)
    (hi : i < FormulaSignSlotRadialJointValueWindowCatalogue.family.count c) :
    valueIndex c i < family.count c :=
  Nat.add_lt_add_left (FormulaSignSlotRadialJointGuardFeatures.value_index_lt c i hi) _


private theorem eval_heq {n m : ℕ} (h : n = m) (p : MvPolynomial (Fin n) ℤ)
    (q : MvPolynomial (Fin m) ℤ) (hp : HEq p q) (v : ℕ → ℝ) :
    p.eval₂ (Int.castRingHom ℝ) (fun j => v j.val) =
      q.eval₂ (Int.castRingHom ℝ) (fun j => v j.val) := by
  cases h
  have H : p = q := eq_of_heq hp
  rw [H]

theorem tarski_feature_eval (c : List Bool) (i : ℕ)
    (hi : i < FormulaSignSlotRadialJointRadiusTarskiCatalogue.family.count c) (v : ℕ → ℝ) :
    (family.feature c (count c + FormulaSignSlotRadialJointGridCompleteCatalogue.family.count c + i)).eval₂
      (Int.castRingHom ℝ) (fun j => v j.val) =
    (FormulaSignSlotRadialJointRadiusTarskiCatalogue.family.feature c i).eval₂
      (Int.castRingHom ℝ) (fun j => v j.val) := by
  have HB : FormulaSignSlotRadialJointGridCompleteCatalogue.family.count c + i <
      FormulaSignSlotRadialJointGuardFeatures.family.count c :=
    (Nat.add_lt_add_left hi _).trans_le (FormulaSignSlotRadialJointGuardFeatures.base_count_le c)
  rw [Nat.add_assoc]
  exact (guard_feature_eval c _ HB v).trans
    (eval_heq rfl _ _ (FormulaSignSlotRadialJointGuardFeatures.tarski_feature c i hi) v)

end LeanCanny.Encoding.FormulaSignSlotRadialJointGuardInclusions
