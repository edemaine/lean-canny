/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoreReadback
/-! # Disjoint literal coordinates assemble a single real joint tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointPacking
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open FormulaSignSlotRadialJointLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def pack (A B F : ℕ → ℝ) (b wr wg : ℝ) (n : ℕ) : ℝ :=
  if n % 4 = 0 then A (n / 4) else if n % 4 = 1 then B (n / 4) else
    if n % 4 = 2 then F (n / 4) else if n = boundVariable then b else
      if n = radiusWitness then wr else if n = gapWitness then wg else 0

theorem pack_zero (A B F : ℕ → ℝ) (b wr wg : ℝ) (i : ℕ) :
    pack A B F b wr wg (column 0 i) = A i := by
  have HM : (4*i+0)%4=0 := by omega
  have HD : (4*i+0)/4=i := by omega
  simp only [pack, column, HM, HD, ite_true]
theorem pack_one (A B F : ℕ → ℝ) (b wr wg : ℝ) (i : ℕ) :
    pack A B F b wr wg (column 1 i) = B i := by
  have HM : (4*i+1)%4=1 := by omega
  have HD : (4*i+1)/4=i := by omega
  simp only [pack, column, HM, HD, ite_true, ite_false, Nat.one_ne_zero]
theorem pack_two (A B F : ℕ → ℝ) (b wr wg : ℝ) (i : ℕ) :
    pack A B F b wr wg (column 2 i) = F i := by
  have HM : (4*i+2)%4=2 := by omega
  have HD : (4*i+2)/4=i := by omega
  simp only [pack, column, HM, HD, ite_true, ite_false, Nat.succ_ne_zero, Nat.reduceEqDiff]
theorem pack_bound (A B F : ℕ → ℝ) (b wr wg : ℝ) :
    pack A B F b wr wg boundVariable = b := by norm_num [pack, boundVariable]
theorem pack_radiusWitness (A B F : ℕ → ℝ) (b wr wg : ℝ) :
    pack A B F b wr wg radiusWitness = wr := by norm_num [pack, boundVariable, radiusWitness]
theorem pack_gapWitness (A B F : ℕ → ℝ) (b wr wg : ℝ) :
    pack A B F b wr wg gapWitness = wg := by norm_num [pack, boundVariable, radiusWitness, gapWitness]

noncomputable def formal (c : List Bool) (z : Fin (FormulaSignSlotRadialFormalInput.spatial c) → ℝ)
    (a : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  if h : n < FormulaSignSlotRadialFormalInput.spatial c then z ⟨n,h⟩ else
    if h : n < FormulaSignSlotRadialFormalInput.spatial c + FormulaSignSlotSource.dimension c then
      a ⟨n - FormulaSignSlotRadialFormalInput.spatial c, by omega⟩ else
        if n = FormulaSignSlotRadialFormalInput.spatial c + FormulaSignSlotSource.dimension c then r else 0

theorem formal_spatial (c : List Bool) (z : Fin (FormulaSignSlotRadialFormalInput.spatial c) → ℝ)
    (a : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ)
    (i : Fin (FormulaSignSlotRadialFormalInput.spatial c)) : formal c z a r i.val = z i := by
  simp only [formal, dite_eq_left i.isLt]
theorem formal_center (c : List Bool) (z : Fin (FormulaSignSlotRadialFormalInput.spatial c) → ℝ)
    (a : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ)
    (i : Fin (FormulaSignSlotSource.dimension c)) :
    formal c z a r (FormulaSignSlotRadialFormalInput.spatial c + i.val) = a i := by
  have HL : ¬ FormulaSignSlotRadialFormalInput.spatial c + i.val < FormulaSignSlotRadialFormalInput.spatial c := by omega
  have HR : FormulaSignSlotRadialFormalInput.spatial c + i.val <
      FormulaSignSlotRadialFormalInput.spatial c + FormulaSignSlotSource.dimension c := by omega
  simp only [formal, dite_eq_right HL, dite_eq_left HR, Nat.add_sub_cancel_left]
theorem formal_radius (c : List Bool) (z : Fin (FormulaSignSlotRadialFormalInput.spatial c) → ℝ)
    (a : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ) :
    formal c z a r (FormulaSignSlotRadialFormalInput.spatial c + FormulaSignSlotSource.dimension c) = r := by
  have HL : ¬ FormulaSignSlotRadialFormalInput.spatial c + FormulaSignSlotSource.dimension c <
      FormulaSignSlotRadialFormalInput.spatial c := by omega
  simp only [formal, dite_eq_right HL, lt_self_iff_false, dite_false, ite_true]

theorem exists_positive_witness (r : ℝ) (hr : 0 < r) : ∃ w : ℝ, r*w^2=1 := by
  refine ⟨(Real.sqrt r)⁻¹, ?_⟩
  rw [inv_pow, Real.sq_sqrt hr.le, mul_inv_cancel₀ (ne_of_gt hr)]

end LeanCanny.Encoding.FormulaSignSlotRadialJointPacking
