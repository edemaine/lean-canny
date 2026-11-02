/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalUnitRecord
public import LeanCanny.Algebra.IntegralMixedCausalPlanBounds
/-! # Literal midpoint/scale metadata has a constant original resource bound

The bound excludes the interpreted slope. Current-Q growth is charged by the
existing causal bank induction; original reference labels do not affect nodes.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalUnitRecordBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open IntegralMixedCausalRecordBits IntegralMixedCausalPlanBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem atom_nodes (code : List Bool) (birth : ℕ) :
    (IntegralMixedCausalRowCode.atom code birth).nodes=1 := by
  unfold IntegralMixedCausalRowCode.atom
  split_ifs <;> rfl

private theorem atom_coefficients (code : List Bool) (birth C : ℕ) :
    (IntegralMixedCausalRowCode.atom code birth).CoefficientsBound C := by
  unfold IntegralMixedCausalRowCode.atom
  split_ifs
  · trivial
  · exact Nat.zero_le C

theorem row_nodes (code : List Bool) (physical : Bool) (birth i : ℕ) :
    (row code physical birth i).nodes≤3 := by
  have H (a b : List Bool) : (IntegralMixedCausalRowCode.expression a b birth).nodes≤3 := by
    unfold IntegralMixedCausalRowCode.expression
    split_ifs
    · simp only [AffineExpr.nodes,atom_nodes]
      decide
    · rw [atom_nodes]
      decide
  exact H _ _

theorem row_coefficients (code : List Bool) (physical : Bool) (birth i C : ℕ) :
    (row code physical birth i).CoefficientsBound C := by
  have H (a b : List Bool) : (IntegralMixedCausalRowCode.expression a b birth).CoefficientsBound C := by
    unfold IntegralMixedCausalRowCode.expression
    split_ifs
    · exact ⟨atom_coefficients _ _ _,atom_coefficients _ _ _⟩
    · exact atom_coefficients _ _ _
  exact H _ _

theorem scale_size (code : List Bool) (physical : Bool) (i : ℕ) : (scale code physical i).natAbs.size≤2 := by
  unfold scale
  split_ifs <;> decide

theorem record_core {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B)
    (C L : ℕ) (hC : 2≤C) (hL : 3≤L) :
    Template.core C L (record S hn birth code hcap).template := by
  unfold record
  cases IntegralMixedUnitRecordCode.critical code
  · simp only [Bool.false_eq_true,ite_false,Template.core]
    exact ⟨fun i => (row_nodes code false birth i.val).trans hL,
      fun i => row_coefficients code false birth i.val C,fun i => (scale_size code false i.val).trans hC⟩
  · simp only [ite_true,Template.core]
    exact ⟨fun i => (row_nodes code true birth i.val).trans hL,
      fun i => row_coefficients code true birth i.val C,fun i => (scale_size code true i.val).trans hC⟩

theorem original_bounds {n B : ℕ} (S : SpatialSource n) (hn : 0<n) (birth : ℕ)
    (code : List Bool) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B)
    (G F W D L : ℕ) (hlow : ∀ e,(S.low.coeff e).natAbs≤2^(F*G+1))
    (hlead : S.leading.natAbs.size≤F*G+1) (hW : S.degree.size≤W) (hD : S.degree≤D)
    (hC : 2≤F*G+1) (hL : 3≤L) :
    OriginalBounds G F W D L (record S hn birth code hcap) :=
  ⟨hlow,hlead,hW,hD,hcap,record_core S hn birth code hcap _ _ hC hL⟩

end LeanCanny.Algebra.IntegralMixedCausalUnitRecordBits
