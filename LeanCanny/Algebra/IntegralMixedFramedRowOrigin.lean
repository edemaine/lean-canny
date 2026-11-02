/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralPrefixRowOrigin
public import LeanCanny.Algebra.IntegralMixedFramedHistoryOrigin

/-! # Each actual framed prefix row retains its own creating equation

An older scalar row is renamed through the persistent newest-first variable
embedding. Its coefficients are the literal original creator equation; later
source changes do not reinterpret that row.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory UniformIntegralPrefix
open MvPolynomial UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem Origin.row {initial : State P S B 0 ι} {cs : List (Instruction n B)}
    {h : cs.length≤S+1} {i : Fin cs.length} (o : Origin initial cs h i) :
    (run initial cs h).sampler.scalarPrefix.rows i=
      rename (UniformIntegralPowerSchedule.embed o.chain.le) ((birthPrefix initial cs h i).rows 0) := by
  have HE : UniformIntegralPowerSchedule.embed o.chain.le (0 : Fin ((older cs i).length+1))=i := by
    apply Fin.ext
    simp only [UniformIntegralPowerSchedule.embed,Fin.val_zero,Nat.add_zero]
    rw [older_length]
    have HI:=i.isLt
    omega
  have HR := o.chain.rows 0
  rw [HE] at HR
  exact HR

theorem Origin.row_layout_new {initial : State P S B 0 ι} {cs : List (Instruction n B)}
    {h : cs.length≤S+1} {i : Fin cs.length} (o : Origin initial cs h i) :
    UniformIntegralPowerSchedule.embed o.chain.le
      (UniformIntegralPrefixRows.layout (older cs i).length (Sum.inr ()))=i := by
  apply Fin.ext
  simp only [UniformIntegralPrefixRows.layout,Sum.elim_inr,UniformIntegralPowerSchedule.embed,
    Fin.val_zero,Nat.add_zero]
  rw [older_length]
  have HI:=i.isLt
  omega

theorem Origin.row_layout_old {initial : State P S B 0 ι} {cs : List (Instruction n B)}
    {h : cs.length≤S+1} {i : Fin cs.length} (o : Origin initial cs h i) (j : Fin (older cs i).length) :
    (UniformIntegralPowerSchedule.embed o.chain.le
      (UniformIntegralPrefixRows.layout (older cs i).length (Sum.inl j))).val=i.val+1+j.val := by
  simp only [UniformIntegralPrefixRows.layout,Sum.elim_inl,UniformIntegralPowerSchedule.embed,Fin.val_succ]
  have HL:=older_length cs i
  have HI:=i.isLt
  omega

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
