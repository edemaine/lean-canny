/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockLayout
public import LeanCanny.Algebra.IntegralCriticalFlatCoordinateQuery
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightSource
/-! # Original-key-preserving source tasks for physical row branches -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem spatialCount_eq (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) :
    spatialCount P D J base q=P.ambient (RankedHistoryTask.root (base q))+1 := by
  change P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P (base q)))+1=_
  simp only [IntegralMixedPhysicalTaskBits.saved,pairFst_pair]

noncomputable def rowSelected (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (row : List Bool→ℕ) (q : List Bool) :=
  if row q<spatialCount P D J base q then row q
  else (row q-(spatialCount P D J base q+1))%spatialCount P D J base q

theorem rowSelected_lt (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (row : List Bool→ℕ) (q : List Bool) :
    rowSelected P D J base row q<spatialCount P D J base q := by
  unfold rowSelected
  split_ifs with h
  · exact h
  · exact Nat.mod_lt _ (Nat.succ_pos _)

theorem rowSelected_unary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP)
    (row : List Bool→ℕ) (hr : BinaryFn row) : UnaryFn (rowSelected P D J base row) := by
  have HA:=spatialCount_unary P a D J c base hb
  have HB:=BinaryFn.ofUnary HA
  have HE : BinaryFn (rowSelected P D J base row):=
    BinaryFn.ite (hr.lt HB) hr ((hr.sub (HB.add (BinaryFn.const 1))).mod HB)
  exact (UnaryFn.fromBitsLE_min HE.bits_mem_FP HA).of_eq (fun q=>by
    rw [BinaryNatCode.encode,Nat.fromBitsLE_bits]
    exact min_eq_left (Nat.le_of_lt (rowSelected_lt P D J base row q)))

def sourceTask (P : Parameters) (base : List Bool→List Bool) (selected : List Bool→ℕ) (q : List Bool) :=
  IntegralCriticalFlatCoordinateQuery.writer P .originalCoefficient (pair (base q) (BinaryNatCode.encode (selected q)))

attribute [local irreducible] sourceTask

theorem sourceTask_FP (P : Parameters) (a : Access P) (base : List Bool→List Bool) (hb : base∈FP)
    (selected : List Bool→ℕ) (hs : BinaryFn selected) : sourceTask P base selected∈FP := by
  exact mem_FP_of_eq (mem_FP_comp (mem_FP_pair hb hs.bits_mem_FP)
    (IntegralCriticalFlatCoordinateQuery.writer_FP P a .originalCoefficient)) (fun _=>by unfold sourceTask; rfl)

theorem sourceTask_root (P : Parameters) (base : List Bool→List Bool) (selected : List Bool→ℕ) (q : List Bool) :
    RankedHistoryTask.root (sourceTask P base selected q)=RankedHistoryTask.root (base q) := by
  rw [sourceTask,IntegralCriticalFlatCoordinateQuery.writer_root,pairFst_pair]

theorem sourceTask_birth (P : Parameters) (base : List Bool→List Bool) (selected : List Bool→ℕ) (q : List Bool) :
    birth P (sourceTask P base selected q)=birth P (base q) := by
  rw [sourceTask,IntegralCriticalFlatCoordinateQuery.writer_birth,pairFst_pair]

theorem sourceTask_context (P : Parameters) (base : List Bool→List Bool) (selected : List Bool→ℕ) (q : List Bool) :
    get P .slot15 (sourceTask P base selected q)=get P .slot15 (base q) := by
  rw [sourceTask,IntegralCriticalFlatCoordinateQuery.writer_other P _ _ _ (by decide),pairFst_pair]

theorem sourceTask_modulus (P : Parameters) (base : List Bool→List Bool) (selected : List Bool→ℕ) (q : List Bool) :
    modulus P (sourceTask P base selected q)=modulus P (base q) := by
  rw [sourceTask,IntegralCriticalFlatCoordinateQuery.writer_modulus,pairFst_pair]

theorem sourceTask_saved (P : Parameters) (base : List Bool→List Bool) (selected : List Bool→ℕ) (q : List Bool) :
    IntegralMixedPhysicalTaskBits.saved P (sourceTask P base selected q)=IntegralMixedPhysicalTaskBits.saved P (base q) :=
  IntegralMixedPhysicalTaskBits.saved_invariance P _ _ (sourceTask_root P base selected q)
    (sourceTask_birth P base selected q) (sourceTask_context P base selected q)

theorem sourceTask_coordinate (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) :
    get P .slot8 (sourceTask P base selected q)=selected q := by
  unfold sourceTask
  apply IntegralCriticalFlatCoordinateQuery.writer_coordinate
  have HA : P.ambient (RankedHistoryTask.root (base q))+1≤numericCap P (RankedHistoryTask.root (base q)):=
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1
  have HI:=hs q
  rw [spatialCount_eq] at HI
  omega

theorem sourceTask_active (P : Parameters) (base : List Bool→List Bool) (selected : List Bool→ℕ) (q : List Bool) :
    IntegralMixedFramedPhysicalHeightBits.Active P (sourceTask P base selected q)↔
      IntegralMixedFramedPhysicalHeightBits.Active P (base q) := by
  simp only [IntegralMixedFramedPhysicalHeightBits.Active,IntegralMixedVirtualCaps.valid,
    sourceTask_birth,sourceTask_root,sourceTask_context]

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
