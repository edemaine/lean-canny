/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightSource
/-! # Native matrix packets for actual un-erased affine heights -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedOldHeightBits (state bankFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalAffineBits.value IntegralMixedFramedCurrentQNativeBits.machine

def parent (z : List Bool) := pairFst (pairFst z)
def query (P : Parameters) (z : List Bool) :=
  IntegralCriticalFlatMatrixQuery.writer P .factorPower (pair (parent z) (pairSnd z))

theorem query_FP (P : Parameters) (a : Access P) : query P∈FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (IntegralCriticalFlatMatrixQuery.writer_FP P a .factorPower)

theorem query_saved (P : Parameters) (z : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P z)=IntegralMixedVirtualTaskBits.saved P (parent z) :=
  by
    unfold query
    simpa only [pairFst_pair] using IntegralMixedVirtualTaskBits.matrix_saved P .factorPower (pair (parent z) (pairSnd z))

theorem query_affine (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :
    IntegralMixedFramedScalarCellsBits.affine P D J (query P z)=
      IntegralMixedFramedScalarCellsBits.affine P D J (parent z) := by
  unfold IntegralMixedFramedScalarCellsBits.affine
  rw [query_saved]
  have HE : get P .slot8 (query P z)=get P .slot8 (parent z) := by
    unfold query
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq,ite_false,pairFst_pair]
  rw [HE]

theorem query_active (P : Parameters) (z : List Bool) (h : Active P (parent z)) : Active P (query P z) := by
  refine ⟨?_,?_⟩
  · change birth P (query P z)<P.cap (RankedHistoryTask.root (query P z))
    have HV:=h.1
    change birth P (parent z)<P.cap (RankedHistoryTask.root (parent z)) at HV
    simpa only [query,IntegralCriticalFlatMatrixQuery.writer_birth,IntegralCriticalFlatMatrixQuery.writer_root,pairFst_pair] using HV
  · unfold query
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simpa only [reduceCtorEq,ite_false,pairFst_pair] using h.2

noncomputable def entry (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (z : List Bool) :=
  if Active P (parent z) then IntegralMixedFramedPhysicalAffineBits.value P a D J c (query P z) else []

theorem entry_space (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c) : SpaceFunction (entry P a D J c) := by
  have HG := (active_FP P a).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have E := (IntegralMixedFramedPhysicalAffineBits.value_space P a D J c hb).precompose (query P) (query_FP P a)
  exact (SpaceFunction.branch _ HG.flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (funext fun z=>by simp only [entry,Function.comp_apply,decide_eq_true_eq];rfl)

theorem query_indices (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q mw : List Bool) (r t : Fin (count ((family P D J).arity q) ((family P D J).width q)))
    (_hq : Active P q) :
    get P .row (query P (pair (pair q mw) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))=r.val ∧
    get P .col (query P (pair (pair q mw) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))=t.val := by
  have HC : count ((family P D J).arity q) ((family P D J).width q)≤numericCap P (RankedHistoryTask.root q) := by
    rw [arity_eq,width_eq]
    exact born_rank_le P _ (min_le_right _ _)
  constructor
  all_goals
    unfold query parent
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,reduceCtorEq,ite_true,ite_false]
  · exact min_eq_left (r.isLt.le.trans HC)
  · exact min_eq_left (t.isLt.le.trans HC)

end LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightBits
