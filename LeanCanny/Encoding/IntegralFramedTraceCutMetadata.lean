/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutTask
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackInstruction
public import LeanCanny.Encoding.WordListRecords
/-! # Original records determine the whole-trace terminal prefix and cut range

One final default-X birth makes the sampler positive, even for an empty
trace. Literal header words give a native unary script length. A creating
cut is necessarily inside the original chronological instruction list;
padded/default and non-cut commands are excluded automatically.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutMetadata
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family keyAt)
open IntegralMixedFramedHistoryScript (chronological)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def length (P : Parameters) (D : Plan P) (root : List Bool) := (D.rules root).length
noncomputable def terminal (P : Parameters) (D : Plan P) (root : List Bool) := keyAt root (length P D root+1) []
noncomputable def key (P : Parameters) (D : Plan P) := terminal P D∘RankedHistoryTask.root

theorem length_unary (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) : UnaryFn (length P D) := by
  apply ((WordListRecords.count_unary).comp h0.native.commands).of_eq
  intro root
  rw [h0.represents.commands]
  simp only [IntegralMixedFramedHeaderBits.words,WordListRecords.count_encode,List.length_map,List.length_reverse,length]

theorem terminal_FP (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) : terminal P D∈FP := by
  have HL : BinaryFn (length P D):=BinaryFn.ofUnary (length_unary P D H h0)
  have HN : BinaryFn (fun root=>length P D root+1):=HL.add (BinaryFn.const 1)
  exact mem_FP_pair id_mem_FP (mem_FP_pair HN.bits_mem_FP (constFn_mem_FP []))

theorem key_FP (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h0 : IntegralMixedFramedNormalizationBits.Controls P D H) : key P D∈FP :=
  mem_FP_comp RankedHistoryTask.root_FP (terminal_FP P D H h0)

theorem terminal_root (P : Parameters) (D : Plan P) (root : List Bool) : pairFst (terminal P D root)=root :=
  IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _

theorem terminal_birth (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (root : List Bool) :
    (family P D H).birth (terminal P D root)=length P D root+1 := by
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
  apply IntegralMixedFramedHistoryFamilyBits.keyAt_prefix
  have HR:=D.room root
  change (D.rules root).length+1≤P.cap root+1
  omega

theorem terminal_positive (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (root : List Bool) :
    0<(family P D H).birth (terminal P D root) := by rw [terminal_birth]; omega

theorem key_positive (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    0<(family P D H).birth (key P D c) := terminal_positive P D H _

theorem key_task (P : Parameters) (D : Plan P) (z : List Bool) :
    key P D (IntegralFramedTraceCutTask.task P z)=terminal P D (pairFst z) :=
  congrArg (terminal P D) (IntegralFramedTraceCutTask.task_root P z)

theorem cut_lt_length (P : Parameters) (D : Plan P) (root : List Bool) (j : ℕ)
    (hcut : IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D root j).command) :
    j<length P D root := by
  by_contra hj
  have HH : chronological (D.rules root) j=none := by
    apply List.getElem?_eq_none
    simp only [List.length_reverse]
    exact Nat.le_of_not_gt hj
  unfold IntegralMixedFramedRootPullback.instructionAt at hcut
  rw [HH] at hcut
  exact hcut.elim

theorem cut_lt_cap (P : Parameters) (D : Plan P) (root : List Bool) (j : ℕ)
    (hcut : IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D root j).command) :
    j<P.cap root := by
  have HJ:=cut_lt_length P D root j hcut
  have HR:=D.room root
  unfold length at HJ
  omega

end LeanCanny.Encoding.IntegralFramedTraceCutMetadata
