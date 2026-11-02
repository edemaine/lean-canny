/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightTransport
public import LeanCanny.Algebra.IntegralMixedFramedCompanionQueryReadback
/-! # Fresh native old-height queries from literal source packets

The packet pairs an arbitrary-modulus generator-source packet with a binary
retained index. Matrix indices wrap at the OLD prefix rank. An invalid retained
index becomes the count itself, so its exact zero extension survives clipping.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def source (q : List Bool) := pairFst q
def key (q : List Bool) := PaddedIntegralGeneratorSource.base (source q)
def root (q : List Bool) := pairFst (key q)
def sourceBirth (P : Parameters) (q : List Bool) := prefixLength P (key q)
def callerModulus (q : List Bool) := IntegralMixedFramedCompanionQueryBits.callerModulus (source q)
def sourceRank (P : Parameters) (q : List Bool) := FixedWidthPolynomial.count (sourceBirth P q) (P.width (root q))
def retainedIndex (P : Parameters) (q : List Bool) := min (Nat.fromBitsLE (pairSnd q)) (sourceBirth P q)
def rowIndex (P : Parameters) (q : List Bool) := Nat.fromBitsLE (PaddedIntegralGeneratorSource.row (source q))%sourceRank P q
def colIndex (P : Parameters) (q : List Bool) := Nat.fromBitsLE (PaddedIntegralGeneratorSource.col (source q))%sourceRank P q

theorem key_FP : key∈FP := mem_FP_comp pairFst_mem_FP PaddedIntegralGeneratorSource.base_FP
theorem root_FP : root∈FP := mem_FP_comp key_FP pairFst_mem_FP
theorem sourceBirth_unary (P : Parameters) (a : Access P) : UnaryFn (sourceBirth P) :=
  (IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp key_FP
theorem callerModulus_binary : BinaryFn callerModulus := IntegralMixedFramedCompanionQueryBits.callerModulus_binary.comp pairFst_mem_FP
theorem sourceRank_binary (P : Parameters) (a : Access P) : BinaryFn (sourceRank P) :=
  ((BinaryFn.const 2).powUnary (a.width.comp root_FP)).powUnary (sourceBirth_unary P a)
theorem retainedIndex_binary (P : Parameters) (a : Access P) : BinaryFn (retainedIndex P) :=
  BinaryFn.ofUnary (UnaryFn.fromBitsLE_min pairSnd_mem_FP (sourceBirth_unary P a))
theorem rowIndex_binary (P : Parameters) (a : Access P) : BinaryFn (rowIndex P) :=
  (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP PaddedIntegralGeneratorSource.row_FP)).mod (sourceRank_binary P a)
theorem colIndex_binary (P : Parameters) (a : Access P) : BinaryFn (colIndex P) :=
  (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP PaddedIntegralGeneratorSource.col_FP)).mod (sourceRank_binary P a)

def field (P : Parameters) (f : Field) (q : List Bool) := match f with
  | .modulus => callerModulus q | .row => rowIndex P q | .col => colIndex P q
  | .sourceIndex => retainedIndex P q | .slot15 => 2 | _ => 0

def reader (P : Parameters) (z : List Bool) :=
  if Nat.fromBitsLE (pairSnd z)=0 then BinaryNatCode.encode (callerModulus (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=1 then BinaryNatCode.encode (rowIndex P (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=2 then BinaryNatCode.encode (colIndex P (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=7 then BinaryNatCode.encode (retainedIndex P (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=15 then BinaryNatCode.encode 2 else []

theorem reader_FP (P : Parameters) (a : Access P) : reader P∈FP := by
  have HM := mem_FP_comp pairFst_mem_FP callerModulus_binary.bits_mem_FP
  have HR := mem_FP_comp pairFst_mem_FP (rowIndex_binary P a).bits_mem_FP
  have HC := mem_FP_comp pairFst_mem_FP (colIndex_binary P a).bits_mem_FP
  have HI := mem_FP_comp pairFst_mem_FP (retainedIndex_binary P a).bits_mem_FP
  exact
    ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)).ite_mem_FP
    HM
    (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 1)).ite_mem_FP
      HR
      (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 2)).ite_mem_FP
        HC
        (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 7)).ite_mem_FP
          HI
          (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 15)).ite_mem_FP
            (constFn_mem_FP (BinaryNatCode.encode 2)) (constFn_mem_FP [])))))

def parent (q : List Bool) := pair (root q) []
theorem parent_FP : parent∈FP := mem_FP_pair root_FP (constFn_mem_FP [])
def query (P : Parameters) := child P parent (sourceBirth P) .clearedHeight (reader P)
theorem query_FP (P : Parameters) (a : Access P) : query P∈FP :=
  child_FP P a parent parent_FP _ (BinaryFn.ofUnary (sourceBirth_unary P a)) _ _ (reader_FP P a)

theorem reader_packet (P : Parameters) (q : List Bool) (f : Field) :
    reader P (pair q (BinaryNatCode.encode f.code))=BinaryNatCode.encode (field P f q) := by
  simp only [reader,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  cases f <;> norm_num [Field.code,field]

theorem query_root (P : Parameters) (q : List Bool) : RankedHistoryTask.root (query P q)=root q := by
  rw [query,child_root]
  exact pairFst_pair _ _
theorem query_get (P : Parameters) (q : List Bool) (f : Field) :
    get P f (query P q)=min (field P f q) (numericCap P (root q)) := by
  rw [query,child_get,reader_packet]
  simp only [parent,RankedHistoryTask.root,pairFst_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem sourceBirth_bound (P : Parameters) (q : List Bool) : sourceBirth P q≤birthCap P (root q) := min_le_right _ _
theorem sourceRank_le (P : Parameters) (q : List Bool) : sourceRank P q≤numericCap P (root q) :=
  born_rank_le P _ (sourceBirth_bound P q)

theorem field_bound (P : Parameters) (q : List Bool) (hm : callerModulus q≤numericCap P (root q)) (f : Field) :
    field P f q≤numericCap P (root q) := by
  have HR : rowIndex P q<sourceRank P q := Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)
  have HC : colIndex P q<sourceRank P q := Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)
  have HI : retainedIndex P q≤numericCap P (root q) :=
    (min_le_right _ _).trans ((sourceBirth_bound P q).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).1)
  have H2 : 2≤numericCap P (root q) := (by decide : 2≤6).trans (IntegralMixedRoutineTaskBits.routine_cap P _)
  cases f <;> simp only [field]
  · exact hm
  · exact HR.le.trans (sourceRank_le P q)
  · exact HC.le.trans (sourceRank_le P q)
  all_goals omega

theorem query_field (P : Parameters) (q : List Bool) (hm : callerModulus q≤numericCap P (root q)) (f : Field) :
    get P f (query P q)=field P f q := by rw [query_get]; exact min_eq_left (field_bound P q hm f)

end LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryBits
