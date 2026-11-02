/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionKeyTransport
public import LeanCanny.Algebra.IntegralMixedFramedNativeCurrent
/-! # Fresh native creating-companion queries from actual source packets

The original root, actual birth, caller modulus and wrapped basis indices
are read from the source packet. Original command headers supply the actual
producer context and coordinate. Representable numeric fields are preserved
exactly; this module never identifies an arbitrary modulus with its clip.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction prefixLength)
open scoped Classical

def root (q : List Bool) := pairFst (PaddedIntegralGeneratorSource.base q)
def sourceBirth (P : Parameters) (q : List Bool) := prefixLength P (PaddedIntegralGeneratorSource.base q)
def callerModulus (q : List Bool) := Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q)+1
def sourceRank (P : Parameters) (q : List Bool) :=
  FixedWidthPolynomial.count (sourceBirth P q+1) (P.width (root q))
def rowIndex (P : Parameters) (q : List Bool) := Nat.fromBitsLE (PaddedIntegralGeneratorSource.row q)%sourceRank P q
def colIndex (P : Parameters) (q : List Bool) := Nat.fromBitsLE (PaddedIntegralGeneratorSource.col q)%sourceRank P q

noncomputable def coordinate (P : Parameters) (D : Plan P) (q : List Bool) :=
  (instruction P D (PaddedIntegralGeneratorSource.base q)).command.coordinate
noncomputable def context (P : Parameters) (D : Plan P) (q : List Bool) :=
  (instruction P D (PaddedIntegralGeneratorSource.base q)).command.context

theorem root_FP : root∈FP := mem_FP_comp PaddedIntegralGeneratorSource.base_FP pairFst_mem_FP
theorem sourceBirth_unary (P : Parameters) (a : Access P) : UnaryFn (sourceBirth P) :=
  (IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp PaddedIntegralGeneratorSource.base_FP
theorem callerModulus_binary : BinaryFn callerModulus :=
  (BinaryFn.fromBits PaddedIntegralGeneratorSource.modulus_FP).add (BinaryFn.const 1)
theorem sourceRank_binary (P : Parameters) (a : Access P) : BinaryFn (sourceRank P) :=
  ((BinaryFn.const 2).powUnary (a.width.comp root_FP)).powUnary ((sourceBirth_unary P a).add (UnaryFn.const 1))
theorem rowIndex_binary (P : Parameters) (a : Access P) : BinaryFn (rowIndex P) :=
  (BinaryFn.fromBits PaddedIntegralGeneratorSource.row_FP).mod (sourceRank_binary P a)
theorem colIndex_binary (P : Parameters) (a : Access P) : BinaryFn (colIndex P) :=
  (BinaryFn.fromBits PaddedIntegralGeneratorSource.col_FP).mod (sourceRank_binary P a)

theorem coordinate_binary (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) :
    BinaryFn (coordinate P D) := by
  have HC : BinaryFn (fun key => (instruction P D key).command.coordinate) :=
    (IntegralMixedHeaderTablesBits.producer_readers P a T ht).coordinate.of_eq
      (fun key => (congrArg IntegralMixedCommandHeaderBits.Header.coordinate
        (IntegralMixedFramedHeaderBits.producer_eq P D H T hr key)).trans
          (IntegralMixedCommandHeaderBits.command_coordinate _))
  exact HC.comp PaddedIntegralGeneratorSource.base_FP

theorem context_binary (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) :
    BinaryFn (context P D) := by
  have HC : BinaryFn (fun key => (instruction P D key).command.context) :=
    (IntegralMixedHeaderTablesBits.producer_readers P a T ht).context.of_eq
      (fun key => (congrArg IntegralMixedCommandHeaderBits.Header.context
        (IntegralMixedFramedHeaderBits.producer_eq P D H T hr key)).trans
          (IntegralMixedCommandHeaderBits.command_context _))
  exact HC.comp PaddedIntegralGeneratorSource.base_FP

noncomputable def field (P : Parameters) (D : Plan P) (f : Field) (q : List Bool) : ℕ :=
  match f with
  | .modulus => callerModulus q
  | .row => rowIndex P q
  | .col => colIndex P q
  | .slot13 => coordinate P D q
  | .slot14 => 6
  | .slot15 => context P D q
  | _ => 0

noncomputable def reader (P : Parameters) (D : Plan P) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z)=0 then BinaryNatCode.encode (callerModulus (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=1 then BinaryNatCode.encode (rowIndex P (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=2 then BinaryNatCode.encode (colIndex P (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=13 then BinaryNatCode.encode (coordinate P D (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=14 then BinaryNatCode.encode 6 else
  if Nat.fromBitsLE (pairSnd z)=15 then BinaryNatCode.encode (context P D (pairFst z)) else []

theorem reader_FP (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) :
    reader P D∈FP := by
  have HM := mem_FP_comp pairFst_mem_FP callerModulus_binary.bits_mem_FP
  have HR := mem_FP_comp pairFst_mem_FP (rowIndex_binary P a).bits_mem_FP
  have HC := mem_FP_comp pairFst_mem_FP (colIndex_binary P a).bits_mem_FP
  have HK := mem_FP_comp pairFst_mem_FP (coordinate_binary P a D H T ht hr).bits_mem_FP
  have HX := mem_FP_comp pairFst_mem_FP (context_binary P a D H T ht hr).bits_mem_FP
  exact ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)).ite_mem_FP HM
    (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 1)).ite_mem_FP HR
      (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 2)).ite_mem_FP HC
        (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 13)).ite_mem_FP HK
          (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 14)).ite_mem_FP (constFn_mem_FP (BinaryNatCode.encode 6))
            (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 15)).ite_mem_FP HX (constFn_mem_FP []))))))

def parent (q : List Bool) := pair (root q) []
theorem parent_FP : parent∈FP := mem_FP_pair root_FP (constFn_mem_FP [])

noncomputable def query (P : Parameters) (D : Plan P) :=
  RankedHistoryFields.flatten (numericCap P) 16 parent (sourceBirth P) (fun _ => 26) (reader P D)

theorem query_FP (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) : query P D∈FP :=
  RankedHistoryFields.flatten_FP _ _ (numericCap_binary P a) parent parent_FP (sourceBirth P) (fun _ => 26)
    (BinaryFn.ofUnary (sourceBirth_unary P a)) (BinaryFn.const 26) _ (reader_FP P a D H T ht hr)

theorem reader_packet (P : Parameters) (D : Plan P) (q : List Bool) (f : Field) :
    reader P D (pair q (BinaryNatCode.encode f.code))=BinaryNatCode.encode (field P D f q) := by
  simp only [reader,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  cases f <;> norm_num [Field.code,field]

theorem query_root (P : Parameters) (D : Plan P) (q : List Bool) : RankedHistoryTask.root (query P D q)=root q := by
  rw [query,RankedHistoryFields.root_flatten]
  exact pairFst_pair _ _

theorem query_birth (P : Parameters) (D : Plan P) (q : List Bool) : birth P (query P D q)=sourceBirth P q := by
  unfold query
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (by
    simp only [sourceBirth,prefixLength,birthCap,parent,RankedHistoryTask.root,pairFst_pair]
    exact min_le_right _ _)

theorem query_phase (P : Parameters) (D : Plan P) (q : List Bool) : phase (query P D q)=26 := by
  unfold query
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ (by decide)

theorem query_get (P : Parameters) (D : Plan P) (q : List Bool) (f : Field) :
    get P f (query P D q)=min (field P D f q) (numericCap P (root q)) := by
  rw [IntegralCriticalHistoryTask.get,query,RankedHistoryFields.get_flatten _ _ _ _ _ _ _ _ f.code_lt,reader_packet]
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,parent,RankedHistoryTask.root,pairFst_pair]

theorem context_bound (P : Parameters) (D : Plan P) (q : List Bool) : context P D q≤numericCap P (root q) :=
  (IntegralMixedFullHistoryScript.Command.context_le _).trans
    ((by decide : 4≤6).trans (IntegralMixedRoutineTaskBits.routine_cap P _))

theorem coordinate_bound (P : Parameters) (D : Plan P) (q : List Bool) : coordinate P D q≤numericCap P (root q) :=
  ((IntegralMixedFullHistoryScript.Command.coordinate_le _).trans (Nat.le_succ _)).trans
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1

theorem query_context (P : Parameters) (D : Plan P) (q : List Bool) : get P .slot15 (query P D q)=context P D q := by
  rw [query_get]
  exact min_eq_left (context_bound P D q)

theorem query_coordinate (P : Parameters) (D : Plan P) (q : List Bool) : get P .slot13 (query P D q)=coordinate P D q := by
  rw [query_get]
  exact min_eq_left (coordinate_bound P D q)

theorem query_routine (P : Parameters) (D : Plan P) (q : List Bool) : IntegralMixedRoutineTaskBits.routine P (query P D q)=6 := by
  rw [IntegralMixedRoutineTaskBits.routine,query_get]
  change min (min 6 (numericCap P (root q))) 6=6
  rw [min_eq_left (IntegralMixedRoutineTaskBits.routine_cap P _)]
  rfl

theorem query_modulus (P : Parameters) (D : Plan P) (q : List Bool)
    (hm : callerModulus q≤numericCap P (root q)) : modulus P (query P D q)=callerModulus q := by
  unfold modulus
  rw [query_get]
  change (if min (callerModulus q) (numericCap P (root q))=0 then 1 else min (callerModulus q) (numericCap P (root q)))=callerModulus q
  rw [min_eq_left hm,ite_eq_right (by unfold callerModulus; omega)]

end LeanCanny.Algebra.IntegralMixedFramedCompanionQueryBits
