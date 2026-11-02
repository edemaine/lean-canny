/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutSourcePlanning
public import LeanCanny.Algebra.IntegralMixedFramedModulusPacket
/-! # Fresh full-factor query packets with an honest caller-modulus budget

The base is the original native parent task. Its complete root, birth and
selected context remain unchanged; only the caller modulus is appended to
the copied original root. Original scalar degree and basis widths are fixed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCutProbeTaskBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedNormalizationBits

def parameters (P : Parameters) (L F C : List Bool→ℕ) : Parameters :=
  planned (IntegralMixedFramedRootPullback.parameters P pairFst IntegralMixedFramedModulusPacket.extra)
    (L ∘ pairFst) (F ∘ pairFst) (C ∘ pairFst)
theorem access (P : Parameters) (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : Access (parameters P L F C) :=
  planned_access _ (IntegralMixedFramedRootPullback.access P a pairFst pairFst_mem_FP _
    IntegralMixedFramedModulusPacket.extra_binary) (hL.comp pairFst_mem_FP) (hF.comp pairFst_mem_FP) (hC.comp pairFst_mem_FP)

def original (q : List Bool) := PaddedIntegralGeneratorSource.base q
def root (q : List Bool) := pair (RankedHistoryTask.root (original q)) (PaddedIntegralGeneratorSource.modulus q)
def parent (q : List Bool) := pair (root q) []
def callerModulus (q : List Bool) := Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus q)+1
def row (q : List Bool) := Nat.fromBitsLE (PaddedIntegralGeneratorSource.row q)
def col (q : List Bool) := Nat.fromBitsLE (PaddedIntegralGeneratorSource.col q)
def coefficient (P : Parameters) (q : List Bool) := get P .coefficient (original q)
def context (P : Parameters) (q : List Bool) := get P .slot15 (original q)

theorem original_FP : original∈FP := PaddedIntegralGeneratorSource.base_FP
theorem root_FP : root∈FP := mem_FP_pair
  (mem_FP_comp original_FP RankedHistoryTask.root_FP) PaddedIntegralGeneratorSource.modulus_FP
theorem parent_FP : parent∈FP := mem_FP_pair root_FP (constFn_mem_FP [])
theorem callerModulus_binary : BinaryFn callerModulus :=
  (BinaryFn.fromBits PaddedIntegralGeneratorSource.modulus_FP).add (BinaryFn.const 1)
theorem row_binary : BinaryFn row := BinaryFn.fromBits PaddedIntegralGeneratorSource.row_FP
theorem col_binary : BinaryFn col := BinaryFn.fromBits PaddedIntegralGeneratorSource.col_FP
theorem coefficient_binary (P : Parameters) (a : Access P) : BinaryFn (coefficient P) :=
  (get_binary P a .coefficient).comp original_FP
theorem context_binary (P : Parameters) (a : Access P) : BinaryFn (context P) :=
  (get_binary P a .slot15).comp original_FP

def field (P : Parameters) (f : Field) (q : List Bool) : ℕ := match f with
  | .modulus => callerModulus q
  | .row => row q
  | .col => col q
  | .coefficient => coefficient P q
  | .slot14 => 4
  | .slot15 => context P q
  | _ => 0
def reader (P : Parameters) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z)=0 then BinaryNatCode.encode (callerModulus (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=1 then BinaryNatCode.encode (row (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=2 then BinaryNatCode.encode (col (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=3 then BinaryNatCode.encode (coefficient P (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z)=14 then BinaryNatCode.encode 4 else
  if Nat.fromBitsLE (pairSnd z)=15 then BinaryNatCode.encode (context P (pairFst z)) else []

section ReaderProof
attribute [local irreducible] callerModulus row col coefficient context

theorem reader_FP (P : Parameters) (a : Access P) : reader P∈FP := by
  have H0:=mem_FP_comp pairFst_mem_FP callerModulus_binary.bits_mem_FP
  have H1:=mem_FP_comp pairFst_mem_FP row_binary.bits_mem_FP
  have H2:=mem_FP_comp pairFst_mem_FP col_binary.bits_mem_FP
  have H4:=mem_FP_comp pairFst_mem_FP (coefficient_binary P a).bits_mem_FP
  have H15:=mem_FP_comp pairFst_mem_FP (context_binary P a).bits_mem_FP
  exact ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)).ite_mem_FP H0
    (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 1)).ite_mem_FP H1
      (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 2)).ite_mem_FP H2
        (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 3)).ite_mem_FP H4
          (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 14)).ite_mem_FP (constFn_mem_FP (BinaryNatCode.encode 4))
            (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 15)).ite_mem_FP H15 (constFn_mem_FP []))))))

end ReaderProof

def query (P : Parameters) (L F C : List Bool→ℕ) :=
  child (parameters P L F C) parent (birth P ∘ original) .companion (reader P)
theorem query_FP (P : Parameters) (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : query P L F C∈FP :=
  child_FP _ (access P a L F C hL hF hC) parent parent_FP _
    ((BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)).comp original_FP) _ _ (reader_FP P a)

theorem reader_packet (P : Parameters) (q : List Bool) (f : Field) :
    reader P (pair q (BinaryNatCode.encode f.code))=BinaryNatCode.encode (field P f q) := by
  simp only [reader,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  cases f <;> norm_num [Field.code,field]
theorem query_root (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    RankedHistoryTask.root (query P L F C q)=root q := by
  rw [query,child_root]
  exact pairFst_pair _ _
theorem query_get (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) (f : Field) :
    get (parameters P L F C) f (query P L F C q)=min (field P f q) (numericCap (parameters P L F C) (root q)) := by
  rw [query,child_get,reader_packet]
  simp only [parent,RankedHistoryTask.root,pairFst_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem modulus_bound (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    callerModulus q≤numericCap (parameters P L F C) (root q) := by
  apply (show callerModulus q≤(parameters P L F C).modulusBound (root q) from ?_).trans
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.2.2
  apply (show callerModulus q≤
      (IntegralMixedFramedRootPullback.parameters P pairFst IntegralMixedFramedModulusPacket.extra).modulusBound (root q) from ?_).trans
    (planned_preserves_modulus _ _ _ _ _)
  exact (show callerModulus q=IntegralMixedFramedModulusPacket.extra (root q) from by
    simp only [callerModulus,root,IntegralMixedFramedModulusPacket.extra,pairSnd_pair]).le.trans (le_max_right _ _)

theorem query_modulus (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    modulus (parameters P L F C) (query P L F C q)=callerModulus q := by
  have HM : get (parameters P L F C) .modulus (query P L F C q)=callerModulus q := by
    rw [query_get]
    exact min_eq_left (modulus_bound P L F C q)
  unfold modulus
  rw [HM,ite_eq_right (by unfold callerModulus; omega)]

theorem query_birth (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    birth (parameters P L F C) (query P L F C q)=birth P (original q) := by
  unfold query child
  rw [RankedHistoryFields.flatten_eq_pack]
  apply RankedHistoryTask.birth_pack
  simpa only [Function.comp_apply,birthCap,parameters,planned,
    IntegralMixedFramedRootPullback.parameters,parent,RankedHistoryTask.root,pairFst_pair,root] using
    (show birth P (original q)≤birthCap P (RankedHistoryTask.root (original q)) from min_le_right _ _)

theorem query_phase (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    phase (query P L F C q)=26 := by
  unfold query child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ (by decide)

theorem query_routine (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    IntegralMixedRoutineTaskBits.routine (parameters P L F C) (query P L F C q)=4 := by
  rw [IntegralMixedRoutineTaskBits.routine,query_get]
  change min (min 4 (numericCap (parameters P L F C) (root q))) 6=4
  rw [min_eq_left ((by decide : 4≤6).trans (IntegralMixedRoutineTaskBits.routine_cap _ _))]
  rfl

theorem query_context (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (original q)) :
    get (parameters P L F C) .slot15 (query P L F C q)=context P q := by
  rw [query_get]
  exact min_eq_left (hc.2.trans ((by decide : 4≤6).trans (IntegralMixedRoutineTaskBits.routine_cap _ _)))

theorem query_field (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) (f : Field)
    (hf : field P f q≤numericCap (parameters P L F C) (root q)) :
    get (parameters P L F C) f (query P L F C q)=field P f q := by
  rw [query_get,min_eq_left hf]

theorem query_valid (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    IntegralMixedVirtualCaps.valid (parameters P L F C) (query P L F C q) ↔
      IntegralMixedVirtualCaps.valid P (original q) := by
  unfold IntegralMixedVirtualCaps.valid
  rw [query_birth,query_root]
  simp only [parameters,planned,IntegralMixedFramedRootPullback.parameters,
    Function.comp_apply,root,pairFst_pair]

theorem query_virtual_context (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (original q)) :
    IntegralMixedVirtualContextBits.context (parameters P L F C) (query P L F C q) := by
  unfold IntegralMixedVirtualContextBits.context
  rw [query_context P L F C q hc]
  exact hc

theorem query_saved (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (original q)) :
    IntegralMixedFramedRootPullback.key pairFst
      (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))=
      IntegralMixedVirtualTaskBits.saved P (original q) := by
  simp only [IntegralMixedFramedRootPullback.key,IntegralMixedVirtualTaskBits.saved,
    pairFst_pair,pairSnd_pair,query_root,query_birth,query_context P L F C q hc,root,context]

theorem query_width (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    (parameters P L F C).width (root q)=P.width (RankedHistoryTask.root (original q)) := by
  simp only [parameters,planned,IntegralMixedFramedRootPullback.parameters,Function.comp_apply,root,pairFst_pair]

theorem scalar_bound (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    2^P.width (RankedHistoryTask.root (original q))≤numericCap (parameters P L F C) (root q) := by
  have HS : 2^(parameters P L F C).width (root q)≤numericCap (parameters P L F C) (root q) :=
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.1
  rw [query_width] at HS
  exact HS

theorem old_rank_bound (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    FixedWidthPolynomial.count (birth P (original q)) (P.width (RankedHistoryTask.root (original q)))≤
      numericCap (parameters P L F C) (root q) := by
  have HB : birth P (original q)≤birthCap (parameters P L F C) (root q) := by
    simpa only [birthCap,parameters,planned,IntegralMixedFramedRootPullback.parameters,Function.comp_apply,root,pairFst_pair] using
      (show birth P (original q)≤birthCap P (RankedHistoryTask.root (original q)) from min_le_right _ _)
  have HR := born_rank_le (parameters P L F C) (root q) HB
  rw [query_width] at HR
  exact HR

theorem query_coefficient (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hk : coefficient P q<2^P.width (RankedHistoryTask.root (original q))) :
    get (parameters P L F C) .coefficient (query P L F C q)=coefficient P q :=
  query_field P L F C q .coefficient (hk.le.trans (scalar_bound P L F C q))

theorem query_row (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hr : row q<FixedWidthPolynomial.count (birth P (original q)) (P.width (RankedHistoryTask.root (original q)))) :
    get (parameters P L F C) .row (query P L F C q)=row q :=
  query_field P L F C q .row (hr.le.trans (old_rank_bound P L F C q))

theorem query_col (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hr : col q<FixedWidthPolynomial.count (birth P (original q)) (P.width (RankedHistoryTask.root (original q)))) :
    get (parameters P L F C) .col (query P L F C q)=col q :=
  query_field P L F C q .col (hr.le.trans (old_rank_bound P L F C q))

end LeanCanny.Algebra.IntegralMixedFramedCutProbeTaskBits
