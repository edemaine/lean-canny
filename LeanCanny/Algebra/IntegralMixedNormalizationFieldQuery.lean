/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeEntries
/-! # Native coefficient queries with explicit small caller moduli -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationFieldBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

def reader (P : Parameters) (parent : List Bool → List Bool) (modulusValue coefficient : List Bool → ℕ) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = Field.modulus.code then BinaryNatCode.encode (modulusValue (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z) = Field.coefficient.code then BinaryNatCode.encode (coefficient (pairFst z)) else
    RankedHistoryFields.read (numericCap P) 16 (pair (parent (pairFst z)) (pairSnd z))

theorem reader_FP (P : Parameters) (a : Access P) (parent : List Bool → List Bool) (hp : parent ∈ FP)
    (modulusValue coefficient : List Bool → ℕ) (hm : BinaryFn modulusValue) (hk : BinaryFn coefficient) : reader P parent modulusValue coefficient ∈ FP := by
  have HM : BinaryFn (fun z => modulusValue (pairFst z)) := hm.comp pairFst_mem_FP
  have HK : BinaryFn (fun z => coefficient (pairFst z)) := hk.comp pairFst_mem_FP
  have HR := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hp) pairSnd_mem_FP)
    (RankedHistoryFields.read_FP (numericCap P) 16 (numericCap_binary P a))
  exact ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.modulus.code)).ite_mem_FP HM.bits_mem_FP
    (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.coefficient.code)).ite_mem_FP HK.bits_mem_FP HR)

def query (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (modulusValue coefficient : List Bool → ℕ) :=
  child P parent (birth P ∘ parent) p (reader P parent modulusValue coefficient)

theorem query_FP (P : Parameters) (a : Access P) (parent : List Bool → List Bool) (hp : parent ∈ FP)
    (p : Phase) (modulusValue coefficient : List Bool → ℕ) (hm : BinaryFn modulusValue) (hk : BinaryFn coefficient) :
    query P parent p modulusValue coefficient ∈ FP :=
  child_FP P a parent hp _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (birthCap_unary P a))).comp hp) p _
    (reader_FP P a parent hp modulusValue coefficient hm hk)

theorem reader_packet (P : Parameters) (parent : List Bool → List Bool) (modulusValue coefficient : List Bool → ℕ)
    (z : List Bool) (i : ℕ) : reader P parent modulusValue coefficient (pair z (BinaryNatCode.encode i)) =
      if i = Field.modulus.code then BinaryNatCode.encode (modulusValue z) else
      if i = Field.coefficient.code then BinaryNatCode.encode (coefficient z) else
        BinaryNatCode.encode (RankedHistoryFields.get (numericCap P) 16 (parent z) i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits _
  simp only [reader, pairFst_pair, pairSnd_pair, HI]
  rw [RankedHistoryFields.read_packet]

theorem query_root (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (m k : List Bool → ℕ) (z : List Bool) :
    RankedHistoryTask.root (query P parent p m k z) = RankedHistoryTask.root (parent z) := child_root P _ _ _ _ z

theorem query_birth (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (m k : List Bool → ℕ) (z : List Bool) :
    birth P (query P parent p m k z) = birth P (parent z) := by
  unfold query child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem query_phase (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (m k : List Bool → ℕ) (z : List Bool) :
    phase (query P parent p m k z) = p.code := IntegralCriticalFlatMatrixQuery.child_phase P parent _ p _ z

theorem query_get (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (m k : List Bool → ℕ) (z : List Bool) (f : Field) :
    get P f (query P parent p m k z) =
      if f = .modulus then min (m z) (numericCap P (RankedHistoryTask.root (parent z))) else
      if f = .coefficient then min (k z) (numericCap P (RankedHistoryTask.root (parent z))) else get P f (parent z) := by
  rw [query, child_get, reader_packet]
  cases f <;> norm_num only [Field.code, reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  all_goals exact min_eq_left (RankedHistoryFields.get_le (numericCap P) 16 (parent z) _)

theorem query_routine (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (m k : List Bool → ℕ) (z : List Bool) :
    IntegralMixedRoutineTaskBits.routine P (query P parent p m k z) = IntegralMixedRoutineTaskBits.routine P (parent z) := by
  unfold IntegralMixedRoutineTaskBits.routine
  rw [query_get]
  rfl

theorem query_saved (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (m k : List Bool → ℕ) (z : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P parent p m k z) = IntegralMixedVirtualTaskBits.saved P (parent z) := by
  apply IntegralMixedVirtualTaskBits.saved_invariance
  · exact query_root P parent p m k z
  · exact query_birth P parent p m k z
  · simp only [query_get, reduceCtorEq, ite_false]

theorem query_modulus (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (m k : List Bool → ℕ) (z : List Bool)
    (hm : m z ≤ numericCap P (RankedHistoryTask.root (parent z))) (hp : 0 < m z) :
    modulus P (query P parent p m k z) = m z := by
  unfold modulus
  rw [query_get]
  simp only [ite_true, min_eq_left hm, Nat.ne_of_gt hp, ite_false]

theorem query_coefficient (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (m k : List Bool → ℕ) (z : List Bool)
    (hk : k z ≤ numericCap P (RankedHistoryTask.root (parent z))) : get P .coefficient (query P parent p m k z) = k z := by
  rw [query_get]
  simp only [reduceCtorEq, ite_false, ite_true, min_eq_left hk]

theorem query_frame (P : Parameters) (parent : List Bool → List Bool) (p : Phase) (m k : List Bool → ℕ) (z : List Bool)
    (hp : p.code < phase (parent z)) : IntegralMixedRoutineTaskBits.Frame P (parent z) (query P parent p m k z) := by
  refine ⟨query_root P parent p m k z, ?_, ?_⟩
  · exact child_length P parent (birth P ∘ parent) p _ z (min_le_right _ _)
  · exact IntegralMixedRoutineTaskBits.lower_phase P _ _ (query_birth P parent p m k z)
      (query_routine P parent p m k z) (by rw [query_phase]; exact hp)

theorem coefficient_value (P : Parameters) (F : IntegralMixedCutSource.Family) (parent : List Bool → List Bool)
    (p : Phase) (m k : List Bool → ℕ) (z : List Bool)
    (hm : m z ≤ numericCap P (RankedHistoryTask.root (parent z))) (hp : 0 < m z)
    (hk : k z ≤ numericCap P (RankedHistoryTask.root (parent z))) :
    (IntegralMixedNormalizationTopBits.source P F).value (query P parent p m k z) =
      residueBits (((IntegralMixedNormalizationTopBits.top F (IntegralMixedVirtualTaskBits.saved P (parent z))).charpoly.coeff (k z) : ℤ) :
        ZMod (m z)) := by
  rw [IntegralMixedNormalizationTopBits.value_coefficient, query_saved,
    query_modulus P parent p m k z hm hp, query_coefficient P parent p m k z hk]

end LeanCanny.Algebra.IntegralMixedNormalizationFieldBits
