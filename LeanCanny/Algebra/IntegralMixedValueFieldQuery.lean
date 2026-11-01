/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedRoutineTask

/-! # Fresh numeric field queries for the value Gram computation

One native numeric selector is changed together with the routine and phase.
Repeated updates retain a single ROOT record and the same physical prefix.
The modulus and source context are copied unless explicitly selected. The
unclipped field theorem requires its actual numeric cap, rather than silently
identifying an oversized selector with its bounded encoding.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueFieldQuery
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedRoutineTaskBits (Routine)

def reader (P : Parameters) (parent : List Bool → List Bool) (r : Routine)
    (f : Field) (value : List Bool → ℕ) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = Field.slot14.code then BinaryNatCode.encode r.code else
  if Nat.fromBitsLE (pairSnd z) = f.code then BinaryNatCode.encode (value (pairFst z)) else
    RankedHistoryFields.read (numericCap P) 16 (pair (parent (pairFst z)) (pairSnd z))

theorem reader_FP (P : Parameters) (a : Access P) (parent : List Bool → List Bool)
    (hp : parent ∈ FP) (r : Routine) (f : Field) (value : List Bool → ℕ)
    (hv : BinaryFn value) : reader P parent r f value ∈ FP := by
  have HV : BinaryFn (fun z => value (pairFst z)) := hv.comp pairFst_mem_FP
  have HC := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hp) pairSnd_mem_FP)
    (RankedHistoryFields.read_FP (numericCap P) 16 (numericCap_binary P a))
  exact ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.slot14.code)).ite_mem_FP
    (constFn_mem_FP (BinaryNatCode.encode r.code))
    (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const f.code)).ite_mem_FP HV.bits_mem_FP HC)

def query (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (value : List Bool → ℕ) : List Bool → List Bool :=
  child P parent (birth P ∘ parent) p (reader P parent r f value)

theorem query_FP (P : Parameters) (a : Access P) (parent : List Bool → List Bool)
    (hp : parent ∈ FP) (r : Routine) (p : Phase) (f : Field) (value : List Bool → ℕ)
    (hv : BinaryFn value) : query P parent r p f value ∈ FP :=
  child_FP P a parent hp _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (birthCap_unary P a))).comp hp)
    p _ (reader_FP P a parent hp r f value hv)

theorem reader_packet (P : Parameters) (parent : List Bool → List Bool) (r : Routine)
    (f : Field) (value : List Bool → ℕ) (z : List Bool) (i : ℕ) :
    reader P parent r f value (pair z (BinaryNatCode.encode i)) =
      if i = Field.slot14.code then BinaryNatCode.encode r.code else
      if i = f.code then BinaryNatCode.encode (value z) else
        BinaryNatCode.encode (RankedHistoryFields.get (numericCap P) 16 (parent z) i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits _
  simp only [reader, pairFst_pair, pairSnd_pair, HI]
  rw [RankedHistoryFields.read_packet]

theorem query_root (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool) :
    RankedHistoryTask.root (query P parent r p f v z) = RankedHistoryTask.root (parent z) :=
  child_root P _ _ _ _ z

theorem query_birth (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool) :
    birth P (query P parent r p f v z) = birth P (parent z) := by
  unfold query child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem query_phase (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool) :
    phase (query P parent r p f v z) = p.code :=
  IntegralCriticalFlatMatrixQuery.child_phase P parent _ p _ z

theorem query_get (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool) (g : Field) :
    get P g (query P parent r p f v z) =
      if g = .slot14 then r.code else
      if g = f then min (v z) (numericCap P (RankedHistoryTask.root (parent z))) else
        get P g (parent z) := by
  rw [query, child_get, reader_packet]
  have H14 : (g.code = Field.slot14.code) ↔ g = .slot14 := by cases g <;> decide
  have HE : (g.code = f.code) ↔ g = f := by cases f <;> cases g <;> decide
  simp only [BinaryNatCode.encode, H14, HE]
  by_cases HR : g = .slot14
  · rw [ite_eq_left HR, ite_eq_left HR, Nat.fromBitsLE_bits]
    exact min_eq_left ((Nat.le_of_lt_succ r.code_lt).trans
      (IntegralMixedRoutineTaskBits.routine_cap P _))
  · rw [ite_eq_right HR, ite_eq_right HR]
    by_cases HF : g = f
    · rw [ite_eq_left HF, ite_eq_left HF, Nat.fromBitsLE_bits]
    · rw [ite_eq_right HF, ite_eq_right HF, Nat.fromBitsLE_bits]
      exact min_eq_left (RankedHistoryFields.get_le (numericCap P) 16 (parent z) _)

theorem query_field (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool) (hf : f ≠ .slot14)
    (hv : v z ≤ numericCap P (RankedHistoryTask.root (parent z))) :
    get P f (query P parent r p f v z) = v z := by
  rw [query_get, ite_eq_right hf, ite_eq_left rfl, min_eq_left hv]

theorem query_other (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool) (g : Field)
    (hr : g ≠ .slot14) (hf : g ≠ f) :
    get P g (query P parent r p f v z) = get P g (parent z) := by
  rw [query_get, ite_eq_right hr, ite_eq_right hf]

theorem query_routine (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool) :
    IntegralMixedRoutineTaskBits.routine P (query P parent r p f v z) = r.code := by
  rw [IntegralMixedRoutineTaskBits.routine, query_get, ite_eq_left rfl]
  exact min_eq_left (Nat.le_of_lt_succ r.code_lt)

theorem query_modulus (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool) (hf : .modulus ≠ f) :
    modulus P (query P parent r p f v z) = modulus P (parent z) := by
  unfold modulus
  rw [query_other P parent r p f v z .modulus (by decide) hf]

theorem query_saved (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool) (hf : .slot15 ≠ f) :
    IntegralMixedVirtualTaskBits.saved P (query P parent r p f v z) =
      IntegralMixedVirtualTaskBits.saved P (parent z) := by
  apply IntegralMixedVirtualTaskBits.saved_invariance
  · exact query_root P parent r p f v z
  · exact query_birth P parent r p f v z
  · exact query_other P parent r p f v z .slot15 (by decide) hf

theorem query_length (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool) :
    (query P parent r p f v z).length ≤ wordBudget P (parent z) :=
  child_length P parent (birth P ∘ parent) p _ z (min_le_right _ _)

theorem query_frame_phase (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P (parent z) = r.code)
    (hp : p.code < phase (parent z)) :
    IntegralMixedRoutineTaskBits.Frame P (parent z) (query P parent r p f v z) := by
  refine ⟨query_root P parent r p f v z, query_length P parent r p f v z, ?_⟩
  exact IntegralMixedRoutineTaskBits.lower_phase P _ _ (query_birth P parent r p f v z)
    ((query_routine P parent r p f v z).trans hr.symm)
    (by rw [query_phase]; exact hp)

theorem query_frame_routine (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (f : Field) (v : List Bool → ℕ) (z : List Bool)
    (hr : r.code < IntegralMixedRoutineTaskBits.routine P (parent z)) :
    IntegralMixedRoutineTaskBits.Frame P (parent z) (query P parent r p f v z) := by
  refine ⟨query_root P parent r p f v z, query_length P parent r p f v z, ?_⟩
  exact IntegralMixedRoutineTaskBits.lower_routine P _ _ (query_birth P parent r p f v z)
    (by rw [query_routine]; exact hr)

end LeanCanny.Algebra.IntegralMixedValueFieldQuery
