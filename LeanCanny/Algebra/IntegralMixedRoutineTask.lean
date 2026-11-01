/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualTaskBackend
/-! # A routine rank above the unchanged critical arithmetic phases

Scalar and old-height routines may ask arbitrary routines at an earlier
physical prefix. At the same prefix, the routine tag decreases before the
existing phase digit. Fresh queries copy all source-selection fields.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRoutineTaskBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

inductive Routine where
  | scalar | critical | pscEntry | pscDeterminant | rawFactor | normalization | companion
  deriving DecidableEq, Repr

def Routine.code : Routine → ℕ
  | .scalar => 0 | .critical => 1 | .pscEntry => 2 | .pscDeterminant => 3
  | .rawFactor => 4 | .normalization => 5 | .companion => 6

theorem Routine.code_lt (r : Routine) : r.code < 7 := by cases r <;> decide

def routine (P : Parameters) (q : List Bool) : ℕ := min (get P .slot14 q) 6

def rank (P : Parameters) (q : List Bool) : ℕ := 27 * (7 * birth P q + routine P q) + phase q

theorem routine_lt (P : Parameters) (q : List Bool) : routine P q < 7 := by
  have H := min_le_right (get P .slot14 q) 6
  unfold routine
  omega

theorem phase_lt (q : List Bool) : phase q < 27 := by
  have H := min_le_right (Nat.fromBitsLE (RankedHistoryTask.phaseWord q)) 26
  exact Nat.lt_of_le_of_lt H (by decide)

theorem routine_unary (P : Parameters) (a : Access P) : UnaryFn (routine P) := by
  have H := UnaryFn.fromBitsLE_min (get_binary P a .slot14).bits_mem_FP (UnaryFn.const 6)
  exact H.of_eq (fun q => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)

theorem rank_unary (P : Parameters) (a : Access P) : UnaryFn (rank P) :=
  ((UnaryFn.const 27).mul (((UnaryFn.const 7).mul
    (RankedHistoryTask.birth_unary _ (birthCap_unary P a))).add (routine_unary P a))).add
      (RankedHistoryTask.phase_unary 27)

theorem rank_bound (P : Parameters) (q : List Bool) : rank P q < 189 * (birthCap P (RankedHistoryTask.root q) + 1) := by
  have HB : birth P q ≤ birthCap P (RankedHistoryTask.root q) := min_le_right _ _
  have HR := routine_lt P q
  have HP := phase_lt q
  unfold rank
  omega

theorem lower_birth (P : Parameters) (q c : List Bool) (hb : birth P c < birth P q) : rank P c < rank P q := by
  have HRc := routine_lt P c
  have HRq := routine_lt P q
  have HPc := phase_lt c
  have HPq := phase_lt q
  unfold rank
  omega

theorem lower_routine (P : Parameters) (q c : List Bool) (hb : birth P c = birth P q)
    (hr : routine P c < routine P q) : rank P c < rank P q := by
  have HPc := phase_lt c
  have HPq := phase_lt q
  unfold rank
  omega

theorem lower_phase (P : Parameters) (q c : List Bool) (hb : birth P c = birth P q)
    (hr : routine P c = routine P q) (hp : phase c < phase q) : rank P c < rank P q := by
  unfold rank
  omega

theorem routine_cap (P : Parameters) (q : List Bool) : 6 ≤ numericCap P q := by
  have HR : 1 ≤ rankCap P q := Nat.succ_le_of_lt (pow_pos (Nat.two_pow_pos _) _)
  have HN : 1 ≤ 2 ^ P.width q := Nat.succ_le_of_lt (Nat.two_pow_pos _)
  have HG : 1 ≤ FixedWidthPolynomial.count (P.ambient q + 1) (P.sourceWidth q) :=
    Nat.succ_le_of_lt (pow_pos (Nat.two_pow_pos _) _)
  unfold numericCap IntegralCriticalQueryBounds.cap birthCap
  omega

def reader (P : Parameters) (r : Routine) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = Field.slot14.code then BinaryNatCode.encode r.code
  else RankedHistoryFields.read (numericCap P) 16 z

theorem reader_FP (P : Parameters) (a : Access P) (r : Routine) : reader P r ∈ FP :=
  ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.slot14.code)).ite_mem_FP
    (constFn_mem_FP (BinaryNatCode.encode r.code))
    (RankedHistoryFields.read_FP (numericCap P) 16 (numericCap_binary P a))

def query (P : Parameters) (b : List Bool → ℕ) (r : Routine) (p : Phase) : List Bool → List Bool :=
  child P id b p (reader P r)

theorem query_FP (P : Parameters) (a : Access P) (b : List Bool → ℕ) (hb : BinaryFn b) (r : Routine) (p : Phase) :
    query P b r p ∈ FP := child_FP P a id id_mem_FP b hb p _ (reader_FP P a r)

theorem query_root (P : Parameters) (b : List Bool → ℕ) (r : Routine) (p : Phase) (q : List Bool) :
    RankedHistoryTask.root (query P b r p q) = RankedHistoryTask.root q := child_root P id b p _ q

theorem query_birth (P : Parameters) (b : List Bool → ℕ) (r : Routine) (p : Phase) (q : List Bool)
    (hb : b q ≤ birthCap P (RankedHistoryTask.root q)) : birth P (query P b r p q) = b q := by
  unfold query child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ hb

theorem query_phase (P : Parameters) (b : List Bool → ℕ) (r : Routine) (p : Phase) (q : List Bool) :
    phase (query P b r p q) = p.code := IntegralCriticalFlatMatrixQuery.child_phase P id b p _ q

theorem query_get (P : Parameters) (b : List Bool → ℕ) (r : Routine) (p : Phase) (q : List Bool) (f : Field) :
    get P f (query P b r p q) = if f = .slot14 then r.code else get P f q := by
  rw [query, child_get]
  have HI : Nat.fromBitsLE (BinaryNatCode.encode f.code) = f.code := Nat.fromBitsLE_bits _
  simp only [reader, pairSnd_pair, HI]
  by_cases hf : f = .slot14
  · subst f
    rw [ite_eq_left rfl, ite_eq_left rfl]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left ((Nat.le_of_lt_succ r.code_lt).trans (routine_cap P _))
  · have HC : f.code ≠ Field.slot14.code := by cases f <;> simp_all [Field.code]
    rw [ite_eq_right HC, ite_eq_right hf, RankedHistoryFields.read_packet]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change min (get P f q) (numericCap P (RankedHistoryTask.root q)) = get P f q
    exact min_eq_left (get_le P f q)

theorem query_routine (P : Parameters) (b : List Bool → ℕ) (r : Routine) (p : Phase) (q : List Bool) :
    routine P (query P b r p q) = r.code := by
  rw [routine, query_get, ite_eq_left rfl]
  exact min_eq_left (Nat.le_of_lt_succ r.code_lt)

theorem query_length (P : Parameters) (b : List Bool → ℕ) (r : Routine) (p : Phase) (q : List Bool)
    (hb : b q ≤ birthCap P (RankedHistoryTask.root q)) :
    (query P b r p q).length ≤ wordBudget P q := child_length P id b p _ q hb

def Frame (P : Parameters) (q c : List Bool) : Prop :=
  RankedHistoryTask.root c = RankedHistoryTask.root q ∧ c.length ≤ wordBudget P q ∧ rank P c < rank P q

theorem query_frame_birth (P : Parameters) (b : List Bool → ℕ) (r : Routine) (p : Phase) (q : List Bool)
    (hb : b q < birth P q) : Frame P q (query P b r p q) := by
  have HC : b q ≤ birthCap P (RankedHistoryTask.root q) := hb.le.trans (min_le_right _ _)
  exact ⟨query_root P b r p q, query_length P b r p q HC,
    lower_birth P q _ (by rw [query_birth P b r p q HC]; exact hb)⟩

theorem query_frame_routine (P : Parameters) (r : Routine) (p : Phase) (q : List Bool)
    (hr : r.code < routine P q) : Frame P q (query P (birth P) r p q) := by
  have HC : birth P q ≤ birthCap P (RankedHistoryTask.root q) := min_le_right _ _
  exact ⟨query_root P (birth P) r p q, query_length P (birth P) r p q HC,
    lower_routine P q _ (query_birth P (birth P) r p q HC) (by rw [query_routine]; exact hr)⟩

theorem query_saved (P : Parameters) (r : Routine) (p : Phase) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P (birth P) r p q) = IntegralMixedVirtualTaskBits.saved P q := by
  apply IntegralMixedVirtualTaskBits.saved_invariance
  · exact query_root P (birth P) r p q
  · exact query_birth P (birth P) r p q (min_le_right _ _)
  · rw [query_get]; rfl

theorem query_coordinate (P : Parameters) (b : List Bool → ℕ) (r : Routine) (p : Phase) (q : List Bool) :
    IntegralMixedVirtualTaskBits.coordinate P (query P b r p q) = IntegralMixedVirtualTaskBits.coordinate P q := by
  rw [IntegralMixedVirtualTaskBits.coordinate, query_get]; rfl
end LeanCanny.Algebra.IntegralMixedRoutineTaskBits
