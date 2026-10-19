/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SubroutinePSPACE
public import LeanCanny.Encoding.BinarySubFP

/-!
# A bounded scan with polynomial-space predicate calls

The parent retains the original input, a binary counter, and one accumulator
bit. Each candidate starts a certified space decider and waits for its answer.
The whole predicate computation need not be FP. Candidate `k` is supplied as
`pair input (encode k)`; the parent counter stores `k+1`.
-/

@[expose] public section

namespace LeanCanny.Computation.BoundedScan
open Complexity
open LeanCanny.Encoding

def counter (p : List Bool) : List Bool := pairFst (pairSnd p)
def accumulator (p : List Bool) : Bool := (pairSnd (pairSnd p))[0]?.getD false
def query (p : List Bool) : List Bool := pair (pairFst p) (BinaryNat.pred (counter p))
def request (bound : List Bool → List Bool) (p : List Bool) : Bool :=
  decide (Nat.fromBitsLE (counter p) ≤ Nat.fromBitsLE (bound (pairFst p)))
def halted (bound : List Bool → List Bool) (p : List Bool) : Bool :=
  decide (¬ Nat.fromBitsLE (counter p) ≤ Nat.fromBitsLE (bound (pairFst p)))

def combineAnswer {L : Language} (D : SpaceDecider L) (z : List Bool) : Bool :=
  accumulator (pairFst z) && D.answer (pairSnd z)

def resume {L : Language} (D : SpaceDecider L) (z : List Bool) : List Bool :=
  pair (pairFst (pairFst z))
    (pair (BinaryNat.succ (counter (pairFst z))) [combineAnswer D z])

def program {L : Language} (D : SpaceDecider L) (bound : List Bool → List Bool) :
    SubroutineIteration.Program where
  ordinary := id
  request := request bound
  start := fun p => D.init (query p)
  advance := D.advance
  halt := D.halt
  resume := resume D

def childTime {L : Language} (D : SpaceDecider L) (p : List Bool) : ℕ := D.time (query p)

def packet (c : List Bool) (k : ℕ) (v : Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (k + 1)) [v])

def init (c : List Bool) : List Bool := packet c 0 true

def result {L : Language} (D : SpaceDecider L) (q : List Bool) : Bool :=
  D.answer (D.advance^[D.time q] (D.init q))

def allBelow {L : Language} (D : SpaceDecider L) (c : List Bool) (k : ℕ) : Bool :=
  (List.range k).foldl (fun v i => v && result D (pair c (BinaryNatCode.encode i))) true

theorem counter_mem_FP : counter ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP

theorem accumulator_mem_FP : (fun p => [accumulator p]) ∈ FP :=
  (FPPred.getBit (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (UnaryFn.const 0)).flag_mem_FP

theorem query_mem_FP : query ∈ FP := by
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_comp counter_mem_FP BinaryNat.pred_mem_FP)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem request_mem_FP {bound : List Bool → List Bool} (hb : bound ∈ FP) :
    (fun p => [request bound p]) ∈ FP :=
  (BinaryNat.le_fppred counter_mem_FP (mem_FP_comp pairFst_mem_FP hb)).flag_mem_FP

theorem halted_mem_FP {bound : List Bool → List Bool} (hb : bound ∈ FP) :
    (fun p => [halted bound p]) ∈ FP :=
  (BinaryNat.le_fppred counter_mem_FP (mem_FP_comp pairFst_mem_FP hb)).not.flag_mem_FP

theorem combineAnswer_mem_FP {L : Language} (D : SpaceDecider L) :
    (fun z => [combineAnswer D z]) ∈ FP := by
  have hv := mem_FP_comp pairFst_mem_FP accumulator_mem_FP
  have h := (FPPred.of_flag hv).ite_mem_FP (mem_FP_comp pairSnd_mem_FP D.answerFP)
    (constFn_mem_FP [false])
  refine mem_FP_of_eq (g := fun z => [combineAnswer D z]) h ?_
  intro z
  cases ha : accumulator (pairFst z) <;> simp [combineAnswer, ha]

theorem resume_mem_FP {L : Language} (D : SpaceDecider L) : resume D ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hn := mem_FP_comp (mem_FP_comp pairFst_mem_FP counter_mem_FP) BinaryNat.succ_mem_FP
  have h := mem_FP_pair hc (mem_FP_pair hn (combineAnswer_mem_FP D))
  refine mem_FP_of_eq (g := resume D) h ?_
  intro z
  simp only [Function.comp_apply, resume]

theorem program_polyTime {L : Language} (D : SpaceDecider L)
    {bound : List Bool → List Bool} (hb : bound ∈ FP) : (program D bound).PolyTime := by
  have hs := mem_FP_comp query_mem_FP D.initFP
  exact ⟨id_mem_FP, request_mem_FP hb, hs, D.advanceFP, D.haltFP, resume_mem_FP D⟩

theorem init_mem_FP : init ∈ FP := by
  have h := mem_FP_pair id_mem_FP (constFn_mem_FP (pair (BinaryNatCode.encode 1) [true]))
  exact mem_FP_of_eq h (fun _ => rfl)

@[simp] theorem counter_packet (c : List Bool) (k : ℕ) (v : Bool) :
    counter (packet c k v) = BinaryNatCode.encode (k + 1) := by simp [counter, packet]

@[simp] theorem context_packet (c : List Bool) (k : ℕ) (v : Bool) :
    pairFst (packet c k v) = c := by simp [packet]

@[simp] theorem accumulator_packet (c : List Bool) (k : ℕ) (v : Bool) :
    accumulator (packet c k v) = v := by simp [accumulator, packet]

@[simp] theorem query_packet (c : List Bool) (k : ℕ) (v : Bool) :
    query (packet c k v) = pair c (BinaryNatCode.encode k) := by
  simp only [query, packet, pairFst_pair, counter, pairSnd_pair, BinaryNat.pred_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.add_sub_cancel]

theorem request_packet (bound : List Bool → List Bool) (c : List Bool) (N k : ℕ) (v : Bool)
    (hb : bound c = BinaryNatCode.encode N) :
    request bound (packet c k v) = decide (k < N) := by
  simp only [request, counter_packet, context_packet, hb,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  congr 1

theorem halted_packet (bound : List Bool → List Bool) (c : List Bool) (N k : ℕ) (v : Bool)
    (hb : bound c = BinaryNatCode.encode N) :
    halted bound (packet c k v) = decide (N ≤ k) := by
  simp only [halted, counter_packet, context_packet, hb,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  simp only [Nat.not_le, Nat.lt_succ_iff]

theorem resume_packet {L : Language} (D : SpaceDecider L) (c : List Bool) (k : ℕ)
    (v : Bool) (u : List Bool) :
    resume D (pair (packet c k v) u) = packet c (k + 1) (v && D.answer u) := by
  simp only [resume, pairFst_pair, pairSnd_pair, combineAnswer, accumulator_packet,
    counter_packet, context_packet]
  simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, packet]

@[simp] theorem allBelow_zero {L : Language} (D : SpaceDecider L) (c : List Bool) : allBelow D c 0 = true := rfl

theorem allBelow_succ {L : Language} (D : SpaceDecider L) (c : List Bool) (k : ℕ) :
    allBelow D c (k + 1) = (allBelow D c k && result D (pair c (BinaryNatCode.encode k))) := by
  simp only [allBelow, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem allBelow_correct {L : Language} (D : SpaceDecider L) (c : List Bool) (k : ℕ) :
    allBelow D c k = true ↔ ∀ i < k, pair c (BinaryNatCode.encode i) ∈ L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [allBelow_succ, Bool.and_eq_true, ih, show result D (pair c (BinaryNatCode.encode k)) = true ↔
      pair c (BinaryNatCode.encode k) ∈ L from (D.correct _).symm]
    constructor
    · rintro ⟨h, hk⟩ i hi
      by_cases he : i = k
      · simpa only [he] using hk
      · exact h i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h k (by omega)⟩

theorem step_packet {L : Language} (D : SpaceDecider L) (bound : List Bool → List Bool)
    (c : List Bool) (N k : ℕ) (hb : bound c = BinaryNatCode.encode N) (hk : k < N) :
    SubroutineIteration.abstractStep (program D bound) (childTime D) (packet c k (allBelow D c k)) =
      packet c (k + 1) (allBelow D c (k + 1)) := by
  simp only [SubroutineIteration.abstractStep, program, request_packet bound c N k _ hb,
    hk, decide_true, ↓reduceIte, childTime, query_packet]
  rw [resume_packet, allBelow_succ]
  rfl

theorem iterate_packet {L : Language} (D : SpaceDecider L) (bound : List Bool → List Bool)
    (c : List Bool) (N k : ℕ) (hb : bound c = BinaryNatCode.encode N) (hk : k ≤ N) :
    (SubroutineIteration.abstractStep (program D bound) (childTime D))^[k] (init c) =
      packet c k (allBelow D c k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega), step_packet D bound c N k hb (by omega)]

end LeanCanny.Computation.BoundedScan
