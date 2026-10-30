/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PairedScanSpace
public import LeanCanny.Computation.ImplicitGraphPSPACE
public import LeanCanny.Encoding.BracketsFP

/-! # Native resumable midpoint queries for recursive implicit graphs

A query retains the original graph context, reachability depth, and two short
vertex words. Its paired scan requests the two lower-depth halves through
every candidate midpoint. The child writers are native FP, and accepted
answers implement exactly the successor step of Savitch's recursion.
-/

@[expose] public section
namespace LeanCanny.Computation.RecursiveGraphMidpoints
open LeanCanny.Encoding Turing.MultiTapeTM Cslib.Reachability
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def context (q : List Bool) : List Bool := pairFst (pairFst q)
def depthWord (q : List Bool) : List Bool := pairSnd (pairFst q)
def depth (q : List Bool) : ℕ := Nat.fromBitsLE (depthWord q)
def start (q : List Bool) : List Bool := pairFst (pairSnd q)
def finish (q : List Bool) : List Bool := pairSnd (pairSnd q)
def task (c : List Bool) (d : ℕ) (u v : List Bool) : List Bool := pair (pair c (BinaryNatCode.encode d)) (pair u v)

theorem context_FP : context ∈ FP := by polytime [context]
theorem start_FP : start ∈ FP := by polytime [start]
theorem finish_FP : finish ∈ FP := by polytime [finish]
theorem depth_binary : BinaryFn depth := BinaryFn.fromBits (by polytime [depthWord])

def left (width : List Bool → ℕ) (z : List Bool) : List Bool :=
  let q := pairFst z
  task (context q) (depth q - 1) (start q)
    (ImplicitGraph.word (width (context q)) (Nat.fromBitsLE (pairSnd z)))
def right (width : List Bool → ℕ) (z : List Bool) : List Bool :=
  let q := pairFst z
  task (context q) (depth q - 1)
    (ImplicitGraph.word (width (context q)) (Nat.fromBitsLE (pairSnd z))) (finish q)

def program (width : List Bool → ℕ) : PairedScan.Program where
  count q := 2 ^ width (context q)
  left := left width
  right := right width

theorem left_FP {width : List Bool → ℕ} (hw : UnaryFn width) : left width ∈ FP := by
  have HC := mem_FP_comp pairFst_mem_FP context_FP
  have D : BinaryFn (fun z => depth (pairFst z)) := depth_binary.comp pairFst_mem_FP
  have HD := (D.sub (BinaryFn.const 1)).bits_mem_FP
  have HM := ImplicitGraph.word_computable (hw.comp HC) (BinaryFn.fromBits pairSnd_mem_FP)
  have HS : (fun z => start (pairFst z)) ∈ FP := by polytime [start]
  exact mem_FP_pair (mem_FP_pair HC HD) (mem_FP_pair HS HM)

theorem right_FP {width : List Bool → ℕ} (hw : UnaryFn width) : right width ∈ FP := by
  have HC := mem_FP_comp pairFst_mem_FP context_FP
  have D : BinaryFn (fun z => depth (pairFst z)) := depth_binary.comp pairFst_mem_FP
  have HD := (D.sub (BinaryFn.const 1)).bits_mem_FP
  have HM := ImplicitGraph.word_computable (hw.comp HC) (BinaryFn.fromBits pairSnd_mem_FP)
  have HF : (fun z => finish (pairFst z)) ∈ FP := by polytime [finish]
  exact mem_FP_pair (mem_FP_pair HC HD) (mem_FP_pair HM HF)

theorem certificates {width : List Bool → ℕ} (hw : UnaryFn width) :
    (program width).controller.Certificates (encQ := encBits) (encS := PairedScan.encState) :=
  (program width).certificates (ComputableTidilyInPolyTime.binary_two_pow.comp (hw.comp context_FP))
    (SpaceFunction.ofFP _ (left_FP hw)) (SpaceFunction.ofFP _ (right_FP hw))

theorem value_true_iff (width : List Bool → ℕ) (answer : List Bool → List Bool) (q : List Bool) :
    (program width).value answer q = [true] ↔ ∃ m : List Bool, m.length = width (context q) ∧
      answer (task (context q) (depth q - 1) (start q) m) = [true] ∧
      answer (task (context q) (depth q - 1) m (finish q)) = [true] := by
  change [(program width).scan answer q ((program width).count q)] = [true] ↔ _
  simp only [List.cons.injEq, and_true]
  rw [(program width).scan_true_iff]
  simp only [program, left, right, PairedScan.Program.entry, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  constructor
  · rintro ⟨k, _, hl, hr⟩
    exact ⟨_, ImplicitGraph.length_word _ _, hl, hr⟩
  · rintro ⟨m, hm, hl, hr⟩
    have HB : Nat.fromBitsLE m < 2 ^ width (context q) := by
      simpa only [hm] using Nat.fromBitsLE_lt_pow_length m
    refine ⟨Nat.fromBitsLE m, HB, ?_, ?_⟩
    · simpa only [← hm, ImplicitGraph.word_fromBitsLE] using hl
    · simpa only [← hm, ImplicitGraph.word_fromBitsLE] using hr

theorem value_reach (width : List Bool → ℕ) (edge : List Bool → List Bool → Bool)
    (answer : List Bool → List Bool) (c : List Bool) (d : ℕ) (u v : List Bool)
    (hl : ∀ m : List Bool, m.length = width c → answer (task c d u m) = [reach edge (width c) d u m])
    (hr : ∀ m : List Bool, m.length = width c → answer (task c d m v) = [reach edge (width c) d m v]) :
    (program width).value answer (task c (d + 1) u v) = [reach edge (width c) (d + 1) u v] := by
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  have HP := value_true_iff width answer (task c (d + 1) u v)
  simp only [task, context, depth, depthWord, start, finish, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.add_sub_cancel] at HP
  change (program width).scan answer (task c (d + 1) u v) ((program width).count (task c (d + 1) u v)) = true ↔ _
  change ([(program width).scan answer (task c (d + 1) u v) ((program width).count (task c (d + 1) u v))] = [true] ↔ _) at HP
  simp only [List.cons.injEq, and_true] at HP
  have HQ : reach edge (width c) (d + 1) u v = true ↔
      ∃ m : List Bool, m.length = width c ∧ reach edge (width c) d u m = true ∧ reach edge (width c) d m v = true := by
    simp only [reach, List.any_eq_true, Cslib.BitString.mem_enumList, Bool.and_eq_true]
  rw [HQ]
  constructor
  · intro H
    obtain ⟨m, hm, hL, hR⟩ := HP.mp H
    change answer (task c d u m) = [true] at hL
    change answer (task c d m v) = [true] at hR
    rw [hl m hm] at hL
    rw [hr m hm] at hR
    exact ⟨m, hm, List.cons.inj hL |>.1, List.cons.inj hR |>.1⟩
  · rintro ⟨m, hm, hL, hR⟩
    apply HP.mpr
    exact ⟨m, hm, (hl m hm).trans (congrArg List.singleton hL), (hr m hm).trans (congrArg List.singleton hR)⟩

theorem request_depth (width : List Bool → ℕ) (answer : List Bool → List Bool) (q child : List Bool)
    (hq : 0 < depth q)
    (hrequest : (program width).controller.Requests answer (fun q => 2 * (program width).count q) q child) :
    context child = context q ∧ depth child < depth q := by
  obtain ⟨k, _, he | he⟩ := ((program width).requests_iff answer q child).mp hrequest
  all_goals subst child
  all_goals simp only [program, left, right, PairedScan.Program.entry, pairFst_pair, pairSnd_pair,
    task, context, depth, depthWord, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  all_goals exact ⟨True.intro, Nat.sub_lt hq (by decide)⟩

end LeanCanny.Computation.RecursiveGraphMidpoints
