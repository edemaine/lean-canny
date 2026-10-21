/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.NegationNormalForm
public import LeanCanny.Encoding.DynamicTreeFold

/-!
# Encoded operations for the simultaneous NNF transform

Each frame stores the original children and the two transformed child lists.
Atoms use the original bytes, protecting arithmetic payloads from reinterpretation.
The local constructor tests also check that their operand fields are nonempty.
-/

@[expose] public section

namespace LeanCanny.ETR.NNF

open LeanCanny.Encoding.Brackets

def second (bits : List Bool) : List Bool := firstChild (remainingChildren bits)

def third (bits : List Bool) : List Bool := firstChild (remainingChildren (remainingChildren bits))

theorem second_mem_FP : second ∈ FP := by
  unfold second
  simpa only [Function.comp_def] using
    mem_FP_comp remainingChildren_mem_FP firstChild_mem_FP

theorem third_mem_FP : third ∈ FP := by
  unfold third
  simpa only [Function.comp_def] using
    mem_FP_comp (mem_FP_comp remainingChildren_mem_FP remainingChildren_mem_FP) firstChild_mem_FP

@[simp] theorem firstChild_empty : firstChild Data.empty.toBits = [] := by
  simp [firstChild, contents_toBits, firstNode]

@[simp] theorem remainingChildren_empty : remainingChildren Data.empty.toBits = Data.empty.toBits := by
  rw [remainingChildren, contents_toBits]
  simp [afterNode, wrap, Data.toBits_l]

def HasOne (tag : ℕ) (bits : List Bool) : Prop :=
  bits = Codec.taggedOne tag (second bits) ∧ second bits ≠ []

def HasTwo (tag : ℕ) (bits : List Bool) : Prop :=
  bits = Codec.taggedTwo tag (second bits) (third bits) ∧ second bits ≠ [] ∧ third bits ≠ []

instance (tag : ℕ) (bits : List Bool) : Decidable (HasOne tag bits) := by unfold HasOne; infer_instance
instance (tag : ℕ) (bits : List Bool) : Decidable (HasTwo tag bits) := by unfold HasTwo; infer_instance

theorem hasOne_toBits (tag : ℕ) (d : Data) :
    HasOne tag d.toBits ↔ ∃ p : Data, d = one tag p := by
  have hnonempty (p : Data) : p.toBits ≠ [] := by
    intro hp
    have hh := congrArg List.length hp
    have hpos := @Data.size_pos p
    simp only [Data.length_toBits, List.length_nil] at hh
    omega
  cases d with
  | l xs =>
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        simp [HasOne, second, Codec.taggedOne_toBits, Data.toBits_injective.eq_iff,
          remainingChildren_toBits, firstChild_toBits, one, hnonempty]

theorem hasTwo_toBits (tag : ℕ) (d : Data) :
    HasTwo tag d.toBits ↔ ∃ p q : Data, d = two tag p q := by
  have hnonempty (p : Data) : p.toBits ≠ [] := by
    intro hp
    have hh := congrArg List.length hp
    have hpos := @Data.size_pos p
    simp only [Data.length_toBits, List.length_nil] at hh
    omega
  cases d with
  | l xs =>
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩ <;>
        simp [HasTwo, second, third, Codec.taggedTwo_toBits, Data.toBits_injective.eq_iff,
          remainingChildren_toBits, firstChild_toBits, two, hnonempty]

theorem hasOne_fppred (tag : ℕ) : FPPred (HasOne tag) :=
  (stringEq_fppred id_mem_FP (Codec.taggedOne_mem_FP tag second_mem_FP)).and
    ((FPPred.eq (UnaryFn.length second_mem_FP) (UnaryFn.const 0)).not.of_iff
      (by intro bits; simp only [List.length_eq_zero_iff]))

theorem hasTwo_fppred (tag : ℕ) : FPPred (HasTwo tag) :=
  (stringEq_fppred id_mem_FP (Codec.taggedTwo_mem_FP tag second_mem_FP third_mem_FP)).and
    (((FPPred.eq (UnaryFn.length second_mem_FP) (UnaryFn.const 0)).not.of_iff
      (by intro bits; simp only [List.length_eq_zero_iff])).and
     ((FPPred.eq (UnaryFn.length third_mem_FP) (UnaryFn.const 0)).not.of_iff
      (by intro bits; simp only [List.length_eq_zero_iff])))

def code (xs : List Data) : List Bool :=
  pair (Data.l xs).toBits
    (pair (Data.l (xs.map (fun d => (dual d).1))).toBits
      (Data.l (xs.map (fun d => (dual d).2))).toBits)

def raw (frame : List Bool) : List Bool := pairFst frame
def pos (frame : List Bool) : List Bool := pairFst (pairSnd frame)
def neg (frame : List Bool) : List Bool := pairSnd (pairSnd frame)

theorem raw_mem_FP : raw ∈ FP := pairFst_mem_FP
theorem pos_mem_FP : pos ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem neg_mem_FP : neg ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

def finishWith (positive : Bool) (frame : List Bool) : List Bool :=
  let r := raw frame
  let chosen := if positive then pos frame else neg frame
  if HasOne 1 r ∨ HasOne 2 r then
    if positive then r else Codec.taggedOne 3 r
  else if HasOne 3 r then second (if positive then neg frame else pos frame)
  else if HasTwo 4 r then Codec.taggedTwo (if positive then 4 else 5) (second chosen) (third chosen)
  else if HasTwo 5 r then Codec.taggedTwo (if positive then 5 else 4) (second chosen) (third chosen)
  else if positive then falseData.toBits else trueData.toBits

theorem finishWith_mem_FP (positive : Bool) : finishWith positive ∈ FP := by
  have hatom := ((hasOne_fppred 1).or (hasOne_fppred 2)).comp raw_mem_FP
  have hnot := (hasOne_fppred 3).comp raw_mem_FP
  have hand := (hasTwo_fppred 4).comp raw_mem_FP
  have hor := (hasTwo_fppred 5).comp raw_mem_FP
  have hp2 := mem_FP_comp pos_mem_FP second_mem_FP
  have hp3 := mem_FP_comp pos_mem_FP third_mem_FP
  have hn2 := mem_FP_comp neg_mem_FP second_mem_FP
  have hn3 := mem_FP_comp neg_mem_FP third_mem_FP
  have hnegOr := hor.ite_mem_FP (Codec.taggedTwo_mem_FP 4 hn2 hn3) (constFn_mem_FP trueData.toBits)
  have hnegAnd := hand.ite_mem_FP (Codec.taggedTwo_mem_FP 5 hn2 hn3) hnegOr
  have hnegNot := hnot.ite_mem_FP hp2 hnegAnd
  have hneg := hatom.ite_mem_FP (Codec.taggedOne_mem_FP 3 raw_mem_FP) hnegNot
  have hposOr := hor.ite_mem_FP (Codec.taggedTwo_mem_FP 5 hp2 hp3) (constFn_mem_FP falseData.toBits)
  have hposAnd := hand.ite_mem_FP (Codec.taggedTwo_mem_FP 4 hp2 hp3) hposOr
  have hposNot := hnot.ite_mem_FP hn2 hposAnd
  have hpos := hatom.ite_mem_FP raw_mem_FP hposNot
  cases positive
  · refine mem_FP_of_eq hneg (fun frame => ?_)
    simp only [finishWith, Function.comp_apply, Bool.false_eq_true, ite_false]
  · refine mem_FP_of_eq hpos (fun frame => ?_)
    simp only [finishWith, Function.comp_apply, ite_true]

theorem finishWith_code (positive : Bool) (xs : List Data) :
    finishWith positive (code xs) = (if positive then (dual (.l xs)).1 else (dual (.l xs)).2).toBits := by
  cases positive <;>
    rcases xs with _ | ⟨tag, _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩⟩ <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals
    rw [dual] <;>
    simp [finishWith, code, raw, pos, neg, hasOne_toBits, hasTwo_toBits, one, two,
      second, third, remainingChildren_toBits, firstChild_toBits, Codec.taggedOne_toBits,
      Codec.taggedTwo_toBits]
  all_goals split_ifs <;> rfl

def combine (child parent : List Data) : List Data := Data.l child :: parent

def combineBits (packet : List Bool) : List Bool :=
  let child := pairFst (pairSnd packet)
  let parent := pairSnd (pairSnd packet)
  pair (consNode (raw child) (raw parent))
    (pair (consNode (finishWith true child) (pos parent))
      (consNode (finishWith false child) (neg parent)))

theorem combineBits_mem_FP : combineBits ∈ FP := by
  have hc := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hp := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hrc := mem_FP_comp hc raw_mem_FP
  have hrp := mem_FP_comp hp raw_mem_FP
  have hpc := mem_FP_comp hc (finishWith_mem_FP true)
  have hpp := mem_FP_comp hp pos_mem_FP
  have hnc := mem_FP_comp hc (finishWith_mem_FP false)
  have hnp := mem_FP_comp hp neg_mem_FP
  unfold combineBits
  exact mem_FP_pair
    (consNode_mem_FP hrc hrp)
    (mem_FP_pair (consNode_mem_FP hpc hpp) (consNode_mem_FP hnc hnp))

theorem combineBits_code (z : List Bool) (child parent : List Data) :
    combineBits (pair z (pair (code child) (code parent))) = code (combine child parent) := by
  simp only [combineBits, pairFst_pair, pairSnd_pair, finishWith_code, ite_true, Bool.false_eq_true,
    ite_false]
  simp only [code, raw, pos, neg, combine, pairFst_pair, pairSnd_pair, List.map_cons, consNode_toBits]

end LeanCanny.ETR.NNF
