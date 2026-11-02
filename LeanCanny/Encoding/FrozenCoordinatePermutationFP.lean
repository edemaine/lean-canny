/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.WordListFP
public import LeanCanny.Computation.PolyTimeRange
/-! # Native stable partition of coordinate indices from an original flag mask -/
@[expose] public section
namespace LeanCanny.Encoding.FrozenCoordinatePermutationBits
set_option backward.isDefEq.respectTransparency false

def selected (mask : List Bool) (b : Bool) := (List.range mask.length).filter (fun j => decide (mask[j]?.getD false = b))
def partition (mask : List Bool) := selected mask true ++ selected mask false

def entry (b : Bool) (p : List Bool) :=
  if (pairFst (pairFst p))[(pairSnd p).length]?.getD false = b then
    pair (BinaryNatCode.encode (pairSnd p).length) [] else []
def pass (b : Bool) (q : List Bool) := (List.range (pairFst q).length).flatMap fun j =>
  if (pairFst q)[j]?.getD false = b then pair (BinaryNatCode.encode j) [] else []
def table (q : List Bool) := pass true q ++ pass false q
def reader (q : List Bool) := WordList.reader (pair (table q) (pairSnd q))

theorem entry_FP (b : Bool) : entry b ∈ FP := by
  have HP := FPPred.getBit (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) UnaryFn.index
  have HV := mem_FP_pair (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP (constFn_mem_FP [])
  cases b with
  | true => exact HP.ite_mem_FP HV (constFn_mem_FP [])
  | false =>
    have HN : FPPred (fun p => (pairFst (pairFst p))[(pairSnd p).length]?.getD false = false) :=
      HP.not.of_iff (by intro p; cases H : (pairFst (pairFst p))[(pairSnd p).length]?.getD false <;> simp [Function.comp_apply, H])
    exact HN.ite_mem_FP HV (constFn_mem_FP [])

theorem pass_FP (b : Bool) : pass b ∈ FP :=
  mem_FP_of_eq (flatMap_range_mem_FP (entry_FP b) pairFst_mem_FP) (fun q => by
    simp only [pass, entry, pairFst_pair, pairSnd_pair, List.length_replicate])

theorem reader_FP : reader ∈ FP :=
  mem_FP_comp (mem_FP_pair (appendFn_mem_FP (pass_FP true) (pass_FP false)) pairSnd_mem_FP) WordList.reader_FP

theorem encode_flatMap (ws : List (List Bool)) : WordList.encode ws = ws.flatMap (fun w => pair w []) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [WordList.encode, List.flatMap_cons, ih, pair, List.append_nil]

theorem encode_append (xs ys : List (List Bool)) : WordList.encode (xs ++ ys) = WordList.encode xs ++ WordList.encode ys := by
  simp only [encode_flatMap, List.flatMap_append]

theorem flatMap_filter {α : Type*} (xs : List α) (p : α → Prop) [DecidablePred p] (f : α → List Bool) :
    xs.flatMap (fun x => if p x then f x else []) = (xs.filter (fun x => decide (p x))).flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases hx : p x <;> simp [hx, ih]

theorem pass_eq (b : Bool) (q : List Bool) :
    pass b q = WordList.encode ((selected (pairFst q) b).map BinaryNatCode.encode) := by
  unfold pass selected
  rw [flatMap_filter, encode_flatMap, List.flatMap_map]

theorem table_eq (q : List Bool) : table q = WordList.encode ((partition (pairFst q)).map BinaryNatCode.encode) := by
  simp only [table, partition, List.map_append, encode_append, pass_eq]

theorem reader_packet (mask : List Bool) (j : ℕ) :
    reader (pair mask (BinaryNatCode.encode j)) = BinaryNatCode.encode ((partition mask)[j]?.getD 0) := by
  simp only [reader, table_eq, pairFst_pair, pairSnd_pair, WordList.reader_packet, WordList.get_encode, List.getElem?_map]
  cases (partition mask)[j]? <;> rfl
end LeanCanny.Encoding.FrozenCoordinatePermutationBits
