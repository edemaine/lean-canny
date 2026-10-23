/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.Brackets
public import LeanCanny.Tactic.PolyTime

/-!
# Polynomial-time recognition of serialized `Data` trees

The certificates use the native verified fold, unary arithmetic, and bounded
quantification interfaces. They produce membership in the multitape-machine class
`FP`, rather than a separate cost model for Lean functions.
-/

@[expose] public section

namespace LeanCanny.Encoding.Brackets

/-- Counting closing brackets is polynomial time, using a unary accumulator in a
verified bounded fold. The accumulator never exceeds the length of the input. -/
theorem countTrue_unary : UnaryFn (fun bits : List Bool => bits.count true) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsCountWithInput
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.id'
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const true)

theorem countFalse_unary : UnaryFn (fun bits : List Bool => bits.count false) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsCountWithInput
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.id'
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const false)

/-- Prefix counts are polynomial-time functions of the word and a unary position. -/
theorem prefixTrue_unary {bits : List Bool → List Bool} {n : List Bool → ℕ}
    (hbits : bits ∈ FP) (hn : UnaryFn n) :
    UnaryFn (fun z => ((bits z).take (n z)).count true) :=
  countTrue_unary.comp (take_mem_FP hbits hn)

theorem prefixFalse_unary {bits : List Bool → List Bool} {n : List Bool → ℕ}
    (hbits : bits ∈ FP) (hn : UnaryFn n) :
    UnaryFn (fun z => ((bits z).take (n z)).count false) :=
  countFalse_unary.comp (take_mem_FP hbits hn)

instance balancedDecidable (bits : List Bool) : Decidable (Balanced bits) := by
  unfold Balanced
  infer_instance

instance treeCodeDecidable (bits : List Bool) : Decidable (TreeCode bits) := by
  unfold TreeCode
  infer_instance

/-- Every prefix has nonnegative bracket depth, and the final depth is zero. -/
theorem balanced_fppred : FPPred Balanced := by
  have hprefix : FPPred fun w : List Bool =>
      ((pairFst w).take (pairSnd w).length).count true ≤
        ((pairFst w).take (pairSnd w).length).count false :=
    FPPred.le (prefixTrue_unary pairFst_mem_FP UnaryFn.index)
      (prefixFalse_unary pairFst_mem_FP UnaryFn.index)
  have hall := FPPred.forall_lt
    ((UnaryFn.length id_mem_FP).add (UnaryFn.const 1)) hprefix
  refine ((FPPred.eq countFalse_unary countTrue_unary).and hall).of_iff fun bits => ?_
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate, id_eq]
  exact and_congr Iff.rfl (forall_congr' fun i => imp_congr (by omega) Iff.rfl)

/-- Recognition of complete single tree encodings is a polynomial-time predicate. -/
theorem treeCode_fppred : FPPred TreeCode := by
  have hstrict : FPPred fun w : List Bool =>
      (pairSnd w).length = 0 ∨
        ((pairFst w).take (pairSnd w).length).count true <
          ((pairFst w).take (pairSnd w).length).count false :=
    (FPPred.eq UnaryFn.index (UnaryFn.const 0)).or
      (FPPred.lt (prefixTrue_unary pairFst_mem_FP UnaryFn.index)
        (prefixFalse_unary pairFst_mem_FP UnaryFn.index))
  have hall := FPPred.forall_lt (UnaryFn.length id_mem_FP) hstrict
  have hnonempty : FPPred fun bits : List Bool => bits ≠ [] :=
    ((FPPred.eq (UnaryFn.length id_mem_FP) (UnaryFn.const 0)).not).of_iff fun bits => by simp
  refine (balanced_fppred.and (hnonempty.and hall)).of_iff fun bits => ?_
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate, TreeCode]
  constructor
  · rintro ⟨hb, hn, hi⟩
    refine ⟨hb, hn, ?_⟩
    intro i hlt hpos
    exact (hi i hlt).resolve_left (by omega)
  · rintro ⟨hb, hn, hi⟩
    refine ⟨hb, hn, ?_⟩
    intro i hlt
    by_cases hz : i = 0
    · exact Or.inl hz
    · exact Or.inr (hi i hlt (by omega))

/-- A total one-bit machine-level recognizer for the image of `Data.toBits`. -/
def recognize (bits : List Bool) : Bool := decide (TreeCode bits)

theorem recognize_mem_FP : (fun bits => [recognize bits]) ∈ FP :=
  treeCode_fppred.flag_mem_FP

theorem recognize_eq_true_iff (bits : List Bool) :
    recognize bits = true ↔ ∃ d : Data, bits = d.toBits := by
  simp only [recognize, decide_eq_true_eq, treeCode_iff]

/-- Equality of polynomial-time strings is a polynomial-time predicate. -/
theorem stringEq_fppred {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    FPPred fun z => a z = b z :=
  .of_computable (Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_eq'
    (FP.computable ha) (FP.computable hb)) fun _ => decide_eq_true_iff.symm

/-- Repeat a fixed finite word a polynomial-time unary number of times. -/
theorem repeatWord_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) (word : List Bool) :
    (fun z => (List.replicate (n z) word).flatten) ∈ FP :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsFlatten
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.replicate hn
      (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const word))

end LeanCanny.Encoding.Brackets
