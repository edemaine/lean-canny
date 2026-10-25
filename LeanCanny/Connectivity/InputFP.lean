/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.Encoding
public import LeanCanny.ETR.Grammar
public import LeanCanny.ETR.NNFEncoding
public import LeanCanny.ETR.FormulaView

/-! # Polynomial-time connectivity input recognition

These predicates recognize the complete canonical encodings, including tags,
dimensions, nested formulas and the absence of trailing data.
-/

@[expose] public section

namespace LeanCanny.Connectivity.Input
open ETR LeanCanny.Encoding.Brackets

def field : ℕ → List Bool → List Bool
  | 0 => firstChild
  | k + 1 => fun bits => field k (remainingChildren bits)

theorem field_mem_FP (k : ℕ) : field k ∈ FP := by
  induction k with
  | zero => exact firstChild_mem_FP
  | succ k ih => exact mem_FP_comp remainingChildren_mem_FP ih

def pointFrame (bits : List Bool) : List Bool :=
  wrap ((Codec.unary 0).toBits ++ field 1 bits ++ field 2 bits ++ field 3 bits ++ field 4 bits)

def wholeFrame (bits : List Bool) : List Bool :=
  wrap ((Codec.unary 1).toBits ++ field 1 bits ++ field 2 bits)

theorem pointFrame_mem_FP : pointFrame ∈ FP :=
  mem_FP_comp (appendFn_mem_FP
    (appendFn_mem_FP (appendFn_mem_FP
      (appendFn_mem_FP (constFn_mem_FP _) (field_mem_FP 1)) (field_mem_FP 2))
      (field_mem_FP 3)) (field_mem_FP 4)) wrap_mem_FP

theorem wholeFrame_mem_FP : wholeFrame ∈ FP :=
  mem_FP_comp (appendFn_mem_FP
    (appendFn_mem_FP (constFn_mem_FP _) (field_mem_FP 1)) (field_mem_FP 2)) wrap_mem_FP

def IsPoint (bits : List Bool) : Prop :=
  bits = pointFrame bits ∧ Codec.IsUnary (field 1 bits) ∧
    Grammar.recognizeFormula (field 2 bits) = true ∧
    Grammar.recognizeFormula (field 3 bits) = true ∧
    Grammar.recognizeFormula (field 4 bits) = true

def IsWhole (bits : List Bool) : Prop :=
  bits = wholeFrame bits ∧ Codec.IsUnary (field 1 bits) ∧
    Grammar.recognizeFormula (field 2 bits) = true

instance (bits : List Bool) : Decidable (IsPoint bits) := by unfold IsPoint; infer_instance
instance (bits : List Bool) : Decidable (IsWhole bits) := by unfold IsWhole; infer_instance

theorem isPoint_fppred : FPPred IsPoint :=
  (stringEq_fppred id_mem_FP pointFrame_mem_FP).and
    ((Codec.isUnary_fppred.comp (field_mem_FP 1)).and
      (((FPPred.of_flag Grammar.recognizeFormula_mem_FP).comp (field_mem_FP 2)).and
        (((FPPred.of_flag Grammar.recognizeFormula_mem_FP).comp (field_mem_FP 3)).and
          ((FPPred.of_flag Grammar.recognizeFormula_mem_FP).comp (field_mem_FP 4)))))

theorem isWhole_fppred : FPPred IsWhole :=
  (stringEq_fppred id_mem_FP wholeFrame_mem_FP).and
    ((Codec.isUnary_fppred.comp (field_mem_FP 1)).and
      ((FPPred.of_flag Grammar.recognizeFormula_mem_FP).comp (field_mem_FP 2)))

@[simp] theorem field_point_dimension (q : PointQuery) :
    field 1 (point q).encode = (Codec.unary q.space.dimension).toBits := by
  simp [field, encode, toData, firstChild_toBits, remainingChildren_toBits]

@[simp] theorem field_point_space (q : PointQuery) : field 2 (point q).encode = q.space.formula.encode := by
  simp [field, encode, toData, Formula.encode, firstChild_toBits, remainingChildren_toBits]

@[simp] theorem field_point_source (q : PointQuery) : field 3 (point q).encode = q.source.encode := by
  simp [field, encode, toData, Formula.encode, firstChild_toBits, remainingChildren_toBits]

@[simp] theorem field_point_target (q : PointQuery) : field 4 (point q).encode = q.target.encode := by
  simp [field, encode, toData, Formula.encode, firstChild_toBits, remainingChildren_toBits]

@[simp] theorem field_whole_dimension (d : Description) :
    field 1 (whole d).encode = (Codec.unary d.dimension).toBits := by
  simp [field, encode, toData, firstChild_toBits, remainingChildren_toBits]

@[simp] theorem field_whole_space (d : Description) : field 2 (whole d).encode = d.formula.encode := by
  simp [field, encode, toData, Formula.encode, firstChild_toBits, remainingChildren_toBits]

theorem isPoint_iff (bits : List Bool) : IsPoint bits ↔ ∃ q : PointQuery, bits = (point q).encode := by
  constructor
  · rintro ⟨h, hd, hs, ha, hb⟩
    obtain ⟨n, hn⟩ := (Codec.isUnary_iff _).mp hd
    obtain ⟨s, hS⟩ := (Grammar.recognizeFormula_true_iff _).mp hs
    obtain ⟨a, hA⟩ := (Grammar.recognizeFormula_true_iff _).mp ha
    obtain ⟨b, hB⟩ := (Grammar.recognizeFormula_true_iff _).mp hb
    refine ⟨⟨⟨n, s⟩, a, b⟩, ?_⟩
    rw [h]
    simp [pointFrame, hn, hS, hA, hB, encode, toData, Formula.encode, Data.toBits_l, wrap,
      List.append_assoc]
  · rintro ⟨q, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [pointFrame, field_point_dimension, field_point_space,
        field_point_source, field_point_target]
      simp [encode, toData, Formula.encode, Data.toBits_l, wrap, List.append_assoc]
    · simp [Codec.IsUnary]
    · simp [Grammar.recognizeFormula_encode]
    · simp [Grammar.recognizeFormula_encode]
    · simp [Grammar.recognizeFormula_encode]

theorem isWhole_iff (bits : List Bool) : IsWhole bits ↔ ∃ d : Description, bits = (whole d).encode := by
  constructor
  · rintro ⟨h, hd, hs⟩
    obtain ⟨n, hn⟩ := (Codec.isUnary_iff _).mp hd
    obtain ⟨s, hS⟩ := (Grammar.recognizeFormula_true_iff _).mp hs
    refine ⟨⟨n, s⟩, ?_⟩
    rw [h]
    simp [wholeFrame, hn, hS, encode, toData, Formula.encode, Data.toBits_l, wrap, List.append_assoc]
  · rintro ⟨d, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [wholeFrame, field_whole_dimension, field_whole_space]
      simp [encode, toData, Formula.encode, Data.toBits_l, wrap, List.append_assoc]
    · simp [Codec.IsUnary]
    · simp [Grammar.recognizeFormula_encode]

end LeanCanny.Connectivity.Input
