/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCoordinatePacket
public import LeanCanny.Algebra.IntegerGridValueGramSpace
public import LeanCanny.Computation.PolyTimeBinaryRange
/-! # Native varying-degree metadata of the literal radial value system

The two local tables select perturbation indices and target degrees. The
Macaulay width is computed from ALL declared coordinate degrees, exactly as
in the existing affine value certificate; uniform-degree substitution is not
used.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueLayout
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def original (c : List Bool) := pairFst c
def tauTable (c : List Bool) := pairFst (pairSnd c)
def degreeTable (c : List Bool) := pairSnd (pairSnd c)
def tau (c : List Bool) (i : ℕ) := Nat.fromBitsLE (WordList.get (tauTable c) i)
def degree (c : List Bool) (i : ℕ) := Nat.fromBitsLE (WordList.get (degreeTable c) i)
noncomputable def arity (c : List Bool) := FormulaSignSlotRadialFormalInput.spatial (original c)
noncomputable def testDegree (c : List Bool) := degreeBudget (original c) + 1
noncomputable def level (c : List Bool) := (testDegree c - 1) +
  (∑ i : Fin (arity c), (degree c i.val - 1)) + 1
noncomputable def width (c : List Bool) := (level c).size

theorem original_FP : original ∈ FP := pairFst_mem_FP
theorem tauTable_FP : tauTable ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem degreeTable_FP : degreeTable ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem arity_unary : UnaryFn arity := FormulaSignSlotRadialFormalInput.spatial_unary.comp original_FP
theorem testDegree_unary : UnaryFn testDegree :=
  ((degreeBudget_unary).comp original_FP).add (UnaryFn.const 1)

private theorem table_binary (table : List Bool → List Bool) (ht : table ∈ FP)
    (index : List Bool → ℕ) (hi : BinaryFn index) :
    BinaryFn (fun q => Nat.fromBitsLE (WordList.get (table q) (index q))) := by
  have E := mem_FP_comp (mem_FP_pair ht hi.bits_mem_FP) WordList.reader_FP
  exact (BinaryFn.fromBits E).of_eq (fun q => by
    simp only [Function.comp_apply, WordList.reader_packet])

theorem degree_binary : BinaryFn (fun q => degree (pairFst q) (Nat.fromBitsLE (pairSnd q))) :=
  table_binary (degreeTable ∘ pairFst) (mem_FP_comp pairFst_mem_FP degreeTable_FP)
    (fun q => Nat.fromBitsLE (pairSnd q)) (BinaryFn.fromBits pairSnd_mem_FP)
theorem tau_binary : BinaryFn (fun q => tau (pairFst q) (Nat.fromBitsLE (pairSnd q))) :=
  table_binary (tauTable ∘ pairFst) (mem_FP_comp pairFst_mem_FP tauTable_FP)
    (fun q => Nat.fromBitsLE (pairSnd q)) (BinaryFn.fromBits pairSnd_mem_FP)
theorem level_binary : BinaryFn level := by
  have HD : BinaryFn (fun q => degree (pairFst q) (pairSnd q).length) :=
    table_binary (degreeTable ∘ pairFst) (mem_FP_comp pairFst_mem_FP degreeTable_FP)
      (fun q => (pairSnd q).length) (BinaryFn.ofUnary UnaryFn.index)
  have HS := BinaryFn.sum arity_unary (HD.sub (BinaryFn.const 1))
  apply (((BinaryFn.ofUnary testDegree_unary).sub (BinaryFn.const 1)).add HS).add (BinaryFn.const 1) |>.of_eq
  intro c
  simp only [level, List.length_replicate, pairFst_pair, pairSnd_pair]
  rw [Fin.sum_univ_eq_sum_range (fun i => degree c i - 1) (arity c)]
theorem width_unary : UnaryFn width :=
  (UnaryFn.length level_binary.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

noncomputable def layout : MacaulayFullBoxBits.Layout where
  arity c := arity c + 1
  width := width
  level := level
  degree c i := if i = 0 then testDegree c else degree c (i - 1)

theorem controls : layout.Controls := by
  refine ⟨arity_unary.add (UnaryFn.const 1), width_unary, level_binary, ?_⟩
  have HI : BinaryFn (fun q => Nat.fromBitsLE (pairSnd q)) := BinaryFn.fromBits pairSnd_mem_FP
  let rq : List Bool → List Bool := fun q =>
    pair (pairFst q) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) - 1))
  have HQ : rq ∈ FP := mem_FP_pair pairFst_mem_FP (HI.sub (BinaryFn.const 1)).bits_mem_FP
  have HDB : BinaryFn ((fun q => degree (pairFst q) (Nat.fromBitsLE (pairSnd q))) ∘ rq) :=
    degree_binary.comp HQ
  have HD : BinaryFn (fun q => degree (pairFst q) (Nat.fromBitsLE (pairSnd q) - 1)) :=
    HDB.of_eq (fun q => by
      simp only [Function.comp_apply, rq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  exact BinaryFn.ite (HI.eq (BinaryFn.const 0))
    ((BinaryFn.ofUnary testDegree_unary).comp pairFst_mem_FP) HD

theorem level_eq (c : List Bool) : level c = Macaulay.level
    (ProjectiveValueGram.degrees (fun i : Fin (arity c) => degree c i.val) (testDegree c)) := by
  simp only [level, Macaulay.level, ProjectiveValueGram.degrees,
    Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueLayout
