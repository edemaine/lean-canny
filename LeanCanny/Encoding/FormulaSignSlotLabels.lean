/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotBounds
/-! # Exact fixed-width sign labels cover all original coordinate tuples -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotSource
open ETR LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical

def signCode : SignType → List Bool
  | .zero => [false,false]
  | .neg => [false,true]
  | .pos => [true,false]
def encodeSigns (ss : List SignType) : List Bool := ss.flatMap signCode

theorem signCode_length (s : SignType) : (signCode s).length=2 := by cases s <;> rfl

theorem encodeSigns_length (ss : List SignType) : (encodeSigns ss).length=2*ss.length := by
  induction ss with
  | nil => rfl
  | cons s ss IH => simp only [encodeSigns,List.flatMap_cons,List.length_append,
      signCode_length,List.length_cons] at IH ⊢; omega

theorem sign_block (ss : List SignType) (i : ℕ) (hi : i < ss.length) :
    ((encodeSigns ss).drop (2*i)).take 2=signCode ss[i] := by
  induction ss generalizing i with
  | nil => simp at hi
  | cons s ss IH =>
    cases i with
    | zero => cases s <;> rfl
    | succ i =>
      have HI : i < ss.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      have HE : 2*(i+1)=2*i+2 := by omega
      rw [HE]
      cases s <;> simpa only [encodeSigns,List.flatMap_cons,signCode,List.cons_append,
        List.nil_append,List.drop_succ_cons,List.getElem_cons_succ] using IH i HI

theorem term_relabel (c a b idx : List Bool) :
    term (pair (pair c a) idx)=term (pair (pair c b) idx) := by
  simp only [term,termCode,raw,rawCode,query,dimension,pairFst_pair,pairSnd_pair]

noncomputable def pointLabel (c : List Bool) (env : ℕ → ℝ) : List Bool :=
  encodeSigns ((List.range (ClosedFormulaGateMetadata.count c)).map (fun i =>
    SignType.sign ((term (pair (pair c []) (List.replicate i true))).eval env)))

theorem pointLabel_length (c : List Bool) (env : ℕ → ℝ) :
    (pointLabel c env).length=2*ClosedFormulaGateMetadata.count c := by
  simp only [pointLabel,encodeSigns_length,List.length_map,List.length_range]

theorem pointLabel_block (c : List Bool) (env : ℕ → ℝ) (i : ℕ)
    (hi : i < ClosedFormulaGateMetadata.count c) :
    slotCode (pair (pair c (pointLabel c env)) (List.replicate i true))=
      signCode (SignType.sign ((term (pair (pair c []) (List.replicate i true))).eval env)) := by
  have H := sign_block ((List.range (ClosedFormulaGateMetadata.count c)).map (fun j =>
    SignType.sign ((term (pair (pair c []) (List.replicate j true))).eval env))) i
      (by simpa only [List.length_map,List.length_range] using hi)
  simpa only [slotCode,pairFst_pair,pairSnd_pair,List.length_replicate,pointLabel,
    List.getElem_map,List.getElem_range] using H

theorem strict_of_code (q : List Bool) (env : ℕ → ℝ) (s : SignType)
    (hcode : slotCode q=signCode s) (hsign : SignType.sign ((term q).eval env)=s) :
    (strict q).Holds env := by
  cases s with
  | zero =>
    simpa only [strict,hcode,signCode,ite_true,Formula.Holds] using sign_eq_zero_iff.mp hsign
  | neg =>
    simpa only [strict,hcode,signCode,Bool.false_eq_true,Bool.true_eq_false,List.cons.injEq,false_and,true_and,and_false,ite_false,
      ite_true,Formula.Holds] using sign_eq_neg_one_iff.mp hsign
  | pos =>
    have H := sign_eq_one_iff.mp hsign
    simp only [strict,hcode,signCode,Bool.false_eq_true,Bool.true_eq_false,List.cons.injEq,
      false_and,and_false,ite_false,ite_true,Formula.Holds,Term.eval,Int.cast_neg,Int.cast_one]
    linarith

theorem pointLabel_stratum (c : List Bool) (env : ℕ → ℝ) :
    (stratum (pair c (pointLabel c env))).Holds env := by
  have HL : (pairSnd (pair c (pointLabel c env))).length=2*count (pair c (pointLabel c env)) := by
    simpa only [count,pairFst_pair,pairSnd_pair] using pointLabel_length c env
  rw [stratum,ite_eq_left HL,FormulaConjunctionWriter.rangeConjunction,FormulaConjunctionWriter.holds]
  simp only [List.forall_mem_map,List.mem_range,count,pairFst_pair]
  intro i hi
  apply strict_of_code _ env _ (pointLabel_block c env i hi)
  rw [term_relabel c (pointLabel c env) []]

theorem pointLabel_envelope (c : List Bool) (env : ℕ → ℝ) :
    (envelope (pair c (pointLabel c env))).Holds env :=
  stratum_implies_envelope _ env (pointLabel_stratum c env)

end LeanCanny.Encoding.FormulaSignSlotSource
