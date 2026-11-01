/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.FormulaBooleanCircuitNodes
public import LeanCanny.Computation.PolyTimeRange
/-! # A native linear-size conjunction writer over a unary range -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaConjunctionWriter
open LeanCanny.Computation ETR FormulaBooleanCircuitSource

def conjunction (ps : List Formula) : Formula := ps.foldr Formula.and (.not .falsum)

theorem holds (ps : List Formula) (env : ℕ → ℝ) :
    (conjunction ps).Holds env ↔ ∀ p∈ps, p.Holds env := by
  induction ps with
  | nil => simp [conjunction,Formula.Holds]
  | cons p ps IH =>
    change p.Holds env ∧ (conjunction ps).Holds env ↔ _
    simp only [IH,List.mem_cons,forall_eq_or_imp]

theorem arity (ps : List Formula) (n : ℕ) (h : ∀ p∈ps, p.arity≤n) : (conjunction ps).arity≤n := by
  induction ps with
  | nil => exact Nat.zero_le _
  | cons p ps IH =>
    exact max_le (h p (List.mem_cons_self)) (IH (fun q hq => h q (List.mem_cons_of_mem p hq)))

theorem encode (ps : List Formula) :
    (conjunction ps).encode=(ps.flatMap (fun p => header 4++p.encode))++
      (Formula.not .falsum).encode++List.replicate ps.length true := by
  induction ps with
  | nil => simp [conjunction]
  | cons p ps IH =>
    change (Formula.and p (conjunction ps)).encode=_
    have HB := encode_binary false p (conjunction ps)
    change (Formula.and p (conjunction ps)).encode=_ at HB
    rw [HB,IH]
    simp only [binaryTag,Bool.false_eq_true,ite_false,List.flatMap_cons,List.length_cons,List.replicate_succ,
      List.append_assoc]
    simp only [← List.replicate_succ',List.replicate_succ]

def rangeConjunction (E : List Bool → Formula) (n : List Bool → ℕ) (c : List Bool) : Formula :=
  conjunction ((List.range (n c)).map (fun i => E (pair c (List.replicate i true))))

theorem range_FP {E : List Bool → Formula} {n : List Bool → ℕ}
    (hE : (fun q => (E q).encode) ∈ FP) (hn : UnaryFn n) :
    (fun c => (rangeConjunction E n c).encode) ∈ FP := by
  have HE : (fun q => header 4++(E q).encode) ∈ FP := appendFn_mem_FP (constFn_mem_FP _) hE
  have HL := flatMap_range_mem_FP HE hn.mem_FP
  have HR : (fun c => (Formula.not .falsum).encode++List.replicate (n c) true) ∈ FP :=
    appendFn_mem_FP (constFn_mem_FP _) hn.mem_FP
  apply mem_FP_of_eq (appendFn_mem_FP HL HR)
  intro c
  simp only [rangeConjunction,encode,List.flatMap_map,List.length_map,List.length_range,
    List.length_replicate,List.append_assoc]

end LeanCanny.Encoding.FormulaConjunctionWriter
