/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.StrictOrTraversalSteps
/-! # The actual bounded native traversal returns exactly the original strict-OR terms -/
@[expose] public section
namespace LeanCanny.ETR.StrictOrTraversal
open LeanCanny.Encoding

theorem run_complete (n : ℕ) (ps : List Formula) (out : List Bool)
    (hp : ∀ p∈ps,StrictOrSyntax.Strict p) (hn : StrictOrSyntax.measure ps≤n) :
    step^[n] (pair (StrictOrSyntax.forest ps) out)=
      pair [] (out++SumSquares.forest (ps.flatMap StrictOrSyntax.atoms)) := by
  induction n generalizing ps out with
  | zero =>
    cases ps with
    | nil => simp only [StrictOrSyntax.forest_nil,List.flatMap_nil,SumSquares.forest_nil,List.append_nil,Function.iterate_zero_apply]
    | cons p ps =>
      have H:=StrictOrSyntax.nodes_pos p
      simp only [StrictOrSyntax.measure_cons] at hn
      omega
  | succ n IH =>
    cases ps with
    | nil =>
      simp only [StrictOrSyntax.forest_nil,List.flatMap_nil,SumSquares.forest_nil,List.append_nil]
      exact Function.iterate_fixed (step_empty out) _
    | cons p ps =>
      have HP:=hp p List.mem_cons_self
      have HT : ∀ q∈ps,StrictOrSyntax.Strict q := fun q hq => hp q (List.mem_cons_of_mem p hq)
      cases HP with
      | falsum =>
        rw [StrictOrSyntax.forest_cons,Function.iterate_succ_apply,step_false]
        have HB : StrictOrSyntax.measure ps≤n := by
          simp only [StrictOrSyntax.measure_cons,StrictOrSyntax.nodes] at hn
          omega
        simpa only [List.flatMap_cons,StrictOrSyntax.atoms,List.nil_append] using IH ps out HT HB
      | ltZero t =>
        rw [StrictOrSyntax.forest_cons,Function.iterate_succ_apply,step_lt]
        have HB : StrictOrSyntax.measure ps≤n := by
          simp only [StrictOrSyntax.measure_cons,StrictOrSyntax.nodes] at hn
          omega
        simpa only [List.flatMap_cons,StrictOrSyntax.atoms,List.singleton_append,SumSquares.forest_cons,List.append_assoc] using
          IH ps (out++(Term.mul (.const (-1)) t).toData.toBits) HT HB
      | @or p q HP HQ =>
        rw [StrictOrSyntax.forest_cons,Function.iterate_succ_apply,step_or]
        have HC : ∀ a∈p::q::ps,StrictOrSyntax.Strict a := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact HP
          · rcases List.mem_cons.mp ha with rfl | ha
            · exact HQ
            · exact HT a ha
        have HB : StrictOrSyntax.measure (p::q::ps)≤n := by
          simp only [StrictOrSyntax.measure_cons,StrictOrSyntax.nodes] at hn ⊢
          omega
        have HR := IH (p::q::ps) out HC HB
        simpa only [StrictOrSyntax.forest_cons,List.append_assoc,List.flatMap_cons,StrictOrSyntax.atoms,List.append_assoc] using HR

theorem forest_encode {p : Formula} (hp : StrictOrSyntax.Strict p) :
    forest p.encode=SumSquares.forest (StrictOrSyntax.atoms p) := by
  have HR := run_complete p.encode.length [p] [] (by simpa only [List.mem_singleton,forall_eq] using hp)
    (by simpa only [StrictOrSyntax.measure_cons,StrictOrSyntax.measure_nil,Nat.add_zero,
      Formula.encode,Data.length_toBits] using StrictOrSyntax.nodes_le_size p)
  simp only [StrictOrSyntax.forest_cons,StrictOrSyntax.forest_nil,List.append_nil,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.nil_append] at HR
  simp only [forest,init,FormulaView.normalize_encode]
  rw [HR,pairSnd_pair]

end LeanCanny.ETR.StrictOrTraversal
