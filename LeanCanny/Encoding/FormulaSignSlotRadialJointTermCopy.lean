/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.ComplexProjectionCollision
/-! # Exact short arithmetic copies for the three literal joint source blocks -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointTermCopy
open LeanCanny.Computation LeanCanny.ETR LeanCanny.Encoding.Brackets
set_option backward.isDefEq.respectTransparency false

def renameBits (side : Bool) (bits : List Bool) :=
  NNF.second (Interleave.renameBits side (Codec.taggedOne 1 bits))
theorem renameBits_FP (side : Bool) : renameBits side ∈ FP := by
  apply mem_FP_of_eq (mem_FP_comp (mem_FP_comp (Codec.taggedOne_mem_FP 1 id_mem_FP)
    (Interleave.renameBits_mem_FP side)) NNF.second_mem_FP)
  intro bits
  rfl

theorem renameBits_term (side : Bool) (t : Term) :
    renameBits side t.toData.toBits = (t.rename (Interleave.index side)).toData.toBits := by
  have HQ : Codec.taggedOne 1 t.toData.toBits = (Formula.eqZero t).encode := by
    simp only [Formula.encode, Formula.toData, Codec.taggedOne_toBits]
  rw [renameBits, HQ, Interleave.renameBits_encode]
  simp only [Formula.rename, NNF.second, Formula.encode, Formula.toData,
    remainingChildren_toBits, firstChild_toBits]

def copy (first second : Bool) (t : Term) := (t.rename (Interleave.index first)).rename (Interleave.index second)
theorem copy_FP (first second : Bool) {t : List Bool → Term} (ht : (fun q => (t q).toData.toBits) ∈ FP) :
    (fun q => (copy first second (t q)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (mem_FP_comp ht (renameBits_FP first)) (renameBits_FP second))
    (fun q => by simp only [Function.comp_apply, renameBits_term, copy])

theorem copy_eval {R : Type*} [CommRing R] (first second : Bool) (t : Term) (env : ℕ → R) :
    (copy first second t).eval env = t.eval (fun i => env (4 * i + 2 * first.toNat + second.toNat)) := by
  rw [copy, Term.eval_rename, Term.eval_rename]
  apply Term.eval_congr
  intro i _
  simp only [Function.comp_apply, Interleave.index]
  congr 1
  omega

theorem copy_scope (first second : Bool) (t : Term) : (copy first second t).arity ≤ 4 * t.arity := by
  exact (ComplexProjectionCollision.term_rename_scope _ second).trans
    ((Nat.mul_le_mul_left 2 (ComplexProjectionCollision.term_rename_scope t first)).trans_eq (by omega))

end LeanCanny.Encoding.FormulaSignSlotRadialJointTermCopy
