/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.PartialHomogenizationPaddedFP
public import LeanCanny.Algebra.FixedLeadingTiltedSource

/-! # Native writing of the fixed-leading integer tilted source

The degree allowance may be the original expression's unary data size. The
literal resulting term supplies the existing original coefficient reader;
there is no retained-ring leading coefficient or evaluator assumption.
-/
@[expose] public section
namespace LeanCanny.ETR.FixedLeadingTiltedSourceFP
open LeanCanny.Encoding LeanCanny.Algebra

theorem lowTerm_FP {t : List Bool → Term} {k D u : List Bool → ℕ}
    (ht : (fun c => (t c).toData.toBits) ∈ FP) (hk : UnaryFn k) (hD : UnaryFn D) (hu : UnaryFn u)
    (hb : ∀ c, (t c).degreeBound ≤ D c) :
    (fun c => (FixedLeadingTiltedSource.lowTerm (k c) (D c) (u c) (t c)).toData.toBits) ∈ FP := by
  have HH := PartialHomogenization.padded_FP ht hk hD hb
  have HE : (fun c => ((Term.var 0).power (3*D c)).toData.toBits) ∈ FP := by
    apply mem_FP_of_eq (TermPower.write_mem_FP (constFn_mem_FP (Term.var 0).toData.toBits)
      ((UnaryFn.const 3).mul hD))
    intro c
    rw [TermPower.write_correct,TermView.term_toBits]
  have HV := mem_FP_of_eq (Term.variableBits_mem_FP (hu.add (UnaryFn.const 1)))
    (fun _ => Term.variableBits_eq _)
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 HH HH)
    (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) (Codec.taggedTwo_mem_FP 3 HE HV)))
  intro c
  simp only [FixedLeadingTiltedSource.lowTerm,Term.add_toBits,Term.mul_toBits]

def lowWord (k D u : ℕ) (t : Term) : List Bool :=
  (FixedLeadingTiltedSource.lowTerm k D u t).toData.toBits

theorem lowWord_arity (k D : ℕ) {n : ℕ} (u : Fin n) (t : Term) (ha : t.arity ≤ n) :
    (TermView.term (lowWord k D u.val t)).arity ≤ n+1 := by
  rw [lowWord,TermView.term_toBits]
  exact (FixedLeadingTiltedSource.lowTerm_arity k D u.val t).trans (by omega)

theorem lowWord_polynomial (k D : ℕ) {n : ℕ} (u : Fin n) (t : Term) (ht : t.degreeBound ≤ D) :
    (TermView.term (lowWord k D u.val t)).finitePolynomial (n+1) =
      (FixedLeadingTiltedSource.source k D u t ht).low := by
  rw [lowWord,TermView.term_toBits]
  rfl

def originalDegree (t : List Bool → Term) (c : List Bool) : ℕ := (t c).toData.size

theorem originalDegree_unary {t : List Bool → Term} (ht : (fun c => (t c).toData.toBits) ∈ FP) :
    UnaryFn (originalDegree t) :=
  (UnaryFn.length ht).of_eq (fun _ => Data.length_toBits _)

theorem sourceDegree_unary {t : List Bool → Term} (ht : (fun c => (t c).toData.toBits) ∈ FP) :
    UnaryFn (fun c => FixedLeadingTiltedSource.degree (originalDegree t c)) :=
  ((UnaryFn.const 4).mul (originalDegree_unary ht)).add (UnaryFn.const 2)

theorem original_lowWord_FP {t : List Bool → Term} {k u : List Bool → ℕ}
    (ht : (fun c => (t c).toData.toBits) ∈ FP) (hk : UnaryFn k) (hu : UnaryFn u) :
    (fun c => lowWord (k c) (originalDegree t c) (u c) (t c)) ∈ FP :=
  lowTerm_FP ht hk (originalDegree_unary ht) hu (fun c => (t c).degreeBound_le_dataSize)

end LeanCanny.ETR.FixedLeadingTiltedSourceFP
