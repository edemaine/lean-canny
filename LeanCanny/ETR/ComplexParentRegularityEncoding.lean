/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexParentRegularityCircuit

/-! # Native shared parent regularity guard generation -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.ParentRegularity
open LeanCanny.Encoding.Brackets

private theorem copyBase_unary {base : List Bool → ℕ} (hb : UnaryFn base) :
    UnaryFn (fun c => copyBase (base c)) := hb.add (UnaryFn.const 2)

private theorem inverseBase_unary {base start n : List Bool → ℕ} {ops : List Bool → List Operation}
    (hb : UnaryFn base) (hs : UnaryFn start) (hn : UnaryFn n) (hl : UnaryFn (fun c => (ops c).length)) :
    UnaryFn (fun c => inverseBase (base c) (start c) (n c) (ops c)) :=
  (copyBase_unary hb).add (hn.mul ((UnaryFn.const 16).mul (hs.add hl)))

theorem program_encode_mem_FP {base start inverse n : List Bool → ℕ}
    {ops : List Bool → List Operation} {outputs : List Bool → ℕ → ℕ}
    (hb : UnaryFn base) (hs : UnaryFn start) (hu : UnaryFn inverse) (hn : UnaryFn n)
    (hl : UnaryFn (fun c => (ops c).length))
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP)
    (he : UnaryFn (fun q => outputs (pairFst q) (pairSnd q).length)) :
    (fun c => encode (gates (base c) (start c) (inverse c) (n c) (ops c) (outputs c))) ∈ FP := by
  have hcopy := copyBase_unary hb
  have hiBase := inverseBase_unary hb hs hn hl
  have hentry := GradientFamily.derivativeWire_unary (hcopy.comp pairFst_mem_FP |>.comp pairFst_mem_FP)
    (hs.comp pairFst_mem_FP |>.comp pairFst_mem_FP) (UnaryFn.length pairSnd_mem_FP)
    (he.comp pairFst_mem_FP) (hl.comp pairFst_mem_FP |>.comp pairFst_mem_FP)
  have hGrad := GradientFamily.encode_mem_FP hb hcopy hs (UnaryFn.const 0) hn hl hg
  have hInv := RightInverse.program_encode_mem_FP (entry := fun c => entry (base c) (start c) (ops c) (outputs c))
    hb (hb.add (UnaryFn.const 1)) hiBase hu hn (hn.mul hn) hentry
  have hz := constantGateBits_mem_FP hb (constFn_mem_FP (Term.const 0).toData.toBits)
  have ho := constantGateBits_mem_FP (hb.add (UnaryFn.const 1)) (constFn_mem_FP (Term.const 1).toData.toBits)
  have H := mem_FP_comp (appendFn_mem_FP hz (appendFn_mem_FP ho
    (appendFn_mem_FP (mem_FP_comp hGrad contents_mem_FP) (mem_FP_comp hInv contents_mem_FP)))) wrap_mem_FP
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply, contents_encode, constantGateBits_encode]
  rw [encode_eq_wrap, gates_eq]
  simp only [forest_cons, forest_append]

theorem length_unary {base start inverse n : List Bool → ℕ} {ops : List Bool → List Operation}
    (hs : UnaryFn start) (hn : UnaryFn n) (hl : UnaryFn (fun c => (ops c).length))
    (outputs : List Bool → ℕ → ℕ) :
    UnaryFn (fun c => (program (base c) (start c) (inverse c) (n c) (ops c) (outputs c)).length) :=
  (((UnaryFn.const 2).add (hn.mul ((UnaryFn.const 16).mul (hs.add hl)))).add
    ((hn.mul hn).mul (((UnaryFn.const 4).mul hn).add (UnaryFn.const 3)))).of_eq
      (fun _ => (program_length ..).symm)

theorem guardOutput_unary {base start n : List Bool → ℕ} {ops : List Bool → List Operation}
    {outputs : List Bool → ℕ → ℕ}
    (hb : UnaryFn base) (hs : UnaryFn start) (hn : UnaryFn n) (hl : UnaryFn (fun c => (ops c).length))
    (he : UnaryFn (fun q => outputs (pairFst q) (pairSnd q).length)) :
    UnaryFn (fun q => guardOutput (base (pairFst q)) (start (pairFst q)) (n (pairFst q)) (ops (pairFst q)) (outputs (pairFst q)) (pairSnd q).length) := by
  have hq := UnaryFn.length pairSnd_mem_FP
  have hn' := hn.comp pairFst_mem_FP
  have hroot := GradientFamily.valueWire_unary ((copyBase_unary hb).comp pairFst_mem_FP)
    (hs.comp pairFst_mem_FP) (UnaryFn.const 0) he (hl.comp pairFst_mem_FP)
  have hInv := RightInverse.output_unary ((inverseBase_unary hb hs hn hl).comp pairFst_mem_FP) hn' (hq.sub hn')
  exact (UnaryFn.ite (FPPred.lt hq hn') hroot hInv).of_eq (fun _ => rfl)

end LeanCanny.ETR.ComplexCircuit.ParentRegularity
