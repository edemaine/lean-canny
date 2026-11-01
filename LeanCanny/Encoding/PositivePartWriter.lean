/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.PositivePartGraph
public import LeanCanny.ETR.TermArityFP
/-! # Native writer for the exact closed positive-part graph -/
@[expose] public section
namespace LeanCanny.Encoding.PositivePartWriter
open ETR LeanCanny.Geometry LeanCanny.Computation
open WeakCircleCanonicalFormula

theorem condition_FP {t : List Bool → Term} {i : List Bool → ℕ}
    (ht : (fun q => (t q).toData.toBits) ∈ FP) (hi : UnaryFn i) :
    (fun q => (PositivePartGraph.condition (t q) (i q)).encode) ∈ FP := by
  have HV := mem_FP_of_eq (Term.variableBits_mem_FP hi) (fun q => Term.variableBits_eq (i q))
  have HD : (fun q => (difference (.var (i q)) (t q)).toData.toBits) ∈ FP := by
    apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 HV (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) ht))
    intro q
    simp only [difference,Term.add_toBits,Term.mul_toBits]
  have HM : (fun q => (Term.mul (.var (i q)) (difference (.var (i q)) (t q))).toData.toBits) ∈ FP :=
    mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 HV HD) (fun q => (Term.mul_toBits _ _).symm)
  have H := Codec.taggedTwo_mem_FP 4 (Codec.taggedOne_mem_FP 3 (Codec.taggedOne_mem_FP 2 HV))
    (Codec.taggedTwo_mem_FP 4 (Codec.taggedOne_mem_FP 3 (Codec.taggedOne_mem_FP 2 HD)) (Codec.taggedOne_mem_FP 1 HM))
  apply mem_FP_of_eq H
  intro q
  simp only [PositivePartGraph.condition,nonnegative,Formula.encode,Formula.toData,Codec.taggedTwo_toBits,Codec.taggedOne_toBits]

end LeanCanny.Encoding.PositivePartWriter
