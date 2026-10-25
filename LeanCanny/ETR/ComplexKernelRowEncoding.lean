/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexKernelRow
public import LeanCanny.ETR.ComplexCircuitBuilders
public import LeanCanny.ETR.ComplexPowerSize
public import LeanCanny.Computation.PolyTimeRange

/-! # Native polynomial-time kernel-row generation

The two Hessian-entry references are generated for each unary column. Binary
direction coefficients are copied once into the shared row coefficient wire.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.KernelRow
open LeanCanny.Encoding.Brackets

theorem sumWire_unary {zWire start k : List Bool → ℕ} (hz : UnaryFn zWire)
    (hs : UnaryFn start) (hk : UnaryFn k) : UnaryFn (fun c => sumWire (zWire c) (start c) (k c)) :=
  (UnaryFn.ite (FPPred.eq hk (UnaryFn.const 0)) hz
    (hs.add ((UnaryFn.const 4).mul hk))).of_eq (fun _ => rfl)

theorem step_forest_mem_FP {zWire start kernelStart k first entry : List Bool → ℕ}
    (hz : UnaryFn zWire) (hs : UnaryFn start) (hu : UnaryFn kernelStart) (hk : UnaryFn k)
    (hf : UnaryFn first) (he : UnaryFn entry) :
    (fun c => forest (stepGates (zWire c) (start c) (kernelStart c)
      (fun _ => first c) (fun _ => entry c) (k c))) ∈ FP := by
  have hw := (hs.add (UnaryFn.const 1)).add ((UnaryFn.const 4).mul hk)
  have h1 := arithmeticGateBits_mem_FP 2 hw hs hf
  have h2 := arithmeticGateBits_mem_FP 1 (hw.add (UnaryFn.const 1)) he hw
  have h3 := arithmeticGateBits_mem_FP 2 (hw.add (UnaryFn.const 2))
    (hw.add (UnaryFn.const 1)) (hu.add hk)
  have h4 := arithmeticGateBits_mem_FP 1 (sumWire_unary hz hs (hk.add (UnaryFn.const 1)))
    (sumWire_unary hz hs hk) (hw.add (UnaryFn.const 2))
  apply mem_FP_of_eq (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP h1 h2) h3) h4)
  intro c
  simp only [mulGateBits_encode, addGateBits_encode, stepGates, forest_cons, forest_nil,
    List.append_nil, List.append_assoc, stepStart]

theorem prefix_forest_range (zWire start kernelStart : ℕ) (coefficient : ℤ) (first entry : ℕ → ℕ) (m : ℕ) :
    forest (prefixGates zWire start kernelStart coefficient first entry m) =
      (Gate.constant start coefficient).encode ++
        (List.range m).flatMap (fun k => forest (stepGates zWire start kernelStart first entry k)) := by
  induction m with
  | zero => simp only [prefixGates, prefixProgram, StraightLine.gates, Operation.gate,
      forest_cons, forest_nil, List.append_nil, List.range_zero, List.flatMap_nil]
  | succ m ih =>
    rw [prefixGates_succ, forest_append, ih, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem encode_mem_FP {zWire start kernelStart m value baseGradient : List Bool → ℕ}
    {coefficient : List Bool → ℤ} {first entry : List Bool → ℕ → ℕ}
    (hz : UnaryFn zWire) (hs : UnaryFn start) (hu : UnaryFn kernelStart) (hm : UnaryFn m)
    (hv : UnaryFn value) (hb : UnaryFn baseGradient)
    (hc : (fun c => (Term.const (coefficient c)).toData.toBits) ∈ FP)
    (hf : UnaryFn (fun q => first (pairFst q) (pairSnd q).length))
    (he : UnaryFn (fun q => entry (pairFst q) (pairSnd q).length)) :
    (fun c => encode (StraightLine.gates (start c)
      (program (zWire c) (start c) (kernelStart c) (m c) (value c) (baseGradient c)
        (coefficient c) (first c) (entry c)))) ∈ FP := by
  have hz' := UnaryFn.comp (f := zWire) (g := pairFst) hz pairFst_mem_FP
  have hs' := UnaryFn.comp (f := start) (g := pairFst) hs pairFst_mem_FP
  have hu' := UnaryFn.comp (f := kernelStart) (g := pairFst) hu pairFst_mem_FP
  have hk := UnaryFn.length pairSnd_mem_FP
  have hstep := step_forest_mem_FP hz' hs' hu' hk hf he
  have hsteps := flatMap_range_mem_FP hstep hm.mem_FP
  have hconstant := constantGateBits_mem_FP hs hc
  have hout := (hs.add ((UnaryFn.const 4).mul hm)).add (UnaryFn.const 1)
  have hmul := arithmeticGateBits_mem_FP 2 hout hs hb
  have hadd := arithmeticGateBits_mem_FP 1 (hout.add (UnaryFn.const 1)) hv hout
  have h := mem_FP_comp (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP hconstant hsteps) hmul) hadd) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, List.length_replicate, pairFst_pair, pairSnd_pair,
    constantGateBits_encode, mulGateBits_encode, addGateBits_encode]
  rw [encode_eq_wrap, gates_eq, forest_append, prefix_forest_range]
  simp only [forest_cons, forest_nil, List.append_nil, List.append_assoc, criticalWire]
  rfl

end LeanCanny.ETR.ComplexCircuit.KernelRow
