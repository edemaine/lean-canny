/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCriticalKernelPSPACE
public import LeanCanny.ETR.ComplexCriticalKernelRegular
public import LeanCanny.ETR.ComplexInterleavedPolynomial

/-! # Shared real critical-sample queries

The critical outputs of the existing acyclic derivative program define the
sample equations. Kernel normalization and kernel-zero constraints are absent.
The output models depend only on the original spatial inputs, allowing
independent existential formula witnesses through the interleaved query API.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CriticalSamples
open MvPolynomial CriticalKernel LeanCanny.Encoding.Brackets
open scoped Classical

def output (start m : ℕ) (ops : List Operation) (j : ℕ) : ℕ :=
  KernelRow.criticalWire (rowStart start m ops j) m

def outputs (start m : ℕ) (ops : List Operation) : List ℕ :=
  (List.range m).map (output start m ops)

def query (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) : List Gate :=
  StraightLine.gates (zeroWire start m) (program start m ops out v) ++
    (outputs start m ops).map Gate.zero

theorem next (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) :
    zeroWire start m + (program start m ops out v).length = rowStart start m ops m := by
  rw [program, List.length_append, ← Nat.add_assoc, prefix_next, rows_next]

theorem output_lt (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) (j : ℕ) (hj : j < m) :
    output start m ops j < zeroWire start m + (program start m ops out v).length := by
  rw [next]
  have h := Nat.mul_le_mul_right (rowStride m) (Nat.succ_le_of_lt hj)
  rw [Nat.succ_mul] at h
  unfold output KernelRow.criticalWire rowStart rowStride at *
  omega

theorem length_unary {start m : List Bool → ℕ} {ops : List Bool → List Operation}
    {out : List Bool → ℕ} {v : List Bool → ℕ → ℤ}
    (hs : UnaryFn start) (hm : UnaryFn m) (hlen : UnaryFn (fun c => (ops c).length)) :
    UnaryFn (fun c => (program (start c) (m c) (ops c) (out c) (v c)).length) := by
  have h := ((UnaryFn.const 1).add ((hm.mul hm).mul ((UnaryFn.const 16).mul (hs.add hlen)))).add
    (hm.mul (((UnaryFn.const 4).mul hm).add (UnaryFn.const 3)))
  exact h.of_eq (fun c => by
    simp only [program, List.length_append, prefixProgram, List.length_cons, List.length_nil,
      HessianFamily.program_length, rows_length, HessianFamily.stride, rowStride])

private theorem forest_flatMap {α : Type*} (xs : List α) (f : α → List Gate) :
    forest (xs.flatMap f) = xs.flatMap (fun a => forest (f a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.flatMap_cons, forest_append, ih, List.flatMap_cons]

theorem program_encode_mem_FP {start m out : List Bool → ℕ} {ops : List Bool → List Operation}
    {v : List Bool → ℕ → ℤ} (hs : UnaryFn start) (hm : UnaryFn m) (ho : UnaryFn out)
    (hlen : UnaryFn (fun c => (ops c).length))
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    (fun c => encode (StraightLine.gates (zeroWire (start c) (m c))
      (program (start c) (m c) (ops c) (out c) (v c)))) ∈ FP := by
  have hz := hs.add hm
  have hcopies := HessianFamily.encode_mem_FP hz (copyBase_unary hs hm) hs hm (hm.mul hm) hlen hg
  have hs' := hs.comp pairFst_mem_FP
  have hm' := hm.comp pairFst_mem_FP
  have hl' := hlen.comp pairFst_mem_FP
  have ho' := ho.comp pairFst_mem_FP
  have hj := UnaryFn.length pairSnd_mem_FP
  have hstrip := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
  have hv' : (fun p => (Term.const (-v (pairFst (pairFst p)) (pairSnd p).length)).toData.toBits) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hstrip hv) (fun p => by simp only [Function.comp_apply, pairFst_pair, pairSnd_pair])
  have hc := coefficient_literal_mem_FP (v := fun p => v (pairFst p)) hj hv'
  have hrow := row_encode_mem_FP (v := fun p => v (pairFst p)) hs' hm' hl' ho' hj hc
  have hrows := flatMap_range_mem_FP (mem_FP_comp hrow contents_mem_FP) hm.mem_FP
  have hzero := constantGateBits_mem_FP hz (constFn_mem_FP (Term.const 0).toData.toBits)
  have h := mem_FP_comp (appendFn_mem_FP (appendFn_mem_FP hzero (mem_FP_comp hcopies contents_mem_FP)) hrows) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, List.length_replicate, pairFst_pair, pairSnd_pair,
    contents_encode, constantGateBits_encode]
  rw [encode_eq_wrap, gates_eq]
  simp only [forest_append, forest_cons, forest_nil, forest_flatMap, List.append_nil]
  rfl

theorem query_encode_mem_FP {start m out : List Bool → ℕ} {ops : List Bool → List Operation}
    {v : List Bool → ℕ → ℤ} (hs : UnaryFn start) (hm : UnaryFn m) (ho : UnaryFn out)
    (hlen : UnaryFn (fun c => (ops c).length))
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    (fun c => encode (query (start c) (m c) (ops c) (out c) (v c))) ∈ FP := by
  have hp := program_encode_mem_FP hs hm ho hlen hg hv
  have hj := UnaryFn.length pairSnd_mem_FP
  have hrow := rowStart_unary (hs.comp pairFst_mem_FP) (hm.comp pairFst_mem_FP)
    (hlen.comp pairFst_mem_FP) hj
  have hz := zeroGateBits_mem_FP ((hrow.add ((UnaryFn.const 4).mul (hm.comp pairFst_mem_FP))).add (UnaryFn.const 2))
  have hzeros := flatMap_range_mem_FP hz hm.mem_FP
  have h := mem_FP_comp (appendFn_mem_FP (mem_FP_comp hp contents_mem_FP) hzeros) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate, contents_encode,
    zeroGateBits_encode]
  rw [encode_eq_wrap]
  simp only [query, outputs, forest, List.map_map, List.flatten_eq_flatMap,
    List.flatMap_append, List.flatMap_map, Function.comp_def, id_eq, output, KernelRow.criticalWire]

noncomputable def criticalPolynomial (p : MvPolynomial ℕ ℤ) (v : ℕ → ℤ) (j : ℕ) : MvPolynomial ℕ ℤ :=
  selectedPolynomial p j + C (coefficient v j) * pderiv 0 p

theorem symbolic_output (wire : ℕ → MvPolynomial ℕ ℤ) (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : out < start + ops.length) (j : ℕ) (hj : j < m) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (zeroWire start m) (program start m ops out v)
      (output start m ops j) = criticalPolynomial (wire out) v j := by
  let W := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (zeroWire start m) (program start m ops out v)
  have hW := wellFormed start m ops out v hw ho
  have hR := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) (zeroWire start m)
    (program start m ops out v) hW
  apply Differential.eq_of_eval_complex
  intro x
  let env : ℕ → ℂ := fun i => (W i).eval₂ (Int.castRingHom ℂ) x
  have hg := Differential.realizes_gates_eval _ _ _ hR x
  have hx : ∀ i < start, env i = x i := by
    intro i hi
    change (W i).eval₂ (Int.castRingHom ℂ) x = x i
    rw [show W i = X i from Differential.symbolicRun_preserves_before _ _ _ i (by unfold zeroWire; omega), eval₂_X]
  have hu : ∀ k < m, env (start + k) = x (start + k) := by
    intro k hk
    change (W (start + k)).eval₂ (Int.castRingHom ℂ) x = x (start + k)
    rw [show W (start + k) = X (start + k) from
      Differential.symbolicRun_preserves_before _ _ _ _ (by unfold zeroWire; omega), eval₂_X]
  have hs := (rows_sound wire start m ops out v hw hr hin ho x (fun k => x (start + k)) env hx hu hg j hj).1
  change (W (output start m ops j)).eval₂ (Int.castRingHom ℂ) x = _
  calc
    _ = criticalValue (wire out) v x j := hs
    _ = (criticalPolynomial (wire out) v j).eval₂ (Int.castRingHom ℂ) x := by
      simp only [criticalPolynomial, criticalValue, eval₂_add, eval₂_mul, eval₂_C]
      rfl

theorem finite_polynomial {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℤ) (v : ℕ → ℤ) (j : Fin (n + 1)) :
    criticalPolynomial (rename Fin.val p) v j.val = rename Fin.val (finiteRows p (fun i => v i.val) j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [criticalPolynomial, selectedPolynomial, Fin.val_zero, ite_true, coefficient,
      C_0, zero_mul, add_zero, finiteRows, Fin.cons_zero]
  · simp only [criticalPolynomial, selectedPolynomial, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
      coefficient, Nat.add_sub_cancel_right, finiteRows, Fin.cons_succ,
      map_sub, map_mul, rename_C]
    have hder (k : Fin (n + 1)) : pderiv k.val (rename Fin.val p) = rename Fin.val (pderiv k p) :=
      pderiv_rename Fin.val_injective k p
    have hi := hder i.succ
    have h0 := hder 0
    simp only [Fin.val_succ] at hi
    simp only [Fin.val_zero] at h0
    rw [hi, h0]
    simp only [map_neg, neg_mul, sub_eq_add_neg]

end LeanCanny.ETR.ComplexCircuit.CriticalSamples
