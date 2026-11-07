/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatSyntax
public import LeanCanny.Computation.BoundedImagePSPACE
public import LeanCanny.ETR.CoercivePSPACE
public import LeanCanny.Connectivity.NativeConnectivityPSPACE
public import LeanCanny.Connectivity.InputFP

/-! # PSPACE bounds under flat library encodings

The forward translators are polynomial time. Their images have polynomially
bounded original witnesses, so bounded inverse search transfers the PSPACE
bounds and rejects every word outside the exact encoding images.
-/
@[expose] public section
set_option maxHeartbeats 400000
namespace LeanCanny.AbstractEncodingBridge
open Turing.MultiTapeTM Encoding Encoding.FlatSyntax Encoding.Brackets

def etrLanguage : Language :=
  {bits | ∃ p : ETR.Formula, bits = encoding (formulaTokens p) ∧ p.Satisfiable}
def spaceCode (n : ℕ) (p : ETR.Formula) : List Bool :=
  encPair encUnary encoding (n, formulaTokens p)
def pointCode (n : ℕ) (p a b : ETR.Formula) : List Bool :=
  encPair encUnary (encList encoding) (n, [formulaTokens p, formulaTokens a, formulaTokens b])
def connectedLanguage : Language :=
  {bits | ∃ d : Connectivity.Description, bits = spaceCode d.dimension d.formula ∧ d.Connected}
def pointLanguage : Language :=
  {bits | ∃ q : Connectivity.PointQuery,
    bits = pointCode q.space.dimension q.space.formula q.source q.target ∧ q.Reachable}

theorem etr_mem_PSPACE : etrLanguage ∈ PSPACE := by
  have H := Computation.bounded_image_mem_PSPACE (bound := fun z => 100 * z.length) ETR.etr_mem_PSPACE translate_FP
    ((UnaryFn.const 100).mul (UnaryFn.length id_mem_FP))
    (fun w hw => by
      obtain ⟨p, rfl, _⟩ := (ETR.mem_language_iff w).mp hw
      rw [translate_formula]
      simpa only [ETR.Formula.encode, Data.length_toBits] using (formula_lengths p).2)
  have HE : translate '' ETR.language = etrLanguage := by
    ext bits
    simp only [Set.mem_image, ETR.mem_language_iff, etrLanguage, Set.mem_ofPred_eq]
    aesop (add simp [translate_formula])
  exact HE ▸ H

def dimension (bits : List Bool) : ℕ := ETR.Codec.unaryValue (Connectivity.Input.field 1 bits)
def spaceBits (bits : List Bool) : List Bool := translate (Connectivity.Input.field 2 bits)
def sourceBits (bits : List Bool) : List Bool := translate (Connectivity.Input.field 3 bits)
def targetBits (bits : List Bool) : List Bool := translate (Connectivity.Input.field 4 bits)
def translateSpace (bits : List Bool) : List Bool := frame (encUnary (dimension bits)) ++ spaceBits bits
def translatePoint (bits : List Bool) : List Bool :=
  frame (encUnary (dimension bits)) ++ encList encBits [spaceBits bits, sourceBits bits, targetBits bits]

theorem dimension_unary : UnaryFn dimension := ETR.Codec.unaryValue_unary.comp (Connectivity.Input.field_mem_FP 1)
theorem spaceBits_FP : spaceBits ∈ FP := by
  have h := mem_FP_comp (Connectivity.Input.field_mem_FP 2) translate_FP
  exact mem_FP_of_eq (g := spaceBits) h (fun _ => by simp only [spaceBits, Function.comp_apply])
theorem sourceBits_FP : sourceBits ∈ FP := by
  have h := mem_FP_comp (Connectivity.Input.field_mem_FP 3) translate_FP
  exact mem_FP_of_eq (g := sourceBits) h (fun _ => by simp only [sourceBits, Function.comp_apply])
theorem targetBits_FP : targetBits ∈ FP := by
  have h := mem_FP_comp (Connectivity.Input.field_mem_FP 4) translate_FP
  exact mem_FP_of_eq (g := targetBits) h (fun _ => by simp only [targetBits, Function.comp_apply])
theorem translateSpace_FP : translateSpace ∈ FP := by
  have h := appendFn_mem_FP (mem_FP_comp dimension_unary.encoded frame_FP) spaceBits_FP
  exact mem_FP_of_eq (g := translateSpace) h (fun _ => by simp only [translateSpace, Function.comp_apply])
theorem translatePoint_FP : translatePoint ∈ FP := by
  have h := appendFn_mem_FP (mem_FP_comp dimension_unary.encoded frame_FP)
    (appendFn_mem_FP (mem_FP_comp spaceBits_FP frame_FP)
      (appendFn_mem_FP (mem_FP_comp sourceBits_FP frame_FP) (mem_FP_comp targetBits_FP frame_FP)))
  exact mem_FP_of_eq (g := translatePoint) h (fun _ => by
    simp only [Function.comp_apply, translatePoint, encList_cons, encList_nil, encBits_apply, List.append_nil])

@[simp] theorem translateSpace_whole (d : Connectivity.Description) :
    translateSpace (Connectivity.Input.whole d).encode = spaceCode d.dimension d.formula := by
  simp only [translateSpace, dimension, spaceBits, Connectivity.Input.field_whole_dimension,
    Connectivity.Input.field_whole_space, ETR.Codec.unaryValue_toBits, translate_formula]
  rfl
@[simp] theorem translatePoint_point (q : Connectivity.PointQuery) :
    translatePoint (Connectivity.Input.point q).encode =
      pointCode q.space.dimension q.space.formula q.source q.target := by
  simp only [translatePoint, dimension, spaceBits, sourceBits, targetBits,
    Connectivity.Input.field_point_dimension, Connectivity.Input.field_point_space,
    Connectivity.Input.field_point_source, Connectivity.Input.field_point_target,
    ETR.Codec.unaryValue_toBits, translate_formula]
  rfl

theorem space_balance (d : Connectivity.Description) :
    (Connectivity.Input.whole d).encode.length ≤ 100 * (spaceCode d.dimension d.formula).length := by
  have hp := (formula_lengths d.formula).2
  simp only [Connectivity.Input.encode, Connectivity.Input.toData, Data.length_toBits,
    Data.cons_size, Data.size_empty, ETR.Codec.unary_size]
  simp only [spaceCode, encPair, Function.Embedding.coeFn_mk, List.length_append,
    length_frame, encUnary_apply, List.length_replicate]
  omega

theorem point_balance (q : Connectivity.PointQuery) :
    (Connectivity.Input.point q).encode.length ≤
      100 * (pointCode q.space.dimension q.space.formula q.source q.target).length := by
  have hp := (formula_lengths q.space.formula).2
  have ha := (formula_lengths q.source).2
  have hb := (formula_lengths q.target).2
  simp only [Connectivity.Input.encode, Connectivity.Input.toData, Data.length_toBits,
    Data.cons_size, Data.size_empty, ETR.Codec.unary_size]
  simp only [pointCode, encPair, Function.Embedding.coeFn_mk, encList_cons, encList_nil,
    List.length_append, List.length_nil, length_frame, encUnary_apply, List.length_replicate]
  omega

theorem connected_mem_PSPACE : connectedLanguage ∈ PSPACE := by
  have H := Computation.bounded_image_mem_PSPACE (bound := fun z => 100 * z.length) Connectivity.connectedLanguage_mem_PSPACE translateSpace_FP
    ((UnaryFn.const 100).mul (UnaryFn.length id_mem_FP))
    (fun w hw => by
      obtain ⟨d, rfl, _⟩ := hw
      simpa only [translateSpace_whole] using space_balance d)
  have HE : translateSpace '' Connectivity.connectedLanguage = connectedLanguage := by
    ext bits
    simp only [Set.mem_image, connectedLanguage, Set.mem_ofPred_eq, Connectivity.connectedLanguage]
    aesop (add simp [translateSpace_whole])
  exact HE ▸ H

theorem point_mem_PSPACE : pointLanguage ∈ PSPACE := by
  have H := Computation.bounded_image_mem_PSPACE (bound := fun z => 100 * z.length) Connectivity.pointLanguage_mem_PSPACE translatePoint_FP
    ((UnaryFn.const 100).mul (UnaryFn.length id_mem_FP))
    (fun w hw => by
      obtain ⟨q, rfl, _⟩ := hw
      simpa only [translatePoint_point] using point_balance q)
  have HE : translatePoint '' Connectivity.pointLanguage = pointLanguage := by
    ext bits
    simp only [Set.mem_image, pointLanguage, Set.mem_ofPred_eq, Connectivity.pointLanguage]
    aesop (add simp [translatePoint_point])
  exact HE ▸ H

end LeanCanny.AbstractEncodingBridge
