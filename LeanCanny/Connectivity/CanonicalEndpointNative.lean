/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalEndpointFrontier

/-! # Native validation of the actual fixed endpoint graph labels

All routines are total on raw input words. The two endpoint verdicts include
singleton validation, membership in the original realization and source
well-formedness. Only frontier edge costs remain separate.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalEndpointNative
open ETR Computation Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def description (c : List Bool) : Description :=
  ⟨Codec.unaryValue (Input.field 1 c),FormulaView.formula (Input.field 2 c)⟩
noncomputable def endpoint (k : ℕ) (c : List Bool) := FormulaView.formula (Input.field k c)
noncomputable def endpointValid (k : ℕ) (c : List Bool) : Bool :=
  decide ((description c).WellFormed ∧
    (EndpointSingletonPieces.piece (description c) (endpoint k c)).Nonempty)
noncomputable def baseWidth (c : List Bool) := CanonicalAuxiliaryCandidateCover.tagWidth (Input.wholeFrame c)
noncomputable def width (c : List Bool) := baseWidth c+2
noncomputable def valid (c label : List Bool) : Bool :=
  BitEndpointFrontier.valid (baseWidth c) (CanonicalAuxiliaryBitFrontier.valid (Input.wholeFrame c))
    (endpointValid 3 c) (endpointValid 4 c) label

theorem endpoint_computable (k : ℕ) :
    ComputableInPolySpace (endpointValid k) encBits encBool :=
  EndpointSingletonPieces.nonempty_computable
    (Codec.unaryValue_unary.comp (Input.field_mem_FP 1))
    (FormulaView.encoded_computable.comp (Input.field_mem_FP 2))
    (FormulaView.encoded_computable.comp (Input.field_mem_FP k))

theorem baseWidth_unary : UnaryFn baseWidth :=
  CanonicalAuxiliaryCandidateCover.tagWidth_unary.comp Input.wholeFrame_mem_FP
theorem width_unary : UnaryFn width := baseWidth_unary.add (UnaryFn.const 2)

theorem valid_computable :
    ComputableInPolySpace (fun p : List Bool×List Bool=>valid p.1 p.2)
      (encPair encBits encBits) encBool := by
  have HA:=ComputableTidilyInPolyTime.fst encBits encBits
  have HV:=CanonicalAuxiliaryBitFrontier.vertex_computable.comp
    (.of_tidyPolyTime ((Input.wholeFrame_mem_FP.comp HA).prod (ComputableTidilyInPolyTime.snd encBits encBits)))
  exact BitEndpointFrontier.valid_computable (v:=fun c u=>CanonicalAuxiliaryBitFrontier.valid (Input.wholeFrame c) u)
    baseWidth_unary HV (endpoint_computable 3) (endpoint_computable 4)

@[simp] theorem description_point (q : PointQuery) : description (Input.point q).encode=q.space := by
  simp only [description,Input.field_point_dimension,Codec.unaryValue_toBits,
    Input.field_point_space,FormulaView.formula_encode]

@[simp] theorem endpoint_source (q : PointQuery) : endpoint 3 (Input.point q).encode=q.source := by
  simp only [endpoint,Input.field_point_source,FormulaView.formula_encode]
@[simp] theorem endpoint_target (q : PointQuery) : endpoint 4 (Input.point q).encode=q.target := by
  simp only [endpoint,Input.field_point_target,FormulaView.formula_encode]

theorem wholeFrame_point (q : PointQuery) : Input.wholeFrame (Input.point q).encode=CanonicalSignRefinement.original q.space := by
  simp only [Input.wholeFrame,Input.field_point_dimension,Input.field_point_space]
  simp [CanonicalSignRefinement.original,Input.encode,Input.toData,Formula.encode,
    Data.toBits_l,Encoding.Brackets.wrap,List.append_assoc]

theorem width_point (q : PointQuery) : width (Input.point q).encode=CanonicalEndpointFrontier.width q := by
  unfold width baseWidth
  rw [wholeFrame_point]

theorem valid_point (q : PointQuery) (hd : q.space.WellFormed) (label : List Bool) :
    valid (Input.point q).encode label=CanonicalEndpointFrontier.valid q label := by
  unfold valid baseWidth endpointValid
  rw [wholeFrame_point,description_point,endpoint_source,endpoint_target]
  simp only [hd,true_and]
  rfl

theorem source_computable :
    ComputableTidilyInPolyTime (fun c=>BitEndpointFrontier.source (baseWidth c)) encBits encBits :=
  BitEndpointFrontier.source_computable baseWidth_unary
theorem target_computable :
    ComputableTidilyInPolyTime (fun c=>BitEndpointFrontier.target (baseWidth c)) encBits encBits :=
  BitEndpointFrontier.target_computable baseWidth_unary

end LeanCanny.Connectivity.CanonicalEndpointNative
