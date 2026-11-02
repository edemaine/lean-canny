/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalEndpointNative

/-! # The remaining native edge obligation for point connectivity

The total graph has native widths, fixed endpoint writers and native vertex
validation. A native cost bound for its actual frontier edges suffices for
the original point language, including rejection of all malformed queries.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalEndpointNative
open ETR Computation Turing.MultiTapeTM
open scoped Classical

noncomputable def query (c : List Bool) : PointQuery := ⟨description c,endpoint 3 c,endpoint 4 c⟩
noncomputable def edge (c : List Bool) := CanonicalEndpointFrontier.edge (query c)

@[simp] theorem query_point (q : PointQuery) : query (Input.point q).encode=q := by
  simp only [query,description_point,endpoint_source,endpoint_target]

theorem baseWidth_point (q : PointQuery) :
    baseWidth (Input.point q).encode=CanonicalAuxiliaryBitFrontier.width q.space := by
  unfold baseWidth
  rw [wholeFrame_point]

theorem point_mem_PSPACE
    (he : ComputableTidilyInPolySpace
      (fun p : List Bool×List Bool×List Bool=>edge p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBool) : pointLanguage∈PSPACE := by
  have HR:=ImplicitGraph.reachable_computable he valid_computable width_unary
    (.of_polyTime source_computable) (.of_polyTime target_computable)
    (fun c=>BitEndpointFrontier.source_length (baseWidth c))
    (fun c=>BitEndpointFrontier.target_length (baseWidth c))
  have HP:=ComputableTidilyInPolySpace.of_polyTime Input.isPoint_fppred.computable
  have HF : ComputableTidilyInPolySpace (fun _ : List Bool=>false) encBits encBool:=.of_polyTime (.const false)
  apply NativeSpace.of_computable (HP.ite HR HF)
  intro c
  by_cases hp : Input.IsPoint c
  · obtain ⟨q,rfl⟩:=(Input.isPoint_iff c).mp hp
    simp only [hp,decide_true,ite_true,decide_eq_true_eq]
    by_cases hd : q.space.WellFormed
    · have HV : valid (Input.point q).encode=CanonicalEndpointFrontier.valid q :=
        funext (valid_point q hd)
      rw [edge,query_point,HV,width_point,baseWidth_point]
      exact CanonicalEndpointFrontier.point_language_iff q hd
    · have HB : (Input.point q).encode∉pointLanguage := by
        rw [point_encode_mem_iff]
        rintro ⟨h,_,_,_,_,_⟩
        exact hd h
      have HN : ¬ImplicitGraph.Reachable (edge (Input.point q).encode) (valid (Input.point q).encode)
          (width (Input.point q).encode)
          (BitEndpointFrontier.source (baseWidth (Input.point q).encode))
          (BitEndpointFrontier.target (baseWidth (Input.point q).encode)) := by
        intro h
        have HS:=h.1
        simp only [valid,BitEndpointFrontier.valid,BitEndpointFrontier.not_isOriginal_source,
          ite_false,ite_true,endpointValid,description_point,hd,false_and,decide_false,Bool.false_eq_true] at HS
      exact iff_of_false HB HN
  · have HB : c∉pointLanguage := by
      rintro ⟨q,rfl,_⟩
      exact hp ((Input.isPoint_iff _).mpr ⟨q,rfl⟩)
    simp only [hp,decide_false,ite_false,Bool.false_eq_true]
    exact iff_of_false HB id

end LeanCanny.Connectivity.CanonicalEndpointNative
