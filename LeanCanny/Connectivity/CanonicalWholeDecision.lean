/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalEndpointDecision

/-! # Whole-space connectivity uses the same remaining frontier-edge routine

The two added singleton pieces do not change connectivity of the covered
space. The total graph and its native vertex validator can therefore serve
both input tags. Only the actual edge routine is a computational premise.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalEndpointNative
open ETR Computation Turing.MultiTapeTM Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaView.formula Input.field Codec.unaryValue

@[simp] theorem description_whole (d : Description) : description (Input.whole d).encode=d := by
  simp only [description,Input.field_whole_dimension,Codec.unaryValue_toBits,
    Input.field_whole_space,FormulaView.formula_encode]

theorem wholeFrame_whole (d : Description) : Input.wholeFrame (Input.whole d).encode=CanonicalSignRefinement.original d := by
  simp only [Input.wholeFrame,Input.field_whole_dimension,Input.field_whole_space]
  simp [CanonicalSignRefinement.original,Input.encode,Input.toData,Formula.encode,
    Data.toBits_l,Encoding.Brackets.wrap,List.append_assoc]

theorem wellFormed_computable :
    ComputableTidilyInPolyTime (fun c=>decide (description c).WellFormed) encBits encBool := by
  have HF:=FormulaView.encoded_computable.comp (Input.field_mem_FP 2)
  have HA : ComputableTidilyInPolyTime (fun c=>(FormulaView.formula (Input.field 2 c)).arity) encBits encUnary := by
    apply (ComputableTidilyInPolyTime.comp FormulaArity.value_unary HF).of_enc_eq
    intro c
    exact congrArg encUnary (FormulaArity.value_encode _).symm
  apply (ComputableTidilyInPolyTime.unary_le' HA (Codec.unaryValue_unary.comp (Input.field_mem_FP 1))).of_enc_eq
  intro c
  exact congrArg encBool (decide_eq_decide.mpr Iff.rfl)

theorem connected_language_iff (d : Description) (hd : d.WellFormed) :
    (Input.whole d).encode∈connectedLanguage ↔
      ImplicitGraph.Connected (edge (Input.whole d).encode) (valid (Input.whole d).encode)
        (width (Input.whole d).encode) := by
  let c:=(Input.whole d).encode
  let q:=query c
  have HQ : q.space=d:=description_whole d
  have HD : q.space.WellFormed:=HQ ▸ hd
  have HO : Input.wholeFrame c=CanonicalSignRefinement.original q.space := by
    rw [HQ]
    exact wholeFrame_whole d
  have HW : width c=CanonicalEndpointFrontier.width q := by
    unfold width baseWidth
    rw [HO]
  have HV : valid c=CanonicalEndpointFrontier.valid q := by
    funext label
    unfold valid baseWidth endpointValid CanonicalEndpointFrontier.valid
    rw [HO]
    have HF : (description c).WellFormed:=HD
    simp only [HF,true_and]
    rfl
  have HS : c∈connectedLanguage ↔ IsPreconnected (univ : Set q.space.realization) := by
    rw [HQ]
    change (Input.whole d).encode∈connectedLanguage ↔ IsPreconnected (univ : Set d.realization)
    rw [whole_encode_mem_iff]
    change (d.WellFormed ∧ IsPreconnected d.realization)↔_
    rw [and_iff_right hd,isPreconnected_iff_preconnectedSpace,preconnectedSpace_iff_univ]
  change c∈connectedLanguage ↔ ImplicitGraph.Connected (edge c) (valid c) (width c)
  rw [HV,HW]
  exact HS.trans (CanonicalEndpointFrontier.cover q HD).isPreconnected_iff_connected

/-- A total whole-space decider only needs a space-bounded test that is correct
on well-formed canonical inputs. Tag and dimension validation are shared by
all frontier implementations. -/
theorem connected_mem_PSPACE_of_test {test : List Bool → Bool}
    (htest : ComputableTidilyInPolySpace test encBits encBool)
    (hcorrect : ∀ d : Description, d.WellFormed →
      ((Input.whole d).encode ∈ connectedLanguage ↔ test (Input.whole d).encode = true)) :
    connectedLanguage ∈ PSPACE := by
  have HP := ComputableTidilyInPolySpace.of_polyTime Input.isWhole_fppred.computable
  have HW := ComputableTidilyInPolySpace.of_polyTime wellFormed_computable
  have HF : ComputableTidilyInPolySpace (fun _ : List Bool => false) encBits encBool :=
    .of_polyTime (.const false)
  apply NativeSpace.of_computable (HP.ite (HW.ite htest HF) HF)
  intro c
  by_cases hp : Input.IsWhole c
  · obtain ⟨d, rfl⟩ := (Input.isWhole_iff c).mp hp
    simp only [hp, decide_true, ite_true, description_whole]
    by_cases hd : d.WellFormed
    · simpa only [hd, decide_true, ite_true] using hcorrect d hd
    · have HB : (Input.whole d).encode ∉ connectedLanguage := by
        rw [whole_encode_mem_iff]
        exact fun h => hd h.1
      simp only [hd, decide_false, ite_false, Bool.false_eq_true]
      exact iff_of_false HB id
  · have HB : c ∉ connectedLanguage := by
      rintro ⟨d, rfl, _⟩
      exact hp ((Input.isWhole_iff _).mpr ⟨d, rfl⟩)
    simp only [hp, decide_false, ite_false, Bool.false_eq_true]
    exact iff_of_false HB id

theorem connected_mem_PSPACE
    (he : ComputableTidilyInPolySpace
      (fun p : List Bool×List Bool×List Bool=>edge p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBool) : connectedLanguage∈PSPACE := by
  apply connected_mem_PSPACE_of_test
    (ImplicitGraph.connected_computable he valid_computable width_unary)
  intro d hd
  simpa only [decide_eq_true_eq] using connected_language_iff d hd

end LeanCanny.Connectivity.CanonicalEndpointNative
