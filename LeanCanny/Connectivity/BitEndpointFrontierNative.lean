/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.BitEndpointFrontier

/-! # Native endpoint word writers and augmented vertex validation -/
@[expose] public section
namespace LeanCanny.Connectivity.BitEndpointFrontier
open Computation Turing.MultiTapeTM
open scoped Classical

theorem source_computable {α : Type} {enc : α↪List Bool} {w : α→ℕ}
    (hw : ComputableTidilyInPolyTime w enc encUnary) :
    ComputableTidilyInPolyTime (fun a=>source (w a)) enc encBits :=
  .bitsCons (.const false) (.bitsCons (.const true) ((ComputableTidilyInPolyTime.bitsReplicate false).comp hw))

theorem target_computable {α : Type} {enc : α↪List Bool} {w : α→ℕ}
    (hw : ComputableTidilyInPolyTime w enc encUnary) :
    ComputableTidilyInPolyTime (fun a=>target (w a)) enc encBits :=
  .bitsCons (.const true) (.bitsCons (.const false) ((ComputableTidilyInPolyTime.bitsReplicate false).comp hw))

theorem valid_computable {α : Type} {enc : α↪List Bool} {w : α→ℕ}
    {v : α→List Bool→Bool} {s t : α→Bool}
    (hw : ComputableTidilyInPolyTime w enc encUnary)
    (hv : ComputableInPolySpace (fun p : α×List Bool=>v p.1 p.2) (encPair enc encBits) encBool)
    (hs : ComputableInPolySpace s enc encBool)
    (ht : ComputableInPolySpace t enc encBool) :
    ComputableInPolySpace
      (fun p : α×List Bool=>valid (w p.1) (v p.1) (s p.1) (t p.1) p.2) (encPair enc encBits) encBool := by
  have HA:=ComputableTidilyInPolyTime.fst enc encBits
  have HU:=ComputableTidilyInPolyTime.snd enc encBits
  have HD:=HU.bitsDropWithInput (.const 2)
  have HP:=HU.bitsTakeWithInput (.const 2)
  have HL:=ComputableTidilyInPolyTime.decide_eq' (ComputableTidilyInPolyTime.length_bits.comp HD) (hw.comp HA)
  have HE:=ComputableTidilyInPolyTime.decide_eq' HP (.const [false,false])
  have HF : ComputableInPolySpace (fun _ : α×List Bool=>false) (encPair enc encBits) encBool:=.of_tidyPolyTime (.const false)
  have HO : ComputableInPolySpace
      (fun p : α×List Bool=>decide (IsOriginal (w p.1) p.2)) (encPair enc encBits) encBool := by
    apply ((ComputableInPolySpace.of_tidyPolyTime HL).ite (.of_tidyPolyTime HE) HF).congr
    intro p
    by_cases h : (p.2.drop 2).length=w p.1 <;> simp [IsOriginal,h]
  have HS:=ComputableTidilyInPolyTime.decide_eq' HU ((source_computable hw).comp HA)
  have HT:=ComputableTidilyInPolyTime.decide_eq' HU ((target_computable hw).comp HA)
  have HV:=hv.comp (.of_tidyPolyTime (HA.prod HD))
  apply (HO.ite HV ((ComputableInPolySpace.of_tidyPolyTime HS).ite (hs.comp (.of_tidyPolyTime HA))
    ((ComputableInPolySpace.of_tidyPolyTime HT).ite (ht.comp (.of_tidyPolyTime HA)) HF))).congr
  intro p
  simp only [valid,decide_eq_true_eq,Function.comp_apply]

end LeanCanny.Connectivity.BitEndpointFrontier
