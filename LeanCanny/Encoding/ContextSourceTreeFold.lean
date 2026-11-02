/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ContextTreeFold
/-! # Captured-context tree passes over a separately read source -/
@[expose] public section
namespace LeanCanny.Encoding.DynamicTreeFold
open Turing.MultiTapeTM
open Brackets
variable {σ : Type*}

theorem sourceEncoded_mem_FP_context (source : List Bool → List Bool) (hs : source ∈ FP)
    (empty : List Bool → σ) (combine : List Bool → σ → σ → σ)
    (code : List Bool → σ → List Bool) (emptyBits combineBits : List Bool → List Bool)
    (hempty : emptyBits ∈ FP) (hcombine : combineBits ∈ FP)
    (hempty_eq : ∀ z, emptyBits z = code z (empty z))
    (hcombine_eq : ∀ z child parent,
      combineBits (pair z (pair (code z child) (code z parent))) = code z (combine z child parent))
    {bound : List Bool → ℕ} (hbound : PolyBounded List.length bound)
    (hle : ∀ z t, t <:+ source z →
      (encode (code z) (TreeFold.run (empty z) (combine z) t)).length ≤ bound z) :
    (fun z => encode (code z) (TreeFold.run (empty z) (combine z) (source z))) ∈ FP := by
  have hinit : (fun z => encode (code z) (some [empty z])) ∈ FP := by
    refine mem_FP_of_eq
      (mem_FP_comp (mem_FP_pair hempty (constFn_mem_FP [])) (cons_mem_FP true)) ?_
    intro z
    simp only [hempty_eq, encode, stackBits, Function.comp_apply]
  let step := fun z acc bit => update emptyBits combineBits bit (pair z acc)
  have hp : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (List Bool × List Bool) × Bool => pair p.1.1 p.1.2)
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
        Turing.MultiTapeTM.encBool) Turing.MultiTapeTM.encBits := by fun_prop
  have hstep : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (List Bool × List Bool) × Bool => step p.1.1 p.1.2 p.2)
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
        Turing.MultiTapeTM.encBool) Turing.MultiTapeTM.encBits := by
    have hb := Turing.MultiTapeTM.ComputableTidilyInPolyTime.snd
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
      Turing.MultiTapeTM.encBool
    exact (hb.cond ((update_mem_FP hempty hcombine true).comp hp)
      ((update_mem_FP hempty hcombine false).comp hp)).of_enc_eq
        fun p => by cases p.2 <;> rfl
  refine foldrEncodedWith_spec
    (fun state : List Bool × Option (List σ) => encode (code state.1) state.2) (step := step)
    (g := fun z t => (z,TreeFold.run (empty z) (combine z) t))
    id_mem_FP hs hinit hstep ?_ hbound hle
  intro z t bit
  exact update_encode_context empty combine code emptyBits combineBits hempty_eq hcombine_eq z bit
    (TreeFold.run (empty z) (combine z) t)

end LeanCanny.Encoding.DynamicTreeFold
