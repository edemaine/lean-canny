/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.BooleanCircuitValues
public import LeanCanny.Computation.SpaceFunctionBranch
/-! # Reading an arbitrary native wire from the polynomial-size circuit table -/
@[expose] public section
namespace LeanCanny.Computation.BooleanCircuitSpace

def indexed (F : Family) (atom : List Bool → Bool) (index : List Bool → ℕ) (c : List Bool) : Bool :=
  (values F atom c (F.count c))[index c]?.getD false

theorem indexed_evaluator (F : Family) (A : Access F) (atom : List Bool → Bool)
    (R : SpaceFunction (fun q => [atom q])) (index : List Bool → ℕ) (hi : UnaryFn index) :
    SpaceFunction (fun c => [indexed F atom index c]) := by
  have ET := (values_evaluator F A atom R).pairOutputs (SpaceFunction.ofFP _ id_mem_FP)
  have ER := getBit_mem_FP pairFst_mem_FP (hi.comp pairSnd_mem_FP)
  exact (ET.postcompose _ ER).congr (funext fun c => by
    simp only [Function.comp_apply,id_eq,indexed,pairFst_pair,pairSnd_pair])

theorem indexed_eq_wire (F : Family) (atom : List Bool → Bool) (index : List Bool → ℕ)
    (c : List Bool) (hi : index c < F.count c) :
    indexed F atom index c = wireValue F atom c (index c) :=
  read_wire F atom c (F.count c) (index c) hi


theorem wireValue_comp (F : Family) (f : List Bool → List Bool) (atom sourceAtom : List Bool → Bool)
    (c : List Bool) (i : ℕ)
    (h : ∀ k < i+1,atom (pair c (BinaryNatCode.encode k)) = sourceAtom (pair (f c) (BinaryNatCode.encode k))) :
    wireValue (F.comp f) atom c i = wireValue F sourceAtom (f c) i := by
  unfold wireValue
  rw [values_comp F f atom sourceAtom c (i+1) h]

end LeanCanny.Computation.BooleanCircuitSpace
