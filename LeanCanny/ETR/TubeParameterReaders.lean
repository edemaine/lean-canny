/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeParameterBounds

/-! # Reusing uniform parameter readers in extended matrix contexts

An FP context projection can discard the matrix row and selected coefficient
fields before calling the original parameter-coordinate routines. Coordinates
are uniform over spatial ranks, so those child requests use rank zero. The
resulting certificates include the original readers' space-bounded workspace.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeParameter
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Algebra.MatrixPower

attribute [local irreducible] parameterCount

def coordinateQuery (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pair (pair (f (pairFst (pairFst (pairFst p)))) []) (pairSnd (pairFst p))) (pairSnd p)

theorem coordinateQuery_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) : coordinateQuery f ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) hf
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair hc (constFn_mem_FP []))
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

theorem coordinateQuery_packet (f : List Bool → List Bool) (c : List Bool) (i k m : ℕ) :
    coordinateQuery f (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      pair (pair (pair (f (pairFst c)) []) (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1)) := by
  simp only [coordinateQuery, pairFst_pair, pairSnd_pair]

def coordinateContext (f : List Bool → List Bool) (c : List Bool) : List Bool := pair (f (pairFst c)) []

theorem coordinateContext_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) : coordinateContext f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) (constFn_mem_FP [])

noncomputable def CoordinateReaders.precomposeUniform {source : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ}
    (C : CoordinateReaders source (fun c => n (pairFst c)) (fun c => d (pairFst c)))
    (f : List Bool → List Bool) (hf : f ∈ FP) :
    CoordinateReaders (source ∘ f) (fun c => n (f (pairFst c))) (fun c => d (f (pairFst c))) := by
  exact (Algebra.RationalSubstitution.IntegerBits.CoordinateReaders.precompose
    (arity := fun c => parameterCount (source (pairFst c)))
    (n := fun c => n (pairFst c)) (d := fun c => d (pairFst c)) C
    (coordinateContext f) (coordinateContext_mem_FP hf)).congr
      (arity' := fun c => parameterCount (source (f (pairFst c))))
      (n' := fun c => n (f (pairFst c))) (d' := fun c => d (f (pairFst c)))
      (funext fun c => by simp only [Function.comp_apply, coordinateContext, pairFst_pair])
      (funext fun c => by simp only [coordinateContext, pairFst_pair])
      (funext fun c => by simp only [coordinateContext, pairFst_pair])

noncomputable def CoordinateBounds.precomposeUniform {source : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ}
    (B : CoordinateBounds source (fun c => n (pairFst c)) (fun c => d (pairFst c)))
    (f : List Bool → List Bool) (hf : f ∈ FP) :
    CoordinateBounds (source ∘ f) (fun c => n (f (pairFst c))) (fun c => d (f (pairFst c))) := by
  exact (Algebra.RationalSubstitution.IntegerBits.CoordinateBounds.precompose
    (arity := fun c => parameterCount (source (pairFst c)))
    (n := fun c => n (pairFst c)) (d := fun c => d (pairFst c)) B
    (coordinateContext f) (coordinateContext_mem_FP hf)).congr
      (arity' := fun c => parameterCount (source (f (pairFst c))))
      (n' := fun c => n (f (pairFst c))) (d' := fun c => d (f (pairFst c)))
      (funext fun c => by simp only [Function.comp_apply, coordinateContext, pairFst_pair])
      (funext fun c => by simp only [coordinateContext, pairFst_pair])
      (funext fun c => by simp only [coordinateContext, pairFst_pair])

end LeanCanny.ETR.TubeParameter
