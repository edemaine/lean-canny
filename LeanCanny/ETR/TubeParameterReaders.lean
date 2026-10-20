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
resulting certificates include the original readers' suspended workspace.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeParameter
open Complexity LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Algebra.MatrixPower

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
    CoordinateReaders (source ∘ f) (fun c => n (f (pairFst c))) (fun c => d (f (pairFst c))) where
  numerator := C.numerator ∘ coordinateQuery f
  denominator := C.denominator ∘ coordinateQuery f
  numeratorEvaluator := C.numeratorEvaluator.precompose _ (coordinateQuery_mem_FP hf)
  denominatorEvaluator := C.denominatorEvaluator.precompose _ (coordinateQuery_mem_FP hf)
  numerator_eq c i hi k m hm := by
    change C.numerator (coordinateQuery f _) = _
    rw [coordinateQuery_packet]
    have h := C.numerator_eq (pair (f (pairFst c)) []) i (by simpa only [pairFst_pair, Function.comp_apply] using hi) k m hm
    simp only [pairFst_pair] at h
    exact h
  denominator_eq c i hi k m hm := by
    change C.denominator (coordinateQuery f _) = _
    rw [coordinateQuery_packet]
    have h := C.denominator_eq (pair (f (pairFst c)) []) i (by simpa only [pairFst_pair, Function.comp_apply] using hi) k m hm
    simp only [pairFst_pair] at h
    exact h

noncomputable def CoordinateBounds.precomposeUniform {source : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ}
    (B : CoordinateBounds source (fun c => n (pairFst c)) (fun c => d (pairFst c)))
    (f : List Bool → List Bool) (hf : f ∈ FP) :
    CoordinateBounds (source ∘ f) (fun c => n (f (pairFst c))) (fun c => d (f (pairFst c))) where
  degree := B.degree ∘ coordinateContext f
  bits := B.bits ∘ coordinateContext f
  degreeFP := mem_FP_comp (coordinateContext_mem_FP hf) B.degreeFP
  bitsFP := mem_FP_comp (coordinateContext_mem_FP hf) B.bitsFP
  numerator_degree c i hi := by
    have h := B.numerator_degree (coordinateContext f c) i (by
      simpa only [coordinateContext, pairFst_pair, Function.comp_apply] using hi)
    simp only [coordinateContext, pairFst_pair] at h
    exact h
  denominator_degree c i hi := by
    have h := B.denominator_degree (coordinateContext f c) i (by
      simpa only [coordinateContext, pairFst_pair, Function.comp_apply] using hi)
    simp only [coordinateContext, pairFst_pair] at h
    exact h
  numerator_coeff c i hi k := by
    have h := B.numerator_coeff (coordinateContext f c) i (by
      simpa only [coordinateContext, pairFst_pair, Function.comp_apply] using hi) k
    simp only [coordinateContext, pairFst_pair] at h
    exact h
  denominator_coeff c i hi k := by
    have h := B.denominator_coeff (coordinateContext f c) i (by
      simpa only [coordinateContext, pairFst_pair, Function.comp_apply] using hi) k
    simp only [coordinateContext, pairFst_pair] at h
    exact h

end LeanCanny.ETR.TubeParameter
