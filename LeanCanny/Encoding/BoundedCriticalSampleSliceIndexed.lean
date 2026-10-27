/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceIndexed
public import LeanCanny.Encoding.BoundedCriticalSampleSliceDegree

/-! # Native indexed factors at actual sample descriptors

An attached index selects a factor without changing the parent sample or
original query record. Native specialized zero tests include degree drops.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleSliceIndexed
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice
open scoped Classical

def sourceContext (v : List Bool) : List Bool := pair (dropRecord v) (pairSnd (pairSnd v))
theorem sourceContext_FP : sourceContext ∈ FP :=
  mem_FP_pair dropRecord_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

def family (Q : BivariateQueryProductBits.Family) : Family :=
  (BoundedAlgebraicSliceIndexed.family Q).comp sourceContext
def access {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) : (family Q).Access :=
  (BoundedAlgebraicSliceIndexed.access A).comp sourceContext sourceContext_FP

noncomputable def value (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ) : ℝ[X] :=
  specialized P (family Q) (attach u (BinaryNatCode.encode i))

theorem value_valid (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ) (hu : u ∈ valid P) :
    value P Q u i = (Q.polynomial (context u) i).map (ParameterTarski.evalHom (point P (pairFst u))) := by
  have hv := (attach_valid P u (BinaryNatCode.encode i)).mpr hu
  rw [value, specialized, ite_eq_left hv]
  simp only [Family.slice, family, Family.comp, BoundedAlgebraicSliceIndexed.family, sourceContext,
    context, attach, dropRecord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem value_invalid (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ) (hu : u ∉ valid P) :
    value P Q u i = 0 := by
  have hv := mt (attach_valid P u (BinaryNatCode.encode i)).mp hu
  rw [value, specialized, ite_eq_right hv]

def query (q : List Bool) : List Bool := attach (pairFst q) (BinaryNat.normalize (pairSnd q))
theorem query_FP : query ∈ FP := by polytime [query, attach]

noncomputable def nonzeroLanguage (P : Readers) (Q : BivariateQueryProductBits.Family) : Language :=
  query ⁻¹' BoundedCriticalSampleSlice.nonzeroLanguage P (family Q)

theorem nonzero_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (q : List Bool) :
    q ∈ nonzeroLanguage P Q ↔ value P Q (pairFst q) (Nat.fromBitsLE (pairSnd q)) ≠ 0 := by
  simp only [nonzeroLanguage, Set.mem_preimage, BoundedCriticalSampleSlice.nonzeroLanguage,
    Set.mem_ofPred_eq, query, BinaryNat.normalize_eq_bits, value, BinaryNatCode.encode]

theorem nonzero_decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (nonzeroLanguage P Q) :=
  (BoundedCriticalSampleSlice.nonzero_decider h (access A) ha).precompose query query_FP

end LeanCanny.Encoding.BoundedCriticalSampleSliceIndexed
