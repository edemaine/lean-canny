/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleIndexedSign
public import LeanCanny.Encoding.BoundedAlgebraicSliceReindex

/-! # Algebraic slices based at actual critical samples

An input is `pair (pair source descriptor) record`. The bivariate family
receives `pair source record`; the sample descriptor and its selected frame
remain fixed. Invalid descriptors denote the zero polynomial. This includes
degree drops and identically zero specializations.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleSlice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Brackets
open BoundedAlgebraicSlice (Family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleIndexedSign.value
  BoundedCriticalSampleIndexedSign.probeContext BoundedCriticalSampleIndexedSign.baseContext

def context (u : List Bool) : List Bool := pair (pairFst (pairFst u)) (pairSnd u)
theorem context_FP : context ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

noncomputable def valid (P : Readers) : Language := {u | pairFst u ∈ BoundedCriticalSampleDescriptors.language P}
theorem valid_decider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (valid P) :=
  (BoundedCriticalSampleDescriptors.decider h ha).precompose pairFst pairFst_mem_FP

noncomputable def point (P : Readers) (q : List Bool) : ℝ :=
  if hq : q ∈ BoundedCriticalSampleDescriptors.language P then
    (BoundedCriticalSampleLabels.parameter P (pairFst q) (Classical.choose hq)).val else 0

theorem point_at (P : Readers) (q : List Bool) (x : BoundedFullCriticalSamples.Samples P (pairFst q))
    (hx : BoundedCriticalSampleHashChoice.descriptor P (pairFst q) x = pairSnd q) :
    point P q = (BoundedCriticalSampleLabels.parameter P (pairFst q) x).val := by
  have hq : q ∈ BoundedCriticalSampleDescriptors.language P := ⟨x, hx⟩
  rw [point, dite_eq_left hq]
  have he : Classical.choose hq = x := BoundedCriticalSampleHashChoice.descriptor_injective P (pairFst q)
    ((Classical.choose_spec hq).trans hx.symm)
  rw [he]

theorem point_sample (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    point P (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) =
      (BoundedCriticalSampleLabels.parameter P c x).val := by
  have H := point_at P (pair c (BoundedCriticalSampleHashChoice.descriptor P c x))
  rw [pairFst_pair, pairSnd_pair] at H
  exact H x rfl

noncomputable def specialized (P : Readers) (F : Family) (u : List Bool) : ℝ[X] :=
  if u ∈ valid P then F.slice (context u) (point P (pairFst u)) else 0

def reindexQuery (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (f (RationalSubstitution.IntegerBits.context q))
    (RationalSubstitution.IntegerBits.selectedDegree q)) (pairSnd q)
theorem reindexQuery_FP {f : List Bool → List Bool} (hf : f ∈ FP) : reindexQuery f ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP hf)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

def reindexTest (T : BoundedProjectionTestMoments.Test) (f : List Bool → List Bool) :
    BoundedCriticalSampleTestMoments.Test where
  polynomial := T.polynomial ∘ f
  degree := T.degree ∘ f
  mass := T.mass ∘ f
  polynomial_degree u := T.polynomial_degree (f u)
  polynomial_mass u := T.polynomial_mass (f u)

def reindexAccess {T : BoundedProjectionTestMoments.Test} (A : T.Access)
    (f : List Bool → List Bool) (hf : f ∈ FP) : (reindexTest T f).Access where
  degree_binary := A.degree_binary.comp hf
  mass_binary := A.mass_binary.comp hf
  coefficient := A.coefficient ∘ reindexQuery f
  evaluator := A.evaluator.precompose (reindexQuery f) (reindexQuery_FP hf)
  coefficient_eq u k m hm := by
    simpa only [Function.comp_apply, reindexQuery, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair, reindexTest]
      using A.coefficient_eq (f u) k m hm

def scalarContext (u : List Bool) : List Bool :=
  pair (pair (pairFst u) (pairFst (pairSnd u))) (pairSnd (pairSnd u))
theorem scalarContext_FP : scalarContext ∈ FP :=
  mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def scalar (F : Family) : BoundedCriticalSampleTestMoments.Test :=
  reindexTest (BoundedAlgebraicSlice.scalar F) scalarContext
noncomputable def scalarAccess {F : Family} (A : F.Access) : (scalar F).Access :=
  reindexAccess (BoundedAlgebraicSlice.scalarAccess A) scalarContext scalarContext_FP

def coefficientQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst q))) (pairSnd (pairFst (pairFst q))))
    (pair (pairSnd (pairFst q)) (pairSnd q))
theorem coefficientQuery_FP : coefficientQuery ∈ FP := by polytime [coefficientQuery]

noncomputable def rawSign (P : Readers) (F : Family) : List Bool → List Bool :=
  BoundedCriticalSampleIndexedSign.value P (scalar F) ∘ coefficientQuery

theorem rawSign_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (rawSign P F) :=
  (BoundedCriticalSampleIndexedSign.evaluator h (scalarAccess A) ha).precompose coefficientQuery coefficientQuery_FP

theorem rawSign_at (P : Readers) (F : Family) (u : List Bool) (hu : u ∈ valid P) (k : ℕ) :
    rawSign P F (pair u (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign ((F.slice (context u) (point P (pairFst u))).coeff k)) := by
  let x := Classical.choose hu
  have hx : BoundedCriticalSampleHashChoice.descriptor P (pairFst (pairFst u)) x = pairSnd (pairFst u) := Classical.choose_spec hu
  have H := BoundedCriticalSampleIndexedSign.value_sample P (scalar F) (pairFst (pairFst u))
    (pair (pairSnd u) (BinaryNatCode.encode k)) x
  rw [hx] at H
  have hp := point_at P (pairFst u) x hx
  simpa only [rawSign, Function.comp_apply, coefficientQuery, pairFst_pair, pairSnd_pair,
    BoundedCriticalSampleTestMoments.sign, scalar, reindexTest, scalarContext, BoundedAlgebraicSlice.scalar,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Family.slice, Polynomial.coeff_map, ParameterTarski.evalHom,
    Polynomial.coe_eval₂RingHom, Polynomial.eval_map, context, hp] using H

noncomputable def coefficientSign (P : Readers) (F : Family) (q : List Bool) : List Bool :=
  if pairFst q ∈ valid P then rawSign P F q else []
theorem coefficientSign_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficientSign P F) :=
  SpaceFunction.branchDecider ((valid_decider h ha).precompose pairFst pairFst_mem_FP)
    (rawSign_evaluator h A ha) (SpaceFunction.ofFP _ (constFn_mem_FP []))

theorem coefficientSign_packet (P : Readers) (F : Family) (u : List Bool) (k : ℕ) :
    coefficientSign P F (pair u (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign ((specialized P F u).coeff k)) := by
  by_cases hu : u ∈ valid P
  · rw [coefficientSign, pairFst_pair, ite_eq_left hu, rawSign_at P F u hu k, specialized, ite_eq_left hu]
  · simp only [coefficientSign, pairFst_pair, hu, ite_false, specialized, coeff_zero, sign_zero, InfinitesimalSign.encode]

theorem specialized_degree (P : Readers) (F : Family) (u : List Bool) :
    (specialized P F u).natDegree ≤ F.degree (context u) := by
  unfold specialized Family.slice
  split_ifs
  · exact Polynomial.natDegree_map_le.trans (F.polynomial_degree _)
  · simp only [natDegree_zero, Nat.zero_le]

theorem specialized_sample (P : Readers) (F : Family) (c d : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    specialized P F (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) =
      F.slice (pair c d) (BoundedCriticalSampleLabels.parameter P c x).val := by
  have hv : pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d ∈ valid P := by
    change pairFst _ ∈ BoundedCriticalSampleDescriptors.language P
    rw [pairFst_pair]
    change ∃ y : BoundedFullCriticalSamples.Samples P (pairFst (pair c (BoundedCriticalSampleHashChoice.descriptor P c x))),
      BoundedCriticalSampleHashChoice.descriptor P _ y = pairSnd (pair c (BoundedCriticalSampleHashChoice.descriptor P c x))
    rw [pairFst_pair, pairSnd_pair]
    exact ⟨x, rfl⟩
  rw [specialized, ite_eq_left hv]
  simp only [context, pairFst_pair, pairSnd_pair, point_sample]

def attach (u r : List Bool) : List Bool := pair (pairFst u) (pair (pairSnd u) r)
def dropRecord (v : List Bool) : List Bool := pair (pairFst v) (pairFst (pairSnd v))
theorem dropRecord_FP : dropRecord ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem attach_valid (P : Readers) (u r : List Bool) : attach u r ∈ valid P ↔ u ∈ valid P := by
  simp only [valid, Set.mem_ofPred_eq, attach, pairFst_pair]
theorem specialized_attach (P : Readers) (F : Family) (u r : List Bool) :
    specialized P (F.comp dropRecord) (attach u r) = specialized P F u := by
  simp only [specialized, valid, Set.mem_ofPred_eq, attach, context, pairFst_pair, pairSnd_pair, Family.slice,
    Family.comp, dropRecord]

end LeanCanny.Encoding.BoundedCriticalSampleSlice
