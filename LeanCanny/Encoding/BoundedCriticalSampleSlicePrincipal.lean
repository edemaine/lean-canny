/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleSliceDegree

/-! # Native principal signs at fixed actual-sample parameters

The two actual slice degrees are computed internally. Their metadata selects
a parameter-polynomial principal test without reindexing the sample source,
filter, basis, or descriptor.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleSlice.Principal
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Brackets
open BoundedAlgebraicSlice (Family)
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleIndexedSign.value degree point specialized

def testContext (u : List Bool) : List Bool :=
  pair (pair (pair (pair (pairFst u) (pairFst (pairSnd u))) [])
    (pairFst (pairSnd (pairSnd u)))) (pairSnd (pairSnd (pairSnd u)))
theorem testContext_FP : testContext ∈ FP := by polytime [testContext]

noncomputable def test (F G : Family) : BoundedCriticalSampleTestMoments.Test :=
  reindexTest (BoundedAlgebraicSlice.Principal.test F G) testContext
noncomputable def testAccess {F G : Family} (A : F.Access) (B : G.Access) : (test F G).Access :=
  reindexAccess (BoundedAlgebraicSlice.Principal.testAccess A B) testContext testContext_FP

theorem test_sign (F G : Family) (c r : List Bool) (d e j : ℕ) (theta : ℝ) :
    BoundedCriticalSampleTestMoments.sign (test F G)
      (pair c (pair r (pair (pair (BinaryNatCode.encode d) (BinaryNatCode.encode e)) (BinaryNatCode.encode j)))) theta =
        SignType.sign (PrincipalSubresultant.signedPsc (F.slice (pair c r) theta) (G.slice (pair c r) theta) d e j) := by
  simp only [BoundedCriticalSampleTestMoments.sign, test, reindexTest, Function.comp_apply, Polynomial.eval_map]
  change SignType.sign ((ParameterTarski.evalHom theta) ((BoundedAlgebraicSlice.Principal.test F G).polynomial _)) = _
  rw [BoundedAlgebraicSlice.Principal.test_eval]
  simp only [testContext, pairFst_pair, pairSnd_pair, BoundedAlgebraicSlice.Principal.origin,
    BoundedAlgebraicSlice.Principal.leftDegree, BoundedAlgebraicSlice.Principal.rightDegree,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def prepare (P : Readers) (F G : Family) (q : List Bool) : List Bool :=
  pair q (pair (BinaryNatCode.encode (degree P F (pairFst q))) (BinaryNatCode.encode (degree P G (pairFst q))))

theorem prepare_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (prepare P F G) :=
  (((degree_evaluator h A ha).precompose pairFst pairFst_mem_FP).pairOutputs
    ((degree_evaluator h B ha).precompose pairFst pairFst_mem_FP)).withInput

def finish (z : List Bool) : List Bool :=
  let q := pairFst z
  let u := pairFst q
  let p := pairFst u
  pair (pair (pairFst p) (pairSnd p)) (pair (pairSnd u) (pair (pairSnd z) (pairSnd q)))
theorem finish_FP : finish ∈ FP := by polytime [finish]

noncomputable def rawSign (P : Readers) (F G : Family) (q : List Bool) : List Bool :=
  BoundedCriticalSampleIndexedSign.value P (test F G) (finish (prepare P F G q))
theorem rawSign_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (rawSign P F G) :=
  ((prepare_evaluator h A B ha).postcompose finish finish_FP).chain
    (BoundedCriticalSampleIndexedSign.evaluator h (testAccess A B) ha)

theorem rawSign_packet (P : Readers) (F G : Family) (u : List Bool) (hu : u ∈ valid P) (j : ℕ) :
    rawSign P F G (pair u (BinaryNatCode.encode j)) = InfinitesimalSign.encode
      (SignType.sign (PrincipalSubresultant.signedPsc (specialized P F u) (specialized P G u)
        (degree P F u) (degree P G u) j)) := by
  let x := Classical.choose hu
  have hx : BoundedCriticalSampleHashChoice.descriptor P (pairFst (pairFst u)) x = pairSnd (pairFst u) := Classical.choose_spec hu
  have H := BoundedCriticalSampleIndexedSign.value_sample P (test F G) (pairFst (pairFst u))
    (pair (pairSnd u) (pair (pair (BinaryNatCode.encode (degree P F u)) (BinaryNatCode.encode (degree P G u)))
      (BinaryNatCode.encode j))) x
  rw [hx, test_sign] at H
  have hp := point_at P (pairFst u) x hx
  simpa only [rawSign, prepare, finish, pairFst_pair, pairSnd_pair, specialized, ite_eq_left hu, context, hp] using H

noncomputable def value (P : Readers) (F G : Family) (q : List Bool) : List Bool :=
  if pairFst q ∈ valid P then rawSign P F G q else []
theorem evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F G) :=
  SpaceFunction.branchDecider ((valid_decider h ha).precompose pairFst pairFst_mem_FP)
    (rawSign_evaluator h A B ha) (SpaceFunction.ofFP _ (constFn_mem_FP []))
theorem value_packet (P : Readers) (F G : Family) (u : List Bool) (hu : u ∈ valid P) (j : ℕ) :
    value P F G (pair u (BinaryNatCode.encode j)) = InfinitesimalSign.encode
      (SignType.sign (PrincipalSubresultant.signedPsc (specialized P F u) (specialized P G u)
        (degree P F u) (degree P G u) j)) := by
  rw [value, pairFst_pair, ite_eq_left hu, rawSign_packet P F G u hu j]

theorem value_invalid (P : Readers) (F G : Family) (q : List Bool) (hq : pairFst q ∉ valid P) :
    value P F G q = [] := by rw [value, ite_eq_right hq]

end LeanCanny.Encoding.BoundedCriticalSampleSlice.Principal
