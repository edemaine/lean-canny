/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialSampleSliceDegree
public import LeanCanny.Encoding.IntegerPolynomialTestSource
public import LeanCanny.Encoding.BoundedAlgebraicSlicePrincipal

/-! # Native principal signs at complete algebraic sample labels

Actual specialized degrees are computed internally and attached to the test
query. The original scalar sample and its label remain fixed throughout.
This includes degree drops, repeated parameter roots, and singular samples.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialSampleSlice.Principal
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegerPolynomialRootQueriesBits (Source)
open BoundedAlgebraicSlice (Family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
attribute [local irreducible] degree point specialized BoundedAlgebraicSlice.Principal.test

def testContext (u : List Bool) : List Bool :=
  pair (pair (pair (pair (pairFst u) (pairFst (pairSnd u))) [])
    (pairFst (pairSnd (pairSnd u)))) (pairSnd (pairSnd (pairSnd u)))
theorem testContext_FP : testContext ∈ FP := by polytime [testContext]

noncomputable def source (F G : Family) : Source where
  polynomial z := (BoundedAlgebraicSlice.Principal.test F G).polynomial (testContext z)
  degree z := (BoundedAlgebraicSlice.Principal.test F G).degree (testContext z)
  mass z := (BoundedAlgebraicSlice.Principal.test F G).mass (testContext z)
  degree_bound z := (BoundedAlgebraicSlice.Principal.test F G).polynomial_degree (testContext z)
  mass_bound z := (BoundedAlgebraicSlice.Principal.test F G).polynomial_mass (testContext z)

theorem sourceAccess {F G : Family} (A : F.Access) (B : G.Access) : IntegerPolynomialRootQueriesBits.Access (source F G) := by
  have E := IntegerPolynomialTestSource.access (BoundedAlgebraicSlice.Principal.testAccess A B)
  exact ⟨PolynomialFamilyProductBits.reindexEvaluator E.coefficient testContext testContext_FP,
    E.degree.comp testContext_FP, E.mass.comp testContext_FP⟩

theorem test_sign (F G : Family) (c r : List Bool) (d e j : ℕ) (theta : ℝ) :
    SignType.sign (((source F G).polynomial
      (pair c (pair r (pair (pair (BinaryNatCode.encode d) (BinaryNatCode.encode e)) (BinaryNatCode.encode j))))).eval₂
        (Int.castRingHom ℝ) theta) =
      SignType.sign (PrincipalSubresultant.signedPsc (F.slice (pair c r) theta) (G.slice (pair c r) theta) d e j) := by
  change SignType.sign ((ParameterTarski.evalHom theta) ((BoundedAlgebraicSlice.Principal.test F G).polynomial
    (testContext (pair c (pair r (pair (pair (BinaryNatCode.encode d) (BinaryNatCode.encode e)) (BinaryNatCode.encode j))))))) = _
  rw [BoundedAlgebraicSlice.Principal.test_eval]
  simp only [testContext, pairFst_pair, pairSnd_pair, BoundedAlgebraicSlice.Principal.origin,
    BoundedAlgebraicSlice.Principal.leftDegree, BoundedAlgebraicSlice.Principal.rightDegree,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

attribute [local irreducible] source IntegerPolynomialIndexedSampleTest.value

noncomputable def prepare (S : Source) (F G : Family) (q : List Bool) : List Bool :=
  pair q (pair (BinaryNatCode.encode (degree S F (pairFst q))) (BinaryNatCode.encode (degree S G (pairFst q))))

theorem prepareEvaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) {F G : Family}
    (B : F.Access) (C : G.Access) : SpaceFunction (prepare S F G) := by
  have E := (((degreeEvaluator A B).precompose pairFst pairFst_mem_FP).pairOutputs
    ((degreeEvaluator A C).precompose pairFst pairFst_mem_FP)).withInput
  exact E.congr (funext fun q => by simp only [Function.comp_apply, prepare, degree])

def finish (z : List Bool) : List Bool :=
  let q := pairFst z
  let u := pairFst q
  let p := pairFst u
  pair (pair (pairFst p) (pairSnd p)) (pair (pairSnd u) (pair (pairSnd z) (pairSnd q)))
theorem finish_FP : finish ∈ FP := by polytime [finish]

noncomputable def rawSign (S : Source) (F G : Family) (q : List Bool) : List Bool :=
  IntegerPolynomialIndexedSampleTest.value S (source F G) (finish (prepare S F G q))

theorem rawSignEvaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) {F G : Family}
    (B : F.Access) (C : G.Access) : SpaceFunction (rawSign S F G) := by
  have E := ((prepareEvaluator (S := S) (F := F) (G := G) A B C).postcompose finish finish_FP).chain
    (IntegerPolynomialIndexedSampleTest.evaluator (S := S) (Q := source F G) A (sourceAccess (F := F) (G := G) B C))
  exact E.congr (funext fun q => by simp only [rawSign, Function.comp_apply])

theorem rawSign_packet (S : Source) (F G : Family) (u : List Bool) (hu : u ∈ valid S) (j : ℕ) :
    rawSign S F G (pair u (BinaryNatCode.encode j)) = InfinitesimalSign.encode
      (SignType.sign (PrincipalSubresultant.signedPsc (specialized S F u) (specialized S G u)
        (degree S F u) (degree S G u) j)) := by
  have H := IntegerPolynomialIndexedSampleTest.packet S (source F G)
    (pairFst (pairFst u)) (pairSnd (pairFst u))
    (pair (pairSnd u) (pair (pair (BinaryNatCode.encode (degree S F u)) (BinaryNatCode.encode (degree S G u)))
      (BinaryNatCode.encode j))) hu
  rw [test_sign] at H
  simpa only [rawSign, prepare, finish, pairFst_pair, pairSnd_pair, specialized, ite_eq_left hu, context,
    point, dite_eq_left hu] using H

noncomputable def value (S : Source) (F G : Family) (q : List Bool) : List Bool :=
  if pairFst q ∈ valid S then rawSign S F G q else []

theorem evaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) {F G : Family}
    (B : F.Access) (C : G.Access) : SpaceFunction (value S F G) :=
  SpaceFunction.branchDecider ((validDecider A).precompose pairFst pairFst_mem_FP)
    (rawSignEvaluator A B C) (SpaceFunction.ofFP _ (constFn_mem_FP []))

theorem value_packet (S : Source) (F G : Family) (u : List Bool) (hu : u ∈ valid S) (j : ℕ) :
    value S F G (pair u (BinaryNatCode.encode j)) = InfinitesimalSign.encode
      (SignType.sign (PrincipalSubresultant.signedPsc (specialized S F u) (specialized S G u)
        (degree S F u) (degree S G u) j)) := by
  rw [value, pairFst_pair, ite_eq_left hu, rawSign_packet S F G u hu j]

theorem value_invalid (S : Source) (F G : Family) (q : List Bool) (hq : pairFst q ∉ valid S) :
    value S F G q = [] := by rw [value, ite_eq_right hq]

end LeanCanny.Encoding.IntegerPolynomialSampleSlice.Principal
