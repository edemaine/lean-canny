/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleLineCorrect
public import LeanCanny.Encoding.BoundedCriticalSampleSliceRootCount

/-! # Native arithmetic-term slices on lines through actual samples

The coordinate and term families are constructed from the original readers.
Their denominator powers are even and nonzero at every point of the line.
Thus the specialized polynomial has exactly the original term's signs.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleLineTerm
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Brackets
open scoped Classical
attribute [local irreducible] BoundedCriticalRationalCoordinates.coordinateDegree
  BoundedCriticalRationalCoordinates.coordinateMass

noncomputable def source (read : List Bool → List Bool) : RationalSubstitutionBits.Source :=
  RationalSubstitutionBits.Source.ofTerm read

noncomputable def family (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) : BoundedAlgebraicSlice.Family where
  polynomial := BivariateRationalTermReader.polynomial (source read)
    (BoundedCriticalSampleLineCoordinates.family P f true) (BoundedCriticalSampleLineCoordinates.family P f false)
  degree u := BivariateRationalTermReader.weight (source read) u *
    max ((BoundedCriticalSampleLineCoordinates.family P f true).degree u) ((BoundedCriticalSampleLineCoordinates.family P f false).degree u)
  parameterDegree u := BivariateRationalTermReader.weight (source read) u *
    max ((BoundedCriticalSampleLineCoordinates.family P f true).parameterDegree u) ((BoundedCriticalSampleLineCoordinates.family P f false).parameterDegree u)
  mass u := 2 * ((source read).normalized u).length + 1 + BivariateRationalTermReader.weight (source read) u *
    BivariateRationalTermReader.coordinateMass (BoundedCriticalSampleLineCoordinates.family P f true) (BoundedCriticalSampleLineCoordinates.family P f false) u
  polynomial_degree := BivariateRationalTermReader.outer_degree_le _ _ _
  coefficient_degree := BivariateRationalTermReader.inner_degree_le _ _ _
  coefficient_mass u i := by
    simpa only [BivariateTermReader.size_eq] using (NestedMass.coeff_le _ i).trans
      (BivariateRationalTermReader.mass_le (source read) (BoundedCriticalSampleLineCoordinates.family P f true)
        (BoundedCriticalSampleLineCoordinates.family P f false) u)

noncomputable def access {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : (family P f read).Access := by
  let N := BoundedCriticalSampleLineCoordinates.access h hf true ha
  let D := BoundedCriticalSampleLineCoordinates.access h hf false ha
  have hs : (source read).PolyTime := RationalSubstitutionBits.Source.ofTerm_polyTime hr
  have hw := BivariateRationalTermReader.weight_binary (source read) hs
  refine ⟨BivariateRationalTermReader.reader (source read) hs N D,
    hw.mul (BivariateRationalTermReader.max_binary N.degree_binary D.degree_binary),
    hw.mul (BivariateRationalTermReader.max_binary N.parameterDegree_binary D.parameterDegree_binary), ?_⟩
  have hsize := BinaryFn.ofUnary (UnaryFn.length ((source read).normalized_mem_FP hs))
  have hn := N.mass_binary.add ((N.degree_binary.add (BinaryFn.const 1)).size)
  have hd := D.mass_binary.add ((D.degree_binary.add (BinaryFn.const 1)).size)
  exact (((BinaryFn.const 2).mul hsize).add (BinaryFn.const 1)).add
    (hw.mul (BivariateRationalTermReader.max_binary hn hd))

theorem sign_sample (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (t : ℝ) :
    SignType.sign (((family P f read).slice (pair c r) (BoundedCriticalSampleLabels.parameter P c x).val).eval t) =
      SignType.sign ((TermView.term (read (pair c r))).eval (Function.update (Formula.extend x.val) (f (pair c r)) t)) := by
  have H := BivariateRationalTermReader.sign_specialize (source read)
    (BoundedCriticalSampleLineCoordinates.family P f true) (BoundedCriticalSampleLineCoordinates.family P f false)
    (pair c r) (BoundedCriticalSampleLabels.parameter P c x).val t
    (fun i _ => BoundedCriticalSampleLineCoordinates.denominator_nonzero P f c r x t i)
  rw [BoundedCriticalSampleLineCoordinates.environment_sample] at H
  exact H

theorem zero_sample (P : Readers) (f : List Bool → ℕ) (read : List Bool → List Bool) (c r : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (t : ℝ) :
    ((family P f read).slice (pair c r) (BoundedCriticalSampleLabels.parameter P c x).val).eval t = 0 ↔
      (TermView.term (read (pair c r))).eval (Function.update (Formula.extend x.val) (f (pair c r)) t) = 0 := by
  rw [← sign_eq_zero_iff, sign_sample, sign_eq_zero_iff]

theorem native_readers {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f)
    (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedCriticalSampleSlice.coefficientSign P (family P f read)) ∧
      SpaceFunction (fun u => BinaryNatCode.encode (BoundedCriticalSampleSlice.degree P (family P f read) u)) ∧
      SpaceFunction (fun u => BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P (family P f read) u)) :=
  ⟨BoundedCriticalSampleSlice.coefficientSign_evaluator h (access h hf read hr ha) ha,
    BoundedCriticalSampleSlice.degree_evaluator h (access h hf read hr ha) ha,
    BoundedCriticalSampleSlice.RootCount.count_evaluator h (access h hf read hr ha) ha⟩

end LeanCanny.Encoding.BoundedCriticalSampleLineTerm
