/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalInitialValueBound
public import LeanCanny.Encoding.LevelLiftCoefficient

/-! # Initial-parent provenance for the original level coefficient

Only actual initial coordinate/exceptional roots are used. The source mass
bound predates A and every subsequent mixed birth. Later frozen values require
their own provenance theorem and are not included by this selector interface.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalLevelBound
open LeanCanny.Algebra LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)

 theorem selected_margin (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a)
    (n k D : ℕ) (select : Fin n → Fin (births F u)) :
    |FixedLeadingDilationValueBound.frozenValue k D
      (fun j => FlatAffineExceptionalParentBank.values F C h u v a hv (select j))| <
      (FixedLeadingDilationValueBound.levelCoefficient n D
        (FlatAffineExceptionalInitialValueBound.height F C h u):ℝ)-1 :=
  FixedLeadingDilationValueBound.frozen_margin k D _ _
    (fun j _ => FlatAffineExceptionalInitialValueBound.values_bound F C h u v a hv ha (select j))

theorem initial_coefficient_FP {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (hh : UnaryFn (fun u => (h u).val)) {n D : List Bool → ℕ} {modulus : List Bool → List Bool}
    (hn : UnaryFn n) (hD : UnaryFn D) (hm : modulus ∈ FP) :
    LevelLiftCoefficient.read n D (FlatAffineExceptionalInitialValueBound.height F C h) modulus ∈ FP :=
  LevelLiftCoefficient.read_FP hn hD (FlatAffineExceptionalInitialValueBound.height_binary hF C h hh) hm

end LeanCanny.Encoding.FlatAffineExceptionalLevelBound
