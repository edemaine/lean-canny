/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
/-! # One original regular source across candidate labels and record tables

Only the original input selects the radius. Candidate labels, record bytes,
auxiliary fields and saved births do not select a different spatial source.
This says nothing about equality of the corresponding retained banks.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedOriginalRegularSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (original number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def context (input label tail : List Bool) :=pair (pair input label) tail
def canonical (input : List Bool) :=context input [] []
def radius (R0 : List Bool→ℕ) (c : List Bool) :=R0 (original c)

theorem original_context (input label tail : List Bool) : original (context input label tail)=input :=by
  simp only [context,original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,pairFst_pair]
theorem radius_context (R0 : List Bool→ℕ) (input label tail : List Bool) :
    radius R0 (context input label tail)=R0 input :=by rw [radius,original_context]
theorem radius_binary {R0 : List Bool→ℕ} (hR0 : BinaryFn R0) : BinaryFn (radius R0) :=
  hR0.comp IntegralMixedAuxiliaryMarkedIntegerPlan.original_FP

theorem context_FP {input label tail : List Bool→List Bool}
    (hi : input∈FP) (hl : label∈FP) (ht : tail∈FP) :
    (fun q=>context (input q) (label q) (tail q))∈FP :=mem_FP_pair (mem_FP_pair hi hl) ht

theorem original_writer {input label records aux : List Bool→List Bool} (q : List Bool) :
    original (context (input q) (label q) (pair (records q) (aux q)))=input q :=
  original_context _ _ _

noncomputable def source (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ) (input : List Bool) :=
  BoundedRegularLowModularTerm.source (BoundedRegularLowCoefficient.readers n t R0) input

theorem spatial_source (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ) (c : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c=source n t R0 (original c) :=rfl

theorem source_congr (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ)
    (a b : List Bool) (h : a=b) : HEq (source n t R0 a) (source n t R0 b) :=by cases h;rfl
private theorem low_congr (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ)
    (a b : List Bool) (h : a=b) : HEq (source n t R0 a).low (source n t R0 b).low :=by cases h;rfl

theorem spatial_context (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ)
    (input label tail : List Bool) :
    HEq (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (context input label tail))
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (canonical input)) :=by
  simp only [spatial_source]
  exact source_congr n t R0 _ _ ((original_context input label tail).trans (original_context input [] []).symm)

theorem low_context (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ)
    (input label tail : List Bool) :
    HEq (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (context input label tail)).low
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (canonical input)).low :=by
  simp only [spatial_source]
  exact low_congr n t R0 _ _ ((original_context input label tail).trans (original_context input [] []).symm)
theorem leading_context (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ)
    (input label tail : List Bool) :
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (context input label tail)).leading=
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (canonical input)).leading :=by
  simp only [spatial_source]
  exact congrArg (fun c=>(source n t R0 c).leading)
    ((original_context input label tail).trans (original_context input [] []).symm)
theorem degree_context (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ)
    (input label tail : List Bool) :
    (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (context input label tail)).degree=
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) (canonical input)).degree :=by
  simp only [spatial_source]
  exact congrArg (fun c=>(source n t R0 c).degree)
    ((original_context input label tail).trans (original_context input [] []).symm)

theorem source_polynomial (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ) (input : List Bool) :
    FermatCriticalHomogenization.polynomial (source n t R0 input).low (source n t R0 input).leading
      (source n t R0 input).degree=
      LeanCanny.Geometry.BoundedRegularSource.polynomial ((t input).finitePolynomial (n input))
        (t input).toData.size (t input).toData.size (R0 input) :=
  BoundedRegularLowCoefficient.readers_source_polynomial n t R0 input

theorem spatial_polynomial (n : List Bool→ℕ) (t : List Bool→Term) (R0 : List Bool→ℕ) (c : List Bool) :
    FermatCriticalHomogenization.polynomial
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c).low
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c).leading
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) c).degree=
      LeanCanny.Geometry.BoundedRegularSource.polynomial ((t (original c)).finitePolynomial (number n c))
        (t (original c)).toData.size (t (original c)).toData.size (radius R0 c) :=
  source_polynomial n t R0 (original c)
end LeanCanny.Encoding.IntegralMixedOriginalRegularSource
