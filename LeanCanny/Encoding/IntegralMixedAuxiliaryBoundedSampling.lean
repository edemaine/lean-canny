/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeNativeRealization
public import LeanCanny.Encoding.IntegralMixedAuxiliaryChoiceBounds
/-! # Polynomially bounded native descriptors meet every original clopen piece -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
open LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Geometry.CoerciveComponentSampling
open LeanCanny.Algebra.AuxiliaryTiltedTerm (polynomial)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] terminalState nativeRun planAt scalarWidth scalarCeiling

theorem exists_bounded_prepared_run_sample {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    ∃ rootBound adviceBound : Polynomial ℕ, ∀ original,
      ∀ (C : Set (Zeros (polynomial (n original) (t original)))), IsClopen C →
      ∀ x0 : Zeros (polynomial (n original) (t original)), x0∈C →
      ∃ labels : Fin (n original) → ℕ × ℕ, ∃ advice : List Bool,
        advice=IntegralMixedAuxiliaryChoiceAdvice.encode (scalarWidth n t original) labels ∧
        advice.length=2*n original*scalarWidth n t original ∧
        advice.length≤adviceBound.eval original.length ∧
        (root original labels advice).length≤rootBound.eval original.length ∧
        IntegralMixedAuxiliaryChoiceAdvice.prepare n t (pair original advice)=root original labels advice ∧
        (∀ i,(labels i).1≤scalarCeiling n t original ∧ (labels i).2≤scalarCeiling n t original) ∧
        ∃ p : Zeros (polynomial (n original) (t original)), p∈C ∧
          OriginalRealization (nativeRun hn ht ha original labels advice) p.val := by
  obtain ⟨r,hr⟩:=IntegralMixedAuxiliaryChoiceAdvice.root_length_polynomial hn ht
  obtain ⟨a,ha'⟩:=IntegralMixedAuxiliaryChoiceAdvice.advice_length_polynomial hn ht
  refine ⟨r,a,fun original C hC x0 hx0 => ?_⟩
  obtain ⟨labels,hb,p,hp,hreal⟩:=exists_prepared_run_sample_uniform hn ht ha original C hC x0 hx0
  refine ⟨labels,IntegralMixedAuxiliaryChoiceAdvice.encode (scalarWidth n t original) labels,rfl,
    IntegralMixedAuxiliaryChoiceAdvice.encode_length _ _,ha' original labels,
    hr original labels (fun i => (hb i).1) (fun i => (hb i).2),
    IntegralMixedAuxiliaryChoiceAdvice.prepare_encode n t original labels
      (fun i => (hb i).1) (fun i => (hb i).2),hb,p,hp,hreal _⟩
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
