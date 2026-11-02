/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalInitialRealization
/-! # Original-source bounds under the constructed bank-only real hom

Bounds use only the original integer polynomials. They do not depend on the
later level coefficient or on a mixed-history height containing that coefficient.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalInitialRealization
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedIntegerRealization
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births width)

theorem values_bound (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a) (i : ℕ) :
    |values F C h u v a hv i| ≤ (2:ℝ)^FlatAffineExceptionalInitialValueBound.height F C h u := by
  by_cases hi : i<births F u
  · rw [values_fin F C h u v a hv ⟨i,hi⟩]
    exact FlatAffineExceptionalInitialValueBound.values_bound F C h u v a hv ha _
  · simp only [values,hi,dite_false,abs_zero]
    positivity

theorem realizes_bounds {n S B m : ℕ} {P : SpatialSource n} {ι : Type} (x : State P S B m ι)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u v a : List Bool) (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a)
    (hr : Realizes x (values F C h u v a hv)) :
    ∃ y : ι → ℝ, ∃ φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
      (∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀ i, φ (x.sampler.scalarPrefix.basis.generator i)=y (x.sampler.scalar i)^
        UniformIntegralPowerSchedule.weights S (2^B) m i) ∧
      (∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values F C h u v a hv i.val) ∧
      (∀ i, |φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)| ≤
        (2:ℝ)^FlatAffineExceptionalInitialValueBound.height F C h u) ∧
      (∀ i, |φ (cleared x i)/(commonDenominator x:ℝ)| ≤
        (2:ℝ)^FlatAffineExceptionalInitialValueBound.height F C h u) := by
  obtain ⟨y,φ,hy,hφ,H⟩ := hr
  refine ⟨y,φ,hy,hφ,H,?_,?_⟩
  · intro i
    rw [H]
    exact values_bound F C h u v a hv ha i.val
  · intro i
    rw [cleared_recover x φ (fun i => values F C h u v a hv i.val) H i,
      mul_div_cancel_left₀ _ (Int.cast_ne_zero.mpr (commonDenominator_ne_zero x))]
    exact values_bound F C h u v a hv ha i.val

theorem family_bounded_realization (P : IntegralCriticalHistoryTask.Parameters)
    (base : IntegralMixedFullHistoryFamilyBits.Data P)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (input : List Bool → List Bool)
    (later : (root : List Bool) → List (Command (base.spatial root) (P.width root)))
    (hW : ∀ root, width F (input root) ≤ P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2 ≤ P.cap root+1)
    (key v a : List Bool)
    (hb : IntegralMixedFullHistoryFamilyBits.prefixLength P key = births F (input (pairFst key)))
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) (input (pairFst key)) v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) (input (pairFst key)) a) :
    let x := (IntegralMixedFullHistoryFamilyBits.family P
      (FlatAffineExceptionalIntegerProducer.data P base F C h input later hW hroom)).state key
    ∃ φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
      (∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=
        values F C h (input (pairFst key)) v a hv i.val) ∧
      (∀ i, |φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)| ≤
        (2:ℝ)^FlatAffineExceptionalInitialValueBound.height F C h (input (pairFst key))) ∧
      (∀ i, |φ (cleared x i)/(commonDenominator x:ℝ)| ≤
        (2:ℝ)^FlatAffineExceptionalInitialValueBound.height F C h (input (pairFst key))) := by
  dsimp only
  obtain ⟨_,φ,_,_,H,Hnorm,Hclear⟩ := realizes_bounds _ F C h _ v a hv ha
    (family_realizes P base F C h input later hW hroom key v a hb hv ha)
  exact ⟨φ,H,Hnorm,Hclear⟩

end LeanCanny.Encoding.FlatAffineExceptionalInitialRealization
