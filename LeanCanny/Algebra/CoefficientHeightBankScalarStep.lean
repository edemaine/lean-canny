/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientHeightBank
public import LeanCanny.Algebra.CoefficientCanonicalScalarAppend
public import LeanCanny.Algebra.IntegralMixedNormalizedScalar

/-! # Actual scalar-root bank births over a coefficient base

The new numerator is the actual padded quotient root, and its denominator
is the selected coefficient-base leading value. This is the native rootStep
bank, rather than the inverse-normalized alternative HeightBank.step.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoefficientHeightBank
open scoped Classical
variable {R A T B : Type*} [CommRing R] [CommRing A] [CommRing T] [CommRing B]
  [Algebra R A] [Algebra T B] {m : ℕ}

noncomputable def rootStep (x : CoefficientHeightBank R A m) (p : Polynomial A)
    (d N : ℕ) (leading : R) :
    CoefficientHeightBank R (PaddedIntegralParameterExtension.Extension p d N) (m + 1) where
  numerator := Fin.cons (AdjoinRoot.root _) (fun i => AdjoinRoot.of _ (x.numerator i))
  denominator := Fin.cons leading x.denominator

omit [Algebra R A] in
theorem rootStep_numerator_zero (x : CoefficientHeightBank R A m) (p : Polynomial A)
    (d N : ℕ) (leading : R) : (x.rootStep p d N leading).numerator 0 = AdjoinRoot.root _ := rfl

omit [Algebra R A] in
theorem rootStep_numerator_succ (x : CoefficientHeightBank R A m) (p : Polynomial A)
    (d N : ℕ) (leading : R) (i : Fin m) :
    (x.rootStep p d N leading).numerator i.succ = AdjoinRoot.of _ (x.numerator i) := rfl

omit [Algebra R A] in
theorem rootStep_denominator_zero (x : CoefficientHeightBank R A m) (p : Polynomial A)
    (d N : ℕ) (leading : R) : (x.rootStep p d N leading).denominator 0 = leading := rfl

omit [Algebra R A] in
theorem rootStep_denominator_succ (x : CoefficientHeightBank R A m) (p : Polynomial A)
    (d N : ℕ) (leading : R) (i : Fin m) :
    (x.rootStep p d N leading).denominator i.succ = x.denominator i := rfl

namespace Specializes
variable {φ : R →+* T} {ψ : A →+* B}
  {x : CoefficientHeightBank R A m} {y : CoefficientHeightBank T B m} (H : Specializes φ ψ x y)
include H

theorem rootStep (p : Polynomial A) (d N : ℕ) (leading : R) :
    Specializes φ (PaddedIntegralParameterExtension.specialize ψ p d N)
      (x.rootStep p d N leading) (y.rootStep (p.map ψ) d N (φ leading)) := by
  constructor
  · intro r
    change PaddedIntegralParameterExtension.specialize ψ p d N
      (AdjoinRoot.of _ (algebraMap R A r)) = AdjoinRoot.of _ (algebraMap T B (φ r))
    rw [PaddedIntegralParameterExtension.specialize_of, H.coefficients]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact PaddedIntegralParameterExtension.specialize_root ψ p d N
    · change PaddedIntegralParameterExtension.specialize ψ p d N
        (AdjoinRoot.of _ (x.numerator j)) = AdjoinRoot.of _ (y.numerator j)
      rw [PaddedIntegralParameterExtension.specialize_of, H.numerator]
  · intro i
    exact Fin.cases rfl (fun j => H.denominator j) i

end Specializes

theorem rootStep_ofState_integer {n cap width : ℕ} {P : IntegralMixedHistory.SpatialSource n}
    {ι : Type} [Fintype ι] (x : IntegralMixedHistory.State P cap width m ι) (hm : m ≤ cap)
    (p : Polynomial ℤ) (hp : p ≠ 0) (hcap : p.natDegree ≤ 2 ^ width) :
    (ofState x).rootStep (p.map (Int.castRingHom x.sampler.scalarPrefix.carrier))
      p.natDegree (2 ^ width) p.leadingCoeff =
      ofState (IntegralMixedHistory.integerStep x hm p hp hcap) := rfl

theorem rootStep_ofState_critical {n cap width : ℕ} {P : IntegralMixedHistory.SpatialSource n}
    {ι : Type} [Fintype ι] (x : IntegralMixedHistory.State P cap width m ι) (hm : m ≤ cap)
    (r : IntegralMixedHistory.CriticalRule n) :
    (ofState x).rootStep (IntegralMixedHistory.criticalPolynomial x hm r)
      (IntegralMixedHistory.criticalDegree x hm r) (2 ^ width) (IntegralMixedHistory.criticalLeading x hm r) =
      ofState (IntegralMixedHistory.criticalStep x hm r) := rfl

theorem rootStep_ofState_normalizedScalar {n cap width : ℕ} {P : IntegralMixedHistory.SpatialSource n}
    {ι : Type} [Fintype ι] (x : IntegralMixedHistory.State P cap width m ι) (hm : m ≤ cap)
    (p : Polynomial x.sampler.scalarPrefix.carrier) (d : ℕ) :
    (ofState x).rootStep (IntegralMixedHistory.normalizedScalarPolynomial x p d) d
      (2 ^ width) (IntegralMixedHistory.normalizedScalarLeading x p d) =
      ofState (IntegralMixedHistory.normalizedScalarStep x hm p d) := rfl

/-- All computed integer-birth fields agree with the actual native update. -/
theorem integer_birth_fields {n cap width : ℕ} {P : IntegralMixedHistory.SpatialSource n}
    {ι : Type} [Fintype ι] (x : IntegralMixedHistory.State P cap width m ι) (hm : m ≤ cap)
    (p : Polynomial ℤ) (hp : p ≠ 0) (hcap : p.natDegree ≤ 2 ^ width) :
    CoefficientCoordinateBasis.ofIntegral (IntegralMixedHistory.integerStep x hm p hp hcap).sampler.scalarPrefix.basis =
      (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis).paddedStep
        (p.map (Int.castRingHom x.sampler.scalarPrefix.carrier)) p.natDegree ∧
    ofState (IntegralMixedHistory.integerStep x hm p hp hcap) =
      (ofState x).rootStep (p.map (Int.castRingHom x.sampler.scalarPrefix.carrier))
        p.natDegree (2 ^ width) p.leadingCoeff ∧
    (IntegralMixedHistory.integerStep x hm p hp hcap).sampler.rows =
      CoefficientCanonicalScalarAppend.rows cap x.sampler.rows x.sampler.scalar
        (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis)
        (p.map (Int.castRingHom x.sampler.scalarPrefix.carrier)) p.natDegree := ⟨rfl, rfl, rfl⟩

/-- The same actual quotient map extends all three constructor invariants. -/
theorem scalar_birth_specializes {ι : Type*} [Nontrivial A] [Nontrivial B]
    {φ : R →+* T} {ψ : A →+* B} {N : ℕ}
    {b : CoefficientCoordinateBasis R A m N} {c : CoefficientCoordinateBasis T B m N}
    (HB : CoefficientCoordinateBasis.Specializes φ ψ b c)
    {x : CoefficientHeightBank R A m} {y : CoefficientHeightBank T B m}
    (HX : Specializes φ ψ x y) (S : ℕ)
    (q : ι → MvPolynomial ι R) (q' : ι → MvPolynomial ι T)
    (HQ : ∀ i, MvPolynomial.map φ (q i) = q' i) (slots : Fin m → ι)
    (p : Polynomial A) (d : ℕ) (leading : R) :
    CoefficientCoordinateBasis.Specializes φ (PaddedIntegralParameterExtension.specialize ψ p d N)
      (b.paddedStep p d) (c.paddedStep (p.map ψ) d) ∧
    Specializes φ (PaddedIntegralParameterExtension.specialize ψ p d N)
      (x.rootStep p d N leading) (y.rootStep (p.map ψ) d N (φ leading)) ∧
    (fun i => MvPolynomial.map φ (CoefficientCanonicalScalarAppend.rows S q slots b p d i)) =
      CoefficientCanonicalScalarAppend.rows S q' slots c (p.map ψ) d :=
  ⟨HB.paddedStep p d, HX.rootStep p d N leading,
    CoefficientCanonicalScalarAppend.newrows_map HB S q q' HQ slots p d⟩

end LeanCanny.Algebra.CoefficientHeightBank
