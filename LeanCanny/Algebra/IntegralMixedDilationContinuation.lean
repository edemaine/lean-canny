/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateCorrelated
public import LeanCanny.Algebra.IntegralMixedDilationAdvance
/-! # A correlated changing-source restart after retaining an original limit

An actual selected relative factor root is retained by a normalized scalar
birth. Its interpreting hom recovers both that root and all earlier values.
Recomputing the source at k+1 then satisfies the actual next frozen equations,
while the entire old physical sample stays unchanged. Future critical samples
belong to the new source; no old level equation or old Y coordinate is reused.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDilationAdvance
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
variable {n k D S B m : ℕ} {u : Fin n} {t : ETR.Term} {ht : t.degreeBound ≤ D} {A : ℤ} {ι : Type} [Fintype ι]

theorem continue_after_limit
    (x : State (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) A) S B m ι)
    (hm : m ≤ S) (hmNext : m+1 ≤ S) (hkn : k<n) (nextObjective : Fin n) (nextLevelCoefficient : ℤ)
    (r : Rule (n+1)) (j : Fin ((n+1)-r.critical.offset.val+1))
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound
      (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) A) r))
    (hc : IntegralMixedLimitCoordinate.Valid x hm r j φ c)
    (z : ι → ℝ) (hz : ∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i, φ (x.sampler.scalarPrefix.basis.generator i)=
      z (x.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) m i)
    (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a : ℝ) (ha : ((IntegralMixedLimitCoordinate.factor x hm r j c).map φ.toRingHom).eval a=0)
    (select : Fin k → Fin m) (old : Fin n → ℝ)
    (Hparam : ∀ i : Fin n, ∀ hi : i.val<k, old i=values (select ⟨i.val,hi⟩))
    (Ha : old ⟨k,hkn⟩=a) :
    ∃ d : ℕ, d ≤ IntegralMixedLimitCoordinate.degree
        (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) A) r ∧
      let x' := advance (IntegralMixedLimitCoordinate.step x hm r j c d) nextObjective nextLevelCoefficient
      ∃ y : (ι ⊕ Unit) → ℝ, ∃ ψ : x'.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, (x'.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
        (∀ i, y (Sum.inl i)=z i) ∧
        (∀ i, ψ (x'.sampler.scalarPrefix.basis.generator i)=
          y (x'.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) (m+1) i) ∧
        (∀ i, ψ (x'.bank.numerator i)/(x'.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1) → ℝ) i) ∧
        ∀ (eta v : ℝ) i,
          i.val<(IntegralMixedCanonicalDilation.rule (by omega : k+1≤n) (nextSelector select)).critical.offset.val →
          ((data x' hmNext (IntegralMixedCanonicalDilation.rule (by omega : k+1≤n)
            (nextSelector select)).critical).scales i:ℝ)*
            IntegralMixedCanonicalDilation.point (k:=k+1) x' eta old v i =
          heightValue x' (IntegralMixedCanonicalDilation.rule (by omega : k+1≤n)
            (nextSelector select)) ψ eta i := by
  obtain ⟨d,hd,y,ψ,hy,htail,_,hψ,Hnew⟩ := IntegralMixedLimitCoordinate.real_extend_correlated
    x hm r j φ c hc z hz hφ values H a ha
  refine ⟨d,hd,y,ψ,hy,htail,hψ,Hnew,?_⟩
  intro eta v
  exact advanced_frozen (IntegralMixedLimitCoordinate.step x hm r j c d) nextObjective nextLevelCoefficient hmNext hkn
    select ψ values a Hnew eta old v Hparam Ha

end LeanCanny.Algebra.IntegralMixedDilationAdvance
