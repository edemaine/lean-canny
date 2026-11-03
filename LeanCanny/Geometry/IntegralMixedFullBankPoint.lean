/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalColumn
/-! # A full physical joint root determines the actual retained bank point

All physical critical rows are retained in the root premise. The scalar
coordinates are read through their actual injection into the full carrier;
there is no scalar-only sampling or independent coordinate root choice.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFullBankPoint
open LeanCanny.Algebra IntegralMixedHistory IntegralHistorySampler UniformIntegralPowerSchedule
open LeanCanny.Encoding IntegralCriticalHistoryTask
open scoped Classical
variable {n S B m a : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable def point (x : State P S B m ι) (z : ι→ℝ) : Fin m→ℝ :=
  IntegralMixedCanonicalBankPoint.point x (z ∘ x.sampler.scalar)

omit [Fintype ι] in
theorem interprets (x : State P S B m ι) (hc : Canonical x) (z : ι→ℝ)
    (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃ φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i) ∧
      ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=point x z i := by
  obtain ⟨φ,hφ⟩:=x.sampler.interpret ℝ z hz
  exact ⟨φ,hφ,IntegralMixedCanonicalBankPoint.quotient_eq x hc _ φ hφ⟩

noncomputable def indexedPoint (x : State P S B m ι) (e : ι≃Fin a) (z : Fin a→ℝ) : Fin m→ℝ :=
  point x (z ∘ e)

theorem indexed_interprets (x : State P S B m ι) (hc : Canonical x) (e : ι≃Fin a) (z : Fin a→ℝ)
    (hz : ∀ i,((reindex x.sampler e).rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃ φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (e (x.sampler.scalar i))^weights S (2^B) m i) ∧
      ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=indexedPoint x e z i := by
  obtain ⟨φ,hφ⟩:=(reindex x.sampler e).interpret ℝ z hz
  exact ⟨φ,hφ,IntegralMixedCanonicalBankPoint.quotient_eq x hc _ φ hφ⟩

/-- Full physical native column readback for an actual source-framed state. -/
theorem framed_point (p : Parameters) (d : IntegralMixedFramedHistoryFamilyBits.Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents p d h T) (key : List Bool)
    (z : Fin (IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryFamilyBits.commands p d key))→ℝ)
    (i : Fin (IntegralMixedFramedHistoryFamilyBits.commands p d key).length) :
    indexedPoint ((IntegralMixedFramedHistoryFamilyBits.family p d h).state key)
      (IntegralMixedFramedPhysicalIndex.enumerate (IntegralMixedFramedHistoryFamilyBits.commands p d key)) z i=
      z ⟨IntegralMixedFramedPhysicalIndex.scalarColumn p T (pair key (BinaryNatCode.encode i.val)),by
        rw [IntegralMixedFramedPhysicalIndex.scalarColumn_actual p d h T hr key i]
        exact (IntegralMixedFramedPhysicalIndex.enumerate _ (((IntegralMixedFramedHistoryFamilyBits.family p d h).state key).sampler.scalar i)).isLt⟩^
        weights (p.cap (pairFst key)+1) (2^p.width (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.commands p d key).length i /
      ((((IntegralMixedFramedHistoryFamilyBits.family p d h).state key).bank.denominator i):ℝ) := by
  unfold indexedPoint point IntegralMixedCanonicalBankPoint.point
  congr 2
  apply congrArg z
  apply Fin.ext
  exact (IntegralMixedFramedPhysicalIndex.scalarColumn_actual p d h T hr key i).symm
end LeanCanny.Geometry.IntegralMixedFullBankPoint
