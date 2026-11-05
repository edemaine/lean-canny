/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalVariables
public import LeanCanny.Algebra.CoefficientFinitePhysicalQuery
/-! # Actual ordinary/mean principal series on one full raw tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalSeries
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedRoadmapProperRow CoefficientTarskiParameterQueries
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

/-- The literal actual full scalar columns, before taking canonical retained
quotients. Ordinary and mean roots keep their own raw tuples. -/
noncomputable def scalars (mean : Bool) (z : List Bool)
    (raw : Fin (properPhysicalData hn ht ha mean z).count → ℝ) :
    Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n mean z)) → ℝ :=
  fun i => CoefficientFinitePhysicalQuery.natural raw (scalarAt (properPhysicalData hn ht ha mean z) i.val)

noncomputable def near (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j : ℕ) (β : ℝ)
    (raw : Fin (properPhysicalData hn ht ha false z).count → ℝ) :=
  MvTwoParameterCoefficient.evaluate (SymbolicScaledSquarefree.scalarEvaluation β) (scalars hn ht ha false z raw)
    (castVariables (by omega : 1 + (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z) + 1) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (catalogRoot n false z) + 2)
      (properNearPrincipal hn ht ha right power eta eps z hc j))

noncomputable def rank (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j : ℕ) (β : ℝ)
    (raw : Fin (properPhysicalData hn ht ha true z).count → ℝ) :=
  MvTwoParameterCoefficient.evaluate (SymbolicScaledSquarefree.scalarEvaluation β) (scalars hn ht ha true z raw)
    (properRankPrincipal hn ht ha power eps z hc j)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic properPhysicalData
  properNearPrincipal properRankPrincipal

/-- Extraction keeps the native eta/epsilon axis order and the exact own
physical query. No trailing-coefficient selection is moved through a map. -/
theorem near_coefficient (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j delta epsilon : ℕ) (β : ℝ)
    (raw : Fin (properPhysicalData hn ht ha false z).count → ℝ) :
    ((near hn ht ha right power eta eps z hc j β raw).coeff delta).coeff epsilon =
      (properNearPhysical hn ht ha right power eta eps z hc j delta epsilon).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation β) (CoefficientFinitePhysicalQuery.natural raw) := by
  rw [near, MvTwoParameterCoefficient.selected_coefficient]
  unfold properNearPhysical scalarApply
  rw [MvPolynomial.eval₂_rename]
  rfl

theorem rank_coefficient (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (j delta epsilon : ℕ) (β : ℝ)
    (raw : Fin (properPhysicalData hn ht ha true z).count → ℝ) :
    ((rank hn ht ha power eps z hc j β raw).coeff delta).coeff epsilon =
      (properRankPhysical hn ht ha power eps z hc j delta epsilon).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation β) (CoefficientFinitePhysicalQuery.natural raw) := by
  rw [rank, MvTwoParameterCoefficient.selected_coefficient]
  unfold properRankPhysical scalarApply
  rw [MvPolynomial.eval₂_rename]
  rfl

end LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalSeries
