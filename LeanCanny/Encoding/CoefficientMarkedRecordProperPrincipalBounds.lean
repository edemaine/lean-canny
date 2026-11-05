/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalPhysical
/-! # Original parameter coefficient bounds for actual proper principal queries -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def properPrincipalCutoff (mean : Bool) (z : List Bool) :=
  CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z)

noncomputable def properNearCoefficientBudget (z : List Bool) :=
  IntegerPolynomialDyadic.massBudget (properPrincipalCutoff hn ht ha false z)
    (nearMassSlope hn ht ha z) (nearMassOffset hn ht ha z)

noncomputable def properRankCoefficientBudget (z : List Bool) :=
  IntegerPolynomialDyadic.massBudget (properPrincipalCutoff hn ht ha true z)
    (rankMassSlope hn ht ha z) (rankMassOffset hn ht ha z)

theorem properPrincipalCutoff_binary (mean : Bool) : BinaryFn (properPrincipalCutoff hn ht ha mean) := by
  cases mean
  · exact (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).comp
      (near_catalogRoot_FP hn ht ha)
  · exact (CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).comp
      (rank_catalogRoot_FP hn ht ha)

theorem properNearCoefficientBudget_binary : BinaryFn (properNearCoefficientBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary (properPrincipalCutoff_binary hn ht ha false)
    (nearMassSlope_binary hn ht ha) (nearMassOffset_binary hn ht ha)

theorem properRankCoefficientBudget_binary : BinaryFn (properRankCoefficientBudget hn ht ha) :=
  IntegerPolynomialDyadic.massBudget_binary (properPrincipalCutoff_binary hn ht ha true)
    (rankMassSlope_binary hn ht ha) (rankMassOffset_binary hn ht ha)

theorem proper_near_coefficient_degree_mass (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (j delta epsilon : ℕ) (v : ℕ →₀ ℕ) :
    ((properNearPhysical hn ht ha right power eta eps z hc j delta epsilon).coeff v).natDegree ≤
      nearMassSlope hn ht ha z ∧
    coefficientMass ((properNearPhysical hn ht ha right power eta eps z hc j delta epsilon).coeff v) ≤
      2^properNearCoefficientBudget hn ht ha z := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius (fun _ => r) (catalogRoot n false z) := hr
  have HS := congrArg (fun p : MvPolynomial ℕ ℤ => p.coeff v)
    (proper_near_physical_map hn ht ha (BinaryFn.const r) right power eta eps z hc hg HR j delta epsilon)
  rw [MvPolynomial.coeff_map] at HS
  change ((properNearPhysical hn ht ha right power eta eps z hc j delta epsilon).coeff v).eval ((2 : ℤ)^r) = _ at HS
  rw [HS]
  exact (MvMass.coeff_le _ v).trans ((MvMass.rename_le _ _).trans
    (near_physical_principal_mass hn ht ha (BinaryFn.const r) right power eta eps z j delta epsilon hc hg))

theorem proper_rank_coefficient_degree_mass (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (j delta epsilon : ℕ) (v : ℕ →₀ ℕ) :
    ((properRankPhysical hn ht ha power eps z hc j delta epsilon).coeff v).natDegree ≤
      rankMassSlope hn ht ha z ∧
    coefficientMass ((properRankPhysical hn ht ha power eps z hc j delta epsilon).coeff v) ≤
      2^properRankCoefficientBudget hn ht ha z := by
  apply IntegerPolynomialDyadic.degree_mass_of_growth
  intro r hr
  have HR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n true z) ≤
      IntegralMixedOriginalRegularSource.radius (fun _ => r) (catalogRoot n true z) := hr
  have HS := congrArg (fun p : MvPolynomial ℕ ℤ => p.coeff v)
    (proper_rank_physical_map hn ht ha (BinaryFn.const r) power eps z hc hg HR j delta epsilon)
  rw [MvPolynomial.coeff_map] at HS
  change ((properRankPhysical hn ht ha power eps z hc j delta epsilon).coeff v).eval ((2 : ℤ)^r) = _ at HS
  rw [HS]
  exact (MvMass.coeff_le _ v).trans ((MvMass.rename_le _ _).trans
    (rank_physical_principal_mass hn ht ha (BinaryFn.const r) power eps z j delta epsilon hc hg))

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
