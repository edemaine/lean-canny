/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperSeriesErasure
public import LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessContext
/-! # Native statistic compilation at the literal replacement-word row key -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessValue
open LeanCanny.Algebra LeanCanny.Computation Polynomial PrincipalSubresultant
open IntegralMixedRoadmapProperRow CoefficientMarkedRecordProperWitnessLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def reindex {a b : ℕ} (h : a = b) (x : Fin b → ℝ) : Fin a → ℝ := x ∘ Fin.cast h
private theorem reindex_heq {a b : ℕ} (h : a = b) (x : Fin b → ℝ) : HEq (reindex h x) x := by
  cases h
  rfl
private theorem evaluate_heq {A B : Type} (f : ℝ → A → (ℝ[X])[X]) (g : ℝ → B → (ℝ[X])[X])
    (h : HEq f g) (β : ℝ) (x : A) (y : B) (he : HEq x y) : f β x = g β y := by
  cases he
  cases eq_of_heq h
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
attribute [local irreducible] CoefficientMarkedRecordProperPrincipalSeries.near
  CoefficientMarkedRecordProperPrincipalSeries.rank CoefficientMarkedRecordRows.symbolic
  IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family

theorem near_value_rekey (right : Bool) (power : Fin 3) (eta eps : Bool) (z baseWord : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius R (catalogRoot n false z)) (own : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false)
      (request z baseWord) own)
    (raw : Fin (properPhysicalData hn ht ha false z).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false)
      (request z baseWord) own hv).val raw) :
    CoefficientMarkedRecordProperWordValue.nearStatistic hn ht ha hR right power eta eps (request z baseWord) own =
      permanencesMinusVariations ((List.range (max 1 (catalogDegree hn ht ha false z)+1)).reverse.map
        (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j
          ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R (catalogRoot n false z)) raw))) := by
  let hN := congrArg (fun d : CoefficientMarkedRecordRows.Data ℤ[X] => d.count)
    (CoefficientMarkedRecordProperSeriesErasure.data_request hn ht ha false z baseWord)
  let raw' := reindex hN raw
  have he : HEq raw' raw := reindex_heq hN raw
  let hc' := (count_request z baseWord).symm ▸ hc
  have hl : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false (request z baseWord)) ≤
      IntegralMixedOriginalRegularSource.radius R (catalogRoot n false (request z baseWord)) := by
    simpa only [catalogRoot_request] using hlarge
  have HR := CoefficientMarkedRecordProperWordValue.near_value_eq hn ht ha hR right power eta eps (request z baseWord) hc'
    ((syntax_request n z baseWord).mpr hg) hl own hv raw' (hj.trans he.symm)
  rw [catalogRoot_request, CoefficientMarkedRecordProperSeriesErasure.degree_request] at HR
  apply HR.trans
  apply congrArg permanencesMinusVariations
  apply List.map_congr_left
  intro j _
  apply congrArg RealIteratedTarski.lex
  exact evaluate_heq _ _ (CoefficientMarkedRecordProperSeriesErasure.near_function_heq hn ht ha right power eta eps z baseWord hc j)
    _ raw' raw he

theorem rank_value_rekey (power : Fin 3) (eps : Bool) (z baseWord : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n true z) ≤
      IntegralMixedOriginalRegularSource.radius R (catalogRoot n true z)) (own : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true)
      (request z baseWord) own)
    (raw : Fin (properPhysicalData hn ht ha true z).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true)
      (request z baseWord) own hv).val raw) :
    CoefficientMarkedRecordProperWordValue.rankStatistic hn ht ha hR power eps (request z baseWord) own =
      permanencesMinusVariations ((List.range (max 1 (catalogDegree hn ht ha true z)+1)).reverse.map
        (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j
          ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R (catalogRoot n true z)) raw))) := by
  let hN := congrArg (fun d : CoefficientMarkedRecordRows.Data ℤ[X] => d.count)
    (CoefficientMarkedRecordProperSeriesErasure.data_request hn ht ha true z baseWord)
  let raw' := reindex hN raw
  have he : HEq raw' raw := reindex_heq hN raw
  let hc' := (count_request z baseWord).symm ▸ hc
  have hl : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n true (request z baseWord)) ≤
      IntegralMixedOriginalRegularSource.radius R (catalogRoot n true (request z baseWord)) := by
    simpa only [catalogRoot_request] using hlarge
  have HR := CoefficientMarkedRecordProperWordValue.rank_value_eq hn ht ha hR power eps (request z baseWord) hc'
    ((syntax_request n z baseWord).mpr hg) hl own hv raw' (hj.trans he.symm)
  rw [catalogRoot_request, CoefficientMarkedRecordProperSeriesErasure.degree_request] at HR
  apply HR.trans
  apply congrArg permanencesMinusVariations
  apply List.map_congr_left
  intro j _
  apply congrArg RealIteratedTarski.lex
  exact evaluate_heq _ _ (CoefficientMarkedRecordProperSeriesErasure.rank_function_heq hn ht ha power eps z baseWord hc j)
    _ raw' raw he

end LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessValue
