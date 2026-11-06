/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessValue
/-! # Canonical actual Near/Rank formulas at replacement-word witness keys -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessGuards
open LeanCanny.Algebra LeanCanny.Computation Polynomial PrincipalSubresultant Set
open IntegralMixedRoadmapProperRow CoefficientMarkedRecordProperWitnessLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def nearValue (right : Bool) (power : Fin 3) (eta eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (β : ℝ)
    (raw : Fin (properPhysicalData hn ht ha false z).count → ℝ) :=
  permanencesMinusVariations ((List.range (max 1 (catalogDegree hn ht ha false z)+1)).reverse.map
    (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j β raw)))

noncomputable def nearHolds (right : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (code : List Bool) (β : ℝ)
    (raw : Fin (properPhysicalData hn ht ha false z).count → ℝ) : Prop :=
  OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack code
    (SignStatisticBits.integerCode (nearValue hn ht ha right 0 right false z hc β raw))
    (SignStatisticBits.integerCode (nearValue hn ht ha right 2 right false z hc β raw))
    (SignStatisticBits.integerCode (nearValue hn ht ha right 1 right false z hc β raw))
    (SignStatisticBits.integerCode (nearValue hn ht ha right 2 right true z hc β raw))
    (SignStatisticBits.integerCode (nearValue hn ht ha right 1 right true z hc β raw)))

theorem near_native_iff {R : List Bool → ℕ} (hR : BinaryFn R) (right : Bool) (z baseWord : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n false z) ≤
      IntegralMixedOriginalRegularSource.radius R (catalogRoot n false z)) (own code : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false)
      (request z baseWord) own)
    (raw : Fin (properPhysicalData hn ht ha false z).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false)
      (request z baseWord) own hv).val raw) :
    pair (pair (request z baseWord) own) code ∈ nearLanguage hn ht ha hR right ↔
      nearHolds hn ht ha right z hc code
        ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R (catalogRoot n false z)) raw := by
  rw [CoefficientMarkedRecordProperGuardPackets.near_guard_iff hn ht ha hR right (request z baseWord)
    ((count_request z baseWord).symm ▸ hc) ((syntax_request n z baseWord).mpr hg) own code hv]
  have H (power : Fin 3) (eps : Bool) := CoefficientMarkedRecordProperWitnessValue.near_value_rekey hn ht ha hR
    right power right eps z baseWord hc hg hlarge own hv raw hj
  unfold nearHolds nearValue
  rw [H 0 false, H 2 false, H 1 false, H 2 true, H 1 true]

theorem near_holds_on_curve (right : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) (code : List Bool)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordProperPrincipalSign.cutoff hn ht ha false right z ≤ a)
    (x : C(Ioo a b, Fin (properPhysicalData hn ht ha false z).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (catalogRoot n false z)
      (IntegralMixedCausalRecordPlanBits.count (catalogRoot n false z)) le_rfl u.val (x u))
    (u v : Ioo a b) : nearHolds hn ht ha right z hc code u.val (x u) ↔
      nearHolds hn ht ha right z hc code v.val (x v) := by
  have H (power : Fin 3) (eps : Bool) : nearValue hn ht ha right power right eps z hc u.val (x u) =
      nearValue hn ht ha right power right eps z hc v.val (x v) := by
    unfold nearValue
    apply permanencesMinusVariations_congr
    simp only [List.map_map]
    apply List.map_congr_left
    intro j _
    simpa only [Function.comp_apply] using CoefficientMarkedRecordProperPrincipalLex.near_lex_on_root_curve hn ht ha
      right z hc hg ha0 x hx power right eps j u v
  unfold nearHolds
  rw [H 0 false, H 2 false, H 1 false, H 2 true, H 1 true]

noncomputable def rankValue (power : Fin 3) (eps : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (β : ℝ)
    (raw : Fin (properPhysicalData hn ht ha true z).count → ℝ) :=
  permanencesMinusVariations ((List.range (max 1 (catalogDegree hn ht ha true z)+1)).reverse.map
    (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j β raw)))

noncomputable def rankHolds (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (code : List Bool) (β : ℝ)
    (raw : Fin (properPhysicalData hn ht ha true z).count → ℝ) : Prop :=
  OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack code
    (SignStatisticBits.integerCode (rankValue hn ht ha 0 false z hc β raw))
    (SignStatisticBits.integerCode (rankValue hn ht ha 2 false z hc β raw))
    (SignStatisticBits.integerCode (rankValue hn ht ha 1 false z hc β raw))
    (SignStatisticBits.integerCode (rankValue hn ht ha 2 true z hc β raw))
    (SignStatisticBits.integerCode (rankValue hn ht ha 1 true z hc β raw)))

theorem rank_native_iff {R : List Bool → ℕ} (hR : BinaryFn R) (z baseWord : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n true z) ≤
      IntegralMixedOriginalRegularSource.radius R (catalogRoot n true z)) (own code : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true)
      (request z baseWord) own)
    (raw : Fin (properPhysicalData hn ht ha true z).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true)
      (request z baseWord) own hv).val raw) :
    pair (pair (request z baseWord) own) code ∈ rankLanguage hn ht ha hR ↔
      rankHolds hn ht ha z hc code
        ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R (catalogRoot n true z)) raw := by
  rw [CoefficientMarkedRecordProperGuardPackets.rank_guard_iff hn ht ha hR (request z baseWord)
    ((count_request z baseWord).symm ▸ hc) ((syntax_request n z baseWord).mpr hg) own code hv]
  have H (power : Fin 3) (eps : Bool) := CoefficientMarkedRecordProperWitnessValue.rank_value_rekey hn ht ha hR
    power eps z baseWord hc hg hlarge own hv raw hj
  unfold rankHolds rankValue
  rw [H 0 false, H 2 false, H 1 false, H 2 true, H 1 true]

theorem rank_holds_on_curve (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) (code : List Bool)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordProperPrincipalSign.cutoff hn ht ha true false z ≤ a)
    (x : C(Ioo a b, Fin (properPhysicalData hn ht ha true z).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (catalogRoot n true z)
      (IntegralMixedCausalRecordPlanBits.count (catalogRoot n true z)) le_rfl u.val (x u))
    (u v : Ioo a b) : rankHolds hn ht ha z hc code u.val (x u) ↔
      rankHolds hn ht ha z hc code v.val (x v) := by
  have H (power : Fin 3) (eps : Bool) : rankValue hn ht ha power eps z hc u.val (x u) =
      rankValue hn ht ha power eps z hc v.val (x v) := by
    unfold rankValue
    apply permanencesMinusVariations_congr
    simp only [List.map_map]
    apply List.map_congr_left
    intro j _
    simpa only [Function.comp_apply] using CoefficientMarkedRecordProperPrincipalLex.rank_lex_on_root_curve hn ht ha
      z hc hg ha0 x hx power eps j u v
  unfold rankHolds
  rw [H 0 false, H 2 false, H 1 false, H 2 true, H 1 true]

end LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessGuards
