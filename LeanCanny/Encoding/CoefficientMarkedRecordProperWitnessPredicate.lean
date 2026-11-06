/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessGuards
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldListTransport
/-! # One actual coordinate-witness predicate shares both complete prepared tuples -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessPredicate
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open IntegralMixedRoadmapProperRow CoefficientMarkedRecordProperWitnessLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family

noncomputable abbrev OriginalPoint (z : List Bool) :=
  CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (leftContext z)
noncomputable abbrev PreparedPoint (mean : Bool) (z : List Bool) :=
  CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (preparedContext n mean z)

/-- BOTH field scans use the same complete ordinary/mean tuples as their
native infinitesimal guards. No interpreting hom or preselected word occurs. -/
noncomputable def At (right : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (code : List Bool) (β : ℝ)
    (original : OriginalPoint hn ht ha z) (ordinary : PreparedPoint hn ht ha false z)
    (mean : PreparedPoint hn ht ha true z) : Prop :=
  rankRowSyntax n z ∧ IntegralMixedRoadmapProperRowWitness.SideGood right z ∧
  CoefficientMarkedRecordProperWitnessGuards.nearHolds hn ht ha right z hc code β ordinary ∧
  CoefficientMarkedRecordProperWitnessGuards.rankHolds hn ht ha z hc code β mean ∧
  CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha (leftContext z) (preparedContext n false z) (table n z)
    β original ordinary ∧
  CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha (leftContext z) (preparedContext n true z) (table n z)
    β original mean

noncomputable def Holds (right : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (code : List Bool) (β : ℝ)
    (original : OriginalPoint hn ht ha z) : Prop :=
  ∃ ordinary : PreparedPoint hn ht ha false z, ∃ mean : PreparedPoint hn ht ha true z,
    CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (catalogRoot n false z)
      (IntegralMixedCausalRecordPlanBits.count (catalogRoot n false z)) le_rfl β ordinary ∧
    CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (catalogRoot n true z)
      (IntegralMixedCausalRecordPlanBits.count (catalogRoot n true z)) le_rfl β mean ∧
    At hn ht ha right z hc code β original ordinary mean

theorem radius_prepared (R : List Bool → ℕ) (mean : Bool) (z : List Bool) :
    IntegralMixedOriginalRegularSource.radius R (pairFst (leftContext z)) =
      IntegralMixedOriginalRegularSource.radius R (catalogRoot n mean z) := by
  simp only [IntegralMixedOriginalRegularSource.radius, leftContext, IntegralMixedRoadmapAtomic.context,
    IntegralMixedRoadmapAtomic.root, catalogRoot, IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate, pairFst_pair]

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR) false

theorem witness_iff (right : Bool) (z baseWord ownO ownM code : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hlargeL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst (leftContext z)) ≤
      IntegralMixedOriginalRegularSource.radius R (pairFst (leftContext z)))
    (hlargeP : ∀ mean, CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius R (catalogRoot n mean z))
    (hwL : SquareSampleCompleteVertices.Valid S (leftContext z) baseWord)
    (hwO : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false) (request z baseWord) ownO)
    (hwM : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true) (request z baseWord) ownM)
    (original : OriginalPoint hn ht ha z) (ordinary : PreparedPoint hn ht ha false z) (mean : PreparedPoint hn ht ha true z)
    (hjL : HEq (SquareSampleCompleteVertices.candidate S (leftContext z) baseWord hwL).val original)
    (hjO : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR false)
      (request z baseWord) ownO hwO).val ordinary)
    (hjM : HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR true)
      (request z baseWord) ownM hwM).val mean) :
    IntegralMixedRoadmapProperRowWitness.packet (request z baseWord) ownO ownM code ∈
      IntegralMixedRoadmapProperRowWitness.language hn ht ha hR right ↔
    At hn ht ha right z hc code
      ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R (pairFst (leftContext z))) original ordinary mean := by
  let hwP (m : Bool) : SquareSampleCompleteVertices.Valid S (preparedContext n m z) (if m then ownM else ownO) := by
    cases m
    · exact (CoefficientMarkedRecordProperWitnessContext.valid_prepared hn ht ha hR false z baseWord ownO).mp hwO
    · exact (CoefficientMarkedRecordProperWitnessContext.valid_prepared hn ht ha hR true z baseWord ownM).mp hwM
  let rawP (m : Bool) : PreparedPoint hn ht ha m z := by
    cases m
    · exact ordinary
    · exact mean
  have hJP (m : Bool) : HEq (SquareSampleCompleteVertices.candidate S (preparedContext n m z)
      (if m then ownM else ownO) (hwP m)).val (rawP m) := by
    cases m
    · exact (CoefficientMarkedRecordProperWitnessContext.candidate_prepared hn ht ha hR false z baseWord ownO hwO (hwP false)).symm.trans hjO
    · exact (CoefficientMarkedRecordProperWitnessContext.candidate_prepared hn ht ha hR true z baseWord ownM hwM (hwP true)).symm.trans hjM
  have HF (m : Bool) : IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR m
      (IntegralMixedRoadmapProperRowWitness.packet (request z baseWord) ownO ownM code) ∈
        IntegralMixedPhysicalFieldEqualityList.language hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR) ↔
      CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha (leftContext z) (preparedContext n m z) (table n z)
        ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R (pairFst (leftContext z))) original (rawP m) := by
    rw [field_packet hn ht ha hR]
    exact CoefficientMarkedRecordFieldListIncidence.language_iff hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR)
      (leftContext z) baseWord (preparedContext n m z) (if m then ownM else ownO) (table n z)
      (by simpa only [preparedContext, pairFst_pair] using radius_prepared (n := n) R m z)
      hlargeL (by simpa only [preparedContext, pairFst_pair] using hlargeP m) hwL (hwP m)
      original (rawP m) hjL (hJP m)
  have HN := CoefficientMarkedRecordProperWitnessGuards.near_native_iff hn ht ha hR right z baseWord hc hg
    (hlargeP false) ownO code hwO ordinary hjO
  have HR := CoefficientMarkedRecordProperWitnessGuards.rank_native_iff hn ht ha hR z baseWord hc hg
    (hlargeP true) ownM code hwM mean hjM
  rw [← radius_prepared (n := n) R false z] at HN
  rw [← radius_prepared (n := n) R true z] at HR
  simp only [IntegralMixedRoadmapProperRowWitness.language, Set.mem_ofPred_eq, IntegralMixedRoadmapProperRowWitness.key,
    IntegralMixedRoadmapProperRowWitness.query, IntegralMixedRoadmapProperRowWitness.ownWord,
    IntegralMixedRoadmapProperRowWitness.rank, IntegralMixedRoadmapProperRowWitness.packet,
    Bool.false_eq_true, ite_false, ite_true, pairFst_pair, pairSnd_pair, At]
  exact and_congr (native_row_good hn ht ha hR z baseWord) ((side_request right z baseWord).and
    (HN.and (HR.and ((HF false).and (HF true)))))

end LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessPredicate
