/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCoordinateHeadActual
public import LeanCanny.Encoding.IntegralMixedRoadmapProperPrincipalCatalog
public import LeanCanny.Algebra.IntegralMixedFramedCutSourcePlanning
/-! # Original proper-row records select the constructed saved head -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCoordinateHead
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedNormalizationBits (planned plannedPlan plannedData)

theorem heads_planned (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) (key : List Bool) (d e : ℕ) :
    HEq (heads ((IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
      (plannedData P D H L F C)).state key)
      ((IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
        (plannedData P D H L F C)).birth_bound key)
      ((IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
        (plannedData P D H L F C)).rule key) d e)
      (heads ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule key) d e) := by
  have HR := congrArg (fun s => s.rule) (IntegralMixedFramedCutPlanning.selection P D H L F C key)
  exact heads_transport _ _ _ _ _ _ rfl rfl rfl rfl HEq.rfl rfl HEq.rfl (heq_of_eq HR) d e

theorem rule_offset_heq {a b : ℕ} (r : IntegralMixedCriticalSweep.Rule a) (t : IntegralMixedCriticalSweep.Rule b)
    (en : a = b) (hr : HEq r t) : r.critical.offset.val = t.critical.offset.val := by
  cases en
  cases eq_of_heq hr
  rfl

theorem at_mod_heq {a b m k : ℕ}
    (f : Fin (a+1) → Polynomial (MvPolynomial (Fin (m+1)) ℤ))
    (g : Fin (b+1) → Polynomial (MvPolynomial (Fin (k+1)) ℤ))
    (ha : a = b) (hm : m = k) (hf : HEq f g) (j : ℕ) :
    HEq (f ⟨j%(a+1), Nat.mod_lt _ (Nat.succ_pos _)⟩)
      (g ⟨j%(b+1), Nat.mod_lt _ (Nat.succ_pos _)⟩) := by
  cases ha
  cases hm
  cases eq_of_heq hf
  rfl

theorem heads_planned_at (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) (key : List Bool) (d e j : ℕ) :
    HEq (heads ((IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
      (plannedData P D H L F C)).state key)
      ((IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
        (plannedData P D H L F C)).birth_bound key)
      ((IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
        (plannedData P D H L F C)).rule key) d e
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate
        (IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
          (plannedData P D H L F C)) key j))
      (heads ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule key) d e
        (IntegralMixedCoordinateCoefficientSnapshot.coordinate (IntegralMixedFramedHistoryFamilyBits.family P D H) key j)) := by
  have HR := congrArg (fun s => s.rule) (IntegralMixedFramedCutPlanning.selection P D H L F C key)
  change (IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
    (plannedData P D H L F C)).rule key = (IntegralMixedFramedHistoryFamilyBits.family P D H).rule key at HR
  have HD : (IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
      (plannedData P D H L F C)).ambient key-
      ((IntegralMixedFramedHistoryFamilyBits.family (planned P L F C) (plannedPlan P D L F C)
        (plannedData P D H L F C)).rule key).critical.offset.val =
      (IntegralMixedFramedHistoryFamilyBits.family P D H).ambient key-
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule key).critical.offset.val := by
    change P.ambient (pairFst key)-_ = P.ambient (pairFst key)-_
    rw [HR]
  exact at_mod_heq _ _ HD rfl (heads_planned P D H L F C key d e) j

theorem packed_head (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (parent : List Bool → List Bool)
    (d e : List Bool → ℕ) (q : List Bool) :
    HEq (IntegralMixedFramedCoordinatePackedBits.head P D H parent d e q)
      (heads ((IntegralMixedFramedHistoryFamilyBits.family P D H).state (IntegralMixedVirtualTaskBits.saved P (parent q)))
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound _)
        ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule _) (d q) (e q)
        (IntegralMixedCoordinateCoefficientSnapshot.coordinate (IntegralMixedFramedHistoryFamilyBits.family P D H)
          (IntegralMixedVirtualTaskBits.saved P (parent q)) (get P .slot13 (parent q)))) := by
  have HC : IntegralMixedFramedAllCoordinateSourceBits.horizon P (parent q) =
      (IntegralMixedFramedHistoryFamilyBits.family P D H).cap (IntegralMixedVirtualTaskBits.saved P (parent q)) := by
    change P.cap (RankedHistoryTask.root (parent q))+1 =
      P.cap (pairFst (IntegralMixedVirtualTaskBits.saved P (parent q)))+1
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  unfold IntegralMixedFramedCoordinatePackedBits.head heads
  rw [HC]
  rfl

noncomputable def indexedHead (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) (d e j : ℕ) :=
  heads ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
    ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule key) d e
    (IntegralMixedCoordinateCoefficientSnapshot.coordinate (IntegralMixedFramedHistoryFamilyBits.family P D H) key j)

theorem indexedHead_congr (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) {key key' : List Bool} (hk : key = key') (d e j : ℕ) :
    HEq (indexedHead P D H key d e j) (indexedHead P D H key' d e j) := by
  cases hk
  rfl

end LeanCanny.Algebra.CoefficientMixedCoordinateHead

namespace LeanCanny.Encoding.CoefficientMarkedRecordCoordinateHead
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan CoefficientMarkedRecordPrefix.cut CoefficientMarkedRecordNative.cut

theorem coordinate_count_eq (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) (aux : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3-(rule hn ht ha ctx k).critical.offset.val =
      (actualFamily hn ht ha R).ambient (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)-
        ((actualFamily hn ht ha R).rule (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)).critical.offset.val := by
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let cR := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  have HT := CoefficientMarkedRecordBirthSpecialization.cut_transport hn ht ha ctx R
    (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) (IntegralMixedCausalRecordPlanBits.code ctx k)
  have HO := congrArg (fun c : IntegralMixedCausalRecordBits.Cut (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx R)
    (CoefficientMarkedIntegerBirth.width hn ht ha ctx) => c.critical.offset.val) HT
  have HR := CoefficientMixedCoordinateHead.rule_offset_heq
    (cR.rule (commonDenominator x) (commonDenominator_ne_zero x))
    ((actualFamily hn ht ha R).rule (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux))
    (CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k aux)
    (CoefficientMarkedRecordRuleSelection.rule_heq hn ht ha ctx R k hk hc aux)
  change (rule hn ht ha ctx k).critical.offset.val = cR.critical.offset.val at HO
  change cR.critical.offset.val = _ at HR
  rw [HO, HR, CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k aux]

theorem specializes_family_at (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (aux : List Bool) (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (d e j : ℕ) :
    HEq ((polynomial hn ht ha ctx k ⟨j%_, Nat.mod_lt _ (Nat.succ_pos _)⟩ d e).map
      (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))))
      (CoefficientMixedCoordinateHead.heads
        ((actualFamily hn ht ha R).state (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux))
        ((actualFamily hn ht ha R).birth_bound _) ((actualFamily hn ht ha R).rule _) d e
        (IntegralMixedCoordinateCoefficientSnapshot.coordinate (actualFamily hn ht ha R)
          (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) j)) := by
  exact CoefficientMixedCoordinateHead.at_mod_heq _ _
    (coordinate_count_eq hn ht ha ctx R k hk hc aux)
    (CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk.le aux)
    (specializes_family hn ht ha ctx R k hk hc aux hR d e) j

end LeanCanny.Encoding.CoefficientMarkedRecordCoordinateHead

namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)

def catalogStage (z : List Bool) := IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1

include hn ht ha hR0 in
theorem catalog_stage_code (mean : Bool) (z : List Bool) :
    IntegralMixedCausalRecordPlanBits.code (catalogRoot n mean z) (catalogStage z) = catalogCode n mean z := by
  have HR : IntegralMixedCausalRecordPlanBits.records (catalogRoot n mean z) = raw hn ht ha hR0 mean z := by
    rw [← root_catalog hn ht ha hR0 mean z]
    simp only [IntegralMixedCausalRecordPlanBits.records, root, pairFst_pair, pairSnd_pair]
  unfold IntegralMixedCausalRecordPlanBits.code catalogStage
  rw [HR, raw_last, code_catalog]

include hn ht ha hR0 in
theorem catalog_stage_fit (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    catalogStage z < IntegralMixedCausalRecordPlanBits.count (catalogRoot n mean z) := by
  have HC := root_count hn ht ha hR0 mean z hc
  rw [root_catalog] at HC
  rw [HC]
  exact Nat.sub_lt hc (by decide)

theorem catalog_code_cut (mean : Bool) (z : List Bool) :
    IntegralMixedUnitRecordCode.critical (catalogCode n mean z) = false := by
  cases mean <;> rfl

include hn ht ha hR0 in
theorem catalog_stage_key (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (aux : List Bool) :
    CoefficientMarkedRecordRowLayout.key (n := n) (catalogRoot n mean z) (catalogStage z) aux =
      IntegralMixedFramedHistoryFamilyBits.keyAt (catalogRoot n mean z) (catalogCreating n z) aux := by
  unfold CoefficientMarkedRecordRowLayout.key
  rw [CoefficientMarkedPreludeActual.indices_length]
  congr 1
  have HN := root_number hn ht ha hR0 mean z
  rw [root_catalog, initial_catalog] at HN
  rw [HN]
  unfold catalogStage catalogCreating IntegralMixedRoadmapBadProbePacket.creating
  omega

noncomputable def catalogParameter (mean : Bool) (z : List Bool) :=
  2^(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width (catalogRoot n mean z)-1

noncomputable def properHead (mean : Bool) (z : List Bool) :=
  CoefficientMarkedRecordCoordinateHead.polynomial hn ht ha (catalogRoot n mean z) (catalogStage z)
    ⟨relativeCoordinate z%_, Nat.mod_lt _ (Nat.succ_pos _)⟩
    (catalogDegree hn ht ha mean z) (catalogParameter hn ht ha mean z)

local notation "PC" => IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha
  (IntegralMixedOriginalRegularSource.radius_binary hR0)
local notation "DC" => IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha
  (IntegralMixedOriginalRegularSource.radius_binary hR0)
local notation "HC" => IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha
  (IntegralMixedOriginalRegularSource.radius_binary hR0)

theorem proper_head_specializes (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (catalogRoot n mean z) ≤
      IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)) :
    HEq ((properHead hn ht ha mean z).map (MvPolynomial.map
      (Polynomial.evalRingHom ((2 : ℤ)^IntegralMixedOriginalRegularSource.radius R0 (catalogRoot n mean z)))))
      (IntegralMixedFramedCoordinatePackedBits.head PC DC HC (parent hn ht ha hR0 mean)
        (IntegralMixedSelectedCoordinateHead.fullDegree PC (IntegralMixedFramedHistoryFamilyBits.family PC DC HC)
          (parent hn ht ha hR0 mean))
        (IntegralMixedSelectedCoordinateHead.fullParameter PC (parent hn ht ha hR0 mean)) z) := by
  let ctx := catalogRoot n mean z
  let k := catalogStage z
  let aux := BinaryNatCode.encode 2
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux
  let P := IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D := IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha (IntegralMixedOriginalRegularSource.radius R0)
  let H := IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha (IntegralMixedOriginalRegularSource.radius R0)
  let d := catalogDegree hn ht ha mean z
  let e := catalogParameter hn ht ha mean z
  have hk := catalog_stage_fit hn ht ha hR0 mean z hc
  have hcut : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false := by
    rw [catalog_stage_code hn ht ha hR0 mean z]
    exact catalog_code_cut mean z
  have HK : key = IntegralMixedVirtualTaskBits.saved PC (parent hn ht ha hR0 mean z) := by
    have HP := parentKey_eq hn ht ha hR0 mean z hc
    rw [parent_context, root_catalog, creating_catalog] at HP
    change key = parentKey hn ht ha hR0 mean z
    exact (catalog_stage_key hn ht ha hR0 mean z hc aux).trans HP.symm
  have HM := CoefficientMarkedRecordCoordinateHead.specializes_family_at hn ht ha ctx
    (IntegralMixedOriginalRegularSource.radius R0) k hk hcut aux hR d e (relativeCoordinate z)
  change HEq ((properHead hn ht ha mean z).map _)
    (CoefficientMixedCoordinateHead.indexedHead P D H key d e (relativeCoordinate z)) at HM
  have HP := CoefficientMixedCoordinateHead.heads_planned_at P D H (fun _ => 3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0))
    key d e (relativeCoordinate z)
  change HEq (CoefficientMixedCoordinateHead.indexedHead PC DC HC key d e (relativeCoordinate z))
    (CoefficientMixedCoordinateHead.indexedHead P D H key d e (relativeCoordinate z)) at HP
  have HT := HM.trans (HP.symm.trans (CoefficientMixedCoordinateHead.indexedHead_congr PC DC HC HK d e (relativeCoordinate z)))
  have HG := (rank_row_good_iff hn ht ha hR0 z).mpr hg
  have HD : IntegralMixedSelectedCoordinateHead.fullDegree PC (IntegralMixedFramedHistoryFamilyBits.family PC DC HC)
      (parent hn ht ha hR0 mean) z = d := by
    cases mean
    · exact near_degree_catalog_of_count hn ht ha hR0 z hc HG
    · exact rank_degree_catalog_of_count hn ht ha hR0 z hc HG
  have HE : IntegralMixedSelectedCoordinateHead.fullParameter PC (parent hn ht ha hR0 mean) z = e := by
    have HB : IntegralMixedPhysicalMarkedPlan.bank hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false =
        IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) := rfl
    have HX := (congrArg (fun B : IntegralFramedBankQuery.Bank =>
      IntegralMixedSelectedCoordinateHead.fullParameter B.parameters (parent hn ht ha hR0 mean) z) HB).symm.trans
        (parameter_catalog hn ht ha hR0 mean z)
    exact HX
  have HJ : get PC .slot13 (parent hn ht ha hR0 mean z) = relativeCoordinate z := by
    have HJ := parent_coordinate hn ht ha hR0 mean z HG
    change get PC .slot13 _ = _ at HJ
    exact HJ
  have HX := CoefficientMixedCoordinateHead.packed_head PC DC HC (parent hn ht ha hR0 mean)
    (IntegralMixedSelectedCoordinateHead.fullDegree PC (IntegralMixedFramedHistoryFamilyBits.family PC DC HC)
      (parent hn ht ha hR0 mean)) (IntegralMixedSelectedCoordinateHead.fullParameter PC (parent hn ht ha hR0 mean)) z
  change HEq _ (CoefficientMixedCoordinateHead.indexedHead PC DC HC
    (IntegralMixedVirtualTaskBits.saved PC (parent hn ht ha hR0 mean z)) _ _ _) at HX
  rw [HD, HE, HJ] at HX
  exact HT.trans HX.symm

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
