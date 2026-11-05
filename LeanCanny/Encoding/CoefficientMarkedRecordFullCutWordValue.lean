/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutWordTuple
/-! # Native full-cut statistics are the computed principal permanences -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutWordValue
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial PrincipalSubresultant
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem value_principals (G : FixedWidthTarskiPrincipalBits.Family) (q : List Bool)
    (χ : MvPolynomial (Fin (G.arity q)) ℤ →+* (ℝ[X])[X]) :
    RealIteratedTarski.value ((G.head q).map χ) ((G.query q).map χ) (G.degree q) (G.bound q) (G.seedDegree q) =
      permanencesMinusVariations ((List.range (G.degree q+1)).reverse.map
        (fun j => RealIteratedTarski.lex (χ (FixedWidthTarskiPrincipalBits.polynomial G q j)))) := by
  unfold RealIteratedTarski.value
  apply congrArg permanencesMinusVariations
  apply List.map_congr_left
  intro j _
  unfold RealIteratedTarski.principal RealIteratedTarski.seed FixedWidthTarskiPrincipalBits.polynomial
  rw [PseudoRemainder.seed_map, signedPsc_map_map]

private theorem pmv_range_congr (d e : ℕ) (f g : ℕ → ℝ) (hd : d = e) (h : ∀ j, f j = g j) :
    permanencesMinusVariations ((List.range (d+1)).reverse.map f) =
      permanencesMinusVariations ((List.range (e+1)).reverse.map g) := by
  cases hd
  apply congrArg permanencesMinusVariations
  exact List.map_congr_left (fun j _ => h j)

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "CTX" => CoefficientMarkedRecordFullCutInstalled.context (n := n)
local notation "G" => CoefficientMarkedRecordFullCutInstalled.installedFamily hn ht ha hR

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed
  IntegralMixedPhysicalMarkedPlan.bank

noncomputable def statistic (side negative : Bool) (q w : List Bool) :=
  IntegralFramedFullCutIntervalStatistic.value (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha hR false) (B).key
    (IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR false) (IntegralMixedPhysicalCutOpenInterval.selected side)
    (B).positive (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR false)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR false) 1 negative (pair (pair q w) [])


theorem statistic_principals (side negative : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) q w) :
    statistic hn ht ha hR side negative q w =
      permanencesMinusVariations ((List.range ((G side 1 negative).degree q+1)).reverse.map
        (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordFullCutWordTuple.nativePrincipal hn ht ha hR side negative q w hv j))) := by
  have HV := IntegralFramedFullCutIntervalStatistic.value_at (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha hR false) (B).key
    (IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR false) (IntegralMixedPhysicalCutOpenInterval.selected side)
    (B).positive (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR false)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR false) 1 negative q w hv
  have HM := value_principals (G side 1 negative) q
    (IntegralMixedFramedTerminalTarskiSelected.specialization (B).parameters (B).plan (B).data (B).key q
      (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive q w hv))
  exact HV.trans HM

/-- Native value_at and the SAME declared principal range give the computed
formal statistic on this word's own complete tuple. -/
theorem value_eq (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (left right : ℕ) (side negative : Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) (w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) w)
    (z : Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count → ℝ)
    (hj : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) w hv).val z) :
    statistic hn ht ha hR side negative (CTX ctx k left right) w =
      permanencesMinusVariations ((List.range (CoefficientMarkedRecordFullCutPrincipalHeight.degree hn ht ha ctx k+1)).reverse.map
        (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordFullCutLex.principal hn ht ha ctx k hk
          (if side then right else left) negative j ((2 : ℝ)^R ctx) z))) := by
  have HD : (G side 1 negative).degree (CTX ctx k left right) = CoefficientMarkedRecordFullCutPrincipalHeight.degree hn ht ha ctx k :=
    congrArg (fun d => max 1 d) (CoefficientMarkedRecordFullCutInstalled.degree_context hn ht ha hR ctx k left right hk hc)
  have HP := pmv_range_congr _ _ _ _ HD (fun j => congrArg RealIteratedTarski.lex
    (CoefficientMarkedRecordFullCutWordTuple.principal_eq hn ht ha hR ctx k hk hc left right side negative hlarge w hv z hj j))
  exact (statistic_principals hn ht ha hR side negative (CTX ctx k left right) w hv).trans HP

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutWordValue
