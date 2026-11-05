/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutPrincipal
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusFullCutHead
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusCertifiedWindow
public import LeanCanny.Algebra.FixedWidthTarskiAffineMass
/-! # Original affine radius bounds for full-cut endpoint principals -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutPrincipalHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters certifiedParameters certifiedPlan certifiedData)
open IntegralMixedAuxiliaryMarkedRecordRadiusHeight (rawSlope rawOffset coordinateSlope coordinateOffset)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem pair_mass {m : ℕ} (keep : Bool) (p : Polynomial (MvPolynomial (Fin (m+1)) ℤ)) (i : ℕ) :
    MvMass.mass ((CoefficientTarskiParameterQueries.pairLift keep p).coeff i) ≤ MvMass.mass (p.coeff i) := by
  rw [CoefficientTarskiParameterQueries.pairLift, Polynomial.coeff_map]
  exact MvMass.rename_le _ _

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def headOffset (ctx : List Bool) := rawOffset hn ht ha ctx+
  ((parameters hn ht ha).cap ctx+1)*(parameters hn ht ha).width ctx+1
noncomputable def degree (ctx : List Bool) (k : ℕ) := max 1 (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree
noncomputable def slope (ctx : List Bool) (k : ℕ) :=
  let d := degree hn ht ha ctx k
  FixedWidthTarskiMass.principalSlope d (d-1) (d+2) (rawSlope hn ht ha ctx) (2*coordinateSlope hn ht ha ctx)
noncomputable def offset (ctx : List Bool) (k : ℕ) :=
  let d := degree hn ht ha ctx k
  FixedWidthTarskiMass.principalOffset d (d-1) (d+2)
    (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree 2
    (headOffset hn ht ha ctx) (2*coordinateOffset hn ht ha ctx+1)

theorem cut_degree_formula (ctx : List Bool) (k : ℕ) :
    (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree =
      Nat.fromBitsLE (IntegralMixedUnitRecordCode.field (IntegralMixedCausalRecordPlanBits.code ctx k) 9) %
        (IntegralMixedExceptionalBounds.auxiliaryCap ((parameters hn ht ha).ambient ctx+1)
          ((parameters hn ht ha).degree ctx)+1) := by
  change Nat.fromBitsLE _ % (IntegralMixedExceptionalBounds.auxiliaryCap _
    (CoefficientMarkedRecordPrefix.source (n := n) (t := t) ctx 0).degree+1) = _
  rw [CoefficientMarkedRecordPrefix.source, IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree]
  rfl

theorem cut_degree_binary {ctx : List Bool → List Bool} {k : List Bool → ℕ}
    (hctx : ctx ∈ FP) (hk : BinaryFn k) :
    BinaryFn (fun q => (CoefficientMarkedRecordCutSource.cut hn ht ha (ctx q) (k q)).degree) := by
  have HC : (fun q => IntegralMixedCausalRecordPlanBits.code (ctx q) (k q)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp (mem_FP_pair (mem_FP_comp hctx IntegralMixedCausalRecordPlanBits.records_FP)
      hk.bits_mem_FP) WordList.reader_FP) (fun q => by
      simp only [Function.comp_apply, WordList.reader, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits, IntegralMixedCausalRecordPlanBits.code])
  have HW : BinaryFn (fun q => Nat.fromBitsLE (IntegralMixedUnitRecordCode.field
      (IntegralMixedCausalRecordPlanBits.code (ctx q) (k q)) 9)) := BinaryFn.fromBits
    (mem_FP_comp (f := fun q => IntegralMixedCausalRecordPlanBits.code (ctx q) (k q))
      (g := fun w => WordList.get w 9) HC (IntegralMixedCommandHeaderBits.get_FP 9))
  have HA := IntegralMixedExceptionalBounds.auxiliaryCap_binary
    (((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).ambient.comp hctx).add (UnaryFn.const 1))
    ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).degree.comp hctx)
  exact (HW.mod (HA.add (BinaryFn.const 1))).of_eq (fun q => (cut_degree_formula hn ht ha (ctx q) (k q)).symm)

theorem degree_binary {ctx : List Bool → List Bool} {k : List Bool → ℕ}
    (hctx : ctx ∈ FP) (hk : BinaryFn k) : BinaryFn (fun q => degree hn ht ha (ctx q) (k q)) :=
  (BinaryFn.ite ((BinaryFn.const 1).le (cut_degree_binary hn ht ha hctx hk))
    (cut_degree_binary hn ht ha hctx hk) (BinaryFn.const 1)).of_eq (fun _ => Nat.max_def.symm)

theorem headOffset_binary : BinaryFn (headOffset hn ht ha) :=
  ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset_binary hn ht ha).add
    ((BinaryFn.ofUnary ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.add (UnaryFn.const 1))).mul
      (BinaryFn.ofUnary (IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).width))).add (BinaryFn.const 1)

theorem slope_binary {ctx : List Bool → List Bool} {k : List Bool → ℕ}
    (hctx : ctx ∈ FP) (hk : BinaryFn k) : BinaryFn (fun q => slope hn ht ha (ctx q) (k q)) :=
  FixedWidthTarskiMass.principalSlope_binary (degree_binary hn ht ha hctx hk)
    ((degree_binary hn ht ha hctx hk).sub (BinaryFn.const 1))
    ((degree_binary hn ht ha hctx hk).add (BinaryFn.const 2))
    ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope_binary hn ht ha).comp hctx)
    ((BinaryFn.const 2).mul ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateSlope_binary hn ht ha).comp hctx))

theorem offset_binary {ctx : List Bool → List Bool} {k : List Bool → ℕ}
    (hctx : ctx ∈ FP) (hk : BinaryFn k) : BinaryFn (fun q => offset hn ht ha (ctx q) (k q)) :=
  FixedWidthTarskiMass.principalOffset_binary (degree_binary hn ht ha hctx hk)
    ((degree_binary hn ht ha hctx hk).sub (BinaryFn.const 1))
    ((degree_binary hn ht ha hctx hk).add (BinaryFn.const 2))
    (cut_degree_binary hn ht ha hctx hk) (BinaryFn.const 2) ((headOffset_binary hn ht ha).comp hctx)
    (((BinaryFn.const 2).mul ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.coordinateOffset_binary hn ht ha).comp hctx)).add
      (BinaryFn.const 1))

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "PC" => certifiedParameters hn ht ha hR
local notation "DC" => certifiedPlan hn ht ha hR
local notation "HC" => certifiedData hn ht ha hR
local notation "PAR" => CoefficientMarkedRecordRawCutMetadata.parent hn ht ha hR
local notation "TERM" => CoefficientMarkedRecordRawCutMetadata.terminal (n := n)
local notation "F" => IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha
local notation "C" => IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR
local notation "HS" => IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha hR

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem native_head_mass (ctx : List Bool) (k index : ℕ) (negative : Bool) (i : ℕ) :
    MvMass.mass (((CoefficientMarkedRecordFullCutPrincipal.nativeFamily hn ht ha hR ctx k index 1 negative).head []).coeff i) ≤
      2^(rawSlope hn ht ha ctx*R ctx+headOffset hn ht ha ctx) := by
  have HM := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_full_cut_head_coefficient_mass hn ht ha hR
    (fun _ => PAR ctx k) (fun _ => TERM ctx) (fun _ => (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree) [] i
  have HR : pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (PAR ctx k)) = ctx := by
    simp only [IntegralMixedVirtualTaskBits.saved, pairFst_pair]
    exact CoefficientMarkedRecordRawCutMetadata.parent_root hn ht ha hR ctx k
  unfold IntegralMixedAuxiliaryMarkedRecordRadiusHeight.headOffset at HM
  rw [HR] at HM
  have HM' : MvMass.mass ((IntegralMixedFramedFullCutTerminalHead.polynomial PC DC HC
      (fun _ => PAR ctx k) (fun _ => TERM ctx)
      (fun _ => (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree) []).coeff i) ≤
      2^(rawSlope hn ht ha ctx*R ctx+headOffset hn ht ha ctx) := by
    simpa only [headOffset, Nat.zero_add, Nat.size_one] using HM
  exact (pair_mass true _ i).trans HM'

theorem native_query_mass (ctx : List Bool) (k index : ℕ) (negative : Bool) (i : ℕ) :
    MvMass.mass (((CoefficientMarkedRecordFullCutPrincipal.nativeFamily hn ht ha hR ctx k index 1 negative).query []).coeff i) ≤
      2^((2*coordinateSlope hn ht ha ctx)*R ctx+(2*coordinateOffset hn ht ha ctx+1)) := by
  have HM := IntegralMixedAuxiliaryMarkedRecordRadiusHeight.certified_window_coefficient_mass hn ht ha hR
    (fun _ => TERM ctx) (fun _ => index) negative [] i
  rw [show pairFst (TERM ctx) = ctx from CoefficientMarkedRecordRowLayout.key_root _ _ _] at HM
  change MvMass.mass (((CoefficientTarskiParameterQueries.pairLift false
    (IntegralMixedFramedWindowQuery.polynomial PC DC HC (fun _ => 3) F C HS
      (fun _ => TERM ctx) (fun _ => index) negative []))^1).coeff i) ≤ _
  rw [pow_one]
  exact (pair_mass false _ i).trans HM

/-- Power one is precisely the two-endpoint native NoBad comparison. Every
principal index and every endpoint index share the same original ceiling. -/
theorem principal_mass (ctx : List Bool) (k index : ℕ) (negative : Bool) (j : ℕ) :
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial
      (CoefficientMarkedRecordFullCutPrincipal.nativeFamily hn ht ha hR ctx k index 1 negative) [] j) ≤
      2^(slope hn ht ha ctx k*R ctx+offset hn ht ha ctx k) := by
  let G := CoefficientMarkedRecordFullCutPrincipal.nativeFamily hn ht ha hR ctx k index 1 negative
  let d := (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree
  have HP : (G.head []).natDegree ≤ d := IntegralMixedFramedFullCutIntervalFamily.head_outer_degree PC DC HC
    (fun _ => PAR ctx k) (fun _ => TERM ctx) (fun _ => d) []
  have HQ : (G.query []).natDegree ≤ 2 := IntegralMixedFramedFullCutIntervalFamily.query_outer_degree PC DC HC
    (fun _ => 3) F C HS (fun _ => TERM ctx) (fun _ => index) (fun _ => 1) negative []
  have HM := FixedWidthTarskiMass.principal_mass_direct G [] j d 2
    (rawSlope hn ht ha ctx*R ctx+headOffset hn ht ha ctx)
    ((2*coordinateSlope hn ht ha ctx)*R ctx+(2*coordinateOffset hn ht ha ctx+1)) HP HQ
    (native_head_mass hn ht ha hR ctx k index negative) (native_query_mass hn ht ha hR ctx k index negative)
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  exact FixedWidthTarskiMass.principalMass_affine _ _ _ _ _ _ _ _ _ _

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutPrincipalHeight
