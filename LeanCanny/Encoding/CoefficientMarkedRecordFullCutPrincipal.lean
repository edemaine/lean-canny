/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutWindow
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipal
public import LeanCanny.Algebra.IntegralMixedFramedFullCutIntervalFamily
/-! # Literal full-cut endpoint principal families over the radius parameter -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutPrincipal
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open CoefficientTarskiParameterQueries
open IntegralMixedAuxiliaryMarkedRecordPlan (certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def head (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :=
  pairLift true (CoefficientMarkedRecordFullCutTerminalHead.polynomial hn ht ha ctx k hk)
noncomputable def query (ctx : List Bool) (index : ℕ) (power : Fin 3) (negative : Bool) :=
  pairLift false (CoefficientMarkedRecordFullCutWindow.polynomial hn ht ha ctx index negative)^power.val
noncomputable def polynomial (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (index : ℕ) (power : Fin 3) (negative : Bool) (j : ℕ) :=
  let d := max 1 (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree
  principal (head hn ht ha ctx k hk) (query hn ht ha ctx index power negative) d (d-1) (d+2) j

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "PC" => certifiedParameters hn ht ha hR
local notation "DC" => certifiedPlan hn ht ha hR
local notation "HC" => certifiedData hn ht ha hR
local notation "PAR" => CoefficientMarkedRecordRawCutMetadata.parent hn ht ha hR
local notation "TERM" => CoefficientMarkedRecordRawCutMetadata.terminal (n := n)
local notation "F" => IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha
local notation "C" => IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR
local notation "HS" => IntegralMixedAuxiliaryMarkedRecordPlan.certifiedInputs hn ht ha hR

noncomputable def nativeFamily (ctx : List Bool) (k index : ℕ) (power : Fin 3) (negative : Bool) :=
  IntegralMixedFramedFullCutIntervalFamily.family PC DC HC (fun _ => 3) F C HS
    (fun _ => PAR ctx k) (fun _ => TERM ctx)
    (fun _ => (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree)
    (fun _ => index) (fun _ => power) negative

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem head_map (ctx : List Bool) (k index : ℕ) (power : Fin 3) (negative : Bool)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq ((head hn ht ha ctx k hk).map (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))))
      ((nativeFamily hn ht ha hR ctx k index power negative).head []) := by
  have HM := CoefficientMarkedRecordFullCutTerminalHead.specializes hn ht ha hR ctx k hk hc hlarge
  have HA := (CoefficientMarkedRecordRawCutMetadata.terminal_count hn ht ha hR ctx).symm
  unfold head
  rw [pairLift_map]
  have HP := pair_heq true _ _ HA HM
  dsimp only [nativeFamily, IntegralMixedFramedFullCutIntervalFamily.family,
    IntegralMixedFramedFullCutIntervalFamily.head, IntegralMixedFramedFullCutIntervalFamily.arity,
    FixedWidthBivariateParameterPairBits.lift]
  dsimp only [pairLift] at HP
  exact HP

theorem query_map (ctx : List Bool) (k index : ℕ) (power : Fin 3) (negative : Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq ((query hn ht ha ctx index power negative).map (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))))
      ((nativeFamily hn ht ha hR ctx k index power negative).query []) := by
  have HM := CoefficientMarkedRecordFullCutWindow.specializes hn ht ha hR ctx index negative hlarge
  have HA := (CoefficientMarkedRecordRawCutMetadata.terminal_count hn ht ha hR ctx).symm
  unfold query
  rw [Polynomial.map_pow, pairLift_map]
  have HP := pair_heq false _ _ HA HM
  have HQ := polynomial_pow_heq _ _ (congrArg (fun m => 1+(m+1)) HA) HP power.val
  dsimp only [nativeFamily, IntegralMixedFramedFullCutIntervalFamily.family,
    IntegralMixedFramedFullCutIntervalFamily.query, IntegralMixedFramedFullCutIntervalFamily.baseQuery,
    IntegralMixedFramedFullCutIntervalFamily.arity, FixedWidthBivariateParameterPairBits.lift]
  dsimp only [pairLift] at HQ
  exact HQ

/-- These are the installed full-cut statistics, including both unused dummy
axes and the exact epsilon-window sign; no replacement normalization occurs. -/
theorem specializes (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (index : ℕ) (power : Fin 3) (negative : Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) (j : ℕ) :
    HEq (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))
      (polynomial hn ht ha ctx k hk index power negative j))
      (FixedWidthTarskiPrincipalBits.polynomial (nativeFamily hn ht ha hR ctx k index power negative) [] j) := by
  let G := nativeFamily hn ht ha hR ctx k index power negative
  let d := max 1 (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree
  have HM : 1+(IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+1) = G.arity [] :=
    congrArg (fun m => 1+(m+1)) (CoefficientMarkedRecordRawCutMetadata.terminal_count hn ht ha hR ctx).symm
  have HD : d = G.degree [] := rfl
  have HS' : d-1 = G.seedDegree [] := rfl
  have HB : d+2 = G.bound [] := rfl
  unfold polynomial
  rw [principal_map]
  exact principal_heq _ _ (G.head []) (G.query []) d (G.degree []) (d-1) (G.seedDegree [])
    (d+2) (G.bound []) j HM (head_map hn ht ha hR ctx k index power negative hk hc hlarge)
    (query_map hn ht ha hR ctx k index power negative hlarge) HD HS' HB

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutPrincipal
