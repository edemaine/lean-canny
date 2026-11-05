/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordRawCutMetadata
/-! # A constructed full stored-factor head on its actual full scalar suffix -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutTerminalHead
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open CoefficientFullCutHeadQueries
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem terminal_transport {m k N M : ℕ} (S T B C : ℕ)
    (p : Polynomial (MvPolynomial (Fin m) ℤ)) (q : Polynomial (MvPolynomial (Fin k) ℤ))
    (d e : ℕ) (h : m ≤ N) (h' : k ≤ M) (hS : S = T) (hB : B = C) (hm : m = k) (hN : N = M)
    (hp : HEq p q) (hd : d = e) :
    HEq (terminalHead h (UniformIntegralPowerSchedule.weights S B m) p d)
      (terminalHead h' (UniformIntegralPowerSchedule.weights T C k) q e) := by
  cases hS
  cases hB
  cases hm
  cases hN
  cases eq_of_heq hp
  cases hd
  rfl

private theorem polynomial_at_parent (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (parent : List Bool → List Bool) (q key : List Bool)
    (he : key = IntegralMixedVirtualTaskBits.saved P (parent q)) :
    HEq (CoefficientMarkedRecordFullCutHead.selectedPolynomial P D H key) (nativePolynomial P D H parent q) := by
  cases he
  rfl

private theorem family_width (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family P D H).width key = P.width (pairFst key) := rfl

theorem fits {n : List Bool → ℕ} (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    CoefficientMarkedRecordCutSource.birth (n := n) ctx k ≤ IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx := by
  simp only [CoefficientMarkedRecordCutSource.birth, CoefficientMarkedRecordActual.codes_length,
    CoefficientMarkedPreludeActual.indices_length, IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  omega

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def polynomial (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :=
  terminalHead (fits (n := n) ctx k hk)
    (UniformIntegralPowerSchedule.weights (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (2^CoefficientMarkedIntegerBirth.width hn ht ha ctx) (CoefficientMarkedRecordCutSource.birth (n := n) ctx k))
    (CoefficientMarkedRecordFullCutHead.polynomial hn ht ha ctx k) (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed CoefficientMarkedRecordPrefix.build CoefficientMarkedRecordNative.run
  CoefficientMarkedRecordFullCutHead.selectedPolynomial CoefficientMarkedRecordFullCutHead.polynomial

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "PC" => certifiedParameters hn ht ha hR
local notation "DC" => certifiedPlan hn ht ha hR
local notation "HC" => certifiedData hn ht ha hR
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family PC DC HC
local notation "PAR" => CoefficientMarkedRecordRawCutMetadata.parent hn ht ha hR
local notation "TERM" => CoefficientMarkedRecordRawCutMetadata.terminal (n := n)

theorem specializes (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) :
    HEq ((polynomial hn ht ha ctx k hk).map (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))))
      (IntegralMixedFramedFullCutTerminalHead.polynomial PC DC HC
        (fun _ => PAR ctx k) (fun _ => TERM ctx) (fun _ => (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree) []) := by
  let key := IntegralMixedVirtualTaskBits.saved PC (PAR ctx k)
  have HS := CoefficientMarkedRecordRawCutMetadata.parent_saved hn ht ha hR ctx k hk
  have HR : pairFst key = ctx := by
    rw [show key = CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2) from HS]
    exact CoefficientMarkedRecordRowLayout.key_root _ _ _
  have HP := CoefficientMarkedRecordFullCutHead.polynomial_specializes_certified hn ht ha ctx hR k hk hc
    (BinaryNatCode.encode 2) hlarge
  have HP' := polynomial_at_parent PC DC HC (fun _ => PAR ctx k) [] _ HS.symm
  have HPfull := HP.trans HP'
  have HM : CoefficientMarkedRecordCutSource.birth (n := n) ctx k = (G).birth key :=
    (CoefficientMarkedRecordRawCutMetadata.parent_arity hn ht ha hR ctx k hk).symm
  have HN : IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx =
      (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (TERM ctx)).count :=
    (CoefficientMarkedRecordRawCutMetadata.terminal_count hn ht ha hR ctx).symm
  have Hcap : CoefficientMarkedRecordActual.horizon hn ht ha ctx = (PC).cap (pairFst key)+1 := by
    rw [HR]
    rfl
  have HW : 2^CoefficientMarkedIntegerBirth.width hn ht ha ctx = 2^(G).width key := by
    have HE := family_width PC DC HC key
    rw [HE, HR]
    rfl
  have HD := (CoefficientMarkedRecordRawCutMetadata.degree_clip hn ht ha hR ctx k hk hc).symm
  have HC' := CoefficientMarkedRecordRawCutMetadata.terminal_valid hn ht ha hR ctx k hk
  have HT := terminal_transport _ _ _ _ _ _ _ _ (fits (n := n) ctx k hk) HC' Hcap HW HM HN HPfull HD
  have HA := CoefficientMarkedRecordRawCutMetadata.parent_active hn ht ha hR ctx k hk
  have HNative := terminalHead_native PC DC HC (fun _ => PAR ctx k) (fun _ => TERM ctx)
    (fun _ => (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree) [] HA HC'
  unfold polynomial
  rw [terminalHead_map]
  exact HT.trans (heq_of_eq HNative)

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutTerminalHead
