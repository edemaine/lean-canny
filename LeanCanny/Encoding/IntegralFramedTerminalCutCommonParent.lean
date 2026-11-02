/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutSign
public import LeanCanny.Encoding.IntegralFramedTerminalCutReadback
public import LeanCanny.Encoding.IntegralFramedCompleteSuffix
public import LeanCanny.Computation.FiniteCoefficientSignScan
/-! # Every terminal coefficient probe uses one literal parent interpretation -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutCommonParent
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralFramedTerminalCutTest.value

private theorem extend_fin {m : ℕ} (z : Fin m→ℝ) (i : Fin m) :
    IntegralMixedFramedBankObservation.extend z i.val=z i := by
  simp only [IntegralMixedFramedBankObservation.extend,dite_eq_left i.isLt]

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (key : List Bool→List Bool) (hpos : ∀ q,0<(family P D H).birth (key q))
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "delta" => IntegralFramedTerminalCutTest.count P D H key c-IntegralMixedCutSource.Family.birth G parent
local notation "z" => IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv
local notation "sample" => Subtype.val (SquareSampleCompleteVertices.candidate (IntegralFramedCompleteSquare.input P D H L F C hs key hpos) c w hv)
local notation "T" => IntegralFramedTerminalCutTest.source P D H L F C hs key hpos hFpos hf

variable (hfit : (family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)≤IntegralFramedTerminalCutTest.count P D H key c)
  (φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
  (hφ : ∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.generator i)=
    IntegralFramedCompleteSuffix.joint P D H L F C hs key hpos c w hv
      (i.val+(IntegralFramedTerminalCutTest.count P D H key c-(family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)))^
    UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
      (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P c)) ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)) i)

include ha hfit hφ hv in
theorem evaluation (e k : ℕ) (he : e≤2^P.width (RankedHistoryTask.root c)) (hk : k≤2^P.width (RankedHistoryTask.root c)) :
    ((T).polynomial c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))).eval₂ (Int.castRingHom ℝ)
      (fun i=>sample (Fin.cast ((T).dimension c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)))
        (FixedWidthSuffixLiftBits.shift ((T).newer c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))) i)))=
      φ ((IntegralMixedRelativeCuts.factor old bound rule (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e) := by
  let d:=pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)
  have HA : IntegralFramedTerminalCutTest.arity P D H key c d=(G).birth parent := by
    rw [IntegralFramedTerminalCutTest.arity,IntegralFramedTerminalCutTest.oldArity_parent,Nat.min_eq_left hfit]
  dsimp only [d] at HA
  have HC : (fun i : Fin ((T).arity c d)=>sample (Fin.cast ((T).dimension c d)
        (FixedWidthSuffixLiftBits.shift ((T).newer c d) i)))=
      (fun i=>z (i.val+((T).newer c d))) := by
    funext i
    have HX:=extend_fin sample (Fin.cast ((T).dimension c d) (FixedWidthSuffixLiftBits.shift ((T).newer c d) i))
    change z (((T).newer c d)+i.val)=_ at HX
    exact HX.symm.trans (congrArg z (Nat.add_comm _ _))
  change ((T).polynomial c d).eval₂ (Int.castRingHom ℝ) _=_
  rw [HC]
  apply IntegralFramedTerminalCutTest.polynomial_evaluation P D H key c e k ha he hk
    (by rw [IntegralFramedTerminalCutTest.oldArity_parent]; exact hfit) z φ
  simpa only [HA] using hφ

include ha hfit hφ hv in
theorem zero_iff (e k : ℕ) (he : e≤2^P.width (RankedHistoryTask.root c)) (hk : k≤2^P.width (RankedHistoryTask.root c)) :
    FiniteCoefficientSignScan.Zero (IntegralFramedTerminalCutTest.value P D H L F C hs hFpos hf key hpos) (pair c w) e k ↔
      φ ((IntegralMixedRelativeCuts.factor old bound rule (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e)=0 := by
  unfold FiniteCoefficientSignScan.Zero FiniteCoefficientSignScan.query
  have HP:=IntegralFramedTerminalCutTest.packet P D H L F C hs hFpos hf key hpos c w
    (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)) hv
  have HE:=evaluation P D H L F C hs hFpos hf key hpos c w hv ha hfit φ hφ e k he hk
  have HV:=HP.trans (congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) HE)
  rw [HV]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff

end LeanCanny.Encoding.IntegralFramedTerminalCutCommonParent
