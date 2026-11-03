/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedFullCutIntervalStatisticSpace
public import LeanCanny.Encoding.IntegralFramedFullCutIntervalStatisticValue
public import LeanCanny.Computation.PSPACEBoolean
/-! # Two native endpoint statistics test an open interval of a full cut factor -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedFullCutOpenInterval
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralMixedFramedFullCutHead (saved)
open IntegralFramedFullCutIntervalStatistic
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family RealIteratedTarski.value

theorem integerCode_injective : Function.Injective SignStatisticBits.integerCode :=by
  intro a b h
  have HP:=congrArg (fun w=>Nat.fromBitsLE (pairFst w)) h
  have HN:=congrArg (fun w=>Nat.fromBitsLE (pairSnd w)) h
  simp only [SignStatisticBits.integerCode,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] at HP HN
  omega

theorem constant_empty (p : ℝ[X]) (hp : p≠0) (hd : p.natDegree=0) (a b : ℝ) :
    ∀ r : ℝ, p.eval r = 0 → r ∉ Set.Ioo a b :=by
  intro r hr
  have HE:=eq_C_of_natDegree_eq_zero hd
  have HZ : p.coeff 0=0 :=by
    rw [HE,eval_C] at hr
    exact hr
  exact (hp (by rw [HE,HZ,map_zero])).elim

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (parent terminal : List Bool→List Bool) (d left right : List Bool→ℕ)
  (hpos : ∀q,0<(family P D H).birth (terminal q))
  (hf : ∀root,1≤F root) (hdefault : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)

noncomputable def endpoint (selected : List Bool→ℕ) (negative : Bool) (z : List Bool) :=
  SignStatisticBits.integerCode (value P D H L F C hs parent terminal d selected hpos hf hdefault 1 negative (pair z []))
noncomputable def language : Language := {z | d (pairFst z)=0 ∨
  endpoint P D H L F C hs parent terminal d hpos hf hdefault left true z=
    endpoint P D H L F C hs parent terminal d hpos hf hdefault right false z}

private theorem common_ne_zero (q : List Bool) : (atKey P D H (terminal q)).common≠0 :=
  IntegralMixedHistory.commonDenominator_ne_zero ((family P D H).state (terminal q))

theorem endpoint_at (selected : List Bool→ℕ) (negative : Bool) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w)
    (hc : IntegralMixedFramedFullCutTerminalHead.Valid P D H parent terminal q)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent q))
    (φ : ((family P D H).state (saved P parent q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state (saved P parent q)).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv
        (UniformIntegralPowerSchedule.embed hc i)^UniformIntegralPowerSchedule.weights
          (P.cap (pairFst (saved P parent q))+1) (2^(family P D H).width (saved P parent q))
          ((family P D H).birth (saved P parent q)) i)
    (hd : (IntegralMixedFramedFullCutIntervalSelected.factor P D H parent q φ).natDegree≤
      IntegralMixedFramedFullCutHead.degree P parent d q)
    (hdeg : 0<d q) (hi : selected q<(atKey P D H (terminal q)).count) :
    endpoint P D H L F C hs parent terminal d hpos hf hdefault selected negative (pair q w)=
      SignStatisticBits.integerCode (RealRootOpenIntervalOrdered.value
        (IntegralMixedFramedFullCutIntervalSelected.factor P D H parent q φ) (d q)
        (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
          (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
          (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨selected q,hi⟩)
        (((atKey P D H (terminal q)).common:ℝ)^2) negative) :=by
  unfold endpoint
  rw [value_at P D H L F C hs parent terminal d selected hpos hf hdefault 1 negative q w hv]
  exact congrArg SignStatisticBits.integerCode
    (IntegralMixedFramedFullCutIntervalSelected.model_selected P D H parent terminal d q
      L F C hs selected hc ha φ _ hφ hd hdeg hi negative)

theorem empty_iff (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs terminal hpos) q w)
    (hc : IntegralMixedFramedFullCutTerminalHead.Valid P D H parent terminal q)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent q))
    (φ : ((family P D H).state (saved P parent q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state (saved P parent q)).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv
        (UniformIntegralPowerSchedule.embed hc i)^UniformIntegralPowerSchedule.weights
          (P.cap (pairFst (saved P parent q))+1) (2^(family P D H).width (saved P parent q))
          ((family P D H).birth (saved P parent q)) i)
    (hz : IntegralMixedFramedFullCutIntervalSelected.factor P D H parent q φ≠0)
    (hdegree : (IntegralMixedFramedFullCutIntervalSelected.factor P D H parent q φ).natDegree=d q)
    (hclip : d q≤numericCap P (RankedHistoryTask.root (parent q)))
    (hl : left q<(atKey P D H (terminal q)).count) (hr : right q<(atKey P D H (terminal q)).count)
    (hab : LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
      (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
      (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨left q,hl⟩<
      LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
      (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
      (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨right q,hr⟩) :
    pair q w∈language P D H L F C hs parent terminal d left right hpos hf hdefault ↔
      ∀r,(IntegralMixedFramedFullCutIntervalSelected.factor P D H parent q φ).eval r=0→
        r∉Set.Ioo
          (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
            (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
            (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨left q,hl⟩)
          (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
            (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H (terminal q))
            (IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs terminal hpos q w hv) ⟨right q,hr⟩) :=by
  by_cases hd : d q=0
  · have HE:=constant_empty _ hz (hdegree.trans hd)
    simp only [language,Set.mem_ofPred_eq,pairFst_pair,hd,true_or]
    exact iff_of_true trivial (HE _ _)
  · have hdeg : 0<d q:=Nat.pos_of_ne_zero hd
    have HB : (IntegralMixedFramedFullCutIntervalSelected.factor P D H parent q φ).natDegree≤
        IntegralMixedFramedFullCutHead.degree P parent d q :=by
      rw [hdegree,IntegralMixedFramedFullCutHead.degree,min_eq_left hclip]
    simp only [language,Set.mem_ofPred_eq,pairFst_pair,hd,false_or]
    rw [endpoint_at P D H L F C hs parent terminal d hpos hf hdefault left true q w hv hc ha φ hφ HB hdeg hl,
      endpoint_at P D H L F C hs parent terminal d hpos hf hdefault right false q w hv hc ha φ hφ HB hdeg hr,
      integerCode_injective.eq_iff]
    exact (RealRootOpenIntervalOrdered.empty_iff _ _ hdeg hdegree hab _
      (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr (common_ne_zero P D H terminal q)))).symm

theorem decider_of_endpoints (hd : BinaryFn d)
    (EL : SpaceFunction (endpoint P D H L F C hs parent terminal d hpos hf hdefault left true))
    (ER : SpaceFunction (endpoint P D H L F C hs parent terminal d hpos hf hdefault right false)) :
    SpaceDecider (language P D H L F C hs parent terminal d left right hpos hf hdefault) :=by
  have HN : BinaryFn (fun z=>d (pairFst z)):=hd.comp pairFst_mem_FP
  have HZ := HN.eq (BinaryFn.const 0)
  have Z : SpaceDecider {z | d (pairFst z)=0} :=SpaceDecider.of_computable
    (.of_polyTime HZ.computable) (fun z=>by simp only [Set.mem_ofPred_eq,decide_eq_true_eq])
  have E : SpaceDecider {z | endpoint P D H L F C hs parent terminal d hpos hf hdefault left true z=
      endpoint P D H L F C hs parent terminal d hpos hf hdefault right false z} :=by
    apply (EL.pairOutputs ER).decider (fun z=>decide (pairFst z=pairSnd z))
      (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
    intro z
    simp only [Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,decide_eq_true_eq]
  exact Z.union E

end LeanCanny.Encoding.IntegralFramedFullCutOpenInterval
