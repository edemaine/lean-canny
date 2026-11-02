/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutBankPoint
/-! # An accepted cut is a full-factor root at the actual newest bank value

The point is decoded from the same complete successor tuple and the literal
stored denominator. No independent scalar root or parent embedding is chosen.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutBankRoot
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
local notation "G" => family P D H
local notation "key" => IntegralMixedVirtualTaskBits.saved P c
local notation "x" => IntegralMixedCutSource.Family.state G key
local notation "d" => IntegralMixedCutSource.Family.degree G key
local notation "r" => IntegralMixedCutSource.Family.rule G key
local notation "k" => IntegralMixedCutSource.Family.kind G key
local notation "hm" => IntegralMixedCutSource.Family.birth_bound G key
local notation "f" => IntegralMixedRelativeCuts.factor x hm r k
local notation "z" => Subtype.val (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv)
local notation "z'" => (fun i : Fin (IntegralMixedCutSource.Family.birth G key+1)=>
  z (Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) i))
local notation "point" => IntegralMixedFramedBankObservation.Data.point
  (IntegralMixedFramedBankObservation.ofState (IntegralMixedCutSource.Family.state G (IntegralFramedCutSuccessor.key P c)))
  (IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv) 0

omit hFpos hf in
theorem point_newest (hcut : IntegralFramedCreatingCut.ParentCut P D c) :
    point=IntegralRelativeTruncation.jointQuotient (x).sampler.scalarPrefix f d z' := by
  rw [IntegralFramedCutBankPoint.point_newest P D H c ha hcut]
  have HB : 0<(IntegralFramedCutSuccessor.input P D H L F C hs).count c := IntegralFramedCutSuccessor.positive P D H c
  have HZ : IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv 0=z' 0 := by
    unfold IntegralFramedCutParentInterpretation.joint IntegralMixedFramedBankObservation.extend
    rw [dite_eq_left HB]
    exact congrArg z (Fin.ext rfl)
  unfold IntegralRelativeTruncation.jointQuotient
  dsimp only
  simp only [Fin.val_zero]
  rw [HZ]

theorem exists_root (hcut : IntegralFramedCreatingCut.ParentCut P D c)
    (hg : IntegralFramedCutFiniteGuards.Guards P D H L F C hs hFpos hf (pair c w)) :
    ∃ φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀ i,φ ((x).sampler.scalarPrefix.basis.generator i)=z' i.succ^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
          (2^(G).width key) ((G).birth key) i) ∧
      IntegralMixedRelativeCuts.Valid x hm r φ k ∧
      ((f).map φ.toRingHom).natDegree=d ∧ (f).eval₂ φ.toRingHom point=0 := by
  obtain ⟨φ,hφ,hvalid,hd,hr⟩:=IntegralFramedCutAcceptedRoot.exists_root P D H L F C hs hFpos hf c w hv ha hcut hg
  refine ⟨φ,hφ,hvalid,hd,?_⟩
  rw [point_newest P D H L F C hs c w hv ha hcut]
  exact hr

end LeanCanny.Encoding.IntegralFramedCutBankRoot
