/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutParentRoots
public import LeanCanny.Encoding.IntegralFramedCutCommonParent
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # The actual complete successor vertex constructs its parent interpretation

The homomorphism is derived from the actual old row system on the tail of
this one tuple. It is not supplied as a geometric validity premise.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutParentInterpretation
open LeanCanny.Algebra IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem extend_fin {m : ℕ} (z : Fin m→ℝ) (i : Fin m) :
    IntegralMixedFramedBankObservation.extend z i.val=z i := by
  simp only [IntegralMixedFramedBankObservation.extend,dite_eq_left i.isLt]

private theorem rows_roots_heq {a b : ℕ} (f : Fin a→MvPolynomial (Fin a) ℤ)
    (g : Fin b→MvPolynomial (Fin b) ℤ) (hm : a=b) (hf : HEq f g) (z : ℕ→ℝ) :
    (∀ i,(f i).eval₂ (Int.castRingHom ℝ) (fun j=>z j.val)=0) ↔
      (∀ i,(g i).eval₂ (Int.castRingHom ℝ) (fun j=>z j.val)=0) := by
  cases hm
  have he:=eq_of_heq hf
  cases he
  rfl

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w)

noncomputable def joint : ℕ→ℝ := IntegralMixedFramedBankObservation.extend
  (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv).val

theorem successor_roots : RootsAt ((family P D H).state (IntegralFramedCutSuccessor.key P c)).sampler.scalarPrefix
    (joint P D H L F C hs c w hv) := by
  have HCount : (IntegralFramedCutSuccessor.input P D H L F C hs).count c=
      (family P D H).birth (IntegralFramedCutSuccessor.key P c) := rfl
  have HInput : ∀ i,((IntegralFramedCutSuccessor.input P D H L F C hs).system c i).eval₂ (Int.castRingHom ℝ)
      (fun j=>joint P D H L F C hs c w hv j.val)=0 := by
    intro i
    have HE : (fun j : Fin ((IntegralFramedCutSuccessor.input P D H L F C hs).count c)=>joint P D H L F C hs c w hv j.val)=
        (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv).val := by
      funext j
      exact extend_fin _ j
    rw [HE]
    exact (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv).property i
  exact (rows_roots_heq _ _ HCount (IntegralFramedCompleteSquare.rows_heq P D H L F C hs (IntegralFramedCutSuccessor.key P)
    (IntegralFramedCutSuccessor.positive P D H) c) _).mp HInput

theorem parent_roots (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    RootsAt ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix
      (fun i=>joint P D H L F C hs c w hv (i+1)) :=
  IntegralFramedCutParentRoots.parent P D H c ha _ (successor_roots P D H L F C hs c w hv)

theorem exists_interpretation (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    ∃ φ : ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀ i,φ (((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.generator i)=
        (SquareSampleCompleteVertices.candidate (IntegralFramedCutSuccessor.input P D H L F C hs) c w hv).val
          (Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) i.succ)^
            UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
              (2^(family P D H).width (IntegralMixedVirtualTaskBits.saved P c))
              ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)) i := by
  obtain ⟨φ,hφ⟩:=((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.interpret ℝ
    (fun i=>joint P D H L F C hs c w hv (i.val+1)) (parent_roots P D H L F C hs c w hv ha)
  refine ⟨φ,fun i=>?_⟩
  have HB : i.val+1<(IntegralFramedCutSuccessor.input P D H L F C hs).count c := by
    rw [←IntegralFramedCutCommonParent.dimension P D H L F C hs c ha]
    have hi:=i.isLt
    omega
  have HC : (⟨i.val+1,HB⟩ : Fin ((IntegralFramedCutSuccessor.input P D H L F C hs).count c))=
      Fin.cast (IntegralFramedCutCommonParent.dimension P D H L F C hs c ha) i.succ := by
    apply Fin.ext
    rfl
  have HS : (family P D H).cap (IntegralMixedVirtualTaskBits.saved P c)=IntegralMixedFramedChoiceProbeSourceBits.horizon P c := by
    unfold family
    change P.cap (pairFst (IntegralMixedVirtualTaskBits.saved P c))+1=P.cap (RankedHistoryTask.root c)+1
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  have HI:=hφ i
  unfold joint IntegralMixedFramedBankObservation.extend at HI
  rw [dite_eq_left HB,HC] at HI
  simpa only [HS] using HI

end LeanCanny.Encoding.IntegralFramedCutParentInterpretation
