/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutNewestRow
public import LeanCanny.Encoding.IntegralFramedCutSourceRow
/-! # The actual complete vertex satisfies every normalized selected-cut row

The head is the literal creating companion equation. The remaining rows
are the actual retained parent equations on the same tuple tail.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutNormalizedRoots
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem eval_nat_heq {a b : ℕ} (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ)
    (hm : a=b) (hp : HEq p q) (z : ℕ→ℝ) :
    p.eval₂ (Int.castRingHom ℝ) (fun i=>z i.val)=q.eval₂ (Int.castRingHom ℝ) (fun i=>z i.val) := by
  cases hm
  have he:=eq_of_heq hp
  cases he
  rfl

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (c w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedCutSuccessor.input P D H L F C hs) c w)
  (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
local notation "G" => family P D H
local notation "key" => IntegralMixedVirtualTaskBits.saved P c
local notation "x" => IntegralMixedCutSource.Family.state G key
local notation "d" => IntegralMixedCutSource.Family.degree G key
local notation "p" => IntegralMixedHistory.normalizedScalarPolynomial x
  (IntegralMixedCutMatrix.raw x (IntegralMixedCutSource.Family.birth_bound G key)
    (IntegralMixedCutSource.Family.rule G key) (IntegralMixedCutSource.Family.kind G key) d) d

include ha in
theorem rows (hcut : IntegralFramedCreatingCut.ParentCut P D c) :
    ∀ i,(UniformIntegralPrefixRows.rows ((G).cap key) (x).sampler.scalarPrefix.rows (x).sampler.scalarPrefix.basis p d i).eval₂
      (Int.castRingHom ℝ) (fun j=>IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv j.val)=0 := by
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · have HM : (IntegralMixedFramedCompanionBits.source P D H).arity key+1=(G).birth key+1 := rfl
    have HE:=eval_nat_heq _ _ HM (IntegralFramedCutSourceRow.cut_row P D H key hcut)
      (IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv)
    exact HE.symm.trans (IntegralFramedCutNewestRow.source_row_root P D H L F C hs c w hv ha)
  · simp only [UniformIntegralPrefixRows.rows,Fin.cons_succ,MvPolynomial.eval₂_rename]
    change ((x).sampler.scalarPrefix.rows j).eval₂ (Int.castRingHom ℝ)
      (fun k=>IntegralFramedCutParentInterpretation.joint P D H L F C hs c w hv (k.val+1))=0
    exact IntegralFramedCutParentInterpretation.parent_roots P D H L F C hs c w hv ha j

end LeanCanny.Encoding.IntegralFramedCutNormalizedRoots
