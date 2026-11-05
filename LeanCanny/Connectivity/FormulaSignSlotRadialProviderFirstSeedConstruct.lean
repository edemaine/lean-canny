/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerRealization
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedMarked
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedReplay
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedPoint
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedNoCut
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstSeedCriticalWord
public import LeanCanny.Geometry.BoundedMarkedLiftCoordinates
/-! # Genuine OLD and EXTERNAL endpoints construct fresh accepted depth-zero words -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderMarkedGeometry (number radius equation allowance zeroSet)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem marked_values_congr (n : List Bool→ℕ) (Q : (u : List Bool)→MvPolynomial (Fin (n u)) ℤ)
    (E : List Bool→ℕ) (R : ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (c u v : List Bool)
    (he : u=v) (x : ℕ→ℝ)
    (H : ∃a : BoundedZeroSource.Bounded (Q u) R, ∃z : ℕ→ℝ,
      (∀i,(T.polynomial (pair c (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (z i)=0) ∧
      (fun i : Fin (n u+4)=>z i.val)=(BoundedRegularSource.markedLift (Q u) (E u) (E u) R a).val.val ∧
      ∀i : Fin (n u),a.val i=x i.val) :
    ∃a : BoundedZeroSource.Bounded (Q v) R, ∃z : ℕ→ℝ,
      (∀i,(T.polynomial (pair c (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (z i)=0) ∧
      (fun i : Fin (n v+4)=>z i.val)=(BoundedRegularSource.markedLift (Q v) (E v) (E v) R a).val.val ∧
      ∀i : Fin (n v),a.val i=x i.val := by
  cases he
  exact H

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope
local notation "n" => CanonicalAuxiliaryCandidateCover.dimension
local notation "t" => CanonicalAuxiliaryCandidateCover.equation
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderIntegerSource.source CanonicalAuxiliaryCandidateCover.equation
  AuxiliaryCandidateRegularLift.original LeanCanny.ETR.Term.finitePolynomial

private theorem accept {c : List Bool} {v : ℕ→ℝ} {p : Fin ((P).ambient (root c)+1)→ℝ}
    (W : WordReceipt c v p) (hM : FormulaSignSlotRadialProviderAtomic.Marked.Holds (packet c W.word))
    (hR : FormulaSignSlotRadialProviderAtomic.Replay (packet c W.word)) :
    ∃hV : FormulaSignSlotRadialProviderAtomic.Valid (packet c W.word),
      HEq (FormulaSignSlotRadialProviderAtomic.point (packet c W.word) hV) p ∧
      ∀i<FormulaSignSlotRadialProviderRecordPlan.count (root c),
        FormulaSignSlotRadialProviderAtomic.field (packet c W.word) hV i=v i := by
  have HC : seedContext c=pair (root c) [] := rfl
  have HW := (congrArg (fun ctx=>SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input ctx W.word) HC).mp W.valid
  have hV : FormulaSignSlotRadialProviderAtomic.Valid (packet c W.word) :=
    ⟨checked c W.word,W.full_valid_packet,before_probe c W.word HW,W.all_critical,W.companions,hM,hR⟩
  exact ⟨hV,W.point_packet hV,fun i hi=>W.field_packet hV i hi⟩

private theorem marked_coordinates {m : ℕ} (q : MvPolynomial (Fin m) ℤ) (E R : ℕ)
    (a : BoundedZeroSource.Bounded q R) (v : ℕ→ℝ)
    (hv : (fun i : Fin (m+4)=>v i.val)=(BoundedRegularSource.markedLift q E E R a).val.val) :
    ∀i : Fin m,v i.val=a.val i := by
  intro i
  exact (congrFun hv (i.castAdd 4)).trans (BoundedRegularSource.lift_original_coordinate q E E R a i)

section External
variable (H : List Bool) (K : ℕ) (Gamma label : List Bool) (s : Bool) (oldWord : List Bool)
local notation "ctx" => FormulaSignSlotRadialExternalContext.packet H K Gamma label s oldWord

private theorem external_values (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) oldWord∈
      FormulaSignSlotRadialJointStratumSampler.language) :
    ∃a : BoundedZeroSource.Bounded (equation ctx) (radius ctx), ∃v : ℕ→ℝ,
      (∀i,(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial (pair ctx (BinaryNatCode.encode i))).eval₂
        (Int.castRingHom ℝ) (v i)=0) ∧
      (fun i : Fin (number ctx+4)=>v i.val)=
        (BoundedRegularSource.markedLift (equation ctx) (allowance ctx) (allowance ctx) (radius ctx) a).val.val ∧
      ∀i : Fin (number ctx),a.val i=FormulaSignSlotRadialExternalCoordinates.point ctx hw i.val := by
  exact marked_values_congr n (AuxiliaryCandidateRegularLift.original n t) (AuxiliaryCandidateRegularLift.allowance t)
    (radius ctx) FormulaSignSlotRadialProviderIntegerPlan.source ctx (FormulaSignSlotRadialJointLayout.source s H)
    (FormulaSignSlotRadialExternalPrelude.original ctx)
    (FormulaSignSlotRadialExternalContext.original_packet H K Gamma label s oldWord).symm
    (FormulaSignSlotRadialExternalCoordinates.point ctx hw)
    (FormulaSignSlotRadialProviderIntegerRealization.exists_external_values H K Gamma label s oldWord hw hq)

theorem exists_external_seed (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H K) Gamma) oldWord∈
      FormulaSignSlotRadialJointStratumSampler.language) :
    ∃a : BoundedZeroSource.Bounded (equation ctx) (radius ctx), ∃w : List Bool,
      ∃hV : FormulaSignSlotRadialProviderAtomic.Valid (packet ctx w), ∃p : Fin (number ctx+4)→ℝ,
        HEq (FormulaSignSlotRadialProviderAtomic.point (packet ctx w) hV) p ∧
        JoinedIn (zeroSet ctx)
          (BoundedRegularSource.markedLift (equation ctx) (allowance ctx) (allowance ctx) (radius ctx) a).val.val p ∧
        (∀i : Fin (number ctx+4),FormulaSignSlotRadialProviderAtomic.field (packet ctx w) hV i.val=
          (BoundedRegularSource.markedLift (equation ctx) (allowance ctx) (allowance ctx) (radius ctx) a).val.val i) ∧
        ∀i : Fin (number ctx),a.val i=FormulaSignSlotRadialExternalCoordinates.point ctx hw i.val := by
  obtain ⟨a,v,hRoots,hMarked,hCoord⟩ := external_values H K Gamma label s oldWord hw hq
  have HZ : (fun i=>v i.val)∈zeroSet ctx := by
    rw [hMarked]
    exact FormulaSignSlotRadialProviderMarkedGeometry.markedLift_mem ctx a
  obtain ⟨pRoot,W,p,hpq,hPath⟩ := exists_component_word ctx v (fun i _=>hRoots i) HZ
  have HR : (BoundedRegularSource.polynomial (equation ctx) (allowance ctx) (allowance ctx) (radius ctx)).eval₂
      (Int.castRingHom ℝ) (fun i=>v i.val)=0 := by
    exact (congrArg (fun x : Fin (number ctx+4)→ℝ=>
      (BoundedRegularSource.polynomial (equation ctx) (allowance ctx) (allowance ctx) (radius ctx)).eval₂
        (Int.castRingHom ℝ) x) hMarked).trans
      (BoundedRegularSource.markedLift (equation ctx) (allowance ctx) (allowance ctx) (radius ctx) a).val.property
  have HM : (BoundedRegularSource.markPolynomial (equation ctx) (radius ctx)).eval₂
      (Int.castRingHom ℝ) (fun i=>v i.val)=0 := by
    exact (congrArg (fun x : Fin (number ctx+4)→ℝ=>
      (BoundedRegularSource.markPolynomial (equation ctx) (radius ctx)).eval₂ (Int.castRingHom ℝ) x) hMarked).trans
        (BoundedRegularSource.markedLift (equation ctx) (allowance ctx) (allowance ctx) (radius ctx) a).property
  have HReplay := W.replay_external H K Gamma label s oldWord hw hq (fun i hi=>
    (marked_coordinates (equation ctx) (allowance ctx) (radius ctx) a v hMarked ⟨i,hi⟩).trans (hCoord ⟨i,hi⟩))
  obtain ⟨hV,hPoint,hFields⟩ := accept W (W.marked (fun i _=>hRoots i) HR HM) HReplay
  refine ⟨a,W.word,hV,p,hPoint.trans hpq,?_,?_,hCoord⟩
  · rw [←hMarked]
    exact hPath
  · intro i
    exact (hFields i.val (by rw [count_root];change i.val<number ctx+8;omega)).trans (congrFun hMarked i)

end External

section Old
variable (u label aux : List Bool)
local notation "ctx" => FormulaSignSlotRadialOldProviderRealization.context u label aux

private theorem old_values (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label) :
    ∃a : BoundedZeroSource.Bounded (equation ctx) (radius ctx), ∃v : ℕ→ℝ,
      (∀i,(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial (pair ctx (BinaryNatCode.encode i))).eval₂
        (Int.castRingHom ℝ) (v i)=0) ∧
      (fun i : Fin (number ctx+4)=>v i.val)=
        (BoundedRegularSource.markedLift (equation ctx) (allowance ctx) (allowance ctx) (radius ctx) a).val.val ∧
      ∀i : Fin (number ctx),a.val i=IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst ctx)
        (FormulaSignSlotRadialOldProviderRealization.valid u label aux hg) i := by
  exact ⟨FormulaSignSlotRadialOldProviderRealization.boundedPoint u label aux hg,
    FormulaSignSlotRadialOldProviderRealization.values u label aux hg,
    FormulaSignSlotRadialOldProviderRealization.roots u label aux hg,
    FormulaSignSlotRadialOldProviderRealization.marked_coordinates u label aux hg,
    FormulaSignSlotRadialOldProviderRealization.boundedPoint_coordinate u label aux hg⟩

theorem exists_old_seed (hg : AuxiliaryCandidateComponentCover.Good hn ht ha u label) :
    ∃a : BoundedZeroSource.Bounded (equation ctx) (radius ctx), ∃w : List Bool,
      ∃hV : FormulaSignSlotRadialProviderAtomic.Valid (packet ctx w), ∃p : Fin (number ctx+4)→ℝ,
        HEq (FormulaSignSlotRadialProviderAtomic.point (packet ctx w) hV) p ∧
        JoinedIn (zeroSet ctx)
          (BoundedRegularSource.markedLift (equation ctx) (allowance ctx) (allowance ctx) (radius ctx) a).val.val p ∧
        (∀i : Fin (number ctx+4),FormulaSignSlotRadialProviderAtomic.field (packet ctx w) hV i.val=
          (BoundedRegularSource.markedLift (equation ctx) (allowance ctx) (allowance ctx) (radius ctx) a).val.val i) ∧
        ∀i : Fin (number ctx),a.val i=IntegralMixedAuxiliaryCandidate.point hn ht ha (pairFst ctx)
          (FormulaSignSlotRadialOldProviderRealization.valid u label aux hg) i := by
  obtain ⟨a,v,hRoots,hMarked,hCoord⟩ := old_values u label aux hg
  have HZ : (fun i=>v i.val)∈zeroSet ctx := by
    rw [hMarked]
    exact FormulaSignSlotRadialProviderMarkedGeometry.markedLift_mem ctx a
  obtain ⟨pRoot,W,p,hpq,hPath⟩ := exists_component_word ctx v (fun i _=>hRoots i) HZ
  have HR : (BoundedRegularSource.polynomial (equation ctx) (allowance ctx) (allowance ctx) (radius ctx)).eval₂
      (Int.castRingHom ℝ) (fun i=>v i.val)=0 := by
    exact (congrArg (fun x : Fin (number ctx+4)→ℝ=>
      (BoundedRegularSource.polynomial (equation ctx) (allowance ctx) (allowance ctx) (radius ctx)).eval₂
        (Int.castRingHom ℝ) x) hMarked).trans
      (BoundedRegularSource.markedLift (equation ctx) (allowance ctx) (allowance ctx) (radius ctx) a).val.property
  have HM : (BoundedRegularSource.markPolynomial (equation ctx) (radius ctx)).eval₂
      (Int.castRingHom ℝ) (fun i=>v i.val)=0 := by
    exact (congrArg (fun x : Fin (number ctx+4)→ℝ=>
      (BoundedRegularSource.markPolynomial (equation ctx) (radius ctx)).eval₂ (Int.castRingHom ℝ) x) hMarked).trans
        (BoundedRegularSource.markedLift (equation ctx) (allowance ctx) (allowance ctx) (radius ctx) a).property
  have HReplay := W.replay_old (FormulaSignSlotRadialOldProviderRealization.old_context u label aux)
    (FormulaSignSlotRadialOldProviderRealization.valid u label aux hg) (fun i=>
      (hCoord i).symm.trans (marked_coordinates (equation ctx) (allowance ctx) (radius ctx) a v hMarked i).symm)
  obtain ⟨hV,hPoint,hFields⟩ := accept W (W.marked (fun i _=>hRoots i) HR HM) HReplay
  refine ⟨a,W.word,hV,p,hPoint.trans hpq,?_,?_,hCoord⟩
  · rw [←hMarked]
    exact hPath
  · intro i
    exact (hFields i.val (by rw [count_root];change i.val<number ctx+8;omega)).trans (congrFun hMarked i)

end Old
end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
