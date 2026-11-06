/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueInterval
public import LeanCanny.Connectivity.FormulaSignSlotRadialJointDescriptorGeometry
/-! # The native VALUE checker selects all witnesses internally -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueMeaning
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input
local notation "env"=>FormulaSignSlotRadialImplicitSourceTest.env
local notation "payload"=>FormulaSignSlotRadialImplicitValueSelection.packet
local notation "original"=>FormulaSignSlotRadialImplicitValueSelection.original
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialValueCertificate.polynomial
  FormulaSignSlotRadialValueWindowMeaning.certificate FormulaSignSlotRadialValueWindowMeaning.Guard
  FormulaSignSlotRadialCenterValuePacking.source FormulaSignSlotRadialValueCatalogueLayout.family

private noncomputable def extendNat {n:ℕ} (v:Fin n→ℕ) (i:ℕ):ℕ:=if h:i<n then v ⟨i,h⟩ else 0
private theorem extendNat_at {n:ℕ} (v:Fin n→ℕ) (i:Fin n):extendNat v i.val=v i:=by
  simp only [extendNat,dite_eq_left i.isLt]

/-- Every genuine center has a bounded canonical table context for the
actual target trailing coefficient. Its coordinate guards are derived. -/
private theorem selected_context (u:List Bool) (a:ℕ→ℝ):
    ∃o,o<FormulaSignSlotRadialValueCatalogueLayout.outerCount u ∧
      FormulaSignSlotRadialValueWindowMeaning.Guard (FormulaSignSlotRadialValueCatalogueLayout.family u o) a ∧
      FormulaSignSlotRadialValueCatalogueLayout.orderIndex u o=
        (FormulaSignSlotRadialValueWindowMeaning.certificate u a).natTrailingDegree:=by
  obtain ⟨t,D,HB,HG⟩:=FormulaSignSlotRadialCenterValueSelection.exists_bounded_guards u a
  let tau:ℕ→ℕ:=extendNat t
  let deg:ℕ→ℕ:=extendNat D
  have HT:(fun i:Fin (FormulaSignSlotCenteredRadialGraph.N u+FormulaSignSlotCenteredRadialGraph.d u+1)=>tau i.val)=t:=funext (extendNat_at t)
  have HD:(fun i:Fin (FormulaSignSlotCenteredRadialGraph.N u+FormulaSignSlotCenteredRadialGraph.d u+1)=>deg i.val)=D:=funext (extendNat_at D)
  have HBounds:∀j,j<FormulaSignSlotRadialValueCatalogueBounds.coordinates u→
      tau j≤FormulaSignSlotRadialValueCatalogueBounds.bound u ∧deg j≤FormulaSignSlotRadialValueCatalogueBounds.bound u:=by
    intro j hj
    have hj':j<FormulaSignSlotCenteredRadialGraph.N u+FormulaSignSlotCenteredRadialGraph.d u+1:=hj
    simpa only [tau,deg,extendNat,dite_eq_left hj',FormulaSignSlotRadialValueCatalogueBounds.bound] using HB ⟨j,hj'⟩
  have HG0:FormulaSignSlotRadialCenterValueFamily.Guards u (fun j=>a j.val) (fun i=>tau i.val) (fun i=>deg i.val):=by
    rw [HT,HD]
    exact HG
  let C:=FormulaSignSlotRadialValueCatalogueBounds.familyContext u tau deg
  have HO:FormulaSignSlotRadialCenterValueLayout.original C=u:=FormulaSignSlotRadialValueCatalogueBounds.family_original u tau deg
  have GC:FormulaSignSlotRadialValueWindowMeaning.Guard C a:=
    FormulaSignSlotRadialValueWindowMeaning.guard_from_values C u HO a tau deg
      (fun j hj=>FormulaSignSlotRadialValueCatalogueBounds.family_tau u tau deg j hj)
      (fun j hj=>FormulaSignSlotRadialValueCatalogueBounds.family_degree u tau deg j hj) HG0
  have Hdegree:(FormulaSignSlotRadialValueWindowMeaning.certificate u a).natDegree≤FormulaSignSlotRadialCenterValuePacking.degree C:=by
    have H:=FormulaSignSlotRadialValueWindowMeaning.certificate_degree C a GC
    rw [HO] at H
    exact H
  let ell:=(FormulaSignSlotRadialValueWindowMeaning.certificate u a).natTrailingDegree
  obtain ⟨o,ho,HC⟩:=FormulaSignSlotRadialValueCatalogueLayout.covers u tau deg
    (fun j hj=>(HBounds j hj).1) (fun j hj=>(HBounds j hj).2) ell
    ((Polynomial.natTrailingDegree_le_natDegree _).trans Hdegree)
  rw [FormulaSignSlotRadialValueCatalogueLayout.context_packet] at HC
  have HF:FormulaSignSlotRadialValueCatalogueLayout.family u o=C:=by
    simpa only [pairFst_pair,C] using congrArg pairFst HC
  have HE:FormulaSignSlotRadialValueCatalogueLayout.orderIndex u o=ell:=by
    have H:=congrArg (fun z=>Nat.fromBitsLE (pairSnd z)) HC
    simpa only [pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using H
  exact ⟨o,ho,HF.symm ▸ GC,HE⟩

noncomputable def certificate (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):=
  FormulaSignSlotRadialValueWindowMeaning.certificate (original c) (fun j=>env c w hw (4*j))
private theorem family_original (c w:List Bool) (o ell:ℕ):
    FormulaSignSlotRadialCenterValueLayout.original (FormulaSignSlotRadialImplicitValueSelection.family (payload c w o ell))=original c:=by
  unfold FormulaSignSlotRadialImplicitValueSelection.family
  rw [FormulaSignSlotRadialValueCatalogueLayout.family_original]
  simp only [FormulaSignSlotRadialImplicitValueSelection.context,FormulaSignSlotRadialImplicitValueSelection.sample,
    FormulaSignSlotRadialImplicitValueSelection.packet,pairFst_pair]
private theorem certificate_eq (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (o ell:ℕ):
    FormulaSignSlotRadialImplicitValueInterval.certificate c w hw o ell=certificate c w hw:=by
  unfold FormulaSignSlotRadialImplicitValueInterval.certificate
  rw [family_original]
  rfl

private theorem family_packet (c w:List Bool) (o ell:ℕ):
    FormulaSignSlotRadialImplicitValueSelection.family (payload c w o ell)=FormulaSignSlotRadialValueCatalogueLayout.family (original c) o:=by
  simp only [FormulaSignSlotRadialImplicitValueSelection.family,FormulaSignSlotRadialImplicitValueSelection.context,
    FormulaSignSlotRadialImplicitValueSelection.sample,FormulaSignSlotRadialImplicitValueSelection.outer,
    FormulaSignSlotRadialImplicitValueSelection.packet,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

attribute [local irreducible] certificate FormulaSignSlotRadialImplicitValueSelection.family
  FormulaSignSlotRadialImplicitValueSelection.original FormulaSignSlotRadialImplicitSourceTest.env
/-- The finite native outer search is exactly the actual VALUE-cut interval.
No chosen table, trailing index or semantic guard is a caller premise. -/
theorem holds_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (hb:0<env c w hw 3):
    FormulaSignSlotRadialImplicitValueInterval.Holds (pair c w) ↔
      FormulaSignSlotRadialImplicitValueInterval.NoRoot (certificate c w hw).trailingCoeff (env c w hw 3):=by
  unfold FormulaSignSlotRadialImplicitValueInterval.Holds
  simp only [FormulaSignSlotRadialImplicitValueInterval.count,FormulaSignSlotRadialImplicitValueInterval.root,pairFst_pair,
    FormulaSignSlotRadialImplicitValueInterval.row_packet]
  constructor
  · rintro ⟨o,_,HA⟩
    have H:=(FormulaSignSlotRadialImplicitValueInterval.at_trailing c w hw o _ hb).mp HA
    rw [certificate_eq] at H
    exact H.2.2.2
  · intro HN
    have HP:certificate c w hw≠0:=by
      intro H0
      have H:=HN (env c w hw 3/2) (by rw [H0];simp)
      exact H ⟨by linarith,by linarith⟩
    obtain ⟨o,ho,HG,HE⟩:=selected_context (original c) (fun j=>env c w hw (4*j))
    refine ⟨o,ho,(FormulaSignSlotRadialImplicitValueInterval.at_trailing c w hw o _ hb).mpr ?_⟩
    rw [certificate_eq]
    have HE0:FormulaSignSlotRadialValueCatalogueLayout.orderIndex (original c) o=(certificate c w hw).natTrailingDegree:=by
      simpa only [certificate] using HE
    refine ⟨?_,HP,HE0,HN⟩
    rw [family_packet]
    exact HG

private theorem extend_old {n:ℕ} (v:Fin (n+1)→ℝ) (i:Fin n):
    LeanCanny.ETR.Formula.extend (fun j=>v j.castSucc) i.val=IntegralMixedFramedBankObservation.extend v i.val:=by
  have H:i.val<n+1:=i.isLt.trans (Nat.lt_succ_self n)
  simp only [LeanCanny.ETR.Formula.extend,IntegralMixedFramedBankObservation.extend,dite_eq_left i.isLt,dite_eq_left H]
  exact congrArg v (Fin.ext rfl)

attribute [local irreducible] ImplicitSourceComponentSampler.language FormulaSignSlotRadialJointCore.equation

/-- Positivity is extracted from this own word's actual core equation. -/
theorem bound_pos (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (hq:pair c w∈FormulaSignSlotRadialJointStratumSampler.language):0<env c w hw 3:=by
  unfold FormulaSignSlotRadialImplicitSourceTest.env
  have HC:=((FormulaSignSlotRadialJointStratumSampler.accepted_iff c w hw).mp hq).1
  have HP:=FormulaSignSlotRadialJointCoreReadback.parameter_positive _ _ HC
  have HB:=HP.1.trans HP.2
  let i:Fin (FormulaSignSlotRadialJointStratum.oldArity (ImplicitSourceGramGrid.header c)):=
    ⟨3,FormulaSignSlotRadialJointLayout.boundVariable_lt (FormulaSignSlotRadialImplicitValueSelection.header c)⟩
  have HE:=extend_old (SquareSampleCompleteVertices.candidate F c w hw).val i
  change LeanCanny.ETR.Formula.extend (FormulaSignSlotRadialJointStratum.oldPoint
    (ImplicitSourceGramGrid.header c) (SquareSampleCompleteVertices.candidate F c w hw).val) 3=
      IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate F c w hw).val 3 at HE
  exact HE ▸ HB

/-- The installed PSPACE language is exactly its own sampler filter and the
literal actual VALUE-certificate trailing-head no-root condition. -/
theorem language_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):
    pair c w∈FormulaSignSlotRadialImplicitValueInterval.language ↔
      pair c w∈FormulaSignSlotRadialJointStratumSampler.language ∧
        FormulaSignSlotRadialImplicitValueInterval.NoRoot (certificate c w hw).trailingCoeff (env c w hw 3):=by
  change (_∧FormulaSignSlotRadialImplicitValueInterval.Holds (pair c w))↔_
  apply and_congr_right
  intro hq
  exact holds_packet_iff c w hw (bound_pos c w hw hq)

/-- Literal original-source VALUE interval semantics on the unchanged OWN tuple. -/
theorem actual_language_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):
    pair c w∈FormulaSignSlotRadialImplicitValueInterval.language ↔
      pair c w∈FormulaSignSlotRadialJointStratumSampler.language ∧
        ∀r:ℝ,(FormulaSignSlotRadialValueCertificate.polynomial
          (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitValueSelection.header c))
          (fun j=>env c w hw (4*j.val))).trailingCoeff.eval r=0 → r ∉ Ioo 0 (env c w hw 3):=by
  simpa only [certificate,FormulaSignSlotRadialValueWindowMeaning.certificate,
    FormulaSignSlotRadialImplicitValueSelection.original,FormulaSignSlotRadialImplicitValueInterval.NoRoot]
    using language_packet_iff c w hw
end LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueMeaning
