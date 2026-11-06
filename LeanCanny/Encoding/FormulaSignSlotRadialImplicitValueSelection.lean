/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitSourceTest
public import LeanCanny.Encoding.FormulaSignSlotRadialValueWindowMeaning
public import LeanCanny.Encoding.FormulaSignSlotRadialValueCatalogueLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitCenterSelection
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiDecision
/-! # Actual full VALUE window signs at one unchanged implicit sample

The point context contains one own word, a bounded table ordinal and a
coefficient order. Only the window controls change between sign requests.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueSelection
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial
private theorem guard_original (C u:List Bool) (H:FormulaSignSlotRadialCenterValueLayout.original C=u) (a:ℕ→ℝ):
    FormulaSignSlotRadialCenterValueFamily.Guards u (fun i=>a i.val)
      (fun i=>FormulaSignSlotRadialCenterValueLayout.tau C i.val)
      (fun i=>FormulaSignSlotRadialCenterValueLayout.degree C i.val) ↔ FormulaSignSlotRadialValueWindowMeaning.Guard C a:=by
  cases H
  rfl
private theorem raw_dimension (C u:List Bool) (H:FormulaSignSlotRadialCenterValueLayout.original C=u) (ell:ℕ):
    FormulaSignSlotRadialValueWindowCatalogue.centers (pair C (BinaryNatCode.encode ell))=FormulaSignSlotCenteredRadialGraph.d u:=by
  unfold FormulaSignSlotRadialValueWindowCatalogue.centers
  rw [pairFst_pair]
  exact congrArg FormulaSignSlotCenteredRadialGraph.d H
private theorem tau_reindex (f:List Bool→List Bool) (hf:f∈FP):
    BinaryFn (fun q=>FormulaSignSlotRadialCenterValueLayout.tau (f (pairFst q)) (Nat.fromBitsLE (pairSnd q))):=by
  have H:BinaryFn ((fun q=>FormulaSignSlotRadialCenterValueLayout.tau (pairFst q) (Nat.fromBitsLE (pairSnd q))) ∘
      (fun q=>pair (f (pairFst q)) (pairSnd q))):=
    FormulaSignSlotRadialCenterValueLayout.tau_binary.comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP)
  exact H.of_eq (fun q=>by simp only [Function.comp_apply,pairFst_pair,pairSnd_pair])
private theorem degree_reindex (f:List Bool→List Bool) (hf:f∈FP):
    BinaryFn (fun q=>FormulaSignSlotRadialCenterValueLayout.degree (f (pairFst q)) (Nat.fromBitsLE (pairSnd q))):=by
  have H:BinaryFn ((fun q=>FormulaSignSlotRadialCenterValueLayout.degree (pairFst q) (Nat.fromBitsLE (pairSnd q))) ∘
      (fun q=>pair (f (pairFst q)) (pairSnd q))):=
    FormulaSignSlotRadialCenterValueLayout.degree_binary.comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP)
  exact H.of_eq (fun q=>by simp only [Function.comp_apply,pairFst_pair,pairSnd_pair])
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input
local notation "Raw"=>FormulaSignSlotRadialValueRadiusSource.source
local notation "Nraw"=>FormulaSignSlotRadialValueWindowCatalogue.centers
local notation "HD"=>FormulaSignSlotRadialValueWindowCatalogue.dimension_eq

def header (c:List Bool):=FormulaSignSlotRadialJointStratum.header (ImplicitSourceGramGrid.header c)
noncomputable def original (c:List Bool):=FormulaSignSlotRadialJointLayout.source true (header c)
def sample (z:List Bool):=pairFst z
def context (z:List Bool):=pairFst (sample z)
def word (z:List Bool):=pairSnd (sample z)
def outer (z:List Bool):=Nat.fromBitsLE (pairFst (pairSnd z))
def order (z:List Bool):=Nat.fromBitsLE (pairSnd (pairSnd z))
def packet (c w:List Bool) (o ell:ℕ):=pair (pair c w) (pair (BinaryNatCode.encode o) (BinaryNatCode.encode ell))
noncomputable def family (z:List Bool):=FormulaSignSlotRadialValueCatalogueLayout.family (original (context z)) (outer z)
noncomputable def rawContext (z:List Bool):=pair (family z) (BinaryNatCode.encode (order z))
noncomputable def degree (z:List Bool):=(Raw).degree (rawContext z)

theorem header_FP:header∈FP:=by polytime [header,FormulaSignSlotRadialJointStratum.header,ImplicitSourceGramGrid.header]
theorem original_FP:original∈FP:=mem_FP_comp header_FP (FormulaSignSlotRadialJointLayout.source_FP true)
attribute [local irreducible] original FormulaSignSlotRadialValueCatalogueLayout.family

theorem family_FP:family∈FP:=by
  have E:=mem_FP_comp
    (mem_FP_pair (mem_FP_comp (show context∈FP by polytime [context,sample]) original_FP)
      (show (fun z=>pairFst (pairSnd z))∈FP by polytime)) FormulaSignSlotRadialValueCatalogueLayout.family_FP
  exact mem_FP_of_eq E (fun z=>by simp only [Function.comp_apply,family,outer,pairFst_pair,pairSnd_pair])
theorem rawContext_FP:rawContext∈FP:=mem_FP_pair family_FP (BinaryFn.fromBits (show (fun z=>pairSnd (pairSnd z))∈FP by polytime)).bits_mem_FP
theorem degree_binary:BinaryFn degree:=FormulaSignSlotRadialValueRadiusSource.degree_binary.comp rawContext_FP


private theorem family_original (z:List Bool):FormulaSignSlotRadialCenterValueLayout.original (family z)=original (context z):=
  FormulaSignSlotRadialValueCatalogueLayout.family_original _ _
theorem dimension (z:List Bool):Nraw (rawContext z)=FormulaSignSlotRadialJointLayout.centerCount (header (context z)):=by
  exact (raw_dimension (family z) (original (context z)) (family_original z) (order z)).trans (by
    unfold original
    rfl)
noncomputable def coefficientBound (z:List Bool):=FormulaSignSlotRadialCenterValuePacking.degree (family z)
theorem coefficientBound_binary:BinaryFn coefficientBound:=FormulaSignSlotRadialCenterValuePacking.degree_binary.comp family_FP
noncomputable def coordinates (z:List Bool):=FormulaSignSlotRadialValueCatalogueBounds.coordinates (original (context z))
theorem coordinates_unary:UnaryFn coordinates:=FormulaSignSlotRadialValueCatalogueBounds.coordinates_unary.comp
  (mem_FP_comp (show context∈FP by polytime [context,sample]) original_FP)

attribute [local irreducible] family

noncomputable def coordinateQuery (q:List Bool):=pair (pair (sample (pairFst q)) (pairSnd q))
  (pair
    (BinaryNatCode.encode (FormulaSignSlotRadialCenterValueLayout.tau (family (pairFst q)) (Nat.fromBitsLE (pairSnd q))))
    (BinaryNatCode.encode (FormulaSignSlotRadialCenterValueLayout.degree (family (pairFst q)) (Nat.fromBitsLE (pairSnd q)))))
theorem coordinateQuery_FP:coordinateQuery∈FP:=by
  have HT0:BinaryFn (fun q=>FormulaSignSlotRadialCenterValueLayout.tau (family (pairFst q)) (Nat.fromBitsLE (pairSnd q))):=
    tau_reindex family family_FP
  have HD1:BinaryFn (fun q=>FormulaSignSlotRadialCenterValueLayout.degree (family (pairFst q)) (Nat.fromBitsLE (pairSnd q))):=
    degree_reindex family family_FP
  have HT:=HT0.bits_mem_FP
  have HD0:=HD1.bits_mem_FP
  exact mem_FP_pair (by polytime [sample]) (mem_FP_pair HT HD0)
noncomputable def Guards (z:List Bool):Prop:=∀j<coordinates z,
  FormulaSignSlotRadialImplicitCenterSelection.Guards (coordinateQuery (pair z (BinaryNatCode.encode j)))
theorem evaluator:SpaceFunction (fun z=>[decide (Guards z)]):=by
  have E:=(FormulaSignSlotRadialImplicitCenterSelection.evaluator).precompose coordinateQuery coordinateQuery_FP
  exact IntegralPolynomialWindowTarskiDecision.flag_all _ _ E (BinaryFn.ofUnary coordinates_unary)
noncomputable def env:=FormulaSignSlotRadialImplicitSourceTest.env
attribute [local irreducible] FormulaSignSlotRadialCenterSelection.Guards FormulaSignSlotRadialValueWindowMeaning.Guard
  FormulaSignSlotRadialCenterValueFamily.Guards
private theorem coordinate_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j tau deg:ℕ):
    FormulaSignSlotRadialImplicitCenterSelection.Guards (FormulaSignSlotRadialImplicitCenterSelection.packet c w j tau deg) ↔
      FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialCoordinatePacket.packet (original c) j)
        (fun i=>env c w hw (4*i.val)) tau deg:=by
  unfold original header
  exact FormulaSignSlotRadialImplicitCenterSelection.guards_packet c w hw j tau deg

theorem guards_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (o ell:ℕ):
    Guards (packet c w o ell) ↔ FormulaSignSlotRadialValueWindowMeaning.Guard (family (packet c w o ell))
      (fun j=>env c w hw (4*j)):=by
  let z:=packet c w o ell
  have HC:context z=c:=by simp only [context,sample,z,packet,pairFst_pair]
  have HF:=family_original z
  rw [HC] at HF
  change (∀j<coordinates z,FormulaSignSlotRadialImplicitCenterSelection.Guards
    (coordinateQuery (pair z (BinaryNatCode.encode j)))) ↔ _
  have HQ (j:ℕ):coordinateQuery (pair z (BinaryNatCode.encode j))=
    FormulaSignSlotRadialImplicitCenterSelection.packet c w j
      (FormulaSignSlotRadialCenterValueLayout.tau (family z) j)
      (FormulaSignSlotRadialCenterValueLayout.degree (family z) j):=by
    simp only [coordinateQuery,FormulaSignSlotRadialImplicitCenterSelection.packet,sample,z,packet,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  simp_rw [HQ,coordinate_packet c w hw]
  change (∀j<coordinates z,FormulaSignSlotRadialCenterSelection.Guards
    (FormulaSignSlotRadialCoordinatePacket.packet (original c) j) (fun i=>env c w hw (4*i.val))
      (FormulaSignSlotRadialCenterValueLayout.tau (family z) j)
      (FormulaSignSlotRadialCenterValueLayout.degree (family z) j)) ↔ _
  have HN:coordinates z=FormulaSignSlotCenteredRadialGraph.N (original c)+FormulaSignSlotCenteredRadialGraph.d (original c)+1:=by
    simp only [coordinates,HC,FormulaSignSlotRadialValueCatalogueBounds.coordinates,FormulaSignSlotRadialFormalInput.spatial]
  rw [HN]
  have HAll:=FormulaSignSlotRadialCenterValueSelection.all_guards (original c) (fun j=>env c w hw (4*j))
    (fun i=>FormulaSignSlotRadialCenterValueLayout.tau (family z) i.val)
    (fun i=>FormulaSignSlotRadialCenterValueLayout.degree (family z) i.val)
  have HB:(∀j<FormulaSignSlotCenteredRadialGraph.N (original c)+FormulaSignSlotCenteredRadialGraph.d (original c)+1,
    FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialCoordinatePacket.packet (original c) j)
      (fun i=>env c w hw (4*i.val)) (FormulaSignSlotRadialCenterValueLayout.tau (family z) j)
      (FormulaSignSlotRadialCenterValueLayout.degree (family z) j)) ↔
      FormulaSignSlotRadialCenterValueFamily.Guards (original c) (fun j=>env c w hw (4*j.val))
        (fun i=>FormulaSignSlotRadialCenterValueLayout.tau (family z) i.val)
        (fun i=>FormulaSignSlotRadialCenterValueLayout.degree (family z) i.val):=by
    rw [←HAll]
    exact ⟨fun H i=>H i.val i.isLt,fun H j hj=>H ⟨j,hj⟩⟩
  exact HB.trans (guard_original (family z) (original c) HF (fun j=>env c w hw (4*j)))
end LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueSelection
