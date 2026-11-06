/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitWindowAtom
public import LeanCanny.Encoding.FormulaSignSlotRadialJointSquarefreeIndexRetention
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitCenterSelection
/-! # Actual full principal windows on the same implicit own word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitPrincipalWindow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial
  FormulaSignSlotRadialPrincipalRadiusSource.degree FormulaSignSlotRadialPrincipalRadiusSource.width
  FormulaSignSlotRadialCenterPrincipalFamily.principal FormulaSignSlotRadialCenterPrincipalFamily.degreeBound
  FormulaSignSlotRadialCenterPrincipalFamily.width
local notation "Raw"=>FormulaSignSlotRadialPrincipalRadiusSource.source
local notation "N"=>FormulaSignSlotRadialCutWindowSources.principalCenters
local notation "HD"=>FormulaSignSlotRadialCutWindowSources.principal_dimension
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input

def sample (z:List Bool):=pairFst z
def context (z:List Bool):=pairFst (sample z)
def header (c:List Bool):=FormulaSignSlotRadialImplicitGridTest.header c
noncomputable def original (c:List Bool):=FormulaSignSlotRadialJointLayout.source true (header c)
def coordinateWord (z:List Bool):=pairFst (pairSnd z)
def tauWord (z:List Bool):=pairFst (pairSnd (pairSnd z))
def degreeWord (z:List Bool):=pairFst (pairSnd (pairSnd (pairSnd z)))
def orderWord (z:List Bool):=pairSnd (pairSnd (pairSnd (pairSnd z)))
noncomputable def radial (z:List Bool):=FormulaSignSlotRadialCoordinatePacket.writer
  (pair (original (context z)) (coordinateWord z))
noncomputable def family (z:List Bool):=pair (radial z) (pair (tauWord z) (degreeWord z))
noncomputable def rawContext (z:List Bool):=pair (family z) (orderWord z)
noncomputable def degree (z:List Bool):=(Raw).degree (rawContext z)

theorem original_FP:original∈FP:=mem_FP_comp (f:=header) (g:=FormulaSignSlotRadialJointLayout.source true)
  FormulaSignSlotRadialImplicitGridTest.header_FP (FormulaSignSlotRadialJointLayout.source_FP true)
theorem radial_FP:radial∈FP:=mem_FP_comp
  (mem_FP_pair (mem_FP_comp (f:=context) (g:=original)
    (show context∈FP by polytime [context,sample]) original_FP)
    (show coordinateWord∈FP by polytime [coordinateWord])) FormulaSignSlotRadialCoordinatePacket.writer_FP
theorem rawContext_FP:rawContext∈FP:=mem_FP_pair
  (mem_FP_pair radial_FP (show (fun z=>pair (tauWord z) (degreeWord z))∈FP by polytime [tauWord,degreeWord]))
  (show orderWord∈FP by polytime [orderWord])
theorem degree_binary:BinaryFn degree:=FormulaSignSlotRadialPrincipalRadiusSource.degree_binary.comp rawContext_FP
private theorem root_eq (z:List Bool):FormulaSignSlotRadialCutWindowSources.principalRoot (rawContext z)=original (context z):=by
  simp only [FormulaSignSlotRadialCutWindowSources.principalRoot,rawContext,family,
    radial,FormulaSignSlotRadialCoordinatePacket.writer,pairFst_pair]
theorem dimension (z:List Bool):N (rawContext z)=FormulaSignSlotRadialJointLayout.centerCount (header (context z)):=by
  change FormulaSignSlotSource.dimension (FormulaSignSlotRadialCutWindowSources.principalRoot (rawContext z))=_
  rw [root_eq]
  rfl
theorem raw_fit (c:List Bool):(Raw).degree c<2^(Raw).width c:=
  FormulaSignSlotRadialPrincipalRadiusSource.degree_fit c
attribute [local irreducible] FormulaSignSlotRadialPrincipalRadiusSource.source rawContext
noncomputable def atom:=FormulaSignSlotRadialImplicitWindowAtom.atom Raw N HD rawContext dimension
theorem atom_evaluator:SpaceFunction atom:=FormulaSignSlotRadialImplicitWindowAtom.atom_evaluator
  Raw N HD rawContext dimension raw_fit
    FormulaSignSlotRadialPrincipalRadiusSource.access FormulaSignSlotRadialCutWindowSources.principalCenters_unary rawContext_FP
noncomputable def Empty:=IntegralPolynomialWindowTarskiDecision.Empty degree atom
noncomputable def Zero:=IntegralPolynomialWindowTarskiDecision.AllZero degree atom
theorem empty_evaluator:SpaceFunction (fun z=>[decide (Empty z)]):=
  IntegralPolynomialWindowTarskiDecision.empty_evaluator degree atom degree_binary atom_evaluator
theorem zero_evaluator:SpaceFunction (fun z=>[decide (Zero z)]):=
  IntegralPolynomialWindowTarskiDecision.allZero_evaluator degree atom degree_binary atom_evaluator

def packet (c w:List Bool) (j t d p:ℕ):=pair (pair c w)
  (pair (BinaryNatCode.encode j) (pair (BinaryNatCode.encode t) (pair (BinaryNatCode.encode d) (BinaryNatCode.encode p))))
noncomputable def env:=FormulaSignSlotRadialImplicitSourceTest.env

theorem raw_packet (c w:List Bool) (j t d p:ℕ):
    rawContext (packet c w j t d p)=FormulaSignSlotRadialPrincipalWindowBounds.rawContext
      (FormulaSignSlotRadialCoordinatePacket.packet (original c) j) t d p:=by
  simp only [rawContext,family,radial,context,sample,coordinateWord,tauWord,degreeWord,orderWord,packet,
    pairFst_pair,pairSnd_pair,FormulaSignSlotRadialCoordinatePacket.writer_packet,
    FormulaSignSlotRadialPrincipalWindowBounds.rawContext]

theorem atom_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j t d p:ℕ):
    IntegralPolynomialWindowTarskiDecisionReadback.Packet Raw N HD atom
      (packet c w j t d p) (rawContext (packet c w j t d p))
      (env c w hw 3) (fun i=>env c w hw (4*i.val)):=
  FormulaSignSlotRadialImplicitWindowAtom.packet Raw N HD rawContext dimension c w _ hw

theorem zero_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j t d p:ℕ):
    Zero (packet c w j t d p) ↔ IntegralPolynomialWindowTarski.baseHead Raw N HD
      (rawContext (packet c w j t d p)) (fun i=>env c w hw (4*i.val))=0:=
  (IntegralPolynomialWindowTarskiDecisionReadback.allZero Raw N HD degree atom _ _ _ _ rfl
    (atom_packet c w hw j t d p)).trans (IntegralPolynomialWindowTarski.zero_iff Raw N HD _ _)

theorem empty_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j t d p:ℕ)
    (hb:0<env c w hw 3):
    Empty (packet c w j t d p) ↔ ∀r,(IntegralPolynomialWindowTarski.baseHead Raw N HD
      (rawContext (packet c w j t d p)) (fun i=>env c w hw (4*i.val))).eval r=0 → r ∉ Ioo 0 (env c w hw 3):=
  IntegralPolynomialWindowTarskiDecisionReadback.interval Raw N HD degree atom _ _ _ _ rfl
    (atom_packet c w hw j t d p) hb

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitPrincipalWindow
