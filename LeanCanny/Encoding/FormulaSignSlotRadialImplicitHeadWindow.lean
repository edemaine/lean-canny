/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitWindowAtom
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitCenterSelection
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusWindowInterval
/-! # Literal head-window decisions on the implicit sampler's own word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitHeadWindow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
local notation "Raw" => FormulaSignSlotRadialRadiusWindowBridge.source
local notation "N" => FormulaSignSlotRadialRadiusWindowBridge.centers
local notation "HD" => FormulaSignSlotRadialRadiusWindowBridge.dimension

def sample (z:List Bool):=pairFst z
def context (z:List Bool):=pairFst (sample z)
def coordinateWord (z:List Bool):=pairFst (pairSnd z)
def tauWord (z:List Bool):=pairFst (pairSnd (pairSnd z))
def etaWord (z:List Bool):=pairSnd (pairSnd (pairSnd z))
noncomputable def radial (z:List Bool):=FormulaSignSlotRadialCoordinatePacket.writer
  (pair (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitGridTest.header (context z))) (coordinateWord z))
noncomputable def rawContext (z:List Bool):=pair (radial z) (pair (tauWord z) (etaWord z))
theorem rawContext_FP:rawContext∈FP:=by
  have HR:radial∈FP:=mem_FP_comp (mem_FP_pair
    (mem_FP_comp (f:=context) (g:=fun c=>FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitGridTest.header c))
      (show context∈FP by polytime [context,sample])
      (mem_FP_comp (f:=FormulaSignSlotRadialImplicitGridTest.header) (g:=FormulaSignSlotRadialJointLayout.source true)
        FormulaSignSlotRadialImplicitGridTest.header_FP (FormulaSignSlotRadialJointLayout.source_FP true)))
    (show coordinateWord∈FP by polytime [coordinateWord])) FormulaSignSlotRadialCoordinatePacket.writer_FP
  exact mem_FP_pair HR (mem_FP_pair (by polytime [tauWord]) (by polytime [etaWord]))
attribute [local irreducible] FormulaSignSlotSource.dimension

theorem center_count (z:List Bool):N (rawContext z)=FormulaSignSlotRadialJointLayout.centerCount
    (FormulaSignSlotRadialImplicitGridTest.header (FormulaSignSlotRadialImplicitWindowAtom.context z)):=by
  simp only [rawContext,radial,FormulaSignSlotRadialRadiusWindowBridge.centers,
    FormulaSignSlotRadialRadiusHeadReader.arity,FormulaSignSlotRadialRadiusHeadReader.original,
    FormulaSignSlotRadialCoordinatePacket.writer,pairFst_pair]
  rfl
private theorem centers_unary:UnaryFn N:=FormulaSignSlotSource.dimension_unary.comp
  (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
private theorem raw_fit (c:List Bool):(Raw).degree c<2^(Raw).width c:=
  FormulaSignSlotRadialEliminantPacked.result_fit (pairFst c)
attribute [local irreducible] FormulaSignSlotRadialRadiusHeadSource.source rawContext
noncomputable def atom:=FormulaSignSlotRadialImplicitWindowAtom.atom Raw N HD rawContext center_count
theorem atom_evaluator:SpaceFunction atom:=
  FormulaSignSlotRadialImplicitWindowAtom.atom_evaluator Raw N HD rawContext center_count raw_fit
    FormulaSignSlotRadialRadiusHeadSource.access centers_unary rawContext_FP
noncomputable def degree (z:List Bool):=(Raw).degree (rawContext z)
theorem degree_binary:BinaryFn degree:=FormulaSignSlotRadialRadiusHeadSource.access.degree.comp rawContext_FP
noncomputable def Empty (z:List Bool):Prop:=IntegralPolynomialWindowTarskiDecision.Empty degree atom z
theorem empty_evaluator:SpaceFunction (fun z=>[decide (Empty z)]):=
  IntegralPolynomialWindowTarskiDecision.empty_evaluator degree atom degree_binary atom_evaluator

def packet (c w:List Bool) (j tau e:ℕ):=pair (pair c w)
  (pair (BinaryNatCode.encode j) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode e)))
noncomputable def radiusContext (c:List Bool) (j:ℕ):=FormulaSignSlotRadialCoordinatePacket.packet
  (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitGridTest.header c)) j
noncomputable def center (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j:ℕ):
    Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount (radiusContext c j))→ℝ:=
  fun i=>FormulaSignSlotRadialImplicitSourceTest.env c w hw (4*i.val)
noncomputable def bound (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):=
  FormulaSignSlotRadialImplicitSourceTest.env c w hw 3

theorem raw_packet (c w:List Bool) (j tau e:ℕ):rawContext (packet c w j tau e)=
    FormulaSignSlotRadialRadiusTarskiCatalogue.headContext (radiusContext c j) tau e:=by
  simp only [rawContext,radial,context,sample,coordinateWord,tauWord,etaWord,packet,
    pairFst_pair,pairSnd_pair,radiusContext,FormulaSignSlotRadialRadiusTarskiCatalogue.headContext]
  rw [FormulaSignSlotRadialCoordinatePacket.writer_packet]

theorem packet_readback (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j tau e:ℕ):
    IntegralPolynomialWindowTarskiDecisionReadback.Packet Raw N HD atom (packet c w j tau e)
      (rawContext (packet c w j tau e)) (bound c w hw)
      (fun i=>FormulaSignSlotRadialImplicitSourceTest.env c w hw (4*i.val)):=by
  exact FormulaSignSlotRadialImplicitWindowAtom.packet Raw N HD rawContext center_count
    c w (pair (BinaryNatCode.encode j) (pair (BinaryNatCode.encode tau) (BinaryNatCode.encode e))) hw
attribute [local irreducible] atom degree radiusContext center bound Empty

theorem head_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j tau e:ℕ):
    IntegralPolynomialWindowTarski.baseHead Raw N HD (rawContext (packet c w j tau e))
      (fun i=>FormulaSignSlotRadialImplicitSourceTest.env c w hw (4*i.val))=
      FormulaSignSlotRadialRadiusHeadInterval.specialized (radiusContext c j) (center c w hw j) tau e :=by
  rw [raw_packet]
  have H:=FormulaSignSlotRadialRadiusWindowInterval.base_head_eq (radiusContext c j) tau e (center c w hw j)
  have HV:FormulaSignSlotRadialRadiusWindowSigns.center (radiusContext c j) tau e (center c w hw j)=
      (fun i=>FormulaSignSlotRadialImplicitSourceTest.env c w hw (4*i.val)):=by
    funext i
    simp only [FormulaSignSlotRadialRadiusWindowSigns.center,IntegralPolynomialWindowTarski.intervalCastValues,center,Fin.val_cast]
  rw [HV] at H
  exact H

theorem empty_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (j tau e:ℕ) (hb:0<bound c w hw):
    Empty (packet c w j tau e) ↔
      ∀r,(FormulaSignSlotRadialRadiusHeadInterval.specialized (radiusContext c j)
        (center c w hw j) tau e).eval r=0 → r∉Ioo 0 (bound c w hw):=by
  have HP:=packet_readback c w hw j tau e
  have HE:=IntegralPolynomialWindowTarskiDecisionReadback.interval Raw N HD degree atom
    (packet c w j tau e) (rawContext (packet c w j tau e)) (bound c w hw)
    (fun i=>FormulaSignSlotRadialImplicitSourceTest.env c w hw (4*i.val)) (by simp only [degree]) HP hb
  have HC:=head_packet c w hw j tau e
  rw [HC] at HE
  simpa only [Empty] using HE

noncomputable def Zero (z:List Bool):Prop:=IntegralPolynomialWindowTarskiDecision.AllZero degree atom z
theorem zero_evaluator:SpaceFunction (fun z=>[decide (Zero z)]):=
  IntegralPolynomialWindowTarskiDecision.allZero_evaluator degree atom degree_binary atom_evaluator

theorem zero_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j tau e:ℕ):
    Zero (packet c w j tau e) ↔ FormulaSignSlotRadialRadiusHeadInterval.specialized
      (radiusContext c j) (center c w hw j) tau e=0:=by
  have HE:=IntegralPolynomialWindowTarskiDecisionReadback.allZero Raw N HD degree atom
    (packet c w j tau e) (rawContext (packet c w j tau e)) (bound c w hw)
    (fun i=>FormulaSignSlotRadialImplicitSourceTest.env c w hw (4*i.val)) (by simp only [degree])
    (packet_readback c w hw j tau e)
  rw [IntegralPolynomialWindowTarski.zero_iff,head_packet] at HE
  exact HE

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitHeadWindow
