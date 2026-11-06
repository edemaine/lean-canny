/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueSelection
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitWindowAtom
/-! # Actual full VALUE coefficient and interval decisions on the same own tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input
local notation "Raw"=>FormulaSignSlotRadialValueRadiusSource.source
local notation "Nraw"=>FormulaSignSlotRadialValueWindowCatalogue.centers
local notation "HD"=>FormulaSignSlotRadialValueWindowCatalogue.dimension_eq
local notation "ctx"=>FormulaSignSlotRadialImplicitValueSelection.rawContext
local notation "hN"=>FormulaSignSlotRadialImplicitValueSelection.dimension
local notation "D"=>FormulaSignSlotRadialImplicitValueSelection.degree
local notation "env"=>FormulaSignSlotRadialImplicitSourceTest.env
local notation "payload"=>FormulaSignSlotRadialImplicitValueSelection.packet
noncomputable def atom:=FormulaSignSlotRadialImplicitWindowAtom.atom Raw Nraw HD ctx hN

theorem atom_evaluator:SpaceFunction atom:=FormulaSignSlotRadialImplicitWindowAtom.atom_evaluator Raw Nraw HD ctx hN
  FormulaSignSlotRadialValueRadiusSource.degree_fit FormulaSignSlotRadialValueRadiusSource.access
  FormulaSignSlotRadialValueWindowCatalogue.centers_unary FormulaSignSlotRadialImplicitValueSelection.rawContext_FP

theorem packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (o ell:ℕ):
    IntegralPolynomialWindowTarskiDecisionReadback.Packet Raw Nraw HD atom (payload c w o ell) (ctx (payload c w o ell))
      (env c w hw 3) (fun i=>env c w hw (4*i.val)):=
  FormulaSignSlotRadialImplicitWindowAtom.packet Raw Nraw HD ctx hN c w
    (pair (BinaryNatCode.encode o) (BinaryNatCode.encode ell)) hw

noncomputable def Zero (z:List Bool):Prop:=IntegralPolynomialWindowTarskiDecision.AllZero D atom z
noncomputable def Empty (z:List Bool):Prop:=IntegralPolynomialWindowTarskiDecision.Empty D atom z
theorem zero_evaluator:SpaceFunction (fun z=>[decide (Zero z)]):=
  IntegralPolynomialWindowTarskiDecision.allZero_evaluator D atom FormulaSignSlotRadialImplicitValueSelection.degree_binary atom_evaluator
theorem empty_evaluator:SpaceFunction (fun z=>[decide (Empty z)]):=
  IntegralPolynomialWindowTarskiDecision.empty_evaluator D atom FormulaSignSlotRadialImplicitValueSelection.degree_binary atom_evaluator

theorem zero_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (o ell:ℕ):
    Zero (payload c w o ell) ↔FormulaSignSlotRadialValueWindowMeaning.rawHead (ctx (payload c w o ell))
      (fun j=>env c w hw (4*j))=0:=by
  have H:=(IntegralPolynomialWindowTarskiDecisionReadback.allZero Raw Nraw HD D atom
    (payload c w o ell) (ctx (payload c w o ell)) (env c w hw 3) (fun i=>env c w hw (4*i.val)) rfl
      (packet c w hw o ell)).trans (IntegralPolynomialWindowTarski.zero_iff Raw Nraw HD _ _)
  exact H

theorem empty_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (o ell:ℕ) (hb:0<env c w hw 3):
    Empty (payload c w o ell) ↔∀r:ℝ,
      (FormulaSignSlotRadialValueWindowMeaning.rawHead (ctx (payload c w o ell)) (fun j=>env c w hw (4*j))).eval r=0 →
        r ∉ Ioo 0 (env c w hw 3):=
  IntegralPolynomialWindowTarskiDecisionReadback.interval Raw Nraw HD D atom (payload c w o ell)
    (ctx (payload c w o ell)) (env c w hw 3) (fun i=>env c w hw (4*i.val)) rfl (packet c w hw o ell) hb
end LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueTest
