/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialPrincipalRadiusSource
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiRowLength
public import LeanCanny.Computation.WordResourceEnvelope
/-! # Original bounds for bounded actual principal-window contexts

Only the three original principal controls are bounded here. The generic
window row clips its own controls at every ordinal. Certified word envelopes
therefore give original-only bounds without an assumed polynomial family.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialPrincipalWindowBounds
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S"=>FormulaSignSlotRadialPrincipalRadiusSource.source

noncomputable def bound (u:List Bool):=FormulaSignSlotRadialEliminantPacked.resultDegree u
noncomputable def blockWidth (u:List Bool):=(2*bound u+1).size
noncomputable def rawContext (u:List Bool) (t d j:ℕ):=
  pair (pair u (pair (BinaryNatCode.encode t) (BinaryNatCode.encode d))) (BinaryNatCode.encode j)
noncomputable def rawBudget (u:List Bool):=4*u.length+7*blockWidth u+10

theorem bound_binary:BinaryFn bound:=FormulaSignSlotRadialEliminantFormalMass.degree_binary
theorem blockWidth_unary:UnaryFn blockWidth:=
  (UnaryFn.length ((((BinaryFn.const 2).mul bound_binary).add (BinaryFn.const 1)).bits_mem_FP)).of_eq
    (fun _=>BinaryNatCode.length_encode _)
theorem rawBudget_unary:UnaryFn rawBudget:=
  (((UnaryFn.const 4).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 7).mul blockWidth_unary)).add (UnaryFn.const 10)

theorem raw_length (u:List Bool) (t d j:ℕ) (ht:t ≤ bound u) (hd:d ≤ bound u) (hj:j ≤ 2*bound u+1):
    (rawContext u t d j).length ≤ rawBudget u:=by
  have HT:t.size ≤ blockWidth u:=Nat.size_le_size (ht.trans (by omega))
  have HD:d.size ≤ blockWidth u:=Nat.size_le_size (hd.trans (by omega))
  have HJ:j.size ≤ blockWidth u:=Nat.size_le_size hj
  simp only [rawContext,pair_length,BinaryNatCode.length_encode]
  unfold rawBudget
  omega

theorem rawDegree_exists:∃g:List Bool→ℕ,BinaryFn g ∧∀u c,c.length ≤ rawBudget u→(S).degree c ≤ g u:=
  FormulaSignSlotRadialPrincipalRadiusSource.degree_binary.wordEnvelope rawBudget_unary
noncomputable def rawDegreeCap:List Bool→ℕ:=Classical.choose rawDegree_exists
theorem rawDegreeCap_binary:BinaryFn rawDegreeCap:=(Classical.choose_spec rawDegree_exists).1
theorem raw_degree_le (u c:List Bool) (hc:c.length ≤ rawBudget u):(S).degree c ≤ rawDegreeCap u:=
  (Classical.choose_spec rawDegree_exists).2 u c hc

noncomputable def innerLimit (u:List Bool):=rawDegreeCap u+2
noncomputable def innerCount (u:List Bool):=6*(innerLimit u*(innerLimit u*innerLimit u))
noncomputable def queryBudget (u:List Bool):=4*rawBudget u+9*(innerLimit u).size+22

theorem innerLimit_binary:BinaryFn innerLimit:=rawDegreeCap_binary.add (BinaryFn.const 2)
theorem innerCount_binary:BinaryFn innerCount:=(BinaryFn.const 6).mul
  (innerLimit_binary.mul (innerLimit_binary.mul innerLimit_binary))
theorem queryBudget_unary:UnaryFn queryBudget:=
  (((UnaryFn.const 4).mul rawBudget_unary).add ((UnaryFn.const 9).mul
    ((UnaryFn.length innerLimit_binary.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)))).add (UnaryFn.const 22)

theorem inner_count_le (u c:List Bool) (hc:c.length ≤ rawBudget u):
    IntegralPolynomialWindowTarskiCatalogue.count S c ≤ innerCount u:=by
  have HD:(S).degree c+2 ≤ innerLimit u:=Nat.add_le_add_right (raw_degree_le u c hc) 2
  exact Nat.mul_le_mul_left 6 (Nat.mul_le_mul HD (Nat.mul_le_mul HD HD))
theorem row_length (u:List Bool) (t d j i:ℕ) (ht:t ≤ bound u) (hd:d ≤ bound u) (hj:j ≤ 2*bound u+1):
    (IntegralPolynomialWindowTarskiCatalogue.row S
      (pair (rawContext u t d j) (BinaryNatCode.encode i))).length ≤ queryBudget u:=by
  have HR:=raw_length u t d j ht hd hj
  have HQ:=IntegralPolynomialWindowTarskiCatalogue.row_length S (rawContext u t d j) (rawDegreeCap u) i
    (raw_degree_le u _ HR)
  unfold queryBudget innerLimit
  omega

end LeanCanny.Encoding.FormulaSignSlotRadialPrincipalWindowBounds
