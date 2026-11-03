/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockHeightRowSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockPowers
public import LeanCanny.Algebra.FixedWidthCoordinatePowerSpace
/-! # Native coefficient dispatcher for a whole fresh physical critical block -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalHeightBits (Active)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthRowBits.value MvPolynomial.pderiv MvPolynomial.rename

noncomputable def rawRowPolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (selected row : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) :=
  if row q<spatialCount P D J base q then gradient P D J base selected hs q
  else if row q=spatialCount P D J base q then sourcePolynomial P D J base q
  else heightRowPolynomial P D J T hr base selected hs q

noncomputable def rowPolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (selected row : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) :=
  if Active P (base q) ∧ row q<spatialCount P D J base q+(spatialCount P D J base q+1)
  then rawRowPolynomial P D J T hr base selected row hs q else 0

noncomputable def poweredRowPolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (selected row : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) :=
  CoordinatePowerSubstitution.substitute
    (fun i : Fin (fullCount P D J base q)=>powers P D J base (pair q (BinaryNatCode.encode i.val)))
    (rowPolynomial P D J T hr base selected row hs q)

theorem row_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (selected row : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (hselected : UnaryFn selected) (hr : BinaryFn row)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J base) V
      (rowPolynomial P D J c.critical.tables c.critical.represents base selected row hs) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) := by
  have HA:=BinaryFn.ofUnary (spatialCount_unary P a D J c base hb)
  have EE:=FixedWidthRowBits.branch_evaluator (fullCount P D J base) V
    (sourcePolynomial P D J base)
    (heightRowPolynomial P D J c.critical.tables c.critical.represents base selected hs) target
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) _ (hr.eq HA)
    (source_evaluator P a D J c base hb V hV target ht)
    (heightRow_evaluator P a D J c hc base hb selected hs hselected V hV target ht)
  have EG:=FixedWidthRowBits.branch_evaluator (fullCount P D J base) V
    (gradient P D J base selected hs) _ target
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) _ (hr.lt HA)
    (gradient_evaluator P a D J c hc base hb selected hs hselected V hV target ht) EE
  have HG:=((IntegralMixedFramedPhysicalHeightBits.active_FP P a).comp hb).and
    (hr.lt (HA.add (HA.add (BinaryFn.const 1))))
  exact FixedWidthRowBits.guarded_evaluator (fullCount P D J base) V _ target
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) _ _ HG EG (fun _ _=>rfl)

theorem poweredRow_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (selected row : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (hselected : UnaryFn selected) (hr : BinaryFn row)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J base) V
      (poweredRowPolynomial P D J c.critical.tables c.critical.represents base selected row hs) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) := by
  have HN:=fullCount_unary P a D J c base hb
  have HP:=powers_binary P a D J c base hb
  exact FixedWidthCoordinatePowerBits.evaluator (fullCount P D J base) V (powers P D J base) target _ _
    (powers_pos P D J base) HN hV HP ht
    (row_evaluator P a D J c hc base hb selected row hs hselected hr V hV _
      (FixedWidthCoordinatePowerBits.quotientTarget_FP _ _ _ _ HN hV HP ht))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
