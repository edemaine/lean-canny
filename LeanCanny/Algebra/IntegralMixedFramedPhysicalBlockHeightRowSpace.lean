/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockGradientSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockHeightSpace
/-! # Active ancestral-height and inactive-multiplier row coefficients -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalHeightBits (Active)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthRowBits.value MvPolynomial.rename MvPolynomial.pderiv

noncomputable def normalAmbientPolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) :=
  FixedWidthMonomialBits.polynomial (fullCount P D J base)
    (fun q=>(ambientIndex P D J base q ⟨selected q,hs q⟩).val) (fun _=>1)
    (IntegralMixedFramedPhysicalNormalAtBits.integer P D J base selected)

noncomputable def activeHeightPolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) :=
  normalAmbientPolynomial P D J base selected hs q-heightPolynomial P D J T hr base q

noncomputable def heightRowPolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) :=
  if Active P (base q) then
    if selected q<((IntegralMixedFramedPhysicalSourceAtBits.family P D J base).rule q).offset.val then
      activeHeightPolynomial P D J T hr base selected hs q else MvPolynomial.X (multiplierSucc P D J base selected hs q)
  else 0

theorem activeHeight_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (hselected : UnaryFn selected)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J base) V
      (activeHeightPolynomial P D J c.critical.tables c.critical.represents base selected hs) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) := by
  have HA : UnaryFn (fun q=>(ambientIndex P D J base q ⟨selected q,hs q⟩).val):=
    (oldCount_unary P a D J c base hb).add hselected
  have EN:=IntegralMixedFramedPhysicalNormalAtBits.monomial_evaluator P a D J c hc base hb selected
    (BinaryFn.ofUnary hselected) (fullCount P D J base) V _ (fun _=>1) target
    (fullCount_unary P a D J c base hb) hV (BinaryFn.ofUnary HA) (BinaryFn.const 1) ht
  have EH:=height_evaluator P a D J c hc base hb V hV target ht
  exact FixedWidthRowBits.sub_evaluator (fullCount P D J base) V _ _ target
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)
    (mem_FP_comp hb (IntegralMixedFramedPhysicalHeightBits.modulusWord_FP P a)) EN EH

theorem heightRow_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (hselected : UnaryFn selected)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J base) V
      (heightRowPolynomial P D J c.critical.tables c.critical.represents base selected hs) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) := by
  have HF:=(BinaryFn.ofUnary hselected).lt
    (BinaryFn.ofUnary (IntegralMixedFramedPhysicalSourceAtBits.metadata P a D J c base hb).offset)
  have EE:=FixedWidthRowBits.branch_evaluator (fullCount P D J base) V
    (activeHeightPolynomial P D J c.critical.tables c.critical.represents base selected hs)
    (fun q=>MvPolynomial.X (multiplierSucc P D J base selected hs q)) target
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) _ HF
    (activeHeight_evaluator P a D J c hc base hb selected hs hselected V hV target ht)
    (multiplier_evaluator P a D J c base hb selected hs hselected V hV target ht)
  exact FixedWidthRowBits.guarded_evaluator (fullCount P D J base) V _ target
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) _ (fun q=>Active P (base q))
    ((IntegralMixedFramedPhysicalHeightBits.active_FP P a).comp hb) EE (fun _ _=>rfl)

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
