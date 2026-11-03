/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockLayout
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightCoefficientSpace
public import LeanCanny.Algebra.FixedWidthRowArithmetic
/-! # The literal objective-two multiplier of a physical gradient row -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthRowBits.value MvPolynomial.rename MvPolynomial.pderiv

noncomputable def freeIndex (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) :=
  let F:=IntegralMixedFramedPhysicalSourceAtBits.family P D J base
  (F.rule q).offset.val+(F.rule q).objective%(F.ambient q-(F.rule q).offset.val+1)

theorem freeIndex_binary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP) : BinaryFn (freeIndex P D J base) := by
  have H:=IntegralMixedFramedPhysicalSourceAtBits.metadata P a D J c base hb
  exact (BinaryFn.ofUnary H.offset).add
    (H.objective.mod (BinaryFn.ofUnary ((H.ambient.sub H.offset).add (UnaryFn.const 1))))

noncomputable def objectivePolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ) (q : List Bool) :=
  if selected q=freeIndex P D J base q then
    MvPolynomial.X (multiplierIndex P D J base q 0)+MvPolynomial.X (multiplierIndex P D J base q 0) else
    (0 : MvPolynomial (Fin (fullCount P D J base q)) ℤ)

theorem objective_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP)
    (selected : List Bool→ℕ) (hs : BinaryFn selected) (V : List Bool→ℕ) (hV : UnaryFn V)
    (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J base) V (objectivePolynomial P D J base selected) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) := by
  have HN:=fullCount_unary P a D J c base hb
  have HM:=mem_FP_comp hb (IntegralMixedFramedPhysicalHeightBits.modulusWord_FP P a)
  have HL : UnaryFn (fun q=>(multiplierIndex P D J base q 0).val):=
    ((oldCount_unary P a D J c base hb).add (spatialCount_unary P a D J c base hb)).of_eq (fun _=>rfl)
  have EV:=FixedWidthRowBits.variable_evaluator (fullCount P D J base) V (fun q=>multiplierIndex P D J base q 0)
    target (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) HN hV HL ht HM
  have EE:=FixedWidthRowBits.add_evaluator (fullCount P D J base) V
    (fun q=>MvPolynomial.X (multiplierIndex P D J base q 0)) (fun q=>MvPolynomial.X (multiplierIndex P D J base q 0))
    target (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) HM EV EV
  exact FixedWidthRowBits.guarded_evaluator (fullCount P D J base) V _ target
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) _ (fun q=>selected q=freeIndex P D J base q)
    (hs.eq (freeIndex_binary P a D J c base hb)) EE (fun _ _=>rfl)

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
