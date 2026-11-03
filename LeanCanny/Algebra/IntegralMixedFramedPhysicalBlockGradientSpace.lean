/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockSourceSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockObjectiveSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalNormalAtSpace
/-! # Charged full physical gradient terms, before physical powers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalHeightBits (Active)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthRowBits.value MvPolynomial.pderiv MvPolynomial.rename

noncomputable def multiplierSucc (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) :
    Fin (fullCount P D J base q) := multiplierIndex P D J base q ⟨selected q+1,by have H:=hs q;omega⟩

theorem multiplierSucc_unary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP)
    (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) (hselected : UnaryFn selected) :
    UnaryFn (fun q=>(multiplierSucc P D J base selected hs q).val) :=
  (((oldCount_unary P a D J c base hb).add (spatialCount_unary P a D J c base hb)).add
    (hselected.add (UnaryFn.const 1)))

noncomputable def normalPolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) :=
  FixedWidthMonomialBits.polynomial (fullCount P D J base) (fun q=>(multiplierSucc P D J base selected hs q).val)
    (fun _=>1) (IntegralMixedFramedPhysicalNormalAtBits.integer P D J base selected)

noncomputable def rawGradient (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) :
    MvPolynomial (Fin (fullCount P D J base q)) ℤ :=
  derivativePolynomial P D J base selected hs q-objectivePolynomial P D J base selected q-
    normalPolynomial P D J base selected hs q

noncomputable def gradient (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) (q : List Bool) :=
  if Active P (base q) then rawGradient P D J base selected hs q else 0

theorem gradient_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<spatialCount P D J base q) (hselected : UnaryFn selected)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J base) V (gradient P D J base selected hs) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) := by
  have HM:=mem_FP_comp hb (IntegralMixedFramedPhysicalHeightBits.modulusWord_FP P a)
  have ED:=derivative_evaluator P a D J c base hb selected hs hselected V hV target ht
  have EO:=objective_evaluator P a D J c base hb selected (BinaryFn.ofUnary hselected) V hV target ht
  have EN:=IntegralMixedFramedPhysicalNormalAtBits.monomial_evaluator P a D J c hc base hb selected
    (BinaryFn.ofUnary hselected) (fullCount P D J base) V (fun q=>(multiplierSucc P D J base selected hs q).val)
    (fun _=>1) target (fullCount_unary P a D J c base hb) hV
    (BinaryFn.ofUnary (multiplierSucc_unary P a D J c base hb selected hs hselected)) (BinaryFn.const 1) ht
  have ES:=FixedWidthRowBits.sub_evaluator (fullCount P D J base) V
    (derivativePolynomial P D J base selected hs) (objectivePolynomial P D J base selected) target
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) HM ED EO
  have EE:=FixedWidthRowBits.sub_evaluator (fullCount P D J base) V _ (normalPolynomial P D J base selected hs)
    target (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) HM ES EN
  exact FixedWidthRowBits.guarded_evaluator (fullCount P D J base) V (rawGradient P D J base selected hs) target
    (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base) _ (fun q=>Active P (base q))
    ((IntegralMixedFramedPhysicalHeightBits.active_FP P a).comp hb) EE (fun _ _=>rfl)

theorem multiplier_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (base : List Bool→List Bool) (hb : base∈FP)
    (selected : List Bool→ℕ) (hs : ∀q,selected q<spatialCount P D J base q) (hselected : UnaryFn selected)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J base) V
      (fun q=>MvPolynomial.X (multiplierSucc P D J base selected hs q)) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) :=
  FixedWidthRowBits.variable_evaluator (fullCount P D J base) V _ target _ (fullCount_unary P a D J c base hb) hV
    (multiplierSucc_unary P a D J c base hb selected hs hselected) ht
    (mem_FP_comp hb (IntegralMixedFramedPhysicalHeightBits.modulusWord_FP P a))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
