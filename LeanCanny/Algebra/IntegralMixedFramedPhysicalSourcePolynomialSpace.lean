/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalLowSpace
public import LeanCanny.Algebra.FixedWidthFermatHeadSpace
/-! # Literal physical source coefficients from original LOW and leading leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalSourcePolynomialBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalLowBits (arity width low family indices modulusWord)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family

noncomputable def leading (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  ((family P D J).spatial q).leading
noncomputable def degree (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  ((family P D J).spatial q).degree
noncomputable def polynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  FermatCriticalHomogenization.polynomial (low P D J q) (leading P D J q) (degree P D J q)

theorem leading_value (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedFramedScalarLeadingBits.value P D J q=residueBits (leading P D J q : ZMod (modulus P q)) := by
  rw [IntegralMixedFramedScalarLeadingBits.physical_value]
  rfl

theorem leading_space (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) :
    SpaceFunction (fun q=>residueBits (leading P D J q : ZMod (Nat.fromBitsLE (modulusWord P q)+1))) := by
  apply c.scalar.leading.congr
  funext q
  rw [leading_value]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) rfl
    (IntegralMixedFramedPhysicalLowBits.modulusWord_value P q).symm

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (arity P D J) V (polynomial P D J) target (modulusWord P)) := by
  have HM:=IntegralMixedFramedPhysicalLowBits.metadata P a D J c
  have HA : UnaryFn (arity P D J):=HM.ambient.add (UnaryFn.const 1)
  have HL:=IntegralMixedFramedPhysicalLowBits.evaluator P a D J c V hV target ht
  have HH:=FixedWidthFermatHeadBits.evaluator (arity P D J) V (degree P D J) (leading P D J)
    target (modulusWord P) (fun q=>residueBits (leading P D J q : ZMod (Nat.fromBitsLE (modulusWord P q)+1)))
    HA hV HM.degree ht (IntegralMixedFramedPhysicalLowBits.modulusWord_FP P a) (leading_space P D J c) (fun _=>rfl)
  exact (FixedWidthRowBits.add_evaluator (arity P D J) V (low P D J)
    (FixedWidthFermatHeadBits.head (arity P D J) (degree P D J) (leading P D J)) target (modulusWord P)
    (IntegralMixedFramedPhysicalLowBits.modulusWord_FP P a) HL HH).congr (funext fun _=>rfl)

end LeanCanny.Algebra.IntegralMixedFramedPhysicalSourcePolynomialBits
