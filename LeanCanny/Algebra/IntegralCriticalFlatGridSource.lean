/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatEulerRows
public import LeanCanny.Algebra.IntegralClearedCoefficientController

/-! # Original and derivative sources for flat cleared-grid tasks

Expression one differentiates the actual original low polynomial at the
decoded free rank. Other expressions retain the original polynomial.
Both branches keep the old algebra, basis, denominator, heights, target,
and clearing allowance. Native access assumes no coefficient evaluator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatGridSourceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def isDerivative (P : IntegralCriticalHistoryTask.Parameters) (c : List Bool) : Prop :=
  IntegralCriticalHistoryTask.get P .expression c = 1
instance (P : IntegralCriticalHistoryTask.Parameters) (c : List Bool) : Decidable (isDerivative P c) :=
  inferInstanceAs (Decidable (_ = _))

theorem isDerivative_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) :
    FPPred (isDerivative P) := (IntegralCriticalHistoryTask.get_binary P a .expression).eq (BinaryFn.const 1)

abbrev original (S : IntegralEulerBits.Source) := S.toGradient.toFrozen.toSource

noncomputable def derivativeInput (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) :
    IntegralDerivativeBits.Source where
  __ := original S
  selected c := IntegralCriticalGradientBits.freeIndex S.toGradient c
    (IntegralCriticalFlatEulerRowsBits.selected P S c)
  degree := S.degree
  degree_pos := S.degree_pos
  degree_le := S.degree_le
  degree_lt := S.degree_lt

theorem selected_unary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralEulerBits.Source) (h : IntegralEulerBits.Access S) :
    UnaryFn (fun c => (IntegralCriticalFlatEulerRowsBits.selected P S c).val) :=
  (UnaryFn.fromBitsLE_of_le (IntegralCriticalFlatEulerRowsBits.selected_binary P a S h).bits_mem_FP h.free
    (fun c => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
                 exact (IntegralCriticalFlatEulerRowsBits.selected P S c).isLt.le)).of_eq
    (fun _ => Nat.fromBitsLE_bits _)

noncomputable def derivativeInputAccess (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralEulerBits.Source) (h : IntegralEulerBits.Access S) : IntegralDerivativeBits.Access (derivativeInput P S) where
  __ := h.toGradient.toFrozen.toAccess
  selected := h.offset.add (selected_unary P a S h)
  degree := h.degree

noncomputable def derivative (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) :
    IntegralClearedCoefficientBits.Source := IntegralDerivativeBits.clearedSource (derivativeInput P S)

noncomputable def derivativeAccess (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralEulerBits.Source) (h : IntegralEulerBits.Access S) : IntegralClearedCoefficientBits.Access (derivative P S) :=
  IntegralDerivativeBits.clearedAccess (derivativeInput P S) (derivativeInputAccess P a S h)

noncomputable def source (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) :
    IntegralClearedCoefficientBits.Source :=
  { original S with
    polynomial := fun c => if isDerivative P c then (derivative P S).polynomial c else (original S).polynomial c
    support := by
      intro c
      let := S.ring c
      by_cases hd : isDerivative P c
      · simpa only [ite_eq_left hd, derivative, IntegralDerivativeBits.clearedSource, derivativeInput] using
          (derivative P S).support c
      · simpa only [ite_eq_right hd] using (original S).support c }

theorem polynomial (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    letI := S.ring c
    (source P S).polynomial c = if isDerivative P c then
      MvPolynomial.pderiv (IntegralCriticalGradientBits.freeIndex S.toGradient c
        (IntegralCriticalFlatEulerRowsBits.selected P S c)) ((original S).polynomial c)
      else (original S).polynomial c := rfl

def coefficient (P : IntegralCriticalHistoryTask.Parameters) (base derived : List Bool → List Bool) (p : List Bool) : List Bool :=
  if isDerivative P (IntegralDerivativeBits.original p) then derived p else base p

theorem coefficient_packet (P : IntegralCriticalHistoryTask.Parameters) (base derived : List Bool → List Bool)
    (c : List Bool) (k r t : ℕ) :
    coefficient P base derived (pair (IntegralClearedCoefficientBits.context c r t) (BinaryNatCode.encode k)) =
      if isDerivative P c then derived (pair (IntegralClearedCoefficientBits.context c r t) (BinaryNatCode.encode k))
      else base (pair (IntegralClearedCoefficientBits.context c r t) (BinaryNatCode.encode k)) := by
  simp only [coefficient, IntegralDerivativeBits.original, IntegralClearedCoefficientBits.context, pairFst_pair]

noncomputable def access (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralEulerBits.Source) (h : IntegralEulerBits.Access S) : IntegralClearedCoefficientBits.Access (source P S) where
  arity := h.arity
  free := h.free
  offset := h.offset
  sourceWidth := h.sourceWidth
  targetWidth := h.targetWidth
  rank := h.rank
  allowance := h.allowance
  target := h.target
  row := h.row
  col := h.col
  modulus := h.modulus
  coefficient := coefficient P h.coefficient (derivativeAccess P a S h).coefficient
  height := h.height
  denominator := h.denominator
  coefficient_eq c k r t := by
    let := S.ring c
    rw [coefficient_packet]
    by_cases hd : isDerivative P c
    · rw [ite_eq_left hd]
      simpa only [source, hd, ite_true, derivative, IntegralDerivativeBits.clearedSource, derivativeInput] using
        (derivativeAccess P a S h).coefficient_eq c k r t
    · rw [ite_eq_right hd]
      simpa only [source, hd, ite_false] using h.coefficient_eq c k r t
  height_eq := h.height_eq
  denominator_eq := h.denominator_eq

theorem derivative_value (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    (derivative P S).value c = (IntegralCriticalGradientBits.family S.toGradient).value
      (IntegralCriticalFlatEulerRowsBits.packet P S c) := by
  let := S.ring c
  exact (IntegralCriticalGradientBits.packet S.toGradient c
    (IntegralCriticalFlatEulerRowsBits.selected P S c) (S.target c)).symm

theorem value (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    (source P S).value c = if isDerivative P c then (derivative P S).value c else (original S).value c := by
  let := S.ring c
  by_cases hd : isDerivative P c <;>
    simp only [IntegralClearedCoefficientBits.Source.value, IntegralClearedCoefficientBits.Source.targetExponent,
      source, hd, ite_true, ite_false]
  all_goals rfl

noncomputable def actual (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) := source P (IntegralCriticalFlatEulerRowsBits.source P F q)

noncomputable def actualAccess (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : IntegralClearedCoefficientBits.Access (actual P F q) :=
  access P a _ (IntegralCriticalFlatEulerRowsBits.access P a F q h)

theorem actual_value_derivative (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) (hd : isDerivative P c) :
    (actual P F q).value c =
      (IntegralCriticalGradientBits.family (IntegralCriticalFlatEulerRowsBits.source P F q).toGradient).value
        (IntegralCriticalFlatEulerRowsBits.packet P (IntegralCriticalFlatEulerRowsBits.source P F q) c) := by
  change (source P _).value c = _
  rw [value, ite_eq_left hd, derivative_value]

theorem actual_value_original (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) (hd : ¬isDerivative P c) :
    (actual P F q).value c = (original (IntegralCriticalFlatEulerRowsBits.source P F q)).value c := by
  change (source P _).value c = _
  rw [value, ite_eq_right hd]

end LeanCanny.Algebra.IntegralCriticalFlatGridSourceBits
