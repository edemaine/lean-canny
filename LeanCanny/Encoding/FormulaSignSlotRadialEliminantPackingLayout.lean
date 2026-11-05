/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantInput
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterSupport
public import LeanCanny.ETR.CoerciveSourceControls
public import LeanCanny.Algebra.CoerciveHomogeneousLayout
/-! # Original-only native widths for the retained eliminant coefficient block

The context is an original input packet: its first field is the original source
and its coordinate field selects the observable. Other packet fields do not
alter the polynomial or any dimension bound.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantPackingLayout
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def spatial (c : List Bool) := FormulaSignSlotRadialFormalInput.spatial (pairFst c)
noncomputable def sourceDegree (c : List Bool) := degreeBudget (pairFst c)
noncomputable def width (c : List Bool) := CoerciveCoordinateEliminant.width (spatial c) (sourceDegree c)
noncomputable def layout : MacaulayBits.Layout where
  arity c := spatial c + 1
  width := width
  degree c i := if i = 0 then 1 else 2 * sourceDegree c + 1

theorem spatial_unary : UnaryFn spatial := FormulaSignSlotRadialFormalInput.spatial_unary.comp pairFst_mem_FP
theorem sourceDegree_unary : UnaryFn sourceDegree := degreeBudget_unary.comp pairFst_mem_FP
theorem width_unary : UnaryFn width := by
  have HL := (spatial_unary.mul ((UnaryFn.const 2).mul sourceDegree_unary)).add (UnaryFn.const 1)
  have HD := ((UnaryFn.const 2).mul sourceDegree_unary).add (UnaryFn.const 1)
  exact ((HL.max HD).size).of_eq (fun c => by
    rw [width, CoerciveCoordinateEliminant.width, ETR.CoerciveSourceControls.level_eq])

theorem layout_polyTime : layout.PolyTime := by
  refine ⟨spatial_unary.add (UnaryFn.const 1), width_unary, ?_⟩
  have HI := FPPred.eq (UnaryFn.length pairSnd_mem_FP) (UnaryFn.const 0)
  exact UnaryFn.ite HI (UnaryFn.const 1)
    (((UnaryFn.const 2).mul (sourceDegree_unary.comp pairFst_mem_FP)).add (UnaryFn.const 1))

theorem degrees_eq (c : List Bool) : MacaulayBits.Degrees layout c =
    CoerciveCriticalHomogenization.finDegree (sourceDegree c) := by
  funext i
  exact (CoerciveHomogeneousLayout.finDegree_eq (sourceDegree c) i).symm

noncomputable def columnExponent (c : List Bool) := (spatial c + 1) * width c
noncomputable def columns (c : List Bool) := FixedWidthPolynomial.count (spatial c + 1) (width c)
noncomputable def parameterDegree (c : List Bool) := FormulaSignSlotRadialEliminantParameterSupport.degree (pairFst c)
noncomputable def parameterWidth (c : List Bool) := 2 * columnExponent c + parameterDegree c + 3

theorem columnExponent_unary : UnaryFn columnExponent := (spatial_unary.add (UnaryFn.const 1)).mul width_unary
theorem columns_eq (c : List Bool) : columns c = 2 ^ columnExponent c := by
  simp only [columns, columnExponent, FixedWidthPolynomial.count, ← pow_mul, Nat.mul_comm]
theorem columns_binary : BinaryFn columns :=
  ((BinaryFn.const 2).powUnary columnExponent_unary).of_eq (fun c => (columns_eq c).symm)
theorem columns_pos (c : List Bool) : 0 < columns c := by rw [columns_eq]; exact Nat.two_pow_pos _

theorem parameterDegree_unary : UnaryFn parameterDegree :=
  ((FormulaSignSlotSource.dimension_unary.comp pairFst_mem_FP).add (UnaryFn.const 3)).mul
    (((UnaryFn.const 2).mul sourceDegree_unary).add (UnaryFn.const 2))
theorem parameterWidth_unary : UnaryFn parameterWidth :=
  (((UnaryFn.const 2).mul columnExponent_unary).add parameterDegree_unary).add (UnaryFn.const 3)

theorem parameter_fit (c : List Bool) : parameterDegree c < 2 ^ parameterWidth c := by
  have H : parameterDegree c < parameterWidth c := by unfold parameterWidth; omega
  exact H.trans Nat.lt_two_pow_self

theorem columns_even (c : List Bool) : Even (columns c) := by
  have HW : 0 < width c := by
    apply Nat.size_pos.mpr
    exact (Macaulay.level_pos _).trans_le (le_max_left _ _)
  have HE : 0 < columnExponent c := Nat.mul_pos (Nat.succ_pos _) HW
  obtain ⟨k, HK⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt HE)
  rw [columns_eq, HK, pow_succ]
  exact ⟨2 ^ k, by ring⟩

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantPackingLayout
