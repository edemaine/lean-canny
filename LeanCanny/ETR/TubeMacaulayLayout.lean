/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeClearedSystem
public import LeanCanny.Algebra.MacaulayPolynomialSpace

/-! # A polynomially bounded layout for the full regular Macaulay system

The linear projection equation has degree one; every regular spatial row uses
the proved common degree allowance. The matrix width covers the Macaulay level,
which can exceed the original coefficient-reader width. Its unary controls are
uniform FP writers in the compiled ETR input.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCleared
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open scoped BigOperators

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def levelAllowance (bits : List Bool) : ℕ := TubeParameter.spatialCount bits * TubeIndexed.degreeBound bits + 1
noncomputable def matrixWidth (bits : List Bool) : ℕ := (levelAllowance bits).size

theorem levelAllowance_unary : UnaryFn levelAllowance :=
  (TubeParameter.spatialCount_unary.mul TubeIndexed.degreeBound_unary).add (UnaryFn.const 1)

theorem matrixWidth_unary : UnaryFn matrixWidth := levelAllowance_unary.size

noncomputable def layout (source : List Bool → List Bool) : MacaulayBits.Layout where
  arity := TubeParameter.spatialCount ∘ source
  width := matrixWidth ∘ source
  degree c i := if i = 0 then 1 else TubeIndexed.degreeBound (source c)

theorem layout_polyTime {source : List Bool → List Bool} (hs : source ∈ FP) : (layout source).PolyTime where
  arity := TubeParameter.spatialCount_unary.comp hs
  width := matrixWidth_unary.comp hs
  degree := UnaryFn.ite (FPPred.eq UnaryFn.index (UnaryFn.const 0)) (UnaryFn.const 1)
    ((TubeIndexed.degreeBound_unary.comp hs).comp pairFst_mem_FP)

theorem level_le (source : List Bool → List Bool) (c : List Bool) :
    (layout source).level c ≤ levelAllowance (source c) := by
  unfold MacaulayBits.Layout.level levelAllowance
  apply Nat.add_le_add_right
  change (∑ i ∈ Finset.range (TubeParameter.spatialCount (source c)),
    ((if i = 0 then 1 else TubeIndexed.degreeBound (source c)) - 1)) ≤
      TubeParameter.spatialCount (source c) * TubeIndexed.degreeBound (source c)
  calc
    _ ≤ ∑ _i ∈ Finset.range (TubeParameter.spatialCount (source c)), TubeIndexed.degreeBound (source c) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> omega
    _ = _ := by simp

theorem level_lt (source : List Bool → List Bool) (c : List Bool) :
    (layout source).level c < 2 ^ (layout source).width c :=
  (level_le source c).trans_lt (Nat.lt_size_self _)

theorem degree_pos (source : List Bool → List Bool) (c : List Bool) (i : ℕ) : 0 < (layout source).degree c i := by
  change 0 < if i = 0 then 1 else TubeIndexed.degreeBound (source c)
  split_ifs
  · decide
  · unfold TubeIndexed.degreeBound
    omega

end LeanCanny.ETR.TubeCleared
