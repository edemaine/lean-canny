/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBlockPowerSpace
public import LeanCanny.Algebra.GradedReductionAnnihilator

/-! # Relative reduction actions from their original matrix reader

The action selects shifted columns of an algebra-valued matrix power and
pads nonnormal columns by zero. Its native power family retains the
original parameter algebra and both old basis ranks.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralReductionActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralBerkowitzBlockBits (original basisRowCode basisColCode)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Source extends IntegralBerkowitzBlockBits.Source where
  dimension_pos : ∀ c, 0 < dimension c
  normal : ∀ c, Fin (dimension c) → Prop
  shift : ∀ c, Fin (dimension c) → Fin (dimension c)
  bound : List Bool → ℕ

def outerIndex (S : Source) (word : List Bool → List Bool) (p : List Bool) : Fin (S.dimension (original p)) :=
  ⟨Nat.fromBitsLE (word p) % S.dimension (original p), Nat.mod_lt _ (S.dimension_pos _)⟩

def normalGuard (S : Source) (p : List Bool) : Prop :=
  S.normal (original p) (outerIndex S MatrixMoment.EntryBits.colIndex p)

noncomputable def powerFamily (S : Source) : IntegralBlockPowerBits.Family where
  dimension p := S.dimension (original p)
  rank p := S.rank (original p)
  carrier p := S.carrier (original p)
  ring p := S.ring (original p)
  basis p := S.basis (original p)
  matrix p := S.matrix (original p)
  exponent p := S.bound (original p) + 1
  row := outerIndex S MatrixMoment.EntryBits.rowIndex
  col p := S.shift (original p) (outerIndex S MatrixMoment.EntryBits.colIndex p)
  basisRow := IntegralBerkowitzBlockBits.basisIndex S.toSource basisRowCode
  basisCol := IntegralBerkowitzBlockBits.basisIndex S.toSource basisColCode
  modulus p := S.modulus (original p)
  modulus_ne_zero p := S.modulus_ne_zero (original p)

def sourceQuery (q : List Bool) : List Bool :=
  pair (pair (original (original q)) (pairSnd (pairFst q))) (pairSnd q)

theorem sourceQuery_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := original) (g := original)
    IntegralBerkowitzBlockBits.original_FP IntegralBerkowitzBlockBits.original_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

theorem sourceQuery_packet (p : List Bool) (r t i j : ℕ) :
    sourceQuery (pair (IntegralBlockMomentBits.context p r t)
      (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      pair (IntegralBlockMomentBits.context (original p) r t)
        (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)) := by
  simp only [sourceQuery, original, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair]

structure Controls (S : Source) : Prop where
  bound : BinaryFn S.bound
  shift : BinaryFn (fun p => (S.shift (original p) (outerIndex S MatrixMoment.EntryBits.colIndex p)).val)
  normal : FPPred (normalGuard S)

theorem originalBound_binary (S : Source) (h : Controls S) :
    BinaryFn (fun p => S.bound (original p)) := h.bound.comp IntegralBerkowitzBlockBits.original_FP

noncomputable def powerAccess (S : Source) (a : IntegralBerkowitzBlockBits.Access S.toSource)
    (h : Controls S) : IntegralBlockPowerBits.Access (powerFamily S) where
  dimension := IntegralBerkowitzBlockBits.originalDimension_binary S.toSource a
  rank := IntegralBerkowitzBlockBits.originalRank_binary S.toSource a
  exponent := (originalBound_binary S h).add (BinaryFn.const 1)
  row := (BinaryFn.fromBits MatrixMoment.EntryBits.rowIndex_mem_FP).mod
    (IntegralBerkowitzBlockBits.originalDimension_binary S.toSource a)
  col := h.shift
  basisRow := IntegralBerkowitzBlockBits.basisIndex_binary S.toSource a basisRowCode IntegralBerkowitzBlockBits.basisRowCode_FP
  basisCol := IntegralBerkowitzBlockBits.basisIndex_binary S.toSource a basisColCode IntegralBerkowitzBlockBits.basisColCode_FP
  modulus := a.modulus.comp IntegralBerkowitzBlockBits.original_FP
  entry := a.entry ∘ sourceQuery
  entry_eq p i j r t := by
    rw [Function.comp_apply, sourceQuery_packet]
    exact a.entry_eq (original p) i j r t

theorem power_evaluator (S : Source) (a : IntegralBerkowitzBlockBits.Access S.toSource)
    (h : Controls S) (E : SpaceFunction a.entry) : SpaceFunction (powerFamily S).value :=
  IntegralBlockPowerBits.evaluator (powerFamily S) (powerAccess S a h) (E.precompose sourceQuery sourceQuery_FP)

end LeanCanny.Algebra.IntegralReductionActionBits
