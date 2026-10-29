/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineFullSourceEmbedded
public import LeanCanny.Encoding.FlatAffineRowAccess
public import LeanCanny.Encoding.FlatAffineRowPolynomials
public import LeanCanny.Algebra.FixedWidthRowArithmetic

/-! # Native source components guarded by actual original-row validity -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineRowSourceReaders
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity degree)
open FlatAffineRowLayout FlatAffineRowAccess
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

variable (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))

def old (u : List Bool) : Prop := index F row u < FlatAffineFullSourceTower.count F u

noncomputable def guard (p : (u : List Bool) → MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ)
    (u : List Bool) := if old F row u then p u else 0

noncomputable def derivativePolynomial (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  rename (current F row u) (pderiv (spatial F row u) (BoundedFullCriticalSamples.polynomial F.source u))

noncomputable def sourceWidth (u : List Bool) : ℕ := (degree F u).size

def selected (u : List Bool) : ℕ := offset F row u + (spatial F row u).val

theorem old_FP {F : Inputs} (h : F.Access) {row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)}
    (hr : UnaryFn (fun u => (row u).val)) : FPPred (old F row) :=
  (BinaryFn.ofUnary hr).lt (BinaryFn.ofUnary (FlatAffineFullSourceTower.count_unary h))

theorem sourceWidth_unary {F : Inputs} (h : F.Access) : UnaryFn (sourceWidth F) :=
  (UnaryFn.length (FlatAffineFullSourceTower.degree_binary h).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

theorem source_fit (u : List Bool) (h : old F row u) :
    offset F row u + arity F u ≤ FlatAffineFullSourcePositive.count F u := by
  have H := block_fit F row u h
  have hn : arity F u ≤ FlatAffineFullSourceTower.stageWidth F u := by change _ ≤ arity F u + (arity F u + 1); omega
  change _ ≤ FlatAffineFullSourceTower.count F u + 1
  omega

theorem shift_current (u : List Bool) (h : old F row u) :
    BlockRenameCoefficient.shift (arity F u) (FlatAffineFullSourcePositive.count F u) (offset F row u) (source_fit F row u h) =
      current F row u := by
  funext i
  apply Fin.ext
  change offset F row u + i.val = min (offset F row u + i.val) (FlatAffineFullSourceTower.count F u)
  have H := block_fit F row u h
  have hi : i.val < FlatAffineFullSourceTower.stageWidth F u := by
    have := i.isLt
    change _ < arity F u + (arity F u + 1)
    omega
  rw [Nat.min_eq_left (by omega)]

variable {F row}

theorem source_evaluator (h : F.Access) (hr : UnaryFn (fun u => (row u).val))
    {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W
      (guard F row (FlatAffineRowPolynomials.source F row)) target modulus) := by
  apply FixedWidthRowBits.guarded_evaluator _ _ _ _ _
    (FlatAffineFullSourceEmbedded.coefficient F (FlatAffineFullSourcePositive.count F) (offset F row) W target modulus)
    (old F row) (old_FP h hr)
    (FlatAffineFullSourceEmbedded.coefficient_evaluator h (FlatAffineFullSourcePositive.count_unary h) (offset_unary h hr) hW ht hm)
  intro u hu
  rw [FlatAffineFullSourceEmbedded.coefficient_packet F _ _ _ _ _ u (source_fit F row u hu), shift_current F row u hu]
  rfl

theorem derivative_evaluator (h : F.Access) (hr : UnaryFn (fun u => (row u).val))
    {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W
      (guard F row (derivativePolynomial F row)) target modulus) := by
  have hs : UnaryFn (selected F row) := (offset_unary h hr).add (spatial_unary h hr)
  apply FixedWidthRowBits.guarded_evaluator _ _ _ _ _
    (FlatAffineFullSourceEmbedded.derivative F (FlatAffineFullSourcePositive.count F) (offset F row)
      (sourceWidth F) W (selected F row) target modulus) (old F row) (old_FP h hr)
    (FlatAffineFullSourceEmbedded.derivative_evaluator h (FlatAffineFullSourcePositive.count_unary h)
      (offset_unary h hr) (sourceWidth_unary h) hW hs ht hm)
  intro u hu
  rw [FlatAffineFullSourceEmbedded.derivative_packet F _ _ _ _ _ _ _ u (source_fit F row u hu) (spatial F row u)
    rfl (Nat.lt_size_self _), shift_current F row u hu]
  rfl

end LeanCanny.Encoding.FlatAffineRowSourceReaders
