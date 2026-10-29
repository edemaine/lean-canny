/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.NumericLiteralFP
public import LeanCanny.Encoding.FlatAffineFullSourceTower
public import LeanCanny.Computation.PolyTimeArithmetic

/-! # Literal circuit coefficients from actual signed affine records

The two fixed-width magnitudes remain binary. Writing a signed coefficient
therefore costs its record width, without a unary magnitude conversion.
-/

@[expose] public section
namespace LeanCanny.ETR

theorem Term.differenceNat_toBits_mem_FP {p n : List Bool → ℕ} (hp : BinaryFn p) (hn : BinaryFn n) :
    (fun c => (Term.const ((p c : ℤ) - (n c : ℤ))).toData.toBits) ∈ FP := by
  have H := (hn.le hp).ite_mem_FP (Term.nat_toBits_mem_FP (hp.sub hn)) (Term.negNat_toBits_mem_FP (hn.sub hp))
  apply mem_FP_of_eq H
  intro c
  by_cases h : n c ≤ p c
  · have he : ((p c - n c : ℕ) : ℤ) = (p c : ℤ) - (n c : ℤ) := by omega
    simp only [h, ite_true, he]
  · have he : -((n c - p c : ℕ) : ℤ) = (p c : ℤ) - (n c : ℤ) := by omega
    simp only [h, ite_false, he]

end LeanCanny.ETR

namespace LeanCanny.Encoding.FlatAffineIntegerLiteral
open LeanCanny.ETR LeanCanny.Computation

def literal (width index : List Bool → ℕ) (record : List Bool → List Bool) (c : List Bool) : List Bool :=
  (Term.const (FlatAffineFullSourceTower.integer (width c) (record c) (index c))).toData.toBits

theorem literal_FP {width index : List Bool → ℕ} {record : List Bool → List Bool}
    (hW : UnaryFn width) (hi : UnaryFn index) (hr : record ∈ FP) : literal width index record ∈ FP := by
  have hoffset := hi.mul ((UnaryFn.const 2).mul hW)
  have hp := BinaryFn.fromBits (take_mem_FP (drop_mem_FP hr hoffset) hW)
  have hn := BinaryFn.fromBits (take_mem_FP (drop_mem_FP hr (hoffset.add hW)) hW)
  exact Term.differenceNat_toBits_mem_FP hp hn

/-- A charged space reader may supply the record before the FP literal writer. -/
theorem literal_evaluator {width index : List Bool → ℕ} {record : List Bool → List Bool}
    (hW : UnaryFn width) (hi : UnaryFn index) (hr : SpaceFunction record) : SpaceFunction (literal width index record) := by
  have H := hr.withInput.postcompose (literal (width ∘ pairFst) (index ∘ pairFst) pairSnd)
    (literal_FP (hW.comp pairFst_mem_FP) (hi.comp pairFst_mem_FP) pairSnd_mem_FP)
  exact H.congr (funext fun c => by simp only [literal, Function.comp_apply, pairFst_pair, pairSnd_pair])

end LeanCanny.Encoding.FlatAffineIntegerLiteral
