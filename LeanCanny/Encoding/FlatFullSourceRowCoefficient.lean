/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceContext
public import LeanCanny.Encoding.FlatFullSourceRowQuery
public import LeanCanny.Encoding.FlatFullSourceCriticalCoefficient
public import LeanCanny.Algebra.FixedWidthLinearCoefficientSpace
public import LeanCanny.Algebra.FlatCriticalIndexedRows

/-! # Native coefficient evaluation for the complete indexed flat tower

The direction record is computed in polynomial space and attached to the
query. A guarded consumer dispatches to the critical, first-stage coordinate,
or later copy reader. Invalid row indices return canonical zero. Direction
selection and all original-source coefficient costs remain charged.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceRowCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatFullSourceTower (Inputs arity count degree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

def origin (z : List Bool) : List Bool := FlatFullSourceRowQuery.source (pairFst z)
def offset (F : Inputs) (z : List Bool) : ℕ := FlatFullSourceRowQuery.blockOffset F (pairFst z)
def base (F : Inputs) (z : List Bool) : ℕ := FlatFullSourceRowQuery.baseIndex F (pairFst z)
def current (F : Inputs) (z : List Bool) : ℕ := FlatFullSourceRowQuery.rowIndex F (pairFst z)
def previous (F : Inputs) (z : List Bool) : ℕ := FlatFullSourceRowQuery.previousIndex F (pairFst z)
def target (z : List Bool) : List Bool := FlatFullSourceRowQuery.target (pairFst z)
def modulus (z : List Bool) : List Bool := FlatFullSourceRowQuery.modulus (pairFst z)
def width (W : List Bool → ℕ) (z : List Bool) : ℕ := W (origin z)

theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP FlatFullSourceRowQuery.source_FP
theorem target_FP : target ∈ FP := mem_FP_comp pairFst_mem_FP FlatFullSourceRowQuery.target_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairFst_mem_FP FlatFullSourceRowQuery.modulus_FP

noncomputable def frame (F : Inputs) : Inputs := FlatFullSourceContext.comp F origin
theorem frame_access {F : Inputs} (h : F.Access) : (frame F).Access := FlatFullSourceContext.access h origin_FP

def directionBits (F : Inputs) (z : List Bool) : List Bool :=
  ((pairSnd z).drop (FlatFullSourceRowQuery.localIndex F (pairFst z) * F.width (origin z))).take (F.width (origin z))
def directionNat (F : Inputs) (z : List Bool) : ℕ := Nat.fromBitsLE (directionBits F z)
def direction (F : Inputs) (z : List Bool) : List Bool := BinaryNat.normalize (directionBits F z)

theorem direction_FP {F : Inputs} (h : F.Access) : direction F ∈ FP := by
  have hw := h.width.comp origin_FP
  have hi := (FlatFullSourceRowQuery.localIndex_unary h).comp pairFst_mem_FP
  have hd := take_mem_FP (drop_mem_FP pairSnd_mem_FP (hi.mul hw)) hw
  exact mem_FP_comp (g := BinaryNat.normalize) hd BinaryNat.normalize_mem_FP

theorem direction_eq (F : Inputs) (z : List Bool) :
    direction F z = BinaryNatCode.encode (directionNat F z) := BinaryNat.normalize_eq_bits _

noncomputable def criticalValue (F : Inputs) (W : List Bool → ℕ) : List Bool → List Bool :=
  FlatFullSourceCriticalCoefficient.value (frame F) (offset F) (width W) (base F) (current F)
    target modulus (direction F)

theorem critical_evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W) :
    SpaceFunction (criticalValue F W) :=
  FlatFullSourceCriticalCoefficient.evaluator (frame_access h)
    ((FlatFullSourceRowQuery.blockOffset_unary h).comp pairFst_mem_FP) (hW.comp origin_FP)
    ((FlatFullSourceRowQuery.baseIndex_unary h).comp pairFst_mem_FP)
    ((FlatFullSourceRowQuery.rowIndex_unary h).comp pairFst_mem_FP) target_FP modulus_FP (direction_FP h)

noncomputable def copyValue (F : Inputs) (W : List Bool → ℕ) (z : List Bool) : List Bool :=
  if FlatFullSourceRowQuery.stageIndex F (pairFst z) = 0 then
    FixedWidthLinearCoefficientBits.value (count (frame F)) (width W) (current F) target
      (FlatFullSourceCriticalCoefficient.modulusCode modulus) z
  else FixedWidthLinearCoefficientBits.difference (count (frame F)) (width W) (current F) target
    (FlatFullSourceCriticalCoefficient.modulusCode modulus) (previous F) z

theorem copy_FP {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W) : copyValue F W ∈ FP := by
  have hn := FlatFullSourceTower.count_unary (frame_access h)
  have hw := hW.comp origin_FP
  have hc := BinaryFn.ofUnary ((FlatFullSourceRowQuery.rowIndex_unary h).comp pairFst_mem_FP)
  have hp := BinaryFn.ofUnary ((FlatFullSourceRowQuery.previousIndex_unary h).comp pairFst_mem_FP)
  have hm := FlatFullSourceCriticalCoefficient.modulusCode_FP modulus_FP
  have h0 := (BinaryFn.ofUnary ((FlatFullSourceRowQuery.stageIndex_unary h).comp pairFst_mem_FP)).eq (BinaryFn.const 0)
  exact h0.ite_mem_FP (FixedWidthLinearCoefficientBits.value_FP _ _ _ _ _ hn hw hc target_FP hm)
    (FixedWidthLinearCoefficientBits.difference_FP _ _ _ _ _ hn hw hc hp target_FP hm)

noncomputable def consumer (F : Inputs) (W : List Bool → ℕ) (z : List Bool) : List Bool :=
  if FlatFullSourceRowQuery.Valid F (pairFst z) then
    if FlatFullSourceRowQuery.InFree F (pairFst z) then criticalValue F W z else copyValue F W z
  else []

theorem consumer_evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W) :
    SpaceFunction (consumer F W) := by
  have hi := (FlatFullSourceRowQuery.inFree_FP h).comp pairFst_mem_FP
  have hv := (FlatFullSourceRowQuery.valid_FP h).comp pairFst_mem_FP
  have H := SpaceFunction.branch (fun z => decide (FlatFullSourceRowQuery.Valid F (pairFst z))) hv.flag_mem_FP
    (SpaceFunction.branch (fun z => decide (FlatFullSourceRowQuery.InFree F (pairFst z))) hi.flag_mem_FP
      (critical_evaluator h hW) (SpaceFunction.ofFP _ (copy_FP h hW)))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact H.congr (funext fun _ => by simp only [consumer, decide_eq_true_eq])

noncomputable def value (F : Inputs) (W : List Bool → ℕ) (q : List Bool) : List Bool :=
  consumer F W (FlatFullSourceRowQuery.prepare F q)

theorem evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W) :
    SpaceFunction (value F W) := (FlatFullSourceRowQuery.prepare_evaluator h).chain (consumer_evaluator h hW)

theorem invalid (F : Inputs) (W : List Bool → ℕ) (q : List Bool) (h : ¬ FlatFullSourceRowQuery.Valid F q) :
    value F W q = [] := by
  simp only [value, consumer, FlatFullSourceRowQuery.prepare, pairFst_pair, ite_eq_right h]

end LeanCanny.Encoding.FlatFullSourceRowCoefficient
