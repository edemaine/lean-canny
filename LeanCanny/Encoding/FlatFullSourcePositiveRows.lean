/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourcePositiveCoefficientCorrect
public import LeanCanny.Algebra.AffineCoordinateRowsSpace

/-! # Native homogeneous rows for flat coordinate elimination

A selected padded row is read from the actual original-source tower. The
positive completion supplies a total tail-row selector at every input,
including the empty seed. Homogenization retains a coefficient parameter,
and the coordinate equation has its explicit native coefficient reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourcePositiveRows
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatFullSourceTower (Inputs degree)
open FlatFullSourcePositive (count system)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceTower.system

noncomputable def frame (F : Inputs) : Inputs := FlatFullSourceContext.comp F pairFst

theorem system_comp (F : Inputs) (f : List Bool → List Bool) (q : List Bool) (i : Fin (count F (f q))) :
    system (FlatFullSourceContext.comp F f) q i = system F (f q) i := by
  unfold system
  have hs : FlatFullSourceTower.system (FlatFullSourceContext.comp F f) q = FlatFullSourceTower.system F (f q) :=
    funext (FlatFullSourceContext.system_comp F f q)
  rw [hs]

theorem frame_system (F : Inputs) (q : List Bool) (i : Fin (count F (pairFst q))) :
    system (frame F) q i = system F (pairFst q) i := system_comp F pairFst q i

theorem integer_evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    (hw : ∀ c, degree F c < 2 ^ W c)
    (row : (c : List Bool) → Fin (count F c)) (hr : UnaryFn (fun c => (row c).val))
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (HomogenizationPolynomialBits.integerValue (count F) W (fun c => system F c (row c)) modulus) := by
  let rowCode (q : List Bool) := BinaryNatCode.encode (row (pairFst q)).val
  have hrow : rowCode ∈ FP := (BinaryFn.ofUnary (hr.comp pairFst_mem_FP)).bits_mem_FP
  have E := FlatFullSourcePositiveCoefficient.evaluator (FlatFullSourceContext.access h pairFst_mem_FP)
    (hW.comp pairFst_mem_FP) hrow pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm)
  refine E.congr (funext fun q => ?_)
  have H := FlatFullSourcePositiveCoefficient.packet (frame F) (W ∘ pairFst) rowCode pairSnd (modulus ∘ pairFst)
    q (row (pairFst q)) (MacaulayBits.fromBits_encode _) (hw (pairFst q))
  rw [frame_system] at H
  dsimp only [HomogenizationPolynomialBits.integerValue, Function.comp_def, count,
    FlatFullSourceTower.count, FlatFullSourceTower.arity, frame, FlatFullSourceContext.comp,
    BoundedFullWriter.Readers.comp] at H ⊢
  exact H

theorem evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    (hw : ∀ c, degree F c < 2 ^ W c) (hwpos : ∀ c, 0 < W c)
    (coordinate : (c : List Bool) → Fin (count F c)) (hc : UnaryFn (fun c => (coordinate c).val))
    (row : (c : List Bool) → Fin (count F c + 1)) (hr : UnaryFn (fun c => (row c).val))
    {parameter modulus : List Bool → List Bool} (hk : parameter ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (AffineCoordinateRowsBits.value (count F) W (degree F) (system F)
      coordinate row parameter modulus) :=
  AffineCoordinateRowsBits.evaluator (FlatFullSourcePositive.count_unary h) hW
    (FlatFullSourceTower.degree_binary h) (FlatFullSourcePositive.count_pos F) hwpos (system F) coordinate hc row hr hk hm
    (integer_evaluator h hW hw (AffineCoordinateRowsBits.tailRow (count F) (FlatFullSourcePositive.count_pos F) row)
      (AffineCoordinateRowsBits.tailRow_unary (FlatFullSourcePositive.count_unary h)
        (FlatFullSourcePositive.count_pos F) row hr) hm)

end LeanCanny.Encoding.FlatFullSourcePositiveRows
