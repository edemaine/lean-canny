/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerCoordinateRows
public import LeanCanny.Algebra.MacaulayFullBoxDeterminantSpace

/-! # Native full-box layout for the actual positive affine power system -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerGramLayout
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def tail (F : Inputs) (u : List Bool) (i : ℕ) : Fin (count F u) :=
  ⟨min (i - 1) (count F u - 1), by have := FlatAffineFullSourcePositive.count_pos F u; omega⟩

theorem tail_unary {F : Inputs} (h : F.Access) :
    UnaryFn (fun q => (tail F (pairFst q) (Nat.fromBitsLE (pairSnd q))).val) := by
  have hw := ((BinaryFn.fromBits pairSnd_mem_FP).sub (BinaryFn.const 1)).bits_mem_FP
  have H := UnaryFn.fromBitsLE_min hw (((FlatAffineFullSourcePositive.count_unary h).comp pairFst_mem_FP).sub (UnaryFn.const 1))
  exact H.of_eq (fun q => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)

noncomputable def layout (F : Inputs) : MacaulayFullBoxBits.Layout where
  arity u := count F u + 1
  width := FlatAffinePowerControls.width F
  level := FlatAffinePowerControls.level F
  degree u i := if i = 0 then 1 else FlatAffinePowerPositive.degree F u (tail F u i)

theorem controls {F : Inputs} (h : F.Access) : (layout F).Controls := by
  have hf := FlatAffineFullSourceContext.access h pairFst_mem_FP
  have hd := FlatAffinePowerPositive.degree_unary hf
    (fun q => tail F (pairFst q) (Nat.fromBitsLE (pairSnd q))) (tail_unary h)
  have he : BinaryFn (fun q => FlatAffinePowerPositive.degree F (pairFst q)
      (tail F (pairFst q) (Nat.fromBitsLE (pairSnd q)))) := BinaryFn.ofUnary hd
  refine ⟨(FlatAffineFullSourcePositive.count_unary h).add (UnaryFn.const 1),
    FlatAffinePowerControls.width_unary h, BinaryFn.ofUnary (FlatAffinePowerControls.level_unary h), ?_⟩
  exact (BinaryFn.ite ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)) (BinaryFn.const 1) he).of_eq (fun _ => rfl)

lemma degrees_eq (F : Inputs) (u : List Bool) :
    (fun i : Fin ((layout F).arity u) => (layout F).degree u i.val) =
      AffineBoxGramEliminant.degrees (FlatAffinePowerPositive.degree F u) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [layout, Fin.val_zero, ite_true, AffineBoxGramEliminant.degrees, Fin.cases_zero]
  · simp only [layout, Fin.val_succ, Nat.add_one_ne_zero, ite_false, AffineBoxGramEliminant.degrees, Fin.cases_succ]
    have hi : tail F u (i.val + 1) = i := by
      apply Fin.ext
      simp only [tail, Nat.add_sub_cancel]
      exact Nat.min_eq_left (by have := i.isLt; omega)
    rw [hi]

lemma level_eq (F : Inputs) (u : List Bool) :
    (layout F).level u = Macaulay.level (fun i : Fin ((layout F).arity u) => (layout F).degree u i.val) := by
  rw [degrees_eq]
  change FlatAffinePowerControls.level F u = Macaulay.level (AffineBoxGramEliminant.degrees (FlatAffinePowerPositive.degree F u))
  have h := FlatAffinePowerControls.level_eq F u
  simp only [Macaulay.level, AffineBoxGramEliminant.degrees, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    Nat.sub_self, zero_add] at h ⊢
  dsimp only [FlatAffineFullSourcePositive.count]
  rw [Fin.sum_univ_castSucc]
  simp only [FlatAffinePowerPositive.degree, Fin.lastCases_castSucc, Fin.lastCases_last, Nat.sub_self, add_zero]
  exact h

lemma width_eq (F : Inputs) (u : List Bool) :
    FlatAffinePowerControls.width F u = AffineFiniteCoordinates.width (FlatAffinePowerPositive.degree F u) := by
  change (FlatAffinePowerControls.level F u).size =
    (Macaulay.level (AffineBoxGramEliminant.degrees (FlatAffinePowerPositive.degree F u))).size
  exact congrArg Nat.size ((level_eq F u).trans (congrArg Macaulay.level (degrees_eq F u)))

noncomputable def dimension (F : Inputs) (u : List Bool) : ℕ :=
  AffineBoxGramEliminant.dimension (count F u) (FlatAffinePowerControls.width F u)

theorem dimension_binary {F : Inputs} (h : F.Access) : BinaryFn (dimension F) := by
  have hn := FlatAffineFullSourcePositive.count_unary h
  have he := (hn.add (UnaryFn.const 1)).mul (FlatAffinePowerControls.width_unary h)
  have hd := (BinaryFn.ofUnary (hn.add (UnaryFn.const 3))).mul ((BinaryFn.const 2).powUnary he)
  exact hd.of_eq (fun u => by
    unfold dimension AffineBoxGramEliminant.dimension FixedWidthPolynomial.count
    rw [← pow_mul, Nat.mul_comm (FlatAffinePowerControls.width F u) (count F u + 1)])

end LeanCanny.Encoding.FlatAffinePowerGramLayout
