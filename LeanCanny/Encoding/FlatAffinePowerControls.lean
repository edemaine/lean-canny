/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerInfinity
public import LeanCanny.Encoding.FlatAffineFullSourceTower

/-! # Native Macaulay budgets for complete affine power towers

The actual bounded source degree is linear in the original term size. It
therefore has a unary writer, as do the mixed-degree Macaulay level and its
exponent width. The exponential determinant dimension has a binary writer.
No direction or level record is read to compute these bounds.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open scoped Classical BigOperators
variable {n k : ℕ}

lemma macaulay_level_eq (D : ℕ) :
    Macaulay.level (AffineBoxGramEliminant.degrees (degrees (n := n) (k := k) D)) =
      k * (n * (D - 2) + (D - 1)) + 1 := by
  have he := Equiv.sum_comp (rowEquiv n k) (fun j => degrees D j - 1)
  have hs : (∑ j : Index n k, (degrees D j - 1)) = k * (n * (D - 2) + (D - 1)) := by
    rw [← he, Fintype.sum_prod_type]
    simp only [degrees_row]
    simp [rowDegree, Fintype.sum_sum_type, Fin.sum_univ_succ, Nat.sub_sub, Nat.add_comm]
  simp only [Macaulay.level, AffineBoxGramEliminant.degrees, Fin.sum_univ_succ, Fin.cases_zero,
    Fin.cases_succ, Nat.sub_self, zero_add, hs]

end LeanCanny.Algebra.FlatAffinePowerTower

namespace LeanCanny.Encoding.FlatAffinePowerControls
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
set_option backward.isDefEq.respectTransparency false

noncomputable def degree (F : Inputs) : List Bool → ℕ := BoundedFullWriter.degree F.source

noncomputable def level (F : Inputs) (u : List Bool) : ℕ :=
  F.depth u * (FlatAffineFullSourceTower.arity F u * (degree F u - 2) + (degree F u - 1)) + 1

noncomputable def width (F : Inputs) (u : List Bool) : ℕ := (level F u).size

noncomputable def dimension (F : Inputs) (u : List Bool) : ℕ :=
  AffineBoxGramEliminant.dimension (FlatAffineFullSourceTower.count F u) (width F u)

theorem degree_unary {F : Inputs} (h : F.source.PolyTime) : UnaryFn (degree F) := by
  have hs := BoundedFullWriter.size_unary h
  have hd := (UnaryFn.const 2).mul (((UnaryFn.const 2).mul
    ((UnaryFn.const 2).mul (hs.add (UnaryFn.const 2)))).add (UnaryFn.const 1))
  exact hd.of_eq (fun _ => rfl)

theorem level_unary {F : Inputs} (h : F.Access) : UnaryFn (level F) :=
  (h.depth.mul (((FlatAffineFullSourceTower.arity_unary h).mul ((degree_unary h.source).sub (UnaryFn.const 2))).add
    ((degree_unary h.source).sub (UnaryFn.const 1)))).add (UnaryFn.const 1)

theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) := (level_unary h).size

theorem dimension_binary {F : Inputs} (h : F.Access) : BinaryFn (dimension F) := by
  have hn := FlatAffineFullSourceTower.count_unary h
  have he := (hn.add (UnaryFn.const 1)).mul (width_unary h)
  have hd := (BinaryFn.ofUnary (hn.add (UnaryFn.const 3))).mul ((BinaryFn.const 2).powUnary he)
  exact hd.of_eq (fun u => by
    unfold dimension AffineBoxGramEliminant.dimension FixedWidthPolynomial.count
    rw [← pow_mul, Nat.mul_comm (width F u) (FlatAffineFullSourceTower.count F u + 1)])

lemma level_eq (F : Inputs) (u : List Bool) : level F u =
    Macaulay.level (AffineBoxGramEliminant.degrees (FlatAffinePowerTower.degrees
      (n := FlatAffineFullSourceTower.arity F u) (k := F.depth u) (degree F u))) :=
  (FlatAffinePowerTower.macaulay_level_eq (degree F u)).symm

lemma level_lt (F : Inputs) (u : List Bool) : level F u < 2 ^ width F u := Nat.lt_size_self _

end LeanCanny.Encoding.FlatAffinePowerControls
