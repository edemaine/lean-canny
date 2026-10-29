/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatCriticalTower
public import LeanCanny.Encoding.BoundedCriticalProjection
public import LeanCanny.Encoding.BoundedFullCoefficient

/-! # Uniform flat critical towers from the original full-source readers

All stages use the same original integer polynomial. Only free blocks,
directions, and pivots vary. Depth is an input reader, and the complete square
system has depth*(source dimension+4) variables. Degree and mass budgets and
the original-source coefficient reader have native certificates independent
of recursively constructed primitive parameters. Native access to the entire
flat system is constructed separately.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceTower
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open BoundedFullWriter
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

structure Inputs where
  source : Readers
  depth : List Bool → ℕ
  width : List Bool → ℕ
  offset : List Bool → ℕ
  dim : List Bool → ℕ
  direction : List Bool → List Bool
  pivot : (u : List Bool) → ℕ → Fin (source.dim u + 4)

structure Inputs.Access (F : Inputs) : Prop where
  source : F.source.PolyTime
  depth : UnaryFn F.depth
  width : UnaryFn F.width
  offset : BinaryFn F.offset
  dim : UnaryFn F.dim
  direction : SpaceFunction F.direction
  pivot : BinaryFn (fun q => (F.pivot (pairFst q) (Nat.fromBitsLE (pairSnd q))).val)
  sourceArity : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u

def stage (u : List Bool) (k : ℕ) : List Bool := pair u (BinaryNatCode.encode k)
def arity (F : Inputs) (u : List Bool) : ℕ := F.source.dim u + 4
def count (F : Inputs) (u : List Bool) : ℕ := F.depth u * arity F u

noncomputable def free (F : Inputs) (u : List Bool) (k : ℕ) : Finset (Fin (arity F u)) :=
  Finset.univ.filter (fun i => F.offset (stage u k) ≤ i.val ∧
    i.val < F.offset (stage u k) + F.dim (stage u k))

def direction (F : Inputs) (u : List Bool) (k : ℕ) (i : Fin (arity F u)) : ℤ :=
  Nat.fromBitsLE (((F.direction (stage u k)).drop (i.val * F.width u)).take (F.width u))

theorem direction_bound (F : Inputs) (u : List Bool) (k : ℕ) (i : Fin (arity F u)) :
    (direction F u k i).natAbs ≤ 2 ^ F.width u := by
  rw [direction, Int.natAbs_natCast]
  exact ((Nat.fromBitsLE_lt_pow_length _).trans_le
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))).le

noncomputable def family (F : Inputs) (u : List Bool) : TriangularPolynomialTower.Family (arity F u) ℤ :=
  FlatCriticalTower.family (BoundedFullCriticalSamples.polynomial F.source u) (free F u)
    (F.pivot u) (direction F u)

noncomputable def system (F : Inputs) (u : List Bool) :
    Fin (count F u) → MvPolynomial (Fin (count F u)) ℤ :=
  TriangularPolynomialIndexing.system (family F u) (F.depth u)

noncomputable def degree (F : Inputs) (u : List Bool) : ℕ := BoundedFullWriter.degree F.source u + 1
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ :=
  BoundedCriticalProjection.sourceBits F.source u + (degree F u).size + F.width u + 1

theorem count_le (F : Inputs) (u : List Bool) (h : F.depth u ≤ arity F u) : count F u ≤ arity F u ^ 2 := by
  rw [count, pow_two]
  exact Nat.mul_le_mul_right _ h

theorem arity_unary {F : Inputs} (h : F.Access) : UnaryFn (arity F) := h.source.dim.add (UnaryFn.const 4)
theorem count_unary {F : Inputs} (h : F.Access) : UnaryFn (count F) := h.depth.mul (arity_unary h)
theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) :=
  (BoundedFullWriter.degree_binary h.source).add (BinaryFn.const 1)
theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) :=
  (((BoundedCriticalProjection.sourceBits_binary h.source).add (degree_binary h).size).add
    (BinaryFn.ofUnary h.width)).add (BinaryFn.const 1)

theorem degree_pos (F : Inputs) (u : List Bool) : 0 < degree F u := by unfold degree; omega

theorem polynomial_degree (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    (system F u i).totalDegree ≤ degree F u := by
  apply (FlatCriticalTower.degree_le (BoundedFullCriticalSamples.polynomial F.source u)
    (free F u) (F.pivot u) (direction F u) (F.depth u) i).trans
  apply max_le
  · exact (BoundedFullCriticalSamples.source_degree F.source u).trans (Nat.le_succ _)
  · unfold degree
    omega

theorem polynomial_mass (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    MvMass.mass (system F u i) ≤ 2 ^ mass F u := by
  apply (FlatCriticalTower.mass_le (BoundedFullCriticalSamples.polynomial F.source u)
    (free F u) (F.pivot u) (direction F u) (F.depth u) (2 ^ F.width u)
      (fun j _ => direction_bound F u j) i).trans
  apply max_le
  · exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by unfold mass; omega : 1 ≤ mass F u)
  · have hd : (BoundedFullCriticalSamples.polynomial F.source u).totalDegree + 1 ≤ 2 ^ (degree F u).size :=
      ((Nat.add_le_add_right (BoundedFullCriticalSamples.source_degree F.source u) 1)).trans
        (Nat.lt_size_self _).le
    have hw : 2 ^ F.width u + 1 ≤ 2 ^ (F.width u + 1) := by
      rw [pow_succ]
      have := Nat.one_le_two_pow (n := F.width u)
      omega
    calc
      _ ≤ 2 ^ (degree F u).size * 2 ^ (F.width u + 1) *
          2 ^ BoundedCriticalProjection.sourceBits F.source u :=
        Nat.mul_le_mul (Nat.mul_le_mul hd hw) (BoundedCriticalProjection.source_mass F.source u)
      _ = _ := by rw [← pow_add, ← pow_add]; unfold mass; congr 1; omega

theorem roots_iff (F : Inputs) (u : List Bool) (z : Fin (count F u) → ℝ) :
    (∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) z = 0) ↔
      FlatCriticalTower.Steps (Int.castRingHom ℝ) (BoundedFullCriticalSamples.polynomial F.source u)
        (free F u) (F.pivot u) (direction F u) (F.depth u)
          (z ∘ TriangularPolynomialIndexing.enumerate (arity F u) (F.depth u)) :=
  FlatCriticalTower.roots_iff _ _ _ _ _ _ _

noncomputable def originalCoefficient (F : Inputs) (W : List Bool → ℕ)
    (target modulus : List Bool → List Bool) : List Bool → List Bool :=
  BoundedFullCoefficient.value F.source W target modulus

theorem originalCoefficient_evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ}
    {target modulus : List Bool → List Bool} (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (originalCoefficient F W target modulus) :=
  BoundedFullCoefficient.evaluator h.source hW ht hm h.sourceArity

end LeanCanny.Encoding.FlatFullSourceTower
